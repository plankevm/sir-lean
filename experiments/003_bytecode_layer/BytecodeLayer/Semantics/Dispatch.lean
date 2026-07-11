import Evm

/-!
# Dispatch / `stepFrame` characterization (`Dispatch`)

Two clusters about the per-opcode `stepFrame` dispatcher.

**Step characterization.** `stepFrame` equations for the opcodes the capstones
execute. Each says: at a pc where the code decodes to this opcode, with enough
gas and stack room, the step is exactly the obvious result — no `OutOfGas`, no
`StackOverflow`, no decode failure. This is the *vacuity-propagation* discipline
made concrete: the gas and overflow guards are discharged once, here, as
`if_neg`s from explicit hypotheses, and never reappear. These are low-level on
purpose (they mention `pc`, `stack`, `gasAvailable`); they are internal bricks.

**Dispatch signal shape.** The `onlyNext` machinery (mirroring `neverHalts`) and
the `stepFrame`→`systemOp` bridges. The non-`System` dispatcher arms only ever
emit `.next`, so a `.needsCall`/`.needsCreate`/(System) `.next` signal forces the
decoded op to be a `System` op.
-/

namespace BytecodeLayer.Dispatch
open Evm
open Evm.Operation
open GasConstants

/-- **STOP halts with the current state and empty output**, given only that the
stack is not overflowing (≤ 1024). STOP reads no operands and charges no gas, so
there is no gas hypothesis. -/
theorem stepFrame_stop (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .STOP, .none))
    (hstk : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success fr.exec .empty) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide), if_neg (by simpa using hstk)]
  rfl

/-- **PUSH1 imm pushes `imm` and advances pc by 2**, charging `Gverylow = 3`.
The guards (`InvalidInstruction`, `StackOverflow`, `OutOfGas`) are discharged
from the hypotheses `hgas`, `hstk`. -/
theorem stepFrame_push1 (fr : Frame) (imm : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH1, some (imm, 1)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    stepFrame fr = .next
      (({ fr.exec with gasAvailable := fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
        ).replaceStackAndIncrPC (fr.exec.stack.push imm) (pcΔ := 2)) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Push .PUSH1)
      + stackPushCount (.Push .PUSH1) > 1024) := by
    simp only [show stackPopCount (.Push .PUSH1) = 0 from rfl,
               show stackPushCount (.Push .PUSH1) = 1 from rfl]
    omega
  rw [if_neg hov]
  dsimp only [dispatch]
  unfold Evm.charge
  rw [if_neg (by simp only [show GasConstants.Gverylow = 3 from rfl]; omega)]
  rfl

/-- **Generic `PUSH<w>` (w ≥ 1) pushes `imm` and advances pc by `w+1`**, charging
`Gverylow = 3`. Works for any push width `p` other than `PUSH0` (they share the
`.Push _` dispatch arm); the caller supplies the decode and the pop/push counts
(`δ = 0`, `α = 1` for every PUSH). Used for the multi-byte gas/address pushes the
external-call caller needs (PUSH3, PUSH4). -/
theorem stepFrame_push (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    stepFrame fr = .next
      (({ fr.exec with gasAvailable := fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
        ).replaceStackAndIncrPC (fr.exec.stack.push imm) (pcΔ := w + 1)) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by exact (by nofun : (Operation.Push p) ≠ Operation.INVALID))]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Push p)
      + stackPushCount (.Push p) > 1024) := by
    rw [hpop, hpush]; omega
  rw [if_neg hov]
  cases p with
  | PUSH0 => exact absurd rfl hp0
  | _ =>
    all_goals (
      dsimp only [dispatch]
      unfold Evm.charge
      rw [if_neg (by simp only [show GasConstants.Gverylow = 3 from rfl]; omega)]
      rfl)

/-! ## SSTORE

The first instruction with a *persistent* effect. SSTORE (`.Smsf .SSTORE`):
requires state-modifying context, refuses to run with `gasAvailable ≤
Gcallstipend`, pops `key`/`newValue`, charges the EIP-2200 store cost, and
writes the cell. The cost depends on the world (original/current cell values,
warm/cold), so we pull it out as `sstoreChargeOf` and let the step lemma's gas
guard and result share that one term — the result state `sstorePost` is the
frame after charging and performing the write. The three guards
(`StaticModeViolation`, the stipend gate, `OutOfGas`) are discharged once here as
`if_pos`/`if_neg` from explicit hypotheses, in the vacuity-propagation style. -/

/-- The exact cost SSTORE charges for storing `newValue` at `key`, as a function
of the frame's world. Pulled out so the step lemma's gas guard and resulting
state refer to the same term. -/
def sstoreChargeOf (exec : ExecutionState) (key newValue : UInt256) : ℕ :=
  sstoreCost
    (exec.originalAccounts.find? exec.executionEnv.address |>.option 0 (·.storage.findD key 0))
    (exec.accounts.find? exec.executionEnv.address |>.option 0 (·.storage.findD key 0))
    newValue
    (exec.substate.accessedStorageKeys.contains (exec.executionEnv.address, key))

/-- The execution state after SSTORE charges its cost and performs the write. -/
def sstorePost (exec : ExecutionState) (key newValue : UInt256) (rest : Stack UInt256) :
    ExecutionState :=
  let charged : ExecutionState :=
    { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat (sstoreChargeOf exec key newValue) }
  ExecutionState.replaceStackAndIncrPC
    { charged with toState := charged.toState.sstore key newValue } rest

/-- **SSTORE writes `newValue` at `key` and advances pc by 1**, charging the
EIP-2200 store cost. The guards (`StaticModeViolation`, the `Gcallstipend` gate,
`StackOverflow`, `OutOfGas`) are discharged from the hypotheses. -/
theorem stepFrame_sstore (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: newValue :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key newValue ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (sstorePost fr.exec key newValue rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .SSTORE)
      + stackPushCount (.Smsf .SSTORE) > 1024) := by
    simp only [show stackPopCount (.Smsf .SSTORE) = 2 from rfl,
               show stackPushCount (.Smsf .SSTORE) = 0 from rfl]
    have := hsz
    omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold requireStateMod
  rw [if_pos hmod]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg hstip]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  unfold charge
  rw [if_neg (by
    have h := hcost
    dsimp only [sstoreChargeOf, Option.option] at h
    omega)]
  dsimp only [sstorePost, sstoreChargeOf, Option.option]
  rfl

/-- **SSTORE out-of-gas.** With the stipend gate cleared but the store cost
exceeding the remaining gas, `stepFrame` halts with an `OutOfGas` exception. This
is the callee-starving step the external-call `∃G₀` counterexample turns on. -/
theorem stepFrame_sstore_oog (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: newValue :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ Gcallstipend)
    (hoog : fr.exec.gasAvailable.toNat < sstoreChargeOf fr.exec key newValue) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .SSTORE)
      + stackPushCount (.Smsf .SSTORE) > 1024) := by
    simp only [show stackPopCount (.Smsf .SSTORE) = 2 from rfl,
               show stackPushCount (.Smsf .SSTORE) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold requireStateMod
  rw [if_pos hmod]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg hstip]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  unfold charge
  rw [if_pos (by
    have h := hoog
    dsimp only [sstoreChargeOf, Option.option] at h
    omega)]

/-- **SSTORE stipend-gate halt.** With state-modifying context but the available
gas at or below `Gcallstipend`, SSTORE refuses to run: `stepFrame` halts with
`OutOfGas` before charging. The `.next`-success inversion (`stepFrame_sstore_inv`)
turns on the contrapositive of this together with `stepFrame_sstore_oog`. -/
theorem stepFrame_sstore_stipend (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (_hstk : fr.exec.stack = key :: newValue :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : fr.exec.gasAvailable.toNat ≤ Gcallstipend) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .SSTORE)
      + stackPushCount (.Smsf .SSTORE) > 1024) := by
    simp only [show stackPopCount (.Smsf .SSTORE) = 2 from rfl,
               show stackPushCount (.Smsf .SSTORE) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold requireStateMod
  rw [if_pos hmod]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_pos hstip]

/-- **SSTORE success-inversion (the EIP-2200 gate).** A *successful* `.next` SSTORE
step witnesses its own runtime gate: from `stepFrame fr = .next e` at an SSTORE-decoding
frame with stack `key :: newValue :: rest` in state-modifying context, the
`Gcallstipend` gate is open (`¬ gas ≤ Gcallstipend`) and the EIP-2200 charge fits
(`sstoreChargeOf … ≤ gas`). These are exactly the two genuine runtime gates the
dispatch CHECKS, so `.next` ⇒ they held — they are `SstoreRealises`'s gas payload
(`MaterialiseRuns.lean`), no longer supplied. (The third `SstoreRealises` conjunct —
the self account being *present* — is **not** a gate the dispatch checks: SSTORE reads
the cell through `.option 0`, so `.next` does not witness presence; it must come from a
world-wellformedness invariant, not from this inversion.) -/
theorem stepFrame_sstore_inv (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: newValue :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hnext : stepFrame fr = .next e) :
    (¬ fr.exec.gasAvailable.toNat ≤ Gcallstipend)
    ∧ sstoreChargeOf fr.exec key newValue ≤ fr.exec.gasAvailable.toNat := by
  refine ⟨?_, ?_⟩
  · intro hstip
    rw [stepFrame_sstore_stipend fr key newValue rest hdec hstk hsz hmod hstip] at hnext
    exact absurd hnext (by simp)
  · by_contra hcost
    have hoog : fr.exec.gasAvailable.toNat < sstoreChargeOf fr.exec key newValue := by omega
    -- the stipend gate must be open, else the stipend-halt already contradicts `.next`.
    have hstip : ¬ fr.exec.gasAvailable.toNat ≤ Gcallstipend := by
      intro hstip
      rw [stepFrame_sstore_stipend fr key newValue rest hdec hstk hsz hmod hstip] at hnext
      exact absurd hnext (by simp)
    rw [stepFrame_sstore_oog fr key newValue rest hdec hstk hsz hmod hstip hoog] at hnext
    exact absurd hnext (by simp)

/-! ## ADD / LT (binary arithmetic-logic)

The first pure-stack arithmetic bricks Track C's expression lowering needs. Both
go through `binOp f exec cost`: charge `Gverylow = 3`, pop two operands `a`/`b`,
push `f a b`, advance pc by one. The post-state is `replaceStackAndIncrPC` over the
charged state with the result pushed onto `rest`. The guards (`InvalidInstruction`,
`StackOverflow`, `OutOfGas`) are discharged from `hstk`/`hsz`/`hgas` exactly as in
PUSH/SSTORE. The result function `f` is left abstract in `binOpPost` so ADD and LT
share one post-state shape; the rules instantiate `f := UInt256.add` / `UInt256.lt`. -/

/-- The execution state a `binOp f` leaves: charge `Gverylow`, pop `a`/`b`, push
`f a b`, advance pc by one. Shared by ADD (`f := UInt256.add`) and LT
(`f := UInt256.lt`). -/
def binOpPost (exec : ExecutionState) (f : UInt256 → UInt256 → UInt256)
    (a b : UInt256) (rest : Stack UInt256) : ExecutionState :=
  ({ exec with gasAvailable := exec.gasAvailable - UInt64.ofNat Gverylow }
    ).replaceStackAndIncrPC (rest.push (f a b))

/-- The shared `stepFrame` characterization for a `binOp`-dispatched op (ADD/LT):
with `a :: b :: rest` on the stack, enough gas (`Gverylow`) and no overflow, the
step is `.next (binOpPost …)`. `hdisp` pins the decoded op to its `binOp` arm. -/
private theorem stepFrame_binOp (fr : Frame) (op : Operation) (f : UInt256 → UInt256 → UInt256)
    (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (op, .none))
    (hne : op ≠ .INVALID)
    (hpop : stackPopCount op = 2) (hpush : stackPushCount op = 1)
    (hdisp : ∀ exec, dispatch op .none fr exec = binOp f exec Gverylow)
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gverylow ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (binOpPost fr.exec f a b rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg hne]
  have hov : ¬ (fr.exec.stack.size - stackPopCount op + stackPushCount op > 1024) := by
    rw [hpop, hpush]; have := hsz; omega
  rw [if_neg hov]
  rw [hdisp]
  unfold binOp charge
  rw [if_neg (by omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  rfl

/-- **ADD pops `a`/`b`, pushes `a + b`, advances pc by one**, charging `Gverylow = 3`.
Guards discharged from `hstk`/`hsz`/`hgas`. -/
theorem stepFrame_add (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gverylow ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (binOpPost fr.exec UInt256.add a b rest) :=
  stepFrame_binOp fr (.ArithLogic .ADD) UInt256.add a b rest hdec (by nofun)
    rfl rfl (fun _ => rfl) hstk hsz hgas

/-- **LT pops `a`/`b`, pushes `UInt256.lt a b` (= `if a < b then 1 else 0`), advances
pc by one**, charging `Gverylow = 3`. Guards discharged from `hstk`/`hsz`/`hgas`. -/
theorem stepFrame_lt (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gverylow ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (binOpPost fr.exec UInt256.lt a b rest) :=
  stepFrame_binOp fr (.ArithLogic .LT) UInt256.lt a b rest hdec (by nofun)
    rfl rfl (fun _ => rfl) hstk hsz hgas

/-! ## SLOAD (storage read)

The storage-read brick. SLOAD (`.Smsf .SLOAD`) goes through `unStateOp
Evm.State.sload (sloadCost …)`: pop `key`, charge `sloadCost warm` (warm/cold =
100/2100, where `warm` is `accessedStorageKeys.contains (self, key)`), then push the
self account's stored value and mark `(self, key)` accessed. The pushed value is
`exec.toState.sload key |>.2 = lookupAccount self |>.option 0 (·.lookupStorage key)` —
which the `runs_sload` companion lemma exposes through the same storage lens C3 uses.
Guards (`InvalidInstruction`, `StackOverflow`, `OutOfGas`) from `hstk`/`hsz`/`hgas`. -/

/-- The execution state SLOAD leaves: charge `sloadCost warm`, push the self
account's stored value at `key`, mark `(self, key)` accessed, advance pc by one. The
cost and the result both come from the model's `Evm.State.sload`, so the gas guard
and the resulting state refer to the same `sloadCost`. -/
def sloadPost (exec : ExecutionState) (key : UInt256) (rest : Stack UInt256) :
    ExecutionState :=
  let warm := exec.substate.accessedStorageKeys.contains (exec.executionEnv.address, key)
  let charged : ExecutionState :=
    { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat (sloadCost warm) }
  let (state', v) := Evm.State.sload charged.toState key
  ExecutionState.replaceStackAndIncrPC { charged with toState := state' } (rest.push v)

/-- **SLOAD pops `key`, pushes the self account's stored value, advances pc by one**,
charging `sloadCost warm`. Guards discharged from `hstk`/`hsz`/`hgas`. -/
theorem stepFrame_sload (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (sloadPost fr.exec key rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .SLOAD)
      + stackPushCount (.Smsf .SLOAD) > 1024) := by
    simp only [show stackPopCount (.Smsf .SLOAD) = 1 from rfl,
               show stackPushCount (.Smsf .SLOAD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp, unStateOp]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  unfold charge
  rw [if_neg (by have := hgas; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rfl

/-! ## GAS (gas introspection)

The gas-introspection brick. GAS (`.Smsf .GAS`) goes through `pushOp (λ s ↦
UInt256.ofUInt64 s.gasAvailable)`: charge `Gbase = 2`, then push `ofUInt64
gasAvailable` read **after** the charge — so the value pinned in the post-state is
the post-charge gas, keeping C3's gas threading honest. Pops nothing; the overflow
guard is `stack.size + 1 ≤ 1024`. -/

/-- The execution state GAS leaves: charge `Gbase`, push `ofUInt64` of the *post-charge*
`gasAvailable`, advance pc by one. The pushed value reads the charged gas. -/
def gasPost (exec : ExecutionState) : ExecutionState :=
  let charged : ExecutionState :=
    { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat Gbase }
  charged.replaceStackAndIncrPC (charged.stack.push (UInt256.ofUInt64 charged.gasAvailable))

/-- **GAS pushes `ofUInt64` of the post-charge `gasAvailable`, advances pc by one**,
charging `Gbase = 2`. Pops nothing; overflow guard `stack.size + 1 ≤ 1024`. -/
theorem stepFrame_gas (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : Gbase ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (gasPost fr.exec) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .GAS)
      + stackPushCount (.Smsf .GAS) > 1024) := by
    simp only [show stackPopCount (.Smsf .GAS) = 0 from rfl,
               show stackPushCount (.Smsf .GAS) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp, pushOp]
  unfold charge
  rw [if_neg (by have := hgas; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rfl

/-! ## POP (stack discard)

The stack-discard brick. POP (`.Smsf .POP`) charges `Gbase = 2`, pops one operand
off the top and pushes nothing, advancing pc by one. Track C's call lowering uses
it for the fire-and-forget (`resultTmp = none`) call tail, discarding the CALL
success flag. Pops one, pushes none; the overflow guard is trivial (the stack only
shrinks). -/

/-- The execution state POP leaves: charge `Gbase`, drop the top operand (leaving
`rest`), advance pc by one. -/
def popPost (exec : ExecutionState) (rest : Stack UInt256) : ExecutionState :=
  ({ exec with gasAvailable := exec.gasAvailable - UInt64.ofNat Gbase }
    ).replaceStackAndIncrPC rest

/-- **POP discards the top operand, advances pc by one**, charging `Gbase = 2`.
With `v :: rest` on the stack and enough gas, the step is `.next (popPost …)`.
Guards discharged from `hstk`/`hsz`/`hgas`. -/
theorem stepFrame_pop (fr : Frame) (v : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .POP, .none))
    (hstk : fr.exec.stack = v :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gbase ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (popPost fr.exec rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .POP)
      + stackPushCount (.Smsf .POP) > 1024) := by
    simp only [show stackPopCount (.Smsf .POP) = 1 from rfl,
               show stackPushCount (.Smsf .POP) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_neg (by have := hgas; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  rfl

/-! ## MSTORE / MLOAD (memory write / read)

The memory bricks Track C's value channel threads. Both first **charge memory
expansion** (`chargeMemExpansion exec addr 32`), then `Gverylow = 3`, before the
write/read. The expansion charge is the `Cₘ`-difference of the new active-word
count `words'` over the old: it is `none` (an `OutOfGas` halt) only when the
offset/size overflow the addressable window, so the step lemmas take an explicit
witness `hmem : memoryExpansionWords? activeWords addr 32 = some words'` pinning
`words'`, and the gas guards then refer to the same `Cₘ words' - Cₘ activeWords`
term. Memory expansion only ever grows the cost monotonically, so the two charges
are discharged from `hgasMem` (the expansion charge fits) and `hgas` (`Gverylow`
fits *after* the expansion charge). The post-state is the doubly-charged state with
the write (`mstore`) applied / value (`mload`) pushed, pc advanced by one. -/

/-- The active-word-expansion gas MSTORE/MLOAD charge before `Gverylow`, given the
new active-word count `words'` the access expands memory to: `Cₘ words' - Cₘ
activeWords`. Pulled out so the step lemmas' gas guards and resulting state refer to
the same term. -/
def memExpansionChargeOf (exec : ExecutionState) (words' : UInt64) : ℕ :=
  Cₘ words' - Cₘ exec.activeWords

/-- The execution state after the two MSTORE/MLOAD charges (memory expansion to
`words'`, then `Gverylow`). The shared charged state both ops write/read from. -/
def memChargedState (exec : ExecutionState) (words' : UInt64) : ExecutionState :=
  let charged0 : ExecutionState :=
    { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf exec words') }
  { charged0 with gasAvailable := charged0.gasAvailable - UInt64.ofNat Gverylow }

/-- The execution state MSTORE leaves: charge memory expansion (to `words'`) and
`Gverylow`, write `val` at `addr` in memory, advance pc by one. The popped stack is
`rest`. -/
def mstorePost (exec : ExecutionState) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) : ExecutionState :=
  let charged := memChargedState exec words'
  ExecutionState.replaceStackAndIncrPC
    { charged with toMachineState := charged.toMachineState.mstore addr val } rest

/-- The execution state MLOAD leaves: charge memory expansion (to `words'`) and
`Gverylow`, push the loaded value `(toMachineState.mload addr).1` and update the
machine state to `(toMachineState.mload addr).2` (the active-words bump), advance pc
by one. The popped stack is `rest`. -/
def mloadPost (exec : ExecutionState) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256) : ExecutionState :=
  let charged := memChargedState exec words'
  let (v, machine') := charged.toMachineState.mload addr
  ExecutionState.replaceStackAndIncrPC { charged with toMachineState := machine' } (rest.push v)

/-- **MSTORE writes `val` at `addr` and advances pc by one**, charging memory
expansion (to `words'`) and `Gverylow = 3`. The expansion witness `hmem` pins
`words'`; the gas guards (`hgasMem` for the expansion charge, `hgas` for `Gverylow`
on top of it) and the `none`/`StackOverflow` screens are discharged from the
hypotheses, vacuity-propagation style. -/
theorem stepFrame_mstore (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat)
    (hgas : Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat) :
    stepFrame fr = .next (mstorePost fr.exec addr val words' rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MSTORE)
      + stackPushCount (.Smsf .MSTORE) > 1024) := by
    simp only [show stackPopCount (.Smsf .MSTORE) = 2 from rfl,
               show stackPushCount (.Smsf .MSTORE) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  unfold charge
  rw [if_neg (by have := hgasMem; dsimp only [memExpansionChargeOf] at this ⊢; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg (by have := hgas; dsimp only [memExpansionChargeOf] at this ⊢; omega)]
  dsimp only [mstorePost, memChargedState, memExpansionChargeOf]
  rfl

/-- **MLOAD loads the word at `addr`, pushes it, and advances pc by one**, charging
memory expansion (to `words'`) and `Gverylow = 3`. The expansion witness `hmem` pins
`words'`; the gas guards (`hgasMem`/`hgas`) and the `none`/`StackOverflow` screens are
discharged from the hypotheses. -/
theorem stepFrame_mload (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat)
    (hgas : Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat) :
    stepFrame fr = .next (mloadPost fr.exec addr words' rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MLOAD)
      + stackPushCount (.Smsf .MLOAD) > 1024) := by
    simp only [show stackPopCount (.Smsf .MLOAD) = 1 from rfl,
               show stackPushCount (.Smsf .MLOAD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  unfold charge
  rw [if_neg (by have := hgasMem; dsimp only [memExpansionChargeOf] at this ⊢; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg (by have := hgas; dsimp only [memExpansionChargeOf] at this ⊢; omega)]
  dsimp only [mloadPost, memChargedState, memExpansionChargeOf]
  rfl

/-- **MSTORE memory-expansion out-of-gas.** With the expansion witness `words'` resolved
but the expansion charge exceeding the remaining gas, `stepFrame` halts with `OutOfGas`
at the first `charge`. The `.next`-success inversion turns on the contrapositive. -/
theorem stepFrame_mstore_oogMem (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hoog : fr.exec.gasAvailable.toNat < memExpansionChargeOf fr.exec words') :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MSTORE)
      + stackPushCount (.Smsf .MSTORE) > 1024) := by
    simp only [show stackPopCount (.Smsf .MSTORE) = 2 from rfl,
               show stackPushCount (.Smsf .MSTORE) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  unfold charge
  rw [if_pos (by have := hoog; dsimp only [memExpansionChargeOf] at this ⊢; omega)]

/-- **MSTORE `Gverylow` out-of-gas.** With the expansion charge cleared but `Gverylow`
exceeding the post-expansion gas, `stepFrame` halts with `OutOfGas` at the second
`charge`. The `.next`-success inversion turns on the contrapositive. -/
theorem stepFrame_mstore_oogVL (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat)
    (hoog : (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
              < Gverylow) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MSTORE)
      + stackPushCount (.Smsf .MSTORE) > 1024) := by
    simp only [show stackPopCount (.Smsf .MSTORE) = 2 from rfl,
               show stackPushCount (.Smsf .MSTORE) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  unfold charge
  rw [if_neg (by have := hgasMem; dsimp only [memExpansionChargeOf] at this ⊢; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_pos (by have := hoog; dsimp only [memExpansionChargeOf] at this ⊢; omega)]

/-- **MSTORE success-inversion.** A *successful* `.next` MSTORE step witnesses its own
memory-expansion bookkeeping: from `stepFrame fr = .next e` at an MSTORE-decoding frame
with stack `addr :: val :: rest`, there is an expansion witness `words'`
(`memoryExpansionWords? activeWords addr 32 = some words'`), both charges fit
(`memExpansionChargeOf … ≤ gas`, `Gverylow ≤ post-expansion gas`), and the resulting
state is exactly `mstorePost fr.exec addr val words' rest`. Pinning `e = mstorePost …`
exposes the post-state as an MSTORE write at `addr`, so the `MemAlgebra` coverage/readback
lemmas (`mstore_reads_back`, `mstore_memory_size`, `mstore_activeWords_covers`) discharge
the `MemRealises` payload (slot in-bounds + active + readback = stored value) at the
written slot — no longer supplied. The expansion witness `words'` is recovered by case-split
(`none` halts with `OutOfGas`, contradicting `.next`); both charges by the contrapositive of
the forward OOG halts (`stepFrame_mstore_oogMem`/`_oogVL`); and `e = mstorePost …` by the
forward `stepFrame_mstore`. -/
theorem stepFrame_mstore_inv (fr : Frame) (addr val : UInt256) (rest : Stack UInt256)
    {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    ∃ words', memoryExpansionWords? fr.exec.activeWords addr 32 = some words'
      ∧ memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
      ∧ Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      ∧ e = mstorePost fr.exec addr val words' rest := by
  -- the expansion witness `words'`: `none` would halt at `chargeMemExpansion`.
  cases hmem : memoryExpansionWords? fr.exec.activeWords addr 32 with
  | none =>
    -- with no witness, `stepFrame` is the `OutOfGas` halt; contradiction with `.next`.
    exfalso
    rw [stepFrame] at hnext
    simp only [hdec] at hnext
    dsimp only [Option.getD] at hnext
    rw [if_neg (by decide)] at hnext
    have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MSTORE)
        + stackPushCount (.Smsf .MSTORE) > 1024) := by
      simp only [show stackPopCount (.Smsf .MSTORE) = 2 from rfl,
                 show stackPushCount (.Smsf .MSTORE) = 0 from rfl]
      have := hsz; omega
    rw [if_neg hov] at hnext
    dsimp only [dispatch, smsfOp] at hnext
    rw [hstk] at hnext
    dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
      Except.bind, pure, Except.pure] at hnext
    dsimp only [chargeMemExpansion] at hnext
    rw [hmem] at hnext
    exact absurd hnext (by simp)
  | some words' =>
    -- both charges fit (contrapositive of the forward OOG halts).
    have hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat := by
      by_contra h
      rw [stepFrame_mstore_oogMem fr addr val words' rest hdec hstk hsz hmem (by omega)] at hnext
      exact absurd hnext (by simp)
    have hgas : Gverylow ≤
        (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat := by
      by_contra h
      rw [stepFrame_mstore_oogVL fr addr val words' rest hdec hstk hsz hmem hgasMem
            (by omega)] at hnext
      exact absurd hnext (by simp)
    refine ⟨words', rfl, hgasMem, hgas, ?_⟩
    rw [stepFrame_mstore fr addr val words' rest hdec hstk hsz hmem hgasMem hgas] at hnext
    exact (Signal.next.injEq _ _).mp hnext.symm

/-! ## JUMP / JUMPI (control flow)

The conditional/unconditional jumps are the control-flow primitives the CFG
combinator stands on. Both pop their destination off the stack, charge a fixed
gas (`Gmid = 8` for JUMP, `Ghigh = 10` for JUMPI) and — when the destination is a
valid `JUMPDEST` (`fr.get_dest dest = some new_pc`) — set `pc := new_pc` and drop
the consumed operand(s). JUMPI with a zero condition instead falls through to
`pc + 1`. The valid-destination side condition is supplied as the explicit
hypothesis `hdest`; the gas guard is discharged from `hgas`; the overflow guard
from `hsz` (both jumps only ever shrink the stack). These mirror the per-opcode
step lemmas above; they are low-level bricks (they mention `pc`/`stack`/gas).

Unlike PUSH/SSTORE the post-state is not `replaceStackAndIncrPC` — JUMP writes
`pc` directly — so the result is spelled out inline with the charged gas. -/

/-- The execution state JUMP / a taken JUMPI leaves: gas charged by `cost`, `pc`
set to the resolved `new_pc`, and the consumed operand(s) popped to `rest`. -/
def jumpPost (exec : ExecutionState) (cost : ℕ) (new_pc : UInt32) (rest : Stack UInt256) :
    ExecutionState :=
  { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat cost, pc := new_pc, stack := rest }

/-- The execution state a *not-taken* JUMPI leaves: gas charged `Ghigh`, `pc`
advanced by one, and `dest`/`cond` popped to `rest`. -/
def jumpiFallthroughPost (exec : ExecutionState) (rest : Stack UInt256) : ExecutionState :=
  { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat Ghigh, pc := exec.pc + 1, stack := rest }

/-- **JUMP to a valid destination sets pc to `new_pc`**, charging `Gmid = 8` and
popping the destination operand. The valid-destination requirement is the
explicit `hdest : fr.get_dest dest = some new_pc`; the gas/overflow guards are
discharged from `hgas`/`hsz`. -/
theorem stepFrame_jump (fr : Frame) (dest : UInt256) (new_pc : UInt32) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMP, .none))
    (hstk : fr.exec.stack = dest :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gmid ≤ fr.exec.gasAvailable.toNat)
    (hdest : fr.get_dest dest = some new_pc) :
    stepFrame fr = .next (jumpPost fr.exec Gmid new_pc rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMP)
      + stackPushCount (.Smsf .JUMP) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMP) = 1 from rfl,
               show stackPushCount (.Smsf .JUMP) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_neg (by omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  rw [hdest]
  rfl

/-- **JUMPI with a non-zero condition jumps to a valid destination**, charging
`Ghigh = 10` and popping both operands. The valid-destination requirement is
`hdest`; `hcond : cond ≠ 0` selects the taken branch; gas/overflow from
`hgas`/`hsz`. -/
theorem stepFrame_jumpi_taken (fr : Frame) (dest cond : UInt256) (new_pc : UInt32)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: cond :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Ghigh ≤ fr.exec.gasAvailable.toNat)
    (hcond : cond ≠ 0)
    (hdest : fr.get_dest dest = some new_pc) :
    stepFrame fr = .next (jumpPost fr.exec Ghigh new_pc rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMPI)
      + stackPushCount (.Smsf .JUMPI) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMPI) = 2 from rfl,
               show stackPushCount (.Smsf .JUMPI) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_neg (by omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  have hcz : (cond == (0 : UInt256)) = false := by
    rw [Bool.eq_false_iff]
    intro hc; exact hcond ((UInt256.beq_iff_eq cond 0).mp hc)
  rw [if_pos (by show (cond != 0) = true; rw [bne, hcz]; rfl)]
  rw [hdest]
  rfl

/-- **JUMPI with a zero condition falls through to pc + 1**, charging `Ghigh`
and popping both operands. No destination requirement (the jump is not taken);
gas/overflow from `hgas`/`hsz`. -/
theorem stepFrame_jumpi_fallthrough (fr : Frame) (dest : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: (0 : UInt256) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Ghigh ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (jumpiFallthroughPost fr.exec rest) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMPI)
      + stackPushCount (.Smsf .JUMPI) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMPI) = 2 from rfl,
               show stackPushCount (.Smsf .JUMPI) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_neg (by omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  rw [if_neg (by decide)]
  rfl

/-- The execution state JUMPDEST leaves: gas charged `Gjumpdest = 1`, pc advanced
by one, stack unchanged. JUMPDEST is the no-op landing pad every jump target is. -/
def jumpdestPost (exec : ExecutionState) : ExecutionState :=
  ({ exec with gasAvailable := exec.gasAvailable - UInt64.ofNat Gjumpdest }).incrPC

/-- **JUMPDEST advances pc by one**, charging `Gjumpdest = 1` and leaving the stack
untouched. The landing-pad opcode every valid jump target carries; lifted so a
taken jump can step past its target. Gas from `hgas`, overflow from `hsz`. -/
theorem stepFrame_jumpdest (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Gjumpdest ≤ fr.exec.gasAvailable.toNat) :
    stepFrame fr = .next (jumpdestPost fr.exec) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMPDEST)
      + stackPushCount (.Smsf .JUMPDEST) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMPDEST) = 0 from rfl,
               show stackPushCount (.Smsf .JUMPDEST) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_neg (by omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rfl

/-! ## RETURN (empty output)

The first opcode with a *return-data* observable. `RETURN` pops `offset`/`size`,
charges memory expansion, and halts with `.success` carrying the bytes read from
memory. For the zero-size case (`offset = size = 0`) the memory charge is `0`
(`Cₘ activeWords - Cₘ activeWords`) and the output is empty (`readWithPadding _ 0`),
so the step is unconditional — no gas hypothesis. This is the brick the
`RETURN` instances stand on. -/

/-- The execution state RETURN leaves before halting (empty `offset = size = 0`):
the size-0 memory charge (`- ofNat 0`, a no-op on gas), the active-words bump, and
the popped stack. -/
def returnEmptyPost (exec : ExecutionState) (rest : Stack UInt256) : ExecutionState :=
  let charged : ExecutionState := { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat 0 }
  ExecutionState.replaceStackAndIncrPC
    { charged with
        toMachineState :=
          { charged.toMachineState with
              activeWords := MachineState.M charged.activeWords (0 : UInt256).toUInt64 (0 : UInt256).toUInt64 } }
    rest

/-- **RETURN with zero size halts successfully, returning the read bytes.** At a pc
decoding to `RETURN` with `0`/`0` (offset/size) on top of the stack, `stepFrame`
halts with `.success (returnEmptyPost …) (memory.readWithPadding 0 0)`: the
zero-size memory charge is `0`, so no gas hypothesis is needed; only the
stack-overflow guard (discharged from `hsz`). For a frame with empty memory the
returned bytes reduce to `.empty` — the return-data observable the rung lands on. -/
theorem stepFrame_return_empty (fr : Frame) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .RETURN, .none))
    (hstk : fr.exec.stack = (0 : UInt256) :: (0 : UInt256) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success (returnEmptyPost fr.exec rest)
      (fr.exec.memory.readWithPadding (0 : UInt256).toNat (0 : UInt256).toNat)) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.System .RETURN)
      + stackPushCount (.System .RETURN) > 1024) := by
    simp only [show stackPopCount (.System .RETURN) = 2 from rfl,
               show stackPushCount (.System .RETURN) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, systemOp, haltOp, returnOrRevertOp]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion, memoryExpansionWords?]
  -- size = 0 branch of `memoryExpansionWords?` and the `Cₘ - Cₘ = 0` charge.
  rw [if_pos (by decide)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  unfold charge
  rw [if_neg (by simp)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg (by decide)]
  dsimp only [returnEmptyPost]
  rw [Nat.sub_self]

/-! ## `stepFrame` inversion: bridging the `Signal` to `systemOp`

`stepFrame fr` decodes `(op, arg)`, screens `INVALID`/overflow (both `.halted`),
then maps `dispatch op arg fr fr.exec`. A `.needsCall`/`.needsCreate`/(System)
`.next` signal therefore comes from `dispatch op arg fr fr.exec = .ok (that
signal)` with `op = .System s`, and `dispatch (.System s) … = systemOp s …`.

The non-`System` dispatcher arms only ever emit `.next` (`continueWith`) on
success, so they cannot emit `.needsCall`/`.needsCreate`. We capture that with
`onlyNext`, mirroring `neverHalts`. -/

/-- A `Step` whose every `.ok` output is a `.next`. -/
def onlyNext (s : Step) : Prop := ∀ sig, s = .ok sig → ∃ e, sig = .next e

theorem onlyNext_continueWith (e : ExecutionState) : onlyNext (continueWith e) := by
  intro sig he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨e, he.symm⟩
theorem onlyNext_error (e : ExecutionException) : onlyNext (.error e : Step) := by
  intro sig he; simp at he
theorem onlyNext_throw (e : ExecutionException) : onlyNext (throw e : Step) := by
  intro sig he; simp [throw, throwThe, MonadExceptOf.throw] at he
theorem onlyNext_bind_except {α : Type} (m : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, m = .ok a → onlyNext (k a)) : onlyNext (m >>= k) := by
  intro sig he
  cases hm : m with
  | error e => rw [hm] at he; simp [bind, Except.bind] at he
  | ok a => rw [hm] at he; simp only [bind, Except.bind] at he; exact hk a hm sig he
theorem onlyNext_optionBind {α : Type} (o : Option α) (k : α → Step)
    (hk : ∀ a, o = some a → onlyNext (k a)) :
    onlyNext ((o : Except ExecutionException α) >>= k) := by
  intro sig he
  cases ho : o with
  | none => rw [ho] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
  | some a =>
    rw [ho] at he; simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    exact hk a ho sig he
theorem onlyNext_chargeBind {cost : ℕ} {exec : ExecutionState} {k : ExecutionState → Step}
    (hk : ∀ ec, charge cost exec = .ok ec → onlyNext (k ec)) :
    onlyNext (charge cost exec >>= k) :=
  onlyNext_bind_except _ _ hk
theorem onlyNext_memChargeBind {exec : ExecutionState} {off size : UInt256}
    {k : ExecutionState → Step} (hk : ∀ ec, onlyNext (k ec)) :
    onlyNext (chargeMemExpansion exec off size >>= k) := by
  apply onlyNext_bind_except; intro a _; exact hk a

theorem unOp_onlyNext {f : UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (unOp f exec cost) := by
  rw [unOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a⟩ _; exact onlyNext_continueWith _
theorem binOp_onlyNext {f : UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (binOp f exec cost) := by
  rw [binOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _; exact onlyNext_continueWith _
theorem ternOp_onlyNext {f : UInt256 → UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (ternOp f exec cost) := by
  rw [ternOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _; exact onlyNext_continueWith _
theorem pushOp_onlyNext {v : ExecutionState → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (pushOp v exec cost) := by
  rw [pushOp]; apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
theorem unStateOp_onlyNext {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec : ExecutionState} :
    onlyNext (unStateOp f cost exec) := by
  rw [unStateOp]; apply onlyNext_optionBind; rintro ⟨s, a⟩ _
  apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
theorem dup_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (dup n exec) := by
  rw [dup]; apply onlyNext_chargeBind; intro ec _ sig he
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v => rw [hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
theorem swap_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (swap n exec) := by
  rw [swap]; apply onlyNext_chargeBind; intro ec _ sig he
  by_cases hg : List.length (ec.stack.take (n + 1)) = (n + 1)
  · rw [if_pos hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
  · rw [if_neg hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
theorem logArm_onlyNext {exec : ExecutionState} {stack : Stack UInt256}
    {offset size : UInt256} {topics : Array UInt256} :
    onlyNext (logArm exec stack offset size topics) := by
  rw [logArm]; apply onlyNext_bind_except; intro _ _
  apply onlyNext_memChargeBind; intro ec
  apply onlyNext_chargeBind; intro ec2 _; exact onlyNext_continueWith _
theorem smsfOp_onlyNext {op : Operation.SmsfOp} {fr : Frame} {exec : ExecutionState} :
    onlyNext (smsfOp op fr exec) := by
  unfold smsfOp
  cases op with
  | POP =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, a⟩ _; exact onlyNext_continueWith _
  | MLOAD =>
    apply onlyNext_optionBind; rintro ⟨s, a⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | MSTORE =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | MSTORE8 =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | SLOAD => exact unStateOp_onlyNext
  | SSTORE =>
    apply onlyNext_bind_except; intro _ _
    by_cases hg : exec.gasAvailable.toNat ≤ Gcallstipend
    · simp only [hg, if_true]; exact onlyNext_throw _
    · simp only [hg, if_false]
      apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
      apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
  | TLOAD => exact unStateOp_onlyNext
  | TSTORE =>
    apply onlyNext_bind_except; intro _ _
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _; exact onlyNext_continueWith _
  | MSIZE => exact pushOp_onlyNext
  | GAS => exact pushOp_onlyNext
  | JUMP =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, d⟩ _ sig he
    dsimp only at he
    split at he
    · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
    · simp at he
  | JUMPI =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, d, c⟩ _ sig he
    dsimp only at he
    split at he
    · split at he
      · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
      · simp at he
    · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
  | PC => exact pushOp_onlyNext
  | JUMPDEST =>
    apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
  | MCOPY =>
    apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _

/-- The non-`System` dispatcher arms only emit `.next`. -/
theorem dispatch_onlyNext {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec : ExecutionState} (hne : ∀ s, op ≠ .System s) :
    onlyNext (dispatch op arg fr exec) := by
  unfold dispatch
  cases op with
  | System s => exact absurd rfl (hne s)
  | KECCAK256 =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | Smsf s => exact smsfOp_onlyNext
  | Log l => cases l <;>
      (apply onlyNext_optionBind; rintro _ _; exact logArm_onlyNext)
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_onlyNext
    | _ =>
      apply onlyNext_chargeBind; intro ec _ sig he
      cases arg <;>
        first
          | (simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩)
          | simp [throw, throwThe, MonadExceptOf.throw] at he
  | Dup d => exact dup_onlyNext
  | Swap s => exact swap_onlyNext
  | ArithLogic a => cases a <;>
      first
        | exact binOp_onlyNext | exact unOp_onlyNext | exact ternOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
           apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _)
  | Env e =>
    cases e <;>
      first
        | exact pushOp_onlyNext | exact unStateOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _
           apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
           exact onlyNext_continueWith _)
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _ sig he
           revert he; dsimp only; split
           · intro he; simp [bind, Except.bind] at he
           · exact (onlyNext_memChargeBind (k := _)
               (fun ec => onlyNext_chargeBind (fun ec2 _ => onlyNext_continueWith _)) sig))
  | Block b =>
    cases b <;>
      first
        | exact pushOp_onlyNext | exact unStateOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, i⟩ _
           apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _)

/-- Bridge: a non-`.next` `Signal` from a successful `dispatch` forces `op` to be
a `System` op. -/
theorem dispatch_ok_System_of_not_next {op : Operation} {arg : Option (UInt256 × UInt8)}
    {fr : Frame} {exec : ExecutionState} {sig : Signal}
    (hdisp : dispatch op arg fr exec = .ok sig) (hnn : ∀ e, sig ≠ .next e) :
    ∃ s, op = .System s := by
  by_cases hsys : ∃ s, op = .System s
  · exact hsys
  · push Not at hsys
    obtain ⟨e, he⟩ := dispatch_onlyNext hsys sig hdisp
    exact absurd he (hnn e)

/-- The shared `stepFrame`→`dispatch` skeleton. A non-`.halted` `Signal` from
`stepFrame fr` is exactly that `Signal` from `dispatch op arg fr fr.exec` on the
decoded `(op, arg)` — the INVALID/overflow screens and the error arm all produce
`.halted`, so they are excluded. The three public bridges are thin wrappers. -/
private theorem stepFrame_dispatch {fr : Frame} {sig : Signal}
    (h : stepFrame fr = sig) (hnh : ∀ hl, sig ≠ .halted hl) :
    dispatch (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
        (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).2
        fr fr.exec = .ok sig := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h ⊢
  obtain ⟨op, arg⟩ := dp
  simp only at h ⊢
  split at h
  · exact absurd h.symm (hnh _)
  · split at h
    · exact absurd h.symm (hnh _)
    · cases hdisp : dispatch op arg fr fr.exec with
      | error e => rw [hdisp] at h; exact absurd h.symm (hnh _)
      | ok signal =>
        rw [hdisp] at h
        have h' : signal = sig := h
        rw [h']

/-- A `.needsCall` from `stepFrame` is a `.needsCall` from `systemOp s fr fr.exec`. -/
theorem stepFrame_needsCall_systemOp {fr : Frame} {p : CallParams} {pd : PendingCall}
    (h : stepFrame fr = .needsCall p pd) :
    ∃ s, systemOp s fr fr.exec = .ok (.needsCall p pd) := by
  have hdisp := stepFrame_dispatch h (by simp)
  obtain ⟨s, hs⟩ := dispatch_ok_System_of_not_next hdisp (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact ⟨s, hdisp⟩

/-- A `.needsCreate` from `stepFrame` is a `.needsCreate` from `systemOp s fr fr.exec`. -/
theorem stepFrame_needsCreate_systemOp {fr : Frame} {cp : CreateParams} {pd : PendingCreate}
    (h : stepFrame fr = .needsCreate cp pd) :
    ∃ s, systemOp s fr fr.exec = .ok (.needsCreate cp pd) := by
  have hdisp := stepFrame_dispatch h (by simp)
  obtain ⟨s, hs⟩ := dispatch_ok_System_of_not_next hdisp (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact ⟨s, hdisp⟩

/-- A `.needsCreate` at a known decoded system operation comes from that operation's
`systemOp` arm. -/
theorem stepFrame_needsCreate_systemOp_of_decode {fr : Frame} {cp : CreateParams}
    {pd : PendingCreate} {s : Operation.SystemOp}
    (hs : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = .System s)
    (h : stepFrame fr = .needsCreate cp pd) :
    systemOp s fr fr.exec = .ok (.needsCreate cp pd) := by
  have hdisp := stepFrame_dispatch h (by simp)
  rw [hs] at hdisp
  rw [dispatch] at hdisp
  exact hdisp

/-- A `System`-op `.next` from `stepFrame`: when the decoded op is a `System` op
and `stepFrame` is `.next exec'`, that `.next` comes from `systemOp s fr fr.exec`. -/
theorem stepFrame_next_systemOp {fr : Frame} {exec' : ExecutionState} {s : Operation.SystemOp}
    (hs : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s)
    (h : stepFrame fr = .next exec') :
    systemOp s fr fr.exec = .ok (.next exec') := by
  have hdisp := stepFrame_dispatch h (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact hdisp

end BytecodeLayer.Dispatch
