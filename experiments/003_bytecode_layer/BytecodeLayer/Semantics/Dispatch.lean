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
  rw [dup]; apply onlyNext_chargeBind; intro ec _
  intro sig he
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v => rw [hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
theorem swap_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (swap n exec) := by
  rw [swap]; apply onlyNext_chargeBind; intro ec _
  intro sig he
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
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c, d⟩ _
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

/-- A `System`-op `.next` from `stepFrame`: when the decoded op is a `System` op
and `stepFrame` is `.next exec'`, that `.next` comes from `systemOp s fr fr.exec`. -/
theorem stepFrame_next_systemOp {fr : Frame} {exec' : ExecutionState} {s : Operation.SystemOp}
    (hs : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s)
    (h : stepFrame fr = .next exec') :
    systemOp s fr fr.exec = .ok (.next exec') := by
  have hdisp := stepFrame_dispatch h (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact hdisp

end BytecodeLayer.Dispatch
