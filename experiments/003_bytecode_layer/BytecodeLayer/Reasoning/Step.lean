import Evm

/-!
# Step characterization (proof-internal)

`stepFrame` equations for the opcodes the capstones execute. Each says: at a pc
where the code decodes to this opcode, with enough gas and stack room, the step
is exactly the obvious result — no `OutOfGas`, no `StackOverflow`, no decode
failure. This is the *vacuity-propagation* discipline made concrete: the gas and
overflow guards are discharged once, here, as `if_neg`s from explicit
hypotheses, and never reappear.

These are low-level on purpose (they mention `pc`, `stack`, `gasAvailable`);
they are internal bricks, not exports.
-/

namespace BytecodeLayer
open Evm
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 1000000 in
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

set_option maxHeartbeats 2000000 in
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

set_option maxHeartbeats 2000000 in
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

set_option maxHeartbeats 2000000 in
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

end BytecodeLayer
