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

end BytecodeLayer
