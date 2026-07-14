import BytecodeLayer.Exec.Modellable
import LirLean.Decode.BoundaryReach

/-!
# Reachable boundaries in lowered code

This module retains the IR-specific code-and-program-counter tether. -/

namespace BytecodeLayer.Interpreter

open Evm
/-- **`AtReachableBoundary prog fr`** — the structural-reachability premise: `fr` runs
`lower prog` and its current pc is an instruction boundary reachable from the program start,
strictly before the program end and within the `UInt32` address space. -/
def AtReachableBoundary (prog : Lir.Program) (fr : Frame) : Prop :=
  ∃ boundary : Nat,
    fr.exec.executionEnv.code = Lir.lower prog
    ∧ fr.exec.pc = UInt32.ofNat boundary
    ∧ Evm.ReachesBoundary (Lir.lower prog) 0 boundary
    ∧ boundary < (Lir.flatBytes prog).length
    ∧ boundary < 2 ^ 32


end BytecodeLayer.Interpreter
