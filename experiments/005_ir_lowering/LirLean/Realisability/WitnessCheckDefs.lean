import LirLean.Realisability.CheckedStep

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

/-- `exCheck` restated over the checked iterator: the recorded run reaches a terminal
result within 39 transitions and it is clean (`success ∨ gasRemaining ≠ 0`). -/
def exCheckChk : Bool :=
  match Evm.beginCall exParams with
    | .inr _ => false
    | .inl fr₀ =>
      match stepsLogChk 39 ⟨[], .inl fr₀, [], [], []⟩ with
        | some (.inr (res, _, _, _)) =>
          (match res with
            | .call r => r.success || r.gasRemaining != 0
            | .create _ => false)
        | _ => false

/-- `entryCallsCodeOk exParams` restated over the checked iterator: the checker's
replay reaches a verdict within 36 transitions and it is `true`. -/
def ccCheckChk : Bool :=
  match Evm.beginCall exParams with
    | .inr _ => true
    | .inl fr₀ =>
      match stepsCCChk 36 fr₀ with
        | some (.inr b) => b
        | _ => false

end Lir
