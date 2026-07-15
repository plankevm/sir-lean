import LirLean.Realisability.WitnessCheckRun

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

set_option maxRecDepth 100000 in
/-- Kernel evaluation of the checked `CallsCode` trace leaf. -/
theorem ccCheckChk_true : ccCheckChk = true := by decide +kernel

/-- The `CallsCode`/`createResolves` trace check. -/
theorem entryCallsCodeOk_exParams : entryCallsCodeOk exParams 4096 = true := by
  have h := ccCheckChk_true
  unfold ccCheckChk at h
  unfold entryCallsCodeOk
  cases hbeg : Evm.beginCall exParams with
  | inr r => rfl
  | inl fr₀ =>
    rw [hbeg] at h
    dsimp only [] at h
    cases hchk : stepsCCChk 36 fr₀ with
    | none =>
      rw [hchk] at h
      cases h
    | some x =>
      rw [hchk] at h
      cases x with
      | inl fr' =>
        dsimp only [] at h
        cases h
      | inr b =>
        dsimp only [] at h
        have hcc : stepsCC 36 fr₀ = .inr b := stepsCCChk_sound hchk
        have hfin := callsCodeOk_final hcc 4059
        show callsCodeOk 4096 fr₀ = true
        have hfuel : (4096 : ℕ) = 36 + 4059 + 1 := by norm_num
        rw [hfuel, hfin, h]

end Lir
