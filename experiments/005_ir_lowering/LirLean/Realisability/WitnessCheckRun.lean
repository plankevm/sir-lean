import LirLean.Realisability.WitnessCheckDefs

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

set_option maxRecDepth 100000 in
/-- Kernel evaluation of the checked recorded-run leaf. -/
theorem exCheckChk_true : exCheckChk = true := by decide +kernel

/-- The seed-fuel arithmetic pin for the witness. -/
theorem seedFuel_exParams : seedFuel exParams.gas = 39 + 54056 + 1 := by
  decide +kernel

/-- The recorded run exists and is clean. -/
theorem exCheck_true : exCheck = true := by
  have h := exCheckChk_true
  unfold exCheckChk at h
  unfold exCheck runWithLog
  cases hbeg : Evm.beginCall exParams with
  | inr r =>
    rw [hbeg] at h
    cases h
  | inl fr₀ =>
    rw [hbeg] at h
    dsimp only [] at h
    cases hchk : stepsLogChk 39 ⟨[], .inl fr₀, [], [], []⟩ with
    | none =>
      rw [hchk] at h
      cases h
    | some x =>
      rw [hchk] at h
      cases x with
      | inl c' =>
        dsimp only [] at h
        cases h
      | inr res =>
        obtain ⟨r, gasAcc, callAcc, createAcc⟩ := res
        dsimp only [] at h
        have hsteps : stepsLog 39 ⟨[], .inl fr₀, [], [], []⟩ =
            .inr (r, gasAcc, callAcc, createAcc) := stepsLogChk_sound hchk
        have hdrv : driveLog (seedFuel exParams.gas) [] (.inl fr₀) [] [] [] =
            .ok (r, gasAcc, callAcc, createAcc) := by
          rw [seedFuel_exParams]
          exact driveLogC_final hsteps 54056
        dsimp only []
        rw [hdrv]
        dsimp only []
        unfold BytecodeLayer.Exec.Recorder.RunLog.cleanb
        exact h

end Lir
