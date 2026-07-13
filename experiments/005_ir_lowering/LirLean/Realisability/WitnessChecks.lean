import LirLean.Realisability.CheckedStep

/-!
# LirLean — Realisability spec, THE TWO R12a LEAVES (kernel-certified)

The in-kernel discharge of the two `Bool` leaves `exProg_satisfies_hypotheses_of_checks`
consumes — the residue `WitnessParams.lean`'s module header measured as infeasible for
plain `decide` on the raw evaluators. The route (per `SegmentedEval.lean` +
`CheckedStep.lean`): each leaf is restated over the CHECKED transition iterator
(`exCheckChk`, `ccCheckChk`), closed by ONE `decide +kernel` evaluation (measured ~13s /
5.5 GB each — the checked twin never touches the `USize`-opaque byte-window path and
never peels the 54096 seed fuel), then transported to the real leaf by the sorry-free
soundness + fuel-shift chain:

* `stepsLogChk_sound` / `stepsCCChk_sound` — the checked chain's verdict IS the real
  chain's (`stepsLog` / `stepsCC`);
* `driveLogC_final` / `callsCodeOk_final` — a `k`-transition terminal verdict decides
  the fuel-indexed evaluator at ANY fuel `≥ k + 1`; the witness runs in `39`
  (`driveLog`, seed fuel `54096 = 39 + 54056 + 1`) and `36` (`callsCodeOk`, fuel
  `4096 = 36 + 4059 + 1`) transitions (re-measured by native probe against the
  current lowering; identical to the original measurement).

**KERNEL CRANKS (flagged per the R12a protocol): THREE `decide +kernel` evaluations
in this module** — the two heavy leaf cranks `exCheckChk_true` and `ccCheckChk_true`
(`maxRecDepth 100000`; ~13s / 5.5 GB each) plus the cheap seed-fuel arithmetic pin
`seedFuel_exParams` (a `UInt64.toNat` literal computation). No `native_decide`
anywhere. All three are kernel evaluations of closed decidable terms; `#print axioms`
on the final leaves reports only the standard trio via the bridge lemmas' `Classical`
uses.
-/

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

/-! ## §1 — the checked leaf surfaces -/

/-- `exCheck` restated over the checked iterator: the recorded run reaches a terminal
result within 39 transitions and it is clean (`success ∨ gasRemaining ≠ 0`). -/
def exCheckChk : Bool :=
  match Evm.beginCall exParams with
    | .inr _ => false
    | .inl fr₀ =>
      match stepsLogChk 39 ⟨[], .inl fr₀, [], [], [], []⟩ with
        | some (.inr (res, _, _, _, _)) =>
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

/-! ## §2 — the two heavy kernel cranks -/

set_option maxRecDepth 100000 in
/-- **KERNEL CRANK 1 of 3** (heavy: ~13s / 5.5 GB): the checked recorded-run leaf. -/
theorem exCheckChk_true : exCheckChk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **KERNEL CRANK 2 of 3** (heavy: ~13s / 5.5 GB): the checked `CallsCode` trace leaf. -/
theorem ccCheckChk_true : ccCheckChk = true := by decide +kernel

/-! ## §3 — transport to the real leaves -/

/-- **KERNEL CRANK 3 of 3** (cheap): the seed-fuel arithmetic pin for the witness
(`2 * 25000 + 4096 = 54096 = 39 + 54056 + 1`, a `UInt64.toNat` literal evaluation). -/
theorem seedFuel_exParams : seedFuel exParams.gas = 39 + 54056 + 1 := by
  decide +kernel

/-- **R12a leaf 1 of 2, DISCHARGED**: the recorded run exists and is clean. -/
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
    cases hchk : stepsLogChk 39 ⟨[], .inl fr₀, [], [], [], []⟩ with
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
        obtain ⟨r, gasAcc, sloadAcc, callAcc, createAcc⟩ := res
        dsimp only [] at h
        have hsteps : stepsLog 39 ⟨[], .inl fr₀, [], [], [], []⟩ =
            .inr (r, gasAcc, sloadAcc, callAcc, createAcc) := stepsLogChk_sound hchk
        have hdrv : driveLog (seedFuel exParams.gas) [] (.inl fr₀) [] [] [] [] =
            .ok (r, gasAcc, sloadAcc, callAcc, createAcc) := by
          rw [seedFuel_exParams]
          exact driveLogC_final hsteps 54056
        dsimp only []
        rw [hdrv]
        dsimp only []
        unfold RunLog.cleanb
        exact h

/-- **R12a leaf 2 of 2, DISCHARGED**: the `CallsCode`/`createResolves` trace check. -/
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
