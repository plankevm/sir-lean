import Evm
import BytecodeLayer.Reasoning.Drive

/-!
# Fuel monotonicity of `drive`

`drive` recurses on `fuel`. These are the fuel-monotonicity bricks: once a run
has produced *any* answer other than `OutOfFuel`, giving it more fuel changes
nothing. They are fuel-level facts (they mention `drive`, `Pending`, `Frame ⊕
FrameResult`) and live in `Reasoning/`.
-/

namespace BytecodeLayer
open Evm

/-- **One-step fuel monotonicity of `drive`.** If `drive` at fuel `f` does not
bottom out on fuel (its result is *not* `OutOfFuel`), then one extra unit of fuel
yields the *same* result. Proved by induction on `f`, following `drive`'s own
recursion: in every branch `drive (f+1) …` reduces to a recursive call at fuel
`f` (to which the IH applies, its non-`OutOfFuel` hypothesis inherited from the
assumption on `drive (f+1)`), and the single terminal branch returns the same
`.ok result` at both `f+1` and `f+2`. The `f = 0` case is vacuous: `drive 0` *is*
`OutOfFuel`. -/
theorem drive_fuel_succ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
    (h : drive f stack state ≠ .error .OutOfFuel) :
    drive (f + 1) stack state = drive f stack state := by
  induction f generalizing stack state with
  | zero => simp [drive] at h
  | succ n ih =>
    -- Unfold the outer `drive (n+2)` and `drive (n+1)` one layer; they share the
    -- same case split, each recursive branch dropping fuel by one. In every
    -- recursive arm the goal becomes `drive (n+1) s' t' = drive n s' t'`, closed by
    -- `ih` once the inherited non-`OutOfFuel` hypothesis (the same arm of the
    -- unfolded `h`) is supplied; the lone terminal arm (`.inr` with empty stack)
    -- returns the same `.ok result` at both fuels (`rfl`).
    conv_lhs => unfold drive
    conv_rhs => unfold drive
    unfold drive at h
    cases state with
    | inr result =>
      cases stack with
      | nil => rfl
      | cons pending rest =>
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent => rw [hres] at h; dsimp only at h ⊢; exact ih rest (.inl parent) h
        | error e =>
          rw [hres] at h; dsimp only at h ⊢
          exact ih rest (.inr (endFrame pending.frame (.exception e))) h
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec => rw [hstep] at h; dsimp only at h ⊢; exact ih stack (.inl { current with exec := exec }) h
      | halted halt => rw [hstep] at h; dsimp only at h ⊢; exact ih stack (.inr (endFrame current halt)) h
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h ⊢
        cases hbc : beginCall params with
        | inl child => rw [hbc] at h; dsimp only at h ⊢; exact ih (.call pending :: stack) (.inl child) h
        | inr result => rw [hbc] at h; dsimp only at h ⊢; exact ih (.call pending :: stack) (.inr (.call result)) h
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h ⊢
        cases hbcr : beginCreate params with
        | ok child => rw [hbcr] at h; dsimp only at h ⊢; exact ih (.create pending :: stack) (.inl child) h
        | error e => rw [hbcr] at h; dsimp only at h ⊢; exact ih (.create pending :: stack) (.inr (.create _)) h

/-- **Fuel monotonicity of `drive`.** If a run halts within fuel `f` (does not
return `OutOfFuel`), then it halts to the **same** result at every larger fuel
`f'`. Iterating `drive_fuel_succ` along `f ≤ f'`. -/
theorem drive_fuel_mono {f f' : ℕ} (hle : f ≤ f')
    (stack : List Pending) (state : Frame ⊕ FrameResult)
    (h : drive f stack state ≠ .error .OutOfFuel) :
    drive f' stack state = drive f stack state := by
  induction hle with
  | refl => rfl
  | step _ ih => rw [drive_fuel_succ _ stack state (h := by rw [ih]; exact h), ih]

/-- The non-`OutOfFuel` answer is itself preserved upward: from `drive f … ≠
OutOfFuel` and `f ≤ f'`, `drive f' …` is also `≠ OutOfFuel`. A direct corollary of
`drive_fuel_mono` — the budget-sufficiency fact the capstones want phrased as a
disequation. -/
theorem drive_not_outOfFuel_mono {f f' : ℕ} (hle : f ≤ f')
    (stack : List Pending) (state : Frame ⊕ FrameResult)
    (h : drive f stack state ≠ .error .OutOfFuel) :
    drive f' stack state ≠ .error .OutOfFuel := by
  rw [drive_fuel_mono hle stack state h]; exact h

end BytecodeLayer
