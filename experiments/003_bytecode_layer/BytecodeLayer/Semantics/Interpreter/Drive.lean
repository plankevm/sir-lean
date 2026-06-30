import Evm

/-!
# `drive` vocabulary and fuel monotonicity (interpreter-internal)

This file collects the low-level `drive` bricks of the interpreter argument,
merged from the former `Reasoning/{Drive, DriveGen, Fuel}.lean`:

* **Top-level drive vocabulary** (`drive_step`, `drive_halt`, `two_le_seedFuel`,
  `messageCall_eq_drive`) — the two `drive` equations used to thread a top-level
  execution one signal at a time, specialised to the empty pending-stack `[]` (a
  top-level `messageCall` starts with no suspended ancestors).

* **Generalized drive vocabulary** (`driveG_step`, `driveG_halt_callDeliver`,
  `driveG_needsCall_code`) — the same `drive` `match`-equations but over an
  **arbitrary** suspended-ancestor stack `ps`, needed by the external-call rung
  where a running child sits on the parent as a `Pending`.

* **Fuel monotonicity** (`drive_fuel_succ`, `drive_fuel_mono`,
  `drive_not_outOfFuel_mono`) — once a run has produced *any* answer other than
  `OutOfFuel`, giving it more fuel changes nothing.

These are all *internal* bricks (they mention `Frame`, fuel, `Sum`, `Pending`);
they exist only to let the capstones reduce `messageCall` without ever exposing
fuel or frames in an exported statement.
-/

namespace BytecodeLayer.Interpreter
open Evm

/-- A `drive` state that is still executing a frame. -/
abbrev running (fr : Frame) : Frame ⊕ FrameResult := .inl fr

/-- A `drive` state that has finished with a result. -/
abbrev finished (res : FrameResult) : Frame ⊕ FrameResult := .inr res

/-! ## Top-level drive vocabulary

Both equations are pure rewrites of `drive`'s own defining `match`, specialised
to the empty pending-stack `[]` (a top-level `messageCall` starts with no
suspended ancestors). -/

/-- One non-halting instruction: consume one unit of fuel and advance the frame.
`drive` re-enters on the updated frame with the *same* (empty) pending stack. -/
theorem drive_step (n : ℕ) (current : Frame) (exec' : ExecutionState)
    (hstep : stepFrame current = .next exec') :
    drive (n + 1) [] (running current) = drive n [] (running { current with exec := exec' }) := by
  conv_lhs => unfold drive
  dsimp only
  rw [hstep]

/-- A halting instruction at the top level: the frame ends and, with no
suspended ancestors, the driver returns the frame's result. Two units of fuel:
one to take the halting step, one to deliver the `.inr` result through the empty
stack. -/
theorem drive_halt (n : ℕ) (current : Frame) (halt : FrameHalt)
    (hstep : stepFrame current = .halted halt) :
    drive (n + 2) [] (running current) = .ok (endFrame current halt) := by
  unfold drive
  dsimp only
  rw [hstep]
  rfl

/-- `seedFuel` is always at least 2 — enough to take one halting step and
deliver its result. Used to peel `seedFuel g = (seedFuel g - 2) + 2` so
`drive_halt` applies to the fuel `messageCall` actually seeds. -/
theorem two_le_seedFuel (g : UInt64) : 2 ≤ seedFuel g := by
  unfold seedFuel; omega

/-- **The `messageCall` entry characterization.** When a call begins as a frame
(`beginCall p = .inl frame`, i.e. EVM code must run), `messageCall p` is exactly
the driver run on that frame, seeded from the gas. This is the single bridge that
lets every capstone proof start from `drive` **without unfolding `messageCall`**;
the frame is supplied by a `beginCall_*` characterization lemma. -/
theorem messageCall_eq_drive (p : CallParams) (frame : Frame)
    (h : beginCall p = .inl frame) :
    messageCall p = (FrameResult.toCallResult <$> drive (seedFuel p.gas) [] (running frame)) := by
  unfold messageCall
  rw [h]

/-! ## Generalized drive vocabulary

`drive_step`/`drive_halt` specialise `drive` to the empty pending-stack `[]` that
a *top-level* `messageCall` starts with. The external-call rung needs the *same*
`drive` equations but with an **arbitrary** suspended-ancestor stack `ps`,
because while the child call runs the parent sits on that stack as a `Pending`. -/

/-- One non-halting instruction under an arbitrary suspended stack `ps`. -/
theorem driveG_step (n : ℕ) (ps : List Pending) (current : Frame) (exec' : ExecutionState)
    (hstep : stepFrame current = .next exec') :
    drive (n + 1) ps (running current) = drive n ps (running { current with exec := exec' }) := by
  conv_lhs => unfold drive
  dsimp only
  rw [hstep]

/-- A `.call`-kind frame halts with `halt`, and its `endFrame`/`endCall` result is
delivered to a suspended `.call` ancestor `pd` on top of the stack: the ancestor
resumes via `resumeAfterCall` and `drive` continues on the resumed parent. Three
fuel units: the halting step, the fold of the result into the stack, and the
resume. -/
theorem driveG_halt_callDeliver (n : ℕ) (ps : List Pending) (current : Frame)
    (pd : PendingCall) (halt : FrameHalt)
    (hstep : stepFrame current = .halted halt) :
    drive (n + 2) (.call pd :: ps) (running current)
      = drive n ps (running (resumeAfterCall (endFrame current halt).toCallResult pd)) := by
  conv_lhs => unfold drive
  dsimp only
  rw [hstep]
  conv_lhs => unfold drive
  dsimp only [Pending.resume]

/-- A `.needsCall` whose child is genuine `Code`: `beginCall params = .inl child`,
so `drive` descends into the child frame, suspending the parent as `.call pending`
on the stack. (When the child is `Code`, `beginCall` always returns `.inl`.) -/
theorem driveG_needsCall_code (n : ℕ) (ps : List Pending) (current : Frame)
    (params : CallParams) (pending : PendingCall) (child : Frame)
    (hstep : stepFrame current = .needsCall params pending)
    (hbegin : beginCall params = .inl child) :
    drive (n + 1) ps (running current)
      = drive n (.call pending :: ps) (running child) := by
  conv_lhs => unfold drive
  dsimp only
  rw [hstep]
  dsimp only
  rw [hbegin]

/-! ## Fuel monotonicity of `drive`

`drive` recurses on `fuel`. These are the fuel-monotonicity bricks: once a run
has produced *any* answer other than `OutOfFuel`, giving it more fuel changes
nothing. They are fuel-level facts (they mention `drive`, `Pending`, `Frame ⊕
FrameResult`). -/

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
        exact ih (.create pending :: stack) (.inl (beginCreate params)) h

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

end BytecodeLayer.Interpreter
