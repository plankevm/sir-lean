import Evm

/-!
# Drive vocabulary (proof-internal, fuel-level)

The two `drive` equations used to thread a top-level execution one signal at a
time. These are *internal* bricks (they mention `Frame`, fuel, `Sum`); they
exist only to let the capstones reduce `messageCall` without ever exposing fuel
or frames in an exported statement. Both are pure rewrites of `drive`'s own
defining `match`, specialised to the empty pending-stack `[]` (a top-level
`messageCall` starts with no suspended ancestors).
-/

namespace BytecodeLayer
open Evm

/-- One non-halting instruction: consume one unit of fuel and advance the frame.
`drive` re-enters on the updated frame with the *same* (empty) pending stack. -/
theorem drive_step (n : ℕ) (current : Frame) (exec' : ExecutionState)
    (hstep : stepFrame current = .next exec') :
    drive (n + 1) [] (.inl current) = drive n [] (.inl { current with exec := exec' }) := by
  conv_lhs => unfold drive
  dsimp only
  rw [hstep]

/-- A halting instruction at the top level: the frame ends and, with no
suspended ancestors, the driver returns the frame's result. Two units of fuel:
one to take the halting step, one to deliver the `.inr` result through the empty
stack. -/
theorem drive_halt (n : ℕ) (current : Frame) (halt : FrameHalt)
    (hstep : stepFrame current = .halted halt) :
    drive (n + 2) [] (.inl current) = .ok (endFrame current halt) := by
  unfold drive
  dsimp only
  rw [hstep]
  rfl

/-- `seedFuel` is always at least 2 — enough to take one halting step and
deliver its result. Used to peel `seedFuel g = (seedFuel g - 2) + 2` so
`drive_halt` applies to the fuel `messageCall` actually seeds. -/
theorem two_le_seedFuel (g : UInt64) : 2 ≤ seedFuel g := by
  unfold seedFuel; omega

end BytecodeLayer
