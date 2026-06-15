import Evm

/-!
# Generalized `drive` vocabulary (proof-internal, fuel-level)

`Drive.lean` specialises `drive` to the empty pending-stack `[]` that a *top-level*
`messageCall` starts with. The external-call rung needs the *same* `drive`
equations but with an **arbitrary** suspended-ancestor stack `ps`, because while
the child call runs the parent sits on that stack as a `Pending`. These are the
generic `match`-equations of `drive`, parameterised over `ps`:

* `driveG_step` — one non-halting instruction (any `ps`);
* `driveG_halt_call` — a `.call`-kind frame halts and its result is **delivered**
  to the innermost suspended `.call` ancestor, which resumes via
  `resumeAfterCall` and execution continues on the resumed parent (3 fuel units:
  take the halting step → fold to `.inr` → resume through the ancestor);
* `driveG_needsCall_code` — a `.needsCall` whose child is real `Code`: `beginCall`
  descends into the child frame, pushing the parent as a `.call` ancestor (1 unit).

All are low-level internal bricks (they mention `Frame`, `Pending`, fuel); they
never appear in an exported statement.
-/

namespace BytecodeLayer
open Evm

/-- One non-halting instruction under an arbitrary suspended stack `ps`. -/
theorem driveG_step (n : ℕ) (ps : List Pending) (current : Frame) (exec' : ExecutionState)
    (hstep : stepFrame current = .next exec') :
    drive (n + 1) ps (.inl current) = drive n ps (.inl { current with exec := exec' }) := by
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
    drive (n + 2) (.call pd :: ps) (.inl current)
      = drive n ps (.inl (resumeAfterCall (endFrame current halt).toCallResult pd)) := by
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
    drive (n + 1) ps (.inl current)
      = drive n (.call pending :: ps) (.inl child) := by
  conv_lhs => unfold drive
  dsimp only
  rw [hstep]
  dsimp only
  rw [hbegin]

end BytecodeLayer
