import Evm
import BytecodeLayer.Reasoning.Drive

/-!
# Straight-line driving (rung 1 engine)

The call-free capstones all have the same shape: from the initial frame, take a
fixed number of **non-halting** `stepFrame` steps, then one **halting** step, and
read the result off `endFrame`. Each proof peeled `seedFuel` by hand and chained
`drive_step`/`drive_halt` instruction by instruction. This file does that **once**
for an arbitrary straight-line block, so the rung-1 theorem composes a *list* of
steps instead of replaying bytes.

The single semantic relation is `StepsTo fr fr'`: one non-halting instruction
carries `fr` to `fr'` (same kind/jumps, `exec` advanced). A straight-line block
is a `List.IsChain StepsTo` ending in a frame that halts; `drive_chain_halt` runs
the whole block under the driver in one shot, consuming `len + 2` fuel. The
`messageCall`-boundary form is `messageCall_straightline_success`.

These are fuel-level bricks (they mention `Frame`, `drive`, fuel); they live in
`Reasoning/` so the named-outcome rung never unfolds `drive`.
-/

namespace BytecodeLayer
open Evm

/-- **One non-halting step.** `stepFrame fr` advances to `fr'`, which keeps `fr`'s
`kind`/`validJumps` and only moves `exec` forward. The atom a straight-line block
is a chain of. -/
def StepsTo (fr fr' : Frame) : Prop :=
  stepFrame fr = Signal.next fr'.exec ∧ fr' = { fr with exec := fr'.exec }

/-- `StepsTo` preserves the frame `kind` (only `exec` advances). -/
theorem StepsTo.kind_eq {fr fr' : Frame} (h : StepsTo fr fr') : fr'.kind = fr.kind := by
  rw [h.2]

/-- **Build a `StepsTo` from a `.next` step.** `stepFrame fr = .next e` gives a
`StepsTo fr { fr with exec := e }` — the successor frame is `fr` with `exec`
replaced by `e`. The one constructor the per-program instances feed each `Step`
lemma into. -/
theorem stepsTo_of_next {fr : Frame} {e : ExecutionState} (h : stepFrame fr = Signal.next e) :
    StepsTo fr { fr with exec := e } := ⟨h, rfl⟩

/-- The frames of a straight-line block as one list: the halting frame `last`
preceded by the `steps` non-halting frames (`fr₀` is `steps.head`, or `last`
itself when `steps = []` — a program that halts on its very first instruction,
like a bare `STOP`). -/
abbrev blockFrames (steps : List Frame) (last : Frame) : List Frame :=
  steps ++ [last]

/-- A single `StepsTo` is exactly one `drive` step at the top level: `drive`
spends one fuel and re-enters on `fr'`. -/
theorem drive_stepsTo (n : ℕ) {fr fr' : Frame} (h : StepsTo fr fr') :
    drive (n + 1) [] (.inl fr) = drive n [] (.inl fr') := by
  obtain ⟨hstep, hfr'⟩ := h
  rw [drive_step n fr fr'.exec hstep]
  rw [← hfr']

/-- **Run a straight-line block then halt, under the driver.** Given the block's
frames `steps ++ [last]` chained by `StepsTo` (`steps` is the possibly-empty run
of non-halting frames; `last` is the halting frame) and `last` halting
(`stepFrame last = .halted halt`), the driver started on the block's head returns
`endFrame last halt` — consuming `steps.length + 2` fuel (one per non-halting
step, one to take the halting step, one to deliver the result through the empty
pending stack). The `steps = []` case (`last` halts immediately) is included:
zero non-halting steps, `2` fuel. -/
theorem drive_chain_halt (extra : ℕ) (steps : List Frame) (last : Frame)
    (hchain : List.IsChain StepsTo (blockFrames steps last))
    (halt : FrameHalt) (hhalt : stepFrame last = Signal.halted halt) :
    drive (steps.length + 2 + extra) [] (.inl ((blockFrames steps last).head (by simp [blockFrames])))
      = .ok (endFrame last halt) := by
  induction steps with
  | nil =>
    -- `last` halts immediately: no non-halting step.
    simp only [blockFrames, List.nil_append, List.length_nil, List.head_cons, Nat.zero_add]
    rw [show 2 + extra = extra + 2 by omega, drive_halt extra last halt hhalt]
  | cons f fs ih =>
    -- `f` steps, then recurse on `fs ++ [last]` (head is `(fs ++ [last]).head`).
    simp only [blockFrames, List.cons_append, List.head_cons, List.length_cons] at hchain ⊢
    -- The tail `fs ++ [last]` is nonempty; expose its head to split the chain.
    have htail : fs ++ [last] = (fs ++ [last]).head (by simp) :: (fs ++ [last]).tail := by
      cases fs <;> simp
    rw [htail] at hchain
    obtain ⟨hfsucc, hrest⟩ := List.isChain_cons_cons.mp hchain
    rw [show fs.length + 1 + 2 + extra = (fs.length + 2 + extra) + 1 by omega]
    rw [drive_stepsTo (fs.length + 2 + extra) hfsucc]
    rw [← htail] at hrest
    exact ih hrest

/-! ## The `messageCall`-boundary form

`drive_chain_halt` is fuel-level. To use it from `messageCall`, peel the seeded
fuel down to the block's exact length, then route through `messageCall_eq_drive`.
The result is a `CallResult` read straight off `endFrame`.
-/

/-- **The straight-line block at the `messageCall` boundary.** If a code call's
initial frame `fr₀` (`beginCall p = .inl fr₀`) is the head of a straight-line block
`steps ++ [last]` chained by `StepsTo` whose `last` halts with `halt`, and the
seeded fuel covers the block (`steps.length + 2 ≤ seedFuel p.gas`), then
`messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))`.

Every call-free capstone is an instance: supply the explicit chain of frames and
the halting step; this lemma discharges the `messageCall → drive`, the fuel peel,
and the block run in one shot — no per-instruction `drive_step` chaining. The
`steps = []` case covers a program that halts on its first instruction. -/
theorem messageCall_straightline (p : CallParams) (fr₀ : Frame)
    (hbegin : beginCall p = .inl fr₀)
    (steps : List Frame) (last : Frame)
    (hhead : (blockFrames steps last).head (by simp [blockFrames]) = fr₀)
    (hchain : List.IsChain StepsTo (blockFrames steps last))
    (halt : FrameHalt) (hhalt : stepFrame last = Signal.halted halt)
    (hfuel : steps.length + 2 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  rw [messageCall_eq_drive p fr₀ hbegin]
  rw [show seedFuel p.gas
        = steps.length + 2 + (seedFuel p.gas - (steps.length + 2)) by omega]
  rw [← hhead]
  rw [drive_chain_halt (seedFuel p.gas - (steps.length + 2)) steps last hchain halt hhalt]
  rfl

end BytecodeLayer
