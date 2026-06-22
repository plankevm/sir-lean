import BytecodeLayer.Semantics.Interpreter.Drive

/-!
# Generic CALL-boundary descent equation (`DescentEq`)

This file proves the **program-agnostic** decomposition of the interpreter
`drive` across a CALL boundary: a parent's in-line descent into a *terminating*
child equals running that child *independently* to its result and then resuming
the parent on the child's `CallResult`. The child is an arbitrary terminating
run — no concrete fuel offset and no concrete program are baked in.

## The framing lemma

`drive` recurses only on the **head** of its pending stack (study the `match` in
`Evm/Semantics/Interpreter.lean`): every arm inspects/conses/pops only the head.
A *bottom* segment `bot` of the stack is therefore **inert** while execution
proceeds above it. The central lemma `drive_append_framing` makes this precise:
a run that drains `top` to `[]` and returns `.ok res` follows the **identical**
steps when `bot` is appended at the bottom, until it reaches the configuration
`(.inr res, bot)` instead of `(.inr res, [])`. The residual fuel is existential
(`∃ j`) so no exact fuel bookkeeping is needed.

The proof mirrors `drive_fuel_succ`'s `induction f generalizing …` skeleton: in
every recursive arm the goal reduces to the same arm at fuel `f` (the IH), with
the `.error` arms discharged from the `.ok res` hypothesis; the single terminal
arm (`.inr` with the now-drained `top = []`) is the splice point.

## The descent equation

Specialising `top := []` and `bot := .call pd :: ps` and peeling one `.call`
resume step gives `drive_descend_eq`: the parent's in-line descent into a
terminating child equals the independent child run followed by
`resumeAfterCall res.toCallResult pd`. Combined with `drive_fuel_mono` and
`messageCall_never_outOfFuel`, the residual fuel `j` reconciles to whatever the
resumed parent needs. This is the generic brick the sound external-CALL
sequencing rule (`messageCall_call_runs`) uses to reconcile the black-box child
run against the caller's suffix, replacing any assumed-forwarding hypothesis.
-/

namespace BytecodeLayer.Interpreter
open Evm

/-! ## The framing / stack-append lemma -/

/-- **Stack-append framing of `drive`.** A run that drains `top` to the empty
stack and returns `.ok res` produces the *same* answer when an inert bottom
segment `bot` is appended below `top`, except that it stops at the spliced
configuration `(.inr res, bot)` rather than delivering through the empty stack.

Proved by induction on `fuel`, generalizing the stack `top` and the state `st`,
following `drive`'s own recursion: in each non-terminal arm the goal reduces to
the same arm at fuel `f` (the inductive hypothesis), with the residual fuel
threaded through; the `.error` arms cannot fire on a run that yields `.ok res`
and are discharged from the hypothesis; the terminal arm — `.inr res` reached
with `top` drained to `[]` — is the splice: `drive (f+1) (top ++ bot) (.inr res)`
with `top = []` is exactly `drive (f+1) bot (.inr res)`. -/
theorem drive_append_framing :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∀ (bot : List Pending), ∃ j, drive f (top ++ bot) st = drive (j + 1) bot (.inr res) := by
  intro f
  induction f with
  | zero =>
    intro top st res h bot
    simp [drive] at h
  | succ n ih =>
    intro top st res h bot
    -- Unfold both the `top`-run and the `top ++ bot`-run one layer; same split.
    unfold drive at h ⊢
    cases st with
    | inr result =>
      cases top with
      | nil =>
        -- Terminal arm: empty stack delivers `result`; `res = result`.
        -- `[] ++ bot = bot`, so `drive (n+1) bot (.inr result)` is the splice.
        dsimp only at h ⊢
        -- `h : .ok result = .ok res`
        cases h
        exact ⟨n, rfl⟩
      | cons pending rest =>
        -- The head of `(pending :: rest) ++ bot` is the same `pending`.
        rw [List.cons_append]
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h
          dsimp only at h ⊢
          exact ih rest (.inl parent) res h bot
        | error e =>
          rw [hres] at h
          dsimp only at h ⊢
          exact ih rest (.inr (endFrame pending.frame (.exception e))) res h bot
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec =>
        rw [hstep] at h
        dsimp only at h ⊢
        exact ih top (.inl { current with exec := exec }) res h bot
      | halted halt =>
        rw [hstep] at h
        dsimp only at h ⊢
        exact ih top (.inr (endFrame current halt)) res h bot
      | needsCall params pending =>
        rw [hstep] at h
        dsimp only at h ⊢
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h
          dsimp only at h ⊢
          -- The descent conses `.call pending` onto the (appended) stack;
          -- the IH on the *cons* stack carries the framing through.
          have := ih (.call pending :: top) (.inl child) res h bot
          rw [List.cons_append] at this
          exact this
        | inr result =>
          rw [hbc] at h
          dsimp only at h ⊢
          have := ih (.call pending :: top) (.inr (.call result)) res h bot
          rw [List.cons_append] at this
          exact this
      | needsCreate params pending =>
        rw [hstep] at h
        dsimp only at h ⊢
        cases hbcr : beginCreate params with
        | ok child =>
          rw [hbcr] at h
          dsimp only at h ⊢
          have := ih (.create pending :: top) (.inl child) res h bot
          rw [List.cons_append] at this
          exact this
        | error e =>
          rw [hbcr] at h
          dsimp only at h ⊢
          have := ih (.create pending :: top)
            (.inr (.create _)) res h bot
          rw [List.cons_append] at this
          exact this

/-! ## The generic descent equation -/

/-- **Generic CALL-boundary descent equation.** If a child frame run to the
empty stack terminates with `.ok res` (`drive f [] (.inl child) = .ok res`), then
the parent's *in-line* descent into that child — the child suspended on a `.call`
ancestor `pd` over an arbitrary inert stack `ps` — equals, for some residual fuel
`j`, the parent resumed on the child's `CallResult`:
`drive j ps (.inl (resumeAfterCall res.toCallResult pd))`.

Program-agnostic: the child is an arbitrary terminating run, with no concrete
fuel offset or concrete program baked in. Obtained by `drive_append_framing` with
`top := []`, `bot := .call pd :: ps`, then peeling the single `.call` resume step
(`Pending.resume (.call pd) res = .ok (…)`). -/
theorem drive_descend_eq (f : ℕ) (child : Frame) (res : FrameResult)
    (pd : PendingCall) (ps : List Pending)
    (h : drive f [] (.inl child) = .ok res) :
    ∃ j, drive f (.call pd :: ps) (.inl child)
      = drive j ps (.inl (resumeAfterCall res.toCallResult pd)) := by
  obtain ⟨j, hj⟩ := drive_append_framing f [] (.inl child) res h (.call pd :: ps)
  -- `[] ++ (.call pd :: ps) = .call pd :: ps`.
  rw [List.nil_append] at hj
  refine ⟨j, ?_⟩
  rw [hj]
  -- Peel one resume step of `drive (j+1) (.call pd :: ps) (.inr res)`.
  conv_lhs => unfold drive
  dsimp only [Pending.resume]

end BytecodeLayer.Interpreter
