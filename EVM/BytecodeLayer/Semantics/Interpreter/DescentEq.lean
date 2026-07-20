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
proceeds above it. The central lemma `drive_append_framing_lt` makes this
precise: a run that drains `top` to `[]` and returns `.ok res` follows the
**identical** steps when `bot` is appended at the bottom, until it reaches the
configuration `(.inr res, bot)` instead of `(.inr res, [])`. The residual fuel
is existential — with the **strict bound** `j + 1 ≤ f`: the splice consumes at
least the one fuel unit that delivers the drained child's `.inr res`.
`drive_append_framing` is the unbounded weakening (the bound dropped) for
consumers that need no well-foundedness.

The proof mirrors `drive_fuel_succ`'s `induction f generalizing …` skeleton: in
every recursive arm the goal reduces to the same arm at fuel `f` (the IH), with
the `.error` arms discharged from the `.ok res` hypothesis; the single terminal
arm (`.inr` with the now-drained `top = []`) is the splice point, returning the
leftover fuel `n` with `n + 1 = f`.

## The descent equations

Specialising `top := []` and `bot := .call pd :: ps` and peeling one `.call`
resume step gives `drive_descend_lt` / `drive_descend_eq` (its unbounded
weakening): the parent's in-line descent into a terminating child equals the
independent child run followed by `resumeAfterCall res.toCallResult pd`.
`drive_descend_create_lt` is the CREATE twin (`bot := .create pd :: ps`),
conditioned on the successful resume witness `hok` because
`Pending.resume (.create pd)` is the `Except`-typed `resumeAfterCreate`; its
unbounded weakening `drive_descend_create_eq` lives in `Hoare/CallSequence.lean`.

Two consumer families:
* **forward** (`Runs.drive_reconcile`, the engine behind `messageCall_runs`)
  uses the unbounded `_eq` forms combined with `drive_fuel_mono` and
  `messageCall_never_outOfFuel` to reconcile the black-box child run against
  the caller's suffix on each `Runs.call`/`Runs.create` node;
* **reverse** (`runs_of_drive_ok`, `Hoare/DriveRuns.lean`) needs the strict
  `j < f` bound of the `_lt` forms — it is what makes the `drive → Runs`
  recursion well-founded (the resumed run recurses at strictly less fuel).
-/

namespace BytecodeLayer.Interpreter
open Evm

/-! ## The framing / stack-append lemma -/

/-- **Bounded stack-append framing of `drive`.** A run that drains `top` to the
empty stack and returns `.ok res` produces the *same* answer when an inert
bottom segment `bot` is appended below `top`, except that it stops at the
spliced configuration `(.inr res, bot)` rather than delivering through the
empty stack — and the residual fuel `j` satisfies `j + 1 ≤ f`: the splice
consumes at least the one fuel unit that delivers the drained child's `.inr res`
to the bottom segment.

Proved by induction on `fuel`, generalizing the stack `top` and the state `st`,
following `drive`'s own recursion: in each non-terminal arm the goal reduces to
the same arm at fuel `f` (the inductive hypothesis), with the residual fuel
threaded through; the `.error` arms cannot fire on a run that yields `.ok res`
and are discharged from the hypothesis; the terminal arm — `.inr res` reached
with `top` drained to `[]` — is the splice: `drive (f+1) (top ++ bot) (.inr res)`
with `top = []` is exactly `drive (f+1) bot (.inr res)`, returning the leftover
fuel `n` with `n + 1 = f`, so `n < f`. -/
theorem drive_append_framing_lt :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∀ (bot : List Pending),
        ∃ j, j + 1 ≤ f ∧ drive f (top ++ bot) st = drive (j + 1) bot (finished res) := by
  intro f
  induction f with
  | zero => intro top st res h bot; simp [drive] at h
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
        cases h
        exact ⟨n, by omega, rfl⟩
      | cons pending rest =>
        -- The head of `(pending :: rest) ++ bot` is the same `pending`.
        rw [List.cons_append]
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih rest (.inl parent) res h bot
          exact ⟨j, by omega, hj⟩
        | error e =>
          rw [hres] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih rest (.inr (endFrame pending.frame (.exception e))) res h bot
          exact ⟨j, by omega, hj⟩
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec =>
        rw [hstep] at h; dsimp only at h ⊢
        obtain ⟨j, hjlt, hj⟩ := ih top (.inl { current with exec := exec }) res h bot
        exact ⟨j, by omega, hj⟩
      | halted halt =>
        rw [hstep] at h; dsimp only at h ⊢
        obtain ⟨j, hjlt, hj⟩ := ih top (.inr (endFrame current halt)) res h bot
        exact ⟨j, by omega, hj⟩
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h ⊢
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h; dsimp only at h ⊢
          -- The descent conses `.call pending` onto the (appended) stack;
          -- the IH on the *cons* stack carries the framing through.
          obtain ⟨j, hjlt, hj⟩ := ih (.call pending :: top) (.inl child) res h bot
          rw [List.cons_append] at hj
          exact ⟨j, by omega, hj⟩
        | inr result =>
          rw [hbc] at h; dsimp only at h ⊢
          obtain ⟨j, hjlt, hj⟩ := ih (.call pending :: top) (.inr (.call result)) res h bot
          rw [List.cons_append] at hj
          exact ⟨j, by omega, hj⟩
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h ⊢
        obtain ⟨j, hjlt, hj⟩ := ih (.create pending :: top) (.inl (beginCreate params)) res h bot
        rw [List.cons_append] at hj
        exact ⟨j, by omega, hj⟩

/-- **Stack-append framing of `drive`** — the unbounded weakening of
`drive_append_framing_lt` (the strict fuel bound dropped), for consumers that
need no well-foundedness. -/
theorem drive_append_framing :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∀ (bot : List Pending), ∃ j, drive f (top ++ bot) st = drive (j + 1) bot (finished res) := by
  intro f top st res h bot
  obtain ⟨j, _, hj⟩ := drive_append_framing_lt f top st res h bot
  exact ⟨j, hj⟩

/-! ## The generic descent equations -/

/-- **Bounded CALL-boundary descent.** If a child frame run to the empty stack
terminates with `.ok res` (`drive f [] (.inl child) = .ok res`), then the
parent's *in-line* descent into that child — the child suspended on a `.call`
ancestor `pd` over an arbitrary inert stack `ps` — equals the parent resumed on
the child's `CallResult` at a residual fuel `j` **strictly below** the descent
fuel `f`. The strict bound (from the non-empty bottom segment `.call pd :: ps`
in `drive_append_framing_lt`) is what makes the reverse `drive → Runs`
recursion (`runs_of_drive_ok`) well-founded: the resumed run recurses at
`j < f`. Obtained with `top := []`, `bot := .call pd :: ps`, then peeling the
single `.call` resume step (`Pending.resume (.call pd) res = .ok (…)`). -/
theorem drive_descend_lt (f : ℕ) (child : Frame) (res : FrameResult)
    (pd : PendingCall) (ps : List Pending)
    (h : drive f [] (running child) = .ok res) :
    ∃ j, j < f ∧ drive f (.call pd :: ps) (running child)
      = drive j ps (running (resumeAfterCall res.toCallResult pd)) := by
  obtain ⟨j, hjlt, hj⟩ := drive_append_framing_lt f [] (.inl child) res h (.call pd :: ps)
  -- `[] ++ (.call pd :: ps) = .call pd :: ps`.
  rw [List.nil_append] at hj
  -- peel the single `.call` resume of `drive (j+1) (.call pd :: ps) (.inr res)`.
  refine ⟨j, by omega, ?_⟩
  rw [hj]
  conv_lhs => unfold drive
  dsimp only [Pending.resume]

/-- **Generic CALL-boundary descent equation** — the unbounded weakening of
`drive_descend_lt` (the strict fuel bound dropped). Program-agnostic: the child
is an arbitrary terminating run, with no concrete fuel offset or concrete
program baked in. -/
theorem drive_descend_eq (f : ℕ) (child : Frame) (res : FrameResult)
    (pd : PendingCall) (ps : List Pending)
    (h : drive f [] (running child) = .ok res) :
    ∃ j, drive f (.call pd :: ps) (running child)
      = drive j ps (running (resumeAfterCall res.toCallResult pd)) := by
  obtain ⟨j, _, hj⟩ := drive_descend_lt f child res pd ps h
  exact ⟨j, hj⟩

/-- **Bounded CREATE-boundary descent** (the CREATE twin of `drive_descend_lt`).
The resumed-parent run is at a fuel `j` **strictly below** the parent's descent
fuel `f`, conditioned on the *successful* resume witness `hok :
resumeAfterCreate res.toCreateResult pd = .ok parent` (the 63/64 retention
guard passing — `Pending.resume (.create pd)` is `Except`-typed). The strict
bound (from the non-empty bottom segment `.create pd :: ps` in
`drive_append_framing_lt`, which already threads create pendings) makes the
reverse `drive → Runs` recursion well-founded at the `Runs.create` node. The
unbounded weakening `drive_descend_create_eq` lives in `Hoare/CallSequence.lean`. -/
theorem drive_descend_create_lt (f : ℕ) (child : Frame) (res : FrameResult)
    (pd : PendingCreate) (ps : List Pending) (parent : Frame)
    (h : drive f [] (running child) = .ok res)
    (hok : resumeAfterCreate res.toCreateResult pd = .ok parent) :
    ∃ j, j < f ∧ drive f (.create pd :: ps) (running child)
      = drive j ps (running parent) := by
  obtain ⟨j, hjlt, hj⟩ := drive_append_framing_lt f [] (.inl child) res h (.create pd :: ps)
  rw [List.nil_append] at hj
  -- peel the single `.create` resume of `drive (j+1) (.create pd :: ps) (.inr res)` (`.ok` via `hok`).
  refine ⟨j, by omega, ?_⟩
  rw [hj]
  conv_lhs => unfold drive
  dsimp only [Pending.resume]
  rw [hok]

end BytecodeLayer.Interpreter
