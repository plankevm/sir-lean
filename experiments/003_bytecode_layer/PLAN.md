# Track A — local plan (`Runs.call` + multi-call composition)

Worktree: `../evm-semantics-wt/runs-call` · Branch: `exp003-runs-call` · Base: `exp003-fuel-layer-cleanup`
Master index: repo-root `currentplan.md` (read it for cross-track context).

## Goal
Make external **calls a constructor of the `Runs` relation** so a program with
multiple external calls is a single `Runs` value composed by `.trans`, collapsing
the verbose 5-hypothesis `messageCall_call_runs` and — the real prize — enabling
reasoning about **intermediary** calls (calls that don't halt the program).

## Where things are (exp003, this worktree)
- `BytecodeLayer/Hoare/Sequence.lean` — `Runs` (refl/head closure of `StepsTo`),
  `Runs.trans`, `Runs.drive_advance` (exact `n` fuel).
- `BytecodeLayer/Hoare/CallSequence.lean` — `CallReturns`, `messageCall_runs`,
  `messageCall_call_runs` (the verbose keystone), `drive_eq_of_both_ne_oof`.
- `BytecodeLayer/Semantics/Interpreter/DescentEq.lean` — `drive_descend_eq`
  (`∃ j`, program-agnostic descent), `drive_append_framing`.
- `BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean` — `messageCall_never_outOfFuel`.

## Milestones
- [x] **A1** Add `| call …` to `Runs` bundling `CallReturns`'s facts (`stepFrame =
  .needsCall`, `EntersAsCode`, child terminates, resume frame). Drop the `Nat` index
  (fuel premises are already gone) in favour of a non-`OutOfFuel`-reconciliation
  advance lemma proved by induction on `Runs`: `refl`→`drive_eq_of_both_ne_oof`,
  `step`→`drive_stepsTo`, `call`→`drive_descend_eq`+`drive_fuel_mono`.
- [ ] **A2** One boundary bridge `messageCall_runs`; re-derive the old
  `messageCall_call_runs` as a corollary (a `Runs` with one `.call` node).
- [ ] **A3** Multi-call composition: ≥2 calls with code between them, no
  per-call halt requirement. The acceptance test for the defect.
- [ ] **A4** Verdict + concise report; expose the composition API for Track C.

## Agent brief (durable — re-spawn from this verbatim)
> Work ONLY in `/Users/eduardo/workspace/evm-semantics-wt/runs-call`, on branch
> `exp003-runs-call`, inside `experiments/003_bytecode_layer`. Do **Milestone A1
> only** this run, then stop and report. Proof-first, always-green, NO `sorry`/
> `axiom` (verify with `lake build` + grep). Reuse existing lemmas
> (`drive_descend_eq`, `drive_fuel_mono`, `drive_eq_of_both_ne_oof`,
> `drive_stepsTo`) — do not reprove them. After each meaningful step append a dated
> entry to this PLAN.md progress log and commit on this branch. If A1 forces an
> index-design decision you can't resolve, write the options into the log and stop.

## Progress log
- 2026-06-22: Track seeded. Awaiting A1 agent.
- 2026-06-22 (A1, CLOSED): Index-free `Runs` + `call` constructor landed; build
  GREEN (1127 jobs), axiom-clean (`Runs.drive_reconcile`, `messageCall_runs`,
  `messageCall_call_runs`, `messageCall_call_completedWith` all depend only on
  `propext`/`Classical.choice`/`Quot.sound`; no `sorry`/`admit`/`axiom`).
  - `Runs` is now `Frame → Frame → Prop` (no `Nat`): constructors `refl`,
    `step` (was `head`), and the new `call hcall rest` where
    `hcall : CallReturns callFr resumeFr`. `CallReturns` moved up into
    `Hoare.lean` (it is the `call` payload); the duplicate def in
    `CallSequence.lean` was removed.
  - Replaced the exact-fuel `Runs.drive_advance` with the index-free
    reconciliation invariant `Runs.drive_reconcile` (in `CallSequence.lean`,
    which imports `DescentEq`/`NeverOutOfFuel`): "any two non-`OutOfFuel` runs
    from the two endpoints of a `Runs` path agree." Proved by induction on `Runs`,
    REUSING existing lemmas exactly as briefed — `refl`→`drive_eq_of_both_ne_oof`,
    `step`→`drive_stepsTo`, `call`→`drive_descend_eq` + `drive_fuel_mono` (lift the
    black-box child to `max a' (seedFuel cp.gas)`, splice via descent eq). No new
    interpreter lemmas reproved.
  - `messageCall_runs` reproved fuel-free off `drive_reconcile` (halt site in 2
    fuel vs. seeded run). `messageCall_call_runs` collapsed to a 3-line corollary:
    `messageCall_runs … (hpre.trans (Runs.call hcallret hpost)) hhalt` — note this
    is the A1-mechanical fallout of the constructor, NOT the A2 surface collapse
    (both boundary theorems still exist with their own signatures).
  - Mechanical fallout swept: opcode rules (`runs_push1`/`runs_push`/`runs_sstore`)
    now return `Runs` not `Runs 1`; `Runs.trans`/`single` lost the `m+n`/`1`;
    Spec.lean re-exports + Examples (`ProgramExamples`, `HoareDemo`,
    `CallerProgExample`) updated (`Runs 3/6/7` ascriptions and a `(n₂ := 0)`
    arg dropped). Docstrings de-stale'd (`n+2`/`Runs n₁`/`Nat`-index prose).
  - A1 is FULLY CLOSED; no blockers. Dropping the index was clean — every former
    fuel-bound obligation was already discharged by never-out-of-fuel, so the
    index carried no information. Next: A2/A3 (NOT done this run).
