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
- [x] **A2** One boundary bridge `messageCall_runs`. The old verbose
  `messageCall_call_runs` (5-hypothesis prefix/call/suffix) is DELETED, not aliased;
  its content is the one-`.call` special case of `messageCall_runs`. Replaced by the
  named multi-call guarantee `messageCall_runs_calls` and the observable-level
  `messageCall_calls_completedWith` (now over a single multi-call `Runs fr₀ last`).
- [x] **A3** Multi-call composition: ≥2 calls with code between them, no per-call
  halt requirement. General theorem `messageCall_runs_calls`; worked 2-call example
  `Examples/TwoCallExample.lean` (`twoCall_runs` / `twoCall_messageCall` /
  `twoCall_completedWith`). The acceptance test for the defect — intermediary calls
  compose.
- [ ] **A4** Verdict + concise report; finalize the composition API for Track C.

## Composition API for Track C (stable surface)
Build the caller's whole execution as ONE `Runs fr₀ last` and cross the single
bridge once. Constructors: `Runs.refl`, `Runs.step` (one `StepsTo`), `Runs.call`
(one returning external CALL, payload `CallReturns`), glued by `Runs.trans`. Then:
- `messageCall_runs p hbegin h hhalt` / its alias `messageCall_runs_calls` — raw
  `messageCall p = .ok (… endFrame last halt)` (Spec.lean re-exports both).
- `messageCall_calls_completedWith p a k v hbegin h hhalt hsucc hcell` — named
  `Outcome.completedWith` (Spec.lean).
- `Examples.twoCall_runs` / `twoCall_messageCall` / `twoCall_completedWith` — the
  ready-made `prefix·call₁·middle·call₂·suffix` composer (hand it two `CallReturns`
  witnesses + the runs between them). Each `CallReturns` is built like
  `CallerProgExample.caller_callReturns` (CALL step, child `EntersAsCode`, black-box
  child `drive … = .ok childRes`, resumed frame by `rfl`).
There is **no** per-call halt requirement and **no** numeric fuel side condition —
all reconciliation is internal to `Runs.drive_reconcile`.

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
- 2026-06-22 (A2, CLOSED): One boundary bridge. DELETED `messageCall_call_runs`
  (the verbose 5-hypothesis form) outright — per project policy, no dead alias.
  Its content is the single-`.call` case of `messageCall_runs`. Added
  `messageCall_runs_calls` (the named "≥N calls compose" guarantee, defeq to
  `messageCall_runs`) and renamed `messageCall_call_completedWith` →
  `messageCall_calls_completedWith`, now taking one multi-call `Runs fr₀ last`
  (5-hyp split collapsed). Swept call sites: `CallerProgExample` now crosses
  `messageCall_runs` over a `Runs.call` node (extracted `caller_callReturns`
  lemma; whole caller run assembled as `prefix.trans (Runs.call …)`); `Spec.lean`
  re-exports updated; stale doc refs in `ExternalCall`, `DescentEq`, `ConcreteSpecs`
  fixed. Build GREEN (1127 jobs).
- 2026-06-22 (A3, CLOSED): Multi-call composition. General theorem is
  `messageCall_runs_calls` — `messageCall_runs` already accepts a `Runs` with any
  number of `.call` nodes (reconciliation is inside `Runs.drive_reconcile`), so the
  guarantee needed only an explicit name, no new proof obligation. Worked 2-call
  acceptance test: NEW `Examples/TwoCallExample.lean`:
  * `twoCall_runs` — glues `prefix · call₁ · middle · call₂ · suffix` into one
    `Runs fr₀ last` via `Runs.trans`/`Runs.call`. Neither intermediary call halts:
    call₁ returns into `middle`, call₂ into `suffix`, only `last` halts.
  * `twoCall_messageCall` — discharges that `Runs` through `messageCall_runs_calls`.
  * `twoCall_completedWith` — observable-level lift.
  The six per-piece facts are honest structural hypotheses (real
  `Runs`/`CallReturns`/`StepsTo`/halt values, exactly what
  `CallerProgExample.caller_callReturns` produces for one call). Imported via
  `ConcreteSpecs` (avoided a Spec→…→Spec import cycle by referencing the `Hoare.*`
  names, not the Spec re-exports). Build GREEN (1128 jobs), axiom-clean (all six new
  theorems depend only on `propext`/`Classical.choice`/`Quot.sound`; no `sorryAx`).
  No blockers; the general statement needed no extra hypothesis. Track C composition
  API recorded above. A4 (verdict/report) NOT done this run.
