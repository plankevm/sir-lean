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
- [x] **B1 (CFG / conditional control flow)** `Runs`-level JUMP/JUMPI/JUMPDEST
  rules + the `runs_branch` conditional-branch combinator + worked branch example.
  The prereq for Track C's branch lowering. See the dated log entry below and the
  "Control-flow API for Track C" section.
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

## Control-flow API for Track C (CFG / branch lowering)
The conditional-control-flow building blocks. All in `BytecodeLayer/Hoare.lean`
(opened via `BytecodeLayer.Hoare`); the underlying `stepFrame_*` lemmas are in
`BytecodeLayer/Semantics/Dispatch.lean`. Each rule is one `Runs` step with
**semantic-only** preconditions (decode, gas, stack shape, valid jump dest); the
post-frame is named by a transformer the way `pushFrame`/`sstoreFrame` are.

Post-frame transformers (`Hoare.lean`):
- `jumpFrame fr cost new_pc rest` — `exec := jumpPost` (gas `- cost`, `pc :=
  new_pc`, operands popped to `rest`). Used by JUMP and a taken JUMPI.
- `jumpiFallthroughFrame fr rest` — `exec := jumpiFallthroughPost` (gas `- Ghigh`,
  `pc := pc+1`, operands popped). Used by a not-taken JUMPI.
- `jumpdestFrame fr` — `exec := jumpdestPost` (gas `- Gjumpdest`, `pc := pc+1`,
  stack unchanged). The no-op landing pad.

Opcode rules (one `Runs` step each):
- `runs_jump fr dest new_pc rest hdec hstk hsz hgas hdest :
    Runs fr (jumpFrame fr Gmid new_pc rest)` — unconditional jump.
  `hdest : fr.get_dest dest = some new_pc` (valid JUMPDEST), `hgas : Gmid ≤ gas`.
- `runs_jumpi_taken fr dest cond new_pc rest hdec hstk hsz hgas hcond hdest :
    Runs fr (jumpFrame fr Ghigh new_pc rest)` — `hcond : cond ≠ 0`, `hdest` valid.
- `runs_jumpi_fallthrough fr dest rest hdec hstk hsz hgas :
    Runs fr (jumpiFallthroughFrame fr rest)` — stack head must be `dest :: 0 :: rest`.
- `runs_jumpdest fr hdec hsz hgas : Runs fr (jumpdestFrame fr)` — step past a
  landing pad (a taken jump lands on a JUMPDEST, so chain this after the jump).

The branching combinator (the key helper):
- `runs_branch hdec hstk hsz hgas branch : Runs fr fr'`. Given the JUMPI frame
  (decode `JUMPI`, stack `dest :: cond :: rest`, gas/overflow OK) and a `branch`
  decision, builds the whole `if` as one `Runs fr fr'`:
  `branch : (∃ new_pc, cond ≠ 0 ∧ fr.get_dest dest = some new_pc
              ∧ Runs (jumpFrame fr Ghigh new_pc rest) fr')        -- taken arm
           ∨ (cond = 0 ∧ Runs (jumpiFallthroughFrame fr rest) fr')`. -- fall-through
  The caller case-splits on the runtime `cond` (or supplies a statically-known
  side) and hands over the matching arm's continuation `Runs`. The result drops
  straight into `Runs.trans` like straight-line code.

Loops / back-edges: no separate theory needed. A `Runs` already expresses any
finite trace, so a `runs_jump` back to an earlier `pc` is just another node glued
by `Runs.trans` (gas strictly decreases each step ⇒ finiteness). A full
loop-invariant theory is a follow-up if/when a real loop program needs it.

Worked acceptance check: `Examples/BranchExample.lean`. `branchProgram =
JUMPI;STOP;STOP;JUMPDEST;STOP`; `branchRuns cond g hg` builds one
`Runs (jumpiFrame cond g) fr'` to a STOP-decoding frame for **any** `cond`, by
`runs_branch` case-split — taken arm jumps to the JUMPDEST then `runs_jumpdest`
steps to the trailing STOP, fall-through arm advances to its STOP. The frame uses
an explicit `validJumps := #[3]` so `get_dest` is kernel-reducible (`codeFrame`'s
`validJumpDests` is `partial`/opaque) — keeping the example free of `native_decide`.

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
- 2026-06-22 (B1 — CFG / conditional control flow, CLOSED): the branch combinator
  for Track C. NO new circular/trace-shaped hypotheses; all preconditions are
  semantic (decode/gas/stack-shape/valid-dest), matching `runs_push`/`runs_sstore`.
  * `Step.lean`-level (in `BytecodeLayer/Semantics/Dispatch.lean`, derived the same
    way as `stepFrame_push`/`stepFrame_sstore`): `stepFrame_jump`,
    `stepFrame_jumpi_taken`, `stepFrame_jumpi_fallthrough`, `stepFrame_jumpdest`.
    JUMP/JUMPI/JUMPDEST live in `smsfOp` (the `.Smsf` cluster); the result sets
    `pc` directly (not `replaceStackAndIncrPC`), so the post-states `jumpPost` /
    `jumpiFallthroughPost` / `jumpdestPost` are spelled out inline. JUMPI's
    `cond != 0` guard discharged via `UInt256.beq_iff_eq`; overflow guards from
    `stack.size ≤ 1024` (both jumps only shrink the stack); gas from `Gmid`/`Ghigh`/
    `Gjumpdest` bounds.
  * `Runs`-level (in `BytecodeLayer/Hoare.lean`): `runs_jump`, `runs_jumpi_taken`,
    `runs_jumpi_fallthrough`, `runs_jumpdest` (each `Runs.single` off its step
    lemma), plus the **branching combinator `runs_branch`** (case-split on a
    taken/fall-through witness disjunction, glued by `Runs.trans`). Full signatures
    in "Control-flow API for Track C" above.
  * Worked example: NEW `Examples/BranchExample.lean` — `branchRuns` composes both
    arms of a one-JUMPI program into a single `Runs` to a STOP frame for arbitrary
    `cond`, via `runs_branch`. Wired into the default build through `ConcreteSpecs`.
  * Build GREEN (1129 jobs), axiom-clean: all ten new theorems (`stepFrame_jump`,
    `stepFrame_jumpi_taken`, `stepFrame_jumpi_fallthrough`, `stepFrame_jumpdest`,
    `runs_jump`, `runs_jumpi_taken`, `runs_jumpi_fallthrough`, `runs_jumpdest`,
    `runs_branch`, `branchRuns`) depend only on `propext`/`Classical.choice`/
    `Quot.sound` — no `sorryAx`, no `ofReduceBool` (no `native_decide`).
  * Loops: deferred as noted (a back-edge is just another `Runs.trans` node; no
    invariant theory needed this milestone). No blockers.
- 2026-06-22 (C→A opcode rules — ADD/LT/SLOAD/GAS, CLOSED): completed the opcode
  `Runs` rule set C3 requested (the C→A request's items 1–4; items 5–6, JUMP/JUMPI,
  were already shipped by B1). All semantic-only preconditions (decode/gas/stack
  shape — no trace/conclusion hypotheses), each with a named post-frame transformer,
  same brick shape as `runs_push`/`runs_sstore`.
  * `Step.lean`-level (`BytecodeLayer/Semantics/Dispatch.lean`, derived from
    `stepFrame` like the existing per-opcode lemmas): `stepFrame_add`,
    `stepFrame_lt` (both via a shared private `stepFrame_binOp` over `binOp f exec
    Gverylow`, parametric in the result `f`; post-state `binOpPost`),
    `stepFrame_sload` (`unStateOp Evm.State.sload`; post-state `sloadPost` charges
    `sloadCost warm`, pushes the self storage value, marks `(self,key)` accessed),
    `stepFrame_gas` (`pushOp (ofUInt64 gasAvailable)`; post-state `gasPost`, value
    read **after** the `Gbase` charge — the gas-introspection coupling).
  * `Runs`-level (`BytecodeLayer/Hoare.lean`): `runs_add`/`runs_lt`/`runs_sload`/
    `runs_gas` (each `Runs.single` off its step lemma), with transformers
    `addFrame`/`ltFrame`/`sloadFrame`/`gasFrame`. Plus the SLOAD **storage-READ
    companion** `sloadFrame_storage_self` (mirrors `sstoreFrame_storage_self`): the
    head of `sloadFrame`'s resulting stack `= fr.exec.accounts.find? self |>.option
    0 (·.lookupStorage key)` — the exact lens C3's storage `Match` (M3) uses,
    connecting SLOAD's pushed value to the IR storage cell. Proof is `rfl` (the
    model's `sload` pushes exactly that value).
  * Re-exported all five on `Spec.lean` alongside `runs_push`/`runs_sstore` (program-
    logic surface). Note: the C request spelled `fr.exec.code` / `decode … = some
    (.ArithLogic .ADD, none)`; the real field path is `fr.exec.executionEnv.code` and
    `Operation.ADD` is the abbrev `.ArithLogic .ADD`, so the delivered decode
    hypotheses read `.ArithLogic .ADD` / `.ArithLogic .LT` / `.Smsf .SLOAD` /
    `.Smsf .GAS` against `fr.exec.executionEnv.code` — semantically the request.
  * Worked example: NEW `Examples/ArithStorageExample.lean` — `arithStorageRuns`
    composes `ADD ; LT ; GAS ; SLOAD` into one `Runs` via `Runs.trans`, threading
    each rule's post-frame (incl. the GAS→SLOAD coupling where the pushed gas word
    becomes SLOAD's key, and a cold-slot `Gcoldsload = 2100` charge). Wired into the
    default build through `ConcreteSpecs`.
  * Build GREEN (1130 jobs), axiom-clean: all new theorems (`stepFrame_add`,
    `stepFrame_lt`, `stepFrame_sload`, `stepFrame_gas`, the four `runs_*`,
    `sloadFrame_storage_self`, `arithStorageRuns`, and their Spec re-exports) depend
    only on `propext`/`Classical.choice`/`Quot.sound` — no `sorry`/`admit`/`axiom`,
    no `ofReduceBool` (no `native_decide`). No blockers; Track A's exp003 layer is
    ready to merge.

### C→A opcode-rule request — delivery checklist
- [x] **1. `runs_add`** — ADD, `Gverylow = 3`, pop 2 / push 1; post-frame `addFrame`.
- [x] **2. `runs_lt`** — LT, same shape, pushes `UInt256.lt a b`; post-frame `ltFrame`.
- [x] **3. `runs_sload`** — SLOAD, `sloadCost warm/cold = 100/2100`, pop key / push
  value; post-frame `sloadFrame`; **read companion `sloadFrame_storage_self`** added.
- [x] **4. `runs_gas`** — GAS, `Gbase = 2`, pushes post-charge `ofUInt64
  gasAvailable`; post-frame `gasFrame`.
- [x] **5. `runs_jump`** / **6. `runs_jumpi_taken` / `runs_jumpi_fallthrough`** —
  already delivered by B1 (see the CFG / control-flow entry above).
