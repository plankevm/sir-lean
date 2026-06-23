# Current Plan — three-track parallel orchestration

**This is the master index. If you are a freshly-spawned Claude with no context,
READ THIS FIRST, then read the local `PLAN.md` of whichever track you are
resuming. Then verify reality against git (branches, worktrees, `lake build`)
before asserting any status below as fact — these checkboxes are intent, the
build is truth.**

Last updated: 2026-06-22. Owner: Eduardo. Base branch: `exp003-fuel-layer-cleanup`
(holds exp003 + the vendored `EVMLean` subtree; this file lives here and is
inherited by every track's worktree).

---

## The shape of the work

Three tracks run in parallel, each in its **own git worktree on its own branch**
off the base branch. Worktrees (not a shared checkout) so three background agents
can commit concurrently without racing the git index. Each branch merges back
into the base when its milestones are green. The base branch is the integration
trunk.

| Track | Goal | Worktree | Branch | Local plan |
|---|---|---|---|---|
| **A** | Calls as a `Runs` constructor; multi-call composition | `../evm-semantics-wt/runs-call` | `exp003-runs-call` | `experiments/003_bytecode_layer/PLAN.md` |
| **B** | Nested EVM core over EVMYulLean (Yul stripped); fuel↔gas; IR-facing surface | `../evm-semantics-wt/nested-evmyul` | `exp004-nested` | `experiments/004_nested_evmyul/PLAN.md` |
| **C** | High-level IR (storage arith + calls + branching) → EVM bytecode, lowering preserved | `../evm-semantics-wt/ir-lowering` | `exp005-ir` | `experiments/005_ir_lowering/PLAN.md` |

Paths are relative to the repo root `/Users/eduardo/workspace/evm-semantics`.

---

## Why these three, and how they interlock

The driving questions (the "why" behind the milestones):

1. **Multiple external calls.** exp003's sequencing rule (`messageCall_call_runs`)
   is *one frame → one call → one frame that halts*. It composes only with things
   that **eventually halt**, so we cannot yet reason about **intermediary** calls
   (a program that calls, continues, calls again, …). This is the headline defect.
   **Track A** attacks it by making `call` a constructor of `Runs` (so a multi-call
   program is one `Runs` value built by `.trans`). **Track C** is the real consumer
   /test: lowering a multi-call IR program will *prove or disprove* that A's rule
   composes. If A is insufficient, C's requirements drive A's redesign.
2. **Gas introspection.** Can we reason about `GAS`/gas-dependent branches, or at
   least prove introspection "doesn't interfere too much"? This **requires branching
   in the IR** — primarily explored in **Track C** (the IR must have branches), with
   the honesty constraint from project memory: keep theorems TRUE under gas
   introspection, earn gas-freedom as a *proved* result, never assume it.
3. **Fuel↔gas.** "Instantiate fuel ≥ (a function of) gas ⇒ never `OutOfFuel`," so
   IRs never see fuel/frames. Flat side (exp003) already has the unconditional
   `messageCall_never_outOfFuel`. **Track B** must re-establish this on the *nested*
   `Ξ/Θ` semantics.
4. **A higher-level semantics surface for IRs.** Both A (derived-nested over flat)
   and B (genuinely nested) aim to expose observables-only, fuel/frame-free results
   that the next IRs (Track C and beyond) consume. A and B are a deliberate
   **flat-vs-nested bake-off** for which foundation best serves IR reasoning.

Background (validated 2026-06-22, see `experiments/003_bytecode_layer/docs/verifereum-nested-call.md`):
philogy/`leanevm` (= vendored `EVMLean`, exp003's base) is **flat** (one `drive`
trampoline over a shared `List Pending`); NethermindEth/`EVMYulLean` is **nested**
(mutual `Θ/Ξ`, Yellow-Paper-faithful). Nested gives the classical procedure-call +
frame rules by construction; flat makes us earn each as a theorem. Track A recovers
nesting *as a theorem over flat*; Track B *adopts* the already-nested semantics.

---

## END GOAL — converge the two EVM semantics (Phase 2)

**This is the experiment's culminating objective (Eduardo, restated 2026-06-22).** We
now have/are-building two EVM semantics: **flat** (philogy's `EVMLean`, exp003 — single
`drive` over a pending stack, one fuel) and **nested** (`EVMYulLean`-with-Yul-stripped,
exp004 — Yellow-Paper `Θ/Ξ` mutual recursion). The goal is to make them **provably or
structurally the same thing**, so they can be compared on *other* merits (ergonomics,
proof compositionality, conformance) with confidence they're equivalent:
- **Phase 2a — shared interface.** Define a Lean **type class / structure** capturing the
  EVM-semantics surface (e.g. `messageCall`/observables, never-`OutOfFuel`, the
  call/sequencing rules, gas behaviour) and have BOTH semantics *instantiate it with the
  same theorems*. If both are instances of one `EVMSemantics` trait proving the same
  spec, they're interchangeable for IR reasoning.
- **Phase 2b — equivalence (stretch).** Prove an actual behavioural equivalence
  (`messageCall_flat ≃ messageCall_nested` on observables), or a `driveNested ≃ drive`
  bridge. The verifereum doc (E.3) flagged this as the deferred unification.
This is what Tracks A (flat surface) and B (nested surface) are FEEDING. Their B4/A-surface
milestones should converge on the SAME signatures so 2a is mechanical. Track C consumes
whichever interface, ideally the shared one.

## Milestones (intent — verify against build)

### Track A — `Runs.call` + multi-call composition  (worktree `runs-call`)
- [ ] **A1** Add a `call` constructor to `Runs` (bundles `CallReturns`). Decide the
  index: drop the now-vestigial `Nat` (fuel premises already gone) in favour of the
  non-`OutOfFuel`-reconciliation invariant. Reuse `drive_descend_eq`,
  `drive_fuel_mono`, `drive_eq_of_both_ne_oof` (all exist in exp003).
  → **DONE** (`exp003-runs-call` @ `7be5a5b`, green 1127 jobs, axiom-clean).
  `Runs : Frame → Frame → Prop` (no index); constructors `refl`/`step`/`call`
  (`call` payload = `CallReturns`, moved into `Hoare.lean`). Index-free
  `Runs.drive_reconcile` replaces the exact-fuel advance lemma. Dropping the index
  was clean — every former fuel obligation was already discharged by never-out-of-fuel.
  `messageCall_call_runs` already fell out as a 3-line corollary (the A2 *surface*
  collapse — keeping one named bridge — is still nominally pending).
- [x] **A2** DONE (`ec6c297`). `messageCall_call_runs` DELETED outright (no alias);
  `messageCall_runs` is the single bridge; `messageCall_calls_completedWith` takes one
  multi-call `Runs`. Call sites swept.
- [x] **A3** DONE (`aa141e7`, green 1128 jobs, axiom-clean). `messageCall_runs_calls`
  is the named ≥N-call guarantee — `messageCall_runs` already accepts a `Runs` with any
  number of `.call` nodes (all reconciliation inside `drive_reconcile`), so NO new proof
  obligation. Worked 2-call acceptance test in `Examples/TwoCallExample.lean`: two
  intermediary calls that DON'T halt, glued by `Runs.trans`/`Runs.call`, discharged
  through the bridge. **The intermediary-call defect is fixed. This unblocks Track C C4.**
- [x] **A4** Verdict delivered (in A's report + PLAN.md): `messageCall_runs_calls`
  supersedes the old keystone; composition API recorded for Track C.
- [x] **CFG combinator** DONE (`bc810cc`, green 1129 jobs, axiom-clean). Step-level
  `stepFrame_jump/jumpi_taken/jumpi_fallthrough/jumpdest` + `Runs` rules `runs_jump/
  runs_jumpi_taken/runs_jumpi_fallthrough/runs_jumpdest` + the **`runs_branch`** helper
  (disjunction over taken/fall-through; caller case-splits on the runtime condition,
  drops into `Runs.trans`). Worked `BranchExample`. Loops deferred (a back-edge is just
  another `runs_jump` glued by `trans`; gas ⇒ finiteness). **The report MUST argue this
  design choice + alternatives (Eduardo wasn't in this discussion).**
- [x] **Opcode-rule completion** DONE (`2615d03`, green 1130 jobs, axiom-clean):
  `runs_add/lt/sload`(+`sloadFrame_storage_self`)/`gas` + `ArithStorageExample`.
- [x] **A→base MERGE DONE** (integration gate cleared). A's full flat layer merged into
  `exp003-fuel-layer-cleanup` (clean, no conflicts, base exp003 green 1130); base then
  merged into `exp005-ir` so **C is unblocked** (C green 1106 against the new API).
  Track A core is complete & reportable → `lean-review-report` launched.
- NOTE (cleanup, defer to a review pass once `exp003-runs-call` stabilizes): A2's
  deletion left stale `messageCall_call_runs` refs in `docs/review-report.md` +
  `review-report-followup.md` — regenerate via `review-report.prose`, don't hand-patch.

### Track B — Nested EVM core over EVMYulLean  (worktree `nested-evmyul`)
- [x] **B1** DONE (`exp004-nested` @ `20ad4c1`, green 1033 jobs). Vendored
  EVMYulLean @ `066dc8b` (816K). **Finding: a clean Yul-ectomy is impossible** — the
  nested semantics is `τ`-polymorphic over `OperationType = Yul | EVM` and EVM state
  types carry `Yul.Ast.contractCode`, so the EVM path needs a minimal Yul fragment
  (`Yul/{Ast,State,StateOps,Exception,Wheels,PrimOps}` kept; `Yul/{Interpreter,
  MachineState,SizeLemmas,YulNotation}`+tests deleted). exp004 lakefile requires
  `evmyul from "EVMYulLean"`; toolchain v4.22.0; crypto FFI built fine.
- [x] **B0** DONE (`exp004-nested` @ `63e234e` + lakefile fix, green, axiom-clean).
  FULL Yul removal achieved: deleted `OperationType`, the `τ` parameter (~210 sites),
  and ALL of `EvmYul/Yul/`; `contractCode τ → ByteArray`; `.Yul` dispatch arms gone;
  no proofs broke (vendored core was `def`/`structure` only). Nested `Θ/Ξ/X` is now
  plain EVM. (Main loop fixed the default-target glob: `andSubmodules` needed a
  `NestedEvmYul/` dir that won't exist until B2 — temporarily `roots := [NestedEvmYul]`.)
- [~] **B2** Fuel↔gas: never-`OutOfFuel` on nested `Ξ/Θ` — PARTIAL (`863dc24`, green,
  axiom-clean). DONE: `seedFuel g = 4*(g+1)`; fuel-0 base cases (all 5 layers); the
  cornerstone `C'_pos_of_runnable` (every loop-continuing opcode burns ≥1 gas — ~140 ops;
  zero-cost ops all halt); positivity helpers; the headline `Θ_never_outOfFuel` stated.
  PROGRESS (`21f3450`, green, axiom-clean): (1) gas-decrement chain DONE; (2) `X` measure
  descent DONE; (3) cross-layer gas/depth conservation DONE (`Ccallgas_le_gas_of_cover`,
  `call_depth_bound` ≤1024); (4) 4/5 propagation skeletons proved (Ξ/Θ-Code/call/Lambda
  inductive steps of the strong-fuel-induction). **PAUSED for steer (3rd iteration).**
  REMAINING: `step` skeleton + `X` inner loop-induction + precompiled-`Θ` arm + final
  assembly. **KEY DESIGN FINDING: `seedFuel = 4*(g+1)` is INSUFFICIENT for nested** — gas
  is only non-increasing (not strictly smaller) across a descent, so fuel must cover
  ~4 hops × ≤1024 descents ⇒ the seed must be **DEPTH-AWARE**, e.g.
  `B(gas,depth) = (1025−depth)·4·(gas+1)`. This must be settled before the headline closes.
  DECISION (Eduardo): finish it — final iteration IN PROGRESS with the depth-aware bound
  `B(gas,depth)=(1025−depth)·4·(gas+1)`; closing `step` skeleton + `X` inner loop-induction
  + precompiled-`Θ` arm + final mutual assembly. Reports (Track B full + Track C refresh)
  held until B2 lands so they reflect the final state.
- [ ] **B3** Nested external-call core: a `{P} Ξ(child) {Q}` triple + call-site/frame
  rule; demonstrate **multiple** calls compose naturally (contrast with A's effort).
- [ ] **B4** Expose an observables-only, fuel/frame-free semantics surface for IRs.

### Track C — IR + lowering + preservation  (worktree `ir-lowering`)
- [x] **C1** DONE (`exp005-ir` @ `505c83b`, green 1105 jobs). Fresh `LirLean` IR
  (NOT extending `SirLean`: UInt32, no CALL, no gas, dead SSA weight). First-class
  `sload/sstore/add/lt`, `Stmt.call`, `Term.branch`, `Expr.gas`. `docs/ir-design.md`
  + `sorry`-free compiling two-pass lowering skeleton.
- [x] **C2** DONE (`exp005-ir` @ `bde1913`, green 1106 jobs, axiom-clean). Lowering
  emits decode-compatible bytecode per construct (recompute-on-use; PUSH32/ADD/LT/SLOAD/
  GAS/SSTORE/CALL/JUMP/JUMPI/RETURN/STOP), ~40 build-enforced `decode … = expected`
  round-trip `rfl` checks (avoided `native_decide` to stay axiom-clean).
- [~] **C3** Prove lowering preserves semantics — UNBLOCKED (A merged) & PARTIAL
  (`b81b331`, green 1126 jobs, axiom-clean). DONE: small-step gas-aware IR semantics
  (`SmallStep.lean`), the 5-clause `Match` invariant (`Match.lean`), ALL per-construct
  simulation lemmas (`sim_imm/add/lt/sload/gas/sstore/jump/branch/call`, `halt_stop/ret`),
  and the top-level boundary discharge `lower_preserves_discharge` (crosses
  `messageCall_runs`, already handles ANY number of `Runs.call` nodes ⇒ C4 discharge is
  nearly free). Byte-layout half now DONE generically (`84f79aa`): `decode_lower`
  (+`bget`/`bextract` foundations) and the offset-table arithmetic with symbolic `M1`
  (`pcOf_eq_anchor`/`flatBytes_at_pcOf`). REMAINING (final continuation IN PROGRESS):
  the per-program `Runs fr₀ last` assembly for `workedCall` (gas-tracked `Runs.trans`
  chain + a concrete `CallReturns` child run). **ARCHITECTURALLY COMPLETE** (`496ef19`,
  green 1129): `lower_preserves` (single-call) + the concrete `Runs` assembly for
  `workedCall` (`wc_prefix_runs`/`wc_call_step`/`wc_preserves`) hold as the BRIDGE HALF
  with two honest, non-faked hypotheses: (a) the concrete child `CallReturns` (feasible-
  but-large callee `drive` run), (b) the post-CALL branch terminator — **BLOCKED by
  `validJumpDestsAux` being a `partial def`** (kernel-opaque ⇒ `get_dest` unprovable
  without `native_decide`). Track A is now detotalizing it. Track C report launched.
- [x] **C4** Multi-call lowering — RESOLVED STRUCTURALLY (`496ef19`): `wc_preserves_twoCall`
  closes a 2-CALL program by the SAME bridge discharge (the boundary discharge composes any
  number of `Runs.call` nodes). Needed NO new theory — direct payoff of Track A's
  `Runs.call`. Its open pieces are identical to C3's (the two honest hypotheses), not
  multi-call-specific.

---

## Backlog (after the current round A2/A3 · C2 · B2)

**Track A:** CFG combinator (`JUMPI`/branches/loops as `Runs`-level structure — prereq
for C's branching + gas introspection) · gas introspection first-class (∃G₀-monotone) ·
`CREATE` as a 2nd descent constructor · reentrancy/value-transfer (deferred) · symbolic
worlds + gas-ledger to scale past concrete `find?`/`decide`.

**Track B:** B3 `{P} Ξ(child) {Q}` triple + call-site/frame rule (≥2 calls native) ·
B4 observables-only IR surface · **the bake-off verdict** A-vs-B foundation for IRs ·
optional `driveNested ≃ drive` unification · optional monomorphize exp004 to EVM-only
(removes the kept Yul fragment — only if `τ = Yul|EVM` baggage causes real friction; it
is INERT for EVM today, so not urgent — see Yul note below).

**Track C:** C3 lowering-preservation (single-call first) · C4 multi-call lowering (needs
A3) · branch lowering (`Term.branch`→`JUMPI`) where **gas-introspection preservation**
becomes a concrete theorem · connect `LirLean` to the real Plank SIR (the project's
ultimate target).

**Cross-cutting:** integration order A→base, C rebases on A, B merges when ready · the
gas-introspection question lives at the A-CFG × C-branching intersection.

**Yul note (B):** EVMYulLean's semantics is ONE machinery polymorphic over
`OperationType = Yul | EVM`; `Account`/`ExecutionEnv` carry `Yul.Ast.contractCode τ`
(= `ByteArray` for `.EVM`). The kept Yul fragment is the transitive closure the EVM path
references; its `.Yul` dispatch arms are inert when `τ = .EVM`. Full removal = monomorphize
to EVM (a real edit to the trusted semantics) → backlog, not blocking.

## Dependencies & integration

- **A ↔ C** is the live feedback loop: C consumes A's sequencing API; C's multi-call
  lowering is A's acceptance test. C can start *now* (IR design + single-call
  lowering) without waiting on A3.
- **B** is independent; it informs the long-term foundation choice (flat-derived
  nesting vs. genuine nesting). Bake-off, not a blocker.
- **Gas introspection** (Q2) is explored in C once branches exist.
- Merge order when green: A into base first (it improves exp003's reusable layer),
  then C rebases onto it; B merges whenever B-milestones land.

---

## Continuous operation — autonomous next-launch queue

Mode (Eduardo, 2026-06-22): **keep cranking with no latency** — don't wait for the
user between rounds. The loop is **event-driven by agent completions**: each time a
background agent finishes, the main loop (1) VERIFIES it (`lake build` + `git log` in
its worktree + grep `sorry`/`axiom` — never trust the agent's self-report), (2) updates
this file's checkboxes, (3) launches that track's NEXT queue item, respecting
cross-track deps. Always launch ≥1 task per completion so the loop never stalls. The
user reviews/steers asynchronously; "go far, and when idle, also review + simplify."

Per-track queue (top = next to launch when the track's current agent lands):
- **A** (running CFG combinator; A2/A3/A4 done) → **opcode-rule completion**: exactly
  `runs_add`, `runs_lt`, `runs_sload` (+ storage-read companion), `runs_gas` (per C's
  refined "C→A request" in exp005 PLAN.md — JUMP/JUMPI come from the CFG combinator; NO
  halt or CALL `runs_*` needed, the bridge takes halts and CALL is `Runs.call`) →
  **MERGE A→base** (integration gate, unblocks C3; then C rebases) → gas-introspection
  first-class → `CREATE` ctor → symbolic worlds + gas-ledger.
- **B** (running B0 mono) → B2 nested never-OOF (on mono base) → B3 `Ξ` triple +
  call-site/frame rule → B4 IR surface → A-vs-B bake-off verdict.
- **C** (running rebase-safe simplify + C3-plan; C2 done) → [after A→base merge + rebase]
  C3 single-call preservation → C4 multi-call (bridge ready, A3 done) → branch lowering
  (→ gas-introspection preservation theorem) → connect `LirLean` to Plank SIR.

Cross-track deps to respect: C4 waits on A3; C branch-lowering waits on A's CFG
combinator; C rebases on A after A merges to base. If a track's next item is dep-blocked,
launch a **review/simplify pass** on that track's landed code instead (quality work is
never idle). Insert a simplify pass per track roughly every 2–3 milestones. If ALL
tracks are simultaneously dep-blocked (rare), schedule a review wakeup rather than stall.

## Reporting & cleanup policy (Eduardo, 2026-06-22)

Produce documentation **as tracks land, not only at the end**:
1. **Per-track review report** — when a track reaches a stable, reportable state (A after
   opcode-rules + A→base merge; B after B2; C after C3), spawn the **`lean-review-report`
   agent** (read-only, specs-first) to write ONE grounded Markdown report in that
   experiment's `docs/` (e.g. `docs/track-a-review.md`): the goal, the abstraction layers,
   definitions/specs/hypotheses, what depends on what, headline-vs-supporting, with linked
   code blocks / `file:line` refs. **The report MUST ARGUE the design decisions + their
   alternatives** — especially (i) **why `call` is a `Runs` constructor** (and that this is
   what makes the regular-language multi-call composition work — argue it as the report
   would), and (ii) **why the CFG-combinator control-flow design** (`runs_branch`
   disjunction, JUMPDEST handling, loops-as-`trans` back-edges) was chosen, what it buys,
   and what the alternatives were (Eduardo was NOT in that discussion — make the case).
2. **Master experiment report** — `EXPERIMENT-REPORT.md` (repo root) links the per-track
   reports, synthesises results, and says what each means for next steps + the Phase-2
   convergence. Update it incrementally as each track report lands; write the big synthesis
   when all three are done.
3. **End-of-line cleanup sweep** — once tracks mature, spawn review/refactor-finder agents
   that read the docs alongside the code and propose concrete simplification/refactor
   points; APPLY the obvious ones without waiting for Eduardo (open-ended is OK). Keep
   everything clean, green, axiom-clean.

## Resume protocol (for a context-cleared main Claude)

1. Read this file.
2. `git worktree list` and `git branch` — confirm the three worktrees/branches
   exist. If a worktree is missing, recreate: `git worktree add <path> <branch>`
   (branches persist even if worktrees are pruned).
3. For each track, read its local `PLAN.md` **progress log** (agents append there as
   they work) and run `lake build` in that worktree to see real status.
4. Re-spawn the per-track background agents from the briefs captured in each local
   `PLAN.md` ("Agent brief" section). Do NOT rely on old agent IDs — they are
   ephemeral; the briefs are the durable spawn instructions.
5. Update the checkboxes here only after the build confirms a milestone.

**Durability rules for agents (enforced in every brief):** append a dated entry to
your local `PLAN.md` progress log after each meaningful step; commit frequently on
your own branch with clear messages; never touch another track's files; if blocked,
write the blocker into PLAN.md before stopping.

## Orchestration log
- 2026-06-22: **🎉 TRACK C DONE — `wc_preserves` FULLY HYPOTHESIS-FREE + axiom-clean**
  (`5ee984d`; `#print axioms` = `[propext, Classical.choice, Quot.sound]`). A complete
  verified IR→bytecode lowering through an external CALL + storage write + arithmetic +
  gas-dependent branch, depending only on a gas knob `g ≥ 50000`. Post-CALL run closed
  (resumed-gas bound, SLOAD-value/branch-taken, general `RETURN` halt). `wc_preserves_twoCall`
  stays a generic multi-call shape lemma (no concrete 2-call program in `workedCall`; all
  pieces proved). **Merged C→base** (`2482f14`, clean). Track C report predates the close
  → refresh pending. Multi-call needed ZERO new theory — the `Runs.call` payoff.
- 2026-06-22: **C child `CallReturns` CLOSED — kernel-cost wall defeated** (`54b2c7b`, green
  1130). `wc_callReturns` is hypothesis-free (`g`-independent `wcStoredAccounts` +
  `sstore_accounts_congr` dodges the deep-map reduction); `wc_preserves` no longer takes
  `hcall`. ONLY the post-CALL run (`hpost`/`hhalt`) remains — final close launched (block-0
  recompute → taken JUMPI → block-1 RETURN; needs a general `RETURN` halt lemma + resumed-gas
  bound + SLOAD-value/branch-taken). After this, `wc_preserves`/`_twoCall` are FULLY
  hypothesis-free. Still running: B2 mutual-induction crux.
- 2026-06-22: **B2 items 1–2 DONE** (`f460066`, green, axiom-clean; a long 100-min run):
  gas-decrement chain + `X` measure descent proved; item 3 down-payment. Launched the
  **crux attempt** (item 3 finish + item 4 mutual induction, strong-induction-on-fuel
  spine). DECISION: this is the make-or-break B2 run — if item 4 doesn't close, PAUSE B2
  and flag for Eduardo's steer (it's design-sensitive + expensive; 3rd B2 iteration).
  Still running: C child-`CallReturns` close.
- 2026-06-22: **C branch terminator CLOSED + all report cleanups done** (`d4af049`, green
  1129). The foundation blocker is gone (`wc_get_dest_414` via the detotalized
  `validJumpDests`); `ir-design §6` synced to as-built, `Match` doc fixed, `maxHeartbeats`
  hack REMOVED (default budget suffices). Only remaining hypothesis: the concrete child
  `CallReturns` (kernel-cost, not foundations) — final close launched (childXfer/
  sstoreChargeOf_child named-lemma pattern to dodge the deep-recursion wall). After this,
  `wc_preserves`/`_twoCall` should be hypothesis-free. Still running: B2.
- 2026-06-22: **`validJumpDests` DETOTALIZED + A→base merge #2 + C unblocked** (`07c8b8c`;
  merges clean, base green 1130, C green 1129). `validJumpDestsAux` is now a total WF def
  with a full jump-dest characterization (`mem_validJumpDests_of_reachable_jumpdest`,
  `ReachesBoundary`, `Frame.get_dest_of_mem`); Conform still builds; upstreamable to
  philogy. Launched the **C hypothesis-free close**: discharge the branch terminator (via
  the new lemmas) + the concrete child `CallReturns` + the 3 report cleanups (ir-design §6
  sync, Match doc, maxHeartbeats). Goal: `wc_preserves`/`wc_preserves_twoCall` fully
  hypothesis-free ⇒ a complete verified single+multi-call lowering. Still running: B2.
- 2026-06-22: **Track C review report DONE & committed** (`docs/track-c-review.md`, 561
  lines, on `exp005-ir`). Surfaced cleanup items for the C-close / cleanup sweep: (i)
  `ir-design.md §6` describes a generic `IRStep`/`lower_simulates_step` engine that was
  actually built CONCRETELY per `workedCall` — sync doc to as-built; (ii) `Match` doc
  (5-clause conjunction) vs code (6-field structure) — fix doc; (iii) `maxHeartbeats
  2000000` in `WorkedCall.lean` (PUSH32-reduction blowup `wc_preserves` depends on) —
  investigate/contain. These fold into the C hypothesis-free close (after A's
  `validJumpDests` merge) + the end-of-line cleanup sweep. C parked meanwhile.
- 2026-06-22: **C3/C4 ARCHITECTURALLY COMPLETE & verified** (`496ef19`, green 1129).
  Lowering-preservation proved as the bridge half (single-call `lower_preserves` +
  multi-call `wc_preserves_twoCall`) modulo two honest hypotheses. **C4 needed no new
  theory** (Track A's `Runs.call` composes calls) and `decode_lower`+byte-layout are now
  generic. **Foundation finding: `validJumpDestsAux` is a `partial def`** → jump-dest
  validity unprovable without `native_decide`; this blocks the branch terminator. Launched
  **Track A to detotalize it** (vendored-EVMLean fix, upstreamable) + the **Track C
  review report**. Still running: B2 mutual induction. Next: A merges the detotalized
  `validJumpDests` → C rebases → one C agent closes both honest hypotheses (child
  `CallReturns` + branch terminator) ⇒ hypothesis-free C.
- 2026-06-22: **B2 PARTIAL & verified** (`863dc24`, green, axiom-clean). Cornerstone
  (per-opcode gas-positivity, ~140 ops) + fuel bound + base cases proved; remaining = the
  mutual fuel-passing induction (Z→step→X inversion, X descent, cross-layer conservation,
  final mutual induction). Continuation launched. Both proofs now grinding in parallel:
  C3-assembly + B2-mutual-induction.
- 2026-06-22: **C3 PARTIAL & verified** (`b81b331`, green 1126). Semantic core proved
  (Match + all per-construct sims + boundary discharge that already covers multi-call).
  Remaining = byte-layout assembly (`decode_lower` + `lower_simulates_step`); continuation
  agent launched. Track C report deferred until C3 closes. Still running: B2.
- 2026-06-22: **Track A review report DONE & committed** (`docs/track-a-review.md`, 423
  lines; argues `Runs.call` + CFG choices vs alternatives). Fixed master report staleness.
  Report flagged for Phase-2: `Spec.lean`'s surface is frame-level, not observables-only
  (accepted for the low-level layer per project standard; resolve at the shared-interface
  EXPORT boundary). **Track A core now resting at a clean reported milestone** — did NOT
  launch its backlog (gas-introspection is entangled with C's branch lowering; `CREATE` is
  speculative). Loop carried by the two in-flight proofs: **C3** + **B2**.
- 2026-06-22: **A opcode rules DONE + A→base MERGE + C unblocked** (`2615d03`; merge clean,
  base green 1130, C green 1106). Integration gate cleared. Launched: **C3** (single-call
  preservation, now unblocked) and the **Track A `lean-review-report`** (→ `docs/track-a-
  review.md`, arguing the `Runs.call` + CFG design choices). Still running: B2. Track A's
  core flat layer is COMPLETE (`Runs`+call+multi-call+CFG+opcode rules, all merged).
- 2026-06-22: **B0 (mono) + A CFG combinator DONE & verified** (B0 `63e234e`+glob-fix
  green; CFG `bc810cc` green 1129). Yul fully gone from exp004; control-flow combinator
  in exp003. Launched: A **opcode-rule completion** (`runs_add/lt/sload/gas`) → then
  A→base merge; B **B2** nested never-OOF on the mono base (B2 already restored the
  `andSubmodules` glob). C still parked. **Added (Eduardo): END-GOAL convergence section
  (shared `EVMSemantics` interface / equivalence between flat & nested), a reporting &
  cleanup policy (per-track `lean-review-report` docs as tracks land + master
  `EXPERIMENT-REPORT.md` + end-of-line refactor sweep; reports MUST argue the `Runs.call`
  + CFG design choices & alternatives), and created `EXPERIMENT-REPORT.md` skeleton.**
- 2026-06-22: **C rebase-safe prep DONE & verified** (`8946f78`, green 1106). Simplify +
  `Match` plan + C→A rule request. **C now PARKED** (dep-blocked on A→base merge) — did
  NOT launch a new C task (would be busywork; A+B carry the loop). Sharpened A's pending
  opcode-rule task to exactly `runs_add`/`runs_lt`/`runs_sload`(+read)/`runs_gas`
  (JUMP/JUMPI come from the in-flight CFG combinator; no halt/CALL rules needed).
- 2026-06-22: **C2 DONE & verified** (`bde1913`, green 1106, axiom-clean). Decode-compat
  lowering + ~40 round-trip checks. Surfaced the **integration bottleneck: Track A is
  upstream of C3** — C's lowering emits SLOAD/ADD/LT/GAS/JUMP/JUMPI/STOP/RETURN but
  exp003 has `runs_*` only for PUSH/SSTORE+call; those rules (Track A) must land + A must
  merge to base before C3. Action: queued opcode-rule completion onto A (after CFG) + an
  A→base merge gate; launched C on rebase-safe simplify + C3-plan + the C→A rule request.
- 2026-06-22: **A2+A3 DONE & verified** (`aa141e7`, green 1128, axiom-clean). Multi-call
  composition works (`messageCall_runs_calls` + `TwoCallExample`); **the intermediary-call
  defect is fixed, C4 unblocked.** Launched A's next: **CFG combinator** (JUMP/JUMPI +
  branch helper). Still running: C (C2), B (mono). Stale review-report.md doc refs queued
  for a later regen pass.
- 2026-06-22: Plan created. exp003 vendored EVMLean + cleanup already committed on
  base. Three worktrees + branches created (`exp003-runs-call`, `exp004-nested`,
  `exp005-ir`), each with a committed local `PLAN.md`.
- 2026-06-22: **M1 background agents launched for all three tracks** (bounded: each
  does only its M1, appends to its PLAN.md progress log, commits on its branch,
  then stops + reports). On resume: do NOT look for these agents (ephemeral); read
  each PLAN.md log + `lake build`, then re-spawn from the PLAN.md "Agent brief".
- 2026-06-22: **Round 2 launched** (bounded background agents): A2+A3 (one bridge +
  multi-call composition — A3 expected light since `drive_reconcile` already inducts
  through `.call` nodes; the "regular-language" shape IS the `refl`/`step`/`call`
  closure), C2 (single-call decode-compatible lowering + #eval validation), B2 (nested
  never-`OutOfFuel` on `Ξ/Θ`, may land partial — it's a mutual fuel-passing induction).
  Backlog recorded above. On resume mid-round: verify each via `lake build` + `git log`
  in its worktree (do NOT trust agent self-reports of committed/green).
- 2026-06-22: **A1 DONE, green & committed** (`exp003-runs-call` @ `7be5a5b`, 1127
  jobs, axiom-clean — verified by main loop, not just self-report). The `Runs.call`
  constructor lands index-free; `messageCall_call_runs` collapsed to a 3-line
  corollary. **First full bootstrap iteration complete: all three M1s green.** Next:
  A2 (surface collapse to one bridge) + **A3 (multi-call composition, the unblock for
  Track C)**; C2 (single-call lowering, can start now); B2 (nested never-OutOfFuel).
- 2026-06-22: **B1 + C1 DONE, both green & committed** (B `20ad4c1`, C `505c83b`;
  the C agent finished its work but failed to commit — main loop committed it, closing
  the gap). Track A (`Runs.call`) still running. **KEY CROSS-TRACK FINDING (C, the C4
  question, surfaced early): exp003's call sequencing CANNOT express ≥2-call programs**
  — a CALL is `Signal.needsCall`, not a `StepsTo`/`Runs` link, so `Runs.trans` can't
  glue it; the bridge is hard-wired to exactly one `CallReturns`. ⇒ **Track A's
  `Runs.call` constructor is the confirmed critical path**; C's single-call lowering
  (C2) can proceed now, but multi-call (C3/C4) is blocked on A1–A3.
