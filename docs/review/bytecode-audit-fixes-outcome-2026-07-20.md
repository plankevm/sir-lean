# Bytecode audit fixes — outcome (2026-07-20)

Execution record for the prioritized backlog of
`docs/review/bytecode-layer-audit-2026-07-18.md` (main repo). Five tracks, five
commits on `codex/bytecode-audit-fixes`, every track independently re-gated by its
reviewer before commit. All of P0, all of P1, and the core P2 cluster (D8+E7, D7
stretch) landed. Working tree clean at `b1156f9b`.

## Commits

| Track | Commit | Files | Delta | Scope |
|---|---|---|---|---|
| T1 docs-truth-sweep (P0.1) | `04e40b68` | 22 | +246/−123 | Doc/comment-only + `CreateReturns` abbrev + AGENTS.md carve-out |
| T2 local-dedups (P0.2 + P1: D5, D4, V8, S8) | `dded9834` | 4 | +43/−79 | DriveRuns, CyclicSim, ConcreteSpecs, OutcomeBridge |
| T3 fuel-reconcile + framing (P1: E2/D2, E1) | `0d50ee23` | 4 | +169/−253 | CallSequence, DriveRuns, DescentEq, CyclicSim |
| T4 witness-dedup + decisions ledger (P1: D10, V7) | `cd2ec64e` | 2 | +54/−26 | WitnessChecks + new decisions ledger doc |
| T5 CREATE consolidation (P2: D8, E7-core, D7) | `b1156f9b` | 5 | +220/−781 | Recorder, Descent, StepWalk, both System.lean |

**Net: +732/−1262 = −530 lines**, with zero capability deletion: every public
name and statement survives verbatim (folded lemmas became corollaries of
strictly-stronger spines), zero sorries introduced, no protected/Do-NOT-touch
mass modified (CyclicSim edits confined to blessed proof-body loci; Producer,
Machinery, RealisabilitySpec untouched).

## Per-backlog-item ledger

### Done (P0 — all)

- **V1/S5** — all 10 `(SPIKE)` tags deleted; "R4" plan-jargon reworded
  self-containedly; `Create.lean:200` pointer qualified (63/64 guard verified at
  that line). Post-edit grep `SPIKE|R4` in BytecodeLayer: zero hits.
- **V2/S1/S9** — root `BytecodeLayer.lean` header rewritten: exp003 name dropped,
  `.andSubmodules` glob documented, Exec/Asm export surface documented, EVMSpec
  de-aggregation (28e01243) noted, "canonical = `EVMSemantics`/`flatSem`"
  breadcrumb added.
- **V3** — Spec.lean retitled "audit surface of the Hoare program-logic layer";
  settled altitude ruling replaces "To reconcile"; carve-out recorded in AGENTS.md.
- **V4** — dangling `docs/generalization-plan.md` citation dropped from Behaves.lean.
- **V5** — record-only: docstring on the `MonadLift Option` instance
  (PrimOps.lean) explaining the generic none-lift tag; no rename. Reviewer fix:
  Dispatch's PUSH branch throws `.StackUnderflow` explicitly, not via the lift —
  docstring corrected before commit.
- **V6** — verified-empty in-repo (no open backlog/roadmap sload-stream entry);
  the stale artifact is the *memory note* — orchestrator follow-up, outside this
  worktree (see Follow-ups).
- **V9** — 3 `ir-design-v2.md` citations normalized to full exp005 path;
  GasMonotone fold relic fixed (`LirLean/Mono.lean` confirmed deleted).
- **V10** — exp003/leanevm naming sweep across 14+ files, zero residual hits
  (sole survivor: deliberate "formerly experiment 003" note); TransCmp-gap claim
  and live exp004 cross-refs preserved.
- **S2** — phantom `messageCall_runs_completed` removed; Outcome-bridge
  re-attributed to `messageCall_calls_completedWith`.
- **S3** — `abbrev CreateReturns := Hoare.CreateReturns` added to Spec.lean;
  7 call-only docstrings updated for the CREATE channel.
- **S4** — CallReturns provenance corrected; "three call-facts" → "four".
- **S6** — full docstrings on `driveLog`/`runWithLog` incl. explicit WARNING that
  CREATE lowering must add a CREATE soft-fail arm.
- **S10** — doc-only: `offsetBytesBE`/`wordBytesBE` docstrings + import-cycle
  hosting rationale; no module move.
- **M8-doc** — IRRun.lean header rewritten to actual content (retired
  `irRun_exists_*`/`CFGAcyclic` moved to a historical note; `RunDefinableG`
  replacement noted). Header-only.
- **D5** — unprimed `.call` specialization deleted; generic
  `child_ne_oof_of_framed'` renamed to the unprimed name; all 6 call sites
  updated; net −13 lines.

### Done (P1 — all)

- **E2/D2** — `drive_ok_agree` added (Hoare/CallSequence.lean:91, 1-line
  corollary of `drive_eq_of_both_ne_oof`); all 6 max-lift ritual sites rewritten
  (4 CyclicSim recorderCoupled proof bodies + 2 DriveRuns `runs_of_drive_ok`
  arms, deleting the case-split scaffolding). The two `Runs.drive_reconcile`
  sites left untouched as specified.
- **E1** — the single 8-arm framing induction now lives once as
  `drive_append_framing_lt` in DescentEq.lean (import direction verified, no
  cycle); `drive_append_framing`, `drive_descend_eq`, `drive_descend_create_eq`
  re-derived as one-line weakenings with byte-identical statements. Net −84
  lines (matched the ~80-85 estimate).
- **D4** — `recorderCoupled_halted_inv` + `_suffixes_nil` hoisted verbatim; the
  `calls_nil`/`creates_nil_of_stepFrame_halted` twins are now `.2.1`/`.2.2`
  projections, signatures unchanged. Net −50 lines in CyclicSim.
- **D10** — `callsCodeOk_along_runs` shared lemma (local route, no CyclicSim
  import); both checker-soundness twins collapsed to two-liners over it + per-twin
  heads; all four public statements verbatim; WitnessParams.lean untouched.
- **V8** — resolved on the recommended KEEP arm: HoareDemo imported from
  ConcreteSpecs + cross-linked as the repo's one concrete framing theorem.
  **Awaits Eduardo's confirmation** (planner decision #4).
- **V7/S9** — EVMSpec banner already truthful from T1; decisions ledger created:
  `docs/review/bytecode-audit-decisions-2026-07-20.md` (four open calls, below).
- **S8** — dead `import BytecodeLayer.Hoare.Behaves` dropped from
  OutcomeBridge.lean; Behaves.lean kept (incremental lemma). Full
  surface-or-annotate decision recorded as open in the ledger.

### Done (P2 — core cluster)

- **D8(1)** — `Evm.createSoftFailResult` / `Evm.createPendingOf` named in the
  vendored engine; `softFailCreateRecord`'s 16-line literal pair → 2 lines;
  6 StepWalk key-literal sites rewritten. Engine touch verified
  conform-transparent by G5, not assumed.
- **D8(2)+E7-core** — existing `systemOp_createArm_reduce` strengthened in place
  (charge chain + op-indexed CREATE/CREATE2 pop-residual disjunction); new
  single-spine `createArm_next_inv` (7-conjunct `.next` inversion); ~10 StepWalk/
  System per-fact lemmas folded into corollaries; 12 consumer destructure sites
  widened; every public name (incl. Descent.lean wrappers) survives verbatim.
- **D7 (stretch)** — parametric `stepFrame_next_smsf_pc` + `stepFrame_next_binOp_pc`;
  the 8 per-opcode `stepFrame_next_<op>_pc` names survive as 1-line corollaries
  (hyps discharged by `decide`/`rfl`); exp005 BoundaryReach consumers compile
  unchanged. `smsf_<op>_next_pc` family untouched as prescribed.

T5 alone: −561 lines, exceeding the audit's ~400-line D8 estimate.

### Skipped / deferred (with why)

- **E6** (stash-tail fr-level restatement) — deferred: excluded from T5's
  selection to keep the CREATE cluster atomic; still worth scheduling.
- **D6** (generic iterate/shift/final theory) — deferred: requires validating the
  `decide +kernel` canary first; medium effort, standalone.
- **D1 (+D3)** (recorderCoupled peel consolidation) — deferred *and discounted*:
  dissolving mass under the SIR retarget (audit Do-NOT-touch #5); do only if the
  retarget horizon lengthens.
- **E4 option (a)** — deferred, same dissolving-mass discount as D1/D3.
- **P3 items (E3/D9, E5, E8, S7, M-ledger)** — untouched by design: pilot-gated
  or folded into the SIR retarget plan.

## Gate evidence (every track, implementer + independent reviewer re-run)

- **G1** `lake build Evm BytecodeLayer Conform` — green, 1173 jobs, all 5 tracks.
- **G2** exp005 `lake build` — green (1189–1190 jobs).
- **G3** `lake build WIP` (flagship cone) — green (1200–1201 jobs).
- **G4** flagship axioms **unchanged** at every gate: `Lir.lower_conforms`,
  `lower_conforms_exact`, `lower_conforms_gasfree` each exactly
  `[propext, Classical.choice, Quot.sound]`; empty diff vs the pre-edit baseline
  recorded in `.gates/` before any change.
- **G5** `lake exe conform 8` — **2859/2859 succeeded, 0 failed, 0 xfail** at
  every gate, identical to baseline; per-test diff empty after stripping the
  nondeterministic `-- Nms` timing suffixes (raw diffs differ only in wall-clock
  noise, present between baseline reruns too).

Only pre-existing linter warnings observed (all present in the baseline logs).

## Discovered stale in the audit report itself

- **M8 path**: `IRRun.lean` lives at `experiments/005_ir_lowering/LirLean/IRRun.lean`,
  not the report's `LirLean/Drive/IRRun.lean`.
- **Line anchors drifted** slightly (e.g. D5's unprimed lemma at DriveRuns:317,
  not :315; D5 call sites at :414/:454 pre-edit). All anchors were re-verified by
  grep before editing; none were semantically stale.
- **V6**: confirmed the report's own "seed RESOLVED" reading — the stale artifact
  is the out-of-repo memory note, nothing in-repo.
- `child_ne_oof_of_framed'`'s only surviving mention repo-wide is a dated
  recommendation in `experiments/005_ir_lowering/docs/review/tour-2026-07-09/01-trusted-base.md`
  — historical record, deliberately left.

## What remains (updated estimates)

**P1: empty.** All seven P1 backlog items (#3–#9) landed.

**P2 remaining:**
1. **E6** stash-tail fr-level restatement + envelope shrink (3 exp005 twins, both
   cones gated) — ~half-day; highest-value remaining item.
2. **D6** generic Machine/steps/shift/final + stepsChk — ~half-day, gated on the
   `decide +kernel` canary validating first.
3. **D1/D3** and **E4(a)** — discounted to near-zero priority: dissolving mass
   under the SIR retarget; recommend dropping unless the retarget slips a quarter.

**P3: unchanged** (E3/D9 pilot-gated on a `nextDrive` reification; E5/E8 parked;
S7 fold into a future touch; M1–M10 are retarget-plan input, not standalone work).

## Open decisions for Eduardo (ledger: `bytecode-audit-decisions-2026-07-20.md`)

1. EVMSpec adopt-vs-archive (banner now truthful either way).
2. Option-B State/Result ratification (pending).
3. Behaves: minimally resolved (annotated + dead import dropped); full surfacing open.
4. HoareDemo KEEP arm — implemented per recommendation, awaiting confirmation.

## Orchestrator / environment follow-ups

- Update `~/.claude/.../memory/sload-stream-vestigial.md` closing line to
  "landed on main at 33e572b2" + the MEMORY.md index one-liner (outside this
  worktree; carried from T1).
- The `EVM/EthereumTests` symlink (→ `forks/leanevm/EthereumTests`) is an
  untracked worktree-local workaround for the submodule-in-worktree init failure;
  MUST stay uncommitted. `.gates/` + the symlink were added to the *shared*
  `/Users/eduardo/workspace/evm-semantics/.git/info/exclude` during T2 (the
  worktree-local exclude is not consulted by git).
