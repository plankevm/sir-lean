# exp005 Execution Plan — waves & track ownership (2026-07-02)

*Operationalizes `target-architecture-2026-07-02.md` §10 with the lead's amendments:
(1) engine facts move SUBDIRECTORY-FIRST (`LirLean/Engine/`), exp003 promotion deferred to
post-Phase-3; (2) parallel tracks run in separate git worktrees with CLONED `.lake` caches
(never rebuild cold); (3) every track runs an audit cycle (planner → implementer → reviewer,
one fix round); (4) after each wave the lead's main thread merges all track branches into
`exp005-honesty-cleanup`, resolves conflicts, full-builds, and only then launches the next wave.*

> **STATUS (2026-07-03).** Waves 1–4 executed (HEAD `53c2063`). The Lean file paths cited inline
> below (`TieDischarge.lean`, `RunLog.lean`, `Mono`/`Oracle`/`HonestGasTie`) reflect the
> PRE-execution tree and have since moved or been deleted — see the redirect map in
> `headline-transitive-chain.md`. Internal line numbers are left as provenance-at-time-of-writing.

## Global constraints (every track, every wave)

- Build green: `cd experiments/005_ir_lowering && lake build` (background the command if >8 min;
  incremental builds on a cloned cache are minutes, not the ~1 h cold build).
- Axiom-clean: headline theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- Zero `sorry` in the default `LirLean` target. The `Nightly` realisability-spec lib (Track E)
  is the ONLY sorry-carrying lib, by design.
- No new supplied hypotheses on any existing theorem; no weakening of any conclusion.
- Declaration names and namespaces unchanged unless this plan says otherwise (moves are
  import-churn only).
- The vacuity lesson (skeptic-f1-verdict.md) is the review standard: any NEW `Prop` statement
  must be checked for satisfiability — quantifier by quantifier, "can an adversarial witness
  refute this ∀?" — before it is accepted.
- Commit per logical step, message prefixed `exp005 <track>:`. Never push. Never touch `main`
  or another track's worktree/files.
- Do not run `lake update`; do not delete `.lake` (cloned caches).

## Wave 1 (parallel; three worktrees off `exp005-honesty-cleanup`)

### Track A — audit net (`exec/audit-net`, worktree `.worktrees/exec-audit-net`)
NEW `LirLean/Audit.lean`, imported LAST in the `LirLean` root. Content:
1. `#guard_msgs`-pinned `#print axioms` for the ~10 decls that matter:
   `lower_conforms_cyclic_assembled`, `_tiefree`, `lower_conforms_wf`,
   `callPreservesSelf_modGuards`, `materialise_runs_of_cleanHalt`, `cleanHalts_of_runWithLog`,
   `jump_landing_of_cleanHalt`, `branch_landing_of_cleanHalt`, `stepPreservesSelf`,
   `sim_assign_sload_lowered`. (Run each first to capture the exact current message.)
2. A signature-freeze guard on the flagship (`#guard_msgs in #check @…_assembled`). If the
   rendered type is unwieldy/unstable, fall back to axiom guards + a docstring-pinned copy and
   record the decision.
3. Linter baseline: attempt `lake exe runLinter LirLean` (background; generous time). If it
   runs: triage, freeze `nolints.json`. If infeasible: record why in `docs/exec/audit-net.md`.
OWNS: `LirLean/Audit.lean` (new), one import line at the END of `LirLean.lean`, `nolints.json`,
`docs/exec/audit-net.md`. Does NOT delete the 252 scattered `#print axioms` (that is Wave 4).

### Track B — Phase 2 gas-law removal (`exec/phase2-gaslaw`, worktree `.worktrees/exec-phase2`)
Per `gas-decision.md` + target-architecture §4.1, with the KEEP amendment:
1. Grep-verify the import/reference graph first (who imports `V2/Mono.lean`, `V2/Oracle.lean`,
   `V2/HonestGasTie.lean`; which `Oracle` defs `RunLog.lean` references).
2. DELETE the three files. `realisedGas`/`realisedCall`/`callOracleOf`/`observe`/`runWithLog`
   stay fully intact; if live code needs a def currently in `Oracle.lean`, INLINE it into its
   consumer with a `-- RELOCATED from V2/Oracle.lean (Phase 2)` note.
3. Narrow `V2/Law.lean` to determinism (keep the four `.det`; delete the gas-monotone law
   material). Delete `RunLog.lean`'s gas-monotonicity section (`geToNat`/`bound_mono`/
   `driveLog_gas_inv`/`realisedGas_monotone` + their `#print`s) and now-dead imports.
4. Do NOT touch `V2/TieDischarge.lean`; do NOT remove the `DriveCorrPlus` accumulator params
   (they become the Wave-4+ recorder-coupling field, target-architecture §3).
5. Append the lesson paragraph to `docs/gas-decision.md`: the retired `Lir.GasRealises`
   universal was unsatisfiable (HonestGasTie's finding), and the 2026-07-02 skeptic verdict
   shows the same free-∀ disease in the current StmtTies/TermTies — pointer to
   `fleet-2026-07-02/skeptic-f1-verdict.md`.
OWNS: the three deleted files, `V2/Law.lean`, `V2/RunLog.lean`, root import lines,
`docs/gas-decision.md`, `docs/exec/phase2-gaslaw.md`.

### Track E — realisability spec skeleton (`exec/realisability-spec`, worktree `.worktrees/exec-respec`)
The design track (hardest thinking, no existing-code edits). Deliverable:
`LirLean/V2/RealisabilitySpec.lean` (+ helpers if needed) registered as a NEW NON-DEFAULT
`lean_lib Nightly` in `lakefile.lean` (`lake build Nightly` must elaborate; sorry bodies
allowed and expected). Content per target-architecture §2/§5 + `fleet-2026-07-02/
flagship-signature.md` §1/§5:
1. Helper defs: `entryState`, `RunLog.clean`, `Conforms`, `WellLowered` (folds
   hwfl/hdef/presence/stack bounds), `PrecompileSeams`, `SingleCall`, and — the hard design
   piece — `RecorderCoupled` (the recorder-suffix coupling invariant, §3 of target-architecture).
2. Reshaped tie statements `StmtTies'`/`TermTies'`: value conjuncts pinned to the consumed
   suffix head; **NO free-∀** (this is R0 as statements).
3. Obligations R1–R11 as sorry'd theorems; R12 as a sorry'd concrete example skeleton.
4. Header docstring: the tracked-debt declaration + the HonestGasTie/F1 lesson; per-decl
   docstrings say what is supplied vs derived.
Uses only defs that survive Track B (do NOT reference `GasRealises`/`Mono`/monotonicity decls).
REVIEW BAR (the critical one): the reviewer must ATTACK each statement's satisfiability the way
skeptic-f1 attacked StmtTies — an accepted statement with a refutable ∀ is a review failure.
OWNS: new files under `LirLean/V2/` (or `LirLean/Realise/`), one `lean_lib` block in
`lakefile.lean`, `docs/exec/realisability-spec.md`.

## Wave 2 — Track C, engine split (after A+B+E merge)
(1) Prove `stepFrame_next_execEnvAddr`; derive the SelfAt walk as the `a := self` corollary of
`_next_accMono` (~1,000 lines saved). (2) Move the pure-engine spans of `TieDischarge.lean`
(the `namespace Evm` spans + engine-level `Lir.V2` blocks) plus, if import-clean, `MemAlgebra`,
`CleanHalt`, `CleanHaltExtract` §0–§2, `V2/DriveRuns`, `Charges` into NEW `LirLean/Engine/`
(decl-by-decl, names unchanged — subdirectory-first; exp003 promotion is post-Phase-3).
(3) Split the TieDischarge remnant at namespace boundaries → `Drive/{SelfPresent,
CallPreservesSelf,Headline}.lean`. Update `Audit.lean` guards in the same commits.
(4) **Descent shaping (CREATE prep, settled 2026-07-02):** while organizing the moved
invariants, group the per-kind CALL/CREATE descent lemmas (`stepFrame_needsCall_inv` /
`_needsCreate_inv`, `beginCall`/`beginCreate` presence+checkpoint, `resumeAfterCall`/
`resumeAfterCreate` accounts facts) under ONE `DescentKind`-parameterized interface
(needs/begin/resume projections + laws; `DescentReturns k` generalizing `CallReturns`) with
CALL and CREATE as its two instances. Organization of existing green lemmas, NOT new proofs —
this is what makes first-class CREATE (Phase 3.5 below) an instantiation instead of a second
Call.lean ecosystem. The `hprec` seam is the CALL instance's begin-immediate law; CREATE's
analogue is trivial post-RLP-totality.

## Wave 3 — Track D, Spec/ extraction (after C)
Per `fleet-2026-07-02/reorg-legibility.md` §1/§5 Step 3: `Spec/{IR,Semantics,Lowering,Layout,
Recorder,Seams,Conformance}.lean` (pure moves + the transitional Pattern-C conformance
re-export + `RealisabilityObligations` structure); rewrite the `LirLean.lean` root as a clean
import list.

## Wave 4 — closeout
Mass-delete the ~252 scattered `#print axioms` (grep worklist; `Audit.lean` is the net);
re-run the linter; sync living docs (PLAN/HANDOFF/remediation-plan → pointers to
target-architecture); FINAL AUDIT FLEET over the merged result (did we actually reduce the
supplied surface? is anything new refutable? are the moves faithful?). Then Phase 3 proper
(the R-obligation grind) starts against `RealisabilitySpec.lean`.

## Post-Phase-3 roadmap (order settled 2026-07-02)

- **Phase 3.5 — first-class CREATE** (settled: not instantiating it was a scope decision now
  reversed; unified machinery, not duplication). On top of the Wave-2 `DescentKind` interface:
  `Stmt.create` + `CreateSpec` in the IR (inputs: `LirLean/Create.lean`'s existing
  `CreateOracle`/`evmCreateOracle` + the 4 spec-authoring guardrails in
  `docs/create-crosscheck.md`, verdict "GO"); lowering emits CREATE/CREATE2; the simulation
  instantiates the descent machinery (`DescentReturns .create`, one more `DescentRecord`
  arm in the recorder, one more realises-bundle instance). `NoCreateBytes` is then RETIRED —
  replaced by the localized "descents occur exactly at emitted descent sites" predicate over
  the R6 boundary walk (which survives: it is the instruction-alignment fact, also needed for
  data segments). The multi-descent recorder question is the same as the multi-CALL one (R3');
  solve them together (descents as a consumed stream).
- **Alloc generalization** (may run parallel to 3.5): retire the `slotOf` pins for
  `Placement`/`ValidPlacement` if not already done inside Phase 3's reshape.
- **Memory** (object-granular, UB-as-stuckness) → **data segments** (data-after-code,
  CODECOPY; needs memory first) — per `fleet-2026-07-02/future-proofing.md` §3/§5.
- **exp003 promotion**: `Engine/` + recorder + Asm algebra graduate to the exp003 surface
  (`Exec`/`Recorder`/`Invariants`/`Asm`/`CyclicSim`) once Phase 3 has shown which shapes the
  closure consumes. IR #2 starts against that surface.

## Worktree & cache protocol
Worktrees are created by the lead with `.lake` caches CLONED from `.worktrees/ir-lowering`
via APFS `cp -Rc` (instant, copy-on-write). Agents: never `lake update`, never remove `.lake`,
background any build that might exceed the shell timeout, and verify "Build completed
successfully" before committing.

## Merge protocol (lead, between waves)
Merge order A → B → E into `exp005-honesty-cleanup`; expected conflicts only in `LirLean.lean`
root imports and `lakefile.lean` (trivial). After merging: full `lake build` + `Audit.lean`
green + spot-check axiom guards, commit the merge, delete the wave's worktrees/branches, then
launch the next wave.
