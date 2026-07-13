# Track Report — Reorganization & Legibility (exp005)

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


*Grounded in the worktree at `/Users/eduardo/workspace/evm-semantics/.worktrees/ir-lowering` (branch `exp005-honesty-cleanup`, post-Phase-1). All sizes measured with `wc -l` today; all locations verified by grep.*

**Measured baseline:** `LirLean/` is 24,670 lines across 43 files. Five files over 1,000 lines: `TieDischarge.lean` (4,507 — was 5,027 pre-Phase-1; headline `lower_conforms_cyclic_assembled` now at :4292), `LowerDecode.lean` (1,517), `LowerConforms.lean` (1,497), `MaterialiseRuns.lean` (1,370), `SimStmt.lean` (1,196), plus `CleanHaltExtract.lean` (1,169). `#print axioms` count is now **252** across 29 files (audit's 270 was pre-Phase-1), concentrated in TieDischarge (73) and CleanHaltExtract (53). Both packages are on `leanprover/lean4:v4.30.0` with Mathlib/Batteries in the manifest.

---

## 1. Target file tree

### Design constraint first: the spec core

A reviewer should be able to read the entire trusted/reviewable surface without opening a proof file. The current code already contains most of it — it is just interleaved with proofs. The core, post-reorg:

| File | Role | Est. lines | Imports | Content (source today) |
|---|---|---|---|---|
| `LirLean/Spec/IR.lean` | SPEC | ~115 | `Evm` | IR datatypes, verbatim. Already perfect — "datatypes only" (IR.lean:16). |
| `LirLean/Spec/Semantics.lean` | SPEC | ~280 | `Spec.IR` | The executable gas-free IR machine: `IRState`, `evalExpr`, `RunStmts`/`RunFrom`/`IRRun`, `Observable`, `CallOracle` (today `Machine.lean`, 277 ln, 16 defs, near-zero proofs — already clean). |
| `LirLean/Spec/Lowering.lean` | SPEC | ~380 | `Spec.IR`, `Evm` | `lower`/`allocate`/`defsOf`/`recomputeFuel` (today `Lowering.lean`, 415 ln; move its 3 theorems at :257/:297/:360 to `Proofs/`). |
| `LirLean/Spec/Layout.lean` | SPEC | ~205 | `Spec.Lowering` | `offsetTable`/pc arithmetic (today `Layout.lean`). |
| `LirLean/Spec/Recorder.lean` | SPEC | ~300 | `Spec.Semantics`, `BytecodeLayer` | `runWithLog`, `RunLog`, `CallRecord`, `realisedGas`/`realisedCall` (today `RunLog.lean:219` etc.; the file is 674 ln — Phase 2 deletes the gas-monotonicity section from :580 on, and the remaining proofs about the recorder go to `Proofs/`). |
| `LirLean/Spec/Correspondence.lean` | SPEC | ~150 | Spec files + `BytecodeLayer` | `Corr` (today buried at SimStmt.lean:103), `MemRealises`, `StepScoped`, `DriveCorr` (DriveSim.lean:87), `CleanHaltsNonException` re-export. The one fiddly extraction — see §2. |
| `LirLean/Spec/Seams.lean` | INTERFACE | ~120 | Spec files | The named irreducible oracles, one docstring each: `SelfPresent`, `CallPreservesSelf` + `hprec` shape, `CallsCode`, `CleanHaltsNonException` — exactly the four survivors per `docs/headline-transitive-chain.md` §3. This file **is** the tracked-debt register the sorry-equivalence policy requires. |
| `LirLean/Spec/Conformance.lean` | SPEC | ~250 | all Spec | The flagship **statement** as a `Prop`-valued def + `RealisabilityObligations` structure + the helper defs the statement needs (`codeFrame`, `observe` re-exports). See §2 for mechanics and the pre-/post-Phase-3 variants. |

**Spec core total: ~1,800 lines in 8 files** (~7% of the package), plus exp003's existing audit surface `BytecodeLayer/Spec.lean` (258 ln) and `Frame`/`Runs` (reviewer needs those to read `Conformance.lean`) — call it **~2.3k lines end-to-end**. Everything else is proofs/nightly.

### Full tree (post Phases 2–4; sizes assume Phase-2 deletions, ~1,000-line dispatch-walk unification, ~1,100 lines relocated to exp003)

```
LirLean/
├── Spec/                          -- ~1,800 ln, the 8 files above
├── Bytecode/                      -- PROOF: v1 bytecode-coupled simulation bricks
│   ├── SmallStep.lean   PROOF ~130  (v1 reference semantics; AUDIT: check still on-cone, else _attic)
│   ├── Call.lean        PROOF ~165  Create.lean PROOF ~110  Match.lean PROOF ~400
│   └── Charges.lean     PROOF ~32
├── Decode/                        -- PROOF: pc/offset/jumpdest layer (no fork analogue; ours)
│   ├── DecodeLower.lean ~160   DecodeAnchors.lean ~320   JumpValid.lean ~515
│   ├── BoundaryReach.lean ~435  NoCreateBytes.lean ~433
│   └── Landing.lean     PROOF ~1,100  (today LowerDecode.lean 1,517; split out the shared
│                                       `landing_at_block_offset` per audit §8 — the 322-ln
│                                       branch_landing at LowerDecode.lean:755 shares ~600 ln
│                                       with jump_landing; factoring saves ~400)
├── Materialise/                   -- PROOF: spill/recompute value channel
│   ├── MemAlgebra.lean ~980   DefsSound.lean ~580   MaterialiseGas.lean ~250
│   ├── MaterialiseRuns.lean ~700 + MaterialiseRunsLemmas.lean ~650  (split of 1,370)
│   ├── MaterialiseCleanHalt.lean ~406   MatDecLower.lean ~516   StashTail.lean ~523
│   └── CleanHalt.lean ~107   CleanHaltExtract.lean ~1,170 → split at the §-boundaries into 2
├── Sim/                           -- PROOF: per-statement/terminator simulation
│   ├── Ties.lean        INTERFACE ~250  (StmtTies/TermTies/WellFormedLowered defs, today
│   │                                    LowerConforms.lean:1273/:1342/:143 — see §2)
│   ├── SimStmt.lean ~1,000 (minus Corr, moved to Spec)   SimStmts.lean ~165   SimTerm.lean ~760
│   └── BlockAssembly.lean PROOF ~1,250  (rest of LowerConforms.lean: simStmtStep_block etc.)
├── Drive/                         -- PROOF: cyclic-CFG drive recursion + headline proof
│   ├── DriveRuns.lean ~375   Modellable.lean ~490   DriveSim.lean ~755
│   ├── SelfPresent.lean PROOF ~500   (TieDischarge §5 + SelfPresent-forward, :381-:602/:1488-)
│   ├── CallPreservesSelf.lean PROOF ~650 (Brick D + discharge chain, TieDischarge :2916-:3555)
│   └── Headline.lean    PROOF ~900   (DriveCorrPlus + edge wrappers + lower_conforms_cyclic_*,
│                                      TieDischarge :3555-4417 minus Phase-2 field removal)
├── Realise/                       -- PROOF (Phase 3, new): the realisability closure
│   ├── GasTies.lean, SloadTies.lean, CallTies.lean, TiesOfRunWithLog.lean   ~1,500-2,000 total
├── Examples/
│   └── EndToEnd.lean    EXAMPLE ~300  (Phase-3 item 6: one concrete `lower prog` instantiated;
│                                       the non-vacuity witness)
├── Audit.lean           AUDIT ~150    (see §3)
└── (root) LirLean.lean  — clean import list; today it is 90 lines of NOTE-archaeology
```

**New exp003 files** (Phase 4 targets, per audit §7 / remediation Phase 4):

```
003_bytecode_layer/BytecodeLayer/
├── Hoare/AccountsMonotone.lean  PROOF ~900   unified AccPresent/AccMono dispatch walk (the
│                                             a:=self corollary replaces the ~920-ln SelfAt walk),
│                                             stepFrame_next_execEnvAddr, needsCall/needsCreate
│                                             inversions, halt-success accMono
│                                             (today TieDischarge Evm-spans :543-587, :604-1486, :1653-2914)
├── Hoare/AccountMap.lean        PROOF ~120   RBMap/AccountMap primitives + charge invariance
└── Spec.lean                    — gains ~30 ln re-exporting the new general rules (existing pattern)
```

Result: exp005 shrinks from 24.7k to roughly **20-21k** lines (Phase 2 ≈ −1.7k incl. `Mono.lean` 620, `Oracle.lean` 205, `HonestGasTie.lean` 316; Phase 4 ≈ −3.1k), no file over ~1,300 lines, and the reviewer path is `Spec/` + `Examples/EndToEnd.lean` + `Audit.lean`.

**Naming note (recommend, cheap):** once `Mono|Oracle|HonestGasTie` are deleted and `Machine/Law/IRRun/RunLog` move into `Spec/`, the `` directory and the `Lir` *file* layout disappear naturally. Keep the `Lir` **namespace** unchanged (renaming namespaces touches every proof; renaming files/dirs only touches imports).

---

## 2. Spec/proof separation mechanics

### What the code already does well vs badly

Done well today:
- **exp003 `BytecodeLayer/Spec.lean`** — "This is the file to read" (Spec.lean:14) re-exports each general theorem with a fresh docstring and `:= Hoare.proof_name` body. This is the house pattern; copy it.
- **`IR.lean`** and **`Machine.lean`** — genuinely defs-only spec files already.
- **`StmtTies`/`TermTies` as named `Prop` defs** (LowerConforms.lean:1273/:1342) — the obligation *statements* are already first-class terms, which is exactly what makes the Phase-3 "build them, don't supply them" plan stateable.

Done badly today:
- **`TieDischarge.lean`** interleaves `namespace Evm` / `namespace Lir` six times (:543/:589/:604/:1488/:1653/:2916), holds a spec-level definition (`DriveCorrPlus` :3589) 700 lines before the headline (:4292), inside 4.5k lines of engine walks.
- **The flagship exists only as a 16-hypothesis theorem in a proof file.** There is no standalone statement a reviewer can read without scrolling TieDischarge.
- **`Corr`** — the central IR↔frame coupling relation — is at SimStmt.lean:103, inside a 1,196-line proof file.
- **`RunLog.lean`** mixes the recorder definition (:219) with the (soon-deleted) monotonicity theory (:580+).

### The three patterns, and where each applies

**Pattern A — statement-as-def (for the flagship).** In `Spec/Conformance.lean`:

```lean
/-- The flagship: running `lower prog` once with the recorder and feeding the
    recorded gas/sload/call values into the IR oracles yields the same observables. -/
def LowerConforms (prog : Program) (params : CallParams) … : Prop :=
  ∀ log, runWithLog params fuel = some log →
    ∃ O, (∃ last halt, Runs (codeFrame params (lower prog)) last ∧ …
            ∧ (observe self …).world = O.world)
        ∧ RunFrom prog (realisedOracle log) st₀ T prog.entry O
```

and in `Realise/…` / `Drive/Headline.lean`: `theorem lower_conforms : LowerConforms prog params … := …`. The proof file imports the spec file — the import direction is right, and Lean's defeq check means the theorem *cannot* drift from the def silently. Everything here is `Prop`/`Type 0`; no universe issues. The only cost: the def must make binders explicit `∀`s, which is fine (and more readable).

**Pattern B — obligation structures (for StmtTies/TermTies and the seams).** In `Spec/Conformance.lean`:

```lean
structure RealisabilityObligations (prog …) : Prop where
  stmtties  : ∀ L b, blockAt prog L = some b → StmtTies prog … L b
  termties  : ∀ L b, blockAt prog L = some b → TermTies prog … L b
  callSelf  : CallPreservesSelf
```

The conditional headline takes one `(h : RealisabilityObligations …)`; Phase 3's deliverable is literally `theorem obligations_of_runWithLog … : RealisabilityObligations …`. This turns the audit's "supplied-hypothesis = sorry-equivalent debt" into a single named, greppable, auditable term — and the headline's hypothesis list collapses from ~10 to ~4 (the true seams + statics).

**Pattern C — re-export surface (transitional only).** An exp003-style `Spec.lean` that restates and `:=`-forwards. Use it *now*, before Phase 3, for the obligation list; it is downstream of proofs build-wise, so it is an audit surface, not an import layer.

### What breaks / the one hard extraction

- **`Spec/Correspondence.lean` is the only genuinely fiddly move.** `StmtTies` mentions `Corr`, `MemRealises`, `StepScoped`, `MatRuns`, `chargeOf`, `slotOf`, `NonRecomputable` — today these live deep in the proof spine (`SimStmt.lean`, `MaterialiseRuns.lean`, `Match.lean`), whose import chains drag in everything (`SimStmt ← MaterialiseRuns ← Match ← Call ← SmallStep`, per the measured import graph). To state obligations in `Spec/` without importing the spine, the *definitions* (not their lemmas) must be hoisted into `Spec/Correspondence.lean`. They are all structures/defs over `Frame` + Spec types, so this is legal — but it is a multi-file surgical move, not a file split. Do it once, after Phase 3 settles the `StmtTies` shape (remediation plan open question 3 reshapes the gas/sload value conjuncts — hoisting before that means doing the surgery twice).
- **Attributes and docstrings travel with the decl** — moving defs is safe; only imports change. Keep every declaration name and namespace identical during moves so zero proof text changes.
- **`#print axioms` lines must not move into `Spec/`** — they all go to `Audit.lean` (§3).
- **No universe or mutual-block hazards** were found: no `universe` declarations in LirLean, no mutual inductives across the proposed cut lines.

### Pre- vs post-Phase-3 spec core

Before Phase 3, `Spec/Conformance.lean` honestly states the **conditional**: `theorem`-shape with `RealisabilityObligations` as an explicit hypothesis, and a docstring saying "obligations currently SUPPLIED; discharge tracked as Phase 3" (the audit §10 discipline). After Phase 3 it states the unconditional `LowerConforms` def with hypotheses only `runWithLog … = some log` + `hprec` + `CallsCode` + entry facts — and `Spec/Seams.lean` shrinks to the two precompile seams.

---

## 3. Audit consolidation — `LirLean/Audit.lean`

Replace the 252 scattered `#print axioms` (they run at elaboration on every build and prove nothing — nobody reads 252 info messages) with one file of **machine-checked, build-failing** guards. `#guard_msgs` is already in use in the codebase (MemAlgebra.lean:947), so the pattern is proven on this toolchain.

```lean
import LirLean   -- whole lib; Audit is the last module
/-!  # Audit — the single audit surface. Every check here FAILS THE BUILD if violated. -/

/- 1. AXIOM-CLEANLINESS of the flagship (+ each seam-discharge top). A `sorry`
   anywhere in the closure surfaces as `sorryAx` here; `native_decide` as
   `Lean.ofReduceBool`. Either changes the message and fails the guard. -/
/-- info: 'Lir.lower_conforms_cyclic_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Lir.lower_conforms_cyclic_assembled

/- 2. SIGNATURE FREEZE for the flagship only: pins the exact hypothesis surface,
   so a new supplied hypothesis cannot sneak in unreviewed. -/
/-- info: Lir.lower_conforms_cyclic_assembled : ∀ {prog : Program} … -/
#guard_msgs in #check @Lir.lower_conforms_cyclic_assembled

/- 3. NAMED SEAMS: one guard per irreducible oracle (SelfPresent, hprec/CallPreservesSelf,
   CallsCode, CleanHaltsNonException), pinning both existence and axiom set. -/

/- 4. NON-VACUITY WITNESSES: the Examples/EndToEnd.lean concrete run, re-asserted.
   `example : RealisabilityObligations exProg … := obligations_of_exProg`
   plus executable checks: `#guard (runWithLog exParams exFuel).isSome` -/
```

Mechanics of "fails loudly in CI":
- **Make `Audit.lean` the last import of the `LirLean` root** so plain `lake build` fails if any guard breaks. The `#print axioms`/`#check` guards cost milliseconds; there is no reason to hide them in a nightly. This *replaces* the elaboration cost of 252 scattered commands — net cheaper.
- Put only the **expensive executable witnesses** (a `#guard` that actually runs `runWithLog` on a nontrivial program, or `decide`-heavy checks) into a second module `LirLean/AuditSlow.lean` under a separate non-default `lean_lib Nightly where roots := #[`LirLean.AuditSlow]`; CI/nightly runs `lake build Nightly`.
- Deletion of the 252 scattered lines is purely mechanical (`grep -rn "#print axioms" LirLean` is the worklist) and is protected by the new guards themselves: land `Audit.lean` first, then delete.
- One caveat: `#print axioms` output for non-headline decls churns when decls are renamed/moved — guard only the ~10 decls that matter (flagship variants, seam chain tops, `materialise_runs_of_cleanHalt`, `cleanHalts_of_runWithLog`, the Phase-3 `obligations_of_runWithLog`, the end-to-end example), not all 252 historical ones.

---

## 4. Unused-hypothesis linting — verified setup

**What exists on this toolchain (verified in the vendored packages):**
- Both packages are on `lean4:v4.30.0`; `batteries` is in exp005's manifest (transitively via mathlib) at `.lake/packages/batteries`.
- Batteries ships `@[env_linter] def unusedArguments` (`Batteries/Tactic/Lint/Misc.lean:42`) — it flags declaration arguments used in neither the type nor the body, skipping `sorry`-containing decls. This is exactly the class that caught `sim_call_stmt`'s dead `_hself/_hcallee/_hgasfwd` binders (audit §4 #1, deleted in Phase 1).
- Batteries ships the driver: `lean_exe runLinter` with `lintDriver = "runLinter"` (`batteries/lakefile.toml:3,17`), and `scripts/runLinter.lean` resolves the workspace's default-target root modules when called bare and supports a `nolints.json` (`--update` writes it).

**Concrete setup (no custom code needed):**
```bash
cd experiments/005_ir_lowering && lake exe runLinter LirLean        # exp005
cd experiments/003_bytecode_layer && lake exe runLinter BytecodeLayer  # exp003
```
`lake exe` resolves executables from dependency packages, so this works today with zero lakefile changes. First run: triage output, `--update` to freeze a `nolints.json` baseline, then the CI step is "runLinter exits 0". It also runs the other default env-linters (`dupNamespace`, `docBlame`, `defLemma`, `synTaut`, `unusedHavesSuffices` — the last catches dead `have`s inside proofs, a bonus for this codebase). Disable unwanted ones via nolints rather than forking the driver. Cost note: it loads the full environment incl. Mathlib — minutes, so nightly/CI, not per-edit.

**Honest limitation (important for Eduardo's expectation):** `unusedArguments` catches only *syntactically dead* binders. It can **not** catch the audit's real disease — supplied hypotheses that are *used* by the proof but *dischargeable* (StmtTies, the un-wired `hcall`). Those are semantic debt; no generic linter can see them. The tool for that class is §2's `RealisabilityObligations` + §3's signature-freeze guard: any hypothesis on the flagship is by construction either (a) a member of the named-seam list in `Spec/Seams.lean` or (b) a build-visible diff to the frozen signature that has to be justified in review.

**Optional 50-line custom linter** (only if wanted after the above): an `@[headline]` attribute + a meta check that every `Prop`-typed binder of an `@[headline]`-tagged theorem's type is one of the whitelisted seam constants from `Spec/Seams.lean`. Mechanically simple (walk `forallTelescope` over the type, match head constants), and it turns the seam policy into an enforced invariant instead of a convention. I'd defer it; the signature-freeze guard gives 90% of the value for 5% of the work.

---

## 5. Migration order (checklist, gated against remediation Phases 2–4)

Legend: **[pure]** = file split/move, no statement or proof changes, safe anytime, verify with `lake build`; **[semantic]** = changes statements/proofs, gated.

**Step 0 — protect the invariant first.**
- [ ] **[pure]** Land `Audit.lean` (flagship + seam guards only, from the current decl set) and wire it into the `LirLean` root. Do this *before* any further deletion/move — it is the regression net for everything below.
- [ ] **[pure]** Delete the 252 scattered `#print axioms` lines (grep worklist; no decl changes).
- [ ] **[pure]** Baseline the linter: `lake exe runLinter LirLean` + `runLinter BytecodeLayer`, commit `nolints.json`.

**Step 1 — Phase 2 (semantic, gated on the lead's HonestGasTie decision; plan recommends (b) delete).**
- [ ] **[semantic]** Delete `Mono.lean`, `Oracle.lean`, `HonestGasTie.lean`; narrow `Law.lean` to determinism; delete RunLog's monotonicity section (:580+); remove `DriveCorrPlus`'s vacuous alignment fields; add the `hprec` headline variant. (All per remediation Phase 2 — do **not** split `RunLog.lean` or `TieDischarge.lean` before this; you'd be splitting code scheduled for deletion.)
- [ ] Update `Audit.lean`'s frozen signature in the same commit (the freeze guard *forces* this — working as intended).

**Step 2 — Phase 4 first half: unify + relocate (semantic then mostly-pure). I recommend running this BEFORE Phase 3**, contra the plan's numbering (the plan gates 4 only on 1+2): it shrinks `TieDischarge.lean` from 4.5k to ~2k lines, which halves the context any Phase-3 agent must hold, and it moves the stable engine layer out of the churn zone. Rebuild cost is contained: `TieDischarge` is a near-leaf (only `HonestGasTie` imports it, and that dies in Step 1).
- [ ] **[semantic]** Prove `stepFrame_next_execEnvAddr`; derive the SelfAt walk as the `a := self` corollary of `_next_accMono` (~1,000 ln saved).
- [ ] **[pure-ish]** Move the `namespace Evm` spans (:543-587, :604-1486 remnant, :1653-2914) + RBMap primitives to `BytecodeLayer/Hoare/AccountsMonotone.lean` / `AccountMap.lean`, decl-by-decl, names unchanged; update exp005 imports; build both packages.
- [ ] **[pure]** Split the TieDischarge remnant at its existing `namespace` boundaries → `Drive/SelfPresent.lean`, `Drive/CallPreservesSelf.lean`, `Drive/Headline.lean`.

**Step 3 — stable Spec extraction (pure, safe now; untouched by Phase 3).**
- [ ] **[pure]** Create `Spec/`: move `IR.lean`, `Machine.lean`→`Spec/Semantics.lean`, `Lowering.lean` (theorems out to a proof file), `Layout.lean`, post-Phase-2 `RunLog.lean`→`Spec/Recorder.lean`. Imports-only churn; full exp005 rebuild (~1.1k jobs) once.
- [ ] **[pure]** Write `Spec/Seams.lean` (defs/re-exports + docstrings) and the *transitional* `Spec/Conformance.lean` (Pattern C re-export of the conditional headline + `RealisabilityObligations` structure, docstring flagging supplied-vs-discharged).
- [ ] **[pure]** Rewrite the `LirLean.lean` root as a clean import list (drop the 90 lines of NOTE-archaeology; the notes' content lives in docs).

**Step 4 — Phase 3 realisability closure (the milestone; semantic, multi-session; per remediation plan).** New files under `Realise/` + `Examples/EndToEnd.lean`. **Do not pre-split `LowerConforms.lean`/`SimStmt.lean` before this** — Phase 3 item 1 reshapes the `StmtTies` value conjuncts, and those two files are its blast radius.

**Step 5 — post-closure consolidation (pure).**
- [ ] **[pure]** Hoist `Corr`/`MemRealises`/`StepScoped` to `Spec/Correspondence.lean`; move `StmtTies`/`TermTies` to `Sim/Ties.lean`; split `LowerConforms.lean` → `Ties.lean` + `BlockAssembly.lean`; split `MaterialiseRuns.lean` and `CleanHaltExtract.lean` at section boundaries.
- [ ] **[semantic, small]** Factor `landing_at_block_offset` out of the jump/branch landing twins (LowerDecode.lean:755; ~400 ln saved) → `Decode/Landing.lean`.
- [ ] **[pure]** Rewrite `Spec/Conformance.lean` to Pattern A (unconditional statement-as-def), shrink `Spec/Seams.lean` to the two precompile seams, extend `Audit.lean` with the end-to-end witness guards, re-freeze signatures.

Every step ends with `lake build` in both experiments; Steps 1, 2, 4 additionally re-run the linter and re-pin `Audit.lean`.

---

### Key file:line evidence index
- Headline: `LirLean/TieDischarge.lean:4292` (conclusion :4330-4335); `DriveCorrPlus` :3589; namespace interleavings :543/:589/:604/:1488/:1653/:2916.
- Obligation defs: `StmtTies` `LirLean/LowerConforms.lean:1273`, `TermTies` :1342, `WellFormedLowered` :143; `Corr` `LirLean/SimStmt.lean:103`; `DriveCorr` `LirLean/DriveSim.lean:87`.
- Recorder: `runWithLog` `LirLean/RunLog.lean:219`; monotonicity section (Phase-2 delete) :580+.
- House spec-surface pattern: `experiments/003_bytecode_layer/BytecodeLayer/Spec.lean:14`.
- Linter: `unusedArguments` `.lake/packages/batteries/Batteries/Tactic/Lint/Misc.lean:42`; driver `.lake/packages/batteries/lakefile.toml:3,17-20`.
- `#guard_msgs` precedent in-repo: `LirLean/MemAlgebra.lean:947`.
- Measured: 24,670 ln / 43 files; 252 `#print axioms` across 29 files (73 TieDischarge, 53 CleanHaltExtract); toolchains both `lean4:v4.30.0`.
