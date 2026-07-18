# Bytecode-layer audit — 2026-07-18

**Scope.** `EVM/BytecodeLayer/` (22,197 lines, the folded exp003+exp005 engine, on main since
2026-07-15) plus the `experiments/005_ir_lowering/LirLean` seam mass it feeds. Verified at HEAD
`dde891e9` on `codex/sir-internal-functions`; `EVM/BytecodeLayer` has zero diff vs `main`.

**Method.** Every finding below was adversarially re-verified against the working tree (line-exact
citations re-checked, callers traced repo-wide excluding stale `.worktrees/` snapshots, house rules
applied: *unimported ≠ dead*, *live proof path kills a vestigial claim*, *CREATE is wanted*).
Claims are stated post-correction; where the original finding was wrong in a detail, the corrected
version is what appears here. One candidate finding was refuted outright — see Appendix A.

**Memory cross-checks.** No finding contradicts the standing directives: nothing proposes deleting
CREATE machinery (S6 explicitly plans *adding* a CREATE soft-fail arm when SIR lowering emits
CREATE); the sload-warmth-stream item (V6) is confirmed **landed on main** at `33e572b2` — the
`sload-stream-vestigial` memory note and MEMORY.md index line are what is stale, not the code.

---

## Executive summary — the five biggest wins

| # | Win | Effort | Payoff |
|---|-----|--------|--------|
| 1 | **One documentation truth-sweep** across the folded layer: root header + Spec.lean audit-surface claims + 10 SPIKE markers + phantom theorem name + dangling doc pointers + exp003/exp005 naming (V1–V5, V9, V10, S1–S6). | trivial–small, comment-only, ~20 files | The layer's self-description currently misleads any auditor: "Experiment 003", "every exported theorem", "SPIKE", a bridge theorem that doesn't exist. Zero build risk. |
| 2 | **`drive_ok_agree` corollary + kill the max-lift ritual + derive unbounded framing from `_lt`** (E1, E2/D2). One 2–3-line corollary of the existing `drive_eq_of_both_ne_oof`, then 6 mechanical site rewrites and 3 weakening derivations. | small | Deletes one full ~66-line duplicate of the 8-arm drive induction plus ~30–40 lines of inlined fuel-reconcile ritual across 6 theorems; no statement changes. |
| 3 | **CyclicSim peel consolidation** (D1, D3, D4, D5): per-channel `recorderCoupled_{call,create}_peel`, halted-twin one-liners, `child_ne_oof_of_framed` merge, suffix-peel channel factor. | small→medium | ~300 lines of near-identical peel bodies collapse; public names survive as projections (exp005 flagship call sites keep compiling). **Discount:** this file's coupling family dissolves under the SIR retarget (see Do-NOT-touch) — do the trivial/small pieces, defer the medium one unless the retarget stays parked. |
| 4 | **CREATE soft-fail record naming + one inversion** (D8): name `createSoftFailResult`/`createPendingOf` in `EVM/Evm/Semantics/System.lean`, prove `createArm_next_inv` once, strengthen the existing `systemOp_createArm_reduce`. | medium | Removes 7 copies of a ~55-line key-block + dispatch spine and 9 copies of the 17-line record literal across StepWalk/System/Recorder (~400 lines), and gives future CREATE work (which is wanted) a single inversion to extend. |
| 5 | **Parametric dispatch-inversion lemmas** (D7, E7): one `stepFrame_next_smsf_pc` over the `.Smsf` dispatch arm (8 per-opcode proofs → 1 + thin instances), and full-payload `callArm`/`createArm` characterizations to retire ~17 redundant do-block inversions in Descent.lean. | medium | ~220 lines → ~60 in StepWalk; Descent's per-fact three-lemma towers become projections. Public names kept (exp005 BoundaryReach consumes them by name). |

The **large** structural items (E3/D9 drive-induction principle, E5 driveLog suffix refactor, D6
generic iterate machine, E4 RecorderCoupled fuel-existential) are real but are either half-superseded
by existing infrastructure, have their payoff halved by surviving constraints, or dissolve under the
SIR retarget — see the backlog and Do-NOT-touch sections before scheduling any of them.

---

## 1. Vestigial / stale (V)

### V1. SPIKE markers on the closed, load-bearing CREATE machinery
- **Where:** `EVM/BytecodeLayer/Hoare.lean:98,152,212,297`; `Hoare/CallSequence.lean:37,46,57,160`; `Hoare/GasMonotone.lean:237,245` (10 literal `SPIKE` tags); plus `Hoare.lean:110` ("This is R4 in the plan").
- **Claim (verified):** Ten `(SPIKE)` tags still label `CreateReturns`, `Runs.create`, `CreateReturns.det`, `Runs.create_to_halt`, the CREATE descent bricks, and the CREATE gas-debit lemma. The CREATE channel closed axiom-clean 2026-07-11 and folded to main 2026-07-15; all tagged machinery is permanent core, fully consumed (Exec/Frame.lean:357-359, Exec/WitnessChecks.lean:308, Exec/CallRealises.lean:40,100, Exec/CyclicSim.lean:20,580,650-656, Exec/CallPreservesSelf.lean:135-138, Hoare/DriveRuns.lean:472-477, GasMonotone.lean:287).
- **Action:** Delete the `(SPIKE)` qualifiers and the "R4 in the plan" sentence; keep the substantive entry-total/resume-Except notes. Same sweep must fix: (a) the stale "exp003 `Create.lean:200`" pointer at Hoare.lean:107 — the pointer's *line* is actually still correct in `EVM/Evm/Semantics/Create.lean:200` (63/64 guard, `throw .OutOfGas` at :201), but the "exp003" label is retired and the bare filename is ambiguous vs `BytecodeLayer/Exec/Create.lean`; qualify it. (b) Reword — do **not** delete — DriveRuns.lean:166,171,440's "R4 residual" self-containedly (e.g. "the create-resolves residual"): it is a live semantic label for the still-open `createResolves` non-vacuity seam (keccak wall) and must survive the sweep. Present CREATE as a first-class proven twin *while preserving* the disclosed createResolves caveat.
- **Effort:** trivial.

### V2. Root `BytecodeLayer.lean` header still says "Experiment 003" and omits the folded engine
- **Where:** `EVM/BytecodeLayer.lean:1-23` (23-line file).
- **Claim (verified):** Line 1: `-- Experiment 003 — bytecode layer over leanevm.` Layout comment (5-13) lists only 7 entries, omitting `Exec/` (21 modules incl. Recorder/CyclicSim/WitnessChecks), `Asm/` + `Asm/Geometry`, and `EVMSpec.lean` — all built via `EVM/lakefile.lean:80-81` (`.andSubmodules BytecodeLayer`, 63 modules vs 4 root imports). `experiments/003_bytecode_layer` has zero `.lean` sources; this is the package's sole proof layer, not an experiment.
- **Action:** Rewrite the header per S1 below (they are the same fix): drop the experiment framing, describe the post-fold layout, state that the lakefile globs all submodules so the root import list is a curated surface. Document `Exec/` (+`Asm/`) as a second export surface consumed by LirLean; document `EVMSpec.lean` as a deliberately de-aggregated draft (see V7) — do **not** re-import it.
- **Effort:** small.

### V3. Spec.lean "audit surface" claim stale; resolved altitude caveat still says "To reconcile"
- **Where:** `EVM/BytecodeLayer/Spec.lean:12-29`.
- **Claim (verified):** `# Spec — the audit surface of experiment 003` / `**This is the file to read**` — but post-fold the library exports many theorems (the whole Exec/ engine, consumed by exp005's flagship) that are not on this surface. The "Altitude caveat … To reconcile" paragraph (23-29) was settled by Eduardo's ruling (frame-level program-logic rules are the intended surface at this low-level layer) but the open-question framing was never removed. Precision: the *conformance flagship* surface (`lower_conforms*` and its seams) lives in exp005's `LirLean/Realisability/RealisabilitySpec.lean`, not in Exec/ — Exec/ holds the supporting engine machinery.
- **Action:** Retitle as the audit surface of the Hoare program-logic layer; point readers two ways (Exec/ = folded engine layer; LirLean/Realisability = conformance flagship). Replace "To reconcile" with the settled ruling, and record that ruling **in-repo** (it exists only in assistant memory today; AGENTS.md:109-111 still states the observables-only standard with no low-level carve-out).
- **Effort:** small.

### V4. Dangling doc reference: `docs/generalization-plan.md` never existed
- **Where:** `EVM/BytecodeLayer/Hoare/Behaves.lean:8`.
- **Claim (verified, understated in the original):** The cited plan file is absent from the *entire git history* of the repo (no add/delete of any `generalization*` file across all refs) — the citation was dangling at creation (`0a3370a4`, 2026-06-16); the plan was an out-of-repo orchestration artifact. There is no surviving document to repoint at.
- **Action:** Drop the parenthetical citation; the docstring is otherwise self-contained and accurate. (See S8 for the Behaves surfacing question — the predicate itself is a keep.)
- **Effort:** trivial.

### V5. StackUnderflow tag misnomer: generic none-lift tag, undocumented in code
- **Where:** `EVM/Evm/Semantics/PrimOps.lean:25-26`; `EVM/Evm/Semantics/Dispatch.lean:125`.
- **Claim (corrected):** The `MonadLift Option (Except ExecutionException)` instance stamps every lifted `none` as `.error .StackUnderflow`. **Corrections:** (1) the Dispatch.lean:125 PUSH-missing-immediate branch is *unreachable* from the live engine — `decode` (Decode.lean:52-63) always attaches `some` immediates (zero-padded; `ByteArray.extract` total) and `stepFrame` defaults decode failure to `(.STOP, .none)`; it's a defensive arm, not a live mislabeled decode error. (2) The misnomer is already recorded in `docs/backlog.md:24-37` and parked as roadmap item A2; the only missing piece is the in-code docstring on the instance. (3) Kind is naming/doc-hygiene, not vestigial — the tag is live and load-bearing (Semantics/Gas.lean:110-111 `lift_none_bind`, Exec/CheckedStep.lean:235,257-258,444, and `SharedObservable.lean:52` renders it across the exp004 toolchain seam — a rename would ripple across the toolchain boundary; conformance runner does *not* compare these tags).
- **Action:** Record-only per the standing decision: add a docstring on the instance stating StackUnderflow is the generic none-lift tag, noting the Dispatch branch's unreachability. Do not rename.
- **Effort:** trivial.

### V6. Seed RESOLVED: sload warmth stream already dropped — the *memory note* is the stale artifact
- **Where:** `EVM/BytecodeLayer/Exec/Recorder.lean:34-38,157-160` (now the 4-stream RunLog).
- **Claim (verified):** `RunLog = {observable, gas, calls, creates}`; `driveLog` returns the 4-tuple; commit `33e572b2` ("polish: drop vestigial sload warmth stream") is an ancestor of both main and HEAD, and swept exp005 too. Zero `sloads`/`sloadAcc` residue in the main tree (only stale `.worktrees/` branch snapshots retain the 5-tuple). The surviving `sloadChg`/`chargeCache`/`decode_sloadstash` in `LirLean/Spec/WellFormed.lean:485-491` are the free spill-cost parameter with its load-bearing ≤1024 stack bound — *not* residue.
- **Action:** No code change. Update the `sload-stream-vestigial` memory note's closing line ("Branch awaits merge to main" → "landed on main at 33e572b2") and the MEMORY.md index one-liner (still reads as open backlog). Close any backlog entry.
- **Effort:** trivial (bookkeeping only).

### V7. EVMSpec.lean is a parked DRAFT; the parked decision is real, the drift narrative was overstated
- **Where:** `EVM/BytecodeLayer/EVMSpec.lean:4-11,100-139`.
- **Claim (corrected):** Zero importers of `BytecodeLayer.EVMSpec`; zero references to `flatSpec`/`Refines` anywhere in EVM/, experiments/ (004+005), or sir/; the nested mirror was never built; `flatSem` (SharedObservable.lean:156) is the live interface (Refinement.lean:78-100, Equivalence.lean:46,74,76). **But** the zero-import state is a *documented decision*, not drift: commit `28e01243` ("hygiene: de-aggregate draft EVMSpec", 2026-07-15, Phase-D D3 per `docs/review/phase-d-outcome-2026-07-14.md:52-56`) deliberately removed it from the aggregator, executing the interim arm of `port-cleanliness-review-2026-07-14.md` #6. The banner's real staleness: "the open question at the bottom" points at a section that doesn't exist in the file, and the draft author's Option-B pick (line 52) is not the ratification the banner awaits from Eduardo (genuinely unrecorded).
- **Action:** Two remaining items only: (a) decide adopt-vs-archive (the endgame; conformance track dormant-active per `docs/handoff-2026-06-25.md`); (b) rewrite the banner — fix the dangling pointer, note the de-aggregation, and add a root-map breadcrumb naming `EVMSemantics/flatSem` canonical (see S9).
- **Effort:** small (banner) + one decision.

### V8. HoareDemo.lean is an orphan demo; deletion loses the repo's only concrete-program framing theorem
- **Where:** `EVM/BytecodeLayer/Examples/HoareDemo.lean:154-161`.
- **Claim (corrected):** Imported by nothing (ConcreteSpecs.lean:4-8 aggregates the other five example modules); `hoare_demo` has zero consumers; builds only via the lakefile glob. **Corrections:** (1) "zero .md references" was false — six docs under `experiments/003_bytecode_layer/` reference it, incl. `review-report.md:95,405,424` with live links; the prerebuild review already made this exact finding ("either delete HoareDemo or mark it the canonical demo") — this is a re-discovery of a documented parked decision. (2) "content subsumed" is overstated: only the effect half overlaps `messageCall_sstore_storageAt` (ConcreteSpecs.lean:65-69); the framing conclusion (cell (addrA,8) untouched, quantified over the completed outcome, :156) and the Outcome-lens concrete-program statement exist nowhere else.
- **Action:** Decide keep-or-retire. If kept (recommended, given the unique framing theorem): import from ConcreteSpecs and cross-link. If deleted: sweep the six exp003 doc references too.
- **Effort:** trivial (keep) / small (delete + doc sweep).

### V9. Broken `docs/ir-design-v2.md` citations — path-broken, content-correct
- **Where:** `EVM/BytecodeLayer/Spec.lean:55`; `Hoare/GasMonotone.lean:7,269` (GasMonotone.lean:9 already has the full path).
- **Claim (corrected):** Three docstrings cite `docs/ir-design-v2.md §3.4` as repo-relative; the file lives only at `experiments/005_ir_lowering/docs/ir-design-v2.md`. **Do NOT repoint at v3:** v3's own gas one-law apparatus was dropped 2026-07-03 (UPDATE banner; gas is now a log-fed exact-equality oracle) and v3 back-references v2's §3.4 as the settled 2026-06-23 provenance it inherits. §3.4 ("the ONE law on the gas oracle: monotonicity") is exactly what `Runs.gasAvailable_le` discharges — the citation is content-accurate, only path-broken.
- **Action:** Normalize the three paths to the full `experiments/005_ir_lowering/docs/ir-design-v2.md`, optionally noting v3 supersedes v2 *as a plan* while the monotone-gas-read law's provenance is unchanged. Bonus in the same pass: GasMonotone.lean:11 self-referentially claims this file "discharged that law for a concrete two-read program" — a fold relic; repoint at the experiment-side file that held that discharge.
- **Effort:** trivial.

### V10. Experiment-era naming ripple: 19 exp003/exp004/exp005/leanevm hits in 14 BytecodeLayer files
- **Where:** e.g. `Hoare.lean:107`, `Semantics/Maps.lean:9`, `Hoare/DriveRuns.lean:34`; 17 hits/12 files case-sensitive, 19/14 case-insensitive (adds `Programs.lean:6`, `Spec.lean:12`).
- **Claim (corrected):** Doc-comments only, nothing consumed by proofs. Two sub-claims of the original were wrong: (1) `Hoare.lean:107`'s "Create.lean:200" pointer is line-accurate (see V1) — only the "exp003" label and bare filename mislead. (2) `Maps.lean:9`'s "a comparator leanevm does not yet provide" describes a gap that **still exists** — `grep TransCmp EVM/Evm` is empty; the module is live gap-filling code. The rewrite must only rename "leanevm" → "the vendored Evm/ tree", keeping the gap claim.
- **Action:** One mechanical sweep replacing retired experiment names with post-fold layer names and qualifying bare file citations. **Preserve:** the still-true TransCmp-gap statement, and the exp004 cross-references in SharedObservable/Equivalence (experiments/004_nested_evmyul still exists at v4.22.0 vs EVM's v4.30.0 — a live engine-identifier convention, not cruft).
- **Effort:** small.

---

## 2. Encodings (E)

### E1. Unbounded + bounded stack-append framing = two full drive-skeleton inductions for one theorem
- **Where:** `Semantics/Interpreter/DescentEq.lean:58-128` (`drive_append_framing`) vs `Hoare/DriveRuns.lean:50-108` (`drive_append_framing_lt`); descend pairs at DescentEq.lean:143-155 / DriveRuns.lean:114-125 and Hoare/CallSequence.lean:63-76 / DriveRuns.lean:134-147.
- **Claim (corrected, scope halved):** Exactly **one** duplicated 8-arm case-tree induction exists: `drive_append_framing` and `_lt` are independently-proved copies of the identical skeleton, differing only in threading `j+1 ≤ f` (DriveRuns.lean:45-49 admits the shadowing verbatim). The descend `_eq`/`_lt` pairs are *not* duplicate inductions — the `_eq` versions are already ~10-line non-inductive corollaries; their `_lt` twins duplicate the ~10-line peel, not an induction. Real savings ≈ 80-85 lines (one ~66-line case-tree + ~20 lines of peel), not ~140. All six lemmas are live (forward path → `Runs.drive_reconcile` → `messageCall_runs`; reverse path → `runs_of_drive_ok`, where `j < f` is load-bearing for well-foundedness).
- **Action:** Move the `_lt` inductions upstream into DescentEq.lean (import-feasible, no cycle), derive the three unbounded lemmas as one-line weakening corollaries (`.ok res` kills `f=0`; every consumer destructures `⟨j, hj⟩` and tolerates the extra conjunct).
- **Effort:** small.

### E2. The max-lift fuel-reconcile idiom is inlined 6 times despite `drive_eq_of_both_ne_oof` existing
*(Same fix as D2 — one corollary; stated here for the encoding angle, booked once in the backlog.)*
- **Where:** `Hoare/DriveRuns.lean:416-424, 455-463`; `Exec/CyclicSim.lean:534-538, 601-607, 677-683` (recorderCoupled_create_extract — missed by the original count), `921-926`. The two `Hoare/CallSequence.lean:143-157,168-180` sites are **not** instances (one-sided ne-OOF over a *framed* run; the max-free alternative needs `child_ne_oof_of_framed`, defined downstream — import inversion).
- **Claim (corrected):** `CallReturns`/`CreateReturns` pin the child at `seedFuel cp.gas` (Hoare.lean:95,121); 6 sites re-derive the two-`drive_fuel_mono`-through-`max` transport inline, though `drive_eq_of_both_ne_oof` (Hoare/CallSequence.lean:82-89) packages exactly this and is used at only one site (:123).
- **Action:** Add `drive_ok_agree : drive a s st ≠ .error .OutOfFuel → drive b s st = .ok r → drive a s st = .ok r` (2-3 lines from `drive_eq_of_both_ne_oof`); rewrite the 6 sites. In the DriveRuns pair this also collapses the enclosing `cases`/`drive_error_oof` scaffolding (~12 lines each). No statement changes. Not compiled during this audit — but structurally a discard-one-conjunct move.
- **Effort:** small.

### E3. Eleven fuel inductions replay drive's identical 8-arm case skeleton
*(Merged with D9 — same underlying issue, two vantage points.)*
- **Where:** `Semantics/Interpreter/Drive.lean:142-180` (drive_fuel_succ), `Semantics/Interpreter/DescentEq.lean:58-128`, `Semantics/Interpreter/Measure.lean:125-230` (mu_bound — uncited by both originals), `Hoare/DriveRuns.lean:50-108, 191-223, 269-310`, `Hoare/DriveMono.lean:157-287`, `Hoare/GasMonotone.lean:94-195`, `Exec/RecorderLemmas.lean:49-90`, `Exec/CyclicSim.lean:70-155, 272-345`.
- **Claim (corrected):** **11** whole-run invariants (not 10, not 6) each hand-transcribe the same scrutinee tree (`state inr/inl → stack nil/cons → pending.resume → stepFrame 4 arms → beginCall inl/inr`), 40-130 lines apiece. DriveMono.lean:28 and DescentEq.lean:23 self-document the template copying. Two corrections to the proposed fix: (a) a single per-arm `DriveInvariant` obligation record covers only the *forward-invariant* family (drive_error_oof, drive_accounts_find_mono, drive_gasRemaining_le_totalGas, mu_bound); the other seven are **relational/two-run** lemmas (two fuels / two stacks / drive-vs-driveLog) needing a factored one-layer transition function + per-arm unfold equations + a fuel-induction principle, and the driveLog trio needs a driveLog-side (or paired) principle covering the recording arms. (b) Savings are asymmetric: ~90% of the light lemmas is skeleton; only ~30-40% of drive_accounts_find_mono / gasRemaining (payload dominates). Note: SegmentedEval's `nextLog`+`driveLogC_succ_eq` reify *driveLog* only — **no reification of `drive` exists**; one would have to be built first (one more transcript, written once).
- **Action:** Pilot per family: `drive_error_oof` (forward-invariant) and `framed_oof_of_standalone_oof` (framing) as the two pilots. Also collapse the `drive_append_framing/_lt` pair (E1) as part of any such pass. **Minimum bar, effective immediately:** new drive/driveLog whole-run lemmas must go through the reified step rather than adding a twelfth transcript.
- **Effort:** large (pilot first).

### E4. `RecorderCoupled.restart`'s ∃-fuel forces a peel ritual per coupling lemma — but the keystone lemma already exists
- **Where:** `Exec/Recorder.lean:217` (the only `∃ fuel` in BytecodeLayer); ritual across `Exec/CyclicSim.lean` (19 `simp [driveLog]` zero-kills — 16 outer + 3 nested; 6 `cases fuel'` + 10 `cases f` splits; ~29 `unfold driveLog`).
- **Claim (corrected — keystone premise was FALSE):** The claimed-missing driveLog unfolding lemma **already exists**: `driveLogC_succ_eq` (`Exec/SegmentedEval.lean:91-126`) is the exact driveLog mirror of `callsCodeOk_succ_eq`, alongside `nextLog` (:44-89), `driveLogC_shift/final` and `nextLog_inl` (CheckedStep.lean:602). So option (a) of the original proposal is half-done on main; the outstanding work is re-phrasing CyclicSim's peel preludes over it (no import cycle). Scope corrections: 4 of ~21 RecorderCoupled-consuming lemmas are pure delegators; ~half the ritual sites are extract-only; the fuel-peel prelude is only ~5-7 lines/site — the bulk of the big lemmas is descent/framing machinery that option (a) does **not** remove. The tax is confined to this one 1020-line file: exp005 consumes RecorderCoupled ~90× purely through the per-edge API (only 3 ritual sites outside CyclicSim).
- **Action:** Treat option (a) as a modest boilerplate shave (mechanical re-phrasing over existing `driveLogC_succ_eq`/`nextLog_inl`, small-medium), **not** a collapse. Option (b) (RTC restatement of `restart`) is the only route that kills the heavy part — and it is exactly what the SIR retarget's traceRealises reshape delivers for free. **Defer (b) to the retarget** (see Do-NOT-touch).
- **Effort:** small-medium for (a); (b) deferred.

### E5. driveLog's accumulator-passing style forces `acc_hom` + append-noise in consumers — payoff of the fix is half the original claim
- **Where:** `Exec/Recorder.lean:157-199` (gasAcc/callAcc/createAcc params); `Exec/CyclicSim.lean:56-68` (append helpers), `70-155` (driveLog_acc_hom, rewritten at **14** CyclicSim sites: 207, 239, 385, 424, 476, 494, 553, 619, 695, 729, 756, 785, 822, 938).
- **Claim (corrected):** The consumer noise is real and understated (14 sites, not ≥4), and RecorderCoupled's fields already want suffix semantics (restart from empty accumulators + prefix witnesses). **But** the accumulator encoding has one genuine consumer the original missed: the segmented kernel-evaluation machine (SegmentedEval `LogConfig/nextLog/stepsLog`, CheckedStep `stepsLogChk`, exp005 `WitnessCheckRun.lean:29-47` kernel-computing `stepsLogChk 39 ⟨[],.inl fr₀,[],[],[]⟩`). A suffix-returning driveLog either keeps that machine and *relocates* the hom induction as the bridge, or moves the append-noise into segment gluing. Encoding-independent hard parts (driveLog_frame_nonempty, framed-oof fuel plumbing) survive either way. Performance is not a counterargument (driveLog is never bulk-executed; witnesses go through stepsLogChk).
- **Action:** If attempted: keep LogConfig's accumulator fields (decide explicitly up front), refactor driveLog to return suffixes, derive the accumulator form once. Effort is medium-to-large (touches SegmentedEval, CheckedStep, exp005 witness computations with hard-coded 5-field literals), for roughly half the promised simplification. Low priority; also interacts with the retarget (see Do-NOT-touch).
- **Effort:** medium-large.

### E6. Stash-tail gas/expansion side-conditions phrased at nested transformer post-frames
- **Where:** `Exec/Stash.lean:117-125` (stash_tail_runs over `pushFrameW fr …`), `:256-266` (stash_tail_gas over two-deep `pushFrameW (gasFrame fr) …`); `Exec/CleanHaltExtract.lean:667-687` (gas_envelope_of_cleanHalt: 7 nested-term occurrences).
- **Claim (corrected):** Real leak, wider than cited: the identical nested phrasing is replicated in three more live exp005 statements that a fr-level restatement must sweep — `stash_tail_sload` (`LirLean/Materialise/StashTail.lean:74-84`), `sload_envelope_of_cleanHalt` (`LirLean/Materialise/CleanHaltExtract.lean:36-65`), `sim_assign_gas_lowered` (`LirLean/CfgSim/LowerDecode.lean:728-739`). Nuance: at the two envelope-to-stash pipe sites the nested shape is a matched wire format (zero consumer computation); the compute-through burden is concretely realized at `Machinery.lean:2825/3650`. Transport: `hmem` is definitionally fr-level via `pushFrameW_activeWords'` (rfl); the two gas bounds additionally need `UInt64.toNat_sub_ofNat` transport under the no-wrap guards already carried — routine, not pure rfl. Live call sites: stash_tail_runs ×7, stash_tail_gas ×2, gas_envelope_of_cleanHalt ×2 (not "two").
- **Action:** Restate stash_tail_runs/stash_tail_gas (and covered/sload variants) with fr-level preconditions (`Gbase + Gverylow + memExpansionChargeOf … + Gverylow ≤ fr.gas.toNat`, expansion witness at `fr.exec.activeWords`), discharging the intermediate forms internally; then shrink both envelope conclusions. Both the default LirLean cone and the WIP cone must stay green.
- **Effort:** medium (upper end).

### E7. CALL/CREATE-site facts cost a callArm/systemOp/stepFrame lemma trio each — ~17 redundant do-block inversions in Descent.lean
- **Where:** `Hoare/Descent.lean` (1306 lines): trios at :71/:116/:140, :147/:186/:221, :264/:297/:377, :399/:436/:460, :470/:498/:517, :524/:688/:755, plus create2 singles :550-802.
- **Claim (corrected):** Not every layer re-inverts (systemOp_callArm_reduce / systemOp_createArm_reduce / stepFrame_needsCall_systemOp are shared; cross-trio reuse exists at :465). The genuine duplication: callArm do-block inverted 3× (:79/:155/:406), createArm 5× (:272/:477/:531/:556/:581), the systemOp CREATE/CREATE2 arm manually unfolded **7×** (:314/:343/:606/:634/:664/:703/:729 — because `systemOp_createArm_reduce`'s `∃ em` discards the charged-state↔exec relation), stepFrame 2× (:229/:761). "≥6 trios" undercounts (create2 singles form ~3 more partial towers). The originally proposed closed-form `stepFrame_needsCall_inv_full` is **infeasible at stepFrame level** (CALL pops 7 operands vs 6 for the other three call ops with different caller/apparentValue wiring; cp's gas fields depend on two charge successes) — the canonical form is existential with a per-op disjunction. The codebase already demonstrates the projection style works and is unused: `createArm_needsCreate_frame_exec_inv` (:575) is near-full-payload, yet :524/:550 re-invert instead of projecting.
- **Action:** Highest-leverage single fix: strengthen `systemOp_createArm_reduce` (Semantics/System.lean:1347) to carry the charged-state equalities and popped-stack residual — kills all 7 manual create-arm unfolds. Then closed-form full-payload characterizations at callArm/createArm level; re-derive existing lemmas as projections. Keep the 6 stepFrame-level statements verbatim (consumed positionally in EVM/Exec, DriveMono, CyclicSim, and exp005). Note the needsCreate depth trio (:470/:498/:517) has zero consumers today — keep as the symmetric CREATE-side guard (CREATE is wanted), but it is inventory.
- **Effort:** medium.

### E8. Fuel-recursive interpreters + opaque USize primitives ⇒ ~1050 lines of reified-evaluator scaffolding
- **Where:** `Exec/SegmentedEval.lean` (299 lines; file-wide `maxHeartbeats 1000000` at :12, redundant local at :214); `Exec/CheckedStep.lean` (747 lines).
- **Claim (corrected):** The lines exist solely so witnesses evaluate — but that witness is **R12a/R12b** (`exProg_satisfies_hypotheses`/`exProg_nonvacuity`, RealisabilitySpec.lean:722-783), the flagship's build-enforced non-vacuity guard with a `#guard_msgs`-checked axiom trio. Load-bearing, nothing deletable. Precision: the segmentation reason is the seed-fuel peel OOM (54096 seed vs 39/36 real transitions) plus the USize wall; the heavy cranks are three `decide +kernel` in exp005 (~13s/5.5GB), not the SegmentedEval heartbeat settings (those pay for elaborating the reification lemmas). `ffi.ByteArray.zeroes` is not opaque (extern with pure body); the opacity is `System.Platform.numBits`; `ffi.keccak256` is the genuinely opaque one (known keccak wall). `driveLogC_shift`/`callsCodeOk_shift` currently have zero consumers (live path uses only `_final`).
- **Action:** The two proposed moves — (a) define driveLog/callsCodeOk *as* iterate loops over nextLog/nextCC (deletes only the two succ_eq lemmas, ~66 lines, while churning ~35 unfold sites across 4 files incl. the default-cone CyclicSim headline); (b) confine USize to one sanitized primitive (ripples into the conformance hot path: `readWithPadding` in ~16 files, MemAlgebra's 800k-heartbeat proofs, the 22k-test conform runner) — are **not obviously net-positive** given the churn-to-deletion ratio. Park; revisit only if a new heavy witness family lands. See D6 for the cheap generic-machine dedup that *is* worth doing.
- **Effort:** large; parked.

---

## 3. Duplication (D)

### D1. `recorderCoupled_{call,create}_extract` re-run the entire restart-peel done by `recorderCoupled_{call,create}`
- **Where:** `Exec/CyclicSim.lean:505-574, 576-640, 642-713, 888-957`.
- **Claim (verified, near-identical not byte-identical):** Each `_extract` invokes the non-extract lemma (:902, :658) then re-runs the ~45-50-line restart-peel (hdescent/driveLog_drive/child_ne_oof/frame_nonempty/hdeliv/acc_hom/injection cascade) solely to extract the head-record identity the non-extract lemma discards. Usage direction confirms the fix: the non-extract pair has **zero consumers outside the `_extract` wrappers** (re-exported to Lir but never applied); the `_extract` variants are the live workhorses (Machinery.lean:866, 2649, 3959).
- **Action:** One per-channel `recorderCoupled_{call,create}_peel` returning record identity **and** tail coupling; make both existing lemmas projections. For CREATE, formulate over the destructured resume so both `recorderCoupled_create` and `_create_extract` project. Deletes ~110 lines; public names survive.
- **Effort:** medium. *(Dissolving-mass discount applies — see Do-NOT-touch.)*

### D2. Max-fuel reconcile recipe inlined 6× — same fix as E2
- **Where:** `Exec/CyclicSim.lean:533-538, 601-607, 677-683, 921-926`; `Hoare/DriveRuns.lean:417-424, 455-463`. General lemma at `Hoare/CallSequence.lean:82-89`.
- **Claim (verified):** The 4 CyclicSim sites are byte-identical modulo names; the 2 DriveRuns sites are a structurally different rendering of the same recipe (cases split + `drive_error_oof` branch + two `.trans` lifts) — replacing them with `drive_eq_of_both_ne_oof`/`drive_ok_agree` also deletes the enclosing case split (~12 lines each, better than originally claimed). Import chain CyclicSim → DriveRuns → CallSequence puts the lemma in scope everywhere. Not compiled during audit; mechanical by inspection.
- **Action & effort:** See E2 (booked once): small.

### D3. Six single-record suffix-peel lemmas share one skeleton parametrized by accumulator slot
- **Where:** `Exec/CyclicSim.lean:194-226, 228-253, 715-739, 741-766, 768-804, 806-841`.
- **Claim (corrected):** `recorderCoupled_step_gas` / `gasSuffix_nonempty` / `create2Suffix_nonempty_of_next` / `callSuffix_nonempty_of_next` / `recorderCoupled_call_softfail` / `recorderCoupled_create_softfail` differ only in flag hypotheses, acc_hom slot, projected injection, and rebuilt prefix field — rooted in driveLog's `.next` branch having exactly three flag-guarded singleton-append arms (Recorder.lean:157-197). Corrections: the projection evidence was inexact (congrArg only at :739/:766; the rest use manual `injection`); "three 3-line instances" is optimistic (each still needs its unfold+flag-simp preamble and the flag-exclusion lemmas, realistically ~8-12 lines); scope is understated — the same peel-tail motif recurs inside the heavier descent lemmas at 7 more acc_hom sites, so a factored core (natural shape: the converse-shift of `driveLog_acc_hom`) pays ~10×.
- **Constraint:** all six are live in exp005 (Machinery.lean:778,781,2555,2680,3170,3773,3908,3988; Producer.lean:508) — keep the six public statements as thin wrappers.
- **Effort:** medium. *(Dissolving-mass discount.)*

### D4. `calls_nil`/`creates_nil_of_stepFrame_halted` twins subsumed by `recorderCoupled_halted_inv` in the same file
- **Where:** `Exec/CyclicSim.lean:843-864, 866-886` (twins), `972-998` (_inv + suffixes_nil).
- **Claim (verified):** Twins identical except final projection (and one comment line at :860); both are strict consequences of `recorderCoupled_halted_suffixes_nil` (:992-998). Provenance: commit `653f394c` hoisted _inv/suffixes_nil from Machinery but never collapsed the pre-existing twins. External consumers: Machinery.lean:2558, :3780 (names must survive).
- **Action:** Hoist **both** `_inv` and `suffixes_nil` above the twins (dependency-safe) and redefine the twins as `(recorderCoupled_halted_suffixes_nil hcp hstep).2.1` / `.2.2`. ~40 lines deleted, zero API change.
- **Effort:** small.

### D5. `child_ne_oof_of_framed` is the `.call`-instance of `child_ne_oof_of_framed'` ten lines below it
- **Where:** `Hoare/DriveRuns.lean:315-331`.
- **Claim (verified):** Bodies character-identical modulo `.call pending` vs `p`; unprimed is a strict specialization. Complete consumer set: unprimed at CyclicSim.lean:531,920 + DriveRuns.lean:412 (all `.call`, ps=[]); primed at CyclicSim.lean:600,676 + DriveRuns.lean:451 (all `.create`). All fully-applied — instantiation type-checks by construction.
- **Action:** Delete unprimed, drop the prime, update 3+3 call sites, and reword the primed docstring (:322-325, currently defined by comparison to the deleted name). Do not touch `.worktrees/` copies.
- **Effort:** trivial.

### D6. Generic iterate/shift/final/checked-iterator theory instantiated twice by hand
- **Where:** `Exec/SegmentedEval.lean:129-184` vs `246-297`; `Exec/CheckedStep.lean:639-668` vs `716-745`.
- **Claim (corrected):** stepsLog≅stepsCC, driveLogC_shift≅callsCodeOk_shift, driveLogC_final≅callsCodeOk_final, stepsLogChk_sound≅stepsCCChk_sound — token-identical inductions modulo names and the terminal injection (`.ok` into Except vs identity into Bool — the generic law needs an explicit `inject : ρ → α`, glossed by the original). "Next evaluator free" is overstated: only steps/shift/final and stepsChk/_sound come free; per-instance `nextX` body + succ-eq lemma + `nextXChk` + soundness stay (the two succ_eq lemmas are NOT duplicates of each other). Net ~80-100 lines, not 120. **Kernel constraint:** exp005's `exCheckChk_true` closes by `decide +kernel` over `stepsLogChk 39` — the generic `stepsChk` must stay a plain function taking `nextChk` as a direct argument (no typeclass/opaque indirection); that theorem is the refactor's canary. Renames ripple into two exp005 re-export shims (trivial). Both `_shift` lemmas currently have zero consumers — envelope infrastructure, strengthening the case for one generic copy.
- **Action:** `Machine (σ ρ) := σ → σ ⊕ ρ` + steps/shift/final over any evaluator satisfying the succ-eq law (with `inject`), + generic `stepsChk`/`_sound`; instantiate twice. Validate the canary.
- **Effort:** medium.

### D7. `stepFrame_next_<op>_pc`: eight near-identical per-opcode proofs
- **Where:** `Hoare/StepWalk.lean:1969-2134` (pop/mload/mstore/sload/sstore/gas), `2218-2271` (add/lt).
- **Claim (corrected):** The six Smsf proofs are token-identical except opcode literal + helper name; add/lt differ only in `UInt256.add` vs `.lt`. Feasibility verified: dispatch has a single `.Smsf s` arm (Dispatch.lean:106) so a lemma parametric over `SmsfOp` reduces generically (in-repo precedent: `smsfOp_next_lt`, `smsfOp_onlyNext`, `smsfOp_neverHalts`); the **binOp half needs a shape tweak** — dispatch has per-op arithmetic arms, so take `dispatch opv arg fr fr.exec = binOp f fr.exec` as a hypothesis. The `smsf_<op>_next_pc` helper family (366-477) is *not* collapsible (structurally different per op) and correctly stays as per-op inputs. JUMP/JUMPI correctly excluded (different conclusions).
- **Constraint:** all eight names consumed by exp005 `Decode/BoundaryReach.lean:456-494` — keep as thin corollaries.
- **Action:** One `stepFrame_next_smsf_pc` (~30 lines) + eight ~4-line instantiations; binOp variant with the dispatch-equation hypothesis. ~220 → ~60 lines.
- **Effort:** medium.

### D8. CREATE soft-fail inversion chain re-inlines createArm's failed/pending record literals — 7 spine copies, 9 literal copies
- **Where:** `Hoare/StepWalk.lean:778-1140, 1249-1421`; `EVM/Evm/Semantics/System.lean:83-98`; `EVM/BytecodeLayer/Semantics/System.lean:1057-1129` (createArm_next_gas — a **7th** spine copy missed by the original); `Exec/Recorder.lean:108-129`; systemOp spine also at StepWalk.lean:1182-1209 (CREATE2 branch of systemOp_next_accMono, a 6th spine instance).
- **Claim (corrected):** (a) Seven copies of the ~55-line key-block + double resumeAfterCreate dispatch. (b) Six copies of the requireStateMod/pop4/static-split/charge spine. (c) The 17-line failed-record literal appears at System.lean:92-98, StepWalk.lean ×6 (788, 850, 908, 966, 1023, 1091), Semantics/System.lean:1072-1086, Recorder.lean:114-121. Framing fix: a spine lemma **already exists** — `systemOp_createArm_reduce` (Semantics/System.lean:1341-1408, mirror of the callArm one that StepWalk's CALL arms already use); the CREATE2 lemmas bypass it only because its existential hides the pop4/charge equations. Precision: `softFailCreateRecord`'s `result` is verbatim `failed`; its `pending` is a near-copy (`frame := current`, operands via total pop4-with-default) — the shared `createPendingOf` must be parameterized for both. All cited lemmas are live (Descent.lean:835-875 + StepWalk internal + Semantics/System.lean:1515).
- **Action:** (1) Name `createSoftFailResult`/`createPendingOf` in Evm/Semantics/System.lean (names unclaimed repo-wide); use in createArm, softFailCreateRecord, StepWalk. (2) One `createArm_next_inv`; fold all 7 dispatch copies (incl. createArm_next_gas) into corollaries. (3) Strengthen the existing `systemOp_createArm_reduce` to expose the equations (do not add a new pattern). ~400-line deletion, plausible-to-conservative. Directly serves future CREATE lowering work (CREATE is wanted).
- **Effort:** medium (needs a build cycle).

### D9. Branch-for-branch drive/driveLog inductions — merged into E3.

### D10. WitnessChecks checker-soundness twins repeat an identical Runs induction
- **Where:** `Exec/WitnessChecks.lean:322-340` vs `381-399`; wrappers `350-356` vs `403-409`.
- **Claim (verified):** Bodies identical except the refl-case head lemma (`callsCodeOk_head` vs `_head_create`); both consume the shared callsCodeOk_step/call/create edge lemmas. Correction: the `invariant_of_runs` route is oversold (relocates the fuel-match boilerplate into three shims and drags CyclicSim's import cone into WitnessChecks); the **local shared lemma** route is strictly better: `callsCodeOk_along_runs : Runs fr fr' → ∀ fuel, callsCodeOk fuel fr = true → ∃ fuel', callsCodeOk fuel' fr' = true` (provable as-is; `callsCodeOk 0 _ = false` definitionally, Recorder.lean:227). Wrapper-collapse is marginal (~6 lines).
- **Constraint:** all four theorems live — exported via `LirLean/Realisability/WitnessParams.lean:15-18`, consumed at :129-131 to discharge the R12a callsCode/createResolves seams. Keep public statements; both become two-liners.
- **Effort:** small.

---

## 4. Seam-mass map (M) — ledger for the SIR small-step retarget

These are **classification** findings for the parked Track-B retarget (gated on philogy's SIR
maturing), not work items against the closed flagship. Nothing in this section is dead today —
every module is on the live `lower_conforms_exact` path or its witness cone. See the Do-NOT-touch
section for the operational consequence.

### M1. Producer.lean (3,091 lines): ~90-95% dissolving mass — with a CREATE carve-out
- **Where:** `experiments/005_ir_lowering/LirLean/Realisability/Producer.lean`.
- **Corrected split:** The coupling orchestration (StreamsAligned :71, RunFromCoupled :80, DriveLogStep :95, CoupledAdvance :114, the simStmt_coupled_* family, simStmts_coupled_block :2162, driveLogStep_of_block :2476, runFrom_of_driveCorrLog :3024) dissolves under the Steps retarget. **Carve-outs the original missed:** `sim_call_stmt'` (:1074) and `sim_create_stmt'` (:1286) are coupling-FREE fixed-endpoint lemmas — and `sim_create_stmt'` (~230 lines) is the **only** CREATE per-statement Corr-re-establishment lemma anywhere in the live tree (no `sim_create_stmt` twin exists in Sim/SimStmt.lean). Port-not-delete. Also coupling-free and surviving: runs_address_preserved (:2123), runStmts_snoc (:2143), ~6 private scoping/decode helpers.
- **Ledger entry:** budget one backward step-simulation lemma per SmallStep constructor + a Steps induction, **plus** the sim_create_stmt' port (and sim_call_stmt's fixed-endpoint delta) into the coupling-free SimRel layer.

### M2. Machinery.lean (4,177 lines): ~2,600 dissolve, ~1,600 survive — section-level tagging, not whole-file
- **Where:** `LirLean/Realisability/Machinery.lean`.
- **Corrected split:** Dissolving: recorderCoupled_matRunsC (:908-1481 — materialise_runsC + a RecorderCoupled rider; the rider-free twin in Materialise/MatFoldChannel.lean survives, but consumers destructure the coupling conjunct, so no substitution today; the joint recursion is architecturally forced), termTies'_of_walk (:1482-2174), the coupled CALL/CREATE producer bricks. Surviving: defsSoundS_preserved_step (:107), scoping (:317-410), AtReachableBoundaryVJ geometry (:549-758), **plus ~590 coupling-free lines *inside* the dissolving ranges** the original missed: call_tail_of_cleanHalt (:2703-2880), create_tail_of_cleanHalt (:3533-3726), call_softfail_next_pins (:2565), present_of_closed (:2980), create scoping (:3246-3312), create_site_decode (:3790), CREATE2-halt lemmas (:3833-3876) — several `private`, so survival requires extraction/de-privatization.
- **Note:** the assessment doc's "48 vs 219" grep counts do not reproduce (~190 vs ~210 today); the coupling family is not small.

### M3. CfgSim/LowerConforms.lean (1,120) + Sim/SimStmts.lean (164): glue already off the live path — but ~250 lines must be REHOMED
- **Corrected:** The SimStmtStep/SimTermStep/sim_cfg gluing chain is **already dead-endish today**: its only consumers are the tie-parametric lower_conforms_cyclic/' that RealisabilitySpec.lean:251-252 and Producer.lean:17-23 explicitly reject (unconditional SimStmtStep unsatisfiable; assembled flagship over it deleted 2026-07-03). **But** ~250 lines are load-bearing on today's live path and orthogonal to the IR choice: WellFormedLowered (:145, 11 external refs), toList_of_blockAt (:1114, 37 refs), entry_corr (:1064), codeFrame_* reductions (:1027-1042); BudgetDerivations imports the file directly. Rehome, don't drop. Arm-survival precision: the live flagship reuses sim_assign_gas/sload and sim_term_halt_stop/_ret directly, but NOT the original sim_sstore_stmt/sim_call_stmt (live bodies are Producer's primed re-plumbs); jump/branch edge arms are not on the flagship path at all.

### M4. RunFromLeft/RunFromAll (Spec/Semantics.lean:132-207): dissolve fully under trace equality
- **Corrected:** RunFromLeft is a constructor-for-constructor clone of RunFrom threading leftovers; a `traceRealises` equality is exact by construction (SIR's SmallStep emits the trace as an output index — verified against `sir/Sir/Semantics/SmallStep.lean`, not just the docs), so the parallel relation loses its reason to exist. The conversion lemmas (:182, :192) have **zero call sites** already (runFromLeft_exists referenced only in a warning comment telling provers not to use it). Retarget-conditional: live today via RunFromCoupled/DriveLogStep/RealisabilitySpec:282 — not deletable now.

### M5. EVM-side CyclicSim coupling family (:178-970, ~840 lines): shrinks to pointwise — DEFERRED by decision
- **Corrected:** Accurate as architecture (the ten-lemma recorderCoupled_* family becomes one driveLog↔RunsTr boundary lemma; :17-177 survives incl. the private driveLog helpers as boundary-lemma raw material). **Wrong as a work item:** the family is maximally live (~100 exp005 consumer sites), and the plan of record (`docs/planning/steps-reshape-and-trace-indexing-2026-07-16.md:65-96`) headlines Decision 2 as **DEFER to the SIR retarget** — "no cheap partial slice"; consumer migration under closed proofs is the expensive part. Effort: free within the retarget; large/blocked standalone.

### M6. Recorder.lean + RecorderLemmas.lean (399 lines): survive almost whole
- **Corrected line refs (post-sload-shrink):** RecorderCoupled is `Recorder.lean:214-224` with **4** fields (not 5); callsCodeOk :226-248; driveLog :157-199; runWithLog :201-208; realisedGas/Call/Create :250-262; observe :267-270. driveLog/runWithLog/observe/callsCodeOk are the executable spec surface the retarget keeps (`hrun` verbatim); driveLog_drive/runWithLog_drive feed the future boundary lemma. Only the RecorderCoupled structure dissolves (→ traceRealises); realisedGas/Call/Create reshape into `traceOf log`. Minor: realisedCall_cons/realisedCreate_cons currently have no proof-term consumers.

### M7. Surface.lean (693): three-way split — DriveCorrLog dissolves, ties reshape, statics survive
- **Corrected:** DriveCorrLog is :303-321 (not -383); dissolve/reshape mass ≈ 390-410 lines. All six StmtTies' arms carry the RecorderCoupled antecedent (:395/:413/:437/:459/:488/:518, suffix-head pins at :488/:518) — but in TermTies' only the **branch** arm does (:643, re-established at :646/:690); stop/ret/jump are already coupling-free, so the TermTies' reshape is confined to both sides of the branch arm. Surviving vocabulary: ClosedCFG (:46), CallRealisesS/CreateRealisesS (:82/:153, modulo stream→trace), and IRWellFormed+budgets (WellLowered :225 is an internally-rebuilt adapter — RealisabilitySpec.lean:126/:214 reconstructs it — so the public survivor mapping onto SirWellFormed is IRWellFormed).

### M8. Drive/DriveSim.lean (724) + IRRun.lean (173): mostly legacy mass *already*, plus one live brick to migrate
- **Corrected:** (1) IRRun.lean no longer contains runFrom_exists/CFGAcyclic (retired); today it is the gas-free fragment ladder + RunDefinable, documented unsatisfiable for gas/call programs — dead weight **today**, independent of the retarget; its own header docstring is stale (advertises content it no longer has — cleanup regardless). (2) DriveSim's headline chain (DriveStep, runFrom_of_driveCorr, lower_conforms_cyclic/') has zero non-doc consumers — already superseded. (3) "Residue already external" is FALSE for one brick: `cleanHalts_of_runWithLog` (DriveSim.lean:146) is live on the flagship path (Producer.lean:255; axiom-guarded Audit.lean:37) and must migrate, not die. totalGas_succ_lt and driveCorr_measure are live today but dissolve with Producer's strong induction.

### M9. RealisabilitySpec.lean (788): flagships re-stated; conforms_of_worldeq survives verbatim; the gasfree cone is the open decision
- **Corrected:** The three flagships (:221/:269/:304) all close via `conforms_of_worldeq` (:174-202, statement-level IR-agnostic, retained verbatim incl. the `log.clean` seam); exact/inexact collapse under traceRealises. **Understated mass:** ~385 lines (:336-720) are the gasfree support cone (GasWalkInv, driveLog_gas_of_noGasReads, R6 resume edges) — not IR-agnostic, lives or dies with the gasfree decision, and drags the BoundaryReach NoGasOp feeder tower with it. Today `lower_conforms_gasfree`'s `hng` premise is unused in its proof and `realisedGas_nil_of_noGasReads` has zero consumers — the co-flagship's independent content is entirely in the unconsumed companion cone. Unbudgeted items: wellLowered_of_IRWellFormed needs a SirWellFormed analogue; R12a/R12b kernel cranks are Lir-specific.
- **Action for the retarget plan:** decide the gasfree co-flagship, the realisedGas_nil cone, and its BoundaryReach feeder **together**.

### M10. Surviving-mass baseline — do NOT book as savings
- **Corrected numbers:** Materialise/ 3,054; Decode/ 2,140; SimStmt 1,159 + SimTerm 811; LowerDecode 1,107; Spec/* (WellFormed 533, BudgetDerivations 475, Lowering 427, IR 67); BytecodeLayer 22,197; LirLean 22,598. Survivor list sums ~9.8k and *undercounts* non-savings mass (Machinery's value half ~1.5-1.6k, Witness* ~1.0k, Surface remainder ~220, smalls). Dissolve ledger ≈ 9.3k (within the 8.5-9.5k window); Machinery's dissolving share is the softest figure (1.5-2.6k depending on rider-twin booking). Engine carve-out slightly larger than stated: CyclicSim :178-1020 + RecorderCoupled struct + RecorderLemmas (122) + driveLog-replay parts of Recorder/SegmentedEval (~200-400). **Read "survives" as survives-in-shape:** Decode/*, Spec/Lowering+WellFormed+Budget, and the Sim bricks are parameterized over the current Lir datatype and emit tables — re-proved at comparable mass under SIR, which is exactly why they are not savings.

---

## 5. Surface (S)

### S1. Root layer map omits Exec/, Asm, EVMSpec — a newcomer draws the wrong layer map
- **Where:** `EVM/BytecodeLayer.lean:1-14`; `EVM/lakefile.lean:80-81`. *(Same fix as V2.)*
- **Verified:** imports flow one-way Exec→Hoare; no Exec/* is reachable from the root; the real consumer of the Exec surface is exp005 (26 import sites over 20/21 Exec modules + Asm/Asm.Geometry, via `require evm`). Line 6's "Spec.lean — THE AUDIT SURFACE: every exported theorem" is false post-fold. **Correction:** EVMSpec's absence from the import closure is deliberate (28e01243) — document it as draft/glob-only, do not re-import. Prefer stating Exec/ (+Asm, which imports Exec) as a second export surface over importing the Exec aggregator from the root.
- **Effort:** small.

### S2. Hoare.lean header: false "never exported" claim + phantom theorem name
- **Where:** `EVM/BytecodeLayer/Hoare.lean:27-30`.
- **Verified:** Spec.lean exports Runs-mentioning statements throughout (Runs.trans :51-53, gasAvailable_le :62-64, messageCall_runs :70-75, opcode rules :80-190); `messageCall_runs_completed` exists nowhere (Hoare.lean's own line 342 uses the correct `messageCall_runs`; port-cleanliness-review already flagged the phantom).
- **Action (refined):** The phantom's described role ("Runs → high-level Outcome") is filled by `messageCall_calls_completedWith` (Spec.lean:246, via `ofCall_completed_of_success`, Hoare/OutcomeBridge.lean:27), **not** `messageCall_runs` (whose conclusion is a CallResult equation). Either name `messageCall_runs` and drop the Outcome phrasing, or keep the phrasing and cite `messageCall_calls_completedWith`. Rewrite the "never appears in an exported statement" sentence per the accepted frame-level surface decision.
- **Effort:** trivial.

### S3. Spec.lean surface never updated for the CREATE channel
- **Where:** `EVM/BytecodeLayer/Spec.lean:47-64, 192-256` — the word "Create" does not occur in the file.
- **Verified:** Runs gained `.create` (Hoare.lean:150-154) and gasAvailable_le proves the create arm (GasMonotone.lean:287), but Spec's docstrings describe opcode-steps-plus-CALL only, and `CallReturns` is re-exported (:223) with no `CreateReturns` counterpart. **Scope (widened):** also sweep the section comment :201-204, messageCall_runs_calls docstring :225-232, GasMonotone.lean:269-280, and Hoare.lean:135-139 (all call-only). Doc-only gap — no proof path consumes the Spec-level abbrevs by name.
- **Action:** Update ~6 docstrings to mention `.create` nodes; add a `CreateReturns` abbrev mirroring :223. Combine with the V1 SPIKE sweep (root cause is the same: Spec.lean entered main in the fold commit and was never revisited after the CREATE twin landed).
- **Effort:** small.

### S4. CallReturns re-export cites wrong source module and wrong fact count
- **Where:** `EVM/BytecodeLayer/Spec.lean:216-223`.
- **Verified:** Says "Re-exported from `BytecodeLayer.Hoare.CallSequence`" and "three call-facts"; actually defined in `Hoare.lean:91-96` with **four** conjuncts ("the four call-facts", Hoare.lean:86) — Spec's own sentence enumerates all four while saying "three". History: CallReturns lived in Hoare/CallSequence.lean pre-move. The parenthetical check passed: messageCall_runs_calls's provenance (:225) IS CallSequence — leave it.
- **Action:** Provenance → `BytecodeLayer.Hoare`; "three" → "four".
- **Effort:** trivial.

### S5. SPIKE markers — same as V1; booked once there.

### S6. `driveLog` has no docstring; soft-fail recording is silently CALL/CREATE2-only
- **Where:** `EVM/BytecodeLayer/Exec/Recorder.lean:157-208`; soft-fail arms :185-190 (`isCreate2Op`/`isCallOp` under `stack.isEmpty`).
- **Verified:** descent-side recordCall/recordCreate (:145-155) are opcode-agnostic on the Pending constructor, while stepFrame emits `.needsCall` for CALL/CALLCODE/DELEGATECALL/STATICCALL (`EVM/BytecodeLayer/Semantics/System.lean:1293`) and `.needsCreate` for CREATE/CREATE2 (:1348); wider-family soft-fails are reachable in `EVM/Evm/Semantics/System.lean:12-125` (shared callArm else-branch; createArm for plain CREATE). So 1:1 cursor/stream alignment holds only for CALL/CREATE2 cursors — exactly what lowering emits today; all live alignment proofs operate on IsLoweringOp-scoped programs. **Forward risk (per CREATE-is-wanted):** `IsLoweringOp` (`LirLean/Decode/SegAligned.lean:31`) already whitelists `.System .CREATE`; the moment CREATE emission lands, the missing CREATE soft-fail arm becomes a live creates-stream misalignment.
- **Action:** Docstrings on driveLog and runWithLog: the stack-isEmpty top-level gate, the two-arm soft-fail dispatch, the CALL/CREATE2-only scope, and an explicit warning that CREATE lowering must land a CREATE soft-fail arm mirroring the CREATE2 one. This is a doc fix now and a checklist item for the CREATE feature.
- **Effort:** small.

### S7. `World` names two different types in sibling namespaces — DOWNGRADED to cosmetic
- **Where:** `Exec/Observable.lean:16` (`World := Word → Word`) vs `Hoare/Behaves.lean:36` (`World := CallParams`).
- **Verdict (empirically tested by compiling scratch files against the built oleans):** the claimed shadowing trap does not exist — same-level double-open makes bare `World` a hard `Ambiguous term` error in either order; in Recorder.lean the enclosing `namespace BytecodeLayer.Exec.Recorder` prefix resolves it deterministically, order-independent. Bare `World` appears in code only where a namespace prefix wins (Recorder, and exp005's `Lir.World` alias). Nothing can misresolve today.
- **Action:** Optional low-priority rename `Exec.World` → `Exec.Storage` (small ripple: `Lir.World` alias at LirLean/Spec/Semantics.lean:9 + Observable/Recorder uses). Not worth scheduling on its own; fold into any future Exec/Observable touch.
- **Effort:** medium as standalone; effectively deferred.

### S8. `Behaves` is a zero-use entry point that the audit surface silently drops
- **Where:** `Hoare/Behaves.lean:45`; imported by `Spec.lean:4` and `Hoare/OutcomeBridge.lean:3`, used in zero statements repo-wide.
- **Corrected framing:** imports are transitive, so "never re-exported" is imprecise — the accurate charge is that Spec.lean breaks its own convention (every other import gets a documented wrapper; Behaves gets nothing) and no theorem anywhere is phrased through it. `Hoare.World` (:36) shares the zero-consumer fate. The OutcomeBridge import is verified droppable. exp005's own prior audits independently recorded "Behaves zero consumers".
- **Action (do NOT delete — incremental lemma toward the quantified-over-programs goal):** either surface it (Spec.lean section documenting it as the target predicate, restate a completedWith-style result through it) or, minimally, fix the dead doc citation (V4) and drop the unused OutcomeBridge import.
- **Effort:** small.

### S9. EVMSpec surface — same as V7; booked once there. Root map needs a "canonical = EVMSemantics/flatSem" breadcrumb.

### S10. Exec.lean aggregator: two stray encoding defs; closure omits exactly TWO modules (not three)
- **Where:** `EVM/BytecodeLayer/Exec.lean:1-29`.
- **Heavily corrected:** Only the surface kernel survives adversarial checking. Real: `offsetBytesBE`/`wordBytesBE` (:21-27) are undocumented defs in an import-hub file; the aggregator's transitive closure omits SegmentedEval and CheckedStep. **Refuted details:** ByteWindow's omission is structurally forced (`Exec/ByteWindow.lean:1` imports `BytecodeLayer.Exec` — adding it to the aggregator creates an import cycle; the original proposed action would break the build). CheckedStep is NOT unimported (LirLean/Realisability/CheckedStep.lean:2 → the live R12a witness chain); SegmentedEval is imported directly by LirLean; Asm/Geometry is not orphaned (three LirLean Decode importers); the two defs are NOT LirLean-only (Asm.lean:70,72,106 PUSH-immediate encoders, ~15 uses in Asm/Geometry proofs, round-trip theorems in ByteWindow).
- **Action:** Add docstrings to the two defs; optionally move them to a small topical module *below* the aggregator (ByteWindow as-is cannot host them without first narrowing its aggregator import); optionally add SegmentedEval+CheckedStep (only) to Exec.lean or comment why they stay off the hub.
- **Effort:** small.

---

## 6. Do NOT touch (dissolves or reshapes under the SIR retarget — doing the work twice is waste)

The SIR small-step retarget (Track B, parked, gated on philogy's `sir/` maturing) replaces the
big-step RunFrom manufacturing and the pervasive RecorderCoupled threading with an up-front SimRel
+ Steps induction + `traceRealises` trace equality. Per the plan of record
(`docs/planning/steps-reshape-and-trace-indexing-2026-07-16.md`, Decision 2: **DEFER**), the
following must NOT receive standalone refactors now:

1. **Producer.lean coupling orchestration** (M1) — dissolves ~90-95%. *Exception:* the
   `sim_create_stmt'`/`sim_call_stmt'` value cores are port targets, not deletions.
2. **Machinery.lean coupled walks** (M2: recorderCoupled_matRunsC, termTies'_of_walk, *_of_coupled
   bricks) — dissolve; the embedded coupling-free geometry (~590 lines) gets extracted *then*, not now.
3. **LowerConforms/SimStmts glue** (M3) — already off the live path; the ~250 surviving lines get
   rehomed as part of the retarget (or a cheap standalone rehome if the file blocks something).
4. **RunFromLeft/RunFromAll + the `_exact` parallel-relation plumbing** (M4).
5. **CyclicSim's recorderCoupled_* family as a whole** (M5) — shrinks to one boundary lemma *inside*
   the retarget; consumer migration under closed proofs is the expensive part. Corollary: the
   medium-effort dedups D1/D3 inside this family carry a discount — do them only if the retarget
   stays parked for a long horizon; the trivial/small ones (D2/D4/D5) are cheap enough to do anyway.
6. **E4 option (b)** (fuel-free RTC restatement of `RecorderCoupled.restart`) — this IS the
   retarget's reshape; never do it standalone.
7. **E5** (driveLog suffix-return refactor) — interacts with both the segmented witness machine and
   the retarget's traceOf reshape; decide inside the retarget plan (and sequence with nothing —
   the sload-stream shrink it was to be sequenced with has already landed, V6).
8. **DriveSim/IRRun** (M8) — legacy chain already superseded; migrate `cleanHalts_of_runWithLog`
   when the file goes, not before. (IRRun's stale header docstring may be fixed in the doc sweep.)
9. **RealisabilitySpec flagship statements + gasfree cone** (M9) — restate once, in the retarget;
   decide the gasfree co-flagship + realisedGas_nil cone + BoundaryReach NoGasOp feeder together.

**Survivors to protect** (never book as savings, never "simplify away"): Materialise/*, Decode/*,
Sim/SimStmt+SimTerm bricks, LowerDecode, Spec/* emit-and-budget layer, the 22.2k BytecodeLayer
engine minus the coupling family, Recorder.lean's executable surface (driveLog/runWithLog/observe/
callsCodeOk + realised* maps → traceOf), `conforms_of_worldeq`, and the `RunLog.clean` seam (M6,
M9, M10). Also protected per standing directive: **all CREATE machinery** (Create.lean, the CREATE
descent/soft-fail channel, CreateRealisesS) — CREATE is a wanted feature; findings here only
consolidate its encodings (D8) and pre-plan its recorder arm (S6).

---

## 7. Prioritized backlog (value / effort)

**P0 — trivial, do in one hygiene pass (all comment-/doc-only, zero build risk):**
1. Doc truth-sweep bundle: V1 (SPIKE + R4 + Create.lean pointer, with the DriveRuns "R4 residual"
   reword), V2/S1 (root header), V3 (Spec header + settled altitude ruling, recorded in-repo/AGENTS),
   V4 (Behaves citation), V9 (ir-design-v2 paths + GasMonotone self-ref), V10 (exp-naming sweep,
   preserving TransCmp-gap + exp004 refs), S2 (phantom theorem), S3 (CREATE-channel docstrings +
   CreateReturns abbrev), S4 (provenance/count), S6 (driveLog/runWithLog docstrings + CREATE-arm
   warning), V5 (StackUnderflow instance docstring), S10 (offsetBytesBE/wordBytesBE docstrings),
   M8's IRRun header. Bookkeeping: V6 (update sload memory note + index; no code).
2. D5: child_ne_oof_of_framed merge (3+3 call sites + docstring reword).

**P1 — small, high confidence:**
3. E2/D2: `drive_ok_agree` + rewrite 6 sites (also deletes the DriveRuns case-split scaffolding).
4. E1: move `_lt` framing induction to DescentEq; derive the 3 unbounded lemmas (~80-85 lines).
5. D4: halted-twin one-liners (hoist _inv + suffixes_nil first).
6. D10: `callsCodeOk_along_runs` local shared lemma; both soundness theorems become two-liners.
7. V8: HoareDemo keep-or-retire decision (recommend keep + import + cross-link).
8. V7/S9: EVMSpec banner rewrite + root breadcrumb; schedule the adopt-vs-archive decision.
9. S8: Behaves — drop OutcomeBridge import; decide surface-or-annotate.

**P2 — medium, worth scheduling:**
10. D8: CREATE soft-fail consolidation (named records + createArm_next_inv + strengthened
    systemOp_createArm_reduce; ~400 lines; feeds future CREATE lowering).
11. D7: parametric stepFrame_next_smsf_pc + binOp variant (~220 → ~60 lines; keep 8 names).
12. E7: Descent full-payload characterizations, starting with the systemOp_createArm_reduce
    strengthening (shared with #10 — do together).
13. E6: stash-tail fr-level restatement + envelope shrink (sweep the 3 exp005 twins; both cones green).
14. D6: generic Machine/steps/shift/final + stepsChk (validate the `decide +kernel` canary).
15. D1 (+D3): recorderCoupled peel consolidation — **discounted** (dissolving mass, Do-NOT-touch #5);
    only if the retarget horizon is long.
16. E4 option (a): re-phrase CyclicSim peels over the existing driveLogC_succ_eq — same discount.

**P3 — large, pilot-gated or deferred:**
17. E3/D9: drive-induction principle — pilot on drive_error_oof + framed_oof per family; requires
    building a `nextDrive` reification first. Enforce the minimum bar (no twelfth transcript) now.
18. E5: driveLog suffix refactor — decide inside the retarget plan.
19. E8: reified-evaluator/USize confinement — parked (churn-to-deletion ratio unfavorable).
20. S7: Exec.World → Storage rename — fold into a future touch.
21. The seam-mass ledger (M1-M10) — input to the SIR retarget plan, not standalone work.

---

## Appendix A — refuted findings (do not re-find)

### A1. "The 6-hypothesis AccPresent seam bundle is threaded through 4 signatures although all six seams are now proven theorems"
**REFUTED.** The line citations and the seam duplication between `Hoare/DriveMono.lean:158-168`
and `Exec/CallPreservesSelf.lean:52-62` are accurate, and 5-of-6 discharged at :126-131/:195-199
checks out — but both load-bearing claims are false today: `beginCall_inr_noErase` has callers,
`selfPresent_runs_of_call` has consumers, and the "_modGuards wrappers only" framing describes
ordinary supply-then-discharge lemma layering on the live `lower_conforms_exact` cone (verified in
DriveMono, CallPreservesSelf, WitnessChecks:100-180, exp005 WitnessParams + Drive/CallPreservesSelf
re-exports, both lakefiles; the Lir.V2 copy under `.worktrees/foundation` is a stale worktree, not
the live tree). Not vestigial; no action.

### A2. Partial refutations folded into findings above (for the record)
- **S7 (World name clash):** the shadowing-trap mechanism was empirically refuted by compilation;
  downgraded to cosmetic.
- **S10 (Exec.lean aggregator):** the orphan narrative (CheckedStep unimported, Geometry orphaned,
  defs LirLean-only) was refuted; only the doc/placement kernel is real, and the original proposed
  import addition (ByteWindow) is build-breaking.
- **E4 (RecorderCoupled keystone):** the "no driveLog step lemma exists" premise was refuted —
  `driveLogC_succ_eq` exists and is live; the finding survives only as a boilerplate shave.
- **V5 (StackUnderflow):** "a decode defect" refuted (branch unreachable); "still unrecorded"
  half-refuted (docs/backlog.md already documents it); survives as a docstring-only item.
- **E1 ("3 of 6 could be corollaries"):** the descend pairs were shown to already be corollaries;
  only one duplicated induction exists.

---

*Report generated by the bytecode-layer audit fleet, adversarial verification pass included.
All file:line citations verified 2026-07-18 at `dde891e9`. No code was changed by this audit.*
