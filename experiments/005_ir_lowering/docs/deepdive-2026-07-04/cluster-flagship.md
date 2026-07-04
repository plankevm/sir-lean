# Cluster: Flagship + Audit net (deep dive 2026-07-04)

Files audited (read in full, all decl bodies of load-bearing/questionable lemmas):

- `LirLean/V2/RealisabilitySpec.lean` (3874 LOC) — the WIP-only Phase-3 realisability
  spec skeleton; sole root of the non-default `WIP` lean_lib; the tree's **only**
  sorry-carrier. Imported by nobody (`grep -rn RealisabilitySpec LirLean/` finds only
  docstring mentions, never an `import`; `lakefile.lean:31-32` roots the `WIP` lib at it).
- `LirLean/Audit.lean` (62 LOC) — the default-target axiom-footprint audit net; imported
  LAST by the `LirLean` root (`LirLean.lean:52-53`, `import LirLean.Audit` "MUST stay last").

These two files are grouped because both concern the flagship: `RealisabilitySpec.lean`
*hosts* the flagship-in-progress `Lir.V2.lower_conforms`; `Audit.lean` pins the salvage
layer's axiom footprint and is the file where the flagship signature will be frozen once
R11 lands (`Audit.lean:21-24`). They do NOT import each other.

---

## Ground truth verified against the grounding brief

- **Flagship** = `Lir.V2.lower_conforms` at `RealisabilitySpec.lean:3705`. Confirmed
  verbatim. Conclusion `∃ O, RunFrom prog (entryState params) (realisedGas log)
  (realisedCall log params.recipient) prog.entry O ∧ Conforms params.recipient log O`
  (:3715-3718). `Conforms` (:155) compares **world AND result** (foundation
  full-observable change) — `O.world = (observe self log.observable).world ∧ O.result =
  (observe self log.observable).result`.
- **The central blocker is NOT a citable leaf.** The flagship body (:3719-3747) packages
  a single `sorry` (:3739-3746) whose type is the coupled run-producer
  `runFrom_of_driveCorrLog` (named in the comment :3724; does not exist in the tree). The
  comment (:3730-3736) explicitly rules out citing `lower_conforms_cyclic'` (needs an
  unconditional all-frames `SimStmtStep` the reshaped `StmtTies'` cannot supply) and rules
  out citing R6 `runs_atReachableBoundary` alone (its `hsize` B2 side condition has no
  producer from `hwl`). Everything downstream of the `obtain` (`conforms_of_worldeq`,
  :3661) is CLOSED axiom-clean assembly (I read the full body :3670-3689 — no sorry).
- **Exactly 11 open `sorry` bodies** (machine-confirmed): `1385` (R3), `2343`+`2351` (R6
  step edge bricks), `2380`+`2383` (R6 call edge bricks), `3634` (R10a), `3746`/`3780`/`3817`
  (R11 flagship family), `3828` (co-flagship companion), `3843` (R12a). The R7 region
  (2466-2958) and the entire §6 witness (2959-3623) are fully sorry-free (verified by awk).

---

## Per-file section 1: `LirLean/V2/RealisabilitySpec.lean`

**Purpose** (grounded in the module header :5-103 + `docs/target-architecture-2026-07-02.md`):
the reviewable Phase-3 target-statement skeleton. Every `def`/`structure`/`inductive` is
REAL (complete, no sorry); only theorem proofs are sorry'd, and each is a named obligation
(R0–R12) bridging the green in-tree machinery to the flagship. Deliberately in the
`WIP` lib so the default `LirLean` target stays sorry-free. Shaped by 8 documented vacuity
lessons (:15-86): the retired `GasRealises` universal, the free-∀ disease in the old
`StmtTies`/`TermTies`, `SstoreRealises`/`RunDefinable` unsatisfiability, the `defsOf`
shadowing hole, the resolved single-call restriction, and the round-3 scoping-∀ disease.

### §1 — Helper definitions (all REAL, no sorry) — :114-564

| decl | kind | role | callers |
|---|---|---|---|
| `entryState` | def :126 | shared-infra: the flagship's pinned IR entry state (definitional replacement of the deleted supplied entry `StorageAgree`) | flagships :3716/3763/3800, `exProg_nonvacuity` :3853 |
| `RunLog.clean` | def :143 | shared-infra: the flagship's `hclean` premise (log-side clean-halt, conservatively excludes zero-gas reverts) | `haltNonException_of_cleanLog` :1270, all flagships (`hclean` arg) |
| `Conforms` | def :155 | terminal-for-flagship: the conclusion edge (world + result agreement) | `conforms_of_worldeq` :3670, all flagships |
| `ClosedCFG` | structure :165 | incremental-toward-R8/flagship: static CFG closure; `WellLowered.closed` field | `WellLowered.closed` :491, `present_of_closed` :2948, `closedCFG_exProg` :3471 |
| `StackRoomOK` | structure :193 | incremental-toward-flagship: static per-cursor stack bounds; `WellLowered.stack` | `WellLowered.stack` :493, `stackRoomOK_exProg` :3493 |
| `StmtDefinableG` | def :227 | shared-infra: per-statement operand definability | `RunDefinableG.stmts` :246 |
| `RunDefinableG` | structure :240 | incremental-toward-flagship: gas/call-aware run-definability (honest replacement of unsatisfiable `RunDefinable`); `WellLowered.defs` | `WellLowered.defs` :482, `runDefinableG_exProg` :3403 |
| `DefsConsistent` | def :277 | incremental-toward-R0b/flagship: static `defsOf`-cursor consistency (header lesson 6); `WellLowered.defsCons` | `WellLowered.defsCons` :487, `defsSoundS_preserved_step` :1113, `defsConsistent_exProg` :3453 |
| `ReadsOf` | def :326 | shared-infra: static registered-reader relation (invalidation unit) | `invalStep` :338/342, `defsOf_exProg_reads` :3012 |
| `invalStep` | def :336 | incremental-toward-R0b: per-statement invalidation-set transfer (header lesson 8) | `DefsSoundS` threading, `RevalidatesPerBlock` :390, `defsSoundS_preserved_step` :1118 |
| `DefsSoundS` | def :350 | incremental-toward-R0b: shadowing-aware recompute soundness | `defsSoundS_empty_iff` :359, `defsSoundS_preserved_step` :1117 |
| `defsSoundS_empty_iff` | theorem PROVED :358 | incremental-toward-R0b: bridge (empty invalidation set = strong `DefsSound`) | none yet; builds toward the R0 mid-block→boundary reshape |
| `StepScopedS` | def :372 | incremental-toward-R10: static per-step scoping residue (header lesson 8) | `StmtTies'` arms :724/741/764/785, `CallRealisesS` :413 |
| `RevalidatesPerBlock` | def :388 | incremental-toward-R0b: per-block boundary re-validation criterion | `revalidatesPerBlock_exProg` :3077 |
| `CallRealisesS` | def :406 | incremental-toward-R3/R10: shadowing-aware call-realisability tie (deliberate near-copy of in-tree `Lir.CallRealises`, StepScoped→StepScopedS) | `StmtTies'` call arm :809, `callRealises_of_recorded` :1378 |
| `WellLowered` | structure :477 | **terminal-for-flagship**: THE static bundle (`hwl`); 11 fields | every flagship, `stmtTies'/termTies'_of_runWithLog` :3628/3639, `callRealises_of_recorded` :1368, `wellLowered_exProg` :3585 |
| `ReachableFrom` | def :533 | shared-infra: reachable-frame predicate (fleet sketch named-undefined; defined here) | `PrecompileAssumptions.callsCode` :555 |
| `PrecompileAssumptions` | structure :550 | **terminal-for-flagship**: the sole honest seam (`hseams`); `noErase`+`callsCode` | all flagships, `stmt/termTies'_of_runWithLog`, `exProg_satisfies_hypotheses` :3843 |
| `NoGasReads` | def :562 | incremental-toward-co-flagship: gas-introspection-free scope (`hng`) | `lower_conforms_gasfree` :3790, `realisedGas_nil_of_noGasReads` :3825 |

### §2 — Recorder-restart coupling — :566-647

| decl | kind | role | callers |
|---|---|---|---|
| `RecorderCoupled` | structure :599 | **central antecedent**: the load-bearing coupling (restart determinism pins suffixes + observable) that kills the free-∀ disease | `DriveCorrLog.coupled` :647, `StmtTies'` arms, `callRealises_of_recorded` :1373, all R7 edges |
| `DriveCorrLog` | structure :629 | incremental-toward-R11-blocker: the recoupled walk invariant the missing `runFrom_of_driveCorrLog` threads | none yet in proven code; it is the invariant the blocker walks |

### §3 — Reshaped ties — :649-948

| decl | kind | role | callers |
|---|---|---|---|
| `StmtTies'` | def :710 | incremental-toward-R10/R11: reshaped per-block statement ties (5 arms, every free value now antecedent-pinned) | `stmtTies'_of_runWithLog` :3634 (built), consumed by the missing driver |
| `TermTies'` | def :817 | incremental-toward-R10/R11: reshaped per-block terminator ties (4 arms; address/kind demands are now antecedents) | `termTies'_of_walk` :1469, `termTies'_of_runWithLog` :3642 |

### §4 — Exact stream consumption — :950-1040

| decl | kind | role | callers |
|---|---|---|---|
| `RunFromLeft` | inductive :963 | incremental-toward-R11-exact: `RunFrom` mirror exposing leftover streams | `RunFromAll` :1012, `runFrom_of_runFromLeft` :1019, `runFromLeft_exists` :1031 |
| `RunFromAll` | def :1010 | terminal-for-flagship-exact: whole-stream consumption (both leftovers `[]`) | `lower_conforms_exact` :3763 |
| `runFrom_of_runFromLeft` | theorem **PROVED** :1017 | shared-infra: mirror adequacy (forgetful) | none yet; builds toward `lower_conforms_exact` |
| `runFromLeft_exists` | theorem **PROVED** :1029 | shared-infra: mirror adequacy (completion) | none yet; builds toward `lower_conforms_exact` |

> NOTE — correction to grounding: `runFrom_of_runFromLeft`/`runFromLeft_exists` are listed
> as OPEN in the brief's R-list but are fully proven by structural induction (no sorry in
> 1017-1040). They are incremental infra, not open leaves.

### §5 — Obligations R0b–R11 machinery — :1042-2958

| decl | kind | role | callers |
|---|---|---|---|
| `evalExpr_setStorage_noSload` | private thm PROVED :1055 | shared-infra: R0b helper (storage-write irrelevance) | `defsSoundS_preserved_step` :1185 |
| `evalExpr_world_noSload` | private thm PROVED :1068 | shared-infra: R0b helper (world-replacement irrelevance) | `defsSoundS_preserved_step` :1199/1218 |
| `defsSoundS_preserved_step` | theorem **PROVED** :1110 | terminal-for-R0b: one `EvalStmt` step preserves scoped invariant along `invalStep`, side-condition-free | none yet; the reshape it gates re-plumbs the sim spine (cross-file, future) |
| `runs_halt_eq` | theorem PROVED :1223 | shared-infra: halting `Runs` is refl | `haltNonException_of_cleanLog` :1259, `conforms_of_worldeq` :3681 |
| `haltNonException_of_cleanLog` | theorem **PROVED** :1240 | terminal-for-R2 | none yet; consumed by the missing driver / clean-scope threading |
| `resumeAfterCall_code` | theorem PROVED (rfl) :1300 | incremental-toward-R3: resume-frame code pin | none yet; feeds R3 bundle conjuncts |
| `resumeAfterCall_validJumps` | theorem PROVED (rfl) :1305 | incremental-toward-R3 | none yet |
| `resumeAfterCall_pc` | theorem PROVED (rfl) :1309 | incremental-toward-R3 | none yet |
| `resumeAfterCall_stack` | theorem PROVED (rfl) :1313 | incremental-toward-R3 | none yet |
| `callRealises_of_recorded` | theorem **SORRY** :1364 (:1385) | **open leaf R3**: Piece A landed (`recorderCoupled_call_extract`), Piece B (machine arg-push run, ~200 lines) has no in-tree producer | none yet; builds `StmtTies'` call arm |
| `sstoreRealises_at_frame` | theorem **PROVED** :1396 | terminal-for-R4: point-wise SSTORE realisation (honest replacement of unsatisfiable `∃ acc, SstoreRealises`) | none yet; the reshaped `sim_sstore_stmt` will consume it (cross-file) |
| `runs_kind` | theorem PROVED :1423 | shared-infra: `kind` preserved across `Runs` | `termTies'_of_walk` (ret arm) |
| `termTies'_of_walk` | theorem **PROVED** :1469 | terminal-for-R5 (big proof, `maxRecDepth 8192`) | `termTies'_of_runWithLog` :3644 |
| `recordCall_append` | private thm PROVED :2088 | shared-infra: R7 append helper | `driveLog_acc_hom` :2128/2143 |
| `driveLog_acc_hom` | private thm PROVED :2099 | shared-infra: THE R7 accumulator-homomorphism linchpin | the R7 edge lemmas (peel recorded heads) |
| `isGasOp_false_of_isSloadOp` | private thm PROVED :2179 | shared-infra: gas/sload gate exclusivity | R7 sload/other edges |
| `emptyProg` | def :2214 | scaffold: zero-block counterexample witness (B1) | `emptyParams`, `not_runs_atReachableBoundary` |
| `emptyParams` | def :2218 | scaffold: minimal code call for B1 | `not_runs_atReachableBoundary` :2238 |
| `not_runs_atReachableBoundary` | theorem **PROVED** :2232 | terminal (refutation): R6's side-condition-free `∀` form is FALSE (motivates `hne`) | none (a documented refutation, like `not_defsSound_stale`) |
| `lower_size_eq` | theorem PROVED :2249 | shared-infra: `ByteArray`↔`List` size bridge | `atReachableBoundaryVJ_step` :2358, `_call` :... |
| `flatBytes_length_pos` | theorem PROVED :2255 | shared-infra: B1 positive half | `atReachableBoundary_entry` :2285 |
| `atReachableBoundary_entry` | theorem PROVED :2272 | incremental-toward-R6: entry base case | `atReachableBoundaryVJ_entry` :2314 |
| `AtReachableBoundaryVJ` | def :2298 | incremental-toward-R6: strengthened boundary invariant (+`validJumps`, needed by taken-jump edge) | the R6 edge/base/combinator lemmas |
| `atReachableBoundaryVJ_entry` | theorem PROVED :2305 | incremental-toward-R6: strengthened base | `runs_atReachableBoundary` :2464 |
| `atReachableBoundaryVJ_step` | theorem **SORRY** :2325 (:2343,:2351) | **open leaf R6**: STEP edge; 2 pure-engine bricks (B-pc dispatch walk, B-inrange) whose home is a default-target file | `atReachableBoundaryVJ_of_runs` :2416 |
| `atReachableBoundaryVJ_call` | theorem **SORRY** :2369 (:2380,:2383) | **open leaf R6**: CALL edge; 2 bricks (B-call inversion, B-inrange) | `atReachableBoundaryVJ_of_runs` :2417 |
| `atReachableBoundaryVJ_of_runs` | theorem PROVED* :2410 | incremental-toward-R6: `Runs`-induction combinator (*cites the sorry edges) | `runs_atReachableBoundary` :2463 |
| `runs_atReachableBoundary` | theorem PROVED* :2456 | terminal-for-R6: the `hrb` boundary walk (*transitively rests on the 3 bricks) | none yet; produces `hrb` for the flagship/driver |
| `recorderCoupled_entry` | theorem PROVED :2474 | terminal-for-R7a: entry coupling | none yet; seeds the missing driver's walk |
| `recorderCoupled_step_gas` | theorem PROVED :2493 | terminal-for-R7b: GAS step consumes suffix head | none yet |
| `gasSuffix_nonempty` | private thm PROVED :2531 | shared-infra: R7b helper | `gas_suffix_head_realised` / gas edges |
| `gas_suffix_head_realised` | theorem PROVED :2584 | terminal-for-R1-adjacent: gas suffix head IS the machine GAS output | none yet; feeds `StmtTies'` gas arm via the driver |
| `recorderCoupled_sload` | theorem PROVED :2615 | terminal-for-R7: SLOAD step edge | none yet |
| `recorderCoupled_step_other` | theorem PROVED :2651 | terminal-for-R7: non-gas/sload step edge | `recorderCoupled_stepsTo_other` :2941 |
| `driveLog_frame_nonempty` | private thm PROVED :2675 | shared-infra: R7 call-edge helper | `recorderCoupled_call`/`_extract` |
| `recorderCoupled_call` | theorem PROVED :2771 | terminal-for-R7: CALL step edge (black-boxes child's inner reads) | none yet |
| `recorderCoupled_call_extract` | theorem PROVED :2858 | terminal-for-R3-PieceA: produces `CallReturns`+record identity from the coupling | referenced by R3 status (:1338); consumed by the driver |
| `recorderCoupled_stepsTo_other` | theorem PROVED :2933 | terminal-for-R7: `StepsTo` wrapper of `_step_other` | none yet |
| `present_of_closed` | theorem **PROVED** :2947 | terminal-for-R8: successor presence from `ClosedCFG` | none yet; feeds `DriveCorrLog.present` |

### §6 — Concrete non-vacuity witness `exProg` + R9 + R10–R12 assembly — :2959-3865

| decl | kind | role | callers |
|---|---|---|---|
| `exProg` | def :2975 | **terminal-for-R9/R12**: the anti-vacuity witness (gas+sload+sstore+call+cycle) | ~20 witness lemmas below; `exProg_satisfies_hypotheses`, `exProg_nonvacuity` |
| `DecidableEq Block`/`Program` | deriving instance :2996/2997 | shared-infra: needed by the singleton checker + witness `decide`s | `wellLowered_check_exists`, witness proofs |
| `defsOf_exProg_eq` | thm PROVED :3003 | incremental-toward-R9: closed-form `defsOf exProg` | witness scoping lemmas |
| `defsOf_exProg_reads` | thm PROVED :3012 | incremental-toward-R9: only readers are t8←t6/t7 | `revalidatesPerBlock_exProg` |
| `not_readsOf_exProg` | thm PROVED :3034 | incremental-toward-R9 | witness |
| `invalStep_false_assign/_sstore/_call` | 3 thms PROVED :3043/3054/3060 | incremental-toward-R9: invalidation-fold arms | `revalidatesPerBlock_exProg` |
| `revalidatesPerBlock_exProg` | thm PROVED :3077 | incremental-toward-R9: `RevalidatesPerBlock exProg` | (would feed the reshaped walk / R9 checker) |
| `staleSt` | def :3151 | scaffold: the stale mid-block state for the refutation | `not_defsSound_stale` |
| `not_defsSound_stale` | thm **PROVED** :3166 | terminal (refutation): un-scoped `DefsSound` FALSE at exProg's real loop-exit state — motivates R0b | none (a proved refutation) |
| `setLocal_self`/`setLocal_bound` | private thms PROVED :3188/3193 | shared-infra: R9 binding helpers | `runStmts_binds_assign` |
| `runStmts_preserves_bound` | thm PROVED :3204 | incremental-toward-R9: prefix-binding preservation | R9 inversion |
| `runStmts_binds_assign` | thm PROVED :3226 | incremental-toward-R9: prefix-binding inversion | (R9 grind) |
| `exBlk0/1/2`, `blockAt_exProg{0,1,2}`, `toList_exProg{0,1,2}`, `blockAt_exProg_inv`, `toList_exProg_inv` | private defs/thms PROVED :3248-3290 | scaffold: witness block-lookup plumbing | the `WellLowered exProg` field proofs |
| `rankExProg` | private def :3292 | scaffold: acyclicity rank for exProg | `acyclic_exProg` |
| `acyclic_exProg` | private thm PROVED :3294 | incremental-toward-R9: `Acyclic (defsOf exProg)` | `acyclicWellFormedExProg` |
| `acyclicWellFormedExProg` | private def :3311 | incremental-toward-R9 | `wellFormedLowered_exProg` |
| `wellFormedLowered_exProg` | private thm PROVED :3365 | incremental-toward-R9: `WellFormedLowered exProg` | `wellLowered_exProg` |
| `chargeOf_length_indep` | private thm PROVED :3372 | shared-infra: charge-length ∀-sloadChg independence | `stackRoomOK_exProg`/`runDefinableG_exProg` |
| `runDefinableG_exProg`, `defsConsistent_exProg`, `closedCFG_exProg`, `stackRoomOK_exProg`, `gasBound_exProg`, `slotAddr_exProg`, `retEpilogueBound_exProg`, `noSlotSource_exProg` | private thms PROVED :3403-3573 | incremental-toward-R9: the 8 `WellLowered exProg` field discharges | `wellLowered_exProg` |
| `wellLowered_exProg` | private thm **PROVED** :3585 | terminal-for-R9-anti-vacuity: `WellLowered exProg` genuinely holds | `wellLowered_check_exists` :3613, `exProg_nonvacuity` :3865 |
| `wellLowered_check_exists` | thm **PROVED** :3603 | terminal-for-R9: sound checker accepts the witness (singleton checker; general checker `def` is tracked debt) | none yet |
| `stmtTies'_of_runWithLog` | theorem **SORRY** :3624 (:3634) | **open leaf R10a**: build `StmtTies'` from the run | none yet; feeds R11 assembly |
| `termTies'_of_runWithLog` | theorem **PROVED** :3638 | terminal-for-R10b (cites `termTies'_of_walk`) | none yet; feeds R11 assembly |
| `conforms_of_worldeq` | theorem **PROVED** :3661 | **terminal-for-flagship**: the CLOSED `Conforms` channel (world+result), reused by all 3 flagships | `lower_conforms` :3747, `_exact` :3781, `_gasfree` :3818 |
| `lower_conforms` | theorem **SORRY** :3705 (:3746) | **THE FLAGSHIP (R11)**; body reduces to the single missing `runFrom_of_driveCorrLog` | `exProg_nonvacuity` :3864 |
| `lower_conforms_exact` | theorem **SORRY** :3752 (:3780) | terminal (R11-all): exact-consumption strengthening via `RunFromAll` | none yet |
| `lower_conforms_gasfree` | theorem **SORRY** :3788 (:3817) | terminal (co-flagship, de-risking checkpoint; prove first) | none yet |
| `realisedGas_nil_of_noGasReads` | theorem **SORRY** :3823 (:3828) | open leaf: co-flagship companion (empty gas stream) | none yet |
| `exProg_satisfies_hypotheses` | theorem **SORRY** :3835 (:3843) | **open leaf R12a**: flagship antecedent TRUE at exProg + engine-stub seam machine-check | `exProg_nonvacuity` :3861 |
| `exProg_nonvacuity` | theorem PROVED* :3848 | terminal-for-R12b (*green now; axiom-clean once R11+R12a land — cites both) | none |

> NOTE — correction to grounding: R12b `exProg_nonvacuity` (:3848) is NOT itself an open
> sorry; it is assembled from R12a + the flagship and typechecks (transitively sorry).
> `runs_atReachableBoundary` (R6, :2456) likewise has a closed body; the open sorries are
> the 2+2 bricks inside its two edge lemmas (3 distinct bricks: B-pc, B-inrange, B-call).

---

## Per-file section 2: `LirLean/Audit.lean`

**Purpose**: the default-target axiom-footprint audit net (Track A). Contains NO
declarations — only `#guard_msgs in #print axioms` guards that freeze the axiom footprint
of 8 load-bearing exp005 decls, turning any drift (new axiom, `sorry`, native `decide`)
into a hard build error. Must stay the LAST import of the `LirLean` root (`LirLean.lean:53`).

| item | kind | role |
|---|---|---|
| header docstring :8-24 | doc | records the 2026-07-03 removal of the vacuous flagship surface (`lower_conforms_cyclic_assembled`/`_tiefree`, `Lir.lower_conforms_wf`, `Lir.Spec` re-export); notes plan-of-record surface is now `RealisabilitySpec.lean`, signature to be frozen here once R11 proven |
| `#print axioms Lir.V2.callPreservesSelf_modGuards` | guard :27-29 | terminal-for-audit: pins `[propext, Classical.choice, Quot.sound]` |
| `#print axioms Lir.materialise_runs_of_cleanHalt` | guard :31-33 | terminal-for-audit |
| `#print axioms Lir.V2.cleanHalts_of_runWithLog` | guard :35-37 | terminal-for-audit |
| `#print axioms Lir.jump_landing_of_cleanHalt` | guard :39-41 | terminal-for-audit |
| `#print axioms Lir.branch_landing_of_cleanHalt` | guard :43-45 | terminal-for-audit |
| `#print axioms Lir.V2.stepPreservesSelf` | guard :47-49 | terminal-for-audit |
| `#print axioms Lir.sim_assign_sload_lowered` | guard :51-53 | terminal-for-audit |
| `#print axioms Lir.Spec.callPreservesSelf_of_precompiles` | guard :60-62 | terminal-for-audit: the surviving `Lir.Spec` precompile-self seam forwarder |

The 8 guarded decls are exactly the "seam residue" declarations the flagship rests on
(the precompile-self facts, the clean-halt run/landing extractors, the sload sim brick).
No `#print axioms` guard covers any `RealisabilitySpec.lean` decl BY DESIGN (:3867-3872):
each sorry carries `sorryAx`, so guards would only pin the debt's existence; they migrate
here obligation-by-obligation as sorries land.

---

## Section 2: internal sub-DAG + entry/exit edges

### Entry edges (imports INTO this cluster)

`RealisabilitySpec.lean` imports (`:1-3`):
- **`LirLean.V2.Drive.Headline`** — pulls in the whole cyclic drive spine: `runWithLog`,
  `runWithLog_drive`, `runs_of_drive_ok`, `driveLog`, `Runs`, `RunFrom`, `RunStmts`,
  `EvalStmt`, `Corr`, `CleanHaltsNonException`, `SelfPresent`, `lower_modellable`,
  `cleanHalts_of_runWithLog`, `materialise_runs_of_cleanHalt`,
  `jump/branch_landing_of_cleanHalt`, `callPreservesSelf_modGuards`, `stepPreservesSelf`,
  `selfPresent_runs`, `evmCallOracle`, the SSTORE/GAS/SLOAD `stepFrame_*` inversions,
  `Lir.CallRealises` (the def `CallRealisesS` copies), `Lir.StepScoped`/`DefsSound`/
  `NonRecomputable`/`defsOf`/`chargeOf`/`materialise`. This is the L1–L6 machinery.
- **`LirLean.Acyclic`** — `Lir.Acyclic`, `Lir.AcyclicWellFormed`, `Lir.WellFormedLowered`
  (used only by the §6 `exProg` witness well-formedness chain).
- **`LirLean.BoundaryReach`** — `AtReachableBoundary`, `reachable_boundary_loweringByte`,
  `reachesBoundary_of_mem_validJumpDests`, `reachesBoundary_nextInstr`, `flatBytes`,
  `lower_eq_flatBytes` (used only by the R6 geometry track, §5).

`Audit.lean` imports (`:1-6`): `LowerConforms`, `LowerDecode`, `MaterialiseCleanHalt`,
`V2.DriveSim`, `V2.Drive.CallPreservesSelf`, `Spec.Seams` — the modules whose decls it
guards. It adds no decls of its own.

### Exit edges (imports OUT of this cluster)

- `RealisabilitySpec.lean`: **NONE.** Nothing imports it (`grep -rn` confirms only
  docstring mentions). It is the terminal node of the whole LirLean DAG — the sole root of
  the `WIP` lean_lib (`lakefile.lean:31-32`).
- `Audit.lean`: imported by exactly one module — the `LirLean` root (`LirLean.lean:53`,
  "MUST stay last"). It is the terminal node of the default `LirLean` build cone.

### Internal sub-DAG (data-flow spine of `RealisabilitySpec.lean`)

```
§1 statics: WellLowered {wf,defs,defsCons,entry0,closed,stack,gasBound,slotAddr,
            retEpilogueBound,noSlotSource}  +  PrecompileAssumptions {noErase,callsCode}
            +  entryState  +  RunLog.clean  ──────────────► flagship hypothesis surface
                 │
   ClosedCFG ──► present_of_closed (R8)
   DefsConsistent + invalStep + DefsSoundS ──► defsSoundS_preserved_step (R0b)
                                                    │ (gates the sim-spine reshape, cross-file)
§2 RecorderCoupled ──► DriveCorrLog (walk invariant)
        │                    ▲
        │   R7 edges: recorderCoupled_{entry,step_gas,sload,step_other,call,
        │             call_extract,stepsTo_other}  (all PROVED)  ── preserve ─┘
        │             built on driveLog_acc_hom (linchpin)
        ▼
§3 StmtTies' / TermTies'  ◄── built by ── stmtTies'_of_runWithLog (R10a, SORRY)
                                          termTies'_of_runWithLog (R10b) ◄ termTies'_of_walk (R5)
§4 RunFromLeft/RunFromAll ◄── runFrom_of_runFromLeft, runFromLeft_exists (adequacy, PROVED)
§5 R6: atReachableBoundaryVJ_{entry,step*,call*}  ─► ..._of_runs ─► runs_atReachableBoundary (hrb)
       R2: haltNonException_of_cleanLog ;  R3: callRealises_of_recorded (SORRY, Piece A landed)
§6 exProg ──► ~20 witness lemmas ──► wellLowered_exProg ──► wellLowered_check_exists (R9)
                                                        └──► exProg_satisfies_hypotheses (R12a, SORRY)

          ┌──────────────────────── THE BLOCKER (does not exist) ────────────────────────┐
          │ runFrom_of_driveCorrLog : walks DriveCorrLog across F2, instantiating R7 edges │
          │ + R6 hrb + R2 + R3 + R10 ties, yields RunFrom + terminal world eq + hrb        │
          └───────────────────────────────────┬───────────────────────────────────────────┘
                                               ▼
   conforms_of_worldeq (CLOSED) ──► lower_conforms / _exact / _gasfree (R11, SORRY)
                                               ▼
                                    exProg_nonvacuity (R12b, assembled)
```

The R7 edge family, R6 walk, R2, R5, R8, R9, R10b, and `conforms_of_worldeq` are all the
closed "spokes"; the missing hub `runFrom_of_driveCorrLog` is the one thing that consumes
`DriveCorrLog` + the ties + the R7 edges to produce the flagship's `RunFrom`. It is the
single central blocker.

---

## Section 3: SIMPLIFICATION CANDIDATES (evidence-backed only)

### S1. Split the §6 `exProg` witness (~640 LOC) into its own file — DEFENSIBLE (reorg)

Evidence: `exProg` (:2975) through `wellLowered_check_exists` (:3613) is a self-contained
block of ~20 `private` witness lemmas plus 2 exported R9 theorems. Its only exits to the
rest of the file are `wellLowered_exProg` (→ `wellLowered_check_exists`, `exProg_nonvacuity`)
and `exProg` itself (→ R12). Everything else (`exBlk*`, `blockAt_exProg*`, `rankExProg`,
the 8 `*_exProg` field lemmas) is `private` and referenced only within the block. Extracting
`§6` into e.g. `V2/RealisabilitySpecWitness.lean` (imported back) is a pure relocation that
would cut the flagship file roughly in half. Grounding-aligned
(`docs/lirlean-dag-2026-07-04.md:174-193`). Reorg, not deletion.

### S2. Factor the shared "terminal identification" prologue — DEFENSIBLE (internal dedup)

Evidence: `haltNonException_of_cleanLog` (:1249-1263) and `conforms_of_worldeq`
(:3671-3685) open with a byte-for-byte identical ~13-line block: `runWithLog_drive hrun` →
`rw [hbegin] at hbc` → `hfeq : frame = fr₀` → `rw [hfeq] at hdrive` →
`runs_of_drive_ok … (lower_modellable hrb hcc)` → uniqueness via `runs_halt_eq` +
`Runs.linear_to_halt` → `Signal.halted.injEq`. A shared lemma
`terminal_of_runWithLog : … → ∃ last₀ halt₀, Runs fr₀ last₀ ∧ stepFrame last₀ = .halted
halt₀ ∧ log.observable = endFrame last₀ halt₀` would eliminate the duplication in both.
Local, safe, no semantic change.

### S3. `CallRealisesS` vs in-tree `Lir.CallRealises` — KNOWN dedup, cross-file, NOT now

Evidence: `CallRealisesS` (:406) is a deliberate near-verbatim copy of `Lir.CallRealises`
(`LowerConforms.lean:261`) with one conjunct swapped (`StepScoped`→`StepScopedS`). The
docstring (:403-405) itself flags this as "recorded Phase-3 unification debt: the R0b
reshape re-plumbs `sim_call_stmt`'s input to this form and retires the in-tree original."
This is real duplication with a NAMED resolution, but it spans the default target (which
this WIP track does not edit) and is gated on R0b landing. **Needs confirmation** at R0b
time; do not delete now.

### S4. Things that LOOK dead but are NOT (do NOT simplify)

- `runFrom_of_runFromLeft`/`runFromLeft_exists` (:1017/:1029), the R7 edge family
  (:2474-2941), `sstoreRealises_at_frame` (R4), `defsSoundS_preserved_step` (R0b),
  `resumeAfterCall_*` (R3 pins), `gas_suffix_head_realised`, `present_of_closed` (R8),
  `haltNonException_of_cleanLog` (R2): all PROVED, all "no callers yet" — but each is an
  incremental spoke whose consumer is the not-yet-written `runFrom_of_driveCorrLog` hub or
  the R10 assembly. Classifying any as dead would repeat the shallow-pass error.
- `emptyProg`/`emptyParams`/`not_runs_atReachableBoundary`/`not_defsSound_stale`: look like
  unused scaffolding but are PROVED refutations that justify live side conditions (`hne`,
  R0b). Deleting them removes the anti-vacuity/soundness evidence. Keep.
- The `obs`/phantom `0` parameter threaded through `DriveCorrLog.corr` and every
  `StmtTies'` arm: docstrings (:617-618, :655) mark it audit-confirmed unused and slated
  for deletion in the Phase-3 reshape, but it lives in `Corr` (a default-target def), so it
  is NOT this file's edit surface. Cross-file, needs confirmation.

### S5. `Audit.lean` — no decl-level simplification

It is a pure guard file. Its header (:15-24) is current (documents the 2026-07-03 vacuous-
surface removal). The one forward-looking item is that the flagship signature `#check`
freeze should be ADDED here once R11 lands (:22-24) — an addition, not a simplification.
