# exp005 LirLean — incremental-vs-dead re-classification (2026-07-04)

Corrects the prior shallow "unimported ⇒ dead" pass. Every decl the cluster deep-dives
flagged as unimported / no-callers / scaffold / superseded is re-classified with evidence:

- **A — genuinely superseded**: a replacement is named AND the old need is demonstrably gone.
  Removal candidate (delete the old, keep the replacement).
- **B — incremental toward an OPEN goal**: proven/scaffolded, no caller yet, but a named
  open sorry-leaf / planned feature / flagship obligation will consume it. NOT removable.
- **C — intentional reviewer/audit/anti-vacuity infrastructure**: deliberately kept though
  code-unreferenced (seam register, tombstone, lesson-witnesses, refutations). NOT removable.
- **D — truly abandoned**: zero refs repo-wide AND connects to nothing planned. Removal candidate.

Only **A** and **D** are removal candidates. Spot-verified by repo-wide `grep -rn … LirLean/`
(comment/docstring lines discounted). When unsure → B.

## Removal candidates (A + D)

| decl | file:line | cluster | cat | evidence (replacement / zero-ref) | removal-safe? |
|---|---|---|---|---|---|
| `IRConf` | SmallStep.lean:69 | v1bricks | **D** | grep: only its own def line; connects to nothing planned | YES |
| `Program.stmtAt` | SmallStep.lean:127 | v1bricks | **D** | grep: only its own def line | YES |
| `Lir.lower_conforms` (acyclic capstone, ~63 LOC) | LowerConforms.lean:1188 | assembly | **A** | replaced by flagship `V2.lower_conforms` (RealisabilitySpec:3705) + default-build `lower_conforms_cyclic`; grep finds only its def + module-header prose, zero theorem callers | YES |
| `runWithLog_messageCall` | RecorderLemmas.lean:143 | assembly | **A** | sole caller is the dead capstone (LowerConforms:1238); live path uses `runWithLog_drive` | YES — **only together with the capstone** |
| `messageCall_runs` (feeder of capstone) | LowerConforms (capstone body) | assembly | **A** | same: only in the capstone chain | YES — with capstone |
| `assign_sload_sub_key` | LowerDecode.lean:68 | assembly | **A** | never wired; sload arm derives its key segment inline via `MatSeg`/`hsegk` (sim_assign_sload_lowered:1467) + `decode_sloadstash`; grep = only its def | YES |
| `realisedCall_projection` | V2/Drive/SelfPresent.lean:55 | v2spine | **A** | body is literally `realisedCall_cons self hc`; flagship uses `realisedCall_cons` directly (RS:2856); grep = def + docstring | YES |
| `chargeOf_imm_const` | MaterialiseGas.lean:141 | materialise | **A** | PUSH32-width-stability already delivered structurally by `chargeOf_imm`; grep = def + one docstring backref (:63) | YES (or keep as doc) |
| `RunAcc` (type alias) | Spec/Recorder.lean:113 | spec | **A** | superseded by three positional args (gasAcc/sloadAcc/callAcc) threaded by `driveLog`; grep = def + stale docstring (:154, itself wrong "2-tuple") | YES — needs-confirm not reserved for a planned re-bundling |
| `sim_stmts` (block-from-pc alias) | SimStmts.lean:132 | sim | **A** | pure alias `:= sim_stmts_drop …`; consumed form `sim_stmts_block` re-derives from `sim_stmts_drop` directly (:158); grep = only its def | needs-confirm (docstring bills it as plan-facing headline) |
| `mload_after_mstore` | Engine/MemAlgebra.lean:459 | engine | **A** | grow-aware `mstore_reads_back` (:713, no pre-size premise) is what `SimStmt` consumes; grep = def + header prose + axiom guard | needs-confirm (helpers copySlice_size/readWithPadding_written stay) |
| `Match` (invariant structure) | Match.lean:125 | v1bricks | **A** | replaced by `Corr` (SimStmt:103); grep `.storage_eq`/`Match.mk`/`: Match` all EMPTY — never instantiated, no field ever read | YES (but part of "v1 reference layer" — confirm layer retirement) |
| `lower_preserves_discharge` / `_stop` / `_ret` | Match.lean:550/562/577 | v1bricks | **A** | live discharge is `SimTerm.sim_term_halt_*` + LowerConforms; grep = mutually-internal only, zero external (not even dead capstone) | YES (v1-layer scoping) |
| v1 semantics: `IRState`(:49) `IRHalt`(:60) `evalExpr`(:89) `setLocal`(:101) `setStorage`(:117) `bindCallResult`(:110) | SmallStep.lean | v1bricks | **A** | each has a live V2 twin the flagship rides (`V2.IRState`:48 / `V2.IRHalt`:55 / `V2.evalExpr`:123 / `V2.IRState.setLocal`:104 / `.setStorage`:108); v1 originals appear only in Match docstrings; `bindCallResult` never called | needs-confirm (deliberate "v1 reference small-step" — deletion is a layer-scoping decision, not silent) |
| `IRState.applyCall` | Call.lean:158 | v1bricks | **A** | v1-IRState-coupled; v2 threads call effect via `callSuccessFlag`+`CallRealises`; docstrings only | needs-confirm (v1-layer scoping) |
| acyclic-CFG construction: `CFGAcyclic`(:225) `TermRankLt`(:205) `Term.succs`(:212) `runFrom_exists{,_stop,_ret}`(:292/139/149) `irRun_exists{,_stop,_ret}`(:341/162/174) | V2/IRRun.lean | v2spine | **A** | DriveSim's dynamic `totalGas` measure explicitly "retires" the static block-rank (DriveSim:17,54); grep = self-internal + DriveSim docstrings only, zero code callers outside IRRun | YES (~150 LOC). KEEP the definability fold `StmtDefinable/StmtsDefinable/stmtPost/stmtsPost/runStmts_exists` (still cited — see B) |
| `lower_conforms_cyclic'` | V2/DriveSim.lean:666 | v2spine | **A** | flagship (RS:3730-3736) explicitly refuses to cite it — its unconditional all-frames `SimStmtStep` is unsatisfiable under reshaped `StmtTies'`; grep = def + docstrings, zero callers | YES (the single safest DriveSim removal) |

## decode-anchor push twins — superseded-but-symmetric (A / needs-confirm)

| decl | file:line | cluster | cat | evidence | removal-safe? |
|---|---|---|---|---|---|
| `decode_at_stmt_head_nonpush` | DecodeAnchors.lean:195 | decode | A? | PUSH duties done by MatSeg path (matSeg_of_stmt:432, imm_leaf_decode, slot_leaf_decode) built on `flatBytes_at_pcOf_offset`+`decode_lower_push`; grep = only its def | needs-confirm (A1/A2/A3 symmetric completeness API; nonpush twins ARE live) |
| `decode_at_stmt_head_push` | DecodeAnchors.lean:215 | decode | A? | same | needs-confirm |
| `decode_at_offset_push` | DecodeAnchors.lean:257 | decode | A? | same; live sibling `decode_at_offset_nonpush`(:241) used in LowerDecode | needs-confirm |
| `SegAlignedSafe.toSegAligned` / `SegAlignedLowering.toSegAligned` | NoCreateBytes:59 / BoundaryReach:144 | decode | A? | unused forgetful maps; vanish automatically under the C1 SegAligned-tower dedup | needs-confirm (tiny; tie to the tower dedup) |

## Incremental toward an OPEN goal (B) — NOT removable

| decl(s) | file:line | cluster | open goal it feeds | evidence |
|---|---|---|---|---|
| `CreateOracle` `createAddrOrZero` `evmCreateOracle` `evmCreateOracle_addressWord_eq` | Create.lean:64/75/99/107 | v1bricks | first-class CREATE (Phase 3.5) | exact twin of load-bearing `evmCallOracle`; roadmap (execution-plan:121-131, target-arch:182-194) names Create.lean as an INPUT |
| `DescentKind` `callDescent` `createDescent` `DescentReturns` `descentReturns_call_iff` `DescendImmediateNoErase` `createDescent_descendImmediate_trivial` | Descent.lean:421-567 | engine | first-class CREATE | docstring :400-416 + roadmap; CALL/CREATE unified via one interface; scaffold-experimental by design |
| `decode_reachable_boundary_loweringOp`(:415) `reachesBoundary_of_mem_validJumpDests`(:90) `reachesBoundary_nextInstr`(:109) `IsLoweringOp`(:125) `reachable_boundary_loweringByte`(:402) | BoundaryReach.lean | decode | R6 `runs_atReachableBoundary` (RS:2456, **open leaf**) | header (:26-33) says consuming Runs-induction "not yet landed"; byte-level twin already cited by RS R6 geometry |
| `stash_tail_runs_covered` | StashTail.lean:256 | materialise | Phase-C cached-SLOAD reuse (named at SimStmt:1076) | no caller yet; the covered-slot second read is not yet wired |
| `callRealises_bridge` | V2/CallRealises.lean:85 | v2spine | R3 `callRealises_of_recorded` (RS:1364, **open leaf**) | RecorderLemmas:41 docstring names it as the tie R3's head uses; its sibling `evmV2CallEntry` IS live (RS:2856) |
| `Loc`(:92) `Alloc`(:101) `Loc.toDef`(:105) `locOfExpr`(:269) `toDef_locOfExpr`(LoweringLemmas:85) | Spec/Lowering.lean | spec/decode | Phase-D `∀ SoundAlloc` headline | bottom out at keystone `allocate_toDefs` (the Phase-A no-behaviour-change bridge → DecodeLower:56) |
| `realisedSload`(:285) `isSloadOp`(:135) `sloadWarmthOf`(:144) | Spec/Recorder.lean | spec | deferred sload per-cursor tie (SelfPresent:233) | parallel to the fully-live GAS channel; alignment deferred by design |
| whole file: `DriveCorrPlus`(:81) `memRealises_setLocal_nonspilled` `driveCorrPlus_*` `FramesRun.snoc_seed` `gasLogAligned_step_gas_seed` `GasReach` `GasCursorClass` | V2/Drive/Headline.lean | v2spine | R0 reshape / S2/S3/S7 channels | header (:17-25): "RETAINED as green machinery the R0 reshape starts from"; **highest roadmap-risk file — flag for confirmation** |
| `GasLogAligned`/`SloadLogAligned` + step/read lemmas (§3-§4) | V2/Drive/SelfPresent.lean:109-330 | v2spine | deferred gas/sload selection channel | `-- RETAINED for Phase 3 realisability closure` markers; consumed only by Headline (itself B) |
| builder path: `simStmtStep_block`(:374) `simTermStep_block`(:833) `simTermStep_{stop,ret,jump,branch}` `simStmtStep_call` + 4 `sim_*_lowered` wrappers + `decode_sloadstash` `sim_assign_gas_lowered` `sim_assign_sload_lowered` | LowerConforms/LowerDecode | assembly | Phase-D general `SimStmtStep`/`SimTermStep` discharge; **also still feeds default-build `lower_conforms_cyclic` via SimStmtStep/SimTermStep** | tops have zero callers but the abstractions they build ARE consumed by DriveSim cyclic path |
| definability fold: `StmtDefinable`(:61) `StmtsDefinable`(:106) `stmtPost`(:69) `stmtsPost`(:112) `runStmts_exists`(:119) `RunDefinable`(:258) | V2/IRRun.lean | v2spine | DriveSim per-block bricks; inspired flagship `StmtDefinableG` | `stmtsPost`/`stmtPost` load-bearing across all DriveSim `drive_step_block_*`; `RunDefinable`/`StmtDefinable` superseded-for-flagship (by *G variants) but still cited by cyclic path — keep until cyclic path retired |
| measure infra: `DriveCorr`(:87) `driveCorr_measure`(:97) `totalGas_succ_lt`(:196) `jumpdestFrame_gas{ToNat,_lt}` | V2/DriveSim.lean | v2spine | `runFrom_of_driveCorrLog` (the flagship's single missing hub) reuses the `totalGas` measure | grounding: flagship's log-indexed recursion reuses this measure |
| `drive_step_block_{stop,ret,jump,branch}`(:226-382) `DriveStep`(:461) `driveStep_of_block`(:495) `runFrom_of_driveCorr`(:588) `lower_conforms_cyclic`(:624) | V2/DriveSim.lean | v2spine | reshape template for `runFrom_of_driveCorrLog`; `lower_conforms_cyclic` still feeds the default-build cyclic headline | live-but-superseded reference skeleton — needs-confirm as reshape template before removal |
| Descent inversion feeders `callArm_needsCall_inv` `systemOp_needsCall_inv` (+CREATE twins) | Descent.lean:97-243 | engine | building blocks of load-bearing `stepFrame_needs{Call,Create}_inv` | reach flagship via DriveMono→CallPreservesSelf→SelfPresent |
| PROVED flagship spokes: R7 edges (:2474-2941), `haltNonException_of_cleanLog`(R2,:1240), `sstoreRealises_at_frame`(R4,:1396), `termTies'_of_walk`(R5,:1469), `present_of_closed`(R8,:2947), `defsSoundS_preserved_step`(R0b,:1110), `resumeAfterCall_{code,validJumps,pc,stack}`(R3 pins,:1300-1313), `gas_suffix_head_realised`(:2584), `recorderCoupled_call_extract`(R3-PieceA,:2858), `runFrom_of_runFromLeft`/`runFromLeft_exists`(:1017/1029), `RunFromLeft`/`RunFromAll`, `DriveCorrLog`(:629), `StmtTies'`/`TermTies'`, `CallRealisesS`, `WellLowered` field discharges | V2/RealisabilitySpec.lean | flagship | the not-yet-written hub `runFrom_of_driveCorrLog` + R10/R11 assembly | each is a spoke whose consumer is the missing hub; classifying any dead repeats the shallow error |
| the 11 open sorry leaves (R3 :1385, R6 :2343/2351/2380/2383, R10a :3634, R11 :3746/3780/3817, :3828, R12a :3843) | V2/RealisabilitySpec.lean | flagship | THE goals themselves | statements real, proofs are tracked debt |
| `IRRun` top-level wrapper (:275) | Spec/Semantics.lean | spec | top-level IR-run entry (ir-design-v2 §4) | 6 refs; incremental |

## Intentional reviewer / audit / anti-vacuity infrastructure (C) — NOT removable

| decl(s) | file:line | cluster | why kept |
|---|---|---|---|
| `Spec/Conformance.lean` (24-line tombstone, zero decls) | Spec/Conformance.lean | spec | deliberate stub kept live via LirLean.lean:50 so the canonical conformance path resolves to an honest notice (old vacuous headline deleted 2026-07-03) |
| Seam register `SelfPresent`(:38) `CallsCode`(:81) `CleanHaltsNonException`(:93) `CallPreservesSelf`(:47) `PrecompilesPreservePresence`(:59) `callPreservesSelf_of_precompiles`(:68) | Spec/Seams.lean | spec | the deliberate typed seam register (names/types/drift-proofs the debt); imported by Audit.lean; `callPreservesSelf_of_precompiles` is axiom-checked at Audit:60/62 |
| `Audit.lean` (8 `#print axioms` guards, zero decls) | Audit.lean | flagship | freezes the seam-residue axiom footprint; MUST stay last import (LirLean.lean:53) |
| `GasRealises`(:536) `SloadRealises`(:557) + witnesses `gasRealises_obs_of_witness` `sloadRealises_charge_of_witness` | MaterialiseRuns / SelfPresent | materialise/v2spine | RETIRED universals kept as regression/lesson witnesses of the unsatisfiability finding that motivated the spill pivot (gas-decision.md); defensible move is RELOCATION, not deletion |
| refutations `not_runs_atReachableBoundary`(:2232) `not_defsSound_stale`(:3166) `emptyProg`/`emptyParams`/`staleSt` | V2/RealisabilitySpec.lean | flagship | PROVED refutations justifying live side-conditions (`hne`, R0b); deleting removes the anti-vacuity/soundness evidence |
| `exProg` witness + ~20 `*_exProg` lemmas + `wellLowered_exProg`/`wellLowered_check_exists` | V2/RealisabilitySpec.lean:2959-3623 | flagship | the machine-checked anti-vacuity spine (R9/R12); exercises gas+sload+sstore+call+cycle. (S1 split into its own file is a defensible reorg, not deletion) |
| `V2/Call.lean` worked example (`callBlock`/`callIR`/`call_IRRun`/`call_IRRun_unique`) | V2/Call.lean | v2spine | self-contained anti-vacuity demonstration of the §7 call channel; `callIR` cited in DefsSound:124 docstring |
| `cleanHalts_of_runWithLog` | V2/DriveSim.lean:141 | v2spine | axiom-checked entry-scope grounding (Audit:37, Seams:89); intentionally NOT a live flagship proof dependency |
| Law determinism ladder `EvalStmt.det`/`RunStmts.det`/`RunFrom.det`/`IRRun.det` | V2/Law.lean | v2spine | realises the §4 uniqueness headline; only live consumer is the Call.lean worked example |

## Flagged-but-not-removal-candidates (keep as-is; noted to pre-empt a shallow cut)

| decl | file:line | note |
|---|---|---|
| `AccMono` | Engine/AccountMap.lean:107 | vestigial abbrev (transport always written raw) BUT it is the return type of live `accMono_of_accounts_eq`/`accMono_emptySwap` — harmless one-liner, flag not delete |
| `resumeAfterCall_mload`(:85) + feeders `resumeAfterCall_memory`(:58)/`_activeWords`(:69) | Engine/MemAlgebra.lean | zero consumers; EITHER superseded (memory-across-CALL now via MemRealises/StashTail) OR prepared-not-yet-wired (~40 LOC). needs-confirmation which — do NOT assume dead |
| `entry_storageAgree_codeFrame` | LowerConforms.lean:1089 | orphan `w₀` choice; `entry_corr` takes `hstore` as hyp instead. needs-confirm it is not the flagship's intended R7 entry-world supply |
| `jump_landing_of_cleanHalt`(:486) / `branch_landing_of_cleanHalt`(:769) | LowerDecode.lean | vestigial deleted-`Plus`-thread scaffolding; flagship re-derives inline (~RS:1741-1899). Green + Audit-guarded. Strongest dedup target BUT confirm flagship won't factor them back out — do not delete blind |
| three SegAligned towers (JumpValid/NoCreateBytes/BoundaryReach, ~1379 LOC) | decode | parameterized TRIPLICATION (dedup target ~1400→600), NOT supersession — all three headlines LIVE; this is a refactor lever, not a removal |

## Net removal-safe summary

- **Delete now (D + clearly-A, zero risk):** `IRConf`, `Program.stmtAt` (D); `Lir.lower_conforms`
  capstone + `runWithLog_messageCall`/`messageCall_runs` (together); `assign_sload_sub_key`;
  `realisedCall_projection`; `chargeOf_imm_const`; `lower_conforms_cyclic'`; IRRun acyclic-CFG
  block (`CFGAcyclic`/`TermRankLt`/`Term.succs`/`runFrom_exists*`/`irRun_exists*`); `Match` struct.
- **A but confirm layer/plan first:** v1 reference semantics group (SmallStep `IRState`/`evalExpr`/…,
  `Match.lower_preserves_*`, `Call.IRState.applyCall`) — deletion is a v1-reference-layer scoping
  decision; `RunAcc`, `sim_stmts` alias, `mload_after_mstore`, decode push-twins — confirm no
  planned re-bundling / symmetric-API intent.
- **Never remove:** everything in B (feeds an open sorry-leaf or a settled planned feature) and C
  (reviewer/audit/anti-vacuity infra). The "delete Acyclic → drop the engine" hope is false: the
  L4 sim tower and Engine cluster are SHARED by the cyclic flagship.
