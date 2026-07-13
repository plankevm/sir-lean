# LirLean — the authoritative dependency DAG + proof-plan understanding

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Date: 2026-07-04. **Supersedes the earlier shallow draft of this file.** This is a synthesis of
the `docs/deepdive-2026-07-04/` cluster reports (spec, engine, decode, materialise, v1bricks,
sim, assembly, v2spine, flagship), the `docs/eval-2026-07-04/` eval docs, `00-proof-plan.md`,
and spot-verification against the Lean on `main` (the `foundation` lineage: `800709f`, `5abdfee`
merge, `1c77c07` call-stream, `4628201` full-observable). 51 `LirLean/*.lean` files, ~25.5k LOC.
Every claim cites `file:line`. **When a docstring/header contradicts this doc, the Lean on disk
wins** — several in-tree headers are stale (flagged inline).

> **P9 status note (2026-07-08).** This DAG predates the P8/P9 well-formedness and legacy-deletion
> cleanup. Its claims
> that `Acyclic.lean`, `MatFueled`, `AcyclicWellFormed`, or `wellFormedLowered_of_acyclic` are
> live through the flagship witness are historical. The current public theorem surface is
> `IRWellFormed` + `codeFits` + `stackFits`; `WellFormedLowered`/`WellLowered` are internal
> adapters. The residual fuel/materialisation stack (`Expr.slot`, `materialiseExpr`,
> `materialise`, `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`, and `NoSlotSource`) has
> been deleted; old references below are preserved as dated provenance.

The word **"dead"** is used only for the two grep-verified zero-reference decls
(`SmallStep.IRConf`, `SmallStep.Program.stmtAt`) and the one genuinely-superseded capstone
theorem (`Lir.lower_conforms`). Everything else that "has no callers" is classified precisely as
**terminal-for-flagship**, **incremental-toward-X** (a named open goal), **shared-infra**,
**intentional-stub**, or **regression-witness** — see §2 and §6.

---

## TL;DR

- The tree is **one flagship in progress** — `Lir.lower_conforms`
  (`RealisabilitySpec.lean:3705`, cyclic + gas-free, the **only** sorry-carrier) — standing on
  **one shared, layered substrate**, plus **one dead legacy capstone** (`Lir.lower_conforms`,
  `LowerConforms.lean:1188`, the retired "acyclic headline", now unreferenced code).
- The "delete the acyclic path → drop ~6k LOC" hope is **not real**: the gas-aware per-block
  simulation engine (`SimStmt`/`SimTerm`/`Match`/`Materialise*`) is **shared by the cyclic
  flagship** through `DriveSim`'s `sim_cfg` walk. Dropping the acyclic path is a ~300-LOC
  dead-code + relocation refactor; its payoff is conceptual (one headline, not two).
- **11 open `sorry` bodies** across **9 sorry-carrying theorems** in `RealisabilitySpec.lean`,
  reducing to the two genuinely-hard leaves **R3** (call realisation) and **R6** (boundary walk),
  plus assembly leaves (R10a, R11×3, `realisedGas_nil`, R12a) all gated on one missing hub
  `runFrom_of_driveCorrLog`.
- Biggest real LOC win: the **triple-duplicated SegAligned tower**
  (JumpValid/NoCreateBytes/BoundaryReach, ~1400→~600). Biggest structural win: **split
  `RealisabilitySpec` §6 exProg witness** (~640 LOC) into its own file.

---

## 1. The layered DAG (altitude-ordered, bottom = no LirLean deps)

The organizing principle is **altitude, not feature**. `Engine/`, `Decode`, `Materialise`,
`Sim`, `CfgSim`, `V2`, `Drive` are altitude bands; `Spec/` is NOT a single band (see the
warning below). Arrows point **downward-imports** (`A ← B` = B imports A).

```
 L0  Spec CORE  (reviewer-facing DEFINITIONS; import only Evm + Spec/IR)
       Spec/IR ──┬── Spec/Semantics       (V2 IR operational semantics + observables)
                 └── Spec/Lowering         (lowering fn flatBytes; Loc/Alloc policy layer)
                          │
 L1  Engine/  (IR-AGNOSTIC frame-level EVM theory over exp003 Frame/Runs — bound for exp003)
       AccountMap ← StepWalk ← Descent ← DriveMono       (one 4-file chain)
       MemAlgebra ;  CleanHalt ;  Charges ;  DriveRuns    (four independent leaves)
                          │      (ZERO IR/Spec/V2 imports; "Engine" is an altitude grouping,
                          │       NOT a dependency component — no incoming cross-cluster edges)
 L2  DECODE / pc-offset / control-flow validity  (bytes ↔ IR positions)
       LoweringLemmas ← DecodeLower ← Layout ← DecodeAnchors
                              └→ JumpValid ← NoCreateBytes ← BoundaryReach   [SegAligned tower ×3]
                          │
 L3  MATERIALISE (spill/recompute VALUE channel) + v1 small-step + CALL/CREATE bricks
       SmallStep ← Call, Create ;  StorageErase ;  Match ;  DefsSound
       MaterialiseGas ← MaterialiseRuns ← MatDecLower, MaterialiseCleanHalt, StashTail
                          │
 L4  Per-block gas-aware SIMULATION engine  (the "Corr" bricks; the big grind)
       SimStmt ← SimStmts ← SimTerm ;   CleanHaltExtract (sibling root, feeds SimStmt via
                          │              MaterialiseCleanHalt)
 L5  CFG ASSEMBLY
       LowerDecode  (block-walk bricks: sim_stmts_block, sim_term_*)
      LowerConforms  (sim_cfg :970 + SimTermStep :96 + WellFormedLowered :143 = LIVE;
                       + DEAD acyclic capstone Lir.lower_conforms :1188)
      Acyclic  (deleted by P9; historical generic-defs fuel/rank core)
                          │
 L6  V2 gas-free SPINE + cyclic DRIVE
       Law ; IRRun ; Call ← CallRealises ; Decode/Modellable
       DriveSim (imports LowerConforms for sim_cfg — the cyclic path)
       Drive/{SelfPresent ← CallPreservesSelf, Headline}
       Spec/Recorder, Spec/Seams  ← (HIGH-altitude Spec files, see warning)
       RecorderLemmas
                          │
 L7  FLAGSHIP + audit
       RealisabilitySpec  (WIP lib; R0–R12 + flagship + exProg; the ONLY sorry-carrier)
       Audit  (#guard_msgs axiom/signature guard net; imported LAST; terminal of DEFAULT cone)
```

> **CRITICAL WARNING — `Spec/` is NOT one altitude band.** `Spec/IR`, `Spec/Semantics`,
> `Spec/Lowering` are true L0 base (import only `Evm` + `Spec/IR`). But **`Spec/Recorder`** imports
> `CallRealises` + `Hoare.GasMonotone`, and **`Spec/Seams`** imports
> `Drive/CallPreservesSelf` + `Decode/Modellable` + `BytecodeLayer/Hoare/CleanHalt` — both sit **HIGH** (L6) in
> the DAG despite living under `Spec/`. They live in `Spec/` for their reviewer-surface *role*,
> not their altitude. **`Spec/Conformance`** (imported at `LirLean.lean:50`) is a 24-line
> tombstone stub with zero decls. The only intra-Spec base edges are IR→Semantics and IR→Lowering.

**Engine is 4 leaves + 1 chain, not a component.** `Charges`, `MemAlgebra`, `CleanHalt`,
`DriveRuns` are independent leaves; `AccountMap→StepWalk→Descent→DriveMono` is the only chain.
Every Engine file imports ONLY exp003 (`Evm`, `BytecodeLayer.*`) or a sibling Engine file — zero
`LirLean.Spec/IR` imports (`AccountMap.lean:1-2`, `StepWalk.lean:1-2`, `DriveRuns.lean:37`).
There are **no incoming edges from other clusters into Engine at the import level**.

---

## 2. Per-file one-liners (with CORRECTED roles)

Role vocabulary: **terminal-for-flagship** (feeds `Lir.lower_conforms` on the live path),
**shared-infra** (feeds both cyclic path and flagship), **incremental-toward-X** (proven, no
consumer yet, targets a named open goal X), **intentional-stub/register** (exists to name debt),
**regression-witness** (deliberately-retained unsatisfiability lesson), **superseded** (has a
live replacement), **DEAD** (grep-zero, no purpose).

### L0 — Spec core

| File | LOC | Role · why it exists |
|---|---|---|
| Spec/IR | 114 | **terminal.** IR datatypes. `Stmt` = assign/sstore/call/create. P9 deleted the old `Expr.slot` uniform-spill marker; spill placement now lives in `Loc`. Root of everything. |
| Spec/Semantics | 278 | **terminal.** V2 IR operational semantics: `RunFrom` (`:228`, 137 refs), `evalExpr` (`:123`), `blockAt` (`:139`, v2-local twin of `SmallStep.Program.blockAt`). *Stale self-desc "call-free prototype" (:5).* |
| Spec/Lowering | 358 | **terminal.** Lowering fn (`lower` :358); `defEnv`/`defsOf` route non-recomputable temps to `Loc.slot`; `matCache` is the fold-based value channel; `emitStmt` (`:266-290`) emits assign/sstore/call/create. The old `Expr.slot`/fuel materialisation path was deleted by P9. |
| Spec/Recorder | 358 | **terminal** (HIGH altitude — imports CallRealises). Recording interpreter: `observe` (`:340`), `runWithLog` (`:262`), `driveLog` (`:186`), `realisedGas` (`:285`), `realisedSload` (`:291`), `realisedCall` (`:306`), `realisedCreate` (`:321`). `RunAcc` (`:113`) = **defensible-delete candidate** (zero type uses; only historical shape comments remain). |
| Spec/Seams | 95 | **live seam vocabulary** (HIGH altitude). Owns `Lir.PrecompileAssumptions` and `ReachableFrom`; keeps `SelfPresent`/`CallPreservesSelf`/`CallsCode`/`CleanHaltsNonException` as supporting forwarders. Imported by the WIP surface and Audit. |
| Spec/Conformance | 24 | **live conformance vocabulary.** Hosts `entryState`, `RunLog.clean`, `Conforms`, and `NoGasReads`; imported by the WIP surface so the trusted spec surface can name the live theorem vocabulary. |

### L1 — Engine (IR-agnostic, exp003-bound; all 8 sorry-free + axiom-clean)

| File | LOC | Role · why it exists |
|---|---|---|
| BytecodeLayer/Hoare/AccountMap | 145 | **terminal.** Self-address-present frame lemmas. `AccMono` (`:107`) is a vestigial abbreviation (named form unused; the transport is used raw everywhere) — flag, don't delete. Self-flags `-- RELOCATE to exp003` (`:26/:55/:68`). |
| BytecodeLayer/Hoare/StepWalk | 1336 | **terminal.** Core pc/stack/memory step-walk. ~30 per-family `_next_accMono` arms (`:214-851`) shard one dispatch proof, assembling `dispatch_next_accMono` (`:852`); `stepFrame_next_accMono/execEnvAddr/self` + `halted_success` feed CallPreservesSelf. |
| BytecodeLayer/Hoare/Descent | 570 | **terminal + incremental-toward CREATE.** `stepFrame_needs{Call,Create}_inv` + begin/resume lemmas are LIVE (reach flagship via DriveMono→CallPreservesSelf→SelfPresent). The **DescentKind interface block** (`:421-567`: DescentKind/callDescent/createDescent/DescentReturns/…) has zero external consumers but is **first-class-CREATE scaffold by design** (docstring :400-416) — NOT dead. |
| BytecodeLayer/Hoare/DriveMono | 294 | **terminal.** `drive_accounts_find_mono` → CallPreservesSelf → SelfPresent. |
| BytecodeLayer/Hoare/MemAlgebra | 996 | **terminal.** MSTORE/MLOAD/offset algebra; slot lemmas (`mstore_preserves_slot(_grow)`, `slot_windows_disjoint`, `mstore_reads_back` :713) feed SimStmt. **Simplification candidates (confirm):** `mload_after_mstore` (`:459`, superseded by grow-aware `:713`, zero consumers) and `resumeAfterCall_mload` (`:85`) + feeders `resumeAfterCall_memory/activeWords` (`:58/:69`) — advertised Verdict cruxes (`:22`) but consumer-less (superseded or not-yet-wired ~40 LOC). Header "all three cruxes PROVED" **overstates** current role. Ships `#print axioms` guards (`:964-982`). |
| BytecodeLayer/Hoare/CleanHalt | 103 | **terminal.** `CleanHalts`/`CleanHaltsNonException`/`cleanHaltsNonException_forward` feed 9 files across sim tower + flagship. |
| BytecodeLayer/Hoare/Charges | — | **terminal.** Gas-charge primitives; `subCharges_snoc/append` feed MaterialiseGas. Header (`:11`) names nonexistent "WorkedCall" consumer — stale doc. |
| BytecodeLayer/Hoare/DriveRuns | 369 | **terminal.** `runs_of_drive_ok` (`:283`) feeds Modellable/DriveSim/RealisabilitySpec — predicated on `NoCreate`/`ModellableStep` (`:27`), the exact clause CREATE must retire. |

### L2 — Decode / control-flow validity (all 7 sorry-free + axiom-clean)

| File | LOC | Role · why it exists |
|---|---|---|
| LoweringLemmas | 139 | **terminal.** `defsOf_ne_gas/ne_sload` (`:21/:64`) load-bearing spill invariants (consumed by MaterialiseCleanHalt/Runs + RealisabilitySpec), plus `rematOf` projection twins (`:107/:116`) and `defsOf_eq_defEnv_find` (`:136`) for the post-P9 fold value channel. |
| DecodeLower | 159 | **terminal.** Decode-at-cursor; single-caller bricks (`bextract`, `decode_{non,}push_of_list`) are load-bearing internal steps. |
| Layout | 204 | **terminal.** Byte-layout offsets; single-caller length bricks are LIVE internal steps. |
| DecodeAnchors | 318 | **terminal + likely-superseded island (confirm).** nonpush anchors LIVE (LowerDecode:121/1123/1137). But `decode_at_stmt_head_{nonpush,push}` + `decode_at_offset_push` (`:195/:215/:257`) have zero callers — their PUSH duty is done by MatDecLower's MatSeg path; symmetric completeness API (~65 LOC), confirm before removal. |
| JumpValid | 516 | **terminal (SegAligned tower #1, `SegAligned` :78).** `block_offset_validJump`/`decode_at_block_offset_jumpdest` feed LowerConforms/SimTerm/RealisabilitySpec. `reaches_of_segAligned` (`:120`, reach-END, predicate-free) is DISTINCT — kept once under dedup. |
| NoCreateBytes | 431 | **terminal (SegAligned tower #2, `SegAlignedSafe` :50).** `decode_reachable_boundary_some` → Modellable:426. Could fold into tower #3 (SegAlignedLowering is strictly stronger). `toSegAligned` (`:59`) unused (dedup casualty). |
| BoundaryReach | 432 | **incremental-toward R6 (SegAligned tower #3, `SegAlignedLowering` :135).** `IsLoweringOp` (`:126-129`, all 16 ops non-CREATE), `reachable_boundary_loweringByte` (`:402`) feed R6. `decode_reachable_boundary_loweringOp` (`:415`) is incremental (header :26-33 marks the consuming induction "not yet landed"). `toSegAligned` (`:144`) unused. |

> **The three SegAligned towers are a PARAMETERIZED TRIPLICATION** (~1379 LOC, top LOC lever).
> `SegAligned`/`SegAlignedSafe`/`SegAlignedLowering` are the same inductive + emit-ladder
> differing only by a per-head predicate P (True / notCreate / IsLoweringOp). Compare
> `segAligned_emitStmt` (JumpValid:243) / `segAlignedSafe_emitStmt` (NoCreateBytes:243) /
> `segAlignedLowering_emitStmt` (BoundaryReach:282): line-for-line identical bar an extra
> `(by decide)`. Collapse into one `SegAlignedP (P)` proven once at the tightest predicate
> `IsLoweringOp`, deriving the others as `mono` corollaries → ~1400→~650 (~700-730 LOC removed).
> All 3 headlines are LIVE → this is **dedup, NOT supersession**. Risk LOW, GATE NONE.

### L3 — Materialise + v1 bricks

| File | LOC | Role · why it exists |
|---|---|---|
| SmallStep | 131 | v1 reference small-step. `Program.blockAt` (`:123`) is the ONE live decl (via Match pcOf/blockAt_of_toList). **GENUINELY DEAD:** `IRConf` (`:69`), `Program.stmtAt` (`:127`) — grep-zero repo-wide. |
| Call | 164 | **terminal.** Oracle projections LIVE: `evmCallOracle` (`:108`), `callSuccessFlag` (`:120`), `evmCallOracle_successWord_eq_x` (`:128`) → LowerConforms/SimStmt/CallRealises. Only `IRState.applyCall` (`:158`) is v1-dead. |
| Create | 110 | **incremental-toward first-class CREATE.** Imported by nobody; exact green twin of the load-bearing `evmCallOracle` (`CreateOracle` :64, `evmCreateOracle` :99). Settled roadmap keeps it — NOT dead. |
| StorageErase | 217 | **terminal.** `findD_erase_self` (`:189`)/`findD_erase_of_ne` (`:199`) discharge the zero-write SSTORE read-back (sim_sstore, Match:224/252; flagship RS:97/775). RBNode lemmas above = internal chain. |
| DefsSound | 579 | **terminal.** `WellFormed` + defs soundness (Layer B3). `callResultTmps`/`callResult` (`:143`) is a V2 concept (counting call-result tmps) — unrelated to SmallStep's v1 `IRState.callResult`. |
| Match | 595 | **terminal (shared hub).** `sim_*` bricks (imm/gas/add/lt/sload/sstore/mload/mstore/call), `pcOf` (`:66`), `selfStorage/storageAt` (`:113/:120`), `halt_stop` (`:368`), `call_reflects_lowered` (`:519`) all feed the LIVE v2 layers. **SUPERSEDED-for-flagship:** the Match STRUCTURE (`:125`) is never instantiated (replaced by `Corr`, SimStmt:103, whose same-named accessors LowerConforms/LowerDecode actually read); v1 decls (`evalExpr` :89, `IRState` :49, `IRHalt` :60, …) have live V2 twins; `lower_preserves_discharge/stop/ret` (`:550/562/577`) zero consumers. |
| MaterialiseGas | 289 | **terminal (Layer B2, LIVE on gas-free path).** B1's induction CONSUMES `gasToNat` to bound each operand's gas (MaterialiseRuns:1140/1167/…), so B2 is load-bearing for the gas-free flagship. **True orphan:** `chargeOf_imm_const` (`:141`, subsumed by `chargeOf_imm`, ~4 LOC safe delete). |
| MaterialiseRuns | 1372 | **terminal (Layer B1 hub).** `materialise_runs` (`:771`) proven TOTAL over Expr; `.gas`/`.sload` arms discharged as UNREACHABLE via `e ≠ .gas/.sload` (`:834/:840`) — via spill, NOT a warmth universal. `GasRealises`/`SloadRealises` (`:536/557`) = **regression-witnesses** (RELOCATE not delete). |
| MatDecLower | 516 | **terminal.** Materialise↔decode bridge; MatSeg operand-decode path (`matSeg_of_stmt` :432). Cross-cluster back-loop: MatDecLower→CleanHaltExtract→MaterialiseCleanHalt. |
| MaterialiseCleanHalt | 404 | **terminal.** Clean-halt of materialised runs. Covered-slot MLOAD dup vs MaterialiseRuns:896-940 is INTENTIONAL anti-cycle (B1/B2 split). |
| StashTail | 519 | **terminal + incremental.** `stash_tail_gas/sload` LIVE (LowerDecode:1234/1506); `stash_tail_runs_covered` (`:256`) incremental-toward Phase-C SLOAD-reuse (SimStmt:1076). |

### L4 — Per-block sim (all sorry-free)

| File | LOC | Role · why it exists |
|---|---|---|
| SimStmt | 1187 | **terminal + shared-infra.** `Corr` (`:103`) = the central end-to-end invariant (LowerDecode/LowerConforms/DriveSim/RealisabilitySpec/Headline). Five per-stmt arms all LIVE. `sim_call_stmt` (`:576`, "28-hyp smell") JUDGED **genuine irreducible shape lemma** — every hyp consumed, full Corr (incl. memAgree) re-established; only cosmetic bundling possible. |
| SimStmts | 163 | **terminal.** `sim_stmts_block` (`:149`) LIVE. **Simplification (confirm):** `sim_stmts` (`:132`) is a zero-caller pure alias bypassed by `sim_stmts_block`. Dangling "guard" comment at `:163` (no guard beneath). |
| SimTerm | 838 | **terminal.** Terminator arms (halt/jump/branch). Frame-accessor @[simp] families are distinct post-frame constructors — NOT duplication. |
| CleanHaltExtract | 1118 | **terminal + upstream-of-SimStmt.** clean-halt→gas/mem envelope PRODUCER. `next_*_of_cleanHalt` family called directly in flagship (RS:1415…2600); `gas/sload_envelope_of_cleanHalt` (`:696/:785`) → LowerConforms. Sits BELOW SimStmt (via MaterialiseCleanHalt) AND beside it. Header (`:41`) overstates axiom-guard coverage (file has ZERO `#print axioms`). |

### L5 — CFG assembly

| File | LOC | Role · why it exists |
|---|---|---|
| LowerDecode | 1528 | **terminal.** Block-walk bricks (`sim_stmts_block`, `sim_term_*`). **Safe-delete:** `assign_sload_sub_key` (`:68`, zero-caller never-wired twin). **Confirm-first dedup:** `jump/branch_landing_of_cleanHalt` (`:486/769`, ~410 LOC, flagship re-derives inline RS~:1741-1899; green/axiom-guarded — do not delete blind). |
| LowerConforms | 1260 | **shared-infra + DEAD capstone.** `sim_cfg` (`:970`) LIVE (DriveSim cyclic :648 + flagship); `SimTermStep` (`:96`), `WellFormedLowered` (`:143`), `CallRealises` (`:261`) shared-infra. The BUILDER path (`simStmtStep_block`/`_lowered` wrappers) has zero top callers, bypassed by the flagship — **confirm-first, not dead** (SimStmtStep/SimTermStep still feed the cyclic headline). **DEAD:** `Lir.lower_conforms` (`:1188`, ~63 LOC, zero real callers). `entry_storageAgree_codeFrame` (`:1089`) orphaned (confirm not R7 entry supply). |
| Acyclic | 225 | **deleted by P9.** Historical generic-defs fuel/rank core. After P8, `WellFormedLowered` became fuel-free over `matCache` lengths and the WIP witness went through `IRWellFormed` + `codeFits` + `stackFits` into the internal `WellLowered` adapter; P9 removed the residual rank/fuel stack. |

### L6 — V2 spine + Drive

| File | LOC | Role · why it exists |
|---|---|---|
| Law | 172 | **self-contained.** Determinism ladder (EvalStmt.det→…→IRRun.det). |
| IRRun | 371 | **split role.** Definability fold (`stmtPost`/`stmtsPost`/`StmtDefinable`/`runStmts_exists`) LIVE (cyclic per-block bricks). **Superseded (~150 LOC):** acyclic-CFG half (`CFGAcyclic` :225, `TermRankLt` :205, `Term.succs` :212, `runFrom_exists*`/`irRun_exists*`) — DriveSim:17/54 retires it via dynamic totalGas. `RunDefinable` (`:258`) UNSATISFIABLE (RS:215-216), replaced by `RunDefinableG`. |
| Call | 145 | **worked-example/anti-vacuity.** `callIR` cited only in a DefsSound docstring; consumes IRRun.det for `call_IRRun_unique`. |
| CallRealises | 146 | **terminal + incremental.** `callRealises_bridge` and `createRealises_bridge` connect the recorder entries to lowered CALL/CREATE observables. The live `evmV2CallEntry` definition is in `Spec/Recorder`. |
| Decode/Modellable | 483 | **terminal.** `lower_modellable` applied RS:1255; residual seams `AtReachableBoundary` (RS:1245) + `CallsCode` (Seams:81); `notCreate_of_atReachableBoundary` (`:426`) wired RS:1255/3677. The no-CREATE combinator run is unavoidable structural infra. |
| DriveSim | 743 | **shared-infra (cyclic path) + incremental.** Imports LowerConforms for `sim_cfg` (heavy but justified — F3 ties the RunFrom to the bytecode world). F1 measure infra + DriveCorr incremental-toward reshaped `runFrom_of_driveCorrLog`. **Safe-delete:** `lower_conforms_cyclic'` (`:666`, flagship refuses to cite it, RS:3730-3736). |
| Drive/SelfPresent | 437 | **terminal + salvage.** `SelfPresent` (`:364`) is a flagship hypothesis (RS:1397); `accounts_ne_empty_of_selfPresent`/`selfPresent_codeFrame` LIVE. §3-§4 `GasLogAligned`/`SloadLogAligned` = salvage for R0 reshape (used only by Headline). `realisedCall_projection` (`:55`) = safe-simplify (thin re-export of realisedCall_cons). |
| Drive/CallPreservesSelf | 258 | **terminal.** Collapses to the single `hprec` seam; `selfPresent_runs_of_call` (`:248`) applied RS:1723; exported via `Seams.callPreservesSelf_of_precompiles`. |
| Drive/Headline | 298 | **salvage for R0 reshape (currently ALL unreferenced).** Exports `DriveCorrPlus` (`:81`), `GasReach` (`:269`), `GasCursorClass` (`:291`). Header (`:17-25`) says §9/§10 deleted, rest "RETAINED salvage". **NOTE:** `DriveCorrLog` is NOT here (it's RS:629); `drive_fuel_mono` does not exist anywhere. |
| RecorderLemmas | — | **terminal + stranded.** `sloadRecord_eq_sloadCost`/`realisedCall_cons`/`runWithLog_drive`/`driveLog_drive` LIVE (SelfPresent/DriveSim/flagship). `runWithLog_messageCall` (`:143`) called ONLY by the dead capstone — **delete together with it**. |

### L7 — Flagship + audit

| File | LOC | Role · why it exists |
|---|---|---|
| RealisabilitySpec | 3874 | **THE FLAGSHIP + only sorry-carrier** (WIP lib). §1-7 structure below. Sole root of the WIP lean_lib (lakefile.lean:31-32); no exit edges. |
| Audit | 62 | **intentional guard net.** ZERO decls; 8 `#guard_msgs in #print axioms` pinning `[propext,Classical.choice,Quot.sound]` for seam-residue decls. Imported LAST (`LirLean.lean:53`); terminal of the DEFAULT build cone. Guards salvage only; RS decls guarded nowhere by design (RS:3867-3872). |

---

## 3. The flagship shape + the open leaves + how the layers feed them

### 3.1 The flagship (verbatim-confirmed)

`Lir.lower_conforms` (`RealisabilitySpec.lean:3705`), conclusion (`:3715-3718`):

```lean
∃ O, RunFrom prog (entryState params) (realisedGas log)
       (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
   ∧ Conforms params.recipient log O
```

Hypotheses: `hcode`/`hmod` (definitional pins), `hself`/`hgas` (decidable entry facts),
`hwf : IRWellFormed prog`, `hcodeFits : codeFits prog`, `hstk : stackFits prog` (the public
static bundle and two scalar budgets that rebuild internal `WellLowered`), `hrun :
runWithLog … = some log` (the runtime premise), `hclean : log.clean`, `hseams :
PrecompileAssumptions prog params` (the honest 2-field seam now owned by `Spec/Seams`).
`Conforms` compares **BOTH** `observe.world` AND `observe.result` (return value / halt kind) —
the full-observable foundation change (4628201).

Companions: `lower_conforms_exact` (`:3752`, both leftover streams `[]`) and
`lower_conforms_gasfree` (`:3788`, the co-flagship under `NoGasReads`, meant proven FIRST).

### 3.2 The SINGLE central blocker

The flagship body (`:3719-3747`) packages **one sorry** (`:3739-3746`) typed as the missing
**`runFrom_of_driveCorrLog`**. Everything downstream — `conforms_of_worldeq` (`:3661`) — is
CLOSED and axiom-clean. The comment (`:3730-3736`) rules out both in-tree run-producers:
- `lower_conforms_cyclic'` (DriveSim:666) needs an **unconditional all-frames `SimStmtStep`** the
  reshaped `StmtTies'` can't supply (its arms hold only under `RecorderCoupled`) — this is exactly
  the vacuity the reshape exists to kill;
- R6 `runs_atReachableBoundary` can't produce `hrb` alone (its `(flatBytes prog).length ≤ 2^32`
  side-condition has no producer from `hwl`).

The true remaining deep node is a NEW coupled driver walking the `RecorderCoupled`/`DriveCorrLog`
(`:629`) invariant across the F2 recursion, instantiating the Layer-C sim lemmas only at coupled
walk-frames.

### 3.3 The open leaves — 11 sorry BODIES / 9 sorry-carrying theorems (machine-verified)

| # | sorry line(s) | Theorem | R-obligation |
|---|---|---|---|
| 1 | `:1385` | `callRealises_of_recorded` | **R3** — call realisation from the log (needs arg-push machine-run producer, Piece B). Genuinely hard. |
| 2 | `:2343`, `:2351` | `atReachableBoundaryVJ_step` (B-pc, B-inrange) | **R6** — pure-engine boundary geometry brick. |
| 3 | `:2380`, `:2383` | `atReachableBoundaryVJ_call` (B-call, B-inrange) | **R6** — pure-engine boundary geometry brick. |
| 4 | `:3634` | `stmtTies'_of_runWithLog` | **R10a** — build StmtTies' from the run. |
| 5 | `:3746` | `lower_conforms` | **R11** — THE flagship (the §3.2 blocker). |
| 6 | `:3780` | `lower_conforms_exact` | **R11-all** — RunFromAll, both streams `[]`. |
| 7 | `:3817` | `lower_conforms_gasfree` | **R11-gasfree** — co-flagship under NoGasReads. |
| 8 | `:3828` | `realisedGas_nil_of_noGasReads` | backing for `_gasfree`/`_exact`. |
| 9 | `:3843` | `exProg_satisfies_hypotheses` | **R12a** — concrete non-vacuity (R12b `:3848` assembles on it, typechecks now). |

Two genuinely-hard leaves: **R3** (`:1385`) and **R6** (the 3 distinct bricks across 4 sorry
tokens — note the grounding's "2 bricks" undercounts). R6's own body `runs_atReachableBoundary`
(`:2456`) is CLOSED — only the edge-lemma bricks are open. The R7 region (`:2466-2958`) and the
entire §6 witness (`:2959-3623`) are fully sorry-free. **Corrections to prior framing:**
`runFrom_of_runFromLeft` (`:1017`) and `runFromLeft_exists` (`:1029`) are PROVED (not open);
`exProg_nonvacuity` (`:3848`) is NOT an own-sorry (transitively sorry via deps).

### 3.4 How the layers feed the flagship

- **L0 Spec** supplies the trusted surface the conclusion quotes: `RunFrom` (Semantics),
  `lower`/`flatBytes` (Lowering), `observe`/`realisedGas`/`realisedCall`/`realisedCreate`/
  `runWithLog` (Recorder),
  `Conforms` (RS:155). `PrecompileAssumptions` + Seams name the irreducible boundary.
- **L1 Engine** supplies the frame-level facts the drive/self-presence/mem/clean-halt reasoning
  needs: `runs_of_drive_ok`, `CleanHalts*`, `stepFrame_next_*`, MemAlgebra slot lemmas, Charges.
- **L2 Decode** supplies "these bytes implement this CFG": JumpValid feeds SimTerm/RS; BoundaryReach
  feeds R6; NoCreateBytes feeds Modellable's no-CREATE clause.
- **L3 Materialise** supplies the value channel: `materialise_runs` (B1) + gas bookkeeping (B2) +
  clean-halt envelope + Match `sim_*`/oracle projections + StorageErase zero-write.
- **L4 Sim** supplies `Corr` and the per-stmt/terminator arms (`sim_call_stmt` etc.) plus
  CleanHaltExtract's `next_*_of_cleanHalt` (called directly in RS).
- **L5 CFG simulation** supplies `sim_cfg`/`SimTermStep`/`WellFormedLowered`/`CallRealises` (shared).
  The old generic-`defs` fuel/rank support is historical; P9 deleted `Acyclic.lean`.
- **L6 Drive** supplies the cyclic drive spine, SelfPresent/CallPreservesSelf, Modellable,
  RecorderLemmas — the machinery the missing `runFrom_of_driveCorrLog` will walk.

### 3.5 RealisabilitySpec internal § structure (split map)

- §1 helpers `:114-564` (all REAL: `WellLowered` internal adapter; `PrecompileAssumptions` now in `Spec/Seams`) — sorry-free
- §2 coupling `:566-647` (`RecorderCoupled` :599, `DriveCorrLog` :629) — sorry-free
- §3 reshaped ties `:649-948` (`StmtTies'` :710, `TermTies'` :817) — sorry-free
- §4 exact-consumption `:950-1040` (RunFromLeft/RunFromAll + 2 PROVED adequacy lemmas) — sorry-free
- §5 R0b-R8 machinery `:1042-2958` — holds R3 (`:1385`) + R6 (`:2343/2351/2380/2383`) sorries
- §6 exProg witness + R9 + R10-R12 assembly `:2959-3865` — holds R10a/R11/R12a sorries
- §7 audit note `:3867-3873`

**Split candidate (S1):** the §6 exProg block `:2975-3613` (~640 LOC, ~20 mostly-private
self-contained lemmas, exits ONLY `exProg` + `wellLowered_exProg`) → its own file, halving the
3874-line flagship. **Dedup (S2):** `haltNonException_of_cleanLog` (`:1249-1263`) and
`conforms_of_worldeq` (`:3671-3685`) share a byte-identical ~13-line terminal-identification
prologue → factor a shared lemma.

---

## 4. The acyclic-vs-cyclic resolution (from the eval)

**Statement diff — genuinely different shape, strictly weaker deliverable:**

| | acyclic capstone `Lir.lower_conforms` (LowerConforms:1188) | flagship `Lir.lower_conforms` (RS:3705) |
|---|---|---|
| IR run | **SUPPLIES** it as a hypothesis (`hir : Lir.IRRun … O`) | **PRODUCES** it (`∃ O, RunFrom …`) |
| ties | **SUPPLIES** unconditional all-frames `hstmts`/`hterm` (`:1214-1217`) | **DERIVES** them internally (R1-R10 under RecorderCoupled) |
| conclusion | only the WORLD edge (`O.world = (observe …).world`) | full `Conforms` (world AND result, RS:155) |

Neither statement assumes CFG-acyclicity — "acyclic" is historical (the retired IRRun
`runFrom_exists`/`CFGAcyclic` construction, retired by DriveSim's dynamic totalGas measure,
DriveSim:17/54). The capstone's supplied all-frames ties are the **exact VACUITY the flagship
reshape exists to kill**: per target-architecture-2026-07-02, the supplied StmtTies/TermTies are
**UNSATISFIABLE** for a real lowered program, so the capstone is a conditional with an
unfulfillable antecedent. Its world equation is precisely the input to the flagship's closed
`conforms_of_worldeq` (RS:3661, applied :3747).

**The capstone theorem is DEAD.** Its one apparent caller (`RS:3864 exact lower_conforms …`) is
INSIDE `namespace Lir` (open :105, end :3874) so it resolves to the FLAGSHIP, not the capstone.
Zero code consumers. **VERDICT: drop** (`LowerConforms.lean:1188-1250`, ~63 LOC). Its sole
exclusive feeder `runWithLog_messageCall` (RecorderLemmas:143) dies with it (delete together).
`entry_corr` (LowerConforms:1102) also loses its only code caller (:1226) — but RS:626 names it as
intended flagship R7 entry machinery, so **confirm before removing entry_corr**.

**P8 update:** `Acyclic.lean` is no longer the well-formedness route into the WIP witness.
`WellFormedLowered` dropped its `MatFueled` fields, the public theorem shape is
`IRWellFormed` + `codeFits` + `stackFits`, and `wellLowered_of_IRWellFormed` rebuilds the internal
adapter consumed by V2 machinery. P9 removed the remaining `Acyclic`/`MatFueled` legacy
generic-`defs` fuel support.

**No whole simulation layer disappears from the acyclic-vs-cyclic conclusion.** The L4 sim engine
is shared via `sim_cfg`; P8 only makes the static lowered-layout adapter fuel-free and keeps it
internal. P9 is the point where the residual fuel/rank file can disappear, after all remaining
generic fuel consumers are migrated.

---

## 5. What is V2 vs Drive vs Engine (the naming confusion, resolved)

Three **altitude** layers, not feature groups:

- **`Engine/`** = **IR-agnostic, frame-level EVM theory** over exp003 `Frame`/`Runs`. Zero
  IR/Spec/V2 imports (verified: every file imports only `Evm`/`BytecodeLayer.*`/sibling Engine).
  This is the sublayer **slated to graduate to exp003** as a reusable library. It is import-clean
  already; graduation is blocked only on **namespace leakage** — 5/8 files still live in the
  experiment namespace `Lir` (`AccountMap.lean:24`, `StepWalk.lean:24`, `Descent.lean:247`,
  `DriveMono.lean:16`, `CleanHalt.lean:32`), and AccountMap self-flags `-- RELOCATE to exp003`
  (`:26`). Sequence it LAST as its own cross-repo PR (keep the folder self-contained so it lifts as
  one `git mv`).

- **``** = the exp005 **gas-free IR semantics SPINE + bytecode-coupled bridges**:
  `Law` (determinism floor), `IRRun` (run existence; acyclic half retired), `Call`/`CallRealises`
  (the CallStream oracle + realisation bridge), `Modellable`. These mention IR types; they are the
  gas-free machine and its realisability seams.

- **`Drive/`** = the **cyclic interpreter-drive walk** that *simulates* the spine over a real
  bytecode `RunFrom`: `SelfPresent`, `CallPreservesSelf`, `Headline`. This is the "bytecode layer"
  — the mechanism (dynamic `totalGas` measure) that retires the CFG-acyclicity restriction and
  discharges the per-cursor ties in one construction.

- **Misfiling:** `DriveSim.lean` is a drive-layer engine but sits directly under `` instead
  of `Drive/`. Moving it to `Drive/Sim.lean` fixes the mental model (updates importers
  Drive/Headline, Audit, `LirLean.lean:44`).

- **`Spec/` altitude caveat (repeat, because it breaks the naming intuition):** `Spec/Recorder` and
  `Spec/Seams` sit at L6 (they import V2-Drive/Engine), NOT at L0 with the other Spec files.
  They are filed in `Spec/` for reviewer-surface role only.

---

## 6. Cleanup ledger (accurate classification, not "dead")

**GENUINELY DEAD (grep-zero, safe delete now):** `SmallStep.IRConf` (`:69`),
`SmallStep.Program.stmtAt` (`:127`); the acyclic capstone `Lir.lower_conforms`
(LowerConforms:1188) + stranded `runWithLog_messageCall` (RecorderLemmas:143);
`assign_sload_sub_key` (LowerDecode:68); `chargeOf_imm_const` (MaterialiseGas:141);
`realisedCall_projection` (SelfPresent:55).

**SUPERSEDED with named replacement (~150 LOC, keep the fold):** IRRun acyclic-CFG half
(`CFGAcyclic`/`TermRankLt`/`Term.succs`/`runFrom_exists*`/`irRun_exists*`) — KEEP the definability
fold (`stmtsPost`/`StmtDefinable`/`runStmts_exists`). Match invariant STRUCTURE (`:125`, → `Corr`).

**INCREMENTAL-toward-OPEN-goals (NOT removable — the shallow pass's main error source):**
Create.lean + Descent DescentKind block → first-class CREATE; BoundaryReach loweringOp bricks →
R6; `callRealises_bridge` → R3; `stash_tail_runs_covered` → Phase-C; Loc/Alloc layer → Phase-D;
Drive/Headline.lean + SelfPresent §3-4 → R0 reshape.

**INTENTIONAL infra (NOT removable):** Spec/Conformance vocabulary; Spec/Seams register; Audit
guards; GasRealises/SloadRealises regression-witnesses (RELOCATE not delete); exProg witness +
PROVED refutations `not_defsSound_stale`/`not_runs_atReachableBoundary`; Call worked-example.

**NEEDS-CONFIRMATION (do NOT delete blind):** `resumeAfterCall_mload` + feeders (MemAlgebra:85);
`entry_storageAgree_codeFrame` (LowerConforms:1089); `jump/branch_landing_of_cleanHalt`
(LowerDecode:486/769, flagship re-derives inline); `decode_at_stmt_head_{nonpush,push}`/
`decode_at_offset_push` (DecodeAnchors, superseded-by-MatSeg but symmetric API); `sim_stmts` alias;
`RunAcc`; `mload_after_mstore`; LowerConforms builder chain (still feeds cyclic headline).

**Ranked reduction levers:** (1) SegAligned tower dedup ~1400→650 (~700 LOC, LOW risk, NO gate —
the largest ungated do-now win); (2) split RS §6 exProg into its own file (legibility, halves the
flagship file); (3) drop dead capstone + stranded feeder (~80 LOC); (4) directory reorg (flat →
role-dirs, legibility, 0 LOC); (5) small orphan deletes. **NOT wins (guard against shallow pass):**
the ~30 frame-accessor @[simp] families (distinct constructors); chargeCache/matCache lockstep
(intentional B1/B2 split); the covered-slot MLOAD dup (intentional anti-cycle);
`CallRealisesS` vs `CallRealises` (named R0b-gated debt).

**STALE headers/docstrings to distrust:** Drive/Headline
`:17-25` ("headlines deleted" — file is live salvage); Spec/Semantics `:5` ("call-free
prototype"); Spec/Recorder `:154/157` ("(gas, calls)" — real accumulator is a 3/4-tuple);
CleanHaltExtract `:41` + SimStmts `:163` (overstate axiom-guard coverage — no `#print axioms` in
those files); Charges `:11` (nonexistent "WorkedCall" consumer); MemAlgebra `:22` (overstates
mload_after_mstore/resumeAfterCall_mload as live).
