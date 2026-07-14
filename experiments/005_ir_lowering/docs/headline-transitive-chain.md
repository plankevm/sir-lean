# exp005 IR→EVM Conformance — Transitive Definition Chain of the Headline

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


*Definitive dependency-closure report for `Lir.lower_conforms_cyclic_assembled`.*
*Synthesized from 9 cluster maps; every node carries `file:line` where known. All paths are relative to `experiments/005_ir_lowering/` unless prefixed `003_bytecode_layer/` or `EVMLean/`.*

> **Read alongside:** `docs/audit-2026-07-02.md` (honesty/quality audit), `docs/remediation-plan-2026-07-02.md` (the fix plan, now **superseded** by `docs/target-architecture-2026-07-02.md` + `docs/execution-plan-2026-07-02.md`), and `docs/gas-decision.md` (gas is now a log-fed exact-equality oracle; the monotonicity law is dropped). Two facts below are qualified by those docs: (1) the headline is **CONDITIONAL** — and its supplied ties were since confirmed **unsatisfiable**, i.e. VACUOUS (see `target-architecture-2026-07-02.md` §1) — (see §1), and (2) the gas channel is being reduced to an opaque log-fed oracle (see §1 / §2).

> **UPDATE (2026-07-03) — file homes moved; line numbers below are ROTTED.** Waves 1–4 of the honesty cleanup executed a structural reorg (HEAD `53c2063`) AFTER this report was pinned. The authoritative pinned surface for the headline cone is now **`LirLean/Audit.lean`** (the `#guard_msgs`-wrapped axiom/signature net); trust it over any `file:line` below. Decl homes per the **redirect map**:
> - `LirLean/IR.lean` → `LirLean/Spec/IR.lean`; `LirLean/Lowering.lean` → `LirLean/Spec/Lowering.lean`; `LirLean/Semantics.lean` / `Machine.lean` → `LirLean/Spec/Semantics.lean`.
> - `TieDischarge.lean` is **DISSOLVED**: the headline/drive decls (`lower_conforms_cyclic_assembled`, `lower_conforms_cyclic_tiefree`, `DriveCorrPlus`, `runFrom_of_driveCorrPlus`, `driveStepPlus_of_block`, `driveCorrPlus_*`) → `LirLean/Drive/Headline.lean`; `CallPreservesSelf`/`callPreservesSelf_modGuards`/`stepPreservesSelf` → `LirLean/Drive/CallPreservesSelf.lean`; `SelfPresent`/`sstorePresence_of_self` → `LirLean/Drive/SelfPresent.lean`; the engine bricks (`drive_accounts_find_mono`, `stepFrame_next_self`/`_next_accMono`, `stepFrame_needsCall_inv`/`_needsCreate_inv`, `AccPresent`) → `EVM/BytecodeLayer/Hoare/{AccountMap,StepWalk,Descent,DriveMono}.lean`.
> - `RunLog.lean` is **DELETED**: `recordCall`/`driveLog`/`runWithLog`/`callOracleOf`/`realisedCall`/`RunLog`/`CallRecord` → `LirLean/Spec/Recorder.lean`; `driveLog_drive`/`runWithLog_drive`/`realisedCall_eq_evmV2` → `LirLean/RecorderLemmas.lean`; the gas-monotonicity section (`geToNat`/`bound_mono`/`driveLog_gas_inv`/`realisedGas_monotone`) is **DELETED**.
> - `{Mono,Oracle,HonestGasTie}.lean` are **DELETED** whole (`Oracle.GasRealises` survives only as a relocated retired witness in `LirLean/MaterialiseRuns.lean`); `Law.lean` narrowed to 4 `.det` lemmas (its `Trace.gasMonotone`/`MonotoneGas` decls **DELETED**).
> - New: `LirLean/Audit.lean` (guard net) + `LirLean/RealisabilitySpec.lean` (non-default `Nightly` lib, R0–R12 sorry-skeleton). The ~226 scattered `#print axioms` were removed; the 22 `#guard_msgs`-wrapped ones (14 in `Audit.lean`, 8 in `MemAlgebra.lean`) are the net.
>
> The `TieDischarge.lean:NNNN` / `RunLog.lean:NNNN` citations throughout this file are doubly dead (file gone + numbers meaningless); they are kept as provenance-at-time-of-writing, not as navigable references.

> **UPDATE (2026-07-03, second) — THE HEADLINE WAS DELETED; THIS ENTIRE REPORT IS NOW HISTORICAL.** The prior banner (above) said `lower_conforms_cyclic_assembled` "now lives at `LirLean/Drive/Headline.lean`". That is **no longer true.** In commits "delete vacuous conformance surface 1/4..4/4" (`ba42b63..7b763dc`) the vacuous cyclic conformance headline **and its whole apparatus were DELETED** — not relocated. The following decls this report's closure map is *about* **no longer exist anywhere**: `Lir.lower_conforms_cyclic_assembled` / `_tiefree`, `Lir.lower_conforms_wf`, the `Lir.lower_conforms_acyclic{,_stop,_stop_canonical,_cfg}` family, `Lir.StmtTies` / `Lir.TermTies`, the Plus assembly (`runFrom_of_driveCorrPlus`, `driveStepPlus_of_block`, `DriveStepPlus`, `driveCorrPlus_entry`/`_step_jump`/`_step_branch`), and the `Lir.Spec.RealisabilityObligations` / `lower_conforms_cyclic_of_obligations` / `_assembled` / `_tiefree` re-exports (`Spec/Conformance.lean` is now a disclaimer stub). **The SOLE conformance surface is now `LirLean/RealisabilitySpec.lean` (Nightly, R0–R12; the ties are DERIVED from the run via R10a/R10b, not supplied.)** Salvaged but no longer the public P8 well-formedness route: `Lir.DriveCorrPlus` (structure) plus the §7/§8 value/gas channels in `Drive/Headline.lean`, residual generic-`defs` rank/fuel support in `Acyclic.lean`, and `Lir.CallRealises` / `Lir.WellFormedLowered` / `Lir.toList_of_blockAt`. **Read the body below as a description of a removed theorem** — kept for provenance only; do NOT treat it as a map of the live tree.

> **P8 status note (2026-07-08).** Any body text below that says `MatFueled` fields or
> `wellFormedLowered_of_acyclic` are live well-formedness infrastructure is superseded.
> `WellFormedLowered` is fuel-free over `matCache`/fold offsets; the public theorem surface is
> `IRWellFormed` + `codeFits` + `stackFits`.
>
> **P9 status note (2026-07-08).** The residual legacy fuel/materialisation stack named in the
> historical closure (`Expr.slot`, `materialiseExpr`, `materialise`, `recomputeFuel`, `MatFueled`,
> `Assembly/Acyclic.lean`, and `NoSlotSource`) has now been deleted.

---

## 1. Headline & conclusion

**`Lir.lower_conforms_cyclic_assembled`** — `LirLean/Drive/Headline.lean` (pinned in `LirLean/Audit.lean`; the `TieDischarge.lean:4798` below is the rotted pre-reorg citation)

This is the cyclic IR→EVM conformance headline. It states that the **bytecode produced by lowering an IR program conforms to that program's gas-free IR world** — i.e. the observable *world channel* (the account/storage map exposed by the halted bytecode frame) coincides with the world produced by running the IR over the CFG, for **general (cyclic) control-flow graphs**.

**Exact conclusion** (verified at `TieDischarge.lean:4834-4837`):

```
∃ O : Lir.Observable,
  (∃ last haltSig, Runs (codeFrame params code) last
      ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world)
  ∧ RunFrom prog o st₀ T prog.entry O
```

That is: there exists an IR observable `O` such that (a) the lowered bytecode, run from the entry code-frame, `Runs` to a frame `last` that cleanly halts, and the **observed world of that halt equals `O.world`**; and (b) `O` is genuinely produced by an IR `RunFrom` at `prog.entry` under the call oracle `o`. The headline both *matches the world* and *constructs the IR run* — it does not assume the IR run as a hypothesis (contrast §4).

**Build status (already verified):** green + axiom-clean. `TieDischarge.lean:5027` carries `#print axioms Lir.lower_conforms_cyclic_assembled`, and every `#print axioms` guard across the closure (`TieDischarge.lean:5004-5027`, plus the guards in `Acyclic.lean`, `IRRun.lean`, `CleanHalt.lean`, `LowerDecode.lean:585,1053`, `Modellable.lean`) asserts dependence only on the three standard Lean axioms **`[propext, Classical.choice, Quot.sound]`**. No `sorry`, no `native_decide`, no project-introduced axiom anywhere in the closure.

> **⚠ CONDITIONAL headline (audit-2026-07-02.md §1/§3).** `lower_conforms_cyclic_assembled` (`TieDischarge.lean:4798`) **supplies** the per-block runtime ties `hstmtties : ∀ L b, StmtTies …` and `htermties : ∀ L b, TermTies …` (:4813/:4815) **and** `hcall : CallPreservesSelf` (:4804) **as hypotheses**. Nothing in the default build discharges these from an actual run of `lower prog` (from the recorder `runWithLog`), and there is **no concrete end-to-end instantiation** of the headline on a real `lower prog`. So the theorem currently reads: *"IF the lowering realises the per-cursor ties (IR gas = machine gas, SSTORE realises, CALL realises) AND self-presence is preserved, THEN the world conforms."* The runtime ties are **INPUTS, not outputs.** The **realisability closure** that would make the headline unconditional (build `hstmtties`/`htermties` for `lower prog` from `runWithLog`, plus one concrete instantiation) is planned as **Phase 3 of `docs/remediation-plan-2026-07-02.md`** and is the main thing still missing.

> **⚠ Gas channel being reduced to an opaque oracle (gas-decision.md).** Per the settled gas decision, gas is handled exactly like an external call: a **log-fed exact-equality oracle** — the recorder (`runWithLog`) captures the machine's `GAS` output and it is fed into the IR oracle, then proved equal. Gas introspection is **not** a delivered first-class reasoning feature. The gas-monotonicity law (`Trace.gasMonotone` / `MonotoneGas` in `Law.lean`, `realisedGas_monotone` in `RunLog.lean`, `GasRealises.monotoneGas` in `Oracle.lean`, `lower_preserves_obs_mono` in `Mono.lean`) is **proved-but-unused and is being removed** (`Mono.lean`/`Oracle.lean` deleted, `Law.lean` narrowed) — see gas-decision.md §2 and remediation-plan Phase 2. The surviving gas guarantee is the per-cursor **exact-equality** `StmtTies.gas` conjunct only.

---

## 2. The dependency layers (top-down walk)

The closure decomposes into six strata. Nodes are classified by the `kind` field from the maps: `headline` (glue theorems), `structural` (static, per-program-decidable side conditions), `runtime-tie` (genuine correspondence lemmas derived from the semantics), `scope-premise` (domain-restriction hypotheses), `oracle-boundary` (designed deferral seams), `lowering` (pure compiler functions), `semantics-core` (trusted leanevm base).

### Layer A — Headline & assembly glue (`kind: headline`)

| Node | Loc | Role |
|---|---|---|
| `lower_conforms_cyclic_assembled` | `TieDischarge.lean:4798` | headline; builds `hstmts`/`hterm` + jump/branch edge bundles |
| `lower_conforms_cyclic_tiefree` | `TieDischarge.lean:4681` | tie-free cyclic headline (opaque `SimStmtStep`/`SimTermStep` + supplied edge bundles) |
| `runFrom_of_driveCorrPlus` | `TieDischarge.lean:4638` | strong induction on `totalGas` → IR `RunFrom`; **cyclic-safe** |
| `driveStepPlus_of_block` | `TieDischarge.lean:4552` | per-block drive step; dispatches `b.term` |
| `driveCorrPlus_entry` | `TieDischarge.lean:3819` | base case: entry `DriveCorr` → `DriveCorrPlus` (empty prefixes) |
| `driveCorrPlus_step_stop` | `TieDischarge.lean:4227` | stop/halt Plus wrapper |
| `driveCorrPlus_step_jump` | `TieDischarge.lean:4366` | jump-edge Plus wrapper |
| `driveCorrPlus_step_branch` | `TieDischarge.lean:4438` | branch-edge Plus wrapper |
| `sim_cfg` | `LowerConforms.lean:1007` | whole-CFG glue: IR `RunFrom` ⇒ bytecode `Runs` to halt with world-agreement |

**Second, straight-line family** (does NOT drive the CFG from bytecode; takes the IR run `hir` as a supplied hypothesis and proves only the world edge — strictly weaker than the cyclic headline, included for context):

| Node | Loc | Role |
|---|---|---|
| `lower_conforms` | `LowerConforms.lean:1262` | world edge via `entry_corr` + `sim_cfg` + messageCall bridge; supplies `hir` |
| `lower_conforms_wf` | `LowerConforms.lean:1518` | builder variant (`WellFormedLowered` + `StmtTies`/`TermTies`); supplies `hir` |
| `entry_corr` | `LowerConforms.lean:1101` | seeds `Corr` at `(entry,0)` via the leading-JUMPDEST step |
| `messageCall_runs` | `EVM/BytecodeLayer/Hoare/CallSequence.lean:132` | boundary bridge into observables |
| `runWithLog_messageCall` | `LirLean/RunLog.lean` (line not pinned in maps) | pins `messageCall = .ok` from the recording run |

> **Sibling cyclic driver in `DriveSim.lean`.** The map surfaced a parallel F3 chain `lower_conforms_cyclic` (`DriveSim.lean:623`) → `lower_conforms_cyclic'` (`:665`) → `runFrom_of_driveCorr` (F2, `:586`) → `driveStep_of_block` (`:494`) → `drive_step_block_{stop,ret,jump,branch}` (`:226/:252/:298/:381`). This is the un-strengthened (non-`Plus`) sibling of the `assembled` chain; both route through `sim_cfg` and use the `totalGas` measure. The `assembled` headline uses the `Plus`-strengthened variant (which additionally threads `SelfPresent` + gas/sload alignment).

### Layer B — Structural well-formedness & drive invariants

| Node | Loc | Kind |
|---|---|---|
| `WellFormedLowered` | `LowerConforms.lean:143` | structural (P8: pc/offset/slot bounds over fold emission; no `MatFueled` fields) |
| former `WellFormedLowered.matFueled_{sstore,sload,ret,branch}` | historical `LowerConforms.lean:145,159,170,176` | removed from the live P8 lowered-layout bundle |
| `WellFormedLowered.bound_{sstore,sload,ret,stop,jump,branch}` | `LowerConforms.lean:150,165,180,185,189,195` | structural |
| `WellFormedLowered.slots_slot` | `LowerConforms.lean:210` | structural |
| `DriveCorr` | `DriveSim.lean:87` | scope-premise (`Corr` + `CleanHaltsNonException`) |
| `DriveCorrPlus` | `TieDischarge.lean:3800` | scope-premise (`DriveCorr` + `SelfPresent` + `GasLogAligned`/`SloadLogAligned`) |
| `DriveStep` / `DriveStepPlus` | `DriveSim.lean:460` / `TieDischarge.lean:4532` | structural per-block obligation |
| `totalGas` | `Measure.lean` (line `:0` in map) | structural drive measure (frame `gasAvailable`, strictly descends/block) |
| `driveCorr_measure` | `DriveSim.lean:97` | runtime-tie (`totalGas` collapses to `gasAvailable.toNat` at boundary) |
| `totalGas_succ_lt` / `jumpdestFrame_gas_lt` | `DriveSim.lean:196` / `:184` | runtime-tie (strict descent; JUMPDEST costs Gjumpdest=1) |
| `RunDefinable` | `IRRun.lean:257` | scope-premise; **benign definability, NOT acyclicity** |

### Layer C — StmtTies / TermTies (§7 runtime ties) + DriveCorr/clean-halt + lowering/decode

**Statement/terminator tie bundles** (Prop-valued conjunctions, *not* theorems — their conjuncts are exactly the builder hypotheses):

| Node | Loc | Kind |
|---|---|---|
| `StmtTies` | `LowerConforms.lean:1353` | runtime-tie (5 conjuncts) |
| `StmtTies.assign / .sload / .gas / .sstore / .call` | `LowerConforms.lean:1355,1364,1387,1404,1415` | runtime-tie (call = oracle edge) |
| `TermTies` | `LowerConforms.lean:1422` | runtime-tie (6 conjuncts) |
| `TermTies.succ / .stop / .ret / .jump / .branch` | `LowerConforms.lean:1424,1427,1433,1458,1472` | structural / scope-premise / runtime-tie |

> **Note (conditional / gas).** `StmtTies`/`TermTies` are **supplied as hypotheses** by the headline (§1 caveat) — the realisability closure that would build them from `runWithLog` is remediation-plan Phase 3. The `StmtTies.gas` conjunct (:1387/:1398) is now an **exact-equality log-fed oracle tie** (`ob = ofUInt64(fr.gas − Gbase)`), NOT a monotonicity property; the gas-monotonicity nodes (`Trace.gasMonotone`/`MonotoneGas`/`realisedGas_monotone`/`GasRealises.monotoneGas`/`lower_preserves_obs_mono`) are being removed per `gas-decision.md`.
| `simStmtStep_block` | `LowerConforms.lean:441` | builder: `WellFormedLowered` + `StmtTies` ⇒ `SimStmtStep` |
| `simTermStep_block` | `LowerConforms.lean:883` | builder: `WellFormedLowered` + `TermTies` ⇒ `SimTermStep` |
| `SimStmtStep` | `SimStmts.lean:66` | per-statement simulation predicate |
| `SimTermStep` | `LowerConforms.lean:96` | per-terminator simulation predicate |
| `sim_stmts_block` | `SimStmts.lean:147` | statement-list spine (induction on `RunStmts`) |
| `Corr` | `SimStmt.lean:103` | runtime-tie workhorse (pc/code/validJumps/stack/storage/defs/mem agreement) |
| `MemRealises` | `MaterialiseRuns.lean:601` | structural (memory value channel; slot readback = abstract value) |
| `MatRuns` | `MaterialiseRuns.lean:335` | runtime-tie (materialise-run correspondence) |
| `StepScoped` | `DefsSound.lean:514` | structural (scoping side-conditions) |
| `NonRecomputable` | `DefsSound.lean:115` | structural (gas/sload/call-result tmps) |

**Clean-halt scope machinery** (`CleanHalt.lean` + `DriveSim.lean` + `Modellable.lean`):

| Node | Loc | Kind |
|---|---|---|
| `CleanHaltsNonException` | `CleanHalt.lean:62` | scope-premise (reaches `.success`/`.revert`, not exception) |
| `CleanHalts` | `CleanHalt.lean:41` | scope-premise (any-halt; weaker, provides `totalGas` well-foundedness) |
| `HaltNonException` | `CleanHalt.lean:45` | scope-premise classifier (True unless `.exception`); dischargeable |
| `cleanHaltsNonException_forward` | `CleanHalt.lean:80` | runtime-tie (propagates witness along `Runs`, via `Runs.linear_to_halt`) |
| `cleanHalts_forward` | `CleanHalt.lean:69` | runtime-tie |
| `cleanHaltsNonException_of_success` | `CleanHalt.lean:96` | runtime-tie (build witness from a `.success` halt) |
| `cleanHalts_of_runWithLog` | `DriveSim.lean:141` | runtime-tie (grounds the entry witness via recording interpreter) |
| `runWithLog` / `driveLog` / `RunLog` / `recordCall` / `CallRecord` | `RunLog.lean:219/156/82/145/68` | lowering (recording interpreter) |
| `driveLog_drive` / `runWithLog_drive` | `RunLog.lean:337/624` | runtime-tie (recording is faithful to `drive`) |
| `runs_of_drive_ok` | `DriveRuns.lean:283` | runtime-tie (reverse `Runs` construction) |
| `ModellableStep` | `DriveRuns.lean:142` | runtime-tie (no CREATE node / no precompile-CALL node) |
| `lower_modellable` | `Decode/Modellable.lean:471` | runtime-tie (produces `ModellableStep` universal) |
| `modellableStep_of` | `Decode/Modellable.lean:442` | runtime-tie |
| `NotCreate` / `notCreate_of_atReachableBoundary` | `Decode/Modellable.lean:398/421` | structural (**discharged** from `AtReachableBoundary`) |
| `AtReachableBoundary` | `Decode/Modellable.lean:407` | structural (pc-reachability residual `hrb`; per-program dischargeable) |
| `stepFrame_needsCreate_isCreate` / `beginCall_isCode_of_codeSource_ne_precompiled` | `Decode/Modellable.lean:336/371` | structural |

**Lowering / decode chain** (`Lowering.lean`, `DecodeLower.lean`, `DecodeAnchors.lean`, `JumpValid.lean`, `LowerDecode.lean`, `MatDecLower.lean`):

| Node | Loc | Kind |
|---|---|---|
| `lower` | `Lowering.lean:413` | lowering (`encode (emit (allocate prog) prog)`) |
| `emit / encode / allocate` | `Lowering.lean:401/408/355` | lowering |
| `defsOf` | `Lowering.lean:243` | lowering (post-P9: non-recomputable temps route to `Loc.slot`; old `Expr.slot` route is historical) |
| `offsetTable / blockLen / recomputeFuel` | `Lowering.lean:385/380/162` | lowering (old `recomputeFuel` entry is historical; P9 deleted the fuel path) |
| `emitStmt / emitTerm / emitBlockBody / materialiseExpr / materialise` | `Lowering.lean:178/212/374/140/157` | lowering (old fuel materialisation entries are historical after P9) |
| `emitDest / emitImm / slotOf / chargeOf` | `Lowering.lean:135/128/132`, `MaterialiseGas.lean:74` | lowering |
| `defsOf_ne_gas / defsOf_ne_sload` | `Lowering.lean:257/297` | structural |
| `flatBytes / lower_eq_flatBytes / termOf / pcOf / pcOf_eq_termOf` | `DecodeLower.lean:46/61`, `DecodeAnchors.lean:156`, `Match.lean:64`, `SimTerm.lean:82` | structural |
| `term_dest_decode`, `decode_at_*`, `decode_lower_{push,nonpush}`, `decode_{push,nonpush}_of_list` | `LowerDecode.lean:339`, `DecodeAnchors.lean:283/241`, `DecodeLower.lean:144/151/100/116` | structural |
| `decode_at_block_offset_jumpdest / block_offset_validJump / reaches_block_offset / ReachesBoundary` | `JumpValid.lean:495/469/411/14` | structural |
| `MatDec` + `matDec_of_{lower,term,seg}` + leaf decoders | `MaterialiseRuns.lean:236`, `MatDecLower.lean:452/498/290/166/236` | structural |
| `jump_landing_of_cleanHalt` | `LowerDecode.lean:471` | headline (jump landing producer) |
| `branch_landing_of_cleanHalt` | `LowerDecode.lean:755` | headline (branch landing producer) |
| `sim_term_edge_branch_lowered` | `LowerDecode.lean:606` | headline (branch decode workhorse) |
| `MatFueled` + unfolding lemmas | `MatDecLower.lean:262/274/278` | structural |

### Layer D — Oracle seams (`kind: oracle-boundary`)

The four designed deferral seams (fully treated in §3):

| Seam | Loc | Abstracts |
|---|---|---|
| `SstoreRealises` | `SimStmt.lean:318` | EIP-2200 SSTORE charge/stipend + self-account presence |
| `CallRealises` / `Lir.Frame.CallOracle` / `evmV2CallOracle` | `LowerConforms.lean:304`, `Machine.lean:96`, `CallRealises.lean:64` | external-CALL world effect |
| `hprec` (`callPreservesSelf_modGuards.hprec`) | `TieDischarge.lean:3690` | precompile immediate-return no-erase (inside `CallPreservesSelf`) |
| `CallsCode` | `Decode/Modellable.lean:435` | reachable CALLs target code, not precompiles 1..10 |

Supporting the call seam: `CallPreservesSelf` (`TieDischarge.lean:3267`), its discharge chain `callPreservesSelf_success` (`:3584`) / `callPreservesSelf` (`:3654`) / `callPreservesSelf_modGuards` (`:3689`), Brick D `drive_accounts_find_mono` (`:3440`), `SelfPresent` (`:408`), and the engine-level inversions `stepFrame_next_accMono` (`:2708`), `stepFrame_needsCall_inv` (`:2812`), `stepFrame_needsCreate_inv` (`:2941`), `stepFrame_halted_success_accMono` (`:3091`). On the SSTORE side: `sstorePresence_of_self` (`:416`), `sim_sstore_stmt` (`SimStmt.lean:346`), `sim_sstore` (`Match.lean:211`), `materialise_runs_of_cleanHalt` (`MaterialiseCleanHalt.lean:377`). On the call value side: `call_reflects_lowered` (`Match.lean:436`), `callRealises_bridge` (`CallRealises.lean:90`), `evmCallOracle` (`Call.lean:109`), `callSuccessFlag` (`Call.lean:121`), `evmCallOracle_successWord_eq_x` (`Call.lean:129`), `realisedCall` (`RunLog.lean:272`).

### Layer E — Trusted base semantics (`kind: semantics-core`, leaves)

All in `EVMLean/Evm/…` (leanevm base) and `EVM/BytecodeLayer/…`. Not proven in this project — the trust root (see §5).

| Node | Loc |
|---|---|
| `Evm.Frame` / `FrameKind` / `FrameHalt` / `FrameResult` / `Signal` / `Pending` | `EVMLean/Evm/Semantics/Frame.lean:27/23/45/50/87/83` |
| `Evm.ExecutionException` | `EVMLean/Evm/Exception.lean:6` |
| `Evm.Account` | `EVMLean/Evm/State/Account.lean:25` |
| `Evm.stepFrame` | `EVMLean/Evm/Semantics/Dispatch.lean:130` |
| `Evm.beginCall` / `endCall` / `resumeAfterCall` | `EVMLean/Evm/Semantics/Call.lean:18/93/122` |
| `Evm.beginCreate` / `endCreate` / `resumeAfterCreate` / `contractAddressBytes_create_isSome` | `EVMLean/Evm/Semantics/Create.lean:64/141/189/38` |
| `Evm.endFrame` / `drive` / `seedFuel` / `messageCall` / `createContract` | `EVMLean/Evm/Semantics/Interpreter.lean:8/36/71/73/78` |
| `Evm.decode` / `validJumpDests` (+AuxNat) / `parseInstr` / `pushArgWidth` / `uInt256OfByteArray` | `EVMLean/Evm/Semantics/Decode.lean:52/126/100/…` |
| `BytecodeLayer.Hoare.Runs` / `StepsTo` / `CallReturns` / `EntersAsCode` | `EVM/BytecodeLayer/Hoare.lean:114/52/91`, `Semantics/System.lean:237` |
| `Runs.linear_to_halt` / `Runs.gasAvailable_le` | `EVM/BytecodeLayer/Hoare.lean:240`, `Hoare/GasMonotone.lean:251` |
| `CallResult.observe` | `EVM/BytecodeLayer/Observables.lean:36` |
| IR semantics cores: `RunFrom` / `IRRun` / `RunStmts` / `EvalStmt` / `stmtPost` / `stmtsPost` | `Machine.lean:228/274`, `IRRun.lean:112/…`, `Machine.lean:166`, `IRRun.lean:69/112` |

*(`totalGas` was cited `:0`; its file is `Measure.lean`. `runWithLog_messageCall`, `sim_stmts_block`, and a few `:0`-annotated cross-cluster leaves were not opened to an exact line in the maps — flagged rather than invented.)*

---

## 3. The four oracle seams — scoping verdicts

This is the section that matters for the scoping decision. Each seam is judged **TRUE oracle** (a designed deferral the gas/call-agnostic IR intentionally does not model — keep as a supplied hypothesis) or **DISCHARGEABLE** (mechanically realised or per-program checkable). Verdicts synthesize the `oracleVerdicts` across all clusters.

### 3.1 `SstoreRealises` — `SimStmt.lean:318`

**Abstracts:** at every self-address SSTORE frame with stack `[kw,vw]`: (1) the `Gcallstipend` (=2300) gate is open, (2) the EIP-2200 charge `sstoreChargeOf ≤ gasAvailable`, (3) the self account is present (`accounts.find? self = some acc`).

**Verdict: SPLIT — gas half DISCHARGEABLE, world half TRUE oracle.**
- Conjuncts 1–2 are exactly the gates the dispatch *checks*, so a successful `.next` SSTORE step witnesses them — derivable via the step-inversion `stepFrame_sstore_inv` (`003_bytecode_layer/…/Dispatch.lean:236`). exp005 already drops them: the two materialise-channel gas envelopes are DERIVED from `CleanHaltsNonException` via `materialise_runs_of_cleanHalt`.
- Conjunct 3 is *not* a dispatch gate — SSTORE reads storage through an `.option 0` lens, so a successful step never witnesses account presence. This is a genuine supplied world fact, isolated in exp005 as the standalone invariant **`SelfPresent`** (`TieDischarge.lean:408`), seeded at the entry code-frame (`selfPresent_codeFrame`) and preserved across materialise/call frames.

**Recommendation:** keep `SelfPresent` (the world half) as an oracle/world-wellformedness premise; the gas half is already discharged.

### 3.2 `CallRealises` — `LowerConforms.lean:304`

**Abstracts:** the realised external-CALL trace: recorded `(result, pd)`, the oracle pinning `o = evmV2CallOracle result pd self`, the arg-push `Runs`, the returning CALL `CallReturns callFr resumeFr`, all pc/memory/storage/stack pins, post-state scoping, and the Route-B stash tail.

**Verdict: PARTLY DISCHARGEABLE around a TRUE-oracle kernel.**
- **Irreducibly oracular kernel:** `CallReturns callFr resumeFr` (`EVM/BytecodeLayer/Hoare.lean:91`) — the assertion that the child call actually ran (`EntersAsCode` + `drive` to `childRes`) and pins `resumeFr = resumeAfterCall …`; plus the identification `o = evmV2CallOracle result pd self`. This is the genuine runtime call observation, unobtainable from the caller's program text. The abstract seam is **`Lir.Frame.CallOracle`** (`Machine.lean:96`), the function `Word→Word→World→(World×Word)` the gas-free IR threads, with its three effects (post-storage world `CallOracle.postStorage` `Call.lean:82`, restored gas [dropped in gas-free v2], success word `CallOracle.successWord` `Call.lean:86`). **Keep.**
- **Mechanically-realised plumbing (dischargeable in principle):** the arg-push `Runs` + pc/memory pins (from `materialise_runs` over `CallSpec` operands), the resume-frame env/pc/stack pins (rfl consequences of `resumeAfterCall`), and the Route-B stash tail. Bundled into `CallRealises` only as an engineering convenience.
- The realisability discharge at the concrete boundary is **rfl-clean**: `call_reflects_lowered` (`Match.lean:436`), `callRealises_bridge` (`CallRealises.lean:90`), `evmCallOracle_successWord_eq_x` (`Call.lean:129`), `realisedCall_eq_evmV2` (`RunLog.lean:280`) — so the IR's call effect *is* the lowered bytecode's by construction, never assumed.

**Recommendation:** keep `Lir.Frame.CallOracle` + `CallReturns` as the oracle; the surrounding frame-threading is realised (dischargeable), so a tightened `CallRealises` could shed the plumbing conjuncts.

### 3.3 `hprec` (inside `CallPreservesSelf`) — `TieDischarge.lean:3690`

**Abstracts:** the sole remaining supplied hypothesis of `callPreservesSelf_modGuards` after 6 of 7 framing seams are discharged engine-level: every `beginCall` that returns immediately as a precompile (`beginCall cp = .inr imm`) is account-presence preserving (precompiles only insert, never erase).

**Verdict: TRUE oracle — keep.** The docstrings at `TieDischarge.lean:3650-3652`/`3686-3688` are explicit that `CallPreservesSelf` is *not* unconditionally true: a live precompile's `.inr` empty-arm really can erase, and `CallReturns` does not rule it out. The gas/call-agnostic IR abstracts precompile world effects; the precompile output map is opaque for a live precompile. It is **vacuous for call-free or non-precompile-targeting programs**, and must be instantiated per precompile set (1..10). It is the *presence-side twin* of `CallsCode`.

Context: 6 seams were discharged engine-level — `hmono ← stepFrame_next_accMono` (`:2708`), `hcall_acc/hcall_kind/hcall_self ← stepFrame_needsCall_inv` (`:2812`), `hhalt ← stepFrame_halted_success_accMono` (`:3091`) — and the former no-CREATE seam was *eliminated* (`beginCreate` is now total, so `stepFrame_needsCreate_inv` `:2941` proves the CREATE step in place). Only `hprec` survives.

### 3.4 `CallsCode` — `Decode/Modellable.lean:435`

**Abstracts:** the honest modellability residual: every reachable `.needsCall` targets a code account, never a precompile (`cp.codeSource` never `.Precompiled p`).

**Verdict: TRUE oracle — keep.** The CALL target is taken off the stack at runtime; an IR `Stmt.call` whose callee materialises a precompile address 1..10 would violate it — it is a genuine runtime property, *not* structurally guaranteed by the lowering. Contrast its sibling `NotCreate` (`Modellable.lean:398`), which is *now discharged structurally* from `AtReachableBoundary` (`notCreate_of_atReachableBoundary`, `:421`), because the lowering emits no CREATE-head opcode. `CallsCode` is **vacuous for call-free programs** and feeds `DriveCorr` via `cleanHalts_of_runWithLog` as the residual `hcc`. It is the *dispatch-gate twin* of `hprec`: `hprec` = the world-effect obligation IF a precompile is called; `CallsCode` = the domain restriction that no precompile is called.

> **Note on `hprec` vs `CallsCode`:** these are the *same* precompile boundary from two angles. Both are non-structural runtime facts, both vacuous for call-free IR, both must remain supplied and be instantiated per precompile set.

---

## 4. Acyclic vs. cyclic partitioning

**Cyclic is the general theorem; acyclic is a strict specialization** that additionally *discharges* two hypothesis families the cyclic case must supply. There are **two independent acyclicity orders**, each discharging a distinct family.

### (1) Control-flow rank → discharges IR-run existence `hir`

- `Lir.CFGAcyclic` (`IRRun.lean:225`) via `blockRank : Label → ℕ` makes the `RunFrom` recursion well-founded (`TermRankLt` `:205`, `Term.succs` `:212`, decreasing + succ_present).
- `runFrom_exists` (`IRRun.lean:291`, strong induction on `blockRank`) → `irRun_exists` (`:340`) **CONSTRUCTS** the IR run instead of assuming it.
- `lower_conforms_acyclic_cfg` (`Acyclic.lean:359`) uses `irRun_exists` from `CFGAcyclic` + `RunDefinable` to **eliminate `hir`**. Base case `lower_conforms_acyclic_stop` (`:275`) uses `irRun_exists_stop` (`IRRun.lean:162`); `_stop_canonical` (`:310`) additionally discharges `hstore` by rfl.
- **A cyclic CFG (a loop) has no `blockRank`.** The `RunFrom` recursion need not terminate structurally, so existence of the run cannot be built by structural induction. **This is exactly why the cyclic headline replaces `blockRank` with the runtime `totalGas` measure** (`runFrom_of_driveCorrPlus`, `TieDischarge.lean:4638`): gas strictly descends per block (`totalGas_succ_lt`, from `Runs.gasAvailable_le` + the JUMPDEST drop), which is well-founded on cyclic CFGs. The cyclic headline therefore **carries no `hir`** — it constructs the run — and the `totalGas` measure replaces *both* `CFGAcyclic` and the supplied IR run.

### (2) Historical def-graph rank → formerly discharged `MatFueled`

- The old chain was `Acyclic` + `rank+1<recomputeFuel` → `matFueled_of_exprRankLt` →
  `matFueled_tmp_of_acyclic` → `wellFormedLowered_of_acyclic`.
- P8 removed this as a live route. `IRWellFormed.defEnvOrdered` and the fold-cache fixpoints
  (`matCache`/`chargeCache`) now replace the rank/fuel envelope; P9 deleted the residual
  `Acyclic` / `MatFueled` definitions.

### Why `hpresent`/`hjumpPresent`/`hbranchPresent` are supplied in the cyclic case

The cyclic `assembled` headline **honestly supplies** the static presence facts `hpresent` (`TieDischarge.lean:4805`), `hjumpPresent` (`:4817`), `hbranchPresent` (`:4822`), and the cond-materialise stack-room fold `hstkBranch` (`:4831`). These are **static CFG well-formedness / charge-length bounds** — *not* program-specific runtime restrictions:
- `hpresent`/`hjumpPresent`/`hbranchPresent` assert that every block / jump target / branch target referenced is present in `prog.blocks` — decidable from the CFG text and dischargeable by a **boundary walk** (the analogue of the `AtReachableBoundary`/`block_offset_validJump` reachability machinery).
- `hstkBranch` is a `chargeOf … ≤ 1024` stack-depth-profile bound — statically checkable, and explicitly *not gas-derivable* (the clean-halt gas thread cannot produce a stack-length bound), which is why it stays supplied.

These are the residue the acyclic case would fold into `CFGAcyclic.succ_present`; in the general cyclic case they are peeled out as explicit, statically-dischargeable hypotheses rather than baked into an acyclicity witness.

---

## 5. Trusted base & caveats

**Axiomatically trusted (the trust root).** Everything under §2 Layer E — all of `EVMLean/Evm/…` (leanevm base) and the `003_bytecode_layer` core: `stepFrame`, `Frame`/`FrameHalt`/`Signal`, `Runs`, `drive`, `beginCall`/`endCall`/`resumeAfterCall`, `beginCreate`/`endCreate`/`resumeAfterCreate`, `endFrame`, `messageCall`, `observe`, `Account`, `decode`/`validJumpDests`. These are *the model of the EVM*; the conformance statement is only as sound as this model. Mathlib is likewise trusted. The `#print axioms` guards confirm no *new* axiom/`sorry` is introduced above the base — the added lemmas use only `[propext, Classical.choice, Quot.sound]`.

**Scope premise — `CleanHaltsNonException`** (`CleanHalt.lean:62`). The honest domain restriction: the frame reaches, via `Runs`, a halt that is **non-exception** — i.e. `.success` or `.revert` only. `HaltNonException` (`CleanHalt.lean:45`) is True *unless* the terminal is `.exception`. Concretely this **excludes `OutOfGas` and the other `ExecutionException` variants** (`Evm.ExecutionException`, `EVMLean/Evm/Exception.lean:6` — 8 variants total: `OutOfFuel`, `InvalidInstruction`, `OutOfGas`, `BadJumpDestination`, `StackOverflow`, `StackUnderflow`, `InvalidMemoryAccess`, `StaticModeViolation`). **REVERT is IN scope** (`.revert` is non-exception). A genuine OOG/exception run is un-modellable by the gas-agnostic IR and legitimately falls outside conformance. The whole-run witness is supplied *once* at the entry and **propagated** (not re-supplied) along each edge by `cleanHaltsNonException_forward` (via `Runs.linear_to_halt`); it is *grounded honestly* at the entry by `cleanHalts_of_runWithLog` (recording interpreter + reverse `Runs` construction under `ModellableStep`).

**Patched-reference caveat (important, unmerged upstream).** Conformance is to a **patched** leanevm, not stock upstream. `EVMLean` is a vendored git-subtree (merge `be6e742`) carrying a local patch chain absent upstream:
- `7ecbee7` — faithful CREATE-begin-fault checkpoint (drop `accounts := ∅`);
- `7b34698` — total RLP encoder for the CREATE address preimage;
- `ad67864` — make `beginCreate` total, remove the dead CREATE-begin fault.

Concretely: `beginCreate` (`Create.lean:64`) is now **total** (former `.error` address-derivation guard removed, justified by `contractAddressBytes_create_isSome` `Create.lean:38`), and `drive`'s `.needsCreate` arm descends **unconditionally** (no soft CREATE-begin fault). `resumeAfterCreate` (`Create.lean:189`) is the patched checkpoint resume (still `Except`-typed, may throw `OutOfGas`). **Until these patches are upstreamed, the trust root does not align with stock leanevm.**

---

## 6. Open scoping decision

For the project lead, per seam:

1. **`SstoreRealises` (`SimStmt.lean:318`) → SPLIT.** Gas half (stipend + EIP-2200 charge): **discharge** — already derived from `CleanHaltsNonException` via `materialise_runs_of_cleanHalt`. World half (`SelfPresent`, `TieDischarge.lean:408`): **keep** as a world-wellformedness premise (SSTORE's `.option 0` read never witnesses presence). *Recommend: keep only `SelfPresent`.*

2. **`CallRealises` (`LowerConforms.lean:304`) → keep kernel, discharge plumbing.** Keep `Lir.Frame.CallOracle` (`Machine.lean:96`) + `CallReturns` (`Hoare.lean:91`) — the genuine child-run observation. Discharge the arg-push/resume/Route-B frame-threading conjuncts (rfl/`materialise_runs` consequences; bridges already rfl-clean). *Recommend: tighten `CallRealises` to shed plumbing; keep the oracle.*

3. **`hprec` (`TieDischarge.lean:3690`) → keep.** True precompile-erase oracle; vacuous for call-free IR; instantiate per precompile set. *Recommend: keep as hypothesis.*

4. **`CallsCode` (`Decode/Modellable.lean:435`) → keep.** True runtime precompile-target restriction (the domain twin of `hprec`); vacuous for call-free IR. *Recommend: keep as hypothesis.*

**Net:** the genuine, irreducible oracle surface of the headline is **three objects** — the world-presence invariant `SelfPresent`, the external-call oracle `Lir.Frame.CallOracle`/`CallReturns`, and the single precompile boundary seen as `hprec`+`CallsCode` — plus the one honest **scope premise** `CleanHaltsNonException`. Everything else (SSTORE/SLOAD/GAS gas envelopes, `NotCreate`, `MatFueled`, presence/reachability folds, decode anchors, the CREATE seam) is either derived from the clean-halt witness or statically dischargeable per program. For a **call-free program**, all three call-side oracles (`CallOracle`/`CallReturns`, `hprec`, `CallsCode`) are vacuous, collapsing the residual oracle surface to `SelfPresent` + `CleanHaltsNonException`.
