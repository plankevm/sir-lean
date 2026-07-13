# Deep-dive cluster: the V2 spine + Drive walk (2026-07-04)

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Scope: `LirLean/{Law,IRRun,Call,CallRealises,Modellable,DriveSim}.lean` and
`LirLean/Drive/{SelfPresent,CallPreservesSelf,Headline}.lean`.

Read-only audit. Every classification below is grounded in a repo-wide grep of the decl name
(`grep -rn <name> LirLean/ --include='*.lean'`, comment lines stripped) plus the proof plan.
Roles used:

- **terminal-for-flagship** — consumed in the *code* (not just docstring) of the flagship
  `Lir.lower_conforms` (`RealisabilitySpec.lean`) or of a `Spec/Seams.lean` forwarder it cites.
- **terminal-for-audit** — `#print axioms`'d in `Audit.lean` (axiom-footprint guard).
- **incremental-toward-X** — proven, currently no code caller, but the header/plan names the future
  connection X (default classification per the audit hard-rules).
- **shared-infra** — an internal helper consumed only by other decls in this cluster.
- **scaffold-experimental** — a worked example / anti-vacuity demonstration, not a dependency.
- **genuinely-superseded-because-EVIDENCE** — a replacement decl is named and the need is gone.

Two global facts anchoring the whole cluster (both machine-verified here):

1. All 9 files are `sorry`/`axiom`/`native_decide`-free (`grep` clean; the flagship
   `RealisabilitySpec.lean` is the tree's only sorry-carrier).
2. The flagship does **not** call the cyclic tie-supplied capstones of this cluster
   (`lower_conforms_cyclic'` / `runFrom_of_driveCorr` / `drive_step_block_*` / `driveStep_of_block`
   appear nowhere in `RealisabilitySpec.lean` code — verified empty). The flagship builds its own
   log-indexed `DriveCorrLog` recursion (`RealisabilitySpec.lean:629`) and its central blocker is a
   *new* `runFrom_of_driveCorrLog` that does not yet exist. So the DriveSim cyclic §5–§7 capstones
   are the reference skeleton the flagship reshapes, not its literal dependency.

---

## 1. `Law.lean` — IR-run determinism (frame-free)

Purpose: the "*the* observable" uniqueness half (`docs/ir-design-v3.md` §4 item 2). Structural
induction ladder `EvalStmt.det → RunStmts.det → RunFrom.det → IRRun.det`. Imports only
`Spec.Semantics` (no bytecode). The deleted gas-monotonicity law used to live here (header:17-18).

| decl | kind | role | callers |
|---|---|---|---|
| `EvalStmt.det` (34) | theorem | shared-infra (uniqueness ladder rung) | `RunStmts.det` (Law:71) only |
| `RunStmts.det` (62) | theorem | shared-infra | `RunFrom.det` (Law:89,106,…) only |
| `RunFrom.det` (80) | theorem | shared-infra | `IRRun.det` (Law:170) only |
| `IRRun.det` (167) | theorem | scaffold-support for the worked example | `Call.lean:140` (`call_IRRun_unique`); docstring in `LowerConforms.lean:1159,1185` |

Assessment: the determinism ladder is a self-contained, closed, axiom-clean unit whose only live
external consumer is the worked call example (`Call.lean`). It is the "uniqueness" counterpart to
`IRRun.lean`'s "existence" ladder. Not dead — it realises the §4 headline shape and is cited as
grounding in `LowerConforms` — but its footprint outside `Call.lean` is documentation only.

---

## 2. `IRRun.lean` — IR-run existence ladder + `CFGAcyclic` (frame-free)

Purpose: the constructive "existence" half of `hir` for the gas-free/call-free fragment: single
halt-block base cases, then the general **acyclic** CFG via a static block-rank `CFGAcyclic`. The
header itself scopes it as "the honest tractable floor" (IRRun:35). DriveSim's cyclic `totalGas`
construction later **retires** the acyclic measure (DriveSim:17,54).

| decl | kind | role | callers |
|---|---|---|---|
| `StmtDefinable` (61) | def | genuinely-superseded-because `RealisabilitySpec:215-216` declares it UNSATISFIABLE on gas/call programs and replaces it with `StmtDefinableG` (RS:227) | `StmtsDefinable`, `evalStmt_exists` (this file); `RunDefinable.stmts` |
| `stmtPost` (69) | def | shared-infra (post-state fold) | `stmtsPost`, `evalStmt_exists`; used pervasively in DriveSim `drive_step_block_*` hyps |
| `evalStmt_exists` (79) | theorem | shared-infra | `runStmts_exists` (IRRun:126) only |
| `StmtsDefinable` (106) | def | shared-infra for `RunDefinable` | `runStmts_exists`, `RunDefinable.stmts`; RS:34 docstring |
| `stmtsPost` (112) | def | shared-infra (heavily reused shape) | DriveSim (21 hits: `driveStep_of_block`, all `drive_step_block_*`, `lower_conforms_cyclic'`) |
| `runStmts_exists` (119) | theorem | incremental-toward the log-indexed drive recursion | `driveStep_of_block` (DriveSim:546) |
| `runFrom_exists_stop` (139) | theorem | genuinely-superseded-because the cyclic drive replaces the acyclic base cases; zero callers | none |
| `runFrom_exists_ret` (149) | theorem | genuinely-superseded (as above) | none |
| `irRun_exists_stop` (162) | theorem | genuinely-superseded (as above) | none |
| `irRun_exists_ret` (174) | theorem | genuinely-superseded (as above) | none |
| `TermRankLt` (205) | def | genuinely-superseded-because `CFGAcyclic` retired by `totalGas` (DriveSim:17) | `CFGAcyclic` only |
| `Lir.Term.succs` (212) | def | genuinely-superseded (CFGAcyclic support) | `CFGAcyclic.succ_present`, `runFrom_exists` only |
| `CFGAcyclic` (225) | structure | genuinely-superseded-because DriveSim's dynamic `totalGas` measure "retires it" (DriveSim:17,54; header:29-32); zero code callers (all 11 grep hits are DriveSim docstrings) | none in code |
| `RunDefinable` (258) | structure | genuinely-superseded-because UNSATISFIABLE with gas/call (`RealisabilitySpec:215`), replaced by `RunDefinableG` (RS:240) | `driveStep_of_block`, `lower_conforms_cyclic'` (the vacuous route) |
| `runFrom_exists` (292) | theorem | genuinely-superseded-because the acyclic construction is retired by the cyclic drive | none |
| `irRun_exists` (341) | theorem | genuinely-superseded (as above) | none |

Assessment: this file splits cleanly. The **acyclic construction** (`CFGAcyclic`, `TermRankLt`,
`Term.succs`, `runFrom_exists*`, `irRun_exists*`) is genuinely superseded — DriveSim's own header
says so and nothing cites it. The **definability fold** (`StmtDefinable`/`StmtsDefinable`/`stmtPost`/
`stmtsPost`/`RunDefinable`/`runStmts_exists`) is still called, but only by the DriveSim
`lower_conforms_cyclic'` path, which is itself the superseded vacuous route, and `RunDefinable` is
provably unsatisfiable on the flagship's domain. `stmtsPost`/`stmtPost` are the one part that lives
on as load-bearing shape in the DriveSim per-block bricks.

---

## 3. `Call.lean` — worked external-`Stmt.call` example (frame-free)

Purpose: a hand-assembled one-block program with one external CALL, demonstrating the §7 call
channel (pop the call-stream head, apply as state change) and the "*the* observable" shape on the
call side. Anti-vacuity / documentation artifact.

| decl | kind | role | callers |
|---|---|---|---|
| `tmp`,`lbl` (37,38) | private def | shared-infra (local) | this file |
| `callBlock` (54) | def | scaffold-experimental | `callIR` only |
| `callIR` (62) | def | scaffold-experimental | `example` (Call:67); docstring `DefsSound:124` |
| `callIR_block0` (69) | private theorem | shared-infra (local) | `call_IRRun` |
| `c0`–`c3`, `c2_callee`,`c2_gasFwd`,`c3_result` (74-86) | private def/thm | shared-infra (local) | `call_IRRun` |
| `callObsResult` (96) | def | scaffold-experimental | `call_IRRun`, `call_IRRun_unique` |
| `call_IRRun` (107) | theorem | scaffold-experimental | `call_IRRun_unique` |
| `call_IRRun_unique` (138) | theorem | scaffold-experimental | none |

Assessment: the entire file is a self-contained worked example. `callIR` is referenced only in a
`DefsSound.lean:124` docstring ("`callIR` satisfies it"). Legitimate anti-vacuity demonstration; not
a headline dependency. Note it imports `DefsSound` (bytecode-side) only for the `WellFormed` sanity
`example` at line 67 — the run itself is frame-free.

---

## 4. `CallRealises.lean` — the call realisability bridge (bytecode-coupled)

Purpose: realise an abstract `Lir.CallStream` entry by v1's concrete `evmCallOracle` — the call
analogue of the deleted gas-side `Oracle.lean` `monotoneGas`. Shows the recorded `(world',success)`
entry equals the lowered CALL's observable effect by construction.

| decl | kind | role | callers |
|---|---|---|---|
| `evmV2CallEntry` (59) | def | terminal-for-flagship (the realised call-stream entry) | `realisedCall_cons` (`RecorderLemmas:47`, code); `realisedCall_projection` (SelfPresent:59); RS:1326,1344,2856; LowerConforms:248,257 |
| `callRealises_bridge` (85) | theorem | incremental-toward R3 (`callRealises_of_recorded`, the open call-realisability leaf) | none in code; `RecorderLemmas:41` docstring cites it as the tie the R3 head uses |

Assessment: `evmV2CallEntry` is genuinely load-bearing — it is the definition the recorder's
`realisedCall` projection produces and that R3's call cursor identifies with (RS:2856).
`callRealises_bridge` is a proven, currently-uncited bridge lemma; its stated purpose (`rfl`-clean
`entry = lowered CALL effect`) is exactly what R3 needs, so it is incremental, not dead. Needs
confirmation whether R3 will consume `callRealises_bridge` directly or re-derive via
`call_reflects_lowered`; do not delete.

---

## 5. `Decode/Modellable.lean` — `ModellableStep` producer (bytecode-coupled) — FULLY LIVE

Purpose: discharge the modellability side condition `runs_of_drive_ok` needs (every reachable frame
issues a code CALL or a halt — no CREATE node, no precompile-CALL). Splits: clause 1 (no CREATE)
**structural** for `lower prog`; clause 2 (no precompile-CALL) the honest runtime residual
`CallsCode`. This is the "conformance oracle surface" the flagship consumes.

| decl | kind | role | callers |
|---|---|---|---|
| `currentOp` (65) | def | shared-infra | `stepFrame_needsCreate_isCreate`, `NotCreate`; `NoCreateBytes:389,412` |
| `NoCallCreate` (78) + the 15 `noCallCreate_*` combinator lemmas (83-182) | def/thm | shared-infra (the dispatch no-signal algebra) | `dispatch_needsCreate_isCreate`, `systemOp_isCreate_or_noCreate` |
| `NoCreate` (194), `noCreate_bind/liftOption/callArm` (198-244), `NoCreate.of_noCallCreate` (247) | def/thm | shared-infra (one-sided no-CREATE algebra) | `systemOp_isCreate_or_noCreate` |
| `systemOp_isCreate_or_noCreate` (254) | theorem | shared-infra | `systemOp_needsCreate_isCreate`, `dispatch_needsCreate_isCreate` |
| `systemOp_needsCreate_isCreate` (281) | theorem | shared-infra | `stepFrame_needsCreate_isCreate` (indirect) |
| `dispatch_needsCreate_isCreate` (296) | theorem | shared-infra | `stepFrame_needsCreate_isCreate` |
| `stepFrame_needsCreate_isCreate` (336) | theorem | shared-infra (clause-1 contrapositive) | `modellableStep_of` |
| `beginCall_isCode_of_codeSource_ne_precompiled` (371) | theorem | shared-infra (clause-2) | `modellableStep_of` |
| `NotCreate` (398) | def | shared-infra | `notCreate_of_atReachableBoundary`, `modellableStep_of`; `Seams:77` |
| `AtReachableBoundary` (407) | def | terminal-for-flagship (residual pc-reachability seam) | `RS:1245`, `DriveSim:145`, `BoundaryReach` |
| `notCreate_of_atReachableBoundary` (421) | theorem | terminal-for-flagship (structural no-CREATE discharge) | `lower_modellable`; RS:2422 |
| `CallsCode` (435) | def | terminal-for-flagship (forwarded as `Lir.Spec.CallsCode`, `Seams:81`) | `modellableStep_of`, `lower_modellable`; DriveSim:146 |
| `modellableStep_of` (442) | theorem | shared-infra | `lower_modellable` |
| `lower_modellable` (471) | theorem | terminal-for-flagship | `RS:1255` (code), `DriveSim:158` (`cleanHalts_of_runWithLog`), `BoundaryReach:8` |

Assessment: entirely live. `lower_modellable` is applied directly in the flagship (RS:1255) and its
residual seams `AtReachableBoundary`/`CallsCode` are the honest, satisfiable side conditions the
flagship carries. The long `noCallCreate_*`/`noCreate_*` combinator run is unavoidable
pure-semantics infra proving clause 1 structurally. No simplification here beyond a possible future
graduation of the pure `stepFrame`-signal algebra to exp003.

---

## 6. `DriveSim.lean` — cyclic-CFG drive walk (F1–F3, bytecode-coupled)

Purpose: replace `IRRun.lean`'s static `CFGAcyclic` rank with the **dynamic bytecode `totalGas`**
measure that descends per block regardless of CFG cycles, and glue per-block steps into a whole IR
`RunFrom` (F2 `runFrom_of_driveCorr`), then feed it into `sim_cfg` (F3 `lower_conforms_cyclic`). The
tie-supplied cyclic path is the reference skeleton the flagship's `DriveCorrLog` reshape supersedes.

| decl | kind | role | callers |
|---|---|---|---|
| `DriveCorr` (87) | structure | incremental-toward `DriveCorrLog` (RS:629 reshapes it log-indexed) | `driveCorr_measure` consumers; DriveStep, drive_step_block_*, lower_conforms_cyclic |
| `driveCorr_measure` (97) | theorem | shared-infra (measure collapse) | `totalGas_succ_lt` |
| `cleanHalts_of_runWithLog` (141) | theorem | terminal-for-audit (`Audit:37`) + entry-clean-halt grounding cited by `Seams:89`, `RS:531,1233` | none in flagship code; grounding/audit only |
| `jumpdestFrame_gasToNat` (173) | theorem | shared-infra | `jumpdestFrame_gas_lt` |
| `jumpdestFrame_gas_lt` (184) | theorem | shared-infra | `totalGas_succ_lt` |
| `totalGas_succ_lt` (196) | theorem | incremental-toward the log-indexed recursion (the reused strict descent) | `drive_step_block_jump/branch` |
| `drive_step_block_stop` (226) | theorem | genuinely-superseded-because the flagship reshapes into `DriveCorrLog`-arms; consumed only by the superseded `driveStep_of_block` | `driveStep_of_block` |
| `drive_step_block_ret` (253) | theorem | (as above) | `driveStep_of_block` |
| `drive_step_block_jump` (299) | theorem | (as above) | `driveStep_of_block` |
| `drive_step_block_branch` (382) | theorem | (as above) | `driveStep_of_block` |
| `DriveStep` (461) | def | shared-infra for the cyclic capstone | `driveStep_of_block`, `runFrom_of_driveCorr`, `lower_conforms_cyclic` |
| `driveStep_of_block` (495) | theorem | genuinely-superseded-because it threads the UNSATISFIABLE `RunDefinable` and is not used by the flagship | `lower_conforms_cyclic'` only |
| `runFrom_of_driveCorr` (588) | theorem | LIVE-BUT-SUPERSEDED: the F2 recursion the flagship's `runFrom_of_driveCorrLog` blocker reworks | `lower_conforms_cyclic`; Headline:48 docstring |
| `lower_conforms_cyclic` (624) | theorem | LIVE-BUT-SUPERSEDED (F3, tie-supplied) | `lower_conforms_cyclic'`; `Spec/Conformance` tombstone docstring |
| `lower_conforms_cyclic'` (666) | theorem | genuinely-superseded-because the flagship (RS:3730-3736) explicitly rules out citing it — its unconditional all-frames `SimStmtStep` is unsatisfiable under the reshaped `StmtTies'` | none |

Assessment: F1 measure infrastructure (`driveCorr_measure`, `jumpdestFrame_gas*`, `totalGas_succ_lt`)
and `DriveCorr` are the real, reusable content — the flagship's log-indexed recursion will reuse the
`totalGas` measure. `cleanHalts_of_runWithLog` is the entry-scope-boundary grounding (audit-checked,
cited by Seams). The tie-supplied capstones `driveStep_of_block`/`lower_conforms_cyclic'` are the
vacuous route the flagship deliberately abandons (RS:3730-3736 comment). Borrow from `LowerConforms`:
**`sim_cfg` (LowerConforms:970) and `SimTermStep` (LowerConforms:96)** — the two names that actually
require the heavy import; `Corr`/`SimStmtStep`/`sim_stmts_block`/`corr_at_jumpdest_landing` come
transitively from `SimStmts`/`SimTerm`. The borrow is *not* small — `sim_cfg` is the CFG-assembly
capstone — but it is load-bearing (F3 ties the constructed `RunFrom` to the bytecode world).

---

## 7. `Drive/SelfPresent.lean` — value-channel discharges + `SelfPresent`

Purpose: the recorder/IR-coupled value-channel bridges (CALL/GAS/SLOAD) plus the SSTORE-presence
world invariant `SelfPresent` (§1–§5 of the former `TieDischarge.lean`).

| decl | kind | role | callers |
|---|---|---|---|
| `realisedCall_projection` (55) | theorem | genuinely-superseded-because it is a thin re-export of `realisedCall_cons` (RecorderLemmas:44), which the flagship uses directly (RS:2856); `realisedCall_projection` has zero callers | none |
| `gasRecord_eq_gasReadOf` (71) | theorem | incremental-toward the deferred gas positional-alignment walk | `gasLogAligned_step_gas`, `gasLogAligned_step_gas_seed` (Headline) |
| `gasReadOf_gasFrame_eq_obs` (91) | theorem | incremental-toward gas alignment | `aligned_read_eq_obs`; also `RecorderLemmas`,`StashTail`,`Spec/Recorder` |
| `GasLogAligned` (109) | def | incremental-toward the gas selection channel (R-series) | Headline (`DriveCorrPlus.gasAligned`, snoc/read lemmas) |
| `gasLogAligned_nil` (113) | theorem | incremental (walk seed) | none in code (was `driveCorrPlus_entry`, deleted) |
| `FramesRun.snoc` (118) | theorem | shared-infra | `gasLogAligned_step_gas`, `sloadLogAligned_step_sload`, `FramesRun.snoc_seed` |
| `gasLogAligned_step_gas` (140) | theorem | incremental toward gas alignment | none in code (superseded by `_seed` variant in Headline) |
| `gasLogAligned_step_norecord` (161) | theorem | incremental (identity no-record arm) | none |
| `aligned_read_eq_obs` (181) | theorem | incremental (list→cursor gas read) | `gasRealises_obs_of_witness` |
| `gasRealises_obs_of_witness` (216) | theorem | incremental-toward the single-`obs` gas selection | none in code; `MaterialiseRuns`,`Headline` docstrings |
| `sloadRecord_discharges_obs` (251) | theorem | incremental (SLOAD value bridge) | none |
| `SloadLogAligned` (278) | def | incremental (SLOAD alignment twin) | Headline; `sloadLogAligned_*`, `alignedSload_read_eq_obs` |
| `sloadLogAligned_nil` (282) | theorem | incremental (seed) | none |
| `sloadLogAligned_step_sload` (292) | theorem | incremental | none |
| `alignedSload_read_eq_obs` (308) | theorem | incremental (list→cursor SLOAD) | `sloadRealises_charge_of_witness` |
| `sloadRealises_charge_of_witness` (330) | theorem | incremental-toward SLOAD selection | none in code; `MaterialiseRuns`,`Headline` docstrings |
| `SelfPresent` (364) | def | terminal-for-flagship (SSTORE presence world-invariant) | RS:1397 (hyp), `Seams`, `CallPreservesSelf`, Headline |
| `accounts_ne_empty_of_selfPresent` (379) | theorem | terminal-for-flagship | RS:1484, RS:1723 (code) |
| `resumeAfterCall_self_of_accounts` (392) | theorem | shared-infra (call-resume presence half) | `callPreservesSelf_success` (CallPreservesSelf:155) |
| `selfPresent_codeFrame` (409) | theorem | terminal-for-flagship (entry base case) | RS + `Seams` |

Assessment: two live sub-groups. (a) The **`SelfPresent` family** (`SelfPresent`,
`accounts_ne_empty_of_selfPresent`, `resumeAfterCall_self_of_accounts`, `selfPresent_codeFrame`) is
genuinely wired into the flagship (RS:1397/1484/1723) — the SSTORE-presence discharge. (b) The
**gas/sload positional-alignment machinery** (`GasLogAligned`/`SloadLogAligned` and their step/read
lemmas) is incremental toward the deferred selection channel; it is currently consumed only by
`Drive/Headline.lean`, which is itself unreferenced. It is proven and non-vacuous, and the header
plus the `-- RETAINED for Phase 3 realisability closure (audit §3)` markers name the future
connection, so per the hard-rules it is incremental, not dead. `realisedCall_projection` is the one
clear redundancy (a zero-caller re-export of `realisedCall_cons`).

---

## 8. `Drive/CallPreservesSelf.lean` — `SelfPresent` forward-closed along `Runs`

Purpose: transport `SelfPresent` across a whole `Runs` segment (step edges + returning-CALL resume
nodes), reducing the chain to the single supplied seam `hprec` (precompile no-erase).

| decl | kind | role | callers |
|---|---|---|---|
| `StepPreservesSelf` (74) | def | shared-infra (the step-edge predicate, discharged) | `stepPreservesSelf`, `selfPresent_runs` |
| `stepPreservesSelf` (84) | theorem | terminal-for-audit (`Audit:49`) | `selfPresent_runs_of_call` |
| `CallPreservesSelf` (94) | def | terminal-for-flagship (the CALL-edge seam predicate) | `selfPresent_runs*`, `callPreservesSelf*`, `Seams` |
| `callPreservesSelf_success` (109) | theorem | shared-infra (the `.success` shape via Brick D) | `callPreservesSelf` |
| `callPreservesSelf` (179) | theorem | shared-infra | `callPreservesSelf_modGuards` |
| `callPreservesSelf_modGuards` (214) | theorem | terminal-for-audit (`Audit:29`) + terminal-for-flagship via `Seams:70` (`callPreservesSelf_of_precompiles`) | `Seams:70`; RS:537 docstring |
| `selfPresent_runs` (235) | theorem | shared-infra | `selfPresent_runs_of_call` |
| `selfPresent_runs_of_call` (248) | theorem | terminal-for-flagship | RS:1723 (code), RS:1440 |

Assessment: fully live. The chain collapses to `hprec` (the one honest precompile seam) and is
exported to the flagship two ways: `callPreservesSelf_modGuards` → `Spec.callPreservesSelf_of_precompiles`
(`Seams:68-70`), and `selfPresent_runs_of_call` applied directly at RS:1723. `stepPreservesSelf` and
`callPreservesSelf_modGuards` are both axiom-guarded in `Audit.lean`.

---

## 9. `Drive/Headline.lean` — `DriveCorrPlus` carrier + value/gas channels

Purpose: the strengthened boundary invariant `DriveCorrPlus` (alignment + presence carrier over
`DriveCorr`) plus the cursor-local value/gas-channel lemmas. The header (Headline:17-25) records
that §9/§10 (the edge wrappers + `DriveCorrPlus` recursion + `lower_conforms_cyclic_assembled`) were
**deleted 2026-07-03** as vacuous surface, and the survivors are "RETAINED as the green machinery
its R0 reshape starts from (currently unreferenced in the default build)."

| decl | kind | role | callers |
|---|---|---|---|
| `DriveCorrPlus` (81) | structure | incremental-toward the R0 reshape (header-stated) | none (its entry/recursion were the deleted vacuous apparatus) |
| `memRealises_setLocal_nonspilled` (138) | theorem | incremental-toward S7 (assign-remat channel) | `driveCorrPlus_assign_remat_memRealises` |
| `driveCorrPlus_assign_remat_memRealises` (162) | theorem | incremental-toward S7 (Route-4b indexed form) | none |
| `driveCorrPlus_sload_value` (182) | theorem | incremental-toward S2 (sload value channel) | none |
| `driveCorrPlus_sload_value_world` (193) | theorem | incremental-toward S2 | none |
| `FramesRun.snoc_seed` (233) | theorem | incremental (seedable gas snoc) | `gasLogAligned_step_gas_seed` |
| `gasLogAligned_step_gas_seed` (251) | theorem | incremental (S3 gas advance) | none |
| `GasReach` (269) | def | incremental (per-cursor gas reachability) | `GasReach.trans` |
| `GasReach.trans` (273) | theorem | incremental | none |
| `GasCursorClass` (291) | inductive | incremental (per-cursor gas dispatch) | none |

Assessment: the entire file is currently unreferenced (every decl has zero external callers;
verified by grep). This is not dead code by the hard-rules: the header explicitly designates it as
the retained green salvage for the R0 realisability reshape, after the vacuous headline apparatus
around it was deleted. It is the highest-risk "is this still on the roadmap?" file in the cluster —
flag for confirmation, not deletion.

---

## 10. Internal sub-DAG and cross-cluster edges

Intra-cluster dependency (module → module it consumes decls from):

```
Law  ──────────────► (nothing in-cluster; base)
IRRun ── imports ──► Law           (existence ladder mirrors Law's determinism ladder)
Call  ── imports ──► Law           (uses IRRun.det for call_IRRun_unique)
CallRealises ─────► (Call, Match)  ; evmV2CallEntry def consumed OUT of cluster (RecorderLemmas)
Modellable ───────► (DriveRuns, NoCreateBytes)  ; self-contained producer
DriveSim ─ borrows ► IRRun (runStmts_exists, RunDefinable, stmtsPost)
          ─ borrows ► Modellable (lower_modellable → cleanHalts_of_runWithLog)
          ─ borrows ► LowerConforms (sim_cfg, SimTermStep) + transitively Corr/SimStmtStep/…
Drive/SelfPresent ► (RecorderLemmas, MaterialiseRuns, AccountMap)  ; CallRealises via evmV2CallEntry
Drive/CallPreservesSelf ─ imports ► Drive/SelfPresent (SelfPresent, resumeAfterCall_self_of_accounts)
                         ─ imports ► BytecodeLayer/Hoare/DriveMono (Brick D)
Drive/Headline ─ imports ► DriveSim (DriveCorr) + Drive/CallPreservesSelf (SelfPresent, alignment)
```

Exit edges (cluster decls consumed by the flagship / audit / Spec):

- **to `RealisabilitySpec` (flagship, code):** `lower_modellable`, `AtReachableBoundary`,
  `SelfPresent`, `accounts_ne_empty_of_selfPresent`, `selfPresent_codeFrame`,
  `selfPresent_runs_of_call`, `evmV2CallEntry` (via `realisedCall_cons`).
- **to `Spec/Seams.lean` (forwarders the flagship cites):** `CallsCode` (→ `Spec.CallsCode`),
  `callPreservesSelf_modGuards` (→ `Spec.callPreservesSelf_of_precompiles`); `cleanHalts_of_runWithLog`
  cited as entry-clean-halt grounding.
- **to `Audit.lean` (`#print axioms`):** `callPreservesSelf_modGuards`, `cleanHalts_of_runWithLog`,
  `stepPreservesSelf`.

Entry edges (cluster consumes from outside): `Spec.Semantics`/`Spec.IR` (Law/IRRun);
`Match`/`Call`/`DefsSound` (CallRealises, Call); `LowerConforms`/`SimStmts`/`SimTerm`
(DriveSim's `sim_cfg`/`Corr` tower); `RecorderLemmas`/`MaterialiseRuns`/`BytecodeLayer/Hoare/AccountMap`
(SelfPresent); `BytecodeLayer/Hoare/DriveMono` Brick D (CallPreservesSelf); `BytecodeLayer/Hoare/DriveRuns`/`NoCreateBytes`
(Modellable).

---

## 11. SIMPLIFICATION CANDIDATES (evidence-backed only)

1. **`realisedCall_projection` (SelfPresent.lean:55) — redundant re-export.** Its body is literally
   `realisedCall_cons self hc` (SelfPresent:59); `realisedCall_cons` (RecorderLemmas:44) is what the
   flagship actually uses (RS:2856, 1326, 1344). `realisedCall_projection` has zero callers. Safe to
   inline/drop once confirmed no external doc depends on the name.

2. **The acyclic construction in `IRRun.lean` — genuinely superseded, ~150 LOC.**
   `CFGAcyclic`, `TermRankLt`, `Term.succs`, `runFrom_exists_stop/ret`, `irRun_exists_stop/ret`,
   `runFrom_exists`, `irRun_exists` have zero code callers, and DriveSim's header (17,54) plus the
   dynamic `totalGas` measure explicitly "retire" the static block-rank. These are provably
   dead-for-the-headline. Caveat: keep the definability fold (`StmtDefinable`/`StmtsDefinable`/
   `stmtsPost`/`stmtPost`) — it still backs the DriveSim per-block bricks and inspired
   `StmtDefinableG`. Recommend: delete the acyclic-CFG half only.

3. **`RunDefinable` + `lower_conforms_cyclic'` route — superseded vacuous path.** `RealisabilitySpec:215`
   declares `RunDefinable` UNSATISFIABLE on gas/call programs (replaced by `RunDefinableG`), and
   `RS:3730-3736` explicitly refuses to cite `lower_conforms_cyclic'`. `driveStep_of_block` +
   `lower_conforms_cyclic'` exist only to feed each other. Needs-confirmation before removal: whether
   the DriveCorrLog reshape wants `driveStep_of_block` as a template; the *measure* lemmas
   (`totalGas_succ_lt` et al.) and `DriveCorr`/`drive_step_block_*` should be kept as the reshape
   skeleton. Flag `lower_conforms_cyclic'` specifically as the safest removal.

4. **`Drive/Headline.lean` — entirely unreferenced (needs confirmation, do NOT delete).** Every decl
   has zero callers. The header designates it retained salvage for the R0 reshape. This is a roadmap
   question, not a dead-code finding: confirm with the lead whether the gas/sload selection channel
   (also the `GasLogAligned`/`SloadLogAligned` cluster in `SelfPresent.lean` §3-§4) is still the plan
   before touching it. If R-series realisability is dropped, this file + the alignment machinery in
   SelfPresent §3-§4 become the largest single simplification (~200 + ~230 LOC).

5. **`cleanHalts_of_runWithLog` framing.** It is not called in flagship code (only audit + Seams
   grounding). This is correct-as-is (it is the axiom-checked grounding lemma), listed here only to
   note it is *not* a live proof dependency of the flagship — do not mistake it for one.
