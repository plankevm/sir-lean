# Deep-dive cluster: CFG assembly

Files: `LirLean/LowerDecode.lean`, `LirLean/LowerConforms.lean`, `LirLean/Acyclic.lean`,
`LirLean/RecorderLemmas.lean`.

Read-only audit, 2026-07-04. Every "callers" cell was checked with repo-wide
`grep -rn` over `LirLean/`, not the import graph. `LirLean` is the sorry-free default lib;
`WIP` is the one-file `RealisabilitySpec.lean` sorry-carrier lib (`lakefile.lean:31-32`). A
caller in `RealisabilitySpec.lean` therefore means "consumed by the WIP flagship", a caller in
`DriveSim.lean` / `SelfPresent.lean` means "consumed by the default build".

> **P8 status note (2026-07-08).** This cluster audit predates the P8 well-formedness reshaping.
> `Acyclic.lean` / `MatFueled` / `AcyclicWellFormed` no longer discharge the live
> `WellFormedLowered` bundle. `WellFormedLowered` is now fuel-free over `matCache` lengths and
> fold offsets; the remaining rank/fuel file is a P9 deletion target.

## What this cluster is for (grounded in the plan)

This is **Layer F assembly** of the world-channel `lower_conforms` grind. Three jobs:

1. **`LowerDecode.lean`** — takes the per-shape simulation bricks from Layers C/E
   (`sim_sstore_stmt`, `sim_term_*`, `sim_assign_gas`, `sim_assign_sload`), which carry their
   per-cursor *decode* facts as structured hypotheses, and **discharges those decode
   hypotheses generically over `lower prog`** by reading them off the `emitStmt`/`emitTerm`
   byte layout. Output: the `_lowered` wrappers plus a set of reusable low-level decode helpers
   (immediate round-trips, `term_dest_decode`, `decode_gasstash`, `decode_sloadstash`) and two
   `*_landing_of_cleanHalt` pre-JUMPDEST producers.
2. **`LowerConforms.lean`** — hosts the two per-block abstraction structures
   (`SimStmtStep` lives in `SimStmts.lean`; `SimTermStep`/`WellFormedLowered`/`CallRealises`
   live here), the whole-CFG induction `sim_cfg`, the entry-correspondence builder `entry_corr`,
   the per-shape **builders** that discharge `SimStmtStep`/`SimTermStep` from `WellFormedLowered`
   + the §7 ties, and the **older acyclic capstone** `lower_conforms`.
3. **`Acyclic.lean`** — legacy generic-`defs` rank/fuel support retained only until P9 deletes
   `materialiseExpr`/`MatFueled`; it is no longer the live R9 route into `WellLowered`.
4. **`RecorderLemmas.lean`** — the proof companions of the recording interpreter: the
   SLOAD/CALL value-level bridges and the `driveLog → runWithLog → messageCall` adequacy chain.

The load-bearing architectural fact this cluster exposes: **there are two parallel discharge
paths.** (a) the *builder path* in `LowerConforms` (`sim*_lowered` wrappers →
`simStmtStep_block`/`simTermStep_block` → `SimStmtStep`/`SimTermStep`), which fed the acyclic
capstone and still feeds the cyclic `lower_conforms_cyclic` (DriveSim); and (b) the *flagship
path* in `RealisabilitySpec.lean` (WIP), which **re-implements the same walk inline** with
shadowing-aware S-variants (`CallRealisesS`, `StepScopedS`, …) and consumes only the low-level
helpers, never the builders. `RealisabilitySpec` calls `term_dest_decode`, `ofNatMod_toUInt32?`,
`ret_sub_value`, `decode_gasstash`, `toList_of_blockAt`, `codeFrame_*` directly, but calls
**none** of `simStmtStep_block`/`simTermStep_block`/`simTermStep_stop|ret|jump|branch`/
`simStmtStep_call`/`sim_*_lowered`/`decode_sloadstash` (verified by grep of `LirLean/V2/`).

---

## LowerDecode.lean — per-decl

| decl (line) | kind | role | callers |
|---|---|---|---|
| `sstore_sub_value` (34) | theorem | shared-infra: sstore value operand is prefix sub-list | `LowerDecode:173` (in `sim_sstore_stmt_lowered`) |
| `sstore_sub_key` (46) | theorem | shared-infra: sstore key operand sub-list at offset lv | `LowerDecode:180` (in `sim_sstore_stmt_lowered`) |
| `assign_sload_sub_key` (68) | theorem | genuinely-superseded: the planned sload-key sub-list fact (twin of `sstore_sub_*`) | **none anywhere** — the sload arm builds its key segment inline via `MatSeg`/`hsegk` in `sim_assign_sload_lowered:1467` and `decode_sloadstash`, so this twin was never wired |
| `sstore_op_decode` (95) | theorem | shared-infra: SSTORE opcode decode at lv+lk | `LowerDecode:187` (in `sim_sstore_stmt_lowered`) |
| `sim_sstore_stmt_lowered` (134) | theorem | incremental-toward builder path (sstore arm of `simStmtStep_block`) | `LowerConforms:539` only |
| `ret_sub_value` (207) | theorem | shared-infra: ret operand prefix sub-list | `LowerDecode:288` (in `sim_term_halt_ret_lowered`); **`RealisabilitySpec:1499`** (flagship) |
| `sim_term_halt_ret_lowered` (229) | theorem | incremental-toward builder path (ret arm of `simTermStep_ret`) | `LowerConforms:665` only |
| `fromBytes_offsetBytesBE` (309) | theorem | shared-infra: 4-byte BE immediate low-32 | `LowerDecode:321` (in `uInt256_offsetBytesBE`) |
| `uInt256_offsetBytesBE` (318) | theorem | shared-infra: PUSH4 immediate round-trip | `LowerDecode:394` (in `term_dest_decode`) |
| `ofNatMod_toUInt32?` (325) | theorem | shared-infra: the `hdestword` offset tie | `LowerDecode` (jump/branch wrappers); **`RealisabilitySpec:1754,1898,1899`** (flagship) |
| `term_dest_decode` (354) | theorem | shared-infra: PUSH4 destination decode at a term offset | `LowerDecode` (jump/branch wrappers + `jump_landing`); **`RealisabilitySpec:1741,1847,1872`** (flagship) |
| `sim_term_edge_jump_lowered` (417) | theorem | incremental-toward builder path (jump arm of `simTermStep_jump`) | `LowerConforms:728` only |
| `jump_landing_of_cleanHalt` (486) | theorem | scaffold/vestigial: the pre-JUMPDEST landing producer built for the deleted `Plus` thread | **no `.lean` call**; only `Audit.lean` (#print axioms) + `RealisabilitySpec` docstrings (:683/:1437 as a "pattern" the flagship re-implements inline) |
| `sim_term_edge_branch_lowered` (620) | theorem | incremental-toward builder path (branch arm of `simTermStep_branch`) | `LowerConforms:806,816` only |
| `branch_landing_of_cleanHalt` (769) | theorem | scaffold/vestigial: branch analogue of the landing producer for the deleted `Plus` thread | **no `.lean` call**; `Audit.lean` + `RealisabilitySpec` docstrings (:683/:899/:1437/:1450 as re-implemented "pattern") |
| `decode_gasstash` (1090) | theorem | shared-infra: 3 GAS-stash decode anchors | `LowerConforms:529` (builder path); **`RealisabilitySpec:2597`** (flagship) |
| `sim_assign_gas_lowered` (1167) | theorem | incremental-toward builder path (gas arm of `simStmtStep_block`) | `LowerConforms:533` only |
| `decode_sloadstash` (1272) | theorem | incremental-toward builder path (sload tail anchors) | `LowerConforms:483` and inside `sim_assign_sload_lowered:1484` only |
| `sim_assign_sload_lowered` (1379) | theorem | incremental-toward builder path (sload arm of `simStmtStep_block`) | `LowerConforms:478` only; tracked by `Audit.lean` #print axioms |

Note on the two `*_landing_of_cleanHalt`: their own docstrings say they build "exactly the
headline `hjump`/`hbranch` bundle … the `Plus` thread needs the pre-step landing". The `Plus`
assembly was deleted 2026-07-03 (final-audit). The flagship now re-derives the same PUSH4 ;
J{UMP,UMPI} ; JUMPDEST landing walk **inline** in `RealisabilitySpec` (~:1741-1899, citing these
as "patterns" in comments) rather than calling them. So they are green, axiom-clean (Audit guard),
but currently orphaned scaffolding — see candidates.

## LowerConforms.lean — per-decl

| decl (line) | kind | role | callers |
|---|---|---|---|
| `SimTermStep` (96) | structure | shared-infra: per-terminator sim bundle consumed by `sim_cfg` | `sim_cfg`; **`DriveSim:639,681`** (`lower_conforms_cyclic`/`'`) |
| `WellFormedLowered` (143) | structure | shared-infra: folded structural side-conditions, P8 fuel-free over fold layout | builders here; **`RealisabilitySpec` internal `WellLowered.wf` adapter** |
| `CallRealises` (263) | def | shared-infra: §7 CALL realisability tie | `simStmtStep_call`; **`RealisabilitySpec:392` builds `CallRealisesS` around it, `:789`, `:1319`** |
| `simStmtStep_call` (337) | theorem | incremental-toward builder path (call arm) | `LowerConforms:545` (`simStmtStep_block`) only |
| `simStmtStep_block` (374) | theorem | builder: `WellFormedLowered`+§7 ties ⇒ `SimStmtStep` | **none** — top of builder path, no caller in tree |
| `simTermStep_stop` (562) | theorem | incremental-toward builder path | `LowerConforms:935` (`simTermStep_block`) only |
| `simTermStep_ret` (615) | theorem | incremental-toward builder path | `LowerConforms:936` only |
| `simTermStep_jump` (686) | theorem | incremental-toward builder path | `LowerConforms:939` only |
| `simTermStep_branch` (748) | theorem | incremental-toward builder path | `LowerConforms:943` only |
| `simTermStep_block` (833) | theorem | builder: ⇒ `SimTermStep` | **none** — top of builder path, no caller in tree |
| `sim_cfg` (970) | theorem | terminal-for-flagship spine: whole-CFG world-channel simulation | **`DriveSim:648`** (`lower_conforms_cyclic`, default build); acyclic capstone `:1232` |
| `codeFrame_pc` (1057) | theorem | shared-infra | `entry_corr:1124`; **`RealisabilitySpec:2283`** |
| `codeFrame_stack` (1060) | theorem | shared-infra | `entry_corr:1128` only |
| `codeFrame_code` (1063) | theorem | shared-infra | `entry_corr:1125`; **`RealisabilitySpec:2282`** |
| `codeFrame_canMod` (1066) | theorem | shared-infra | `entry_corr:1129` only |
| `codeFrame_gas` (1069) | theorem | shared-infra | `entry_corr:1135` only |
| `codeFrame_validJumps` (1072) | theorem | shared-infra | `entry_corr:1126`; **`RealisabilitySpec:2315`** |
| `entry_storageAgree_codeFrame` (1089) | theorem | shared-infra: canonical `w₀` choice discharging entry `StorageAgree` | **none anywhere** (see candidates) |
| `entry_corr` (1102) | theorem | incremental-toward flagship entry (R7): builds `Corr … prog.entry 0` | `LowerConforms:1226` (acyclic capstone); referenced by `RealisabilitySpec` docstrings :162/:626 as the R7 mechanism, no call yet |
| `lower_conforms` (1188) | theorem | genuinely-superseded: the older acyclic capstone | **zero callers** (superseded by `V2.lower_conforms`, RealisabilitySpec:3705) |
| `toList_of_blockAt` (1252) | theorem | shared-infra | **`RealisabilitySpec:1119,1479,2597`** |

## Acyclic.lean — per-decl

| decl (line) | kind | role | callers |
|---|---|---|---|
| `ExprRankLt` (57) | def | shared-infra: fuel-need rank bound | `Acyclic` (self); **`RealisabilitySpec:3304`** (exProg discharge) |
| `ExprRankLt.mono` (68) | theorem | legacy fuel support | `Acyclic` in-file only |
| `Acyclic` (82) | def | legacy generic-`defs` rank predicate | residual fuel support until P9 |
| `matFueled_of_exprRankLt` (93) | theorem | legacy fuel core | `Acyclic` in-file only |
| `matFueled_tmp_of_acyclic` (133) | theorem | legacy fuel core | `Acyclic` in-file only |
| former `AcyclicWellFormed` (152) | structure | superseded acyclicity + bounds bundle | P8 replaced by `IRWellFormed` + budgets |
| former `wellFormedLowered_of_acyclic` (204) | theorem | superseded route into `WellFormedLowered` | P8 replaced by `wellLowered_of_IRWellFormed` |

All of `Acyclic.lean` is reachable from the flagship's `exProg` witness (R9). Its own header
(`:41-43`) says the core is "currently unreferenced in the default build (its only consumers were
the deleted headlines)" — **that is now stale**: `RealisabilitySpec` (WIP lib) consumes every
public decl. Technically true only if "default build" excludes WIP.

## RecorderLemmas.lean — per-decl

| decl (line) | kind | role | callers |
|---|---|---|---|
| `sloadRecord_eq_sloadCost` (31) | theorem | shared-infra: SLOAD value bridge | **`SelfPresent:256,318`** (default); flagship docstrings |
| `realisedCall_cons` (44) | theorem | shared-infra: `realisedCall` head/cons projection | **`SelfPresent:59`** (default); `RealisabilitySpec:1326,1344,2856` |
| `driveLog_drive` (62) | theorem | shared-infra: recorder result adequacy vs `drive` | `RecorderLemmas:134` (in `runWithLog_drive`); **`RealisabilitySpec:2790,2883`** |
| `runWithLog_drive` (117) | theorem | shared-infra: adequacy vs `drive` | **`DriveSim:149`** (default); `BytecodeLayer/Hoare/DriveRuns`; `RealisabilitySpec:1249,3671,3720,3770,3807` |
| `runWithLog_messageCall` (143) | theorem | genuinely-superseded-candidate: adequacy vs `messageCall` | **only `LowerConforms:1238`, inside the dead acyclic capstone** |

---

## Internal sub-DAG and edges to other clusters

Module import order inside the cluster: `Acyclic → LowerConforms → LowerDecode`
(`Acyclic` imports `LowerConforms`; `LowerConforms` imports `LowerDecode` + `CleanHaltExtract`;
`LowerDecode` imports `MatDecLower`/`SimStmt`/`SimTerm`/`StashTail`/`CleanHaltExtract`).
`RecorderLemmas` is off to the side (imports only `Spec/Recorder`).

Internal call edges (decl-level):

```
LowerDecode:
  fromBytes_offsetBytesBE → uInt256_offsetBytesBE → term_dest_decode
  sstore_sub_{value,key}, sstore_op_decode → sim_sstore_stmt_lowered
  ret_sub_value → sim_term_halt_ret_lowered
  ofNatMod_toUInt32?, term_dest_decode → sim_term_edge_{jump,branch}_lowered, {jump,branch}_landing_of_cleanHalt
  decode_gasstash → sim_assign_gas_lowered
  decode_sloadstash → sim_assign_sload_lowered
  (assign_sload_sub_key: no out-edges, no in-edges — isolated)

LowerConforms builder path (self-contained, no external caller at the top):
  sim_sstore_stmt_lowered ─┐
  sim_assign_gas_lowered   ├→ simStmtStep_block   (top; uncalled)
  sim_assign_sload_lowered ┘   ← simStmtStep_call
  sim_term_halt_ret_lowered → simTermStep_ret     ─┐
  sim_term_edge_jump_lowered → simTermStep_jump    ├→ simTermStep_block (top; uncalled)
  sim_term_edge_branch_lowered → simTermStep_branch┤
  (simTermStep_stop)                               ┘
  codeFrame_* → entry_corr

LowerConforms acyclic capstone (dead):
  entry_corr, sim_cfg, runWithLog_messageCall, messageCall_runs → lower_conforms(:1188)   (zero callers)

Acyclic (legacy fuel stack): ExprRankLt(.mono), Acyclic → matFueled_of_exprRankLt →
  matFueled_tmp_of_acyclic. The old `AcyclicWellFormed → wellFormedLowered_of_acyclic` route is
  superseded by P8's `wellLowered_of_IRWellFormed`.

RecorderLemmas: driveLog_drive → runWithLog_drive → runWithLog_messageCall
```

**Exit edges (this cluster → live consumers):**

- `sim_cfg`, `SimTermStep`, `SimStmtStep` (imported struct) → **DriveSim** `lower_conforms_cyclic`/`'` (default build, the cyclic-but-superseded headline).
- `WellFormedLowered`, `CallRealises`, `entry_corr`(doc), `toList_of_blockAt`,
  `codeFrame_{pc,code,validJumps}`, `term_dest_decode`, `ofNatMod_toUInt32?`,
  `ret_sub_value`, `decode_gasstash` → **RealisabilitySpec** (WIP flagship + inline walk).
  The old `AcyclicWellFormed` / `wellFormedLowered_of_acyclic` witness route is superseded.
- `sloadRecord_eq_sloadCost`, `realisedCall_cons` → **SelfPresent** (R-leaf machinery).
- `runWithLog_drive`, `driveLog_drive` → **DriveSim**, **BytecodeLayer/Hoare/DriveRuns**, flagship.

**Entry edges (external → this cluster):** the `sim_*` bricks (`sim_sstore_stmt`, `sim_term_*`,
`sim_assign_gas`, `sim_assign_sload`, `sim_call_stmt`, `sim_stmts_block`) from
`SimStmt`/`SimTerm`/`SimStmts`; the decode anchors from `MatDecLower`/`DecodeAnchors`; the
clean-halt extractors from `CleanHaltExtract`; the recorder defs from `Spec/Recorder`.

---

## SIMPLIFICATION CANDIDATES

Ordered by confidence. All are read-only observations; none applied.

1. **`Lir.lower_conforms` (LowerConforms.lean:1188, ~63 LOC) — dead, safe to delete.**
   Zero callers (grep confirms only docstring self-references and the unrelated
   `V2.lower_conforms`). It is the older acyclic capstone; its exact job (runWithLog → world
   equation) is now done by the flagship `V2.lower_conforms` (RealisabilitySpec:3705) and, over
   cyclic CFGs, by `lower_conforms_cyclic`. Matches the plan-of-record's "delete dead acyclic
   capstone" (lirlean-dag-2026-07-04). Deleting it also strands `runWithLog_messageCall` and
   `messageCall_runs` (see #2).

2. **`runWithLog_messageCall` (RecorderLemmas.lean:143) — superseded-candidate.** Its only
   caller is the dead acyclic capstone (#1). The live/flagship path uses `runWithLog_drive`
   instead. Needs confirmation that no planned headline re-adds a `messageCall`-bridge assembly;
   if #1 is deleted, this becomes dead. Conservative: delete only together with #1.

3. **`assign_sload_sub_key` (LowerDecode.lean:68) — superseded, orphaned.** Zero callers
   anywhere (verified incl. within `LowerDecode`). It is the planned twin of the used
   `sstore_sub_value`/`sstore_sub_key`, but the sload arm derives its key segment inline
   (`hsegk`/`MatSeg` in `sim_assign_sload_lowered:1467`, and `decode_sloadstash`), so the twin was
   never wired. Safe to delete.

4. **`entry_storageAgree_codeFrame` (LowerConforms.lean:1089) — orphaned helper.** Zero callers.
   `entry_corr` takes `hstore : StorageAgree …` as a hypothesis rather than calling this canonical
   choice. It documents "choose `w₀ := selfStorage (codeFrame …)`" but nothing consumes it.
   Needs confirmation it is not intended as the flagship's entry `w₀` supply (R7); if the flagship
   supplies `w₀` differently, delete.

5. **`jump_landing_of_cleanHalt` / `branch_landing_of_cleanHalt` (LowerDecode.lean:486, 769,
   ~110+~300 LOC) — vestigial `Plus`-thread scaffolding; needs confirmation.** No `.lean` call
   (only `Audit.lean` axiom guards + `RealisabilitySpec` docstrings that cite them as re-implemented
   "patterns"). Their docstrings tie them to the deleted `Plus` thread. The flagship re-derives the
   same landing walk inline (RealisabilitySpec ~:1741-1899). **However** they are non-trivial,
   green, axiom-clean, and their inline twins in the WIP file are inside a sorry-carrier: if the
   flagship's landing walk is later factored back out, these are the natural home. Flag as
   "confirm whether the flagship will cite them; otherwise they are the strongest dedup target in
   the cluster." Do NOT delete blind.

6. **The whole builder path — `simStmtStep_block`/`simTermStep_block` and their feeders
   (`simTermStep_stop|ret|jump|branch`, `simStmtStep_call`, the four `sim_*_lowered` wrappers,
   `decode_sloadstash`, `sim_assign_gas_lowered`, `sim_assign_sload_lowered`) — NOT a delete
   candidate; flagged only as needs-confirmation.** `simStmtStep_block`/`simTermStep_block` have
   zero callers, and the flagship discharges `SimStmtStep`/`SimTermStep` via a parallel inline
   S-variant walk instead of these builders. BUT: (a) `SimStmtStep`/`SimTermStep` are still
   consumed by `lower_conforms_cyclic` in the default build; (b) these builders are the documented
   general/`∀ SoundAlloc` discharge path (Phase D, "designed, not yet landed"); (c) they are green.
   Per the default-incremental rule these are "incremental toward a general SimStmtStep/SimTermStep
   discharge, currently only exercised on the superseded cyclic route." Recommendation: revisit
   only after the flagship's coupled run-producer blocker resolves and it is decided whether the
   general headline reuses these builders or the S-variant walk becomes canonical.

7. **Stale comment (not code): Acyclic.lean:41-43** claims the acyclicity core "is currently
   unreferenced in the default build (its only consumers were the deleted headlines)." Every public
   decl is now consumed by `RealisabilitySpec` (WIP). Reword to "consumed by the WIP flagship's
   `exProg`/R9 witness" to avoid a future reviewer mistaking it for dead. (Comment-only.)
