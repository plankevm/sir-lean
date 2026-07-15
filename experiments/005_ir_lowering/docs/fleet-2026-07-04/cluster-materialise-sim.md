# Fleet audit 2026-07-04 — cluster: Materialise + gas-aware Simulation bricks + CALL/CREATE oracles

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


> **P9 status note (2026-07-08).** This audit predates the Phase 2A deletion pass. Legacy
> `Expr.slot`/fuel/materialisation references are historical; current code uses the fold-based
> `Loc`/`matCache` value channel and the old `MatFueled`/`Assembly/Acyclic.lean` route is gone.

Scope: 14 files, **7084 LOC total**. This cluster is the bulk of the gas-aware simulation
stack (stack (a) in the two-stacks picture). The audit question is: how much of it feeds
**only** the doomed acyclic `LowerConforms` path vs. is genuinely reused by the surviving
cyclic flagship (`RealisabilitySpec.lean`, the WIP sorry-carrier).

## Key finding up front

The cluster splits almost exactly in half by the acyclic/cyclic seam:

* **~3347 LOC genuinely reused** by the cyclic flagship via two entry points:
  `Lir.Drive.SelfPresent → MaterialiseRuns` and `Lir.CallRealises → Match` (plus
  `Lir.Call → DefsSound`). Transitive closure of those pulls in
  MaterialiseRuns, MaterialiseGas, Match, SmallStep, Call, StorageErase, DefsSound.
* **~3627 LOC acyclic-only** — reachable from the flagship *only* through
  `LowerConforms → LowerDecode`: MaterialiseCleanHalt, MatDecLower, StashTail, SimStmt,
  SimStmts, SimTerm. If the acyclic `LowerConforms` path dies, these orphan wholesale.
* **110 LOC vestigial NOW** regardless of the acyclic decision: `Create.lean` has **zero
  importers** (only the root aggregate `LirLean.lean:22`).

## 1. Per-file table

| File | LOC | One-line purpose | Key exports | Feeds | Verdict | Simplification note |
|------|-----|------------------|-------------|-------|---------|---------------------|
| MaterialiseRuns.lean | 1372 | B1 linchpin: lowered `materialiseExpr` push-seq reproduces `evalExpr` value + storage/gas envelope | `materialise_runs` (`:771`), `MatRuns` (`:336`), `MatDec` (`:237`), `StorageAgree` (`:565`), `MemRealises` (`:605`), `SloadRealises`/`GasRealises` (regression witnesses `:536`/`:557`) | **both** (cyclic via `SelfPresent`) | load-bearing | gas half (`hgas`, chargeOf conjunct) may be unused by `SelfPresent`; see §3 |
| MaterialiseGas.lean | 289 | B2 gas-charge engine: `chargeOf` list + `subCharges` algebra mirroring `materialiseExpr` | `chargeOf` (`:73`), `MaterialiseGasCharge` (`:250`), `subCharges_chargeOf_binop` (`:159`), `charge_runs_imm` (`:194`) | **both** (only via MaterialiseRuns) | support | pure gas; only consumed by B1's gas conjunct + the acyclic clean-halt fold. Merge candidate into MaterialiseRuns; strandable if gas conjunct dropped |
| MaterialiseCleanHalt.lean | 404 | Gas-dropping twin of B1: derive charge envelope from `CleanHaltsNonException` instead of taking it supplied | `materialise_charge_le_of_cleanHalt` (`:66`), `materialise_runs_of_cleanHalt` (`:377`) | **acyclic-only** (importer: SimStmt) | legacy | orphans if acyclic dies; exists only to feed the SSTORE/SLOAD §7 ties |
| MatDecLower.lean | 516 | A→B1 bridge: reconstruct the `MatDec` decode bundle generically over `lower prog` | `matDec_of_lower` (`:452`), `matDec_of_term` (`:498`), `uInt256_wordBytesBE` (`:123`), `MatSeg` (`:210`) | **acyclic-only** (importers: LowerDecode, CleanHaltExtract) | legacy | orphans if acyclic dies. `uInt256_wordBytesBE` (PUSH32 round-trip) is a reusable 256-bit fact worth rescuing |
| StashTail.lean | 519 | Uniform spill stash-tail forward `Runs` lemma (`PUSH slot; MSTORE`) | `stash_tail_runs` (`:156`), `stash_tail_runs_covered` (`:256`), `stash_tail_gas` (`:320`), `stash_tail_sload` (`:421`) | **acyclic-only** (importers: LowerDecode, SimTerm) | legacy | orphans if acyclic dies; the "uniform spill" keystone the acyclic path was built around |
| SmallStep.lean | 131 | IR small-step operational state (`IRState`, `evalExpr`, halt) — the Match-layer IR | `IRState` (`:49`), `evalExpr` (`:89`), `HaltResult`/`IRConf` (`:60`/`:69`), `IRState.applyCall`-support | **both** (via Match) | load-bearing | NB: this `IRState` is distinct from the flagship's `Lir.IRState`; two IR-state defs coexist (consolidation lever, §3) |
| Match.lean | 595 | `Match` invariant + per-construct frame-local sim bricks (`sim_imm/add/lt/sload/sstore/call`) | `Match` (`:125`), `sim_imm`/`sim_add`/`sim_sload`/`sim_sstore`/`sim_call` (`:150`+), `call_reflects_oracle` (`:519`), `pcOf` (`:66`) | **both** (cyclic via `CallRealises`) | load-bearing | the sim-brick library both stacks lean on |
| SimStmt.lean | 1187 | Layer C: per-statement simulation, the `Corr` bundle + assign/sstore/call/gas/sload arms | `sim_assign`/`sim_sstore_stmt`/`sim_call_stmt` (`:200`/`:346`/`:576`), `sim_assign_gas` (`:893`), `sim_assign_sload` (`:1055`), `Corr` (`:103`) | **acyclic-only** (importers: LowerDecode, SimStmts) | legacy | largest orphan; the whole gas-aware `Corr` per-statement engine |
| SimStmts.lean | 163 | Layer D: glue `sim_stmt` along a statement list | `sim_stmts`/`sim_stmts_block` (`:132`/`:149`), `SimStmtStep` (`:66`) | **acyclic-only** (importer: SimTerm) | legacy | tiny; merge into SimStmt if kept at all |
| SimTerm.lean | 838 | Layer E: block-terminator simulation (halt / edge to successor) | `sim_term_halt_stop`/`_ret` (`:262`/`:310`), `sim_term_edge_jump`/`_branch` (`:623`/`:666`), `jump_to_block` (`:539`) | **acyclic-only** (importer: LowerDecode) | legacy | orphans if acyclic dies |
| Call.lean | 164 | Abstract `CallOracle` + `evmCallOracle` instantiation + `applyCall` | `CallOracle` (`:79`), `evmCallOracle` (`:108`), `IRState.applyCall` (`:158`), `callSuccessFlag` (`:120`) | **both** (via Match) | load-bearing | recently live (call-stream rebuild); keep |
| Create.lean | 110 | Abstract `CreateOracle` + `evmCreateOracle` — CREATE analogue of Call | `CreateOracle` (`:64`), `evmCreateOracle` (`:99`), `createAddrOrZero` (`:75`) | **none** | **vestigial** | **zero importers** (only root `LirLean.lean:22`); `CreateOracle`/`evmCreateOracle`/`createAddrOrZero` referenced nowhere. Delete now |
| StorageErase.lean | 217 | `RBMap.erase` read-back lemmas for zero-write SSTORE slot clearing | `findD_erase_self`/`findD_erase_of_ne` (`:189`/`:199`), `mem_erase` (`:71`) | **both** (via Match) | load-bearing | recently added; pure data-structure facts, arguably belongs in a Batteries-support module |
| DefsSound.lean | 579 | B3: `WellFormed` + `DefsSound` recompute-on-use soundness | `DefsSound` (`:198`), `WellFormed` (`:132`), `defsSound_preserved_*` (`:290`+), `usesInExpr`/`useCount` (`:51`/`:78`), `StepScoped` (`:514`) | **both** (via MaterialiseRuns + Lir.Call) | load-bearing | keep; the recompute-soundness foundation both stacks need |

## 2. Dependency sub-DAG (this cluster)

```
                      SmallStep ──────► Spec.IR
                          ▲
        Call ─────────────┤ (Match imports Call, SmallStep, StorageErase)
        StorageErase ─────┤
                          │
   DefsSound ◄── Match ◄──┴── MaterialiseGas
      ▲            ▲              ▲
      └────── MaterialiseRuns ────┘   (MaterialiseRuns imports Match, MaterialiseGas, DefsSound)
                 ▲   ▲   ▲
   ┌─────────────┘   │   └─────────────┐
 MatDecLower   MaterialiseCleanHalt   StashTail
   │                 │                  │
   │            SimStmt ◄───────────────┤   (SimStmt imports MaterialiseRuns, MaterialiseCleanHalt)
   │              ▲                      │
   │           SimStmts                  │
   │              ▲                      │
   │           SimTerm ◄─────────────────┘   (SimTerm imports SimStmts, StashTail)
   │              │
   └──────────────┴────────► LowerDecode ──► LowerConforms ──► Acyclic ──► [FLAGSHIP]
                                                    ▲
                                     Lir.DriveSim ───┘ (also reaches LowerConforms!)

  CYCLIC REUSE ENTRY POINTS (bypass LowerConforms):
    Lir.Drive.SelfPresent ──► MaterialiseRuns
    Lir.CallRealises      ──► Match
    Lir.Call              ──► DefsSound
```

Two clean layers:
* **Foundation (reused, survives):** SmallStep, Call, StorageErase, DefsSound, Match,
  MaterialiseGas, MaterialiseRuns. Pulled into the cyclic flagship through SelfPresent /
  CallRealises / Lir.Call, independently of `LowerConforms`.
* **Acyclic superstructure (orphans if `LowerConforms` dies):** MatDecLower,
  MaterialiseCleanHalt, StashTail, SimStmt → SimStmts → SimTerm. Reachable from the
  flagship *only* through `LowerConforms → LowerDecode`.

## 3. SIMPLIFICATION OPPORTUNITIES

### 3a. The big lever: ~3627 LOC orphan when the acyclic path dies

If the lead deletes `Acyclic.lean` + `LowerConforms.lean` (and with them the `LowerDecode`
subtree), the following six files in this cluster lose all flagship reachability:

| Orphaned file | LOC |
|---|---|
| SimStmt | 1187 |
| SimTerm | 838 |
| StashTail | 519 |
| MatDecLower | 516 |
| MaterialiseCleanHalt | 404 |
| SimStmts | 163 |
| **subtotal** | **3627** |

That is **51% of this cluster** and the single biggest win in the whole "too many files"
concern. These are the entire Layer C/D/E gas-aware `Corr` simulation engine plus its
decode/gas/stash support — machinery built to prove the acyclic `LowerConforms`.

**CRITICAL CAVEAT — the deletion is gated by DriveSim.** The flagship currently reaches
`LowerConforms` by **two** edges, not one: `RealisabilitySpec → Acyclic → LowerConforms`
**and** `RealisabilitySpec → Lir.Drive.Headline → Lir.DriveSim → LowerConforms`
(`DriveSim.lean:1`). Deleting `Acyclic` alone does **not** orphan the sim stack — DriveSim
still pulls `LowerConforms` and therefore the whole Layer-C/D/E subtree. Realising the
3627-line win requires **first rewiring `Lir.DriveSim` off `LowerConforms`** (out of cluster,
but it is the gate). Recommend the design fleet confirm what `DriveSim` actually consumes from
`LowerConforms` before scheduling the deletion.

### 3b. Vestigial now — delete `Create.lean` (110 LOC)

`Create.lean` has zero importers (only the root aggregate). `CreateOracle`, `evmCreateOracle`,
`createAddrOrZero` are referenced nowhere in the tree (the `resumeAfterCreate` hits in
BytecodeLayer/Hoare/* and CallPreservesSelf are Evm's, not Lir's). It is a field-for-field mirror of
`Call.lean` that was never wired into any proof. Safe to delete immediately, independent of
the acyclic decision.

### 3c. Gas apparatus may be dead weight even in the *surviving* files

The flagship is gas-**free** (V2). `MaterialiseRuns` survives via `SelfPresent`, but
`SelfPresent` needs the *value/self-storage* channel, not the gas envelope. The gas conjunct
(`hgas`, `chargeOf`, `MaterialiseGasCharge`) and the entire `MaterialiseGas.lean` (289 LOC)
appear to be consumed only by the acyclic clean-halt fold (`MaterialiseCleanHalt`) and the
supplied-gas `LowerConforms` path. If so, once the acyclic path dies one could **strip the gas
conjunct from `materialise_runs` and delete `MaterialiseGas.lean` entirely**, shrinking the
1372-line linchpin. This needs a quick check of what `SelfPresent` reads off `MatRuns` — flag
for the design fleet, do not assume.

### 3d. Over-split merges (minor, if the acyclic path is *kept*)

* **SimStmts (163) → SimStmt.** SimStmts is a thin list-induction wrapper over SimStmt's arms;
  its only importer is SimTerm. No reason for a separate module.
* **MaterialiseGas (289) → MaterialiseRuns.** B1/B2 twins; MaterialiseRuns already imports it,
  and the header's split rationale (B1 needs B2's frames) is a coupling argument, not an
  isolation one. Merge unless 3c deletes it outright.
* **MaterialiseCleanHalt (404)** is split out *only* to dodge a `CleanHaltExtract →
  MaterialiseRuns` import cycle (its own header, `:163`). Moot once acyclic dies.

### 3e. Two `IRState` definitions

`SmallStep.IRState` (`:49`, the Match-layer IR) and the flagship's `Lir.IRState` (Machine)
are parallel IR-state records. The Match/sim bricks run on the former; the flagship runs on the
latter, bridged in `Corr` (`SimStmt.lean:103`). Consolidating to one IR-state def is a
structural cleanup but a larger, riskier change than 3a/3b — lower priority.

### 3f. `StorageErase` (217) placement

Pure `RBMap.erase` read-back facts with no EVM content (its own header). Load-bearing (Match
uses it for zero-write SSTORE), but it is really a Batteries-support lemma file — candidate to
move next to other data-structure support rather than living in the LirLean proof root.
