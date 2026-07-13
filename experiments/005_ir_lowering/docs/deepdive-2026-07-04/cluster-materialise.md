# Deep-dive audit — the "Materialise" cluster (2026-07-04)

> **P9 status note (2026-07-08).** This audit describes the pre-Phase-2A materialise stack.
> The legacy APIs it names (`Expr.slot`, `materialiseExpr`, `materialise`, `recomputeFuel`,
> `MatFueled`, `MatDec`, `MatRuns`, `chargeOf`, `MaterialiseGasCharge`, and
> `Assembly/Acyclic.lean`) have been replaced by the fold/channel forms in Lean; keep the body
> below as provenance, not current symbol inventory.

Scope: the six spill/recompute **value-channel** files —
`DefsSound.lean` (B3), `MaterialiseGas.lean` (B2), `MaterialiseRuns.lean` (B1
linchpin), `MatDecLower.lean` (A→B1 bridge), `MaterialiseCleanHalt.lean` (B1
gas-dropping twin), `StashTail.lean` (P1 uniform stash tail).

Method: read every file end-to-end (incl. the 1373-line `MaterialiseRuns` and
all pivotal proof bodies), then repo-wide `grep` on every declaration name over
`LirLean/`. All six files are **terminal-green**: `grep -nE '\bsorry\b|\badmit\b|native_decide'`
finds only docstring prose and one "relaxed to admit" comment (`MaterialiseRuns.lean:780`);
none are in the WIP sorry-carrier `RealisabilitySpec.lean`. Every file ends with a
`#print axioms` guard asserting `[propext, Classical.choice, Quot.sound]`.

Headline conclusion on the audit prompt's central question ("how much of the gas
apparatus is needed by the GAS-FREE flagship vs only the acyclic path"): **the gas
apparatus is NOT acyclic-only and is not deletable.** `MatRuns` bundles the gas
contract (`gasCharge`/`gasToNat`) unconditionally, and B1's own induction *consumes*
`gasToNat` to bound each operand's gas before recursing (`MaterialiseRuns.lean:1140,
1167, 1292, 1319`). Gas-sufficiency is what proves the materialise sub-run *completes*
(the EVM charges gas per opcode; you must show it doesn't run out mid-materialise).
Both the gas-free flagship path (via `Drive/SelfPresent` → `materialise_runs` /
`materialise_runs_of_cleanHalt`) and the dead acyclic path go through B1, so B2
(`MaterialiseGas`) is load-bearing for both. What the gas-free flagship drops is not
the *internal* gas bookkeeping but the *external* `hgas` premise — which is exactly
what `MaterialiseCleanHalt`'s fold derives from a clean-halt witness.

---

## 1. Per-file sections

Legend for the role column: **terminal-for-flagship** = consumed on the live
`Lir.lower_conforms` path; **shared-infra** = used by both flagship and (dead) acyclic
paths and/or many consumers; **incremental-toward-X** = built up toward a still-open
connection; **retired-witness** = a deliberately-retained regression subject for a
mechanism removed from the spine; **internal** = only in-file callers (a documented
brick of the honest split).

### 1a. `DefsSound.lean` — Layer B3 (recompute-on-use soundness)

Purpose (grounded in `docs/lower-conforms-plan.md` B3 + `uniform-spill-alloc-plan.md`
§6): the lowering is *recompute-on-use* — an `assign` emits no bytes; the consuming
opcode re-emits `materialiseExpr defsOf …`. B3 states the coherence B1 needs at its
`.tmp t → defsOf prog t` recursion (`DefsSound`), and `WellFormed` (the DESIGN
DECISION) bounds the *non-recomputable* tmps (call results) to single-use so B1
materialises each at its unique site. Gas and sload are excluded from `DefsSound` and
un-restricted by `WellFormed` because Phase B/C *spill* them to memory.

| decl | kind | role | callers |
|---|---|---|---|
| `usesInExpr` | def | shared-infra (use-counting) | `DefsSound.lean` internally (`usesInStmt`, `evalExpr_setLocal_of_unused`); `RealisabilitySpec.lean` |
| `usesInStmt` / `usesInTerm` / `usesInBlock` | def | shared-infra | in-file (`useCount`); |
| `useCount` | def | shared-infra | in-file (`WellFormed`/`WellFormedDec`) |
| `isCallResult` | def | shared-infra | in-file (`NonRecomputable`, `WellFormed`); `RealisabilitySpec.lean` |
| `isGasDef` | def | shared-infra | in-file (`NonRecomputable`, `defsSound_preserved_assignGas`); `RealisabilitySpec.lean` |
| `isSloadDef` | def | shared-infra | in-file; `RealisabilitySpec.lean` |
| `NonRecomputable` | def | terminal-for-flagship (the spill/remat discriminant) | `MaterialiseRuns.lean`, `MaterialiseCleanHalt.lean`, `LowerConforms.lean`, `LowerDecode.lean`, `SimTerm.lean`, `SimStmt.lean`, `RealisabilitySpec.lean` |
| `WellFormed` | def | shared-infra (DESIGN DECISION) | `LowerDecode`, `LowerConforms`, `SimStmt`, `Spec/Lowering`, `Call`, `RealisabilitySpec`; **and `Acyclic.lean`** (dead path) |
| `callResultTmps` | def | shared-infra | in-file (`WellFormedDec`, `callResult_mem_dec`) |
| `WellFormedDec` | def | shared-infra (decidable surrogate) | `Call.lean` (`by decide` discharge) |
| `Decidable (WellFormedDec …)` | instance | shared-infra | resolves `WellFormedDec` decide |
| `callResult_mem_dec` | thm | shared-infra | in-file (`wellFormed_of_dec`) |
| `wellFormed_of_dec` | thm | shared-infra | `Call.lean` |
| `DefsSound` | def | terminal-for-flagship (B3 invariant) | pervasive premise: `MaterialiseRuns`, `MaterialiseCleanHalt`, `LowerConforms`, `LowerDecode`, `SimStmt`, `SimTerm`, `RealisabilitySpec`, … |
| `defsSound_entry` | thm | terminal-for-flagship (vacuous-at-entry) | `LowerConforms.lean` |
| `setLocal_locals_ne` | private thm | internal | in-file preservation lemmas |
| `evalExpr_setLocal_of_unused` | thm | internal | in-file (`defsSound_preserved_assign*`) |
| `setLocal_locals_self` | private thm | internal | in-file (`defsSound_preserved_assignPure`) |
| `defsSound_preserved_assignPure` | thm | terminal-for-flagship (B3 preservation) | in-file (`defsSound_preserved`); `SimStmt`, `RealisabilitySpec` |
| `defsSound_preserved_assignGas` | thm | terminal-for-flagship | in-file (`defsSound_preserved`); `SimStmt` |
| `defsSound_preserved_assignSload` | thm | terminal-for-flagship | in-file; `SimStmt` |
| `evalExpr_setStorage_of_noSload` | private thm | internal | in-file (`defsSound_preserved_sstore`) |
| `defsSound_preserved_sstore` | thm | terminal-for-flagship | in-file; `SimStmt` |
| `evalExpr_world_irrel_of_noSload` | private thm | internal | in-file (`defsSound_preserved_call`) |
| `defsSound_preserved_call` | thm | terminal-for-flagship | in-file; `SimStmt` |
| `StepScoped` | def | terminal-for-flagship (per-step scoping bundle) | `LowerConforms`, `LowerDecode`, `SimStmts`, `SimStmt`, `RealisabilitySpec` |
| `defsSound_preserved` | thm | terminal-for-flagship (B3 headline preservation) | `SimStmt`, `RealisabilitySpec` |

Note: the header comment (`:118-127`) that `guardIR` is now `WellFormed` because
Phase-B lifted the gas restriction is consistent with the code — `WellFormed` only
constrains `isCallResult` tmps (`:132-133`).

### 1b. `MaterialiseGas.lean` — Layer B2 (honest-gas charge engine)

Purpose (plan node B2 `materialise_gas_charge`): supply the per-`Expr` charge list
`chargeOf` (mirroring `materialiseExpr` opcode-for-opcode) plus the pure `subCharges`
arithmetic that turns B1's per-step gas facts into a whole-expression envelope. The
module is imported **only** by `MaterialiseRuns.lean` (verified: `grep import
LirLean.MaterialiseGas` → sole hit is B1). It is the B2-feeds-B1 seam, nothing else.

| decl | kind | role | callers |
|---|---|---|---|
| `chargeOf` | def | terminal-for-flagship | `MaterialiseRuns`, `MaterialiseCleanHalt`, `LowerDecode`, `LowerConforms`, `SimStmt`, `SimTerm`, `RealisabilitySpec` |
| `chargeOf_imm` | simp thm | shared-infra (reduction) | `MaterialiseRuns`, `MaterialiseCleanHalt` |
| `chargeOf_tmp_some` | thm | shared-infra | `MaterialiseRuns`, `MaterialiseCleanHalt` |
| `chargeOf_tmp_none` | thm | shared-infra | `MaterialiseRuns` (`chargeOf_length_pos_of_matDec`) |
| `chargeOf_add` / `chargeOf_lt` | simp thm | shared-infra | `MaterialiseRuns`, `MaterialiseCleanHalt` |
| `chargeOf_sload` | simp thm | shared-infra | `MaterialiseRuns` (`chargeOf_length_pos_of_matDec`) |
| `chargeOf_gas` | simp thm | shared-infra | `MaterialiseRuns` (`chargeOf_length_pos_of_matDec`) |
| `chargeOf_imm_const` | thm | **genuinely-unused-orphan** (see §3) | none (only its own def + one docstring back-ref) |
| `subCharges_chargeOf_binop` | thm | internal | in-file (`materialiseGasCharge_binop`) |
| `toNat_chargeOf` | thm | terminal-for-flagship | `MaterialiseRuns.lean:1240,1365` (`gasToNat` for add/lt) |
| `subCharges_singleton` | thm | internal | in-file (`charge_runs_imm`, `charge_binOpPost_gas`) |
| `charge_runs_imm` | thm | internal | in-file (`materialiseGasCharge_imm`) |
| `charge_binOpPost_gas` | thm | terminal-for-flagship | `MaterialiseRuns.lean:1230,1239,1355,1364` |
| `MaterialiseGasCharge` | def | terminal-for-flagship (B1's `MatRuns.gasCharge` field type) | `MaterialiseRuns` (structure field + arms) |
| `materialiseGasCharge_imm` | thm | terminal-for-flagship | `MaterialiseRuns.lean:468` (`matRuns_imm`) |
| `materialiseGasCharge_binop` | thm | terminal-for-flagship (the B1 corollary engine) | `MaterialiseRuns.lean:1228,1237,1353,1362` |

### 1c. `MaterialiseRuns.lean` — Layer B1 (the linchpin `materialise_runs`)

Purpose (plan node B1, *the linchpin*): running `materialiseExpr defs fuel e`
reproduces `evalExpr`'s value on the bytecode stack and delivers the whole `MatRuns`
bundle (run, pushed value, code/addr/self-storage/accounts preserved, pc advance, B2
gas contract, and the memory value-channel transport `memBytes`/`memActive`). Proved
**total over `Expr`**; the two non-pure leaves `.gas`/`.sload` are *spilled* and their
arms are discharged as unreachable (`e ≠ .gas`, `∀ k, e ≠ .sload k`). The MLOAD-readback
arm (`.tmp t` with `defs t = some (.slot slot)`) is the memory value channel.

The `.slot` top-level arms of `chargeOf`/`MatDec`/`materialiseExpr` are **reached and
load-bearing** (not dead) — via `chargeOf_tmp_some`/`matDec_tmp_some` collapsing a
call-result `.tmp t` to `.slot slot` (`MaterialiseRuns.lean:871-872, 862-863`); a *bare*
`.slot` is vacuous only at top level (`:810-814, 824-829`, `evalExpr (.slot _) = none`).

Frame-accessor `rfl`/`simp` reductions (≈40 lemmas, `:75-224`): `pushFrameW_*`,
`addFrame_*`, `ltFrame_*`, `sloadFrame_*`, `gasFrame_*` for
`code/validJumps/addr/selfStorage/pc/stack/gas/memory/activeWords`. Role: **shared-infra**
— these thread the `MatRuns` clauses; consumed throughout this file (and, being `@[simp]`,
by the whole downstream `sim_*`/Stash/CleanHalt grind that imports B1). Not individually
re-listed; none are dead (each names a `MatRuns` field the recursion discharges).

| decl | kind | role | callers |
|---|---|---|---|
| `MatDec` | def | terminal-for-flagship (structured decode bundle) | `MatDecLower`, `MaterialiseCleanHalt`, `SimStmt`, `SimTerm`, `SimStmts`, `LowerDecode`, `LowerConforms`, `RealisabilitySpec` |
| `matDec_imm` / `matDec_slot` | simp thm | shared-infra (reduction) | `MaterialiseRuns`, `MaterialiseCleanHalt`, `MatDecLower` |
| `matDec_tmp_some` / `matDec_tmp_none` | thm | shared-infra | same + `MatDecLower` |
| `matDec_add` / `matDec_lt` / `matDec_sload` | simp thm | shared-infra | `MatDecLower` |
| `MatRuns` | structure | terminal-for-flagship (B1 conclusion bundle) | `MaterialiseCleanHalt`, `StashTail`, `LowerDecode`, `LowerConforms`, `SimStmt`, `SimTerm`, `RealisabilitySpec`, `Drive/SelfPresent` |
| `emitImm_length` | thm | shared-infra | `MatDecLower`, `StashTail`, `MaterialiseRuns` |
| `materialiseExpr_imm_length` | thm | internal | in-file (`matRuns_imm`, `MatDecLower`) |
| `materialiseExpr_slot` | thm | shared-infra | `MatDecLower`, `MaterialiseCleanHalt`, `MaterialiseRuns` |
| `materialiseExpr_tmp_some` / `_tmp_none` | thm | shared-infra | `MatDecLower`, `MaterialiseRuns` |
| `materialiseExpr_add` / `_lt` / `_sload` | simp thm | shared-infra | `MatDecLower`, `MaterialiseRuns` |
| `chargeOf_length_pos_of_matDec` | thm | internal (stack-depth bound) | in-file (add/lt/tmp arms), `MaterialiseCleanHalt` |
| `push32_pcΔ` | thm | internal | in-file (`matRuns_imm`), `StashTail` |
| `matRuns_imm` | thm | terminal-for-flagship (B1 `.imm` leaf) | in-file (`materialise_runs` imm arm) |
| `evalExpr_obs_irrel` | thm | terminal-for-flagship (obs-irrelevance on pure fragment) | in-file, `MaterialiseCleanHalt` |
| `SloadRealises` | def | **retired-witness** (Phase C; see §3) | subject of `Drive/SelfPresent.sloadRealises_charge_of_witness` only |
| `GasRealises` | def | **retired-witness** (Phase B; see §3) | subject of `Drive/SelfPresent.gasRealises_obs_of_witness` only |
| `StorageAgree` | def | terminal-for-flagship (M3 storage lens) | `LowerDecode`, `LowerConforms`, `MaterialiseCleanHalt`, `StashTail`, `SimTerm`, `SimStmt`, `RealisabilitySpec` |
| `StorageAgree.transport` | thm | terminal-for-flagship | `MaterialiseRuns` add/lt arms, downstream sim |
| `MemRealises` | def | terminal-for-flagship (memory value channel) | `LowerConforms`, `LowerDecode`, `MaterialiseCleanHalt`, `StashTail`, `SimTerm`, `SimStmt`, `DriveSim`, `Drive/Headline`, `RealisabilitySpec`, `BytecodeLayer/Hoare/MemAlgebra` |
| `mload_covered_congr` | thm | internal (activeWords-nondecreasing read) | in-file (`MemRealises.transport`) |
| `MemRealises.transport` | thm | terminal-for-flagship | `MaterialiseRuns` add/lt arms; downstream |
| `M_32_eq_self_of_covered` | thm | shared-infra (zero-expansion fact) | in-file, `memoryExpansionWords?_ofNat_32_of_covered` |
| `toUInt64?_ofNat_of_lt` | thm | internal | in-file (`memoryExpansionWords?_ofNat_32_of_covered`) |
| `memoryExpansionWords?_ofNat_32_of_covered` | thm | terminal-for-flagship (covered MLOAD/MSTORE no-expand) | in-file (readback arm), `StashTail` (`stash_tail_runs_covered`) |
| `materialise_runs` | thm | **terminal-for-flagship (the B1 linchpin)** | `MaterialiseCleanHalt`, `SimTerm.lean:367`, `StashTail` (`stash_tail_sload` premise), downstream sim |

### 1d. `MatDecLower.lean` — Layer A→B1 bridge (`MatDec` reconstruction)

Purpose: assemble Layer-A byte anchors (`DecodeAnchors`) into B1's whole `MatDec`
bundle, generically over `lower prog`, by induction on `materialiseExpr`'s structure —
so lower layers see no free decode hypothesis. Two pieces: the `PUSH32` immediate
round-trip `uInt256_wordBytesBE`, and the segment bridge `MatSeg`/`matDec_of_seg`, then
specialised to statement (`matDec_of_lower`) and terminator (`matDec_of_term`) cursors.

| decl | kind | role | callers |
|---|---|---|---|
| `u256_toNat_ofNat` | thm | internal | in-file |
| `u256_ofNat_toNat` | thm | internal | in-file (`uInt256_wordBytesBE`) |
| `u256_shiftRight_toNat` | thm | internal | in-file (`fromBytes_wordBytesBE`) |
| `u8_ofNat_toFin` | thm | internal | in-file |
| `fromBytes_wordBytesBE` | thm | internal | in-file (`uInt256_wordBytesBE`) |
| `uInt256_wordBytesBE` | thm | internal (the 256-bit round-trip) | in-file (`imm_leaf_decode`); no external caller |
| `extract_toList_eq` | thm | internal | in-file (`imm_leaf_decode`) |
| `imm_leaf_decode` | thm | shared-infra (PUSH32 leaf) | in-file; `LowerDecode`, `RealisabilitySpec` |
| `nonpush_leaf_decode` | thm | shared-infra (ADD/LT/SLOAD/GAS/MLOAD leaf) | in-file; `LowerDecode` |
| `MatSeg` | def | shared-infra (byte-segment hypothesis) | in-file; `LowerDecode` |
| `seg_prefix` / `seg_suffix` | thm | internal | in-file (`matDec_of_seg`) |
| `ofNat_add'` | thm | internal | in-file |
| `slot_leaf_decode` | thm | internal (`.slot` PUSH32+MLOAD leaf) | in-file (`matDec_of_seg`); no external caller |
| `MatFueled` | def | shared-infra (recompute-fuel sufficiency) | `LowerConforms`, `LowerDecode`, `RealisabilitySpec`; **and `Acyclic.lean`** (dead path) |
| `matFueled_tmp_some` / `_tmp_none` | thm | internal | in-file (`matDec_of_seg`) |
| `matDec_of_seg` | thm | terminal-for-flagship (core reconstruction) | in-file; `LowerDecode`, `SimStmt` |
| `matSeg_of_stmt` | thm | internal | in-file (`matDec_of_lower`) |
| `matDec_of_lower` | thm | terminal-for-flagship (stmt-cursor `MatDec`) | `LowerDecode` |
| `matSeg_of_term` | thm | internal | in-file (`matDec_of_term`) |
| `matDec_of_term` | thm | terminal-for-flagship (term-cursor `MatDec`) | `LowerDecode`, `RealisabilitySpec` |

Note: `uInt256_wordBytesBE` and `slot_leaf_decode` have zero external callers but are
genuine internal bricks of `matDec_of_seg` (the PUSH32 round-trip and `.slot` leaf).
Not dead.

### 1e. `MaterialiseCleanHalt.lean` — B1's gas-dropping twin (FoldLemma)

Purpose: B1 takes the whole-expression gas envelope as a *supplied* `hgas`. This module
**derives** it from a single `CleanHaltsNonException fr` witness (the clean-halt approach),
by a structural gas-fold that reuses B1 to produce intermediate frames and their
`gasToNat` descent, threading clean-halt across each sub-run. Re-exports B1's full
bundle with the gas bound as a derived conjunct. Kept out of `MaterialiseRuns.lean` to
avoid a `CleanHaltExtract → MaterialiseRuns` import cycle.

| decl | kind | role | callers |
|---|---|---|---|
| `materialise_charge_le_of_cleanHalt` | thm | terminal-for-flagship (the gas fold) | in-file (`materialise_runs_of_cleanHalt`); `RealisabilitySpec` |
| `materialise_runs_of_cleanHalt` | thm | **terminal-for-flagship (B1 twin, the widely-consumed entry)** | `LowerDecode`, `LowerConforms`, `SimStmt`, `Spec/Seams`, `Audit`, `RealisabilitySpec`, `CleanHaltExtract` |

### 1f. `StashTail.lean` — P1 uniform spill stash-tail

Purpose (`uniform-spill-alloc-plan.md` §2.2): every spilled def-site ends in the same
two-opcode tail `PUSH32 (slotOf t) ; MSTORE`. Prove it once as a forward `Runs` lemma,
parameterised over the stashed value and residual stack; provide the GAS-prefix and
SLOAD-prefix variants. The module's core insight (`:58-70`): the ties' `toMachineState`
equality over-constrains gas (never preserved on a real run); the honest content that
`MemRealises`/`Corr` actually read is only `memory` bytes + `activeWords`, which the
lemmas expose precisely.

| decl | kind | role | callers |
|---|---|---|---|
| `memChargedState_memory` / `_activeWords` | simp thm | internal | in-file (`mstoreFrame_*_eq`) |
| `mstoreFrame_memBytes_eq` | thm | internal | in-file (`stash_tail_runs`) |
| `mstoreFrame_activeWords_eq` | thm | internal | in-file (`stash_tail_runs`) |
| `pushFrameW_accounts` | simp thm | shared-infra | in-file; (`@[simp]` downstream) |
| `pushFrameW_canMod` | simp thm | shared-infra | in-file; downstream |
| `pushFrameW_activeWords'` | simp thm | internal | in-file |
| `pushFrameW_gas` | simp thm | internal | in-file |
| `pushFrameW_stack'` | simp thm | internal | in-file (`stash_tail_runs`) |
| `stash_tail_runs` | thm | terminal-for-flagship (core tail) | in-file (`stash_tail_gas`, `stash_tail_sload`) |
| `stash_tail_runs_covered` | thm | **incremental-toward Phase-C cached-SLOAD reuse** (see §3) | none yet; named at `SimStmt.lean:1076` as the covered-slot reuse path |
| `stash_tail_gas` | thm | terminal-for-flagship (gas def-site stash) | `LowerDecode.lean:1234` (`sim_assign_gas_lowered`) |
| `stash_tail_sload` | thm | terminal-for-flagship (spilled-SLOAD def-site stash) | `LowerDecode.lean:1506` (`sim_assign_sload_lowered`) |

---

## 2. Cluster internal sub-DAG + entry/exit edges

Internal import edges (module → module it imports, cluster-only):

```
DefsSound ─────┐
               ├──▶ MaterialiseRuns ──┬──▶ MatDecLower
MaterialiseGas ┘                      ├──▶ MaterialiseCleanHalt
                                      └──▶ StashTail
```

`MaterialiseRuns` is the cluster hub: it imports `MaterialiseGas` (B2) and `DefsSound`
(B3), and is imported by the other three (`MatDecLower`, `MaterialiseCleanHalt`,
`StashTail`). `MaterialiseGas` is imported **only** by `MaterialiseRuns`; `DefsSound`
by `MaterialiseRuns` **and** `Call.lean`.

Entry edges (outside cluster → cluster):
- `DefsSound` ← `LoweringLemmas`, `Spec.Semantics`
- `MaterialiseGas` ← `Match`, `Engine.Charges`
- `MaterialiseRuns` ← `Match`, `Engine.MemAlgebra`
- `MatDecLower` ← `DecodeAnchors`
- `MaterialiseCleanHalt` ← `CleanHaltExtract`

Exit edges (cluster → consumers). Note the **cross-cluster back-loop**:
`MatDecLower` → `CleanHaltExtract` (outside) → `MaterialiseCleanHalt` (inside cluster).
- `MatDecLower` is imported by `CleanHaltExtract` and `LowerDecode`.
- `MaterialiseRuns` (transitively via the above) reaches `SimStmt`, `SimTerm`,
  `LowerDecode`, `LowerConforms`, and up to `DriveSim`/`Drive/*`/`RealisabilitySpec`.
- `MaterialiseCleanHalt` is imported by `SimStmt` and `Audit`.
- `StashTail` is imported by `LowerDecode` and `SimTerm`.
- `DefsSound` also exits to `Call` (via `WellFormedDec`/`wellFormed_of_dec`).

P8 update: the live conformance path no longer uses `Acyclic`/`MatFueled` as its
well-formedness route. The canonical value channel is the fold-cache path (`matCache` /
`chargeCache` plus the `MatDecC`/`MatRunsC` stack); the old generic fuel definitions remain only
as residual P9 deletion targets. Retiring `Acyclic.lean` now waits on deleting that old fuel stack,
not on the live lowered-layout bundle.

---

## 3. SIMPLIFICATION CANDIDATES (evidence-backed; conservative)

**C1 — `chargeOf_imm_const` (`MaterialiseGas.lean:141-144`): genuinely-unused theorem.**
Repo-wide grep: the name appears only at its own definition and one docstring
back-reference (`:63`); zero call sites, in-file or out. It restates PUSH32
width-stability (charge of a literal is independent of the word), but that fact is
*already* discharged structurally by `chargeOf_imm` (`chargeOf … (.imm _) = [Gverylow]`
for any word), which is what the proofs actually use. Safe to delete as dead code.
Value is low (≈4 lines) and it documents a real invariant — **needs confirmation** the
lead wants it gone vs. kept as documentation, but it is the one clearly-orphan decl in
the cluster.

**C2 — `GasRealises`/`SloadRealises` (`MaterialiseRuns.lean:536-560`) +
`stash_tail_runs_covered` (`StashTail.lean:256`): retained-but-unreferenced residue.**
These are NOT dead in the "delete me" sense; classify with care:
- `GasRealises`/`SloadRealises` are the **retired** `∀`-over-frames universals
  (Phase B/C). They are provably unsatisfiable on genuine multi-read runs and were
  removed from `Corr`/`materialise_runs`/the headlines. Their *only* remaining consumers
  are the regression-witness lemmas `gasRealises_obs_of_witness` /
  `sloadRealises_charge_of_witness` in `Drive/SelfPresent.lean` (`:220`, `:337`) —
  which are themselves referenced **only in docstrings** (`Headline.lean:58,70`;
  `MaterialiseRuns.lean:509,530`), never on a proof path. So this is a self-contained
  "lesson witness" island documenting the unsatisfiability finding that motivated the
  whole spill pivot (`docs/gas-decision.md`; `HonestGasTie.lean` already deleted).
  Per the project's proof-first/lesson-preservation discipline, deletion is **not**
  recommended; the defensible cleanup is *relocation* of the two defs + two witnesses
  into a clearly-named `RegressionWitnesses`-style file so the B1 spine reads clean.
  **Needs confirmation** — this is an organizational call, not a correctness one.
- `stash_tail_runs_covered` has no caller yet; it is **incremental-toward** the Phase-C
  cached-SLOAD-reuse path explicitly named at `SimStmt.lean:1076`. That connection is
  still open (the covered-slot second read is not yet wired), so this is a planned-feature
  leaf, **not** superseded. Keep.

**C3 — Acknowledged intentional duplication (NOT a defect): the covered-slot MLOAD
gas argument.** The PUSH32+MLOAD zero-expansion charge reasoning appears twice — in
B1's readback arm (`MaterialiseRuns.lean:896-940`) and in the gas-fold's readback arm
(`MaterialiseCleanHalt.lean:122-177`). This is the honest B1/B2 split: the fold tracks
only the `Nat` gas accumulation and cannot cite B1's endpoint without circularity (B1
is what it feeds). Flagging so a future reader does not "dedupe" it into a cycle. No
action recommended.

**Not candidates (checked, all live):** every `pushFrameW_*`/`addFrame_*`/`ltFrame_*`/
`sloadFrame_*`/`gasFrame_*` accessor (each names a `MatRuns` field the recursion
discharges and is `@[simp]` for downstream); `uInt256_wordBytesBE`/`slot_leaf_decode`
(internal bricks of `matDec_of_seg`); the `.slot` arms of `chargeOf`/`MatDec`/
`materialiseExpr` (reached via the `.tmp t`→`.slot` call-result readback, load-bearing);
all `defsSound_preserved_*` per-arm lemmas (dispatched by `defsSound_preserved`).
