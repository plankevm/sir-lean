# exp005: strictly-IR vs EVM-generic classification (2026-07-13)

Input to Phase 3 of `consolidate-under-evm-plan-2026-07-13.md`. Analysis only — no code
moved. Method: read the theorem/def *signatures* of all ~53 `LirLean/` modules and tag
each per the criterion below. Five parallel readers; this is the synthesis.

**Tag criterion**
- **A — strictly-IR:** statement's meaning depends on IR structure (quantifies/destructs
  `Program/Block/Stmt/Term/Expr/Tmp/CallSpec/CreateSpec`, or asserts a property of
  `lower`/`emit`/`defsOf`/`matCache` as such). Cannot be restated without the IR.
- **B — generic-coupled:** statement is about EVM execution objects (`Frame`, `Runs`,
  `decode`, state, gas, storage, memory, `RunLog`) and names the IR / `lower prog` only as
  the *specific* bytecode/program; generalizes to arbitrary bytecode given the right
  hypothesis. → migration candidate.
- **C — already generic:** no IR reference in the statement at all.

## Headline verdict

**Eduardo's estimate holds: the strictly-IR core is the minority.** By best-effort
line/lemma weight, roughly **⅓ of exp005 is strictly-IR (A)** and **~⅔ is EVM-generic
(B/C) reasoning that only mentions `lower prog` as the concrete bytecode.** The generic
mass is not noise — it forms several *reusable EVM-bytecode theories* that belong in the
EVM layer.

**The catch (this reshapes Phase 3): the IR/EVM cut runs *inside* many files, not between
them.** ~12 of 53 modules are genuinely MIXED. So Phase 3 is not "move these files" — it
is "*split* these files": extract the generic theory, leave a thin IR-specific adapter.
That is real surgery and the main cost signal for Phase 3.

## The strictly-IR core (A) — stays in the IR package

1. **IR definition & semantics:** `Spec/IR`, `Spec/Lowering`, `Spec/Semantics`,
   `Spec/WellFormed`, `Spec/BudgetDerivations`, `Law`, `IRRun` (+ `NoGasReads` from
   `Spec/Conformance`).
2. **Lowering layout/anchor arithmetic:** `Decode/Layout`, `Decode/DecodeAnchors`,
   `Decode/LoweringLemmas`, the emit-ladder parts of `Decode/SegAligned`/`JumpValid`/
   `BoundaryReach`/`BoundaryCursor`, `CfgSim/LowerDecode`.
3. **Per-IR-constructor simulation & value-channel correspondence:** `Sim/SimStmt`,
   `Sim/SimStmts`, `Sim/SimTerm`, `Materialise/DefsSound`, `Materialise/MatFoldChannel`,
   `Materialise/MaterialiseGas` (A-core), `Materialise/MaterialiseCleanHalt`,
   `CfgSim/LowerConforms`, `Drive/DriveSim`, `Realisability/Producer`, the
   `matRunsC`/`termTies'`/`callRealises` arms of `Realisability/Machinery`.
4. **Flagships, witness, guard:** `Realisability/RealisabilitySpec` (the three flagships,
   confirmed A), `Realisability/Surface`, `Realisability/Witness`, the `ex*` bundle in
   `Realisability/WitnessParams`/`WitnessChecks`, `Call` (worked example), `Audit` (axiom guard).

## The EVM-generic mass (B/C) — migration surface into EVM/BytecodeLayer

Trapped generic theories, thematically:

| cluster | where it lives now | what it is |
|---|---|---|
| **Instruction-alignment calculus** | `Decode/SegAligned` (`SegAlignedP` + mono/append/nonpush/push) | pure bytecode segment-alignment walk; IR-free |
| **Boundary-walk / jumpdest validity** | `Decode/BoundaryReach`, `Decode/JumpValid` helpers, `Decode/DecodeLower` list↔decode lemmas | `ReachesBoundary`, `validJumpDests`, list/ByteArray/`decode` facts |
| **Modellable-step / no-call-create** | `Decode/Modellable` (payload) | `ModellableStep`/`NoCallCreate`/`CallsCode`/`CreateResolves` over `Frame`/`Step`; `ModellableStep` *already* defined in exp003 `Hoare/DriveRuns.lean` |
| **Recorder / trace reconstruction** | `Spec/Recorder`, `RecorderLemmas`, `Realisability/CheckedStep`, `Realisability/SegmentedEval`, the `RecorderCoupled`+boundary core of `Realisability/Machinery`, checker half of `WitnessParams` | "reconstruct/consume an EVM run against recorded oracle streams" — the witness-production engine |
| **Self/account-presence invariants** | `Drive/CallPreservesSelf`, B-part of `Drive/SelfPresent` (`SelfPresent`, gas/sload alignment) | "an EVM run preserves self/account presence" — generic reachability invariant |
| **CALL/CREATE effect oracles** | `Frame/Call`, `Frame/Create`, `CallRealises`, `sim_*`/`*_reflects_lowered` bricks of `Frame/Match` | EVM call/create resume-effect projections; IR-free |
| **Memory/stack spill algebra** | `Materialise/StashTail`, `MemRealises`+helpers of `Materialise/MaterialiseRuns`, `Materialise/CleanHaltExtract`, `Materialise/MatDecLower` | slot-spill / covered-`mload` readback / clean-halt opcode bricks / word-byte arith |
| **Observable conformance predicate** | `Spec/Conformance` (`Conforms`, `RunLog.clean`), `Spec/Seams` (already generic), `Words` | compare an EVM `RunLog`'s observable to an `Observable`; seam bundle; byte encoders |

## MIXED modules — where the cut runs inside the file (Phase-3 split list)

| module | split |
|---|---|
| `Decode/SegAligned` | `SegAlignedP` calculus (C) ↔ `segAlignedP_emit*`/`matCache` (A) |
| `Decode/BoundaryReach` | `ReachesBoundary`/`validJumpDests` core (C) + `decode_reachable_boundary_*` (B) ↔ emit-ladder (A) |
| `Decode/JumpValid` | `ReachesBoundary.trans`/`reaches_of_segAligned` (C) ↔ `block_offset_validJump` (A) |
| `Decode/BoundaryCursor` | index/append/terminal list lemmas (C) ↔ block-region cursor (A) |
| `Decode/DecodeLower` | `decode_*_of_list` (C) ↔ `decode_lower_*`/`flatBytes` bridge (A) |
| `Decode/Modellable` | almost all `Frame`/`Step` theory (C) ↔ `AtReachableBoundary = lower prog` tether (A, thin) |
| `Realisability/Machinery` | `RecorderCoupled`+suffix+boundary engine (B) ↔ `matRunsC`/`termTies'`/`callRealises` adapter (A) |
| `Realisability/WitnessParams` | `callsCodeOk`/`entryCallsCodeOk`/precompile stubs/`RunLog.cleanb` (C) ↔ `ex*` witness (A) |
| `Materialise/MaterialiseRuns` | `StashRuns`/`mload_covered`/memory-expansion (C) + `MemRealises`/`StorageAgree` (B) ↔ `evalExpr_obs_irrel` (A) |
| `Materialise/StashTail` | `mstoreFrame_*`/`stash_tail_runs` (C) ↔ `stash_tail_sload` key-run (B, thin) |
| `Materialise/MaterialiseGas` | `chargeExpr`/`chargeCache` fold (A) ↔ `subCharges_singleton`/`charge_binOpPost_gas` (C) |
| `Sim/SimTerm` | `sim_term_*`/`pcOf_*` (A) ↔ `result*_endFrame_success` (C) |
| `Frame/Match` | `sim_*`/`*_reflects_lowered`/`sstoreFrame_*` (B, 21) ↔ `lower_preserves_*` (A, 3) |
| `Drive/SelfPresent` | `SelfPresent`+gas/sload alignment+presence (B, ~15) ↔ `sloadRealises_charge_of_witness` (A, 1) |

## Clean whole-file migrations (no split needed)

Already IR-free today; move as-is once their support defs travel with them:
`Frame/StorageErase` (C, calibration), `Frame/Call`, `Frame/Create`, `Drive/CallPreservesSelf`,
`RecorderLemmas`, `CallRealises`, `Realisability/CheckedStep`, `Realisability/SegmentedEval`,
`Materialise/MatDecLower`, `Materialise/CleanHaltExtract`, `Spec/Seams`, `Words`, and
(dominantly) `Spec/Recorder`.

## Precursor blocker for Phase 3 (found during classification)

The generic B modules reference type aliases — `Observable`, `CallStream`, `CreateStream`,
`GasOracle`/`Trace`, `World` (`:= Word → Word`) — that are **defined in the A-tagged
`Spec/Semantics.lean`**. They are structurally EVM-generic but currently live IR-side. Before
any B module can move to EVM, these aliases must be hoisted to a shared/EVM location.
Likewise the B lemmas `open Lir`/`open Lir.Frame` and use IR-free defs (`selfStorage`,
`storageAt`, `gasReadOf`, `FramesRun`, `evmV2CallEntry`, `SelfPresent`, `ModellableStep`) that
must move alongside them — mechanical, but they're the migration's connective tissue.

## Implications for the plan

- Phase 0 (scrub `Lir` from the exp003 engine) and Phase 1 (fold exp003 into EVM) are
  unaffected — still the right immediate move.
- **Phase 3 is bigger than "move files."** It is: (i) hoist the shared aliases/defs out of
  `Spec/Semantics`; (ii) migrate the ~13 clean-generic files; (iii) *split* the ~14 mixed
  files along the cut lines above, extracting the generic theory into EVM/BytecodeLayer and
  leaving thin IR adapters. Every step green-gated + axiom-clean, as always.
- Best sequenced *after* the new canonical IR exists (per Eduardo), because the IR-side
  adapters left behind are exactly what the canonical IR will want to re-target.
