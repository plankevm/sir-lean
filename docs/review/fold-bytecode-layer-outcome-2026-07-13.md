# Bytecode-layer fold outcome — 2026-07-13

## TL;DR

The refactor removed the artificial engine/proof split between exp005 and exp003 without changing the closed conformance contract. IR-independent EVM execution machinery now belongs to exp003's [`BytecodeLayer.Hoare`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare.lean#L33), while lowering-dependent decode, simulation, materialisation, and realisability remain in the flattened [`LirLean`](../../experiments/005_ir_lowering/LirLean.lean#L1) tree under the single `Lir` namespace. The three public flagships—[`lower_conforms`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221), [`lower_conforms_exact`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269), and [`lower_conforms_gasfree`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304)—were byte-for-byte statement-diffed against their pre-refactor forms at `bab5e5c`; only their enclosing namespace/module path changed. Verification status, reported once: the final default and WIP builds passed, the live Lean sources contain no forbidden proof escape, and all three flagship axiom reports are exactly the standard trio; the report agent did not rerun the expensive builds.

## Goal and boundary

The checked-in [refactor plan](../../experiments/005_ir_lowering/docs/refactor-plan-2026-07-06.md#L1) had accumulated an exp005 `Engine/` tier containing facts that mention EVM execution but not the LIR. This run folded that reusable layer into exp003, removed version and role names that no longer described the code, deleted superseded coupling machinery, and consolidated tiny leaf modules. The package edge is now explicit in the exp005 [Lake configuration](../../experiments/005_ir_lowering/lakefile.lean#L4): exp005 requires exp003, while exp003 requires only the EVM package in its own [Lake configuration](../../experiments/003_bytecode_layer/lakefile.lean#L4). A search of exp003 imports finds no `LirLean` import, so the dependency remains one-way: exp005 → exp003 → EVM.

The supplied context path `docs/review/seams-and-migration-2026-07-12.md` is absent from the checkout, the filesystem, and repository history. It could not be reviewed; the checked-in refactor plan and the live import graph were used instead.

## What landed

| ID | Commit | Outcome |
|---|---|---|
| F1 | `8edacff` — Fold IR-free lowering engine into bytecode Hoare layer | Moved the seven surviving IR-free engine modules into exp003: [`AccountMap.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/AccountMap.lean#L1), [`CleanHalt.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L1), [`Descent.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/Descent.lean#L1), [`DriveMono.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/DriveMono.lean#L1), [`DriveRuns.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean#L1), [`MemAlgebra.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L1), and [`StepWalk.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/StepWalk.lean#L1). The eighth engine leaf was charge algebra, consolidated by F8. The lowering-dependent [`Modellable.lean`](../../experiments/005_ir_lowering/LirLean/Decode/Modellable.lean#L1) moved by role within exp005 rather than crossing the package boundary. |
| F2 | `d92df8a` — Dissolve Lir V2 namespace layer | Removed the `V2/` directory and `Lir.V2` namespace. Live call, drive, IR-run, law, recorder, realisability, simulation, and specification modules now use `Lir`; imports and narrative references were swept with the rename. |
| F3 | `2c9aa21` — Rename Assembly layer to CfgSim | Renamed the misleading `Assembly/` role to [`CfgSim/`](../../experiments/005_ir_lowering/LirLean/CfgSim/LowerConforms.lean#L1), whose two modules establish CFG-level decode/simulation facts rather than owning byte emission. |
| F4 | `6adad22` — Delete vestigial Plus layer | Deleted the superseded `Drive/Headline.lean` duplicate and its imports. The actual exported conformance boundary remains the three theorems in [`RealisabilitySpec.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L204). |
| F5 | `ad63e20` — Remove dead v1 coupling surface | Deleted the unused frame small-step machine and result-slot transformers, then reduced [`Frame/Match.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Match.lean#L1) to the frame-local simulation/boundary facts consumed by the live correspondence. [`Frame/Call.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Call.lean#L40) and [`Frame/Create.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Create.lean#L35) retain the oracle projections that remain semantically necessary. |
| F6 | `93cce5f` — Fold call entries into recorder | Deleted the one-definition call-entry leaf and placed the concrete call/create stream projections beside [`RunLog`](../../experiments/005_ir_lowering/LirLean/Spec/Recorder.lean#L34), [`realisedCall`](../../experiments/005_ir_lowering/LirLean/Spec/Recorder.lean#L224), and [`realisedCreate`](../../experiments/005_ir_lowering/LirLean/Spec/Recorder.lean#L230). This makes the recorder the single owner of recorded-oracle reconstruction. |
| F7 | `4e10343` — Flatten byte encoding utility module | Flattened the utility path to [`LirLean/Words.lean`](../../experiments/005_ir_lowering/LirLean/Words.lean#L1) and swept its import/reference sites. |
| F8 | `39e3b36` — Fold charge algebra into bytecode sequence layer | Deleted the standalone charge leaf and placed [`subCharges_snoc`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L67) and [`subCharges_append`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L74) beside [`subCharges`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L62). The two theorem statements and proofs moved verbatim; no theorem statement or proof changed. |
| F9 | `e32ddee` — Refresh refactor-facing source documentation | Corrected source-level module descriptions and deleted stale blocker/path claims after the folds. This commit changed comments only: no definition, theorem statement, or proof changed. |

Run commit log, oldest first:

```text
8edacff Fold IR-free lowering engine into bytecode Hoare layer
d92df8a Dissolve Lir V2 namespace layer
2c9aa21 Rename Assembly layer to CfgSim
6adad22 Delete vestigial Plus layer
ad63e20 Remove dead v1 coupling surface
93cce5f Fold call entries into recorder
4e10343 Flatten byte encoding utility module
39e3b36 Fold charge algebra into bytecode sequence layer
e32ddee Refresh refactor-facing source documentation
```

## Preserved flagship surface

The statement extraction from `bab5e5c:experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean` was diffed against the current source after stripping proof bodies; the diff was empty. These are the current statements, verbatim.

[`lower_conforms`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221) states observable conformance for a recorded lowered-bytecode run and an IR execution driven by the recorded gas, call, and create streams:

```lean
theorem lower_conforms {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
```

[`lower_conforms_exact`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269) strengthens the execution relation to exact oracle-stream consumption:

```lean
theorem lower_conforms_exact {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFromAll prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
```

[`lower_conforms_gasfree`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304) adds the source-level no-gas-read restriction while preserving the same observable conclusion:

```lean
theorem lower_conforms_gasfree {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hng : NoGasReads prog)
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
```

The public vocabulary also remains in the same conceptual layers: [`entryState`](../../experiments/005_ir_lowering/LirLean/Spec/Conformance.lean#L11), [`Conforms`](../../experiments/005_ir_lowering/LirLean/Spec/Conformance.lean#L20), and [`NoGasReads`](../../experiments/005_ir_lowering/LirLean/Spec/Conformance.lean#L24) are reviewer-facing specifications; [`RunFromAll`](../../experiments/005_ir_lowering/LirLean/Spec/Semantics.lean#L189) defines exact stream consumption; [`IRWellFormed`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L517), [`codeFits`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L449), and [`stackFits`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L482) state the static source and scalar budget assumptions; and [`PrecompileAssumptions`](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L31) remains the explicit runtime seam bundle. None of these public meanings was weakened or vacated by the file moves.

## Resulting file and namespace structure

The live package namespace is `Lir`; `Lir.Frame` is retained only for EVM-frame-local/oracle material, and the reusable execution layer is `BytecodeLayer.Hoare`. The current `LirLean/` tree is:

- Root: [`Audit.lean`](../../experiments/005_ir_lowering/LirLean/Audit.lean#L1), [`Call.lean`](../../experiments/005_ir_lowering/LirLean/Call.lean#L1), [`CallRealises.lean`](../../experiments/005_ir_lowering/LirLean/CallRealises.lean#L1), [`IRRun.lean`](../../experiments/005_ir_lowering/LirLean/IRRun.lean#L1), [`Law.lean`](../../experiments/005_ir_lowering/LirLean/Law.lean#L1), [`RecorderLemmas.lean`](../../experiments/005_ir_lowering/LirLean/RecorderLemmas.lean#L1), [`Words.lean`](../../experiments/005_ir_lowering/LirLean/Words.lean#L1)
- `CfgSim/`: [`LowerConforms.lean`](../../experiments/005_ir_lowering/LirLean/CfgSim/LowerConforms.lean#L1), [`LowerDecode.lean`](../../experiments/005_ir_lowering/LirLean/CfgSim/LowerDecode.lean#L1)
- `Decode/`: [`BoundaryCursor.lean`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryCursor.lean#L1), [`BoundaryReach.lean`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryReach.lean#L1), [`DecodeAnchors.lean`](../../experiments/005_ir_lowering/LirLean/Decode/DecodeAnchors.lean#L1), [`DecodeLower.lean`](../../experiments/005_ir_lowering/LirLean/Decode/DecodeLower.lean#L1), [`JumpValid.lean`](../../experiments/005_ir_lowering/LirLean/Decode/JumpValid.lean#L1), [`Layout.lean`](../../experiments/005_ir_lowering/LirLean/Decode/Layout.lean#L1), [`LoweringLemmas.lean`](../../experiments/005_ir_lowering/LirLean/Decode/LoweringLemmas.lean#L1), [`Modellable.lean`](../../experiments/005_ir_lowering/LirLean/Decode/Modellable.lean#L1), [`SegAligned.lean`](../../experiments/005_ir_lowering/LirLean/Decode/SegAligned.lean#L1)
- `Drive/`: [`CallPreservesSelf.lean`](../../experiments/005_ir_lowering/LirLean/Drive/CallPreservesSelf.lean#L1), [`DriveSim.lean`](../../experiments/005_ir_lowering/LirLean/Drive/DriveSim.lean#L1), [`SelfPresent.lean`](../../experiments/005_ir_lowering/LirLean/Drive/SelfPresent.lean#L1)
- `Frame/`: [`Call.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Call.lean#L1), [`Create.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Create.lean#L1), [`Match.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Match.lean#L1), [`StorageErase.lean`](../../experiments/005_ir_lowering/LirLean/Frame/StorageErase.lean#L1)
- `Materialise/`: [`CleanHaltExtract.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/CleanHaltExtract.lean#L1), [`DefsSound.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/DefsSound.lean#L1), [`MatDecLower.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/MatDecLower.lean#L1), [`MaterialiseCleanHalt.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseCleanHalt.lean#L1), [`MaterialiseGas.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseGas.lean#L1), [`MaterialiseRuns.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean#L1), [`MatFoldChannel.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/MatFoldChannel.lean#L1), [`StashTail.lean`](../../experiments/005_ir_lowering/LirLean/Materialise/StashTail.lean#L1)
- `Realisability/`: [`CheckedStep.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/CheckedStep.lean#L1), [`Machinery.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L1), [`Producer.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Producer.lean#L1), [`RealisabilitySpec.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L1), [`SegmentedEval.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/SegmentedEval.lean#L1), [`Surface.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Surface.lean#L1), [`Witness.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Witness.lean#L1), [`WitnessChecks.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/WitnessChecks.lean#L1), [`WitnessParams.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/WitnessParams.lean#L1)
- `Sim/`: [`SimStmt.lean`](../../experiments/005_ir_lowering/LirLean/Sim/SimStmt.lean#L1), [`SimStmts.lean`](../../experiments/005_ir_lowering/LirLean/Sim/SimStmts.lean#L1), [`SimTerm.lean`](../../experiments/005_ir_lowering/LirLean/Sim/SimTerm.lean#L1)
- `Spec/`: [`BudgetDerivations.lean`](../../experiments/005_ir_lowering/LirLean/Spec/BudgetDerivations.lean#L1), [`Conformance.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Conformance.lean#L1), [`IR.lean`](../../experiments/005_ir_lowering/LirLean/Spec/IR.lean#L1), [`Lowering.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean#L1), [`Recorder.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Recorder.lean#L1), [`Seams.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L1), [`Semantics.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Semantics.lean#L1), [`WellFormed.lean`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L1)

This tree has no `V2/`, `Engine/`, `Assembly/`, `Plus/`, or generic `Util/` tier. The exp003 side now places the moved engine alongside the existing sequence, call, outcome, and gas reasoning modules under `BytecodeLayer/Hoare/`; [`Sequence.lean`](../../experiments/003_bytecode_layer/BytecodeLayer/Hoare/Sequence.lean#L1) is the consolidated owner of generic charge-list algebra.

## Skipped or unavailable

| Item | Disposition | Reason |
|---|---|---|
| Supplied seams/migration review | Unavailable | `docs/review/seams-and-migration-2026-07-12.md` does not exist in the checkout, filesystem, or git history. No substitute contents were inferred. |
| Move code into the EVM package | Skipped | Explicitly out of scope. The exp003 → EVM package boundary remains visible in the exp003 [Lake configuration](../../experiments/003_bytecode_layer/lakefile.lean#L4). |
| Split lowering from SIR | Skipped | Explicitly out of scope; lowering-dependent decode and modellability stay in exp005. |
| Fold [`Words.lean`](../../experiments/005_ir_lowering/LirLean/Words.lean#L1) into [`Spec/Lowering.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean#L1) | Deliberately retained | The 16-line module is a small but meaningful audit boundary: prior review moved byte encoders out of the trusted specification surface. F7 removed the artificial `Util/` directory without reversing that separation. |
| Fold [`Frame/Call.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Call.lean#L1) and [`Frame/Create.lean`](../../experiments/005_ir_lowering/LirLean/Frame/Create.lean#L1) away | Deliberately retained | Their oracle projections are still live statement/model vocabulary; F5 removed only the unused coupling machine around them. |
| Move [`Decode/Modellable.lean`](../../experiments/005_ir_lowering/LirLean/Decode/Modellable.lean#L1) to exp003 | Deliberately retained | Its content is lowering-dependent, unlike the IR-free execution engine moved by F1. |

No attempted source fold was abandoned because of a proof failure; the items above are unavailable context or intentional scope/model boundaries.

## Final green gate

Recorded final commands and outcomes:

```text
$ (cd experiments/005_ir_lowering && lake build)
Build completed successfully (1173 jobs).

$ (cd experiments/005_ir_lowering && lake build WIP)
Build completed successfully (1180 jobs).
```

The final importing-module axiom check reported:

```text
'Lir.lower_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_gasfree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The outcome is a smaller, role-named proof tree with one reusable bytecode execution layer and an unchanged reviewer-facing theorem surface. The next architectural work can start from these explicit retained boundaries rather than recreating a versioned or generic `Engine/` tier.
