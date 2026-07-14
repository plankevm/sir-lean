# Experiment 005 clean-split outcome — 2026-07-13

## Result

**PASS.** Phases 0, B0, B1, B2, and A landed on
`refactor/split-five-file-surface`. The EVM-generic execution theory extracted
from experiment 005 now lives in the
[`BytecodeLayer`](../../EVM/BytecodeLayer/) library of the `EVM` package;
experiment 005 imports that package directly and retains the IR-indexed
adapters. The three flagship statements remained frozen, and the final axiom
audit reports exactly `[propext, Classical.choice, Quot.sound]` for each.

Phase C, including the assembler and the remaining re-indexing work, was not
started.

## Phase and commit record

| Phase | Commits | Outcome |
|---|---|---|
| Phase 0 | `559dd269` | Removed `Lir`/`LirLean` ownership from the generic Hoare engine and moved the declarations under `BytecodeLayer.Hoare.*`. |
| B0 | `e59ae1a6` | Hoisted `Observable`, `CallStream`, `CreateStream`, `GasOracle`/`Trace`, and `World` into [`Exec/Observable.lean`](../../EVM/BytecodeLayer/Exec/Observable.lean). |
| B1 | `b3c31593`, `aedcd7d3`, `7044a0b6`, `d8af28aa`, `a41bdd84`, `4c78d6ac`, `1d8fe2fe`, `35ac4da6`, `2b43d6f7`, `608caa0c`, `c4714994`, `de400da0`, `d3337dd8` | Accounted for all 13 planned clean migrations: storage erase, word encoding/decoding, CALL/CREATE oracles, recorder and checked/segmented evaluation, self-presence preservation, call realisability, clean-halt extraction, and seam predicates. [`CleanHaltExtract`](../../experiments/005_ir_lowering/LirLean/Materialise/CleanHaltExtract.lean) correctly retains its IR-specific SLOAD specialization. |
| B1 review cleanup | `6b9723b1` | Removed stale IR/lowering/cross-file allegations and added the grounded [B1 review](./b1-migrations-review-2026-07-13.md). |
| B2 | `b49694cb`, `1bc50999`, `00aa813f`, `574c7ed7`, `391c1638`, `93e731ca`, `2a188960`, `5df82804` | Landed eight green mixed-file cuts: gas bricks, recorder alignment, successful-halt projections, witness checks, modellability, frame simulations, memory/stash invariants, and stash-tail execution. IR-indexed adapters remain in experiment 005. |
| B2 review cleanup | `57e83d07` | Corrected generic/adaptor comments and imports and added the grounded [B2 review](./b2-splits-review-2026-07-13.md). No declaration statement or proof body changed. |
| Phase A | `dbf3aedf` | Moved the completed `BytecodeLayer` tree verbatim into `EVM`, added the `BytecodeLayer` Lean library, changed experiment 005 to `require evm from "../../EVM"`, and reduced experiment 003 to historical documentation plus a [stub README](../../experiments/003_bytecode_layer/README.md). |

The B1 and B2 review cleanups found no new `sorry`, `admit`, `axiom`,
`native_decide`, or `bv_decide`, and both confirmed that the flagship statements
are unchanged from `e59ae1a6`.

## B2 deferrals to Phase C

The relocation-only discipline left three re-indexing tasks for the supervised
assembler phase:

1. **Realisability machinery.** The generic `RecorderCoupled`/boundary engine is
   interleaved with `matRunsC`, `termTies'`, `callRealises`, and the IR value
   channel in
   [`Realisability/Machinery.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean).
   Separating it requires re-indexing rather than moving proof bodies intact.
2. **Materialisation relations.** The generic memory and stash lemmas moved, but
   [`MemRealises` and `StorageAgree`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean)
   still refer directly to IR locals, allocation, and world state. Generalising
   their value source belongs with Phase C.
3. **Decode geometry.** `SegAlignedP`, boundary reach, jump validity, decode/list
   facts, and cursor lemmas remain fused to `lower prog` and the emit ladder
   under [`LirLean/Decode`](../../experiments/005_ir_lowering/LirLean/Decode/).
   They will be re-indexed over the verified assembler rather than mechanically
   relocated.

Nonblocking debt carried forward: the generic theorem name `lower_modellable`
is historical, and the materialisation adapter retains the build-required
`MaterialiseRuns` → `Frame.Match` compatibility import until the namespace/import
graph is re-indexed.

## Final file and namespace structure

[`EVM/lakefile.lean`](../../EVM/lakefile.lean) now exports the `Evm`, `Conform`,
and `BytecodeLayer` libraries. The split execution surface is rooted at
[`BytecodeLayer/Exec.lean`](../../EVM/BytecodeLayer/Exec.lean), which exports the
generic execution leaves:

- `BytecodeLayer.Exec` owns shared observables, CALL/CREATE effects, frame and
  result simulations, gas, memory, stash, and clean-halt execution facts.
- `BytecodeLayer.Exec.Recorder` owns `RunLog`, `runWithLog`, recorder adequacy,
  segmented/checked evaluators, alignment consumers, and executable witness
  checks through [`Exec/Recorder.lean`](../../EVM/BytecodeLayer/Exec/Recorder.lean).
- `BytecodeLayer.Exec.Invariants` owns self/account-presence and execution seam
  predicates through
  [`Exec/Invariants.lean`](../../EVM/BytecodeLayer/Exec/Invariants.lean), with
  generic modellability facts under `BytecodeLayer.Interpreter` and storage-map
  facts under `Evm.Storage`.
- The pre-existing generic run calculus remains under `BytecodeLayer.Hoare.*`,
  including account-map, clean-halt, descent, drive, step-walk, and memory
  algebra modules.
- Experiment 005 retains the `Lir` namespace and only its lowering-, simulation-,
  materialisation-, realisability-, and decode-indexed adapters.

Of the planned five-file target, `Exec.lean`, `Exec/Recorder.lean`, and
`Exec/Invariants.lean` are materialised in the EVM package. `Exec/CyclicSim.lean`
is deferred with the recorder/boundary re-indexing, and `Asm.lean` is explicitly
Phase C. No placeholder files were added for either.

## Final green gate

Fresh post-fold gate output:

```text
EVM / Evm:
Build completed successfully (1101 jobs).

EVM / Conform:
Build completed successfully (1106 jobs).

EVM / BytecodeLayer:
Build completed successfully (1162 jobs).

experiment 005 / default:
Build completed successfully (1187 jobs).

experiment 005 / WIP:
Build completed successfully (1195 jobs).

'Lir.lower_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_gasfree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The branch was pushed after every green migration/split and after the Phase A
fold. This outcome document is the only post-fold change; after its commit and
push, the branch is synchronized with `origin/refactor/split-five-file-surface`.
