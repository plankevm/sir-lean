# Experiment 005 Phase C outcome — 2026-07-14

## Result

**PASS.** Phase C de-fused bytecode placement from LIR, extracted the reusable
recorder/cyclic-simulation engine, and re-indexed decode and jump geometry over
the structured assembler. The assembler definitions and reusable theories now
live in the `BytecodeLayer` library; experiment 005 retains the LIR-to-assembly
translation and the source-indexed semantic adapters.

The three flagship statements remained frozen. Their specification blob is
identical to the pre-Phase-C baseline `edc44aff`
(`741166b4ba9c5ae60373cf4b8cdb95f0513b7339`), and the final axiom audit reports
exactly `[propext, Classical.choice, Quot.sound]` for each theorem.

## Step and commit record

| Step | Commit | Outcome |
|---|---|---|
| C1 | `02dcad64` | Added the IR-free structured assembler types and encoder in [`BytecodeLayer.Asm`](../../EVM/BytecodeLayer/Asm.lean). |
| C1 | `e36f6e3d` | Factored LIR byte emission through structured assembly while preserving the emitted byte stream and offsets. |
| C1 | `70b7dff6` | Defined `Lir.lower` as assembly of the structured lowering output. |
| C1 review fix | `85804171` | Moved the LIR adapter name from `Lir.lowerAsm` to `BytecodeLayer.Asm.lowerAsm` and updated all references and design-doc symbols. `Lir.lower = BytecodeLayer.Asm.assemble (BytecodeLayer.Asm.lowerAsm prog)`, and `lower_eq_assemble_lowerAsm` is proved by `rfl`. |
| C2 | `55ec4025` | Moved the IR-free `RecorderCoupled` carrier beside the generic recorder in [`Exec/Recorder.lean`](../../EVM/BytecodeLayer/Exec/Recorder.lean). |
| C2 | `8631766a` | Added the predicate-parametric cyclic invariant driver in [`Exec/CyclicSim.lean`](../../EVM/BytecodeLayer/Exec/CyclicSim.lean). |
| C2 | `e53bb223` | Extracted recorder coupling, event-consumption, descent, and restart theory into the generic cyclic-simulation module. |
| C2 | `741d4894` | Hoisted generic recorder halt projections out of the LIR machinery. |
| C2 review fix | `98bebb03` | Moved seven residual EVM-only bricks into `BytecodeLayer`, placed carrier documentation with its declaration, removed process-history narration, retained LIR compatibility exports, and added the grounded [C2 review](./phase-c2-cyclic-sim-review-2026-07-14.md). |
| C3 | `f6419443` | Re-indexed generic list/decode, segment alignment, block-offset, block-entry, and valid-jump facts over `AsmProgram` in [`Asm/Geometry.lean`](../../EVM/BytecodeLayer/Asm/Geometry.lean). |
| C3 | `1ddc2e87` | Added structured byte cursors and frame-level `AtEntry`/`AtCursor` assembler geometry; reduced LIR geometry proofs to transports and source-region refinements. |
| C3 review fix | `f0712224` | Removed the dead `Lir.SegAligned` alias and `noCallCreate_of_byte`, corrected stale C3 narration, and added the grounded [C3 review](./phase-c3-review-2026-07-14.md). |
| C3 completion | `8bf8df30` | Strengthened cursors with existence witnesses, added cursor reachability and instruction-offset results, and proved `mem_validJumpDests_assemble_iff`: valid jump destinations are exactly `entryPcSet`. |

Every implementation/review step passed the full green gate and was pushed to
`origin/refactor/phase-c-assembler` before the next step began.

## Re-indexing outcome and deferrals

Two of the three B2 Phase C deferrals are now closed:

1. **Realisability machinery:** the recorder carrier and cyclic fold are now
   IR-free. [`LirLean/Realisability/Machinery.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean)
   instantiates the generic fold with LIR boundary geometry and retains only the
   materialisation, term-tie, value-channel, realisation, and consumer-shaped
   CALL/CREATE dispatch composition. Those dispatch adapters remain LIR-side
   because their stack and resume interfaces encode current lowering policy.
2. **Decode geometry:** assembler alignment, byte classification, decode,
   block placement, cursor, reachability, and exact valid-jump theory are now
   indexed by `AsmProgram`. The files under
   [`LirLean/Decode`](../../experiments/005_ir_lowering/LirLean/Decode/) retain
   source statement/terminator regions, emitted-opcode policies, and short
   transports through `lowerAsm`. No C3 geometry deferral remains.

The remaining B2 deferral is **materialisation relations**.
[`MemRealises` and `StorageAgree`](../../experiments/005_ir_lowering/LirLean/Materialise/MaterialiseRuns.lean)
still depend directly on LIR locals, allocation, IR state, and world state.
Generalising their value source would be a separate semantic interface design,
not assembler or decode re-indexing, so Phase C leaves them in the LIR adapter.

## Resulting surface

- [`EVM/BytecodeLayer/Asm.lean`](../../EVM/BytecodeLayer/Asm.lean) owns
  `BytecodeLayer.Asm.AsmInstr`, `AsmBlock`, `AsmProgram`, relocation resolution,
  byte encoding, offsets, and `assemble`.
- [`EVM/BytecodeLayer/Asm/Geometry.lean`](../../EVM/BytecodeLayer/Asm/Geometry.lean)
  owns the IR-free alignment, decode, block/cursor reachability, entry/cursor
  frame predicates, and exact valid-jump theory.
- [`EVM/BytecodeLayer/Exec/Recorder.lean`](../../EVM/BytecodeLayer/Exec/Recorder.lean)
  owns `BytecodeLayer.Exec.Recorder.RecorderCoupled`; [`Exec/CyclicSim.lean`](../../EVM/BytecodeLayer/Exec/CyclicSim.lean)
  owns the generic EVM run fold and recorder transition/extraction lemmas.
- [`LirLean/Spec/Lowering.lean`](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean)
  defines the LIR-dependent `BytecodeLayer.Asm.lowerAsm` adapter and the thin
  `Lir.lower` composition. LIR emission chooses structured instructions;
  `assemble` chooses byte placement and resolves label relocations.
- [`LirLean/Realisability/Machinery.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean),
  [`Realisability/Surface.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Surface.lean),
  and the residual `LirLean/Decode` modules retain LIR correspondence,
  materialisation/value-channel obligations, source-region classification, and
  lowering-policy adapters.

No new `sorry`, `admit`, `axiom`, `native_decide`, or `bv_decide` was introduced.

## Final green gate

Fresh post-documentation gate output:

```text
EVM / Evm:
Build completed successfully (1101 jobs).

EVM / Conform:
Build completed successfully (1106 jobs).

EVM / BytecodeLayer:
Build completed successfully (1165 jobs).

experiment 005 / default:
Build completed successfully (1190 jobs).

experiment 005 / WIP:
Build completed successfully (1198 jobs).

'Lir.lower_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_gasfree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The outcome document is the only change after `8bf8df30`. After its green-gated
commit and push, the branch is synchronized with
`origin/refactor/phase-c-assembler`.
