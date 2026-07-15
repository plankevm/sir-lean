# Assembler sole-spine outcome

The LIR lowering now has one whole-program byte path. `lowerAsm` performs
instruction selection into `BytecodeLayer.Asm.AsmProgram`, `lowerBytes` exposes
the assembler's resolved bytes, and `lower` wraps the assembler result as a
`ByteArray`. The former whole-program `Lir.emit` / `flatBytes` path,
`bytes_lowerAsm`, `lowerBytes_eq_emit`, and the public `encode_*` reconciliation
ladder are gone. The statements of `Lir.lower_conforms`,
`Lir.lower_conforms_exact`, and `Lir.lower_conforms_gasfree` are unchanged.

## Step outcomes and commits

### S1 — assembler byte accessor bridges

PASS at `e7e32f61656c18662cd00f954509c0b9e8650bb7`, committed and pushed as
`asm-spine: add assembler byte accessor bridges`.

This added `Lir.lowerBytes` and the migration theorems
`lower_eq_lowerBytes`, `lowerBytes_eq_emit`, and
`lowerBytes_eq_flatBytes` without re-pointing consumers. The change was 17
insertions and no deletions. The full gate passed and the three flagship
declarations retained exactly the standard axiom trio.

### S2 — re-index whole-code consumers

The coherent re-indexing commit
`f30db7ce728b8f6d5f261a09d33ee044af45124c` was committed and pushed as
`asm-spine: re-index lowering proofs onto assembler bytes`. It changed the
public geometry and conformance surfaces from `flatBytes` to `lowerBytes` across
decode, CFG simulation, materialisation, budget, and realisability modules.

The S2 review verdict was nevertheless FAIL because nine proof sites still
transported through `lowerBytes_eq_emit`, and the legacy whole-program emitter
and reconciliation ladder still existed in `Spec/Lowering.lean`. An attempted
follow-up for those sites was not committed: `lake build WIP` twice exited 137
while rebuilding `LirLean.Realisability.WitnessChecks`, including a
single-worker retry. Per the task discipline, that attempt was reset to the
pushed commit. The commit itself had previously passed the exact gate with a
warm cache; the failed follow-up was not treated as green.

### S3 — retire the legacy emitter

PASS at `e0d20dc36466e4f83a48e02e54bf6606f8a6d82b`, committed and pushed as
`asm-spine: retire legacy byte emitter`.

This removed the remaining whole-program `Lir.emit`, `flatBytes`,
`bytes_lowerAsm`, `lowerBytes_eq_emit`, and public `encode_*` ladder; changed
the nine remaining consumers to the assembler-defined block-byte view; and
updated the planning appendix to describe the sole-spine state. The heavy
kernel checks were split into the sequential
`WitnessCheckDefs`, `WitnessCheckRun`, and `WitnessCheckCode` modules so the WIP
gate stayed within memory. No flagship statement changed, and no
`sorry`, `admit`, `axiom`, `native_decide`, or `bv_decide` was introduced.

## Net line effect

Relative to the pre-S1 baseline `4982f83`, the three implementation commits
changed 22 files with 505 insertions and 521 deletions: **16 net lines
removed**. Excluding the planning-appendix update, the Lean sources have 486
insertions and 491 deletions: **5 net Lean lines removed**.

The net reduction is smaller than the planning estimate because the byte-local
fragment views remain useful to the existing decode and value proofs, and the
memory-safe witness-check split replaces one large module with three sequential
modules. Neither is a second whole-program lowering path.

## Final file and namespace shape

- `EVM/BytecodeLayer/Asm.lean` owns the IR-independent structured assembler,
  resolution, encoding, `bytes`, and `assemble`. Its generic geometry remains
  in `EVM/BytecodeLayer/Asm/Geometry.lean`.
- `experiments/005_ir_lowering/LirLean/Spec/Lowering.lean` defines the LIR
  instruction-selection fragments under `Lir.Asm`, then defines
  `BytecodeLayer.Asm.lowerAsm : Lir.Program → AsmProgram`.
- The same file defines the only whole-program byte accessors:
  `Lir.lowerBytes prog := bytes (lowerAsm prog)` and
  `Lir.lower prog := assemble (lowerAsm prog)`. The equalities
  `lower_eq_lowerBytes` and `lower_eq_assemble_lowerAsm` are reflexive.
- `Lir.Asm.blockOffset_lowerAsm` is the LIR-specific relocation adapter into
  the generic assembler geometry. Decode geometry and conformance consumers
  are stated over `lowerBytes`.
- Byte-local `Lir.matCache`, `Lir.emitStmt`, `Lir.emitTerm`, and
  `Lir.emitBlockBody` remain as fragment views used to index source constructs
  within assembler output. Private `byteView_*` proofs and the public
  `lowerBytes_eq_blockBytes` expansion justify those views. There is no
  whole-program byte emitter built from them.

The optional generic-geometry step required no new LIR work: the reusable
arbitrary-`AsmProgram` geometry already lives in `BytecodeLayer.Asm.Geometry`,
and LIR now instantiates it through `lowerAsm` and `blockOffset_lowerAsm`.

## Residual and deferred work

Nothing from the requested sole-spine scope is deferred. The fragment views
listed above are intentionally retained because decode, budget, and value
proofs need source-local byte lengths and boundaries; deleting them would be a
separate proof-representation rewrite rather than removal of a competing
lowering. The pre-existing untracked `smithers.db`, `smithers.db-shm`, and
`smithers.db-wal` files remain local and are not committed.

## Final green gate

Both build cones completed successfully:

```text
Build completed successfully (1101 jobs).
Build completed successfully (1106 jobs).
Build completed successfully (1165 jobs).
Build completed successfully (1190 jobs).
Build completed successfully (1201 jobs).
```

The flagship axiom output was exactly:

```text
'Lir.lower_conforms' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lir.lower_conforms_gasfree' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The implementation endpoint is
`e0d20dc36466e4f83a48e02e54bf6606f8a6d82b`, pushed to
`origin/refactor/asm-sole-spine` before this outcome document was added.
