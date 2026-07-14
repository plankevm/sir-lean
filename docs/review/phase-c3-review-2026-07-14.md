# Phase C3 review — assembler decode geometry

## TL;DR

**Pass on the C3 extraction, with one medium-severity API precondition gap before the cursor
predicates become proof inputs.** Commits `f6419443` and
`1ddc2e87` move the reusable list/decode, alignment, valid-jump, block-offset, and cursor facts into
the IR-free [assembler geometry module](../../EVM/BytecodeLayer/Asm/Geometry.lean#L1). The principal
LIR block-placement results are now short transports through
[`lowerAsm`](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean#L254), while the remaining
large LIR files describe source-layout regions and lowering-specific opcode policies rather than
re-proving generic block placement. The three flagship signatures are byte-for-byte unchanged from
the parent of `f6419443`; the supplied handoff reports the full gate green and all three axiom sets
as exactly `[propext, Classical.choice, Quot.sound]` (reported, not re-run here), and a source scan of
all eleven changed Lean files found no `sorry`, `admit`, `axiom`, `native_decide`, or `bv_decide`
command.

## Findings, by severity

### Medium — cursor predicates do not assert that their cursors exist

[`AtEntry`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L744) and
[`AtCursor`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L752) package the intended four frame fields,
but neither includes a block-membership or instruction-membership witness. This matters because
[`cursorPc`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L561) uses a zero default for a missing label
and a saturating list prefix for an oversized instruction index. Consequently the predicates can be
inhabited for a nonexistent block or instruction; by themselves they do not justify applying
[`decode_at_cursor`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L665), whose statement correctly
requires both membership witnesses.

```lean
/-- Frame-level block entry, including the code and valid-jump geometry. -/
def AtEntry (program : AsmProgram) (fr : Frame) (label : Nat)
    (stack : List UInt256) : Prop :=
  fr.exec.executionEnv.code = assemble program ∧
  fr.exec.pc = UInt32.ofNat (blockOffset program label) ∧
  fr.validJumps = validJumpDests (assemble program) 0 ∧
  fr.exec.stack = stack

/-- Frame-level instruction cursor, including the code and valid-jump geometry. -/
def AtCursor (program : AsmProgram) (fr : Frame) (label index : Nat)
    (stack : List UInt256) : Prop :=
  fr.exec.executionEnv.code = assemble program ∧
  fr.exec.pc = UInt32.ofNat (cursorPc program label index) ∧
  fr.validJumps = validJumpDests (assemble program) 0 ∧
  fr.exec.stack = stack
```

No current theorem outside the geometry module consumes either predicate, so no flagship depends on
this gap. Before the planned landing algebra uses them, add validity to the predicates or pair them
with explicit well-formed-cursor premises in every public consumer.

### Resolved during review — dead aliases and stale narration

The review cleanup removed an unused LIR alias of the assembler-owned alignment predicate from
[`JumpValid.lean`](../../experiments/005_ir_lowering/LirLean/Decode/JumpValid.lean#L14), removed an
unused EVM-only byte-predicate projection from
[`BoundaryReach.lean`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryReach.lean#L37), and
rewrote the specialization preface in
[`DecodeLower.lean`](../../experiments/005_ir_lowering/LirLean/Decode/DecodeLower.lean#L42), which had
still called completed byte-layout arithmetic “open C3 work.” The remaining
[`NoCallCreateOp`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryReach.lean#L39), although
EVM-shaped in isolation, is load-bearing throughout the LIR-specific materialisation and terminator
alignment ladder, so keeping that policy in the adapter is defensible. The C3 tag in the title of
[`Layout.lean`](../../experiments/005_ir_lowering/LirLean/Decode/Layout.lean#L3) is historical but not
itself a false status claim.

### Medium — exact jump-destination characterization is not yet exported

The design sketch asks for an exact assembler theorem equating valid jump destinations with block
entries. C3 proves the sound direction
[`blockOffset_validJump`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L536), plus the generic scan
inversion
[`reachesBoundary_of_mem_validJumpDests`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L401), but does
not close those facts into a label-indexed completeness theorem. This does not invalidate the
ported LIR theorem, which only needs the sound direction, but it leaves the assembler surface short
of the design-of-record equality. Close it before claiming the full static geometry API complete.

The current body-only shape of
[`AsmBlock`](../../EVM/BytecodeLayer/Asm.lean#L53)—terminators are ordinary instructions inside the
body produced by
[`Lir.Asm.emitBlock`](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean#L244)—also differs
from the sketch's separate terminator datatype. That choice predates `f6419443` and `1ddc2e87`, so it
is context rather than a defect introduced by C3.

## What was extracted

The target is a small structured language and a deterministic encoder. The central definitions are
[`AsmInstr`, `AsmBlock`, `AsmProgram`, and `assemble`](../../EVM/BytecodeLayer/Asm.lean#L42):

```lean
inductive AsmInstr where
  | push (value : UInt256)
  | pushLabel (label : Nat)
  | op (operation : Op)
deriving DecidableEq, Repr

structure AsmBlock where
  body : List AsmInstr
deriving Repr

structure AsmProgram where
  blocks : Array AsmBlock
deriving Repr

/-- Resolve block relocations and encode a structured assembly program. -/
def assemble (program : AsmProgram) : ByteArray :=
  ⟨(bytes program).toArray⟩
```

The reusable alignment judgment is now
[`SegAlignedP`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L83), independent of any IR:

```lean
inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop where
  | nil : SegAlignedP P []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hP : P (Evm.parseInstr byte))
      (hrest : SegAlignedP P rest) :
      SegAlignedP P (byte :: (imm ++ rest))
```

This supports three main layers:

1. Generic list and decode facts: list-backed byte reads, immediate extraction,
   [`decode_nonpush_of_list`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L36),
   [`decode_push_of_list`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L48), aligned-segment boundary
   transports, and list-region inversion.
2. Whole-program geometry: assembler alignment, block splitting and prefix lengths,
   [`reaches_blockOffset`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L505), block-entry validity, and
   block-entry decoding.
3. Structured cursors: byte positions, instruction decoding, and reachable-opcode classification.

The strongest new instruction-cursor specification is
[`decode_at_cursor`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L665):

```lean
theorem decode_at_cursor (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (instr : AsmInstr)
    (hb : program.blocks.toList[label]? = some block)
    (hi : block.body[index]? = some instr)
    (hbound : cursorPc program label index < 2 ^ 32) :
    Evm.decode (assemble program) (UInt32.ofNat (cursorPc program label index)) =
      some (decodedInstr program instr) := by
```

It covers ordinary operations, literal `PUSH32`, and relocated `PUSH4`. The exhaustive byte
classifier is
[`ByteCursor`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L760), and the boundary-level consequence
is [`reachable_boundary_asmOp`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L796):

```lean
inductive ByteCursor (program : AsmProgram) (position : Nat) : Prop where
  | blockEntry (label : Nat) (block : AsmBlock)
      (hb : program.blocks.toList[label]? = some block)
      (heq : position = blockOffset program label)
  | instr (label : Nat) (block : AsmBlock) (index : Nat) (instruction : AsmInstr)
      (offset : Nat)
      (hb : program.blocks.toList[label]? = some block)
      (hi : block.body[index]? = some instruction)
      (hoffset : offset < (encodeInstr (blockOffset program) instruction).length)
      (heq : position = cursorPc program label index + offset)

theorem reachable_boundary_asmOp (program : AsmProgram) (n : Nat)
    (hreach : ReachesBoundary (assemble program) 0 n)
    (hn : n < (bytes program).length) :
    ∃ byte, (assemble program).get? n = some byte ∧ IsAsmOp (Evm.parseInstr byte) := by
```

These specifications mention only EVM and assembler types. A direct token scan of
[`BytecodeLayer/Asm.lean`](../../EVM/BytecodeLayer/Asm.lean#L1) and the complete
[`BytecodeLayer/Asm/`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L1) tree finds no LIR namespace,
program, lowering, cache, or source-cursor identifier.

## The LIR instantiation

The bridge remains exactly where it belongs: LIR chooses the instruction stream, while the generic
assembler chooses offsets and bytes. The definitions and factorization are
[`lowerAsm` and `lower_eq_assemble_lowerAsm`](../../experiments/005_ir_lowering/LirLean/Spec/Lowering.lean#L251):

```lean
namespace BytecodeLayer.Asm

/-- Translate LIR into structured assembly without choosing block offsets. -/
def lowerAsm (prog : Lir.Program) : AsmProgram :=
  let cache := Lir.Asm.matCache prog
  let alloc := Lir.defsOf prog
  ⟨prog.blocks.map (Lir.Asm.emitBlock cache alloc)⟩

end BytecodeLayer.Asm

namespace Lir

def lower (prog : Program) : ByteArray :=
  BytecodeLayer.Asm.assemble (BytecodeLayer.Asm.lowerAsm prog)

/-- The bytecode lowering factors through the IR-independent assembler. -/
theorem lower_eq_assemble_lowerAsm (prog : Program) :
    lower prog = BytecodeLayer.Asm.assemble (BytecodeLayer.Asm.lowerAsm prog) := rfl
```

The block geometry adapter is now genuinely thin. For example,
[`block_offset_validJump`](../../experiments/005_ir_lowering/LirLean/Decode/JumpValid.lean#L34) only
transports the generic theorem through the block-count and offset bridge:

```lean
theorem block_offset_validJump (prog : Program) (L : Label)
    (hL : L.idx < prog.blocks.size) :
    UInt32.ofNat (offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx) ∈
      validJumpDests (lower prog) 0 := by
```

The larger remaining adapter is intentionally source-indexed:
[`LowerBoundaryCursor`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryCursor.lean#L77)
classifies bytes by LIR statement or terminator region, information the generic assembler cannot
recover from a flat instruction list.

```lean
inductive LowerBoundaryCursor (prog : Program) (b : Nat) : Prop where
  | blockEntry (L : Label) (blk : Block)
      (hb : prog.blocks.toList[L.idx]? = some blk)
      (heq : b = offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx)
  | stmt (L : Label) (blk : Block) (pc k : Nat) (s : Stmt)
      (hb : prog.blocks.toList[L.idx]? = some blk)
      (hs : blk.stmts[pc]? = some s)
      (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length)
      (heq : b = pcOf prog L pc + k)
  | term (L : Label) (blk : Block) (k : Nat)
      (hb : prog.blocks.toList[L.idx]? = some blk)
      (hk : k < (emitTerm (matCache prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk.term).length)
      (heq : b = termOf prog L + k)
```

Similarly, the residual opcode ladders in
[`SegAligned.lean`](../../experiments/005_ir_lowering/LirLean/Decode/SegAligned.lean#L18) and
[`BoundaryReach.lean`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryReach.lean#L37)
express LIR policies: the emitted opcode allow-list, regions without call/create heads, and the
gas-read-free restriction. Those are not generic assembler geometry.

## Changed-file accounting

| File | C3 role |
|---|---|
| [`Asm/Geometry.lean`](../../EVM/BytecodeLayer/Asm/Geometry.lean#L1) | New IR-free owner of generic decode, list, alignment, boundary, block, jump, and cursor facts. |
| [`Decode/BoundaryCursor.lean`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryCursor.lean#L1) | Deletes duplicate generic inversion and terminal-boundary machinery; retains source-region classification. |
| [`Decode/BoundaryReach.lean`](../../experiments/005_ir_lowering/LirLean/Decode/BoundaryReach.lean#L1) | Reuses generic boundary drop, scan inversion, sequential advance, and list facts; retains LIR opcode refinements. |
| [`Decode/DecodeAnchors.lean`](../../experiments/005_ir_lowering/LirLean/Decode/DecodeAnchors.lean#L1) | Imports the relocated geometry needed by its existing source-offset anchors. |
| [`Decode/DecodeLower.lean`](../../experiments/005_ir_lowering/LirLean/Decode/DecodeLower.lean#L1) | Deletes generic list-backed decode proofs and retains two lowered-code specializations. |
| [`Decode/JumpValid.lean`](../../experiments/005_ir_lowering/LirLean/Decode/JumpValid.lean#L1) | Replaces the block-walk proof tower with three transports through the assembler. |
| [`Decode/Layout.lean`](../../experiments/005_ir_lowering/LirLean/Decode/Layout.lean#L1) | Deletes generic list decomposition/index facts; retains LIR offset and source-anchor arithmetic. |
| [`Decode/SegAligned.lean`](../../experiments/005_ir_lowering/LirLean/Decode/SegAligned.lean#L1) | Deletes the generic alignment inductive and transports; retains LIR opcode policies and emission refinements. |
| [`Realisability/Machinery.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/Machinery.lean#L590) | Repoints sequential and taken-jump boundary consumers to the generic declarations. |
| [`Realisability/RealisabilitySpec.lean`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L369) | Repoints two private resume-boundary consumers; public theorem statements are untouched. |
| [`Spec/BudgetDerivations.lean`](../../experiments/005_ir_lowering/LirLean/Spec/BudgetDerivations.lean#L70) | Reuses the generic list split in the LIR program-counter budget proof. |

## Frozen flagships

The statements at
[`lower_conforms`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L221),
[`lower_conforms_exact`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L269),
and
[`lower_conforms_gasfree`](../../experiments/005_ir_lowering/LirLean/Realisability/RealisabilitySpec.lean#L304)
match the pre-C3 source exactly. Their shared hypotheses remain: compiled code selection, writable
state, recipient presence, entry gas, IR well-formedness, code and stack budgets, a clean recorded
run, and precompile seams; the gas-free result adds the source restriction.

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

## Recommendation

Accept the C3 re-indexing with the review cleanup applied. Treat cursor validity and the exact
valid-jump-set theorem as explicit prerequisites for
the later landing/cyclic-simulation work; neither currently affects a flagship. No proof smell
introduced by these commits reaches a headline: the new proofs use structural induction, list
decomposition, arithmetic, and small decidable opcode facts, with no heartbeat crank in the new
geometry module.
