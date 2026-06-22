import LirLean.IR
import Evm

/-!
# LirLean — lowering IR → EVM bytecode (C1: type signature + a compiling body)

`lower : Program → ByteArray` emits opcode bytes that exp003's `Evm.decode`
(`EVMLean/Evm/Semantics/Decode.lean`) reads back as the intended opcode stream.
See `docs/ir-design.md` §4 for the layout (per-block `JUMPDEST`, two-pass offset
table, uniform `PUSH4` destination width) and the per-op opcode templates.

C1 scope: this module provides the **lowering type signature** with a *concrete,
compiling, `sorry`-free* body. The body's *correctness* (`decode (lower prog)` =
the intended opcodes; the simulation/preservation theorems) is **not** proved here
— that is C2/C3. No theorem in this file is stated, so nothing here is axiom- or
`sorry`-backed; it is executable byte emission only.

Opcode bytes (confirmed against `EVMLean/Evm/Instr.lean`):
`STOP 0x00`, `ADD 0x01`, `LT 0x10`, `SLOAD 0x54`, `SSTORE 0x55`, `JUMP 0x56`,
`JUMPI 0x57`, `GAS 0x5a`, `JUMPDEST 0x5b`, `PUSH1 0x60`, `PUSH4 0x63`,
`PUSH32 0x7f`, `CALL 0xf1`, `RETURN 0xf3`.
-/

namespace Lir

open Evm

/-! ## Opcode bytes (a thin local table, kept in sync with `Evm.Instr`) -/

namespace Byte
def stop     : UInt8 := 0x00
def add      : UInt8 := 0x01
def lt       : UInt8 := 0x10
def sload    : UInt8 := 0x54
def sstore   : UInt8 := 0x55
def jump     : UInt8 := 0x56
def jumpi    : UInt8 := 0x57
def gas      : UInt8 := 0x5a
def jumpdest : UInt8 := 0x5b
def push1    : UInt8 := 0x60
def push4    : UInt8 := 0x63
def push32   : UInt8 := 0x7f
def call     : UInt8 := 0xf1
def ret      : UInt8 := 0xf3
end Byte

/-- Uniform destination push width: jump targets are emitted as `PUSH4 <off>` so a
32-bit pc (`decode` uses `UInt32`) always fits and every block's size is
push-width-independent — making the offset table a simple prefix sum. -/
def destPushBytes : Nat := 1 + 4  -- PUSH4 opcode + 4 immediate bytes

/-- Big-endian 4-byte encoding of a `Nat` jump destination (low 32 bits). -/
def offsetBytesBE (n : Nat) : List UInt8 :=
  [ UInt8.ofNat (n >>> 24), UInt8.ofNat (n >>> 16),
    UInt8.ofNat (n >>> 8),  UInt8.ofNat n ]

/-- 32-byte big-endian encoding of a word (for `PUSH32 imm`). -/
def wordBytesBE (w : Word) : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat ((w >>> (UInt256.ofNat ((31 - i) * 8))).toNat))

/-! ## Per-construct emission (operands assumed already materialised) -/

/-- Emit a literal push (`PUSH32 w`). -/
def emitImm (w : Word) : List UInt8 := Byte.push32 :: wordBytesBE w

/-- Emit a destination push (`PUSH4 off`). -/
def emitDest (off : Nat) : List UInt8 := Byte.push4 :: offsetBytesBE off

/-- Emit the opcode bytes for one statement. NOTE: operand-materialisation onto
the stack (recompute / DUP-SWAP shuffling per `docs/ir-design.md` §4) is a C2
concern; here we emit only the *consuming* opcode template so the byte lengths and
opcode sequence are pinned. C2 refines operand handling. -/
def emitStmt : Stmt → List UInt8
  | .assign _ e =>
    match e with
    | .imm w   => emitImm w
    | .tmp _   => []          -- a pure rename; resolved by stack discipline in C2
    | .add _ _ => [Byte.add]
    | .lt _ _  => [Byte.lt]
    | .sload _ => [Byte.sload]
    | .gas     => [Byte.gas]
  | .sstore _ _ => [Byte.sstore]
  | .call _     => [Byte.call]

/-- Emit the opcode bytes for a terminator, given the resolved offset table
`labelOff` (label index → byte offset of its `JUMPDEST`). -/
def emitTerm (labelOff : Nat → Nat) : Term → List UInt8
  | .ret _              => [Byte.ret]
  | .stop               => [Byte.stop]
  | .jump dst           => emitDest (labelOff dst.idx) ++ [Byte.jump]
  | .branch _ thenL elseL =>
      emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
      ++ emitDest (labelOff elseL.idx) ++ [Byte.jump]

/-- Bytes of one block, *excluding* the leading `JUMPDEST`, given the offset
table. (Two-pass: pass 1 measures lengths with a zero offset table to build the
table; pass 2 emits with the real table — both use this same function, so lengths
agree because `emitDest` width is fixed at `destPushBytes`.) -/
def emitBlockBody (labelOff : Nat → Nat) (b : Block) : List UInt8 :=
  (b.stmts.flatMap emitStmt) ++ emitTerm labelOff b.term

/-- Length of a lowered block (leading `JUMPDEST` + body). Independent of the
offset table because destination pushes have fixed width. -/
def blockLen (b : Block) : Nat :=
  1 + (emitBlockBody (fun _ => 0) b).length

/-- The offset table: byte offset of block `i`'s `JUMPDEST`, as a prefix sum of
block lengths over `blocks[0..i)`. -/
def offsetTable (blocks : Array Block) (i : Nat) : Nat :=
  ((blocks.toList.take i).map blockLen).sum

/-- **The lowering.** `lower prog` is the concatenation, in block order, of each
block lowered as `JUMPDEST :: emitBlockBody`. Branch destinations are resolved via
`offsetTable`. The result is a `ByteArray` intended to satisfy
`Evm.decode (lower prog) (offsetTable …) = …` (the decode-correctness lemma is
C2). -/
def lower (prog : Program) : ByteArray :=
  let labelOff := offsetTable prog.blocks
  let bytes : List UInt8 :=
    prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody labelOff b)
  ⟨bytes.toArray⟩

end Lir
