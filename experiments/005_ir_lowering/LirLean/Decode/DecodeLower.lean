import LirLean.Decode.LoweringLemmas
import BytecodeLayer.Asm.Geometry

/-!
# LirLean — decode adapters for lowered programs

The list-backed decode facts are shared assembler geometry. This module relates
`lower prog` to `flatBytes prog` and specializes those facts to the lowered-code
representation consumed by the LIR proofs.

-/

namespace Lir

open Evm
open BytecodeLayer.Asm

/-! ## `lower prog` as a flat byte list -/

/-- The flat byte list `lower prog` wraps: the per-block `JUMPDEST :: body`
concatenation, before `toArray`/`ByteArray`, built from the total fold cache
`matCache prog` and the `defsOf prog` allocation policy, with branch destinations
resolved via `offsetTable`. `lower prog = ⟨(flatBytes prog).toArray⟩`
(`lower_eq_flatBytes`), so byte-indexing `lower prog` is list-indexing
`flatBytes prog`. Fuel-free; total by construction. -/
def flatBytes (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let alloc := defsOf prog
  let labelOff := offsetTable cache alloc prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache alloc labelOff b)

/-- `emit (defsOf prog) prog` is `flatBytes prog`: `emit` runs exactly this per-block
assembly (fold cache + allocation) with `a := defsOf prog`. Definitional. -/
theorem emit_allocate_eq_flatBytes (prog : Program) :
    emit (defsOf prog) prog = flatBytes prog := rfl

/-- `lower prog` is the `ByteArray` wrapping `flatBytes prog`. -/
theorem lower_eq_flatBytes (prog : Program) : lower prog = ⟨(flatBytes prog).toArray⟩ := by
  unfold lower BytecodeLayer.Asm.assemble
  rw [Asm.bytes_lowerAsm, emit_allocate_eq_flatBytes]

/-! ## Specialisations over `lower prog`

The same two lemmas, phrased directly on `lower prog` via `lower_eq_flatBytes`, so a
caller discharges a decode obligation about the lowered program by exhibiting the
byte (and immediate window) of `flatBytes prog` at the pc. The remaining byte-layout
arithmetic (`flatBytes prog`'s byte at `pcOf prog L pc`) is what `PLAN.md` records as
the open C3 work; these are the bricks it plugs into. -/

/-- Non-push decode specialised to `lower prog`. -/
theorem decode_lower_nonpush (prog : Program) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : (flatBytes prog)[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, .none) := by
  rw [lower_eq_flatBytes]; exact decode_nonpush_of_list _ n byte hn hb hnp

/-- Push decode specialised to `lower prog`. -/
theorem decode_lower_push (prog : Program) (n : Nat) (byte : UInt8) (w : UInt8) (imm : UInt256)
    (hn : n < 2 ^ 32) (hb : (flatBytes prog)[n]? = some byte)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((flatBytes prog).toArray).extract (n + 1) (n + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, some (imm, w)) := by
  rw [lower_eq_flatBytes]; exact decode_push_of_list _ n byte w imm hn hb hp hw himm

end Lir
