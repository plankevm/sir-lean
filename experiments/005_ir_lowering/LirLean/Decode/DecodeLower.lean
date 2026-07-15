import LirLean.Decode.LoweringLemmas
import BytecodeLayer.Asm.Geometry

/-!
# LirLean — decode adapters for lowered programs

The list-backed decode facts are shared assembler geometry. This module relates
`lower prog` to `lowerBytes prog` and specializes those facts to the lowered-code
representation consumed by the LIR proofs.

-/

namespace Lir

open Evm
open BytecodeLayer.Asm

/-! ## Specialisations over `lower prog`

The same two lemmas, phrased directly on `lower prog` via `lower_eq_lowerBytes`, so a
caller discharges a decode obligation about the lowered program by exhibiting the
byte (and immediate window) of `lowerBytes prog` at the pc. Source-layout adapters
supply these byte facts at LIR statement and terminator cursors. -/

/-- Non-push decode specialised to `lower prog`. -/
theorem decode_lower_nonpush (prog : Program) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : (lowerBytes prog)[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, .none) := by
  rw [lower_eq_lowerBytes]; exact decode_nonpush_of_list _ n byte hn hb hnp

/-- Push decode specialised to `lower prog`. -/
theorem decode_lower_push (prog : Program) (n : Nat) (byte : UInt8) (w : UInt8) (imm : UInt256)
    (hn : n < 2 ^ 32) (hb : (lowerBytes prog)[n]? = some byte)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
              ⟨((lowerBytes prog).toArray).extract (n + 1) (n + 1 + w.toNat)⟩ = imm) :
    Evm.decode (lower prog) (UInt32.ofNat n) = some (Evm.parseInstr byte, some (imm, w)) := by
  rw [lower_eq_lowerBytes]; exact decode_push_of_list _ n byte w imm hn hb hp hw himm

end Lir
