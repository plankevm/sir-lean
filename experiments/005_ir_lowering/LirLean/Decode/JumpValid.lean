import LirLean.Decode.SegAligned
import LirLean.Decode.Layout
import LirLean.Decode.DecodeAnchors
import BytecodeLayer.Asm.Geometry

/-!
# LIR block placement through the verified assembler

The bytecode geometry is proved for every `AsmProgram` in `BytecodeLayer.Asm.Geometry`.
This module only transports the block-offset, valid-jump, and landing-decode facts through
`BytecodeLayer.Asm.lowerAsm`.
-/

namespace Lir

open Evm

theorem lower_get?_eq (prog : Program) (n : Nat) :
    (lower prog).get? n = (flatBytes prog)[n]? := by
  rw [lower_eq_flatBytes]
  exact BytecodeLayer.Asm.bget (flatBytes prog) n

theorem reaches_block_offset (prog : Program) :
    ∀ i, i ≤ prog.blocks.size →
      ReachesBoundary (lower prog) 0
        (offsetTable (matCache prog) (defsOf prog) prog.blocks i) := by
  intro i hi
  have h := BytecodeLayer.Asm.reaches_blockOffset (BytecodeLayer.Asm.lowerAsm prog) i
  have hsize : (BytecodeLayer.Asm.lowerAsm prog).blocks.size = prog.blocks.size := by
    simp [BytecodeLayer.Asm.lowerAsm]
  rw [Asm.blockOffset_lowerAsm] at h
  exact h (by simpa [hsize] using hi)

theorem block_offset_validJump (prog : Program) (L : Label)
    (hL : L.idx < prog.blocks.size) :
    UInt32.ofNat (offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx) ∈
      validJumpDests (lower prog) 0 := by
  have h := BytecodeLayer.Asm.blockOffset_validJump
    (BytecodeLayer.Asm.lowerAsm prog) L.idx
  have hsize : (BytecodeLayer.Asm.lowerAsm prog).blocks.size = prog.blocks.size := by
    simp [BytecodeLayer.Asm.lowerAsm]
  rw [Asm.blockOffset_lowerAsm] at h
  exact h (by simpa [hsize] using hL)

theorem decode_at_block_offset_jumpdest (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hbound : offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx < 2 ^ 32) :
    Evm.decode (lower prog)
        (UInt32.ofNat (offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx)) =
      some (.Smsf .JUMPDEST, .none) := by
  have hb' : (BytecodeLayer.Asm.lowerAsm prog).blocks.toList[L.idx]? =
      some (Lir.Asm.emitBlock (Lir.Asm.matCache prog) (defsOf prog) b) := by
    simpa [BytecodeLayer.Asm.lowerAsm] using
      congrArg (Option.map (Lir.Asm.emitBlock (Lir.Asm.matCache prog) (defsOf prog))) hb
  have h := BytecodeLayer.Asm.decode_at_blockOffset_jumpdest
    (BytecodeLayer.Asm.lowerAsm prog) L.idx
    (Lir.Asm.emitBlock (Lir.Asm.matCache prog) (defsOf prog) b) hb'
  rw [Asm.blockOffset_lowerAsm] at h
  exact h hbound

end Lir
