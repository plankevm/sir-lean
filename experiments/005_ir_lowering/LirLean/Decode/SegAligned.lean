import LirLean.Decode.DecodeLower
import BytecodeLayer.Asm.Geometry

/-!
# LirLean — opcode refinements for assembler-aligned lowering

Instruction alignment and its boundary transports are shared assembler geometry.
This module defines the lowering-specific opcode predicate, proves it for each LIR
emission form, and transports the assembler's whole-program alignment theorem to
`flatBytes prog`.
-/

namespace Lir

open Evm
open BytecodeLayer.Asm

/-! ## §4 — the tightest predicate: `IsLoweringOp`

The R6 boundary walk currently uses this shared predicate, so it still admits bare `CREATE` as an
engine boundary opcode. `emitStmt .create` itself emits only `CREATE2`. -/

/-- The 18 opcodes admitted by the shared lowering/boundary predicate (`STOP, ADD, LT, POP, MLOAD,
MSTORE, SLOAD, SSTORE, JUMP, JUMPI, GAS, JUMPDEST, PUSH4, PUSH32, CALL, RETURN`, plus the
CREATE-family boundary opcodes). -/
def IsLoweringOp (op : Operation) : Prop :=
  op = .STOP ∨ op = .ADD ∨ op = .LT ∨ op = .POP ∨ op = .MLOAD
    ∨ op = .MSTORE ∨ op = .SLOAD ∨ op = .SSTORE ∨ op = .JUMP
    ∨ op = .JUMPI ∨ op = .GAS ∨ op = .JUMPDEST ∨ op = .PUSH4
    ∨ op = .PUSH32 ∨ op = .CALL ∨ op = .RETURN
    ∨ op = .System .CREATE ∨ op = .System .CREATE2

instance (op : Operation) : Decidable (IsLoweringOp op) := by unfold IsLoweringOp; infer_instance

/-! ## §5 — the emission bricks are `IsLoweringOp`-aligned

Every emission helper produces a `SegAlignedP IsLoweringOp` segment: each emitted opcode is a
concrete lowering byte (`decide` discharges `IsLoweringOp (parseInstr byte)` for each emitted op),
and the immediate widths match `pushArgWidth` by construction. -/

theorem segAlignedP_emitImm (w : Word) : SegAlignedP IsLoweringOp (emitImm w) := by
  refine SegAlignedP.push Byte.push32 (BytecodeLayer.Exec.wordBytesBE w) ?_ (by decide)
  show (BytecodeLayer.Exec.wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [BytecodeLayer.Exec.wordBytesBE, Evm.pushArgWidth]

theorem segAlignedP_emitDest (off : Nat) : SegAlignedP IsLoweringOp (emitDest off) := by
  refine SegAlignedP.push Byte.push4 (BytecodeLayer.Exec.offsetBytesBE off) ?_ (by decide)
  show (BytecodeLayer.Exec.offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [BytecodeLayer.Exec.offsetBytesBE, Evm.pushArgWidth]

theorem segAlignedP_slot (slot : Nat) :
    SegAlignedP IsLoweringOp (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAlignedP_emitImm (UInt256.ofNat slot)).append
    (SegAlignedP.nonpush Byte.mload (by decide) (by decide))

/-! ## §6 — the fold cache is `IsLoweringOp`-aligned pointwise (UNCONDITIONAL)

Proven DIRECTLY over `matCache`/`matExpr`/`matStep` by structural induction — NO fuel. The
engine is `segAlignedP_matExpr` (operand lookups discharged by the pointwise-alignment
hypothesis on the cache) plus `matFold_aligned` (list induction: `matStep` preserves
pointwise-alignment), giving `segAlignedP_matCache` UNCONDITIONALLY (the initial cache
`emitImm 0` is aligned). The `emitStmt`/`emitTerm`/`emitBlockBody`/`flatBytes` ladder then
reuses `SegAlignedP.append` over the per-construct opcode shape. -/

/-- **The fold value channel is aligned pointwise.** If every operand's cached bytes are
`IsLoweringOp`-aligned, then `matExpr cache e` is aligned for every expression `e`. Case analysis
on `e`; operand lookups discharged by `hcache`, composites glued by `SegAlignedP.append`. -/
theorem segAlignedP_matExpr (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) :
    ∀ e, SegAlignedP IsLoweringOp (matExpr cache e) := by
  intro e
  cases e with
  | imm w => exact segAlignedP_emitImm w
  | tmp t => exact hcache t
  | add a b =>
      rw [matExpr_add]
      exact ((hcache b).append (hcache a)).append
            (SegAlignedP.nonpush Byte.add (by decide) (by decide))
  | lt a b =>
      rw [matExpr_lt]
      exact ((hcache b).append (hcache a)).append
            (SegAlignedP.nonpush Byte.lt (by decide) (by decide))
  | sload k =>
      rw [matExpr_sload]
      exact (hcache k).append (SegAlignedP.nonpush Byte.sload (by decide) (by decide))
  | gas =>
      rw [matExpr_gas]
      exact SegAlignedP.nonpush Byte.gas (by decide) (by decide)

/-- A `Loc`'s materialised bytes under an aligned cache are aligned. -/
theorem segAlignedP_matLoc (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) :
    ∀ loc, SegAlignedP IsLoweringOp (matLoc cache loc)
  | .remat e => segAlignedP_matExpr cache hcache e
  | .slot n  => segAlignedP_slot n

/-- **`matStep` preserves pointwise-alignment.** Extending an aligned cache by binding one tmp to
its `Loc`'s (aligned) bytes keeps the cache pointwise-aligned — the update is aligned at the bound
key (`segAlignedP_matLoc`) and unchanged elsewhere. -/
theorem matStep_aligned (c : Tmp → List UInt8)
    (hc : ∀ t, SegAlignedP IsLoweringOp (c t)) (p : Tmp × Loc) :
    ∀ t, SegAlignedP IsLoweringOp (matStep c p t) := by
  intro t
  simp only [matStep, Function.update_apply]
  by_cases h : t = p.1
  · rw [if_pos h]; exact segAlignedP_matLoc c hc p.2
  · rw [if_neg h]; exact hc t

/-- **The fold preserves pointwise-alignment.** From an aligned initial cache, the whole `matFold`
over any def-env is pointwise-aligned. List induction, `matStep_aligned` at each step. -/
theorem matFold_aligned (init : Tmp → List UInt8)
    (hinit : ∀ t, SegAlignedP IsLoweringOp (init t)) (l : List (Tmp × Loc)) :
    ∀ t, SegAlignedP IsLoweringOp (matFold init l t) := by
  induction l generalizing init with
  | nil => simpa [matFold] using hinit
  | cons p rest ih =>
      rw [matFold_cons]
      exact ih (matStep init p) (matStep_aligned init hinit p)

/-- **`matCache prog` is pointwise `IsLoweringOp`-aligned, UNCONDITIONALLY.** The initial cache
`fun _ => emitImm 0` is aligned, and the fold preserves alignment. No well-formedness hypothesis. -/
theorem segAlignedP_matCache (prog : Program) :
    ∀ t, SegAlignedP IsLoweringOp (matCache prog t) := by
  unfold matCache
  exact matFold_aligned _ (fun _ => segAlignedP_emitImm 0) (defEnv prog)

/-- A statement's emitted bytes are aligned under an aligned cache. Operand lookups discharged
by `hcache`; the `assign` def-site uses `segAlignedP_matExpr`. -/
theorem segAlignedP_emitStmt (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc) (s : Stmt) :
    SegAlignedP IsLoweringOp (emitStmt cache alloc s) := by
  cases s with
  | assign t e =>
      rw [show emitStmt cache alloc (.assign t e)
            = (match alloc t with
               | some (.slot n) => matExpr cache e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
               | _ => []) from rfl]
      cases alloc t with
      | none => exact .nil
      | some loc =>
          cases loc with
          | remat => exact .nil
          | slot n =>
              exact ((segAlignedP_matExpr cache hcache e).append
                      (segAlignedP_emitImm (UInt256.ofNat n))).append
                    (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))
  | sstore key value =>
      rw [show emitStmt cache alloc (.sstore key value)
            = cache value ++ cache key ++ [Byte.sstore] from rfl]
      exact ((hcache value).append (hcache key)).append
            (SegAlignedP.nonpush Byte.sstore (by decide) (by decide))
  | call cs =>
      rw [show emitStmt cache alloc (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ cache cs.callee
              ++ cache cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAlignedP_emitImm (0 : Word)).append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (segAlignedP_emitImm 0)
      have h := h.append (hcache cs.callee)
      have h := h.append (hcache cs.gasFwd)
      have h := h.append (SegAlignedP.nonpush Byte.call (by decide) (by decide))
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedP_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))
  | create cs =>
      rw [show emitStmt cache alloc (.create cs)
            = cache cs.salt ++ cache cs.initSize ++ cache cs.initOffset ++ cache cs.value
              ++ [Byte.create2]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (hcache cs.salt).append (hcache cs.initSize)
      have h := h.append (hcache cs.initOffset)
      have h := h.append (hcache cs.value)
      have h := h.append (SegAlignedP.nonpush Byte.create2 (by decide) (by decide))
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) (by decide)
      | some t =>
          exact (segAlignedP_emitImm (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))

/-- A terminator's emitted bytes are aligned under an aligned cache. -/
theorem segAlignedP_emitTerm (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (labelOff : Nat → Nat) (t : Term) :
    SegAlignedP IsLoweringOp (emitTerm cache labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm cache labelOff (.ret tt)
            = cache tt ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32
                ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((((hcache tt).append
              (segAlignedP_emitImm 0)).append
              (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))).append
              (segAlignedP_emitImm 32)).append (segAlignedP_emitImm 0)).append
            (SegAlignedP.nonpush Byte.ret (by decide) (by decide))
  | stop =>
      rw [show emitTerm cache labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedP.nonpush Byte.stop (by decide) (by decide)
  | jump dst =>
      rw [show emitTerm cache labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedP_emitDest _).append
        (SegAlignedP.nonpush Byte.jump (by decide) (by decide))
  | branch cond thenL elseL =>
      rw [show emitTerm cache labelOff (.branch cond thenL elseL)
            = cache cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((hcache cond).append
              (segAlignedP_emitDest _)).append
              (SegAlignedP.nonpush Byte.jumpi (by decide) (by decide))).append
              (segAlignedP_emitDest _)).append
            (SegAlignedP.nonpush Byte.jump (by decide) (by decide))

/-- A block body's emitted bytes are aligned under an aligned cache. -/
theorem segAlignedP_emitBlockBody (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedP IsLoweringOp (emitBlockBody cache alloc labelOff b) := by
  unfold emitBlockBody
  refine SegAlignedP.append ?_ (segAlignedP_emitTerm cache hcache labelOff b.term)
  induction b.stmts with
  | nil => exact .nil
  | cons s rest ih =>
      rw [List.flatMap_cons]
      exact (segAlignedP_emitStmt cache hcache alloc s).append ih

/-- A lowered block `JUMPDEST :: emitBlockBody` is `IsLoweringOp`-aligned: the leading
`JUMPDEST` is a zero-width lowering opcode, the body is aligned. -/
theorem segAlignedP_loweredBlock (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) :
    SegAlignedP IsLoweringOp (Byte.jumpdest :: emitBlockBody cache alloc labelOff b) := by
  have hjd : SegAlignedP IsLoweringOp [Byte.jumpdest] :=
    SegAlignedP.nonpush Byte.jumpdest (by decide) (by decide)
  have := hjd.append (segAlignedP_emitBlockBody cache hcache alloc labelOff b)
  simpa using this

/-- **The whole flat byte stream `flatBytes prog` is `IsLoweringOp`-aligned, UNCONDITIONALLY.**
The `flatMap` of per-block `JUMPDEST :: emitBlockBody`, each aligned
(`segAlignedP_loweredBlock`, cache aligned by `segAlignedP_matCache`), glued by
`SegAlignedP.append`. No well-formedness hypothesis. -/
theorem segAlignedP_flatBytes (prog : Program) :
    SegAlignedP IsLoweringOp (flatBytes prog) := by
  have h := BytecodeLayer.Asm.segAlignedP_bytes (BytecodeLayer.Asm.lowerAsm prog)
  rw [Asm.bytes_lowerAsm, emit_allocate_eq_flatBytes] at h
  exact h.mono (by
    intro op hop
    unfold BytecodeLayer.Asm.IsAsmOp at hop
    unfold IsLoweringOp
    tauto)

end Lir
