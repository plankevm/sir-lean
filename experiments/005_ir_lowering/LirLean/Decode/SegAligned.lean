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

/-! ## §5 — the parameterized emission ladder

The predicates below record only the opcode leaves emitted by each LIR construct.  The alignment
proof follows the lowering structure once, for an arbitrary opcode predicate `P`; concrete
refinements only prove the corresponding leaf facts. -/

def ExprOpLeaves (P : Operation → Prop) : Expr → Prop
  | .imm _ => P (Evm.parseInstr Byte.push32)
  | .tmp _ => True
  | .add _ _ => P (Evm.parseInstr Byte.add)
  | .lt _ _ => P (Evm.parseInstr Byte.lt)
  | .sload _ => P (Evm.parseInstr Byte.sload)
  | .gas => P (Evm.parseInstr Byte.gas)

def LocOpLeaves (P : Operation → Prop) : Loc → Prop
  | .remat e => ExprOpLeaves P e
  | .slot _ => P (Evm.parseInstr Byte.push32) ∧ P (Evm.parseInstr Byte.mload)

def StmtOpLeaves (P : Operation → Prop) : Stmt → Prop
  | .assign _ e => ExprOpLeaves P e ∧ P (Evm.parseInstr Byte.push32) ∧
      P (Evm.parseInstr Byte.mstore)
  | .sstore _ _ => P (Evm.parseInstr Byte.sstore)
  | .call _ => P (Evm.parseInstr Byte.push32) ∧ P (Evm.parseInstr Byte.call) ∧
      P (Evm.parseInstr Byte.mstore) ∧ P (Evm.parseInstr Byte.pop)
  | .create _ => P (Evm.parseInstr Byte.create2) ∧ P (Evm.parseInstr Byte.push32) ∧
      P (Evm.parseInstr Byte.mstore) ∧ P (Evm.parseInstr Byte.pop)

def TermOpLeaves (P : Operation → Prop) : Term → Prop
  | .ret _ => P (Evm.parseInstr Byte.push32) ∧ P (Evm.parseInstr Byte.mstore) ∧
      P (Evm.parseInstr Byte.ret)
  | .stop => P (Evm.parseInstr Byte.stop)
  | .jump _ => P (Evm.parseInstr Byte.push4) ∧ P (Evm.parseInstr Byte.jump)
  | .branch _ _ _ => P (Evm.parseInstr Byte.push4) ∧ P (Evm.parseInstr Byte.jumpi) ∧
      P (Evm.parseInstr Byte.jump)

theorem segAlignedP_emitImm_of {P : Operation → Prop}
    (hP : P (Evm.parseInstr Byte.push32)) (w : Word) : SegAlignedP P (emitImm w) := by
  refine SegAlignedP.push Byte.push32 (BytecodeLayer.Exec.wordBytesBE w) ?_ hP
  show (BytecodeLayer.Exec.wordBytesBE w).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push32)).toNat
  rw [show Evm.parseInstr Byte.push32 = .Push .PUSH32 from rfl]
  simp [BytecodeLayer.Exec.wordBytesBE, Evm.pushArgWidth]

theorem segAlignedP_emitDest_of {P : Operation → Prop}
    (hP : P (Evm.parseInstr Byte.push4)) (off : Nat) : SegAlignedP P (emitDest off) := by
  refine SegAlignedP.push Byte.push4 (BytecodeLayer.Exec.offsetBytesBE off) ?_ hP
  show (BytecodeLayer.Exec.offsetBytesBE off).length = (Evm.pushArgWidth (Evm.parseInstr Byte.push4)).toNat
  rw [show Evm.parseInstr Byte.push4 = .Push .PUSH4 from rfl]
  simp [BytecodeLayer.Exec.offsetBytesBE, Evm.pushArgWidth]

theorem segAlignedP_slot_of {P : Operation → Prop}
    (hpush : P (Evm.parseInstr Byte.push32)) (hload : P (Evm.parseInstr Byte.mload))
    (slot : Nat) : SegAlignedP P (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  (segAlignedP_emitImm_of hpush (UInt256.ofNat slot)).append
    (SegAlignedP.nonpush Byte.mload (by decide) hload)

/-! ## §6 — parameterized cache and construct alignment

The structural inductions over expressions and the materialization fold are generic in `P`.
The `IsLoweringOp` theorems below are compatibility wrappers that discharge their leaf facts. -/

/-- If the cache is `P`-aligned and an expression's emitted leaves satisfy `P`, its materialized
bytes are `P`-aligned. -/
theorem segAlignedP_matExpr_of {P : Operation → Prop} (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP P (cache t)) :
    ∀ e, ExprOpLeaves P e → SegAlignedP P (matExpr cache e) := by
  intro e hleaves
  cases e with
  | imm w => exact segAlignedP_emitImm_of hleaves w
  | tmp t => exact hcache t
  | add a b =>
      rw [matExpr_add]
      exact ((hcache b).append (hcache a)).append
            (SegAlignedP.nonpush Byte.add (by decide) hleaves)
  | lt a b =>
      rw [matExpr_lt]
      exact ((hcache b).append (hcache a)).append
            (SegAlignedP.nonpush Byte.lt (by decide) hleaves)
  | sload k =>
      rw [matExpr_sload]
      exact (hcache k).append (SegAlignedP.nonpush Byte.sload (by decide) hleaves)
  | gas =>
      rw [matExpr_gas]
      exact SegAlignedP.nonpush Byte.gas (by decide) hleaves

/-- A `Loc` whose emitted leaves satisfy `P` materializes to `P`-aligned bytes. -/
theorem segAlignedP_matLoc_of {P : Operation → Prop} (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP P (cache t)) :
    ∀ loc, LocOpLeaves P loc → SegAlignedP P (matLoc cache loc)
  | .remat e, h => segAlignedP_matExpr_of cache hcache e h
  | .slot n, h => segAlignedP_slot_of h.1 h.2 n

/-- Extending a `P`-aligned cache by a location whose leaves satisfy `P` preserves alignment. -/
theorem matStep_aligned_of {P : Operation → Prop} (c : Tmp → List UInt8)
    (hc : ∀ t, SegAlignedP P (c t)) (p : Tmp × Loc) (hp : LocOpLeaves P p.2) :
    ∀ t, SegAlignedP P (matStep c p t) := by
  intro t
  simp only [matStep, Function.update_apply]
  by_cases h : t = p.1
  · rw [if_pos h]; exact segAlignedP_matLoc_of c hc p.2 hp
  · rw [if_neg h]; exact hc t

/-- Folding locations whose leaves satisfy `P` preserves pointwise cache alignment. -/
theorem matFold_aligned_of {P : Operation → Prop} (init : Tmp → List UInt8)
    (hinit : ∀ t, SegAlignedP P (init t)) (l : List (Tmp × Loc))
    (hl : ∀ p ∈ l, LocOpLeaves P p.2) :
    ∀ t, SegAlignedP P (matFold init l t) := by
  induction l generalizing init with
  | nil => simpa [matFold] using hinit
  | cons p rest ih =>
      rw [matFold_cons]
      exact ih (matStep init p)
        (matStep_aligned_of init hinit p (hl p (by simp)))
        (fun q hq => hl q (by simp [hq]))

/-- The materialization cache is `P`-aligned when its initial push and every registered location
satisfy the corresponding leaf facts. -/
theorem segAlignedP_matCache_of {P : Operation → Prop} (prog : Program)
    (hpush : P (Evm.parseInstr Byte.push32))
    (hl : ∀ p ∈ defEnv prog, LocOpLeaves P p.2) :
    ∀ t, SegAlignedP P (matCache prog t) := by
  unfold matCache
  exact matFold_aligned_of _ (fun _ => segAlignedP_emitImm_of hpush 0) (defEnv prog) hl

/-- A statement whose leaves satisfy `P` emits `P`-aligned bytes under a `P`-aligned cache. -/
theorem segAlignedP_emitStmt_of {P : Operation → Prop} (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP P (cache t)) (alloc : Alloc) (s : Stmt)
    (hleaves : StmtOpLeaves P s) : SegAlignedP P (emitStmt cache alloc s) := by
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
              exact ((segAlignedP_matExpr_of cache hcache e hleaves.1).append
                      (segAlignedP_emitImm_of hleaves.2.1 (UInt256.ofNat n))).append
                    (SegAlignedP.nonpush Byte.mstore (by decide) hleaves.2.2)
  | sstore key value =>
      rw [show emitStmt cache alloc (.sstore key value)
            = cache value ++ cache key ++ [Byte.sstore] from rfl]
      exact ((hcache value).append (hcache key)).append
            (SegAlignedP.nonpush Byte.sstore (by decide) hleaves)
  | call cs =>
      rw [show emitStmt cache alloc (.call cs)
            = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
              ++ cache cs.callee
              ++ cache cs.gasFwd
              ++ [Byte.call]
              ++ (match cs.resultTmp with
                  | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
                  | none   => [Byte.pop]) from rfl]
      have h := (segAlignedP_emitImm_of hleaves.1 (0 : Word)).append
        (segAlignedP_emitImm_of hleaves.1 0)
      have h := h.append (segAlignedP_emitImm_of hleaves.1 0)
      have h := h.append (segAlignedP_emitImm_of hleaves.1 0)
      have h := h.append (segAlignedP_emitImm_of hleaves.1 0)
      have h := h.append (hcache cs.callee)
      have h := h.append (hcache cs.gasFwd)
      have h := h.append (SegAlignedP.nonpush Byte.call (by decide) hleaves.2.1)
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) hleaves.2.2.2
      | some t =>
          exact (segAlignedP_emitImm_of hleaves.1 (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) hleaves.2.2.1)
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
      have h := h.append (SegAlignedP.nonpush Byte.create2 (by decide) hleaves.1)
      refine h.append ?_
      cases cs.resultTmp with
      | none => exact SegAlignedP.nonpush Byte.pop (by decide) hleaves.2.2.2
      | some t =>
          exact (segAlignedP_emitImm_of hleaves.2.1 (UInt256.ofNat (slotOf t))).append
            (SegAlignedP.nonpush Byte.mstore (by decide) hleaves.2.2.1)

/-- A terminator whose leaves satisfy `P` emits `P`-aligned bytes under a `P`-aligned cache. -/
theorem segAlignedP_emitTerm_of {P : Operation → Prop} (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP P (cache t)) (labelOff : Nat → Nat) (t : Term)
    (hleaves : TermOpLeaves P t) : SegAlignedP P (emitTerm cache labelOff t) := by
  cases t with
  | ret tt =>
      rw [show emitTerm cache labelOff (.ret tt)
            = cache tt ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32
                ++ emitImm 0 ++ [Byte.ret] from rfl]
      exact (((((hcache tt).append
              (segAlignedP_emitImm_of hleaves.1 0)).append
              (SegAlignedP.nonpush Byte.mstore (by decide) hleaves.2.1)).append
              (segAlignedP_emitImm_of hleaves.1 32)).append
              (segAlignedP_emitImm_of hleaves.1 0)).append
            (SegAlignedP.nonpush Byte.ret (by decide) hleaves.2.2)
  | stop =>
      rw [show emitTerm cache labelOff .stop = [Byte.stop] from rfl]
      exact SegAlignedP.nonpush Byte.stop (by decide) hleaves
  | jump dst =>
      rw [show emitTerm cache labelOff (.jump dst)
            = emitDest (labelOff dst.idx) ++ [Byte.jump] from rfl]
      exact (segAlignedP_emitDest_of hleaves.1 _).append
        (SegAlignedP.nonpush Byte.jump (by decide) hleaves.2)
  | branch cond thenL elseL =>
      rw [show emitTerm cache labelOff (.branch cond thenL elseL)
            = cache cond
              ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
              ++ emitDest (labelOff elseL.idx) ++ [Byte.jump] from rfl]
      exact ((((hcache cond).append
              (segAlignedP_emitDest_of hleaves.1 _)).append
              (SegAlignedP.nonpush Byte.jumpi (by decide) hleaves.2.1)).append
              (segAlignedP_emitDest_of hleaves.1 _)).append
            (SegAlignedP.nonpush Byte.jump (by decide) hleaves.2.2)

private theorem exprOpLeaves_lowering : ∀ e, ExprOpLeaves IsLoweringOp e := by
  intro e
  cases e <;> simp only [ExprOpLeaves] <;> decide

private theorem locOpLeaves_lowering : ∀ loc, LocOpLeaves IsLoweringOp loc := by
  intro loc
  cases loc with
  | remat e => exact exprOpLeaves_lowering e
  | slot _ => constructor <;> decide

private theorem stmtOpLeaves_lowering : ∀ s, StmtOpLeaves IsLoweringOp s := by
  intro s
  cases s with
  | assign _ e => cases e <;> simp only [StmtOpLeaves, ExprOpLeaves] <;> decide
  | sstore _ _ => simp only [StmtOpLeaves]; decide
  | call _ => simp only [StmtOpLeaves]; decide
  | create _ => simp only [StmtOpLeaves]; decide

private theorem termOpLeaves_lowering : ∀ t, TermOpLeaves IsLoweringOp t := by
  intro t
  cases t <;> simp only [TermOpLeaves] <;> decide

theorem segAlignedP_emitImm (w : Word) : SegAlignedP IsLoweringOp (emitImm w) :=
  segAlignedP_emitImm_of (by decide) w

theorem segAlignedP_emitDest (off : Nat) : SegAlignedP IsLoweringOp (emitDest off) :=
  segAlignedP_emitDest_of (by decide) off

theorem segAlignedP_slot (slot : Nat) :
    SegAlignedP IsLoweringOp (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) :=
  segAlignedP_slot_of (by decide) (by decide) slot

theorem segAlignedP_matExpr (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) :
    ∀ e, SegAlignedP IsLoweringOp (matExpr cache e) :=
  fun e => segAlignedP_matExpr_of cache hcache e (exprOpLeaves_lowering e)

theorem segAlignedP_matLoc (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) :
    ∀ loc, SegAlignedP IsLoweringOp (matLoc cache loc) :=
  fun loc => segAlignedP_matLoc_of cache hcache loc (locOpLeaves_lowering loc)

theorem matStep_aligned (c : Tmp → List UInt8)
    (hc : ∀ t, SegAlignedP IsLoweringOp (c t)) (p : Tmp × Loc) :
    ∀ t, SegAlignedP IsLoweringOp (matStep c p t) :=
  matStep_aligned_of c hc p (locOpLeaves_lowering p.2)

theorem matFold_aligned (init : Tmp → List UInt8)
    (hinit : ∀ t, SegAlignedP IsLoweringOp (init t)) (l : List (Tmp × Loc)) :
    ∀ t, SegAlignedP IsLoweringOp (matFold init l t) :=
  matFold_aligned_of init hinit l (fun p _ => locOpLeaves_lowering p.2)

theorem segAlignedP_matCache (prog : Program) :
    ∀ t, SegAlignedP IsLoweringOp (matCache prog t) :=
  segAlignedP_matCache_of prog (by decide) (fun p _ => locOpLeaves_lowering p.2)

theorem segAlignedP_emitStmt (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (alloc : Alloc) (s : Stmt) :
    SegAlignedP IsLoweringOp (emitStmt cache alloc s) :=
  segAlignedP_emitStmt_of cache hcache alloc s (stmtOpLeaves_lowering s)

theorem segAlignedP_emitTerm (cache : Tmp → List UInt8)
    (hcache : ∀ t, SegAlignedP IsLoweringOp (cache t)) (labelOff : Nat → Nat) (t : Term) :
    SegAlignedP IsLoweringOp (emitTerm cache labelOff t) :=
  segAlignedP_emitTerm_of cache hcache labelOff t (termOpLeaves_lowering t)

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
