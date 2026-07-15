import LirLean.Decode.DecodeAnchors
import LirLean.Decode.BoundaryReach

/-!
# LirLean — byte-layout cursor inversion for lowered programs

The generic byte cursor and its decode theorem live in the assembler geometry.
This module retains the LIR adapter that classifies an in-range offset by its
source layout region: a block entry, a byte inside one top-level statement
emission, or a byte inside the block terminator emission.
-/

namespace Lir

open Evm
open BytecodeLayer.Asm

/-- Every lowered block is an aligned prefix followed by its final halting or jumping opcode. -/
theorem loweredBlock_terminal_decomp (prog : Program) (blk : Block) :
    ∃ pre last,
      Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk = pre ++ [last]
      ∧ SegAlignedP IsLoweringOp pre
      ∧ (Evm.parseInstr last = .STOP ∨ Evm.parseInstr last = .RETURN
        ∨ Evm.parseInstr last = .JUMP) := by
  let cache := matCache prog
  let alloc := defsOf prog
  let lo := offsetTable cache alloc prog.blocks
  let stmts := blk.stmts.flatMap (emitStmt cache alloc)
  have hstmts : SegAlignedP IsLoweringOp stmts := by
    unfold stmts
    apply segAlignedP_flatMap
    intro s _
    exact segAlignedP_emitStmt cache (by simpa [cache] using segAlignedP_matCache prog) alloc s
  have hcommon : SegAlignedP IsLoweringOp ([Byte.jumpdest] ++ stmts) :=
    (SegAlignedP.nonpush Byte.jumpdest (by decide) (by decide)).append hstmts
  cases ht : blk.term with
  | stop =>
      refine ⟨[Byte.jumpdest] ++ stmts, Byte.stop, ?_, hcommon, Or.inl rfl⟩
      simp [emitBlockBody, ht, emitTerm, stmts, cache, alloc]
  | jump dst =>
      let termPre := emitDest (lo dst.idx)
      have htermPre : SegAlignedP IsLoweringOp termPre := by
        simpa [termPre] using segAlignedP_emitDest (lo dst.idx)
      refine ⟨([Byte.jumpdest] ++ stmts) ++ termPre, Byte.jump, ?_,
        hcommon.append htermPre, Or.inr (Or.inr rfl)⟩
      simp [emitBlockBody, ht, emitTerm, stmts, termPre, cache, alloc, lo,
        List.append_assoc]
  | ret t =>
      let termPre := cache t ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32 ++ emitImm 0
      have htermPre : SegAlignedP IsLoweringOp termPre := by
        have hc : SegAlignedP IsLoweringOp (cache t) := by
          simpa [cache] using segAlignedP_matCache prog t
        exact ((((hc.append (segAlignedP_emitImm 0)).append
          (SegAlignedP.nonpush Byte.mstore (by decide) (by decide))).append
          (segAlignedP_emitImm 32)).append (segAlignedP_emitImm 0))
      refine ⟨([Byte.jumpdest] ++ stmts) ++ termPre, Byte.ret, ?_,
        hcommon.append htermPre, Or.inr (Or.inl rfl)⟩
      simp [emitBlockBody, ht, emitTerm, stmts, termPre, cache, alloc,
        List.append_assoc]
  | branch cond thenL elseL =>
      let termPre := cache cond ++ emitDest (lo thenL.idx) ++ [Byte.jumpi]
        ++ emitDest (lo elseL.idx)
      have htermPre : SegAlignedP IsLoweringOp termPre := by
        have hc : SegAlignedP IsLoweringOp (cache cond) := by
          simpa [cache] using segAlignedP_matCache prog cond
        exact (((hc.append (segAlignedP_emitDest (lo thenL.idx))).append
          (SegAlignedP.nonpush Byte.jumpi (by decide) (by decide))).append
          (segAlignedP_emitDest (lo elseL.idx)))
      refine ⟨([Byte.jumpdest] ++ stmts) ++ termPre, Byte.jump, ?_,
        hcommon.append htermPre, Or.inr (Or.inr rfl)⟩
      simp [emitBlockBody, ht, emitTerm, stmts, termPre, cache, alloc, lo,
        List.append_assoc]

/-! ## Source cursor classification -/

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

theorem lowered_block_region_inv (prog : Program) (blk : Block) {k base : Nat}
    (hk : k < (Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk).length) :
    k = 0
      ∨ (∃ pc s j, blk.stmts[pc]? = some s
          ∧ j < (emitStmt (matCache prog) (defsOf prog) s).length
          ∧ base + k = base + 1
              + ((blk.stmts.take pc).flatMap
                  (emitStmt (matCache prog) (defsOf prog))).length + j)
      ∨ (∃ j, j < (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk.term).length
          ∧ base + k = base + 1
              + (blk.stmts.flatMap (emitStmt (matCache prog) (defsOf prog))).length + j) := by
  cases k with
  | zero => exact Or.inl rfl
  | succ k' =>
      right
      simp only [List.length_cons] at hk
      have hkbody : k' < (emitBlockBody (matCache prog) (defsOf prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk).length := by omega
      unfold emitBlockBody at hkbody
      rcases append_region_inv
          (blk.stmts.flatMap (emitStmt (matCache prog) (defsOf prog)))
          (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk.term) hkbody with hstmt | hterm
      · left
        obtain ⟨pc, s, j, hs, hj, heq⟩ :=
          flatMap_index_inv blk.stmts (emitStmt (matCache prog) (defsOf prog)) hstmt
        refine ⟨pc, s, j, hs, hj, ?_⟩
        omega
      · right
        obtain ⟨j, hj, heq⟩ := hterm
        exact ⟨j, hj, by omega⟩

theorem lowerBytes_cursor_cases {prog : Program} {b : Nat}
    (hin : b < (lowerBytes prog).length) :
    LowerBoundaryCursor prog b := by
  rw [lowerBytes_eq_emit] at hin
  unfold emit at hin
  set cache := matCache prog with hcache
  set alloc := defsOf prog with halloc
  set lo := offsetTable cache alloc prog.blocks with hlo
  obtain ⟨i, blk, k, hb, hk, heq⟩ :=
    flatMap_index_inv prog.blocks.toList
      (fun blk => Byte.jumpdest :: emitBlockBody cache alloc lo blk) hin
  let L : Label := ⟨i⟩
  have hpre :
      ((prog.blocks.toList.take i).flatMap
        (fun blk => Byte.jumpdest :: emitBlockBody cache alloc lo blk)).length
        = offsetTable cache alloc prog.blocks i := by
    exact blockPrefix_length cache alloc lo prog.blocks i
  have hb' : prog.blocks.toList[L.idx]? = some blk := hb
  have hbase : b = offsetTable cache alloc prog.blocks i + k := by
    rw [heq, hpre]
  subst cache
  subst alloc
  subst lo
  have hbase' : b = offsetTable (matCache prog) (defsOf prog) prog.blocks i + k := by
    simpa using hbase
  rcases lowered_block_region_inv prog blk (k := k)
      (base := offsetTable (matCache prog) (defsOf prog) prog.blocks i) hk with hentry | hrest
  · apply LowerBoundaryCursor.blockEntry L blk hb'
    change b = offsetTable (matCache prog) (defsOf prog) prog.blocks i
    omega
  · rcases hrest with hstmt | hterm
    · obtain ⟨pc, s, j, hs, hj, hbj⟩ := hstmt
      apply LowerBoundaryCursor.stmt L blk pc j s hb' hs hj
      rw [pcOf_eq_anchor prog L blk pc hb']
      change b =
        (offsetTable (matCache prog) (defsOf prog) prog.blocks i + 1
          + (List.flatMap (emitStmt (matCache prog) (defsOf prog))
              (List.take pc blk.stmts)).length) + j
      omega
    · obtain ⟨j, hj, hbj⟩ := hterm
      apply LowerBoundaryCursor.term L blk j hb' hj
      rw [termOf_eq_anchor prog L blk hb']
      change b =
        (offsetTable (matCache prog) (defsOf prog) prog.blocks i + 1
          + (List.flatMap (emitStmt (matCache prog) (defsOf prog)) blk.stmts).length) + j
      omega

/-- A non-terminal instruction head classified by the source layout advances strictly inside the
lowered byte stream. -/
theorem nextInstrPos_lt_lowerBytes_of_cursor {prog : Program} {b : Nat} {byte : UInt8}
    (hcursor : LowerBoundaryCursor prog b)
    (hreach : Evm.ReachesBoundary (lower prog) 0 b)
    (hget : (lower prog).get? b = some byte)
    (hnstop : Evm.parseInstr byte ≠ .STOP)
    (hnreturn : Evm.parseInstr byte ≠ .RETURN)
    (hnjump : Evm.parseInstr byte ≠ .JUMP) :
    Evm.nextInstrPosNat b (Evm.parseInstr byte) < (lowerBytes prog).length := by
  have blockGeometry (L : Label) (blk : Block)
      (hb : prog.blocks.toList[L.idx]? = some blk)
      (hbase : offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx ≤ b)
      (hinside : b < offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx
        + (Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk).length) :
      Evm.nextInstrPosNat b (Evm.parseInstr byte) < (lowerBytes prog).length := by
    let base := offsetTable (matCache prog) (defsOf prog) prog.blocks L.idx
    let blockBytes := Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
      (offsetTable (matCache prog) (defsOf prog) prog.blocks) blk
    obtain ⟨pre, last, hdecomp, hpre, hlast⟩ := loweredBlock_terminal_decomp prog blk
    have hlocal : Evm.ReachesBoundary (lower prog) base b := by
      exact reachesBoundary_drop_to_blockEntry (prog := prog) (L := L) (blk := blk) hb
        hreach (by simpa [base] using hbase)
    have hmatch : ∀ j, j < (pre ++ [last]).length →
        (lower prog).get? (base + j) = (pre ++ [last])[j]? := by
      intro j hj
      rw [lower_get?_eq]
      have hsplit := lowerBytes_block_split prog L blk hb
      have hprelen := lowerBytes_block_offset prog L
      rw [hsplit]
      rw [show base = ((prog.blocks.toList.take L.idx).flatMap
          (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length from by
          simpa [base] using hprelen.symm]
      rw [List.append_assoc, List.getElem?_append_right (by omega),
        show ((prog.blocks.toList.take L.idx).flatMap
          (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length + j
          - ((prog.blocks.toList.take L.idx).flatMap
            (fun b => Byte.jumpdest :: emitBlockBody (matCache prog) (defsOf prog)
              (offsetTable (matCache prog) (defsOf prog) prog.blocks) b)).length = j from by omega]
      rw [List.getElem?_append_left]
      · simpa [blockBytes] using congrArg (fun xs => xs[j]?) hdecomp
      · simpa [blockBytes, hdecomp] using hj
    have hinBlock : b < base + (pre ++ [last]).length := by
      simpa [base, blockBytes, hdecomp] using hinside
    have hneLast : Evm.parseInstr byte ≠ Evm.parseInstr last := by
      rcases hlast with h | h | h
      · rwa [h]
      · rwa [h]
      · rwa [h]
    have hltBlock := nextInstrPos_lt_of_segAlignedP_terminal hpre base hmatch b byte hlocal
      hinBlock hget hneLast
    have hsplit := lowerBytes_block_split prog L blk hb
    have hprelen := lowerBytes_block_offset prog L
    have hblockEnd : base + (pre ++ [last]).length ≤ (lowerBytes prog).length := by
      rw [← hdecomp]
      rw [hsplit]
      simp only [List.length_append]
      rw [hprelen]
      simp only [base]
      omega
    exact lt_of_lt_of_le hltBlock hblockEnd
  cases hcursor with
  | blockEntry L blk hb heq =>
      apply blockGeometry L blk hb
      · rw [heq]
      · rw [heq]
        simp
  | stmt L blk pc k s hb hs hk heq =>
      apply blockGeometry L blk hb
      · rw [heq, pcOf_eq_anchor prog L blk pc hb]
        omega
      · have hsplit := flatMap_split blk.stmts pc s hs
          (emitStmt (matCache prog) (defsOf prog))
        have hlen : (blk.stmts.flatMap (emitStmt (matCache prog) (defsOf prog))).length
            = ((blk.stmts.take pc).flatMap
                (emitStmt (matCache prog) (defsOf prog))).length
              + (emitStmt (matCache prog) (defsOf prog) s).length
              + ((blk.stmts.drop (pc + 1)).flatMap
                (emitStmt (matCache prog) (defsOf prog))).length := by
          conv_lhs => rw [hsplit]
          rw [List.length_append, List.length_append]
        rw [heq, pcOf_eq_anchor prog L blk pc hb]
        simp only [List.length_cons, emitBlockBody, List.length_append]
        omega
  | term L blk k hb hk heq =>
      apply blockGeometry L blk hb
      · rw [heq, termOf_eq_anchor prog L blk hb]
        omega
      · rw [heq, termOf_eq_anchor prog L blk hb]
        simp only [List.length_cons, emitBlockBody, List.length_append]
        omega

theorem reachable_lowering_boundary_cases {prog : Program} {b : Nat}
    (_hreach : Evm.ReachesBoundary (lower prog) 0 b)
    (hin : b < (lowerBytes prog).length) :
    LowerBoundaryCursor prog b :=
  lowerBytes_cursor_cases hin

end Lir
