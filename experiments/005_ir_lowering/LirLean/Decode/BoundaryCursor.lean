import LirLean.Decode.DecodeAnchors
import LirLean.Decode.BoundaryReach

/-!
# LirLean — byte-layout cursor inversion for lowered programs

This module classifies an in-range byte offset of `flatBytes prog` by the source
layout region that contains it: a block `JUMPDEST`, a byte inside one top-level
statement emission, or a byte inside the block terminator emission.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## Generic list-region inversion -/

theorem flatMap_index_inv {α β : Type _} (xs : List α) (f : α → List β) {k : Nat}
    (hk : k < (xs.flatMap f).length) :
    ∃ i a j, xs[i]? = some a ∧ j < (f a).length
      ∧ k = ((xs.take i).flatMap f).length + j := by
  induction xs generalizing k with
  | nil =>
      simp at hk
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append] at hk
      by_cases hx : k < (f x).length
      · refine ⟨0, x, k, by simp, hx, ?_⟩
        simp
      · have htail : k - (f x).length < (xs.flatMap f).length := by omega
        obtain ⟨i, a, j, hget, hj, heq⟩ := ih htail
        refine ⟨i + 1, a, j, ?_, hj, ?_⟩
        · simpa using hget
        · simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega

theorem append_region_inv {α : Type _} (a b : List α) {k : Nat}
    (hk : k < (a ++ b).length) :
    k < a.length ∨ ∃ j, j < b.length ∧ k = a.length + j := by
  by_cases ha : k < a.length
  · exact Or.inl ha
  · refine Or.inr ⟨k - a.length, ?_, by omega⟩
    simp only [List.length_append] at hk
    omega

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

theorem flatBytes_cursor_cases {prog : Program} {b : Nat}
    (hin : b < (flatBytes prog).length) :
    LowerBoundaryCursor prog b := by
  unfold flatBytes at hin
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

theorem reachable_lowering_boundary_cases {prog : Program} {b : Nat}
    (_hreach : Evm.ReachesBoundary (lower prog) 0 b)
    (hin : b < (flatBytes prog).length) :
    LowerBoundaryCursor prog b :=
  flatBytes_cursor_cases hin

end Lir
