import BytecodeLayer.Asm
import BytecodeLayer.Exec.MatDecLower

/-!
# Geometry of structured assembly

This module owns the byte-list, instruction-alignment, boundary-walk, and block-placement
facts that depend only on `AsmProgram` and `assemble`.
-/

namespace BytecodeLayer.Asm

open Evm

theorem bget (l : List UInt8) (n : Nat) :
    ByteArray.get? ⟨l.toArray⟩ n = l[n]? := by
  unfold ByteArray.get?
  split
  · rename_i h; simp [ByteArray.get] at *
  · rename_i h; simp [ByteArray.size] at h; rw [List.getElem?_eq_none]; omega

theorem bextract (a : Array UInt8) (b e : Nat) :
    ((⟨a⟩ : ByteArray).extract b e).data = a.extract b e := by
  unfold ByteArray.extract ByteArray.copySlice
  show (Array.extract _ 0 0 ++ a.extract b (b + (e - b)) ++ Array.extract _ _ _) = _
  have h0 : (ByteArray.empty).data = #[] := rfl
  simp only [h0, Array.extract_empty_of_stop_le_start, Nat.le_refl]
  rw [show b + (e - b) = max b e from by omega]
  rcases Nat.le_total b e with h | h
  · rw [Nat.max_eq_right h]; simp
  · rw [Nat.max_eq_left h]
    rw [Array.extract_empty_of_stop_le_start h,
      Array.extract_empty_of_stop_le_start (Nat.le_refl b)]
    simp

theorem decode_nonpush_of_list (l : List UInt8) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : l[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n) = some (Evm.parseInstr byte, .none) := by
  unfold Evm.decode
  have hpc : (UInt32.ofNat n).toNat = n := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by simpa using hn)
  rw [hpc, bget, hb]
  show some (Evm.parseInstr byte,
      (if Evm.pushArgWidth (Evm.parseInstr byte) > 0 then _ else Option.none)) = _
  rw [hnp]; simp

theorem decode_push_of_list (l : List UInt8) (n : Nat) (byte : UInt8) (w : UInt8)
    (imm : UInt256) (hn : n < 2 ^ 32) (hb : l[n]? = some byte)
    (hp : Evm.pushArgWidth (Evm.parseInstr byte) = w) (hw : w > 0)
    (himm : Evm.uInt256OfByteArray
      ⟨(l.toArray).extract (n + 1) (n + 1 + w.toNat)⟩ = imm) :
    Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n) =
      some (Evm.parseInstr byte, some (imm, w)) := by
  unfold Evm.decode
  have hpc : (UInt32.ofNat n).toNat = n := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by simpa using hn)
  rw [hpc, bget, hb]
  have hext : (⟨l.toArray⟩ : ByteArray).extract (n + 1) (n + 1 + w.toNat) =
      ⟨(l.toArray).extract (n + 1) (n + 1 + w.toNat)⟩ :=
    ByteArray.ext (bextract _ _ _)
  show some (Evm.parseInstr byte,
      (if Evm.pushArgWidth (Evm.parseInstr byte) > 0 then
        some (Evm.uInt256OfByteArray ((⟨l.toArray⟩ : ByteArray).extract (n + 1)
                (n + 1 + (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)),
              Evm.pushArgWidth (Evm.parseInstr byte))
       else Option.none)) = _
  rw [hp, if_pos hw, hext, himm]

theorem reachesBoundary_le {c : ByteArray} {a n : Nat}
    (h : ReachesBoundary c a n) : a ≤ n := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | step _ _ ih => exact Nat.le_trans (Nat.le_of_lt (nextInstrPosNat_gt _ _)) ih

theorem ReachesBoundary.trans {c : ByteArray} {a m n : Nat}
    (h1 : ReachesBoundary c a m) (h2 : ReachesBoundary c m n) :
    ReachesBoundary c a n := by
  induction h1 with
  | refl _ => exact h2
  | step hget _ ih => exact .step hget (ih h2)

theorem ReachesBoundary.tail_of_le {c : ByteArray} {start a b : Nat}
    (ha : ReachesBoundary c start a) (hb : ReachesBoundary c start b)
    (hab : a ≤ b) : ReachesBoundary c a b := by
  induction ha generalizing b with
  | refl _ => exact hb
  | step hget rest ih =>
      cases hb with
      | refl _ =>
          have hnext := reachesBoundary_le rest
          exact absurd hab (by unfold nextInstrPosNat at hnext; omega)
      | step hget' rest' =>
          rw [hget] at hget'
          cases hget'
          exact ih rest' hab

theorem ReachesBoundary.eq_or_step {c : ByteArray} {start finish : Nat}
    (h : ReachesBoundary c start finish) :
    start = finish ∨ ∃ byte, c.get? start = some byte ∧
      ReachesBoundary c (nextInstrPosNat start (Evm.parseInstr byte)) finish := by
  cases h with
  | refl _ => exact Or.inl rfl
  | step hget rest => exact Or.inr ⟨_, hget, rest⟩

inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop where
  | nil : SegAlignedP P []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
      (hP : P (Evm.parseInstr byte))
      (hrest : SegAlignedP P rest) :
      SegAlignedP P (byte :: (imm ++ rest))

theorem SegAlignedP.mono {P Q : Operation → Prop} (h : ∀ op, P op → Q op) :
    ∀ {seg : List UInt8}, SegAlignedP P seg → SegAlignedP Q seg := by
  intro seg hseg
  induction hseg with
  | nil => exact .nil
  | cons byte imm rest himm hP _ ih => exact .cons byte imm rest himm (h _ hP) ih

theorem SegAlignedP.append {P : Operation → Prop} {a b : List UInt8}
    (ha : SegAlignedP P a) (hb : SegAlignedP P b) : SegAlignedP P (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | cons byte imm rest himm hP _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .cons byte imm (rest ++ b) himm hP ih

theorem SegAlignedP.nonpush {P : Operation → Prop} (byte : UInt8)
    (h : Evm.pushArgWidth (Evm.parseInstr byte) = 0) (hP : P (Evm.parseInstr byte)) :
    SegAlignedP P [byte] := by
  have hseg := SegAlignedP.cons (P := P) byte [] [] (by simp [h]) hP .nil
  simpa using hseg

theorem SegAlignedP.push {P : Operation → Prop} (byte : UInt8) (imm : List UInt8)
    (h : imm.length = (Evm.pushArgWidth (Evm.parseInstr byte)).toNat)
    (hP : P (Evm.parseInstr byte)) : SegAlignedP P (byte :: imm) := by
  have hseg := SegAlignedP.cons (P := P) byte imm [] h hP .nil
  simpa using hseg

theorem reaches_end_of_segAlignedP {P : Operation → Prop} (c : ByteArray)
    (seg : List UInt8) (hseg : SegAlignedP P seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ReachesBoundary c base (base + seg.length) := by
  induction hseg with
  | nil =>
    intro base _
    simpa using ReachesBoundary.refl (c := c) base
  | cons byte imm rest himm _ _ ih =>
    intro base hmatch
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp); simpa using this
    have hnext : nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
      unfold nextInstrPosNat; rw [himm]
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
    have hmatch' : ∀ j, j < rest.length →
        c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by
        rw [hseglen]; omega
      have h := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at h
      rw [h]
      rw [show 1 + imm.length + j = (imm.length + j) + 1 from by omega,
        List.getElem?_cons_succ, List.getElem?_append_right (by omega),
        show imm.length + j - imm.length = j from by omega]
    have hih := ih (base + 1 + imm.length) hmatch'
    refine .step (byte := byte) hhead ?_
    rw [hnext]
    rw [show base + (byte :: (imm ++ rest)).length =
        (base + 1 + imm.length) + rest.length from by rw [hseglen]; omega]
    exact hih

theorem reaches_P_of_segAlignedP {P : Operation → Prop} (c : ByteArray)
    (seg : List UInt8) (hseg : SegAlignedP P seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → n < base + seg.length →
        ∃ byte, c.get? n = some byte ∧ P (Evm.parseInstr byte) := by
  induction hseg with
  | nil =>
    intro base _ n hreach hlt
    simp only [List.length_nil, Nat.add_zero] at hlt
    exact absurd (reachesBoundary_le hreach) (by omega)
  | cons byte imm rest himm hP _ ih =>
    intro base hmatch n hreach hlt
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp); simpa using this
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
    have hmatch' : ∀ j, j < rest.length →
        c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by
        rw [hseglen]; omega
      have h := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at h
      rw [h]
      rw [show 1 + imm.length + j = (imm.length + j) + 1 from by omega,
        List.getElem?_cons_succ, List.getElem?_append_right (by omega),
        show imm.length + j - imm.length = j from by omega]
    cases hreach with
    | refl _ => exact ⟨byte, hhead, hP⟩
    | step hget rest' =>
      rw [hhead] at hget
      cases hget
      have hnext : nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
        unfold nextInstrPosNat; rw [himm]
      rw [hnext] at rest'
      have hlt' : n < (base + 1 + imm.length) + rest.length := by
        have : base + (byte :: (imm ++ rest)).length =
            (base + 1 + imm.length) + rest.length := by rw [hseglen]; omega
        omega
      exact ih (base + 1 + imm.length) hmatch' n rest' hlt'

theorem reachesBoundary_drop_segAlignedP {P : Operation → Prop} (c : ByteArray)
    (seg : List UInt8) (hseg : SegAlignedP P seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ∀ n, ReachesBoundary c base n → base + seg.length ≤ n →
        ReachesBoundary c (base + seg.length) n := by
  induction hseg with
  | nil =>
    intro base _ n hreach _
    simpa using hreach
  | cons byte imm rest himm _ _ ih =>
    intro base hmatch n hreach hle
    have hhead : c.get? base = some byte := by
      have := hmatch 0 (by simp); simpa using this
    have hseglen : (byte :: (imm ++ rest)).length = 1 + imm.length + rest.length := by
      simp [List.length_append]; omega
    have hmatch' : ∀ j, j < rest.length →
        c.get? ((base + 1 + imm.length) + j) = rest[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j < (byte :: (imm ++ rest)).length := by
        rw [hseglen]; omega
      have h := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j from by omega] at h
      rw [h]
      rw [show 1 + imm.length + j = (imm.length + j) + 1 from by omega,
        List.getElem?_cons_succ, List.getElem?_append_right (by omega),
        show imm.length + j - imm.length = j from by omega]
    cases hreach with
    | refl _ => rw [hseglen] at hle; omega
    | step hget restReach =>
      rw [hhead] at hget
      cases hget
      have hnext : nextInstrPosNat base (Evm.parseInstr byte) = base + 1 + imm.length := by
        unfold nextInstrPosNat; rw [himm]
      rw [hnext] at restReach
      have hle' : (base + 1 + imm.length) + rest.length ≤ n := by
        rw [hseglen] at hle
        omega
      have h := ih (base + 1 + imm.length) hmatch' n restReach hle'
      simpa [hseglen, Nat.add_assoc] using h

abbrev SegAligned : List UInt8 → Prop := SegAlignedP (fun _ => True)

theorem reaches_of_segAligned (c : ByteArray) (seg : List UInt8) (hseg : SegAligned seg) :
    ∀ base : Nat, (∀ j, j < seg.length → c.get? (base + j) = seg[j]?) →
      ReachesBoundary c base (base + seg.length) :=
  reaches_end_of_segAlignedP c seg hseg

theorem segAlignedP_flatMap {α : Type _} {P : Evm.Operation → Prop}
    {xs : List α} {f : α → List UInt8}
    (h : ∀ x ∈ xs, SegAlignedP P (f x)) : SegAlignedP P (xs.flatMap f) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    rw [List.flatMap_cons]
    exact (h x (by simp)).append (ih (by
      intro y hy
      exact h y (by simp [hy])))

theorem flatMap_split {α β : Type _} (xs : List α) (i : Nat) (a : α)
    (hi : xs[i]? = some a) (f : α → List β) :
    xs.flatMap f = (xs.take i).flatMap f ++ f a ++ (xs.drop (i + 1)).flatMap f := by
  have hlt : i < xs.length := by
    by_contra h
    have : xs[i]? = none := List.getElem?_eq_none (by omega)
    rw [this] at hi
    contradiction
  have hget : xs[i] = a := by
    rw [List.getElem?_eq_getElem hlt] at hi
    exact Option.some.inj hi
  conv_lhs => rw [← List.take_append_drop i xs]
  rw [List.flatMap_append]
  have hdrop : xs.drop i = a :: xs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hlt, hget]
  rw [hdrop, List.flatMap_cons]
  simp only [List.append_assoc]

theorem mid_index (pre mid suf : List UInt8) (k : Nat) (h : k < mid.length) :
    (pre ++ mid ++ suf)[pre.length + k]? = mid[k]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left h]

theorem flatMap_index_inv {α β : Type _} (xs : List α) (f : α → List β) {k : Nat}
    (hk : k < (xs.flatMap f).length) :
    ∃ i a j, xs[i]? = some a ∧ j < (f a).length ∧
      k = ((xs.take i).flatMap f).length + j := by
  induction xs generalizing k with
  | nil => simp at hk
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

theorem nextInstrPos_lt_of_segAlignedP_terminal {P : Operation → Prop}
    {c : ByteArray} {pre : List UInt8} {last : UInt8} (hpre : SegAlignedP P pre) :
    ∀ base : Nat,
      (∀ j, j < (pre ++ [last]).length → c.get? (base + j) = (pre ++ [last])[j]?) →
      ∀ n byte, ReachesBoundary c base n → n < base + (pre ++ [last]).length →
        c.get? n = some byte → Evm.parseInstr byte ≠ Evm.parseInstr last →
          Evm.nextInstrPosNat n (Evm.parseInstr byte) <
            base + (pre ++ [last]).length := by
  induction hpre with
  | nil =>
    intro base hmatch n byte hreach hin hget hne
    have hn : n = base := by
      have hle := reachesBoundary_le hreach
      simp only [List.nil_append, List.length_singleton] at hin
      omega
    subst n
    have hhead := hmatch 0 (by simp)
    simp at hhead
    rw [hhead] at hget
    cases hget
    exact absurd rfl hne
  | cons head imm rest himm _ _ ih =>
    intro base hmatch n byte hreach hin hget hne
    have hshape : (head :: (imm ++ rest)) ++ [last] =
        head :: (imm ++ (rest ++ [last])) := by simp [List.append_assoc]
    rw [hshape] at hmatch hin
    have hhead : c.get? base = some head := by
      have h := hmatch 0 (by simp); simpa using h
    have hmatch' : ∀ j, j < (rest ++ [last]).length →
        c.get? ((base + 1 + imm.length) + j) = (rest ++ [last])[j]? := by
      intro j hj
      have hj' : 1 + imm.length + j <
          (head :: (imm ++ (rest ++ [last]))).length := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hj ⊢
        omega
      have h := hmatch (1 + imm.length + j) hj'
      rw [show base + (1 + imm.length + j) = (base + 1 + imm.length) + j by omega] at h
      rw [show 1 + imm.length + j = (imm.length + j) + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_append_right (by omega),
        show imm.length + j - imm.length = j by omega] at h
      exact h
    cases hreach with
    | refl _ =>
      rw [hhead] at hget
      cases hget
      unfold Evm.nextInstrPosNat
      rw [← himm]
      simp only [List.length_cons, List.length_append] at hin ⊢
      omega
    | step hfirst hrestReach =>
      rw [hhead] at hfirst
      cases hfirst
      have hnext : Evm.nextInstrPosNat base (Evm.parseInstr head) =
          base + 1 + imm.length := by
        unfold Evm.nextInstrPosNat
        rw [himm]
      rw [hnext] at hrestReach
      have hin' : n < (base + 1 + imm.length) + (rest ++ [last]).length := by
        simp only [List.length_cons, List.length_append] at hin ⊢
        omega
      have hlt := ih (base + 1 + imm.length) hmatch' n byte hrestReach hin' hget hne
      simp only [List.length_cons, List.length_append] at hin hlt ⊢
      omega

theorem mem_validJumpDestsAuxNat_inv (c : ByteArray) (start : Nat)
    (acc : Array UInt32) {x : UInt32} (hx : x ∈ validJumpDestsAuxNat c start acc) :
    x ∈ acc ∨ ∃ j byte, ReachesBoundary c start j ∧ x = j.toUInt32 ∧ j < c.size ∧
      c.get? j = some byte ∧ Evm.parseInstr byte = .JUMPDEST := by
  rw [validJumpDestsAuxNat_eq] at hx
  cases hget : c.get? start with
  | none => rw [hget] at hx; exact Or.inl hx
  | some byte =>
    rw [hget] at hx
    simp only at hx
    have hstartlt : start < c.size :=
      lt_size_of_get?_isSome (by rw [hget]; exact Option.isSome_some)
    by_cases hj : Evm.parseInstr byte = .JUMPDEST
    · rw [if_pos hj] at hx
      have ih := mem_validJumpDestsAuxNat_inv c
        (nextInstrPosNat start (Evm.parseInstr byte)) (acc.push start.toUInt32) hx
      rcases ih with hmem | ⟨j, byte', hreach, hxj, hjlt, hjget, hjjd⟩
      · rcases Array.mem_push.mp hmem with hin | heq
        · exact Or.inl hin
        · exact Or.inr ⟨start, byte, ReachesBoundary.refl start, heq,
            hstartlt, hget, hj⟩
      · exact Or.inr ⟨j, byte', ReachesBoundary.step (byte := byte) hget hreach,
          hxj, hjlt, hjget, hjjd⟩
    · rw [if_neg hj] at hx
      have ih := mem_validJumpDestsAuxNat_inv c
        (nextInstrPosNat start (Evm.parseInstr byte)) acc hx
      rcases ih with hmem | ⟨j, byte', hreach, hxj, hjlt, hjget, hjjd⟩
      · exact Or.inl hmem
      · exact Or.inr ⟨j, byte', ReachesBoundary.step (byte := byte) hget hreach,
          hxj, hjlt, hjget, hjjd⟩
  termination_by c.size - start
  decreasing_by
    all_goals
      simp only [nextInstrPosNat]
      omega

theorem reachesBoundary_of_mem_validJumpDests (c : ByteArray) {x : UInt32}
    (hx : x ∈ validJumpDests c 0) :
    ∃ j, ReachesBoundary c 0 j ∧ x = j.toUInt32 ∧ j < c.size := by
  rw [validJumpDests] at hx
  simp only [show (0 : UInt32).toNat = 0 from rfl] at hx
  rcases mem_validJumpDestsAuxNat_inv c 0 #[] hx with
    hmem | ⟨j, _, hreach, hxj, hjlt, _, _⟩
  · exact absurd hmem (by simp)
  · exact ⟨j, hreach, hxj, hjlt⟩

theorem reachesBoundary_nextInstr {c : ByteArray} {start n : Nat} {byte : UInt8}
    (hreach : ReachesBoundary c start n) (hget : c.get? n = some byte) :
    ReachesBoundary c start (nextInstrPosNat n (Evm.parseInstr byte)) :=
  ReachesBoundary.trans hreach (ReachesBoundary.step hget (ReachesBoundary.refl _))

def IsAsmOp (op : Operation) : Prop :=
  op = .STOP ∨ op = .ADD ∨ op = .LT ∨ op = .POP ∨ op = .MLOAD ∨
  op = .MSTORE ∨ op = .SLOAD ∨ op = .SSTORE ∨ op = .JUMP ∨ op = .JUMPI ∨
  op = .GAS ∨ op = .JUMPDEST ∨ op = .PUSH4 ∨ op = .PUSH32 ∨ op = .CALL ∨
  op = .RETURN ∨ op = .System .CREATE2

instance (op : Operation) : Decidable (IsAsmOp op) := by
  unfold IsAsmOp
  infer_instance

theorem segAlignedP_encodeInstr (labelOffset : Nat → Nat) (instr : AsmInstr) :
    SegAlignedP IsAsmOp (encodeInstr labelOffset instr) := by
  cases instr with
  | push value =>
      refine SegAlignedP.push 0x7f (BytecodeLayer.Exec.wordBytesBE value) ?_ (by decide)
      rw [show Evm.parseInstr (0x7f : UInt8) = .Push .PUSH32 from rfl]
      simp [BytecodeLayer.Exec.wordBytesBE, Evm.pushArgWidth]
  | pushLabel label =>
      refine SegAlignedP.push 0x63 (BytecodeLayer.Exec.offsetBytesBE (labelOffset label))
        ?_ (by decide)
      rw [show Evm.parseInstr (0x63 : UInt8) = .Push .PUSH4 from rfl]
      simp [BytecodeLayer.Exec.offsetBytesBE, Evm.pushArgWidth]
  | op operation =>
      cases operation <;>
        exact SegAlignedP.nonpush _ (by decide) (by decide)

theorem segAlignedP_encodeInstrs (labelOffset : Nat → Nat)
    (instructions : List AsmInstr) :
    SegAlignedP IsAsmOp (encodeInstrs labelOffset instructions) := by
  unfold encodeInstrs
  exact segAlignedP_flatMap (fun instr _ => segAlignedP_encodeInstr labelOffset instr)

theorem segAlignedP_encodeBlock (labelOffset : Nat → Nat) (block : AsmBlock) :
    SegAlignedP IsAsmOp (encodeBlock labelOffset block) := by
  exact (SegAlignedP.nonpush 0x5b (by decide) (by decide)).append
    (segAlignedP_encodeInstrs labelOffset block.body)

theorem segAlignedP_bytes (program : AsmProgram) : SegAlignedP IsAsmOp (bytes program) := by
  unfold bytes
  exact segAlignedP_flatMap
    (fun block _ => segAlignedP_encodeBlock (blockOffset program) block)

theorem assemble_get?_eq (program : AsmProgram) (n : Nat) :
    (assemble program).get? n = (bytes program)[n]? := by
  rw [assemble]
  exact bget (bytes program) n

theorem blockOffset_succ (program : AsmProgram) (i : Nat) (block : AsmBlock)
    (hb : program.blocks.toList[i]? = some block) :
    blockOffset program (i + 1) = blockOffset program i + blockLength block := by
  have hlt : i < program.blocks.toList.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hb
    contradiction
  have hget : program.blocks.toList[i] = block := by
    rw [List.getElem?_eq_getElem hlt] at hb
    exact Option.some.inj hb
  unfold blockOffset
  rw [List.take_add_one, List.map_append, List.sum_append]
  congr 1
  rw [List.getElem?_eq_getElem hlt, hget]
  simp

theorem blockPrefix_length (program : AsmProgram) (i : Nat) :
    ((program.blocks.toList.take i).flatMap (encodeBlock (blockOffset program))).length =
      blockOffset program i := by
  unfold blockOffset
  rw [List.length_flatMap]
  simp only [encodeBlock_length]

theorem bytes_block_split (program : AsmProgram) (i : Nat) (block : AsmBlock)
    (hb : program.blocks.toList[i]? = some block) :
    bytes program =
      (program.blocks.toList.take i).flatMap (encodeBlock (blockOffset program)) ++
      encodeBlock (blockOffset program) block ++
      (program.blocks.toList.drop (i + 1)).flatMap (encodeBlock (blockOffset program)) := by
  unfold bytes
  exact flatMap_split program.blocks.toList i block hb _

theorem assemble_match_block (program : AsmProgram) (i : Nat) (block : AsmBlock)
    (hb : program.blocks.toList[i]? = some block) :
    ∀ j, j < (encodeBlock (blockOffset program) block).length →
      (assemble program).get? (blockOffset program i + j) =
        (encodeBlock (blockOffset program) block)[j]? := by
  intro j hj
  rw [assemble_get?_eq, bytes_block_split program i block hb]
  rw [← blockPrefix_length program i]
  exact mid_index _ _ _ j hj

theorem reaches_blockOffset (program : AsmProgram) :
    ∀ i, i ≤ program.blocks.size →
      ReachesBoundary (assemble program) 0 (blockOffset program i) := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa [blockOffset] using ReachesBoundary.refl (c := assemble program) 0
  | succ n ih =>
    intro hn
    have hnlt : n < program.blocks.size := by omega
    have hblist : n < program.blocks.toList.length := by simpa using hnlt
    set block := program.blocks.toList[n]
    have hb : program.blocks.toList[n]? = some block := by
      rw [List.getElem?_eq_getElem hblist]
    have hreach := ih (by omega)
    have hseg : SegAligned (encodeBlock (blockOffset program) block) :=
      (segAlignedP_encodeBlock (blockOffset program) block).mono (fun _ _ => trivial)
    have hwalk := reaches_of_segAligned (assemble program)
      (encodeBlock (blockOffset program) block) hseg (blockOffset program n)
      (assemble_match_block program n block hb)
    rw [blockOffset_succ program n block hb]
    rw [← encodeBlock_length (blockOffset program) block]
    exact ReachesBoundary.trans hreach hwalk

theorem assemble_byte_at_blockOffset (program : AsmProgram) (i : Nat) (block : AsmBlock)
    (hb : program.blocks.toList[i]? = some block) :
    (assemble program).get? (blockOffset program i) = some 0x5b := by
  have h := assemble_match_block program i block hb 0 (by simp [encodeBlock])
  simpa [encodeBlock] using h

theorem blockOffset_validJump (program : AsmProgram) (i : Nat)
    (hi : i < program.blocks.size) :
    UInt32.ofNat (blockOffset program i) ∈ validJumpDests (assemble program) 0 := by
  have hblist : i < program.blocks.toList.length := by simpa using hi
  set block := program.blocks.toList[i]
  have hb : program.blocks.toList[i]? = some block := by
    rw [List.getElem?_eq_getElem hblist]
  have hreach := reaches_blockOffset program i (by omega)
  have hget := assemble_byte_at_blockOffset program i block hb
  have hmem := mem_validJumpDests_of_reachable_jumpdest (assemble program)
    hreach hget (by decide)
  simpa [UInt32.ofNat] using hmem

theorem decode_at_blockOffset_jumpdest (program : AsmProgram) (i : Nat) (block : AsmBlock)
    (hb : program.blocks.toList[i]? = some block)
    (hbound : blockOffset program i < 2 ^ 32) :
    Evm.decode (assemble program) (UInt32.ofNat (blockOffset program i)) =
      some (.Smsf .JUMPDEST, .none) := by
  rw [assemble]
  apply decode_nonpush_of_list (bytes program) (blockOffset program i) 0x5b hbound
  · rw [← assemble_get?_eq]
    exact assemble_byte_at_blockOffset program i block hb
  · decide

/-- Byte offset of instruction `index` in block `label`, after its leading `JUMPDEST`. -/
def cursorPc (program : AsmProgram) (label index : Nat) : Nat :=
  blockOffset program label + 1 +
    match program.blocks.toList[label]? with
    | some block => ((block.body.take index).map AsmInstr.byteLength).sum
    | none => 0

theorem cursorPc_succ (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (instr : AsmInstr)
    (hb : program.blocks.toList[label]? = some block)
    (hi : block.body[index]? = some instr) :
    cursorPc program label (index + 1) =
      cursorPc program label index + instr.byteLength := by
  have hlt : index < block.body.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    contradiction
  unfold cursorPc
  simp only [hb]
  rw [List.take_add_one, List.map_append, List.sum_append]
  simp [hi]
  omega

def decodedInstr (program : AsmProgram) : AsmInstr →
    Operation × Option (UInt256 × UInt8)
  | .push value => (.PUSH32, some (value, 32))
  | .pushLabel label =>
      (.PUSH4, some (Evm.uInt256OfByteArray
        ⟨(BytecodeLayer.Exec.offsetBytesBE (blockOffset program label)).toArray⟩, 4))
  | .op operation => (Evm.parseInstr operation.byte, .none)

theorem encodeInstrs_prefix_length (labelOffset : Nat → Nat)
    (instructions : List AsmInstr) (index : Nat) :
    (encodeInstrs labelOffset (instructions.take index)).length =
      ((instructions.take index).map AsmInstr.byteLength).sum := by
  simp

theorem bytes_at_cursor (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (instr : AsmInstr)
    (hb : program.blocks.toList[label]? = some block)
    (hi : block.body[index]? = some instr) (k : Nat)
    (hk : k < (encodeInstr (blockOffset program) instr).length) :
    (bytes program)[cursorPc program label index + k]? =
      (encodeInstr (blockOffset program) instr)[k]? := by
  have hisplit := flatMap_split block.body index instr hi (encodeInstr (blockOffset program))
  have hiprefix :
      (encodeInstrs (blockOffset program) (block.body.take index)).length =
        ((block.body.take index).map AsmInstr.byteLength).sum :=
    encodeInstrs_prefix_length _ _ _
  have hilen :
      ((block.body.take index).flatMap (encodeInstr (blockOffset program))).length =
        ((block.body.take index).map AsmInstr.byteLength).sum := by
    simpa [encodeInstrs] using hiprefix
  have hbody : encodeInstrs (blockOffset program) block.body =
      encodeInstrs (blockOffset program) (block.body.take index) ++
      encodeInstr (blockOffset program) instr ++
      encodeInstrs (blockOffset program) (block.body.drop (index + 1)) := by
    simpa [encodeInstrs] using hisplit
  have hblockAt := mid_index
    ((program.blocks.toList.take label).flatMap (encodeBlock (blockOffset program)))
    (encodeBlock (blockOffset program) block)
    ((program.blocks.toList.drop (label + 1)).flatMap (encodeBlock (blockOffset program)))
    (1 + ((block.body.take index).map AsmInstr.byteLength).sum + k)
    (by
      simp only [encodeBlock, List.length_cons, encodeInstrs_length]
      have hindex : index < block.body.length := by
        by_contra h
        rw [List.getElem?_eq_none (by omega)] at hi
        contradiction
      have hsumTake :
          ((block.body.take index).map AsmInstr.byteLength).sum + instr.byteLength ≤
            (block.body.map AsmInstr.byteLength).sum := by
        have hdrop : block.body.drop index = instr :: block.body.drop (index + 1) := by
          rw [List.drop_eq_getElem_cons hindex]
          have hget : block.body[index] = instr := by
            rw [List.getElem?_eq_getElem hindex] at hi
            exact Option.some.inj hi
          rw [hget]
        have hsum : (block.body.map AsmInstr.byteLength).sum =
            ((block.body.take index).map AsmInstr.byteLength).sum +
              instr.byteLength +
              ((block.body.drop (index + 1)).map AsmInstr.byteLength).sum := by
          conv_lhs => rw [← List.take_append_drop index block.body]
          rw [hdrop]
          simp [List.map_append, List.sum_append, Nat.add_assoc]
        omega
      rw [encodeInstr_length] at hk
      omega)
  rw [← bytes_block_split program label block hb] at hblockAt
  rw [blockPrefix_length program label] at hblockAt
  have hlocal :
      (encodeBlock (blockOffset program) block)[
          1 + ((block.body.take index).map AsmInstr.byteLength).sum + k]? =
        (encodeInstr (blockOffset program) instr)[k]? := by
    rw [encodeBlock, hbody]
    rw [show 1 + ((block.body.take index).map AsmInstr.byteLength).sum + k =
      (((block.body.take index).map AsmInstr.byteLength).sum + k) + 1 by omega]
    rw [List.getElem?_cons_succ, List.append_assoc]
    rw [List.getElem?_append_right (by
      rw [encodeInstrs_length]
      omega)]
    rw [encodeInstrs_length]
    simp only [Nat.add_sub_cancel_left]
    exact List.getElem?_append_left hk
  rw [cursorPc, hb]
  rw [show blockOffset program label + 1 +
      ((block.body.take index).map AsmInstr.byteLength).sum + k =
      blockOffset program label +
        (1 + ((block.body.take index).map AsmInstr.byteLength).sum + k) by omega]
  exact hblockAt.trans hlocal

theorem assemble_at_cursor (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (instr : AsmInstr)
    (hb : program.blocks.toList[label]? = some block)
    (hi : block.body[index]? = some instr) (k : Nat)
    (hk : k < (encodeInstr (blockOffset program) instr).length) :
    (assemble program).get? (cursorPc program label index + k) =
      (encodeInstr (blockOffset program) instr)[k]? := by
  rw [assemble_get?_eq]
  exact bytes_at_cursor program label index block instr hb hi k hk

theorem reaches_cursorPc (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (hb : program.blocks.toList[label]? = some block)
    (hi : index ≤ block.body.length) :
    ReachesBoundary (assemble program) 0 (cursorPc program label index) := by
  induction index with
  | zero =>
      have hentry := reaches_blockOffset program label (by
        have hlt : label < program.blocks.toList.length := by
          by_contra h
          rw [List.getElem?_eq_none (by omega)] at hb
          contradiction
        simpa using Nat.le_of_lt hlt)
      have hget := assemble_byte_at_blockOffset program label block hb
      have hnext := reachesBoundary_nextInstr hentry hget
      simpa [cursorPc, hb, nextInstrPosNat, Evm.pushArgWidth] using hnext
  | succ n ih =>
      have hnlt : n < block.body.length := by omega
      let instr := block.body[n]
      have hinstr : block.body[n]? = some instr := by
        rw [List.getElem?_eq_getElem hnlt]
      have hprev := ih (by omega)
      have hhead := assemble_at_cursor program label n block instr hb hinstr 0 (by
        cases instr <;> simp [encodeInstr])
      cases hins : instr with
      | push value =>
          have hget : (assemble program).get? (cursorPc program label n) = some 0x7f := by
            simpa [hins, encodeInstr] using hhead
          have hnext := reachesBoundary_nextInstr hprev hget
          rw [cursorPc_succ program label n block (.push value) hb (by simpa [hins] using hinstr)]
          simpa [AsmInstr.byteLength, nextInstrPosNat, Evm.pushArgWidth] using hnext
      | pushLabel target =>
          have hget : (assemble program).get? (cursorPc program label n) = some 0x63 := by
            simpa [hins, encodeInstr] using hhead
          have hnext := reachesBoundary_nextInstr hprev hget
          rw [cursorPc_succ program label n block (.pushLabel target) hb
            (by simpa [hins] using hinstr)]
          simpa [AsmInstr.byteLength, nextInstrPosNat, Evm.pushArgWidth] using hnext
      | op operation =>
          have hget : (assemble program).get? (cursorPc program label n) =
              some operation.byte := by
            simpa [hins, encodeInstr] using hhead
          have hnext := reachesBoundary_nextInstr hprev hget
          rw [cursorPc_succ program label n block (.op operation) hb
            (by simpa [hins] using hinstr)]
          cases operation <;>
            simpa [AsmInstr.byteLength, nextInstrPosNat, Evm.pushArgWidth, Op.byte] using hnext

theorem reachable_instr_offset_eq_zero (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (instr : AsmInstr) (offset : Nat)
    (hb : program.blocks.toList[label]? = some block)
    (hi : block.body[index]? = some instr)
    (hoffset : offset < (encodeInstr (blockOffset program) instr).length)
    (hreach : ReachesBoundary (assemble program) 0
      (cursorPc program label index + offset)) :
    offset = 0 := by
  have hindex : index ≤ block.body.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    contradiction
  have hcursor := reaches_cursorPc program label index block hb hindex
  let cursor := cursorPc program label index
  have htail : ReachesBoundary (assemble program) cursor (cursor + offset) :=
    ReachesBoundary.tail_of_le hcursor hreach (by simp [cursor])
  rcases ReachesBoundary.eq_or_step htail with heq | ⟨_, hget, rest⟩
  · omega
  ·
      change (assemble program).get? (cursorPc program label index) = _ at hget
      have hhead := assemble_at_cursor program label index block instr hb hi 0 (by
        cases instr <;> simp [encodeInstr])
      have hle := reachesBoundary_le rest
      cases hins : instr with
      | push value =>
          have hbyte : (assemble program).get? (cursorPc program label index) = some 0x7f := by
            simpa [hins, encodeInstr] using hhead
          rw [hbyte] at hget
          cases hget
          have hw : Evm.pushArgWidth (Evm.parseInstr (0x7f : UInt8)) = 32 := rfl
          unfold nextInstrPosNat at hle
          rw [hw] at hle
          have h32 : (32 : UInt8).toNat = 32 := rfl
          rw [h32] at hle
          simp [hins, encodeInstr, BytecodeLayer.Exec.wordBytesBE] at hoffset
          omega
      | pushLabel target =>
          have hbyte : (assemble program).get? (cursorPc program label index) = some 0x63 := by
            simpa [hins, encodeInstr] using hhead
          rw [hbyte] at hget
          cases hget
          have hw : Evm.pushArgWidth (Evm.parseInstr (0x63 : UInt8)) = 4 := rfl
          unfold nextInstrPosNat at hle
          rw [hw] at hle
          have h4 : (4 : UInt8).toNat = 4 := rfl
          rw [h4] at hle
          simp [hins, encodeInstr, BytecodeLayer.Exec.offsetBytesBE] at hoffset
          omega
      | op operation =>
          have hbyte : (assemble program).get? (cursorPc program label index) =
              some operation.byte := by
            simpa [hins, encodeInstr] using hhead
          rw [hbyte] at hget
          cases hget
          cases operation <;>
            simp [nextInstrPosNat, Evm.pushArgWidth, Op.byte, hins, encodeInstr] at hle hoffset <;>
            omega

theorem decode_at_cursor (program : AsmProgram) (label index : Nat)
    (block : AsmBlock) (instr : AsmInstr)
    (hb : program.blocks.toList[label]? = some block)
    (hi : block.body[index]? = some instr)
    (hbound : cursorPc program label index < 2 ^ 32) :
    Evm.decode (assemble program) (UInt32.ofNat (cursorPc program label index)) =
      some (decodedInstr program instr) := by
  rw [assemble]
  cases instr with
  | op operation =>
      apply decode_nonpush_of_list (bytes program) (cursorPc program label index)
        operation.byte hbound
      · exact bytes_at_cursor program label index block (.op operation) hb hi 0 (by simp [encodeInstr])
      · cases operation <;> decide
  | push value =>
      apply decode_push_of_list (bytes program) (cursorPc program label index)
        0x7f 32 value hbound
      · exact bytes_at_cursor program label index block (.push value) hb hi 0
          (by simp [encodeInstr])
      · rfl
      · decide
      · have hwindow := BytecodeLayer.Exec.extract_toList_eq (bytes program)
          (cursorPc program label index + 1) 32
          (BytecodeLayer.Exec.wordBytesBE value)
          (by simp [BytecodeLayer.Exec.wordBytesBE])
          (by
            intro j hj
            have h := bytes_at_cursor program label index block (.push value) hb hi (1 + j)
              (by simp [encodeInstr, BytecodeLayer.Exec.wordBytesBE] at hj ⊢; omega)
            rw [show cursorPc program label index + 1 + j =
              cursorPc program label index + (1 + j) by omega]
            rw [show 1 + j = j + 1 by omega] at h ⊢
            simp only [encodeInstr] at h
            rw [List.getElem?_cons_succ] at h
            exact h)
        have harr : (bytes program).toArray.extract
            (cursorPc program label index + 1)
            (cursorPc program label index + 1 + 32) =
            (BytecodeLayer.Exec.wordBytesBE value).toArray := by
          apply Array.toList_inj.mp
          simpa using hwindow
        change Evm.uInt256OfByteArray
          ⟨(bytes program).toArray.extract (cursorPc program label index + 1)
            (cursorPc program label index + 1 + 32)⟩ = value
        rw [harr]
        exact BytecodeLayer.Exec.uInt256_wordBytesBE value
  | pushLabel target =>
      let immediate := BytecodeLayer.Exec.offsetBytesBE (blockOffset program target)
      apply decode_push_of_list (bytes program) (cursorPc program label index)
        0x63 4 (Evm.uInt256OfByteArray ⟨immediate.toArray⟩) hbound
      · exact bytes_at_cursor program label index block (.pushLabel target) hb hi 0
          (by simp [encodeInstr])
      · rfl
      · decide
      · have hwindow := BytecodeLayer.Exec.extract_toList_eq (bytes program)
          (cursorPc program label index + 1) 4 immediate
          (by simp [immediate, BytecodeLayer.Exec.offsetBytesBE])
          (by
            intro j hj
            have h := bytes_at_cursor program label index block (.pushLabel target) hb hi (1 + j)
              (by simp [encodeInstr, BytecodeLayer.Exec.offsetBytesBE] at hj ⊢; omega)
            rw [show cursorPc program label index + 1 + j =
              cursorPc program label index + (1 + j) by omega]
            rw [show 1 + j = j + 1 by omega] at h ⊢
            simp only [encodeInstr] at h
            rw [List.getElem?_cons_succ] at h
            exact h)
        have harr : (bytes program).toArray.extract
            (cursorPc program label index + 1)
            (cursorPc program label index + 1 + 4) = immediate.toArray := by
          apply Array.toList_inj.mp
          simpa using hwindow
        change Evm.uInt256OfByteArray
          ⟨(bytes program).toArray.extract (cursorPc program label index + 1)
            (cursorPc program label index + 1 + 4)⟩ =
          Evm.uInt256OfByteArray ⟨immediate.toArray⟩
        rw [harr]

/-- Frame-level block entry, including the code and valid-jump geometry. -/
def AtEntry (program : AsmProgram) (fr : Frame) (label : Nat)
    (stack : List UInt256) : Prop :=
  (∃ block, program.blocks.toList[label]? = some block) ∧
  fr.exec.executionEnv.code = assemble program ∧
  fr.exec.pc = UInt32.ofNat (blockOffset program label) ∧
  fr.validJumps = validJumpDests (assemble program) 0 ∧
  fr.exec.stack = stack

/-- Frame-level instruction cursor, including the code and valid-jump geometry. -/
def AtCursor (program : AsmProgram) (fr : Frame) (label index : Nat)
    (stack : List UInt256) : Prop :=
  (∃ block instr, program.blocks.toList[label]? = some block ∧
    block.body[index]? = some instr) ∧
  fr.exec.executionEnv.code = assemble program ∧
  fr.exec.pc = UInt32.ofNat (cursorPc program label index) ∧
  fr.validJumps = validJumpDests (assemble program) 0 ∧
  fr.exec.stack = stack

/-- Classification of a byte position in structured assembly. -/
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

theorem bytes_cursor_cases {program : AsmProgram} {position : Nat}
    (hin : position < (bytes program).length) : ByteCursor program position := by
  unfold bytes at hin
  obtain ⟨label, block, localOffset, hb, hlocal, hposition⟩ :=
    flatMap_index_inv program.blocks.toList (encodeBlock (blockOffset program)) hin
  have hprefix := blockPrefix_length program label
  cases localOffset with
  | zero =>
      apply ByteCursor.blockEntry label block hb
      omega
  | succ inner =>
      simp only [encodeBlock, List.length_cons] at hlocal
      have hbody : inner < (encodeInstrs (blockOffset program) block.body).length := by
        omega
      unfold encodeInstrs at hbody
      obtain ⟨index, instruction, offset, hi, hoffset, hlocalEq⟩ :=
        flatMap_index_inv block.body (encodeInstr (blockOffset program)) hbody
      apply ByteCursor.instr label block index instruction offset hb hi hoffset
      rw [cursorPc, hb]
      change position = blockOffset program label + 1 +
        ((block.body.take index).map AsmInstr.byteLength).sum + offset
      have hiprefix := encodeInstrs_prefix_length (blockOffset program) block.body index
      unfold encodeInstrs at hiprefix
      omega

theorem reachable_boundary_asmOp (program : AsmProgram) (n : Nat)
    (hreach : ReachesBoundary (assemble program) 0 n)
    (hn : n < (bytes program).length) :
    ∃ byte, (assemble program).get? n = some byte ∧ IsAsmOp (Evm.parseInstr byte) := by
  apply reaches_P_of_segAlignedP (assemble program) (bytes program)
    (segAlignedP_bytes program) 0
  · intro j _
    simpa using assemble_get?_eq program j
  · exact hreach
  · simpa using hn

/-- The set of byte offsets at which the assembler places block-entry `JUMPDEST`s. -/
def entryPcSet (program : AsmProgram) : Set UInt32 :=
  { pc | ∃ label, label < program.blocks.size ∧
      pc = UInt32.ofNat (blockOffset program label) }

/-- The assembler's valid jump destinations are exactly its block-entry offsets. -/
theorem mem_validJumpDests_assemble_iff (program : AsmProgram) (x : UInt32) :
    x ∈ validJumpDests (assemble program) 0 ↔ x ∈ entryPcSet program := by
  constructor
  · intro hx
    rw [validJumpDests] at hx
    rcases mem_validJumpDestsAuxNat_inv (assemble program) 0 #[] hx with
      hnil | ⟨position, byte, hreach, hxpos, hlt, hget, hjumpdest⟩
    · exact absurd hnil (by simp)
    · have hin : position < (bytes program).length := by
        simpa [assemble, ByteArray.size] using hlt
      cases bytes_cursor_cases hin with
      | blockEntry label block hb heq =>
          refine ⟨label, ?_, ?_⟩
          · have hlabel : label < program.blocks.toList.length := by
              by_contra h
              rw [List.getElem?_eq_none (by omega)] at hb
              contradiction
            simpa using hlabel
          · rw [hxpos, heq]
      | instr label block index instr offset hb hi hoffset heq =>
          have hoffset0 := reachable_instr_offset_eq_zero program label index block instr offset
            hb hi hoffset (by rwa [← heq])
          subst offset
          rw [heq, Nat.add_zero] at hget
          have hhead := assemble_at_cursor program label index block instr hb hi 0 (by
            cases instr <;> simp [encodeInstr])
          simp only [Nat.add_zero] at hhead
          cases hins : instr with
          | push value =>
              have hbyte : (assemble program).get? (cursorPc program label index) = some 0x7f := by
                simpa [hins, encodeInstr] using hhead
              rw [hbyte] at hget
              cases hget
              contradiction
          | pushLabel target =>
              have hbyte : (assemble program).get? (cursorPc program label index) = some 0x63 := by
                simpa [hins, encodeInstr] using hhead
              rw [hbyte] at hget
              cases hget
              contradiction
          | op operation =>
              have hbyte : (assemble program).get? (cursorPc program label index) =
                  some operation.byte := by
                simpa [hins, encodeInstr] using hhead
              rw [hbyte] at hget
              cases hget
              cases operation <;> contradiction
  · rintro ⟨label, hlabel, rfl⟩
    exact blockOffset_validJump program label hlabel

end BytecodeLayer.Asm
