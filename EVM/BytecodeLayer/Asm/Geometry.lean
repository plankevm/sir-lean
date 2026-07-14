import BytecodeLayer.Asm

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

end BytecodeLayer.Asm
