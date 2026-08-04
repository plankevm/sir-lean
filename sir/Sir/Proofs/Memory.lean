import Sir.Spec.Memory
import BytecodeLayer.Hoare.MemAlgebra

namespace Sir.MemoryState

private theorem readByte_fold_writeBytes (m : MemoryState) (base start address : Nat)
    (bytes : List UInt8) :
    ((bytes.zipIdx start).foldl
      (fun memory (byte, index) => memory.writeByte (base + index) byte) m).readByte address =
      if base + start ≤ address ∧ address < base + start + bytes.length
      then bytes.getD (address - (base + start)) 0
      else m.readByte address := by
  induction bytes generalizing start m with
  | nil => simp
  | cons byte bytes ih =>
      rw [List.zipIdx_cons, List.foldl_cons, ih]
      simp only [List.length_cons]
      by_cases heq : base + start = address
      · subst address
        simp [MemoryState.readByte, MemoryState.writeByte]
      · by_cases hle : base + start ≤ address
        · have hnext : base + (start + 1) ≤ address := by omega
          by_cases hrange : address < base + (start + 1) + bytes.length
          · rw [if_pos ⟨hnext, hrange⟩, if_pos ⟨hle, by omega⟩]
            rw [show address - (base + start) =
              (address - (base + (start + 1))) + 1 by omega]
            rfl
          · have hne : address ≠ base + start := Ne.symm heq
            rw [if_neg (by simp [hrange]), if_neg (by intro h; apply hrange; omega)]
            simp [MemoryState.readByte, MemoryState.writeByte, hne]
        · have hnext : ¬ base + (start + 1) ≤ address := by omega
          have hne : address ≠ base + start := Ne.symm heq
          simp [MemoryState.readByte, MemoryState.writeByte, hne, hle, hnext]

theorem readByte_writeByte_self (m : MemoryState) (address : Nat) (value : UInt8) :
    (m.writeByte address value).readByte address = value := by
  simp [MemoryState.readByte, MemoryState.writeByte]

theorem readByte_writeByte_of_ne (m : MemoryState) {address target : Nat} (value : UInt8)
    (h : address ≠ target) :
    (m.writeByte target value).readByte address = m.readByte address := by
  simp [MemoryState.readByte, MemoryState.writeByte, h]

theorem readByte_writeBytes (m : MemoryState) (offset : Word) (bytes : ByteArray)
    (address : Nat) :
    (m.writeBytes offset bytes).readByte address =
      if offset.toNat ≤ address ∧ address < offset.toNat + bytes.size
      then bytes.toList.getD (address - offset.toNat) 0
      else m.readByte address := by
  simpa [MemoryState.writeBytes,
    BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList] using
    readByte_fold_writeBytes m offset.toNat 0 address bytes.toList

theorem readBytes_writeBytes (m : MemoryState) (offset : Word) (bytes : ByteArray) :
    (m.writeBytes offset bytes).readBytes offset bytes.size = bytes := by
  unfold MemoryState.readBytes
  have hround : bytes.toList.toByteArray = bytes := by
    apply ByteArray.ext
    rw [List.data_toByteArray, BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList]
  conv_rhs => rw [← hround]
  apply congrArg List.toByteArray
  apply List.ext_getElem
  · simp [BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList]
  · intro i _ hbytes
    have hi : i < bytes.size := by
      simpa [BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList] using hbytes
    simp [readByte_writeBytes, hi,
      BytecodeLayer.Hoare.MemAlgebra.toList_eq_data_toList]
    rfl

theorem provisioned_writeBytes (m : MemoryState) (offset : Word) (bytes : ByteArray) :
    (m.writeBytes offset bytes).provisioned = m.provisioned := by
  unfold MemoryState.writeBytes
  generalize bytes.toList.zipIdx = writes
  induction writes generalizing m with
  | nil => rfl
  | cons write writes ih =>
      rw [List.foldl_cons, ih]
      rfl

theorem store_push (m : MemoryState) (a : Allocation) : (m.push a).store = m.store := by
  rfl

end Sir.MemoryState
