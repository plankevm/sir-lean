import Sir.Spec.Machine
import BytecodeLayer.Hoare.MemAlgebra

export BytecodeLayer.Hoare.MemAlgebra
  (fromByteArray_toByteArray ofNat_toNat toByteArray_size toList_eq_data_toList)

namespace Sir

theorem MemoryState.readByte?_push_zeroed
    {memory : MemoryState} {allocation : Allocation} {address : Nat}
    (hvalid : memory.IsValidNewAlloc allocation)
    (hzero : allocation.bytes = ByteArray.mk (Array.replicate allocation.size 0))
    (hcontains : allocation.Contains address 1) :
    (memory.push allocation).readByte? address = some 0 := by
  have hold : memory.provisioned.findSome? (·.readByte? address) = none := by
    rw [Array.findSome?_eq_none_iff]
    intro previous hprevious
    have hdisjoint := hvalid.2 previous hprevious
    unfold Allocation.IsDisjoint at hdisjoint
    unfold Allocation.Contains at hcontains
    unfold Allocation.readByte?
    rw [if_neg]
    intro hrange
    omega
  have hnew : allocation.readByte? address = some 0 := by
    have hrange : allocation.start ≤ address ∧ address < allocation.endExclusive := by
      unfold Allocation.Contains at hcontains
      omega
    have hindex : address - allocation.start < allocation.bytes.size := by
      unfold Allocation.endExclusive Allocation.size at hrange
      omega
    unfold Allocation.readByte?
    rw [if_pos hrange]
    change allocation.bytes.data[address - allocation.start]? = some 0
    rw [hzero]
    change (Array.replicate allocation.size 0)[address - allocation.start]? = some 0
    rw [Array.getElem?_replicate, if_pos]
    exact hindex
  simp [MemoryState.readByte?, MemoryState.push, hold, hnew]

theorem MemoryState.readBytes_push_zeroed_word
    {memory : MemoryState} {allocation : Allocation} {offset : Word}
    (hvalid : memory.IsValidNewAlloc allocation)
    (hzero : allocation.bytes = ByteArray.mk (Array.replicate allocation.size 0))
    (hcontains : allocation.Contains offset.toNat 32)
    (assumed : Vector UInt8 32) :
    (memory.push allocation).readBytes offset ⟨assumed.toArray⟩ =
      ByteArray.mk (Array.replicate 32 0) := by
  unfold MemoryState.readBytes
  apply ByteArray.ext
  rw [List.data_toByteArray]
  apply Array.ext
  · rw [toList_eq_data_toList]
    simp
  · intro i hleft hright
    have hi : i < 32 := by simpa using hright
    have hbyte :
        (memory.push allocation).readByte? (offset.toNat + i) = some 0 := by
      apply MemoryState.readByte?_push_zeroed hvalid hzero
      unfold Allocation.Contains at hcontains ⊢
      omega
    simp [toList_eq_data_toList, hbyte]

theorem Machine.Operation.malloc_readBytes_zeroed_word
    {policy : Machine.MemoryPolicy} {globals : Globals} {size offset : Word}
    {allocation : Allocation}
    (hadmissible : Machine.Operation.Admissible policy .malloc globals #[size] allocation)
    (hcontains : allocation.Contains offset.toNat 32)
    (assumed : Vector UInt8 32) :
    (globals.memory.push allocation).readBytes offset ⟨assumed.toArray⟩ =
      ByteArray.mk (Array.replicate 32 0) := by
  obtain ⟨admissibleSize, hoperand, _, hvalid, hsize, hzero⟩ := hadmissible
  have : admissibleSize = size := by simpa using Option.some.inj hoperand.symm
  subst admissibleSize
  apply MemoryState.readBytes_push_zeroed_word hvalid
  · rw [hsize]
    exact hzero
  · exact hcontains

end Sir
