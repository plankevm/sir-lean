import Sir.Machine.Spec

namespace Sir

namespace MemoryState

private theorem le_foldl_max (l : List Allocation) (init : Nat) :
    init ≤ l.foldl (fun watermark allocation => max watermark allocation.endExclusive) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl init
  | cons head tail ih =>
      exact Nat.le_trans (Nat.le_max_left init head.endExclusive) (ih _)

private theorem mem_le_foldl_max (l : List Allocation) (init : Nat) :
    ∀ a ∈ l,
      a.endExclusive ≤
        l.foldl (fun watermark allocation => max watermark allocation.endExclusive) init := by
  induction l generalizing init with
  | nil => intro a ha; cases ha
  | cons head tail ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Nat.le_trans (Nat.le_max_right init a.endExclusive) (le_foldl_max tail _)
      · exact ih _ a ha

theorem endExclusive_le_watermark (m : MemoryState) {a : Allocation}
    (ha : a ∈ m.provisioned) : a.endExclusive ≤ m.watermark := by
  rw [watermark, ← Array.foldl_toList]
  exact mem_le_foldl_max m.provisioned.toList 0 a (Array.mem_def.mp ha)

theorem bumpAlloc_size (m : MemoryState) (size : Nat) :
    (m.bumpAlloc size).size = size := by
  simp [bumpAlloc, Allocation.size, ByteArray.size]

theorem bumpAlloc_bytes (m : MemoryState) (size : Nat) :
    (m.bumpAlloc size).bytes = ByteArray.mk (Array.replicate size 0) := rfl

theorem isValidNewAlloc_bumpAlloc (m : MemoryState) (size : Nat)
    (hspace : m.watermark + size ≤ Evm.UInt256.size) :
    m.IsValidNewAlloc (m.bumpAlloc size) := by
  have hbound : Evm.UInt256.size = 2 ^ 256 := rfl
  have hstart : (m.bumpAlloc size).start = m.watermark % 2 ^ 256 := by
    simp [bumpAlloc, Allocation.start, Evm.UInt256.toNat_ofNat]
  have hend : (m.bumpAlloc size).endExclusive = m.watermark % 2 ^ 256 + size := by
    rw [Allocation.endExclusive, hstart, bumpAlloc_size]
  rw [hbound] at hspace
  rcases Nat.lt_or_ge m.watermark (2 ^ 256) with hlt | hge
  · have hmod : m.watermark % 2 ^ 256 = m.watermark := Nat.mod_eq_of_lt hlt
    refine ⟨by rw [hend, hmod, hbound]; exact hspace, ?_⟩
    intro a' ha'
    exact Or.inr (by rw [hstart, hmod]; exact m.endExclusive_le_watermark ha')
  · have hwatermark : m.watermark = 2 ^ 256 := Nat.le_antisymm (by omega) hge
    have hsize : size = 0 := by omega
    have hend' : (m.bumpAlloc size).endExclusive = 0 := by
      rw [hend, hwatermark, hsize, Nat.mod_self]
    exact ⟨by rw [hend']; exact Nat.zero_le _,
      fun a' _ => Or.inl (by rw [hend']; exact Nat.zero_le _)⟩

theorem memoryPolicy_allows_bumpAlloc (m : MemoryState) (size : Nat)
    (hspace : m.watermark + size ≤ Evm.UInt256.size) :
    Machine.memoryPolicy.Allows m size (m.bumpAlloc size) :=
  ⟨m.isValidNewAlloc_bumpAlloc size hspace, m.bumpAlloc_size size⟩

end MemoryState

end Sir
