import SirLean.Source.State
import SirLean.Source.WF

namespace Sir.Source

instance (a b : MemoryRange) : Decidable (a.Disjoint b) := by
  unfold MemoryRange.Disjoint
  infer_instance

instance (ranges : OccupiedRanges) (r : MemoryRange) : Decidable (ranges.Fresh r) := by
  unfold OccupiedRanges.Fresh
  infer_instance

theorem OccupiedRanges.empty_WF : OccupiedRanges.WF #[] := by simp [WF]

theorem Allocator.sound_ensures_ranges_WF :
    ∀ allocator : Allocator, allocator.Sound →
    ∀ ranges : OccupiedRanges,
    allocator.Provenance ranges → ranges.WF := by
  intro allocator sound ranges provenance
  simp [OccupiedRanges.WF]
  induction provenance
  case empty => simp
  case alloc oldRanges size addr prevProv halloc ih =>
    simp
    apply List.pairwise_append.mpr
    simp
    constructor
    . exact ih
    . {
      let new_alloc_fresh := (sound oldRanges size addr prevProv halloc).left
      simp at new_alloc_fresh
      simp [OccupiedRanges.Fresh] at new_alloc_fresh
      intro r' r'_mem
      exact (MemoryRange.Disjoint_comm r' ⟨addr, size⟩).mpr (new_alloc_fresh r' r'_mem)
    }

def Allocator.bump : Allocator :=
  fun occupied size =>
    let r := occupied.back?.getD ⟨0, 0⟩
    let new_start := r.endExclusive
    if new_start + size.toNat ≤ Word.size then
      .some (.ofNat new_start)
    else
      .none

-- theorem Allocator.bump_sound : Allocator.Sound Allocator.bump := by
--   intro ranges size addr _ h
--   unfold Allocator.bump at h
--   split at h
--   · simp [OccupiedRanges.Fresh, MemoryRange.Disjoint]
--
--
--
--   · cases hfind : ranges.find? (fun r =>
--       let start := r.endExclusive
--       let r' := { addr := .ofNat start, size := size }
--       start ≤ UInt32.size ∧ size.toNat ≤ UInt32.size - start ∧ decide (ranges.Fresh r')) <;> grind

end Sir.Source
