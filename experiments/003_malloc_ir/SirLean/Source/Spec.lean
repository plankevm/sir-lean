import SirLean.Source.State
import SirLean.Source.WF

namespace Sir.Source

instance (a b : MemoryRange) : Decidable (a.Disjoint b) := by
  unfold MemoryRange.Disjoint
  infer_instance

instance (ranges : OccupiedMemory) (r : MemoryRange) : Decidable (ranges.Fresh r) := by
  unfold OccupiedMemory.Fresh
  infer_instance

theorem OccupiedMemory.empty_WF : OccupiedMemory.WF #[] := by simp [WF]

theorem Allocator.sound_ensures_WF_occupied :
    ∀ allocator : Allocator, allocator.Sound →
    ∀ ranges : OccupiedMemory,
    allocator.Provenance ranges → ranges.WF := by
  intro allocator sound ranges provenance
  simp [OccupiedMemory.WF]
  cases provenance with
  | empty => sorry
  | alloc h => by
    sorry





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
--   · simp [OccupiedMemory.Fresh, MemoryRange.Disjoint]
--
--
--
--   · cases hfind : ranges.find? (fun r =>
--       let start := r.endExclusive
--       let r' := { addr := .ofNat start, size := size }
--       start ≤ UInt32.size ∧ size.toNat ≤ UInt32.size - start ∧ decide (ranges.Fresh r')) <;> grind

end Sir.Source
