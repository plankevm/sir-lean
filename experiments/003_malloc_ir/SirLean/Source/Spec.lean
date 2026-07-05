import SirLean.Source.State
import SirLean.Source.WF

namespace Sir.Source

instance (a b : MemoryRange) : Decidable (a.Disjoint b) := by
  unfold MemoryRange.Disjoint
  infer_instance

instance (ranges : OccupiedMemory) (r : MemoryRange) : Decidable (ranges.Fresh r) := by
  unfold OccupiedMemory.Fresh
  infer_instance


def Allocator.bump : Allocator :=
  fun occupied size => do
    if occupied.isEmpty then
      return 0
    let r ← occupied.find? (fun r =>
      let start := r.endExclusive
      let r' := { addr := .ofNat start, size := size }
      start ≤ UInt32.size ∧ size.toNat ≤ UInt32.size - start ∧ decide (occupied.Fresh r')
    )
    return r.addr


theorem Allocator.bump_sound : Allocator.Sound Allocator.bump := by
  sorry

end Sir.Source
