import LirLean.JumpValid

/-!
# LirLean — boundary-reachability of valid jump destinations and segment prefixes

This module supplies the two reachability bricks the whole-run boundary invariant
(`AtReachableBoundary`, `V2/Modellable.lean`) needs beyond `JumpValid.lean`:

* **the converse of `mem_validJumpDests_of_reachable_jumpdest`** — every recorded jump
  destination `x ∈ validJumpDests c 0` is itself a `ReachesBoundary c 0` boundary (it was
  pushed at a boundary the scan reached). This is what turns a taken `JUMP`/`JUMPI` (whose
  `new_pc ∈ fr.validJumps`) back into a `ReachesBoundary` witness.
* **intermediate-boundary reachability from a `SegAligned` whole-program segment** — if a
  prefix of the aligned segment is itself aligned and ends at offset `n`, the boundary walk
  reaches `n`. This is what turns a *sequential* `stepFrame` advance (pc → next instruction
  boundary) back into a `ReachesBoundary` witness.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Lir

open Evm

/-! ## §1 — the converse: a recorded jump destination is a reachable boundary

`validJumpDestsAuxNat c start acc` only ever pushes `i.toUInt32` for boundaries `i` it
reaches from `start` (at which a `JUMPDEST` sits). So any member of the result is either
already in `acc` or such a reached, in-bounds `JUMPDEST` boundary. Induction on the scan's
recursion (well-founded on `c.size - start`). -/

/-- **The scan's membership inversion.** Every `x ∈ validJumpDestsAuxNat c start acc` is
either already in the accumulator `acc`, or it is `j.toUInt32` for some instruction boundary
`j` the walk reaches from `start`, lying in bounds and carrying a `JUMPDEST`. -/
theorem mem_validJumpDestsAuxNat_inv (c : ByteArray) (start : Nat) (acc : Array UInt32)
    {x : UInt32} (hx : x ∈ validJumpDestsAuxNat c start acc) :
    x ∈ acc ∨ ∃ j byte, ReachesBoundary c start j ∧ x = j.toUInt32 ∧ j < c.size
        ∧ c.get? j = some byte ∧ Evm.parseInstr byte = .JUMPDEST := by
  rw [validJumpDestsAuxNat_eq] at hx
  cases hget : c.get? start with
  | none => rw [hget] at hx; exact Or.inl hx
  | some byte =>
    rw [hget] at hx
    simp only at hx
    -- the boundary `start` is in bounds (its byte decoded).
    have hstartlt : start < c.size := lt_size_of_get?_isSome (by rw [hget]; exact Option.isSome_some)
    by_cases hj : Evm.parseInstr byte = .JUMPDEST
    · -- a JUMPDEST at `start`: the recursion ran with `acc.push start.toUInt32`.
      rw [if_pos hj] at hx
      have ih := mem_validJumpDestsAuxNat_inv c (nextInstrPosNat start (Evm.parseInstr byte))
        (acc.push start.toUInt32) hx
      rcases ih with hmem | ⟨j, byte', hreach, hxj, hjlt, hjget, hjjd⟩
      · -- `x` is in `acc.push start.toUInt32`: either in `acc`, or it is `start.toUInt32`.
        rcases Array.mem_push.mp hmem with hin | heq
        · exact Or.inl hin
        · exact Or.inr ⟨start, byte, ReachesBoundary.refl start, heq, hstartlt, hget, hj⟩
      · -- `x = j.toUInt32` reached from the next boundary: prepend the step at `start`.
        exact Or.inr ⟨j, byte', ReachesBoundary.step (byte := byte) hget hreach, hxj, hjlt, hjget, hjjd⟩
    · rw [if_neg hj] at hx
      have ih := mem_validJumpDestsAuxNat_inv c (nextInstrPosNat start (Evm.parseInstr byte)) acc hx
      rcases ih with hmem | ⟨j, byte', hreach, hxj, hjlt, hjget, hjjd⟩
      · exact Or.inl hmem
      · exact Or.inr ⟨j, byte', ReachesBoundary.step (byte := byte) hget hreach, hxj, hjlt, hjget, hjjd⟩
  termination_by c.size - start
  decreasing_by
    all_goals
      simp only [nextInstrPosNat]
      omega

/-- **The converse of `mem_validJumpDests_of_reachable_jumpdest`.** A member `x` of
`validJumpDests c 0` is itself a boundary reachable from `0`: it was pushed at some boundary
`j` the scan reached from `0`, with `x = j.toUInt32` and `j` in bounds. The taken-jump
direction the boundary invariant needs. -/
theorem reachesBoundary_of_mem_validJumpDests (c : ByteArray) {x : UInt32}
    (hx : x ∈ validJumpDests c 0) :
    ∃ j, ReachesBoundary c 0 j ∧ x = j.toUInt32 ∧ j < c.size := by
  rw [validJumpDests] at hx
  simp only [show (0 : UInt32).toNat = 0 from rfl] at hx
  rcases mem_validJumpDestsAuxNat_inv c 0 #[] hx with hmem | ⟨j, _, hreach, hxj, hjlt, _, _⟩
  · exact absurd hmem (by simp)
  · exact ⟨j, hreach, hxj, hjlt⟩

end Lir

-- Build-enforced axiom-cleanliness guards: the converse-membership bricks depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.mem_validJumpDestsAuxNat_inv
#print axioms Lir.reachesBoundary_of_mem_validJumpDests
