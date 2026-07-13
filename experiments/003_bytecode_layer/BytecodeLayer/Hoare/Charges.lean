import BytecodeLayer.Hoare.Sequence

/-!
# General `subCharges` fold lemmas

The two general fold lemmas about `subCharges` (exp003 `Hoare.Sequence`, the
left-fold subtracting a charge list off the gas): how it distributes over a snoc
and an append. They are pure list-fold algebra — independent of any particular
program — so they live here in the shared charge-arithmetic module.
-/

namespace Lir

open BytecodeLayer.Hoare

/-- `subCharges` over a snoc: charging `c` last subtracts it last. -/
theorem subCharges_snoc (g : UInt64) (cs : List ℕ) (c : ℕ) :
    subCharges g (cs ++ [c]) = subCharges g cs - UInt64.ofNat c := by
  induction cs generalizing g with
  | nil => rfl
  | cons d cs ih => show subCharges (g - UInt64.ofNat d) (cs ++ [c]) = _; rw [ih]; rfl

/-- `subCharges` over an append: charge `a` then `b`. -/
theorem subCharges_append (g : UInt64) (a b : List ℕ) :
    subCharges g (a ++ b) = subCharges (subCharges g a) b := by
  induction a generalizing g with
  | nil => rfl
  | cons d a ih => show subCharges (g - UInt64.ofNat d) (a ++ b) = _; rw [ih]; rfl

end Lir
