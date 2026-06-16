import Evm
import Batteries.Classes.Order

/-!
# Map reasoning bricks (proof-internal)

The EVM's `AccountMap` and `Storage` are `Batteries.RBMap`s; reasoning about
`insert`/`find?` for *symbolic* keys needs the `Std.TransCmp` law for the key
comparator, which leanevm does not yet provide (its `Maps/StorageMap.lean`
explicitly defers this). This file supplies the two missing `TransCmp` instances
(for `UInt256` and `AccountAddress`, both derived from their order, no `sorry`,
no `decide`) and the handful of `find?`/`findD` framing equations the SSTORE rule
needs to state *what storage it leaves untouched*.

These are pure data-structure facts; they mention no EVM execution concept.
-/

namespace BytecodeLayer
open Evm

/-! ## `TransCmp` for the key comparators -/

/-- `UInt256`'s bespoke `compare` agrees with `compareOfLessAndEq`. -/
theorem uint256_compare_eq (a b : UInt256) :
    compare a b = compareOfLessAndEq a b := by
  show (if a < b then Ordering.lt else if b < a then .gt else .eq) = compareOfLessAndEq a b
  unfold compareOfLessAndEq
  by_cases h : a < b
  · simp [h]
  · by_cases h2 : a = b
    · subst h2
      have hii : ¬ (a < a) := by show ¬ a.toBitVec < a.toBitVec; exact BitVec.lt_irrefl _
      rw [if_neg hii, if_pos rfl, if_neg hii, if_neg hii]
    · have hba : b < a := by
        show b.toBitVec < a.toBitVec
        have hle : b.toBitVec ≤ a.toBitVec := BitVec.not_lt.mp h
        rcases Std.le_iff_lt_or_eq.mp hle with hh2 | hh2
        · exact hh2
        · exact absurd (UInt256.toBitVec_inj hh2) (fun he => h2 he.symm)
      simp [h, hba, h2]

/-- `UInt256`'s comparator is transitive — the law `RBMap` lemmas require. -/
instance instTransCmpUInt256 : Std.TransCmp (compare : UInt256 → UInt256 → Ordering) := by
  have heq : (compare : UInt256 → UInt256 → Ordering) = (compareOfLessAndEq · ·) := by
    funext a b; exact uint256_compare_eq a b
  rw [heq]
  refine Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    (fun x => ?_) (fun {x y z} h1 h2 => ?_) (fun {x y} h1 h2 => ?_)
  · show ¬ x.toBitVec < x.toBitVec; exact BitVec.lt_irrefl _
  · show x.toBitVec < z.toBitVec; exact BitVec.lt_trans h1 h2
  · apply UInt256.toBitVec_inj
    exact BitVec.le_antisymm (BitVec.not_lt.mp h2) (BitVec.not_lt.mp h1)

/-- `AccountAddress`'s comparator (compare on the underlying `Fin`/`Nat`) is
transitive, inherited from `Nat`. -/
instance instTransCmpAddr : Std.TransCmp (compare : AccountAddress → AccountAddress → Ordering) := by
  have heq : (compare : AccountAddress → AccountAddress → Ordering)
      = (fun a b => compare a.val b.val) := rfl
  rw [heq]
  exact inferInstanceAs (Std.TransCmp (compareOn Fin.val))

/-! ## `compare … ≠ .eq ↔ key inequality`

The `RBMap` `_of_ne` lemmas are phrased on `compare k' k ≠ .eq`; the SSTORE rule
wants the readable `k' ≠ key`. These bridge the two for both key types. -/

theorem uint256_compare_ne_eq_of_ne {k' k : UInt256} (h : k' ≠ k) : compare k' k ≠ .eq := by
  rw [uint256_compare_eq]
  unfold compareOfLessAndEq
  by_cases h1 : k' < k
  · simp [h1]
  · simp only [h1, if_false]; simp [h]

theorem addr_compare_ne_eq_of_ne {a' a : AccountAddress} (h : a' ≠ a) : compare a' a ≠ .eq := by
  show compare a'.val a.val ≠ .eq
  have hne : a'.val ≠ a.val := fun he => h (Fin.ext he)
  exact fun hc => hne (Nat.compare_eq_eq.mp hc)

/-! ## Storage-map framing equations -/

/-- Reading the just-written `Storage` cell returns the written value. -/
theorem storage_findD_insert_self (s : Storage) (k v d : UInt256) :
    (s.insert k v).findD k d = v := by
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_eq s (by rw [show compare k k = Ordering.eq from
    by rw [uint256_compare_eq]; simp [compareOfLessAndEq]])]
  rfl

/-- Reading **another** `Storage` cell after a write returns its old value — the
storage-framing equation. -/
theorem storage_findD_insert_of_ne (s : Storage) {k' k : UInt256} (v d : UInt256)
    (h : k' ≠ k) : (s.insert k v).findD k' d = s.findD k' d := by
  unfold Batteries.RBMap.findD
  rw [Batteries.RBMap.find?_insert_of_ne s (uint256_compare_ne_eq_of_ne h)]

/-! ## Account-map framing equations -/

/-- Reading the just-written account returns it. -/
theorem accounts_find?_insert_self (m : AccountMap) (a : AccountAddress) (acc : Account) :
    (m.insert a acc).find? a = some acc := by
  rw [Batteries.RBMap.find?_insert_of_eq m (by
    show compare a.val a.val = Ordering.eq
    exact Nat.compare_eq_eq.mpr rfl)]

/-- Reading **another** account after a write returns its old entry. -/
theorem accounts_find?_insert_of_ne (m : AccountMap) {a' a : AccountAddress} (acc : Account)
    (h : a' ≠ a) : (m.insert a acc).find? a' = m.find? a' := by
  rw [Batteries.RBMap.find?_insert_of_ne m (addr_compare_ne_eq_of_ne h)]

end BytecodeLayer
