import Evm

/-!
# UInt256/UInt64 gas-threading arithmetic (`UInt256`)

The one UInt64 fact the gas-honest floor forces: charging `c ≤ g.toNat` gas
(with `c` in range) leaves exactly `g.toNat - c`, used to carry the running
balance across charges in place of a shadow gas ledger.

Mirrors leanevm's `Evm/UInt256.lean`, its arith-lemma home.
-/

namespace BytecodeLayer.UInt256
open Evm

/-- `gasAvailable` threading: charging `c ≤ g.toNat` gas (with `c` in range)
leaves exactly `g.toNat - c`. The one piece of UInt64 arithmetic the gas-honest
floor forces — used to carry the running balance across charges, in place of a
shadow gas ledger. -/
theorem toNat_sub_ofNat (g : UInt64) (c : ℕ) (hc : c ≤ g.toNat) (hlt : c < 2 ^ 64) :
    (g - UInt64.ofNat c).toNat = g.toNat - c := by
  have hofNat : (UInt64.ofNat c).toNat = c := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
  have hle : UInt64.ofNat c ≤ g := by
    rw [UInt64.le_iff_toNat_le, hofNat]; exact hc
  rw [UInt64.toNat_sub_of_le _ _ hle, hofNat]

end BytecodeLayer.UInt256
