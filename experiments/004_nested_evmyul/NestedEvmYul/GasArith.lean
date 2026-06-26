import EvmYul.EVM.Semantics

/-!
# UInt256 gas arithmetic helpers (shared, kernel-light)

`gas_sub_le` / `gas_branch_le` are split into their own module so that downstream
precompile gas lemmas reference them as *imported opaque constants* — the kernel then
never unfolds them together with an FFI-backed precompile body (which would overflow its
whnf recursion).
-/

namespace EvmYul.EVM.NeverOutOfFuel

open EvmYul EvmYul.EVM

/-- `(g - UInt256.ofNat m).toNat ≤ g.toNat` when `m ≤ g.toNat` (no wrap, `m < size`). -/
theorem gas_sub_le (g : UInt256) (m : ℕ) (hle : m ≤ g.toNat) (hm : m < UInt256.size) :
    (g - UInt256.ofNat m).toNat ≤ g.toNat := by
  have htn : g.toNat = g.val.val := rfl
  have hgsz : g.val.val < UInt256.size := g.val.isLt
  have hcmod : (Fin.ofNat UInt256.size m).val = m := by
    simp only [Fin.ofNat, Fin.val_ofNat]; exact Nat.mod_eq_of_lt hm
  have hsub : (g - UInt256.ofNat m).toNat = g.toNat - m := by
    show ((g.val - (Fin.ofNat _ m))).val = g.val.val - m
    rw [Fin.sub_def, hcmod]
    show (UInt256.size - m + g.val.val) % UInt256.size = g.val.val - m
    have hle' : m ≤ g.val.val := by rw [← htn]; exact hle
    have hrw : UInt256.size - m + g.val.val = (g.val.val - m) + UInt256.size := by omega
    rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hsub]; omega

/-- **Generic precompile gas-branch bound.** `(if g.toNat < gr then ⟨0⟩ else g − .ofNat gr)
.toNat ≤ g.toNat`: then-branch is `0`, else-branch is `g − gr ≤ g` (`gas_sub_le`, no wrap
since `gr ≤ g.toNat < size` there). Uniform closer for the simple precompile shapes. -/
theorem gas_branch_le (g : UInt256) (gr : ℕ) :
    (if g.toNat < gr then (⟨0⟩ : UInt256) else g - .ofNat gr).toNat ≤ g.toNat := by
  by_cases hlt : g.toNat < gr
  · rw [if_pos hlt]; exact Nat.zero_le _
  · rw [if_neg hlt]
    have hle : gr ≤ g.toNat := Nat.le_of_not_lt hlt
    exact gas_sub_le g gr hle (Nat.lt_of_le_of_lt hle g.val.isLt)

/-- Gas-projection bound through an inner `Except`-`match`, with the discriminant `res`
and BOTH arm bodies as parameters. The fallible precompiles (BN_ADD/BN_MUL/SNARKV/BLAKE2_F/
PointEval) instantiate `res` with their (kernel-heavy, FFI-backed) result; passing it as an
explicit argument means the kernel only has to check the application's type by *substitution*
(no whnf of the FFI body), sidestepping the `(kernel) deep recursion` overflow. -/
theorem match_proj_le {β : Type} (res : Except β ByteArray) (g : UInt256)
    (okf : ByteArray → Bool × AccountMap × UInt256 × Substate × ByteArray)
    (errf : β → Bool × AccountMap × UInt256 × Substate × ByteArray)
    (hok : ∀ o, (okf o).2.2.1.toNat ≤ g.toNat)
    (herr : ∀ e, (errf e).2.2.1.toNat ≤ g.toNat) :
    (match res with | .ok o => okf o | .error e => errf e).2.2.1.toNat ≤ g.toNat := by
  cases res with
  | ok o => exact hok o
  | error e => exact herr e

end EvmYul.EVM.NeverOutOfFuel
