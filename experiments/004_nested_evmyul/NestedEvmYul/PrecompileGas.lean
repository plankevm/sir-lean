import EvmYul.EVM.Semantics
import NestedEvmYul.GasArith

/-!
# Precompiled-contract gas-monotonicity bricks (`Θ`'s `.Precompiled` arm)

Each precompiled contract `Ξ_*` returns its leftover gas as
`if g.toNat < gᵣ then (⟨0⟩ : UInt256) else g − .ofNat gᵣ` (the "cheap-out" `⟨0⟩` when the
required gas `gᵣ` is not covered, otherwise `g − gᵣ`); the fallible ones (BN_ADD/BN_MUL/
SNARKV/BLAKE2_F/PointEval) additionally wrap the else-branch in a `match` on an elliptic-
curve / FFI result, whose `.error` arm also returns `⟨0⟩`. Either way the leftover gas is
`≤ g.toNat`, which is the `.Precompiled` arm of `Θ`'s gas-monotonicity.

These live in their **own module** (not in `NeverOutOfFuel`): the FFI-backed precompiles
(`BN_MUL`/`SNARKV`/…) have a kernel-heavy `String`-pattern `match` body, and when the
per-contract lemmas are kernel-checked deep inside the large `NeverOutOfFuel` compilation
unit they overflow the kernel's whnf recursion (`(kernel) deep recursion detected`). Each
lemma is identical-but-green when checked as its own top-level theorem here.
-/

namespace EvmYul.EVM.NeverOutOfFuel

open EvmYul EvmYul.EVM

/-- `Ξ_ECREC` leftover gas `≤ g`. (Simple shape: outer `if`, no inner result match.) -/
theorem ecrec_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ECREC σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_ECREC; simp only []
  rw [apply_ite (fun t : (Bool × AccountMap × UInt256 × Substate × ByteArray) => t.2.2.1)]
  exact gas_branch_le _ _

/-- `Ξ_SHA256` leftover gas `≤ g`. -/
theorem sha256_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SHA256 σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_SHA256; simp only []
  rw [apply_ite (fun t : (Bool × AccountMap × UInt256 × Substate × ByteArray) => t.2.2.1)]
  exact gas_branch_le _ _

/-- `Ξ_RIP160` leftover gas `≤ g`. -/
theorem rip160_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_RIP160 σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_RIP160; simp only []
  rw [apply_ite (fun t : (Bool × AccountMap × UInt256 × Substate × ByteArray) => t.2.2.1)]
  exact gas_branch_le _ _

/-- `Ξ_ID` leftover gas `≤ g`. -/
theorem id_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_ID σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_ID; simp only []
  rw [apply_ite (fun t : (Bool × AccountMap × UInt256 × Substate × ByteArray) => t.2.2.1)]
  exact gas_branch_le _ _

/-- `Ξ_EXPMOD` leftover gas `≤ g`. `gᵣ` contains nested `if`s (`adjusted_exp_length`),
so `split` would grab those; `apply_ite (·.2.2.1)` + `gas_branch_le` sidesteps it. -/
theorem expmod_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_EXPMOD σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_EXPMOD; simp only []
  rw [apply_ite (fun t : (Bool × AccountMap × UInt256 × Substate × ByteArray) => t.2.2.1)]
  exact gas_branch_le _ _

/-- `Ξ_BN_ADD` leftover gas `≤ g`. Else-branch has an inner `match BN_ADD …`; the
discriminant is made opaque by `generalize` (its FFI-backed `String`-pattern body would
otherwise force the kernel to whnf it), then `cases` splits the now-free var. -/
theorem bn_add_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_ADD σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_BN_ADD; dsimp only []
  by_cases hlt : g.toNat < (150 : ℕ)
  · rw [if_pos hlt]; exact Nat.zero_le _
  · rw [if_neg hlt]
    have hle : (150 : ℕ) ≤ g.toNat := Nat.le_of_not_lt hlt
    generalize BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) = o
    cases o with
    | error e => exact Nat.zero_le _
    | ok o => exact gas_sub_le g 150 hle (Nat.lt_of_le_of_lt hle g.val.isLt)

/-- `Ξ_BN_MUL` leftover gas `≤ g`. -/
theorem bn_mul_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BN_MUL σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_BN_MUL; dsimp only []
  by_cases hlt : g.toNat < (6000 : ℕ)
  · rw [if_pos hlt]; exact Nat.zero_le _
  · rw [if_neg hlt]
    have hle : (6000 : ℕ) ≤ g.toNat := Nat.le_of_not_lt hlt
    generalize BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
        (I.calldata.readBytes 64 32) = o
    cases o with
    | error e => exact Nat.zero_le _
    | ok o => exact gas_sub_le g 6000 hle (Nat.lt_of_le_of_lt hle g.val.isLt)

/-- `Ξ_SNARKV` leftover gas `≤ g` (computed `gᵣ = 34000*k + 45000`, inner match). -/
theorem snarkv_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_SNARKV σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_SNARKV; simp only []
  by_cases hlt : g.toNat < (34000 * (I.calldata.size / 192) + 45000 : ℕ)
  · rw [if_pos hlt]; exact Nat.zero_le _
  · rw [if_neg hlt]
    have hle := Nat.le_of_not_lt hlt
    generalize SNARKV I.calldata = o
    cases o with
    | error e => exact Nat.zero_le _
    | ok o => exact gas_sub_le g _ hle (Nat.lt_of_le_of_lt hle g.val.isLt)

/-- `Ξ_BLAKE2_F` leftover gas `≤ g` (computed `gᵣ` from calldata, inner match). -/
theorem blake2_f_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_BLAKE2_F σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_BLAKE2_F; simp only []
  by_cases hlt : g.toNat < (fromByteArrayBigEndian (I.calldata.extract 0 4) : ℕ)
  · rw [if_pos hlt]; exact Nat.zero_le _
  · rw [if_neg hlt]
    have hle := Nat.le_of_not_lt hlt
    generalize ffi.BLAKE2 I.calldata = o
    cases o with
    | error e => exact Nat.zero_le _
    | ok o => exact gas_sub_le g _ hle (Nat.lt_of_le_of_lt hle g.val.isLt)

/-- `Ξ_PointEval` leftover gas `≤ g`. -/
theorem point_eval_gas_le (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    (Ξ_PointEval σ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold Ξ_PointEval; simp only []
  by_cases hlt : g.toNat < (50000 : ℕ)
  · rw [if_pos hlt]; exact Nat.zero_le _
  · rw [if_neg hlt]
    have hle : (50000 : ℕ) ≤ g.toNat := Nat.le_of_not_lt hlt
    generalize PointEval I.calldata = o
    cases o with
    | error e => exact Nat.zero_le _
    | ok o => exact gas_sub_le g 50000 hle (Nat.lt_of_le_of_lt hle g.val.isLt)

end EvmYul.EVM.NeverOutOfFuel
