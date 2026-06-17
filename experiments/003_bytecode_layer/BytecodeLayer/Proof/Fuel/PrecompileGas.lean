import BytecodeLayer.Proof.DecodeGas

/-!
# Proof — precompile gas bounds (`PrecompileGas`)

Every precompile returns its gas component as either `0` (insufficient gas) or
`gas - .ofNat requiredGas` taken in the `gas.toNat ≥ requiredGas` branch (so the
subtraction does not wrap). Either way it is `≤ gas.toNat`.

This cluster was extracted from `Proof/DescentDrops.lean`; the capstone
`beginCall_inr_gas` feeds `descentDrops_conj5a` there (which imports this file).
-/

namespace BytecodeLayer.Proof
open Evm
open Evm.Operation
open GasConstants

/-! ## Precompile gas — a precompile consumes `≤` the forwarded gas -/

/-- The one UInt64 fact: `gas - .ofNat c` never exceeds `gas` (the only `else`
arms use it under `c ≤ gas.toNat`, where it is exact; here we need just `≤`,
which holds because `c < 2^64` follows from `c ≤ gas.toNat`). -/
theorem toNat_sub_ofNat_le {gas : UInt64} {c : ℕ} (hc : c ≤ gas.toNat) :
    (gas - UInt64.ofNat c).toNat ≤ gas.toNat := by
  rw [toNat_sub_ofNat gas c hc (Nat.lt_of_le_of_lt hc gas.toNat_lt)]
  exact Nat.sub_le _ _

/-- A precompile's returned gas (`.2.2.1`) is `≤` the forwarded `gas`. The proof
is uniform: `split` on the `gas.toNat < requiredGas` guard; the `then` arm
returns `0`, the `else` arm returns `gas - .ofNat requiredGas` under
`requiredGas ≤ gas.toNat` (possibly behind an inner `match` that does not touch
the gas). -/
private theorem hsub_le {gas : UInt64} (c : ℕ) (hc : ¬ gas.toNat < c) :
    (gas - UInt64.ofNat c).toNat ≤ gas.toNat :=
  toNat_sub_ofNat_le (Nat.not_lt.mp hc)

-- Precompiles whose gas component does NOT sit behind an inner `match`.
theorem ecRecover_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecRecover a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecRecover; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem sha256_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.sha256 a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.sha256; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem ripemd160_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ripemd160 a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ripemd160; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem identity_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.identity a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.identity; dsimp only; split
  · simp
  · rename_i h; exact hsub_le _ h
theorem modExp_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.modExp a g s e).2.2.1.toNat ≤ g.toNat := by
  -- `requiredGas` is itself an `if`-cascade; abstract it so the gas guard is a
  -- single `if`.
  unfold Precompiles.modExp; dsimp only
  generalize (max 200 _) = rg
  split
  · simp
  · rename_i h; dsimp only; exact hsub_le _ h
-- Precompiles whose gas component sits behind an inner `Except` `match`
-- (the `.error` arm returns gas `0`, the `.ok` arm returns `gas - requiredGas`).
theorem ecAdd_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecAdd a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecAdd; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem ecMul_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecMul a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecMul; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem ecPairing_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.ecPairing a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.ecPairing; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem blake2f_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.blake2f a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.blake2f; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp
theorem pointEvaluation_gas_le (a : AccountMap) (g : UInt64) (s : Substate) (e : ExecutionEnv) :
    (Precompiles.pointEvaluation a g s e).2.2.1.toNat ≤ g.toNat := by
  unfold Precompiles.pointEvaluation; dsimp only; split
  · simp
  · rename_i h; split
    · exact hsub_le _ h
    · simp

/-- **Precompile gas (conjunct 5a, the `beginCall` side).** A precompile entry
returns gas `≤ params.gas`. The `beginCall` precompile branch dispatches on the
precompile address; every arm's gas component is bounded by the per-precompile
lemmas above (the `_ => 0` default is bounded trivially). -/
theorem beginCall_inr_gas {p : CallParams} {result : CallResult}
    (h : beginCall p = .inr result) :
    result.gasRemaining.toNat ≤ p.gas.toNat := by
  unfold beginCall at h
  cases hcs : p.codeSource with
  | Code code => rw [hcs] at h; simp at h
  | Precompiled pc =>
    rw [hcs] at h
    simp only [Sum.inr.injEq] at h
    subst h
    dsimp only [CallResult.gasRemaining]
    split
    case _ => exact ecRecover_gas_le _ _ _ _
    case _ => exact sha256_gas_le _ _ _ _
    case _ => exact ripemd160_gas_le _ _ _ _
    case _ => exact identity_gas_le _ _ _ _
    case _ => exact modExp_gas_le _ _ _ _
    case _ => exact ecAdd_gas_le _ _ _ _
    case _ => exact ecMul_gas_le _ _ _ _
    case _ => exact ecPairing_gas_le _ _ _ _
    case _ => exact blake2f_gas_le _ _ _ _
    case _ => exact pointEvaluation_gas_le _ _ _ _
    case _ => simp

end BytecodeLayer.Proof
