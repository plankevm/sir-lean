import ToyExternalCall.Preservation

/-!
# Soundness of the canonical call oracle

`CallOracleSound evmCallOracle` was the one hypothesis left in the metered
lowering theorem. This file discharges it as a *theorem* about `EVM.call`:
the EVM's call function neither reads nor garbles the frame fields (`pc`,
machine `stack`, executing code) that `injectFrame` pins — every field it
consults passes through `injectFrame`, and the state it returns merges the
callee's effects into the caller state by record updates that commute with
`injectFrame` definitionally (structure eta).

The corollary `lowering_exact` is the assumption-free lowering theorem:
`Preservation.lowering_correct` instantiated with `evmCallOracle`.
-/

namespace ToyExternalCall

open EvmYul

namespace CallSound

/-- `map` after a bind is the bind with `map` fused into the continuation
(stated with the continuations abstract so it can be applied by `exact`,
letting defeq bridge the `injectFrame`-projected and plain argument
forms). -/
theorem bind_map_comm {ε α β γ : Type} (x : Except ε α)
    (k : α → Except ε β) (k' : α → Except ε γ) (g : β → γ)
    (hk : ∀ a, k' a = (k a).map g) :
    x >>= k' = (x >>= k).map g := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

/-- `map` distributes over `ite`. -/
theorem map_ite {ε α β : Type} (c : Prop) [Decidable c] (g : α → β)
    (x y : Except ε α) :
    (ite c x y).map g = ite c (x.map g) (y.map g) := by
  by_cases h : c <;> simp [h]

end CallSound

/-- **`EVM.call` is frame-insensitive.** Running it from an
`injectFrame`-pinned state yields exactly the result from the unpinned
state, with the frame re-pinned on the resulting state.

After unfolding, both sides are an `ite` (the funds/depth check) whose
branches bind a callee computation (`Θ`, or the no-call fallback tuple)
into a merge continuation. Everything `EVM.call` reads from the state is a
projection `injectFrame` passes through by `rfl`, so the two conditions and
the two callee computations are *definitionally* equal (`if_congr Iff.rfl`,
and the `exact`-applied `bind_map_comm` bridges the scrutinees by defeq);
the merged result states agree by structure eta — record-updating an
`injectFrame`-pinned state is definitionally pinning the record-updated
state. No record-commutation simp lemmas are needed (cf.
`docs/findings.md`: defeq bridging instead of update-commutation). -/
theorem evmCallOracle_sound : CallOracleSound evmCallOracle := by
  intro fuel gasCost s gas target value inOffset inSize outOffset outSize pc stk code
  cases fuel with
  | zero => rfl
  | succ f =>
      unfold evmCallOracle EVM.call
      dsimp only
      rw [CallSound.map_ite]
      refine if_congr Iff.rfl ?_ ?_
      · exact CallSound.bind_map_comm _ _ _ _ (fun a => rfl)
      · rfl

/-- **The assumption-free lowering theorem**: the metered preservation
theorem with its call oracle instantiated by `EVM.call` itself, the oracle
hypothesis discharged by `evmCallOracle_sound`. -/
theorem lowering_exact (program : Program) (vj : Array UInt256) (s : Exec)
    (hsize : (Bytecode.lower program).size < UInt256.size) :
    EVM.X s.fuel vj
      (injectFrame s.evm (.ofNat 0) [] (Bytecode.lower program)) =
      (run evmCallOracle program s).map (fun s' =>
        .success
          (injectFrame s'.evm (.ofNat ((Bytecode.lower program).size - 1)) []
            (Bytecode.lower program))
          ByteArray.empty) :=
  Preservation.lowering_correct evmCallOracle evmCallOracle_sound program vj s hsize

-- Axiom audit (`#print axioms`): both `evmCallOracle_sound` and
-- `lowering_exact` depend only on `propext`, `Classical.choice`,
-- `Quot.sound`.

end ToyExternalCall
