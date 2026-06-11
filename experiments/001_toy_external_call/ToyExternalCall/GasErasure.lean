import ToyExternalCall.EVMLemmas

/-!
# Gas erasure: the gasless IR semantics refines the metered one

If a gasless run succeeds, then for every sufficiently large representable
gas budget the metered run (`run evmCallOracle`) succeeds with the *same*
final state up to the remaining-gas counter (`run_erasure`).
-/

namespace ToyExternalCall

open EvmYul

namespace GasErasure

/-! ## §1 `withGas`/`fullTank` projections and update algebra -/

section Projections

variable (s : Exec) (g g' : Word) (evm : EVM.State)

@[simp] theorem withGas_fuel : (s.withGas g).fuel = s.fuel := rfl

@[simp] theorem withGas_gas : (s.withGas g).evm.gasAvailable = g := rfl

@[simp] theorem withGas_withGas : (s.withGas g).withGas g' = s.withGas g' := rfl

@[simp] theorem withGas_activeWords :
    (s.withGas g).evm.toMachineState.activeWords =
      s.evm.toMachineState.activeWords := rfl

theorem wordTouchCost_withGas (addr : Word) :
    wordTouchCost (s.withGas g).evm addr = wordTouchCost s.evm addr := rfl

theorem callTouchCost_withGas (io is oo os : Word) :
    callTouchCost (s.withGas g).evm io is oo os =
      callTouchCost s.evm io is oo os := rfl

end Projections

/-! ## §2 `UInt256` and `L` arithmetic helpers -/

section Arith

theorem toNat_lt (a : Word) : a.toNat < UInt256.size := a.val.isLt

theorem toNat_inj {a b : Word} (h : a.toNat = b.toNat) : a = b := by
  obtain ⟨⟨av, ha⟩⟩ := a
  obtain ⟨⟨bv, hb⟩⟩ := b
  cases (show av = bv from h)
  rfl

theorem toNat_sub_of_le (a : Word) (c : Nat) (hc : c ≤ a.toNat) :
    (a - UInt256.ofNat c).toNat = a.toNat - c := by
  have hcs : c < UInt256.size := Nat.lt_of_le_of_lt hc (toNat_lt a)
  have hct : (UInt256.ofNat c).toNat = c := EVMLemmas.toNat_ofNat_of_lt hcs
  show (UInt256.sub a (UInt256.ofNat c)).toNat = a.toNat - c
  unfold UInt256.sub
  show ((a.val - (UInt256.ofNat c).val) : Fin UInt256.size).val = a.toNat - c
  rw [Fin.sub_def]
  show (UInt256.size - (UInt256.ofNat c).toNat + a.toNat) % UInt256.size = a.toNat - c
  rw [hct]
  have ha := toNat_lt a
  have h1 : UInt256.size - c + a.toNat = (a.toNat - c) + UInt256.size := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem sub_ofNat (G c : Nat) (hc : c ≤ G) (hG : G < UInt256.size) :
    UInt256.ofNat G - UInt256.ofNat c = UInt256.ofNat (G - c) := by
  apply toNat_inj
  rw [toNat_sub_of_le _ c (by rw [EVMLemmas.toNat_ofNat_of_lt hG]; exact hc),
    EVMLemmas.toNat_ofNat_of_lt hG,
    EVMLemmas.toNat_ofNat_of_lt (by omega)]

theorem toNat_add (a b : Word) :
    (a + b).toNat = (a.toNat + b.toNat) % UInt256.size := by
  show (UInt256.add a b).toNat = _
  unfold UInt256.add
  show ((a.val + b.val) : Fin UInt256.size).val = _
  rw [Fin.add_def]
  rfl

/-- `L n = n - n/64` dominates anything ≤ half of `n - 64`. -/
theorem le_L {a n : Nat} (h : 2 * a + 64 ≤ n) : a ≤ EVM.L n := by
  unfold EVM.L
  omega

end Arith

/-! ## §3 Erasure simulation relations and composition

`SimE A s t` says: above some gas threshold `G₀`, the metered action `A`
run from `s` with that budget succeeds, lands on the gasless result `t` up
to the remaining-gas counter, and nets at most `D` gas. `SimP` is the same
for actions returning a value alongside the state.
-/

def SimE (A : Exec → Except EVM.ExecutionException Exec) (s t : Exec) : Prop :=
  ∃ G₀ D : Nat, ∀ G : Nat, G₀ ≤ G → G < UInt256.size →
    ∃ gFin : Word,
      A (s.withGas (.ofNat G)) = .ok (t.withGas gFin) ∧ G - D ≤ gFin.toNat

def SimP (A : Exec → Except EVM.ExecutionException (Word × Exec))
    (s : Exec) (v : Word) (t : Exec) : Prop :=
  ∃ G₀ D : Nat, ∀ G : Nat, G₀ ≤ G → G < UInt256.size →
    ∃ gFin : Word,
      A (s.withGas (.ofNat G)) = .ok (v, t.withGas gFin) ∧ G - D ≤ gFin.toNat

theorem SimE.congrFun {A B : Exec → Except EVM.ExecutionException Exec} {s t : Exec}
    (h : SimE A s t) (hf : ∀ x, B x = A x) : SimE B s t := by
  obtain ⟨G₀, D, h⟩ := h
  exact ⟨G₀, D, fun G hG hsz => by rw [hf]; exact h G hG hsz⟩

theorem SimE.bindE {A₁ A₂ : Exec → Except EVM.ExecutionException Exec} {s t u : Exec}
    (h₁ : SimE A₁ s t) (h₂ : SimE A₂ t u) :
    SimE (fun x => A₁ x >>= A₂) s u := by
  obtain ⟨G₁, D₁, h₁⟩ := h₁
  obtain ⟨G₂, D₂, h₂⟩ := h₂
  refine ⟨max G₁ (G₂ + D₁), D₁ + D₂, fun G hG hsz => ?_⟩
  have hG₁ : G₁ ≤ G := le_trans (Nat.le_max_left _ _) hG
  have hG₂ : G₂ + D₁ ≤ G := le_trans (Nat.le_max_right _ _) hG
  obtain ⟨gMid, hA₁, hb₁⟩ := h₁ G hG₁ hsz
  obtain ⟨gFin, hA₂, hb₂⟩ := h₂ gMid.toNat (by omega) (toNat_lt _)
  rw [UInt256.ofNat_toNat] at hA₂
  refine ⟨gFin, ?_, by omega⟩
  show A₁ (s.withGas (.ofNat G)) >>= A₂ = _
  rw [hA₁]
  exact hA₂

theorem SimE.bindP {A₁ : Exec → Except EVM.ExecutionException Exec}
    {A₂ : Exec → Except EVM.ExecutionException (Word × Exec)}
    {s t u : Exec} {w : Word}
    (h₁ : SimE A₁ s t) (h₂ : SimP A₂ t w u) :
    SimP (fun x => A₁ x >>= A₂) s w u := by
  obtain ⟨G₁, D₁, h₁⟩ := h₁
  obtain ⟨G₂, D₂, h₂⟩ := h₂
  refine ⟨max G₁ (G₂ + D₁), D₁ + D₂, fun G hG hsz => ?_⟩
  have hG₁ : G₁ ≤ G := le_trans (Nat.le_max_left _ _) hG
  have hG₂ : G₂ + D₁ ≤ G := le_trans (Nat.le_max_right _ _) hG
  obtain ⟨gMid, hA₁, hb₁⟩ := h₁ G hG₁ hsz
  obtain ⟨gFin, hA₂, hb₂⟩ := h₂ gMid.toNat (by omega) (toNat_lt _)
  rw [UInt256.ofNat_toNat] at hA₂
  refine ⟨gFin, ?_, by omega⟩
  show A₁ (s.withGas (.ofNat G)) >>= A₂ = _
  rw [hA₁]
  exact hA₂

theorem SimP.bindE {A₁ : Exec → Except EVM.ExecutionException (Word × Exec)}
    {k : Word × Exec → Except EVM.ExecutionException Exec} {s t u : Exec} {v : Word}
    (h₁ : SimP A₁ s v t) (h₂ : SimE (fun x => k (v, x)) t u) :
    SimE (fun x => A₁ x >>= k) s u := by
  obtain ⟨G₁, D₁, h₁⟩ := h₁
  obtain ⟨G₂, D₂, h₂⟩ := h₂
  refine ⟨max G₁ (G₂ + D₁), D₁ + D₂, fun G hG hsz => ?_⟩
  have hG₁ : G₁ ≤ G := le_trans (Nat.le_max_left _ _) hG
  have hG₂ : G₂ + D₁ ≤ G := le_trans (Nat.le_max_right _ _) hG
  obtain ⟨gMid, hA₁, hb₁⟩ := h₁ G hG₁ hsz
  obtain ⟨gFin, hA₂, hb₂⟩ := h₂ gMid.toNat (by omega) (toNat_lt _)
  rw [UInt256.ofNat_toNat] at hA₂
  refine ⟨gFin, ?_, by omega⟩
  show A₁ (s.withGas (.ofNat G)) >>= k = _
  rw [hA₁]
  exact hA₂

/-! ## §4 Per-action erasure lemmas (non-call) -/

theorem gasless_opStep_fuel0 (evm : EVM.State) :
    Gasless.opStep ⟨evm, 0⟩ = .error .OutOfFuel := rfl

theorem gasless_opStep_fuel1 (evm : EVM.State) :
    Gasless.opStep ⟨evm, 1⟩ = .error .OutOfFuel := rfl

theorem gasless_opStep_eval (evm : EVM.State) (f : Nat) :
    Gasless.opStep ⟨evm, f + 2⟩ =
      .ok ⟨{evm with execLength := evm.execLength + 1}, f + 1⟩ := rfl

/-- The metered `opStep` on a state with explicit gas counter `g`. -/
theorem opStep_eval (c₁ c₂ : Nat) (evm : EVM.State) (g : Word) (f : Nat) :
    opStep c₁ c₂ ⟨{evm with gasAvailable := g}, f + 2⟩ =
      if g.toNat < c₁ then .error .OutOfGass
      else if (g - UInt256.ofNat c₁).toNat < c₂ then .error .OutOfGass
      else .ok ⟨{evm with
          gasAvailable := g - UInt256.ofNat c₁ - UInt256.ofNat c₂,
          execLength := evm.execLength + 1}, f + 1⟩ := by
  by_cases h₁ : g.toNat < c₁
  · simp [opStep, tick, payZ, chargeMem, h₁, Bind.bind, Except.bind]
  · by_cases h₂ : (g - UInt256.ofNat c₁).toNat < c₂
    · simp [opStep, tick, payZ, chargeMem, requireGas, Exec.chargeGas, h₁, h₂,
        Bind.bind, Except.bind]
    · simp [opStep, tick, payZ, chargeMem, requireGas, stepGuard, commit,
        Exec.chargeGas, Exec.bumpExecLength, h₁, h₂, Bind.bind, Except.bind]

theorem opStep_erases {s t : Exec} (c₁ c₂ : Nat) (h : Gasless.opStep s = .ok t)
    (G : Nat) (hG : c₁ + c₂ ≤ G) (hsz : G < UInt256.size) :
    opStep c₁ c₂ (s.withGas (.ofNat G)) =
      .ok (t.withGas (.ofNat (G - (c₁ + c₂)))) := by
  obtain ⟨evm, fuel⟩ := s
  match fuel with
  | 0 => rw [gasless_opStep_fuel0] at h; exact absurd h (by simp)
  | 1 => rw [gasless_opStep_fuel1] at h; exact absurd h (by simp)
  | f + 2 =>
      rw [gasless_opStep_eval] at h
      have ht : t = ⟨{evm with execLength := evm.execLength + 1}, f + 1⟩ :=
        (Except.ok.inj h).symm
      subst ht
      show opStep c₁ c₂ ⟨{evm with gasAvailable := .ofNat G}, f + 2⟩ = _
      rw [opStep_eval]
      rw [if_neg (show ¬ (UInt256.ofNat G).toNat < c₁ by
        rw [EVMLemmas.toNat_ofNat_of_lt hsz]; omega)]
      rw [if_neg (show ¬ (UInt256.ofNat G - UInt256.ofNat c₁).toNat < c₂ by
        rw [sub_ofNat G c₁ (by omega) hsz,
          EVMLemmas.toNat_ofNat_of_lt (by omega)]; omega)]
      rw [sub_ofNat G c₁ (by omega) hsz, sub_ofNat (G - c₁) c₂ (by omega) (by omega),
        show G - c₁ - c₂ = G - (c₁ + c₂) from by omega]
      rfl

theorem pushStep_erases {s t : Exec} (h : Gasless.opStep s = .ok t)
    (G : Nat) (hG : GasConstants.Gverylow ≤ G) (hsz : G < UInt256.size) :
    pushStep (s.withGas (.ofNat G)) =
      .ok (t.withGas (.ofNat (G - GasConstants.Gverylow))) := by
  have := opStep_erases 0 GasConstants.Gverylow h G (by omega) hsz
  rw [show 0 + GasConstants.Gverylow = GasConstants.Gverylow from by omega] at this
  exact this

theorem mloadStep_erases {s : Exec} {v : Word} {t : Exec} (addr : Word)
    (h : Gasless.mloadStep addr s = .ok (v, t))
    (G : Nat) (hG : wordTouchCost s.evm addr + GasConstants.Gverylow ≤ G)
    (hsz : G < UInt256.size) :
    mloadStep addr (s.withGas (.ofNat G)) =
      .ok (v, t.withGas
        (.ofNat (G - (wordTouchCost s.evm addr + GasConstants.Gverylow)))) := by
  cases hop : Gasless.opStep s with
  | error e =>
      simp [Gasless.mloadStep, hop, Bind.bind, Except.bind] at h
  | ok s₁ =>
      simp only [Gasless.mloadStep, hop, Bind.bind, Except.bind,
        MachineState.mload, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, ht⟩ := h
      subst hv
      subst ht
      simp only [mloadStep, wordTouchCost_withGas, Bind.bind, Except.bind]
      rw [opStep_erases _ _ hop G hG hsz]
      rfl

theorem mstoreStep_erases {s t : Exec} (addr v : Word)
    (h : Gasless.mstoreStep addr v s = .ok t)
    (G : Nat) (hG : wordTouchCost s.evm addr + GasConstants.Gverylow ≤ G)
    (hsz : G < UInt256.size) :
    mstoreStep addr v (s.withGas (.ofNat G)) =
      .ok (t.withGas
        (.ofNat (G - (wordTouchCost s.evm addr + GasConstants.Gverylow)))) := by
  cases hop : Gasless.opStep s with
  | error e =>
      simp [Gasless.mstoreStep, hop, Bind.bind, Except.bind] at h
  | ok s₁ =>
      simp only [Gasless.mstoreStep, hop, Bind.bind, Except.bind,
        Except.ok.injEq] at h
      subst h
      simp only [mstoreStep, wordTouchCost_withGas, Bind.bind, Except.bind]
      rw [opStep_erases _ _ hop G hG hsz]
      rfl

theorem stopStep_erases {s t : Exec} (h : Gasless.stopStep s = .ok t)
    (G : Nat) (hsz : G < UInt256.size) :
    stopStep (s.withGas (.ofNat G)) =
      .ok (t.withGas (.ofNat (G - GasConstants.Gzero))) := by
  cases hop : Gasless.opStep s with
  | error e =>
      simp [Gasless.stopStep, hop, Bind.bind, Except.bind] at h
  | ok s₁ =>
      simp only [Gasless.stopStep, hop, Bind.bind, Except.bind,
        Except.ok.injEq] at h
      subst h
      simp only [stopStep, Bind.bind, Except.bind]
      rw [opStep_erases 0 GasConstants.Gzero hop G
        (by show 0 + 0 ≤ G; omega) hsz]
      rfl

/-! ## §5 Cap analysis: `Cgascap`/`Ccallgas`/`Ccall` under an adequate budget -/

/-- Reduce a mod by `UInt256.size` of anything below `2·size`. -/
theorem two_mod (a : Nat) (h : a < 2 * UInt256.size) :
    a % UInt256.size = if a < UInt256.size then a else a - UInt256.size := by
  have hS : 0 < UInt256.size := by
    show 0 < UInt256.size
    unfold UInt256.size
    omega
  by_cases h1 : a < UInt256.size
  · rw [if_pos h1, Nat.mod_eq_of_lt h1]
  · rw [if_neg h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem add_left_cancel' {a b c : Word} (h : a + b = a + c) : b = c := by
  apply toNat_inj
  have hb := congrArg UInt256.toNat h
  rw [toNat_add, toNat_add] at hb
  have h1 := toNat_lt a
  have h2 := toNat_lt b
  have h3 := toNat_lt c
  rw [two_mod _ (by omega), two_mod _ (by omega)] at hb
  split_ifs at hb <;> omega

/-- With `Cextra + 2·g + 64` gas available, the 63/64 cap does not bind:
the gas cap is exactly the requested `g`. -/
theorem Cgascap_eq (t r : AccountAddress) (val g : Word)
    (σ : AccountMap .EVM) (μ : MachineState) (A : Substate)
    (h : EVM.Cextra t r val σ A + 2 * g.toNat + 64 ≤ μ.gasAvailable.toNat) :
    EVM.Cgascap t r val g σ μ A = g.toNat := by
  unfold EVM.Cgascap
  rw [if_pos (by omega)]
  exact min_eq_right (le_L (by omega))

/-- Two machine states whose gas caps both evaluate to `g` forward the same
call gas. -/
theorem Ccallgas_congr (t r : AccountAddress) (val g : Word)
    (σ : AccountMap .EVM) (A : Substate) (μ₁ μ₂ : MachineState)
    (h₁ : EVM.Cgascap t r val g σ μ₁ A = g.toNat)
    (h₂ : EVM.Cgascap t r val g σ μ₂ A = g.toNat) :
    EVM.Ccallgas t r val g σ μ₁ A = EVM.Ccallgas t r val g σ μ₂ A := by
  unfold EVM.Ccallgas
  rw [h₁, h₂]

theorem Ccall_eq (t r : AccountAddress) (val g : Word)
    (σ : AccountMap .EVM) (μ : MachineState) (A : Substate)
    (h : EVM.Cgascap t r val g σ μ A = g.toNat) :
    EVM.Ccall t r val g σ μ A = g.toNat + EVM.Cextra t r val σ A := by
  unfold EVM.Ccall
  rw [h]

/-! ## §6 `EVM.call` agreement up to the caller's gas counter -/

theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {b : β}
    (h : x >>= k = .ok b) : ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [Bind.bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-- **Gas agreement for `EVM.call`.** Run the same call from the same caller
state with two different gas counters (and deducted instruction costs). If
the forwarded gas (`Ccallgas`) agrees — which §5 guarantees under an
adequate budget — then a successful run on the second counter forces the
run on the first to succeed with the *same* flag and the *same* state up to
the caller's remaining-gas counter; the callee's refund `gr` is the same on
both sides. -/
theorem call_agree (f c : Nat) (bvh : List ByteArray)
    (gas source recipient tw value value' io is oo os : Word) (perm : Bool)
    (st : EVM.State) (gfull : Word)
    (hcg : EVM.Ccallgas (.ofUInt256 tw) (.ofUInt256 recipient) value gas
             st.accountMap st.toMachineState st.substate =
           EVM.Ccallgas (.ofUInt256 tw) (.ofUInt256 recipient) value gas
             st.accountMap {st.toMachineState with gasAvailable := gfull} st.substate)
    {flag : Word} {e' : EVM.State}
    (h : EVM.call f 0 bvh gas source recipient tw value value' io is oo os perm
           {st with gasAvailable := gfull} = .ok (flag, e')) :
    ∃ gr : Word,
      e'.gasAvailable = (gfull - UInt256.ofNat 0) + gr ∧
      EVM.call f c bvh gas source recipient tw value value' io is oo os perm st =
        .ok (flag, {e' with gasAvailable := (st.gasAvailable - UInt256.ofNat c) + gr}) := by
  cases f with
  | zero =>
      rw [show EVM.call 0 0 bvh gas source recipient tw value value' io is oo os perm
          {st with gasAvailable := gfull} = .error .OutOfFuel from rfl] at h
      exact absurd h (by simp)
  | succ f' =>
      unfold EVM.call at h ⊢
      dsimp only at h ⊢
      rw [hcg]
      by_cases hcond : value ≤ (st.accountMap.find? st.executionEnv.codeOwner
            |>.option ⟨0⟩ (·.balance)) ∧ st.executionEnv.depth < 1024
      · rw [if_pos hcond] at h ⊢
        obtain ⟨a, hΘ, hk⟩ := bind_ok_inv h
        obtain ⟨cA, σ', g', A', z, o⟩ := a
        rw [hΘ]
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hk ⊢
        injection hk with hk
        injection hk with hflag he'
        subst hflag
        subst he'
        exact ⟨g', rfl, rfl⟩
      · rw [if_neg hcond] at h ⊢
        simp only [Bind.bind, Except.bind] at h ⊢
        injection h with h
        injection h with hflag he'
        subst hflag
        subst he'
        exact ⟨UInt256.ofNat (EVM.Ccallgas (.ofUInt256 tw) (.ofUInt256 recipient)
          value gas st.accountMap {st.toMachineState with gasAvailable := gfull}
          st.substate), rfl, rfl⟩

/-! ## §7 Erasure of the call step -/

/-- Evaluation equation for the gasless `callStep` (cf. the metered
`EVMLemmas.callStep_eval`). -/
theorem gasless_callStep_eval (g t v io is oo os : Word) (evm : EVM.State) (f : Nat) :
    Gasless.callStep g t v io is oo os ⟨evm, f + 1⟩ =
      if ¬ evm.executionEnv.perm ∧ ¬ v = UInt256.ofNat 0 then
        .error .StaticModeViolation
      else
        match f with
        | 0 => .error .OutOfFuel
        | _ + 1 =>
          match EVM.call (f - 1) 0 evm.executionEnv.blobVersionedHashes
              g (.ofNat evm.executionEnv.codeOwner) t t v v io is oo os
              evm.executionEnv.perm
              {evm with
                gasAvailable := UInt256.ofNat (UInt256.size - 1),
                execLength := evm.execLength + 1} with
          | .error e => .error e
          | .ok (flag, evm') => .ok (flag, ⟨evm', f⟩) := by
  by_cases h₃ : ¬ evm.executionEnv.perm ∧ ¬ v = UInt256.ofNat 0
  · simp [Gasless.callStep, tick, h₃, Bind.bind, Except.bind]
  · cases f with
    | zero =>
        simp [Gasless.callStep, tick, stepGuard, Bind.bind, Except.bind]
    | succ f'' =>
        simp only [Gasless.callStep, tick, stepGuard, h₃, Exec.bumpExecLength,
          Gasless.fullTank, Bind.bind, Except.bind, if_false]
        rfl

/-- The metered `callStep` on a state with explicit gas counter `gw`
(specialization of `EVMLemmas.callStep_eval`, with the caller state of the
forwarded call written in the canonical update shape). -/
theorem callStep_evalW (oracle : CallOracle) (g t v io is oo os : Word)
    (evm : EVM.State) (gw : Word) (f : Nat) :
    callStep oracle g t v io is oo os ⟨{evm with gasAvailable := gw}, f + 1⟩ =
      if gw.toNat < callTouchCost evm io is oo os then
        .error .OutOfGass
      else if (gw - UInt256.ofNat (callTouchCost evm io is oo os)).toNat <
          EVM.Ccall (.ofUInt256 t) (.ofUInt256 t) v g evm.accountMap
            {evm.toMachineState with
              gasAvailable := gw - UInt256.ofNat (callTouchCost evm io is oo os)}
            evm.substate then
        .error .OutOfGass
      else if ¬ evm.executionEnv.perm ∧ ¬ v = UInt256.ofNat 0 then
        .error .StaticModeViolation
      else
        match f with
        | 0 => .error .OutOfFuel
        | _ + 1 =>
          match oracle (f - 1)
              (EVM.Ccall (.ofUInt256 t) (.ofUInt256 t) v g evm.accountMap
                {evm.toMachineState with
                  gasAvailable := gw - UInt256.ofNat (callTouchCost evm io is oo os)}
                evm.substate)
              {evm with
                gasAvailable := gw - UInt256.ofNat (callTouchCost evm io is oo os),
                execLength := evm.execLength + 1}
              g t v io is oo os with
          | .error e => .error e
          | .ok (flag, evm') => .ok (flag, ⟨evm', f⟩) := by
  rw [EVMLemmas.callStep_eval]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Erasure of the call step.** If the gasless call step succeeds, the
metered one (against the canonical oracle, i.e. `EVM.call` itself) succeeds
above an adequate budget, with the same flag and state up to gas. The
threshold guarantees the 63/64 cap binds on neither side, so the callee is
run on exactly the same forwarded gas and is *the same computation* —
`call_agree` then transports the gasless success. -/
theorem callStep_erases {s : Exec} {flag : Word} {s' : Exec}
    (gas target value io is oo os : Word)
    (h : Gasless.callStep gas target value io is oo os s = .ok (flag, s')) :
    SimP (fun x => callStep evmCallOracle gas target value io is oo os x) s flag s' := by
  obtain ⟨evm, fuel⟩ := s
  cases fuel with
  | zero => exact absurd h (by simp [Gasless.callStep, tick, Bind.bind, Except.bind])
  | succ f =>
      rw [gasless_callStep_eval] at h
      by_cases h₃ : ¬ evm.executionEnv.perm ∧ ¬ value = UInt256.ofNat 0
      · rw [if_pos h₃] at h
        exact absurd h (by simp)
      · rw [if_neg h₃] at h
        cases f with
        | zero => exact absurd h (by simp)
        | succ f' =>
            dsimp only at h
            simp only [Nat.add_sub_cancel] at h
            cases hcall : EVM.call f' 0 evm.executionEnv.blobVersionedHashes gas
                (.ofNat evm.executionEnv.codeOwner) target target value value io is oo os
                evm.executionEnv.perm
                {evm with
                  gasAvailable := UInt256.ofNat (UInt256.size - 1),
                  execLength := evm.execLength + 1} with
            | error e => rw [hcall] at h; exact absurd h (by simp)
            | ok p =>
                obtain ⟨fl, evmRes⟩ := p
                rw [hcall] at h
                injection h with h
                injection h with hflag hs'
                subst hflag
                subst hs'
                -- Phase 1: extract the callee's gas refund from the gasless run.
                obtain ⟨gr, hgr, -⟩ := call_agree f' 0
                  evm.executionEnv.blobVersionedHashes gas
                  (.ofNat evm.executionEnv.codeOwner) target target value value
                  io is oo os evm.executionEnv.perm
                  {evm with
                    gasAvailable := UInt256.ofNat (UInt256.size - 1),
                    execLength := evm.execLength + 1}
                  (UInt256.ofNat (UInt256.size - 1)) rfl hcall
                have hpos : 0 < UInt256.size := by unfold UInt256.size; omega
                have hgrlt := toNat_lt gr
                -- Phase 2, uniform in G: the metered call step evaluates with
                -- final gas `(G - ctc) - (gas + Cextra) + gr`.
                have hmain : ∀ G : Nat,
                    callTouchCost evm io is oo os +
                      EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate + 2 * gas.toNat + 64 ≤ G →
                    G < UInt256.size →
                    callStep evmCallOracle gas target value io is oo os
                      ⟨{evm with gasAvailable := UInt256.ofNat G}, f' + 1 + 1⟩ =
                    .ok (fl, (⟨evmRes, f' + 1⟩ : Exec).withGas
                      ((UInt256.ofNat (G - callTouchCost evm io is oo os) -
                        UInt256.ofNat (gas.toNat +
                          EVM.Cextra (AccountAddress.ofUInt256 target)
                            (AccountAddress.ofUInt256 target) value evm.accountMap
                            evm.substate)) + gr)) := by
                  intro G hT hsz
                  have hcap : EVM.Cgascap (AccountAddress.ofUInt256 target)
                      (AccountAddress.ofUInt256 target) value gas evm.accountMap
                      {evm.toMachineState with
                        gasAvailable := UInt256.ofNat (G - callTouchCost evm io is oo os)}
                      evm.substate = gas.toNat := by
                    apply Cgascap_eq
                    show EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate + 2 * gas.toNat + 64 ≤
                      (UInt256.ofNat (G - callTouchCost evm io is oo os)).toNat
                    rw [EVMLemmas.toNat_ofNat_of_lt (by omega)]
                    omega
                  have hcapFull : EVM.Cgascap (AccountAddress.ofUInt256 target)
                      (AccountAddress.ofUInt256 target) value gas evm.accountMap
                      {evm.toMachineState with
                        gasAvailable := UInt256.ofNat (UInt256.size - 1)}
                      evm.substate = gas.toNat := by
                    apply Cgascap_eq
                    show EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate + 2 * gas.toNat + 64 ≤
                      (UInt256.ofNat (UInt256.size - 1)).toNat
                    rw [EVMLemmas.toNat_ofNat_of_lt (by omega)]
                    omega
                  have hC2 : EVM.Ccall (AccountAddress.ofUInt256 target)
                      (AccountAddress.ofUInt256 target) value gas evm.accountMap
                      {evm.toMachineState with
                        gasAvailable := UInt256.ofNat (G - callTouchCost evm io is oo os)}
                      evm.substate
                      = gas.toNat + EVM.Cextra (AccountAddress.ofUInt256 target)
                          (AccountAddress.ofUInt256 target) value evm.accountMap
                          evm.substate :=
                    Ccall_eq _ _ _ _ _ _ _ hcap
                  obtain ⟨grG, hgrG, hmet⟩ := call_agree f'
                    (gas.toNat + EVM.Cextra (AccountAddress.ofUInt256 target)
                      (AccountAddress.ofUInt256 target) value evm.accountMap evm.substate)
                    evm.executionEnv.blobVersionedHashes gas
                    (.ofNat evm.executionEnv.codeOwner) target target value value
                    io is oo os evm.executionEnv.perm
                    {evm with
                      gasAvailable := UInt256.ofNat (G - callTouchCost evm io is oo os),
                      execLength := evm.execLength + 1}
                    (UInt256.ofNat (UInt256.size - 1))
                    (Ccallgas_congr _ _ _ _ _ _ _ _ hcap hcapFull) hcall
                  rw [← add_left_cancel' (hgr.symm.trans hgrG)] at hmet
                  rw [callStep_evalW]
                  rw [sub_ofNat G (callTouchCost evm io is oo os) (by omega) hsz]
                  rw [if_neg (show ¬ (UInt256.ofNat G).toNat <
                      callTouchCost evm io is oo os by
                    rw [EVMLemmas.toNat_ofNat_of_lt hsz]; omega)]
                  rw [if_neg (show
                      ¬ (UInt256.ofNat (G - callTouchCost evm io is oo os)).toNat <
                        EVM.Ccall (AccountAddress.ofUInt256 target)
                          (AccountAddress.ofUInt256 target) value gas evm.accountMap
                          {evm.toMachineState with
                            gasAvailable :=
                              UInt256.ofNat (G - callTouchCost evm io is oo os)}
                          evm.substate by
                    rw [hC2, EVMLemmas.toNat_ofNat_of_lt (by omega)]; omega)]
                  rw [if_neg h₃]
                  dsimp only
                  simp only [Nat.add_sub_cancel]
                  simp only [evmCallOracle]
                  rw [hC2]
                  rw [hmet]
                  rfl
                -- Choose the threshold/net-cost pair, absorbing a possible
                -- wrap of the refunded gas counter.
                by_cases hK : gr.toNat ≤ callTouchCost evm io is oo os +
                    (gas.toNat + EVM.Cextra (AccountAddress.ofUInt256 target)
                      (AccountAddress.ofUInt256 target) value evm.accountMap evm.substate)
                · refine ⟨callTouchCost evm io is oo os +
                      EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate + 2 * gas.toNat + 64,
                    callTouchCost evm io is oo os +
                      (gas.toNat + EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate),
                    fun G hG hsz => ?_⟩
                  refine ⟨(UInt256.ofNat (G - callTouchCost evm io is oo os) -
                      UInt256.ofNat (gas.toNat +
                        EVM.Cextra (AccountAddress.ofUInt256 target)
                          (AccountAddress.ofUInt256 target) value evm.accountMap
                          evm.substate)) + gr, hmain G hG hsz, ?_⟩
                  rw [sub_ofNat _ _ (by omega) (by omega), toNat_add,
                    EVMLemmas.toNat_ofNat_of_lt (by omega),
                    two_mod _ (by omega), if_pos (by omega)]
                  omega
                · refine ⟨max (callTouchCost evm io is oo os +
                      EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate + 2 * gas.toNat + 64)
                      (UInt256.size + (callTouchCost evm io is oo os +
                        (gas.toNat + EVM.Cextra (AccountAddress.ofUInt256 target)
                          (AccountAddress.ofUInt256 target) value evm.accountMap
                          evm.substate)) - gr.toNat),
                    callTouchCost evm io is oo os +
                      (gas.toNat + EVM.Cextra (AccountAddress.ofUInt256 target)
                        (AccountAddress.ofUInt256 target) value evm.accountMap
                        evm.substate) + UInt256.size - gr.toNat,
                    fun G hG hsz => ?_⟩
                  have hG₁ := le_trans (Nat.le_max_left _ _) hG
                  have hG₂ := le_trans (Nat.le_max_right _ _) hG
                  refine ⟨(UInt256.ofNat (G - callTouchCost evm io is oo os) -
                      UInt256.ofNat (gas.toNat +
                        EVM.Cextra (AccountAddress.ofUInt256 target)
                          (AccountAddress.ofUInt256 target) value evm.accountMap
                          evm.substate)) + gr, hmain G hG₁ hsz, ?_⟩
                  rw [sub_ofNat _ _ (by omega) (by omega), toNat_add,
                    EVMLemmas.toNat_ofNat_of_lt (by omega),
                    two_mod _ (by omega), if_neg (by omega)]
                  omega

/-! ## §8 Instruction-level and program-level erasure -/

/-- Variant of `SimE.congrFun` only requiring agreement on the states the
simulation actually visits (those of the form `s.withGas g`). -/
theorem SimE.congrWithGas {A B : Exec → Except EVM.ExecutionException Exec} {s t : Exec}
    (h : SimE A s t) (hf : ∀ g : Word, B (s.withGas g) = A (s.withGas g)) :
    SimE B s t := by
  obtain ⟨G₀, D, h⟩ := h
  exact ⟨G₀, D, fun G hG hsz => by rw [hf]; exact h G hG hsz⟩

theorem pushStep_simE {s t : Exec} (h : Gasless.opStep s = .ok t) :
    SimE pushStep s t :=
  ⟨GasConstants.Gverylow, GasConstants.Gverylow, fun G hG hsz =>
    ⟨.ofNat (G - GasConstants.Gverylow), pushStep_erases h G hG hsz,
      Nat.le_of_eq (EVMLemmas.toNat_ofNat_of_lt (by omega)).symm⟩⟩

theorem stopStep_simE {s t : Exec} (h : Gasless.stopStep s = .ok t) :
    SimE (fun x => stopStep x) s t :=
  ⟨GasConstants.Gzero, GasConstants.Gzero, fun G hG hsz =>
    ⟨.ofNat (G - GasConstants.Gzero), stopStep_erases h G hsz,
      Nat.le_of_eq (EVMLemmas.toNat_ofNat_of_lt (by omega)).symm⟩⟩

theorem evalOperand_simP {s : Exec} {op : Operand} {v : Word} {t : Exec}
    (h : Gasless.evalOperand s op = .ok (v, t)) :
    SimP (fun x => evalOperand x op) s v t := by
  cases op with
  | const w =>
      cases hop : Gasless.opStep s with
      | error e => simp [Gasless.evalOperand, hop, Bind.bind, Except.bind] at h
      | ok s₁ =>
          simp only [Gasless.evalOperand, hop, Bind.bind, Except.bind,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, ht⟩ := h
          subst hv
          subst ht
          refine ⟨GasConstants.Gverylow, GasConstants.Gverylow, fun G hG hsz =>
            ⟨.ofNat (G - GasConstants.Gverylow), ?_,
              Nat.le_of_eq (EVMLemmas.toNat_ofNat_of_lt (by omega)).symm⟩⟩
          show evalOperand (s.withGas (.ofNat G)) (.const w) = _
          simp only [evalOperand]
          rw [pushStep_erases hop G hG hsz]
          rfl
  | «local» x =>
      cases hop : Gasless.opStep s with
      | error e => simp [Gasless.evalOperand, hop, Bind.bind, Except.bind] at h
      | ok s₁ =>
          have hml : Gasless.mloadStep (localSlot x) s₁ = .ok (v, t) := by
            simpa [Gasless.evalOperand, hop, Bind.bind, Except.bind] using h
          refine ⟨GasConstants.Gverylow +
              (wordTouchCost s₁.evm (localSlot x) + GasConstants.Gverylow),
            GasConstants.Gverylow +
              (wordTouchCost s₁.evm (localSlot x) + GasConstants.Gverylow),
            fun G hG hsz =>
            ⟨.ofNat (G - GasConstants.Gverylow -
              (wordTouchCost s₁.evm (localSlot x) + GasConstants.Gverylow)), ?_, by
              rw [EVMLemmas.toNat_ofNat_of_lt (by omega)]; omega⟩⟩
          show evalOperand (s.withGas (.ofNat G)) (.local x) = _
          simp only [evalOperand]
          rw [pushStep_erases hop G (by omega) hsz]
          show mloadStep (localSlot x)
            (s₁.withGas (UInt256.ofNat (G - GasConstants.Gverylow))) = _
          exact mloadStep_erases (localSlot x) hml (G - GasConstants.Gverylow)
            (by omega) (by omega)

theorem writeLocal_simE {s t : Exec} (x : Local) (v : Word)
    (h : Gasless.writeLocal s x v = .ok t) :
    SimE (fun y => writeLocal y x v) s t := by
  cases hop : Gasless.opStep s with
  | error e => simp [Gasless.writeLocal, hop, Bind.bind, Except.bind] at h
  | ok s₁ =>
      have hms : Gasless.mstoreStep (localSlot x) v s₁ = .ok t := by
        simpa [Gasless.writeLocal, hop, Bind.bind, Except.bind] using h
      refine ⟨GasConstants.Gverylow +
          (wordTouchCost s₁.evm (localSlot x) + GasConstants.Gverylow),
        GasConstants.Gverylow +
          (wordTouchCost s₁.evm (localSlot x) + GasConstants.Gverylow),
        fun G hG hsz =>
        ⟨.ofNat (G - GasConstants.Gverylow -
          (wordTouchCost s₁.evm (localSlot x) + GasConstants.Gverylow)), ?_, by
          rw [EVMLemmas.toNat_ofNat_of_lt (by omega)]; omega⟩⟩
      show writeLocal (s.withGas (.ofNat G)) x v = _
      simp only [writeLocal]
      rw [pushStep_erases hop G (by omega) hsz]
      show mstoreStep (localSlot x) v
        (s₁.withGas (UInt256.ofNat (G - GasConstants.Gverylow))) = _
      exact mstoreStep_erases (localSlot x) v hms (G - GasConstants.Gverylow)
        (by omega) (by omega)

theorem execInstr_erases {s : Exec} {instr : Instr} {t : Exec}
    (h : Gasless.execInstr s instr = .ok t) :
    SimE (fun x => execInstr evmCallOracle x instr) s t := by
  cases instr with
  | inputLoad dst offset =>
      cases h₁ : Gasless.evalOperand s offset with
      | error e => simp [Gasless.execInstr, h₁, Bind.bind, Except.bind] at h
      | ok p₁ =>
          obtain ⟨off, s₁⟩ := p₁
          cases h₂ : Gasless.opStep s₁ with
          | error e => simp [Gasless.execInstr, h₁, h₂, Bind.bind, Except.bind] at h
          | ok s₂ =>
              have h₃ : Gasless.writeLocal s₂ dst
                  (EvmYul.State.calldataload s₂.evm.toState off) = .ok t := by
                simpa [Gasless.execInstr, h₁, h₂, Bind.bind, Except.bind] using h
              exact SimP.bindE (evalOperand_simP h₁)
                (SimE.bindE (pushStep_simE h₂)
                  (SimE.congrWithGas
                    (writeLocal_simE dst (EvmYul.State.calldataload s₂.evm.toState off) h₃)
                    (fun g => rfl)))
  | add dst lhs rhs =>
      cases h₁ : Gasless.evalOperand s rhs with
      | error e => simp [Gasless.execInstr, h₁, Bind.bind, Except.bind] at h
      | ok p₁ =>
          obtain ⟨vr, s₁⟩ := p₁
          cases h₂ : Gasless.evalOperand s₁ lhs with
          | error e => simp [Gasless.execInstr, h₁, h₂, Bind.bind, Except.bind] at h
          | ok p₂ =>
              obtain ⟨vl, s₂⟩ := p₂
              cases h₃ : Gasless.opStep s₂ with
              | error e =>
                  simp [Gasless.execInstr, h₁, h₂, h₃, Bind.bind, Except.bind] at h
              | ok s₃ =>
                  have h₄ : Gasless.writeLocal s₃ dst (vl + vr) = .ok t := by
                    simpa [Gasless.execInstr, h₁, h₂, h₃, Bind.bind, Except.bind] using h
                  exact SimP.bindE (evalOperand_simP h₁)
                    (SimP.bindE (evalOperand_simP h₂)
                      (SimE.bindE (pushStep_simE h₃)
                        (writeLocal_simE dst (vl + vr) h₄)))
  | call dst args =>
      cases h₁ : Gasless.evalOperand s args.outSize with
      | error e => simp [Gasless.execInstr, h₁, Bind.bind, Except.bind] at h
      | ok p₁ =>
      obtain ⟨vOutSize, s₁⟩ := p₁
      cases h₂ : Gasless.evalOperand s₁ args.outOffset with
      | error e => simp [Gasless.execInstr, h₁, h₂, Bind.bind, Except.bind] at h
      | ok p₂ =>
      obtain ⟨vOutOffset, s₂⟩ := p₂
      cases h₃ : Gasless.evalOperand s₂ args.inSize with
      | error e => simp [Gasless.execInstr, h₁, h₂, h₃, Bind.bind, Except.bind] at h
      | ok p₃ =>
      obtain ⟨vInSize, s₃⟩ := p₃
      cases h₄ : Gasless.evalOperand s₃ args.inOffset with
      | error e => simp [Gasless.execInstr, h₁, h₂, h₃, h₄, Bind.bind, Except.bind] at h
      | ok p₄ =>
      obtain ⟨vInOffset, s₄⟩ := p₄
      cases h₅ : Gasless.evalOperand s₄ args.value with
      | error e =>
          simp [Gasless.execInstr, h₁, h₂, h₃, h₄, h₅, Bind.bind, Except.bind] at h
      | ok p₅ =>
      obtain ⟨vValue, s₅⟩ := p₅
      cases h₆ : Gasless.evalOperand s₅ args.target with
      | error e =>
          simp [Gasless.execInstr, h₁, h₂, h₃, h₄, h₅, h₆, Bind.bind, Except.bind] at h
      | ok p₆ =>
      obtain ⟨vTarget, s₆⟩ := p₆
      cases h₇ : Gasless.evalOperand s₆ args.gas with
      | error e =>
          simp [Gasless.execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
            Bind.bind, Except.bind] at h
      | ok p₇ =>
      obtain ⟨vGas, s₇⟩ := p₇
      cases h₈ : Gasless.callStep vGas vTarget vValue vInOffset vInSize vOutOffset
          vOutSize s₇ with
      | error e =>
          simp [Gasless.execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
            Bind.bind, Except.bind] at h
      | ok p₈ =>
      obtain ⟨fl, s₈⟩ := p₈
      have h₉ : Gasless.writeLocal s₈ dst fl = .ok t := by
        simpa [Gasless.execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
          Bind.bind, Except.bind] using h
      exact SimP.bindE (evalOperand_simP h₁)
        (SimP.bindE (evalOperand_simP h₂)
          (SimP.bindE (evalOperand_simP h₃)
            (SimP.bindE (evalOperand_simP h₄)
              (SimP.bindE (evalOperand_simP h₅)
                (SimP.bindE (evalOperand_simP h₆)
                  (SimP.bindE (evalOperand_simP h₇)
                    (SimP.bindE
                      (callStep_erases vGas vTarget vValue vInOffset vInSize
                        vOutOffset vOutSize h₈)
                      (writeLocal_simE dst fl h₉))))))))

theorem run_erases {program : Program} {s t : Exec}
    (h : Gasless.run program s = .ok t) :
    SimE (fun x => run evmCallOracle program x) s t := by
  induction program generalizing s with
  | nil => exact stopStep_simE h
  | cons instr rest ih =>
      cases hi : Gasless.execInstr s instr with
      | error e =>
          rw [show Gasless.run (instr :: rest) s =
              (match Gasless.execInstr s instr with
              | .ok s' => Gasless.run rest s'
              | .error e => .error e) from rfl, hi] at h
          exact absurd h (by simp)
      | ok s₁ =>
          rw [show Gasless.run (instr :: rest) s =
              (match Gasless.execInstr s instr with
              | .ok s' => Gasless.run rest s'
              | .error e => .error e) from rfl, hi] at h
          have hf : ∀ x, run evmCallOracle (instr :: rest) x =
              execInstr evmCallOracle x instr >>= fun y => run evmCallOracle rest y := by
            intro x
            cases hx : execInstr evmCallOracle x instr with
            | error e => simp [run, hx, Bind.bind, Except.bind]
            | ok y => simp [run, hx, Bind.bind, Except.bind]
          exact SimE.congrFun (SimE.bindE (execInstr_erases hi) (ih h)) hf

end GasErasure

/-- **Gas erasure**: a successful gasless run is refined by the metered run
on every sufficiently large representable gas budget — same final state up
to the remaining-gas counter. -/
theorem run_erasure (program : Program) (s s' : Exec)
    (h : Gasless.run program s = .ok s') :
    ∃ G₀ : Nat, ∀ G : Nat, G₀ ≤ G → G < UInt256.size →
      ∃ gFin : Word,
        run evmCallOracle program (s.withGas (.ofNat G)) = .ok (s'.withGas gFin) := by
  obtain ⟨G₀, D, hsim⟩ := GasErasure.run_erases h
  refine ⟨G₀, fun G hG hsz => ?_⟩
  obtain ⟨gFin, heq, -⟩ := hsim G hG hsz
  exact ⟨gFin, heq⟩

end ToyExternalCall

-- Verified: `#print axioms ToyExternalCall.run_erasure` reports exactly
-- [propext, Classical.choice, Quot.sound].
