import BytecodeLayer.Exec.Alignment
import BytecodeLayer.Exec.CallPreservesSelf

namespace BytecodeLayer.Exec.Recorder

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter

/-! ## §1 — the executable twin of `RunLog.clean` -/

/-- `cleanb` soundness: the `Bool` twin implies the `Prop` predicate. -/
theorem RunLog.clean_of_cleanb {log : RunLog} (h : log.cleanb = true) : log.clean := by
  unfold BytecodeLayer.Exec.Recorder.RunLog.cleanb at h
  unfold BytecodeLayer.Exec.Recorder.RunLog.clean
  cases hobs : log.observable with
  | call r =>
    rw [hobs] at h
    simpa using h
  | create r =>
    rw [hobs] at h
    cases h

/-! ## §2 — the `noErase` engine fact (the `hseams.noErase` seam, discharged)

Each stub lemma says: the precompile's account-map component is either its input map
or `∅`. `beginCall`'s `.inr` packaging then either keeps the caller's original map
(the `== ∅` fallback) or the stub's input map, which is `cp.accounts` after at most
two balance-credit `insert`s — presence-monotone (`accounts_find?_insert_mono`). -/

private theorem stub_accounts_ecRecover (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.ecRecover m g s env).2.1 = m ∨ (Precompiles.ecRecover m g s env).2.1 = ∅ := by
  unfold Precompiles.ecRecover
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_sha256 (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.sha256 m g s env).2.1 = m ∨ (Precompiles.sha256 m g s env).2.1 = ∅ := by
  unfold Precompiles.sha256
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_ripemd160 (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.ripemd160 m g s env).2.1 = m ∨ (Precompiles.ripemd160 m g s env).2.1 = ∅ := by
  unfold Precompiles.ripemd160
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_identity (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.identity m g s env).2.1 = m ∨ (Precompiles.identity m g s env).2.1 = ∅ := by
  unfold Precompiles.identity
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_modExp (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.modExp m g s env).2.1 = m ∨ (Precompiles.modExp m g s env).2.1 = ∅ := by
  unfold Precompiles.modExp
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_ecAdd (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.ecAdd m g s env).2.1 = m ∨ (Precompiles.ecAdd m g s env).2.1 = ∅ := by
  unfold Precompiles.ecAdd
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_ecMul (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.ecMul m g s env).2.1 = m ∨ (Precompiles.ecMul m g s env).2.1 = ∅ := by
  unfold Precompiles.ecMul
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_ecPairing (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.ecPairing m g s env).2.1 = m ∨ (Precompiles.ecPairing m g s env).2.1 = ∅ := by
  unfold Precompiles.ecPairing
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_blake2f (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.blake2f m g s env).2.1 = m ∨ (Precompiles.blake2f m g s env).2.1 = ∅ := by
  unfold Precompiles.blake2f
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

private theorem stub_accounts_pointEvaluation (m : AccountMap) (g : UInt64) (s : Substate)
    (env : ExecutionEnv) :
    (Precompiles.pointEvaluation m g s env).2.1 = m
      ∨ (Precompiles.pointEvaluation m g s env).2.1 = ∅ := by
  unfold Precompiles.pointEvaluation
  dsimp only []
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

/-- Presence closer for the `.inr` packaging: the result map is the original `orig` when
the stub map `x` is `∅` (the `==`-fallback), else `x` itself, which is the stub's input
map `m` (the `∅` case contradicts the guard). -/
private theorem accPresent_ite {a : AccountAddress} {orig m x : AccountMap}
    (horig : AccPresent a orig) (hm : AccPresent a m) (hx : x = m ∨ x = ∅) :
    AccPresent a (if x == ∅ then orig else x) := by
  split
  · exact horig
  · next hne =>
    rcases hx with rfl | rfl
    · exact hm
    · exact absurd rfl hne

/-- Presence closer for a goal already split into the stub-map branch: `x` is the stub's
input map `m` or `∅`; the non-`∅` split hypothesis rules the latter out. -/
private theorem accPresent_stub {a : AccountAddress} {x m : AccountMap}
    (hx : x = m ∨ x = ∅) (hm : AccPresent a m) (hne : ¬(x == ∅) = true) :
    AccPresent a x := by
  rcases hx with rfl | rfl
  · exact hm
  · exact absurd rfl hne

-- The unused-/unreachable-tactic linters are silenced for `beginCall_inr_noErase`: the
-- `solve` alternation closes each of the split's ~40 goals with whichever closer fits,
-- and a successful alternative may carry no-op or never-reached trailing steps on the
-- easy goals — every goal IS closed (the proof term is checked).
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **The `noErase` seam is an engine theorem** for `beginCall`
precompile stubs: an immediate `.inr` result preserves account presence. Verbatim the
`PrecompileAssumptions.noErase` field, discharged once for all `cp`. -/
theorem beginCall_inr_noErase :
    ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts := by
  intro cp imm h a hpres
  rcases hcs : cp.codeSource with code | p
  · exact absurd h (by simp [beginCall, hcs])
  · unfold beginCall at h
    rw [hcs] at h
    simp only [] at h
    repeat split at h
    all_goals (injection h with h; subst h; dsimp only [])
    all_goals solve
      | with_reducible exact hpres
      | (repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_ecRecover _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_sha256 _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_ripemd160 _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_identity _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_modExp _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_ecAdd _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_ecMul _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_ecPairing _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_blake2f _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_ite hpres ?_ (stub_accounts_pointEvaluation _ _ _ _);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_ecRecover _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_sha256 _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_ripemd160 _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_identity _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_modExp _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_ecAdd _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_ecMul _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_ecPairing _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_blake2f _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | (with_reducible refine accPresent_stub (stub_accounts_pointEvaluation _ _ _ _) ?_ (by assumption);
         repeat' first
           | with_reducible exact hpres
           | with_reducible apply accounts_find?_insert_mono
           | split)
      | with_reducible exact accPresent_ite hpres hpres (Or.inr rfl)
      | with_reducible exact accPresent_stub (Or.inr rfl) hpres (by assumption)


/-- The checker's head fact: a passing frame's own `.needsCall`s target code. -/
theorem callsCodeOk_head {fuel : ℕ} {fr : Frame}
    (hok : callsCodeOk fuel fr = true) : CallsCode fr := by
  intro cp pending hstep p hcs
  match fuel with
  | 0 => exact Bool.noConfusion hok
  | fuel+1 =>
    unfold callsCodeOk at hok
    rw [hstep] at hok
    dsimp only [] at hok
    rcases Bool.and_eq_true .. |>.mp hok with ⟨h1, _⟩
    rw [hcs] at h1
    dsimp only [] at h1
    exact Bool.noConfusion h1

/-- The checker steps down along a `StepsTo` edge. -/
theorem callsCodeOk_step {fuel : ℕ} {fr mid : Frame}
    (hok : callsCodeOk (fuel+1) fr = true) (hstep : StepsTo fr mid) :
    callsCodeOk fuel mid = true := by
  unfold callsCodeOk at hok
  rw [hstep.1] at hok
  dsimp only [] at hok
  rw [hstep.2]
  exact hok

/-- The checker steps down along a returning-CALL edge. -/
theorem callsCodeOk_call {fuel : ℕ} {fr resumeFr : Frame}
    (hok : callsCodeOk (fuel+1) fr = true) (hcall : CallReturns fr resumeFr) :
    callsCodeOk fuel resumeFr = true := by
  obtain ⟨cp, pending, child, childRes, hstep, hbegin, hdrive, hres⟩ := hcall
  unfold callsCodeOk at hok
  rw [hstep] at hok
  dsimp only [] at hok
  rcases Bool.and_eq_true .. |>.mp hok with ⟨_, h2⟩
  rw [hbegin] at h2
  dsimp only [] at h2
  rw [hdrive] at h2
  dsimp only [] at h2
  rw [hres]
  exact h2

/-- The checker steps down along a returning-CREATE edge. -/
theorem callsCodeOk_create {fuel : ℕ} {fr resumeFr : Frame}
    (hok : callsCodeOk (fuel+1) fr = true) (hc : CreateReturns fr resumeFr) :
    callsCodeOk fuel resumeFr = true := by
  obtain ⟨cp, pending, childRes, hstep, hdrive, hres⟩ := hc
  unfold callsCodeOk at hok
  rw [hstep] at hok
  dsimp only [] at hok
  rw [hdrive] at hok
  dsimp only [] at hok
  rw [hres] at hok
  exact hok

/-- **Checker soundness**: a passing check covers every `Runs`-reachable frame — the
chain is linear (`stepFrame`/`beginCall`/`drive`/resume are functions), so the checker's
replay visits every frame any `Runs` derivation can reach. -/
theorem callsCode_of_callsCodeOk {fr fr' : Frame} (h : Runs fr fr') :
    ∀ fuel, callsCodeOk fuel fr = true → CallsCode fr' := by
  induction h with
  | refl fr => exact fun _ hok => callsCodeOk_head hok
  | step hstep _ ih =>
    intro fuel hok
    match fuel with
    | 0 => exact Bool.noConfusion hok
    | fuel+1 => exact ih fuel (callsCodeOk_step hok hstep)
  | call hcall _ ih =>
    intro fuel hok
    match fuel with
    | 0 => exact Bool.noConfusion hok
    | fuel+1 => exact ih fuel (callsCodeOk_call hok hcall)
  | create hc _ ih =>
    intro fuel hok
    match fuel with
    | 0 => exact Bool.noConfusion hok
    | fuel+1 => exact ih fuel (callsCodeOk_create hok hc)

/-- The entry-level check: run the checker from `beginCall`'s entry frame (immediate
`.inr` entries have no reachable frames). -/
def entryCallsCodeOk (params : CallParams) (fuel : ℕ) : Bool :=
  match beginCall params with
  | .inl fr => callsCodeOk fuel fr
  | .inr _ => true

/-- Entry-check soundness: a passing entry check discharges the `callsCode` seam. -/
theorem callsCode_of_entryCheck {params : CallParams} {fuel : ℕ}
    (h : entryCallsCodeOk params fuel = true) :
    ∀ fr', BytecodeLayer.Exec.Invariants.ReachableFrom params fr' → CallsCode fr' := by
  rintro fr' ⟨fr₀, hbegin, hruns⟩
  unfold entryCallsCodeOk at h
  rw [hbegin] at h
  exact callsCode_of_callsCodeOk hruns fuel h

/-- The checker's head fact, create face: a passing frame's own `.needsCreate` with a
terminating init child resumes successfully (`CreateResolves`) — the resume-`.error`
arm of the checker is `false`, and `drive` is a function, so the hypothesis `childRes`
IS the checker's computed one. -/
theorem callsCodeOk_head_create {fuel : ℕ} {fr : Frame}
    (hok : callsCodeOk fuel fr = true) : CreateResolves fr := by
  intro cp pending childRes hstep hdrive
  match fuel with
  | 0 => exact Bool.noConfusion hok
  | fuel+1 =>
    unfold callsCodeOk at hok
    rw [hstep] at hok
    dsimp only [] at hok
    rw [hdrive] at hok
    dsimp only [] at hok
    cases hres : resumeAfterCreate childRes.toCreateResult pending with
    | ok resumeFr => exact ⟨resumeFr, rfl⟩
    | error e => rw [hres] at hok; exact Bool.noConfusion hok

/-- **Checker soundness, create face**: a passing check certifies `CreateResolves` at
every `Runs`-reachable frame — the same linear-chain replay as
`callsCode_of_callsCodeOk` (the descent lemmas are shared), landing on
`callsCodeOk_head_create` at the target frame. -/
theorem createResolves_of_callsCodeOk {fr fr' : Frame} (h : Runs fr fr') :
    ∀ fuel, callsCodeOk fuel fr = true → CreateResolves fr' := by
  induction h with
  | refl fr => exact fun _ hok => callsCodeOk_head_create hok
  | step hstep _ ih =>
    intro fuel hok
    match fuel with
    | 0 => exact Bool.noConfusion hok
    | fuel+1 => exact ih fuel (callsCodeOk_step hok hstep)
  | call hcall _ ih =>
    intro fuel hok
    match fuel with
    | 0 => exact Bool.noConfusion hok
    | fuel+1 => exact ih fuel (callsCodeOk_call hok hcall)
  | create hc _ ih =>
    intro fuel hok
    match fuel with
    | 0 => exact Bool.noConfusion hok
    | fuel+1 => exact ih fuel (callsCodeOk_create hok hc)

/-- Entry-check soundness, create face: a passing entry check discharges the
`createResolves` seam (immediate `.inr` entries have no reachable frames). -/
theorem createResolves_of_entryCheck {params : CallParams} {fuel : ℕ}
    (h : entryCallsCodeOk params fuel = true) :
    ∀ fr', BytecodeLayer.Exec.Invariants.ReachableFrom params fr' → CreateResolves fr' := by
  rintro fr' ⟨fr₀, hbegin, hruns⟩
  unfold entryCallsCodeOk at h
  rw [hbegin] at h
  exact createResolves_of_callsCodeOk hruns fuel h

end BytecodeLayer.Exec.Recorder
