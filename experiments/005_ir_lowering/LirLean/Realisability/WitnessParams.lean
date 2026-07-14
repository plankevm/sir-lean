import LirLean.Realisability.Witness

/-!
# LirLean — Realisability spec, WITNESS PARAMS (R12a's concrete run)

The concrete `CallParams` witness for `exProg_satisfies_hypotheses` (R12a,
`RealisabilitySpec.lean`) and the sorry-free machinery its conjuncts need. This module
is SORRY-FREE; it reduces R12a to exactly TWO decidable `Bool` leaves
(`exProg_satisfies_hypotheses_of_checks`). Contents:

* `RunLog.cleanb` — the executable `Bool` twin of the log-side clean-scope predicate
  (`RunLog.clean` is a `Prop` match; a `cleanb = true` evaluation discharges it);
* `beginCall_inr_noErase` — the **engine fact** behind the `hseams.noErase` seam,
  DISCHARGED for the current exp003 engine: every one of the 10 precompile stubs
  returns, in its account-map component, either its input map (= `cp.accounts` after
  at most two balance-credit `insert`s — presence-monotone) or `∅` (in which case
  `beginCall`'s packaging falls back to the caller's original map). R12a deliberately
  doubles as the machine-check of this fact against the seam bundle
  (`Spec/Seams.lean`, `PrecompileAssumptions.noErase`);
* `callsCodeOk` — a fuel-indexed **trace checker** for the `hseams.callsCode` AND
  `hseams.createResolves` seams: it replays the deterministic top-level chain
  (`stepFrame` steps, returning CALLs, returning CREATEs), checks every issued
  `.needsCall`'s code source, and checks every issued `.needsCreate` with a
  terminating init child resumes successfully. Soundness (`callsCode_of_entryCheck`,
  `createResolves_of_entryCheck`) turns ONE `Bool` evaluation into BOTH
  reachable-frame universals — the chain is linear because
  `stepFrame`/`beginCall`/`drive`/the resumes are functions;
* `exParams` — the literal witness params: recipient `0x1234` (a `default` account —
  the executed code is pinned by `codeSource := .Code (lower exProg)`), callee `0x100`
  (an ordinary empty-code account, NOT a precompile address `1..10`), `value := 0`,
  gas `25000` — tuned so the recorded run halts cleanly after ONE block-1 loop
  iteration (measured landscape, native probe: block 0's cold SLOAD + cold nonzero
  SSTORE + cold CALL + spill traffic clear at ≥ 24850; at 25000 the first `t6 := gas`
  read is already below the `1000` threshold, so the loop exits at once with 179 gas
  left — a clean `.stop`, 2 recorded gas reads, 1 sload, 1 call);
* `exProg_satisfies_hypotheses_of_checks` — **the R12a reduction**: from the two `Bool`
  leaves `exCheck = true` (the recorded run exists and is clean) and
  `entryCallsCodeOk exParams 4096 = true` (the `CallsCode` trace check), the FULL R12a
  conjunction follows by real (sorry-free) assembly.

## Where the two leaves ARE discharged (`WitnessChecks.lean`, kernel-certified)

Both leaves are decidable and TRUE; plain `decide +kernel` on the raw evaluators is
measured-infeasible (`native_decide` is banned repo-wide). Two DISTINCT walls, found in
order:

1. **Fuel-peel memory blow-up** (the original measured ladder): the v4.30 kernel's
   lazy whnf explodes evaluating `driveLog` at the 54096 seed fuel. Gas-prefix ladder,
   kernel wall-clock: 100 ↦ 1s, 3000 ↦ 2s, 10000 ↦ 2s, 23000 ↦ 5s, 24400 ↦ 5s,
   24700 (dies AT the CALL charge) ↦ 5s; 24770+ ↦ OOM-killed (>30 GB — 60 GB, 10–15
   min, 96 GB machine). Fixed by `SegmentedEval.lean`: the run is a linear chain of
   ONE-fuel transitions (`nextLog`/`stepsLog`; the witness run is 39 transitions
   total), composed back to the fuel-indexed evaluator by the shift/final lemmas —
   no fuel peel, no laziness pile-up.

2. **The `USize` opacity wall** (found once the fuel peel was gone): every padded
   byte-window primitive routes through `ffi.ByteArray.zeroes (u : USize)`, and
   `USize` normalization is stuck on the OPAQUE `System.Platform.getNumBits` —
   platform-dependent BY DESIGN, so NO kernel evaluation can cross it (first forced
   at transition 20, the CALL descent's calldata window; located with a kernel-whnf
   stuck-head chaser). Fixed by `CheckedStep.lean`: a checked twin evaluator with
   `ℕ`-computed padding twins for exactly the poisoned arms (MLOAD/MSTORE/CALL
   calldata) under decidable `< 2 ^ 32` bound checks (both platforms agree there —
   `System.Platform.numBits_eq`), delegation everywhere else, and full soundness
   back to the real chain.

`WitnessChecks.lean` runs THREE flagged `decide +kernel` cranks — the two heavy leaf
evaluations over the checked twin (~13s / 5.5 GB each) plus the cheap `seedFuel`
arithmetic pin — and transports the verdicts to `exCheck = true` (`exCheck_true`) and
`entryCallsCodeOk exParams 4096 = true` (`entryCallsCodeOk_exParams`);
`exProg_satisfies_hypotheses` (R12a) is CLOSED from them, axiom-clean
(`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `ofReduceBool`).
-/

namespace Lir

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
/-- **The `noErase` seam is an engine THEOREM** for the current exp003 `beginCall`
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
    ∀ fr', ReachableFrom params fr' → CallsCode fr' := by
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
    ∀ fr', ReachableFrom params fr' → CreateResolves fr' := by
  rintro fr' ⟨fr₀, hbegin, hruns⟩
  unfold entryCallsCodeOk at h
  rw [hbegin] at h
  exact createResolves_of_callsCodeOk hruns fuel h


/-! ## §4 — the concrete witness params -/

/-- The witness self (recipient) address. Arbitrary non-precompile address. -/
def exSelf : AccountAddress := Fin.ofNat _ 0x1234

/-- The witness callee address (`exProg`'s CALL target, `t4 := 0x100`): an ordinary
code account slot — NOT a precompile (`1..10`). -/
def exCallee : AccountAddress := Fin.ofNat _ 0x100

/-- The witness caller address (not present in the account map; `value = 0` makes the
transfer prologue a no-op on it). -/
def exCaller : AccountAddress := Fin.ofNat _ 0xC0FFEE

/-- The recipient's account: `default` (empty storage/code — the executed code is
pinned by `codeSource`, and `exProg`'s SLOAD/SSTORE run against this storage). -/
def exAcc : Account := default

/-- The witness account map: the recipient and the (empty-code) callee. -/
def exAccounts : AccountMap :=
  (Batteries.RBMap.empty.insert exSelf exAcc).insert exCallee default

/-- **The R12a witness `CallParams`.** Gas `25000`: enough to clear `exProg`'s block 0
(cold SLOAD `2100` + cold zero→nonzero SSTORE `22100` + cold CALL `2600` net of the
callee's returned forward + the emitted PUSH/MSTORE spill traffic — measured floor
`24850`), small enough that the first block-1 `t6 := gas` read is already below the
`1000` loop threshold: the loop exits after ONE iteration with `179` gas left, a clean
`.stop` (probed landscape: `24800 ↦ OOG`, `24850 ↦ rem 29`, `25000 ↦ rem 179`,
`25800 ↦ 2 iterations`). Keeps the two kernel cranks minimal. -/
def exParams : CallParams :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := #[]
    accounts := exAccounts
    originalAccounts := exAccounts
    substate := default
    caller := exCaller
    origin := exCaller
    recipient := exSelf
    codeSource := .Code (Lir.lower exProg)
    gas := 25000
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 1
    canModifyState := true }

/-- The single-evaluation run check: the recording interpreter completes on
`lower exProg` from `exParams` at the seeded fuel AND the recorded run halted cleanly
(the `cleanb` twin). One `Bool`, so ONE evaluation certifies both the `hrun` and the
`hclean` conjuncts. **R12a leaf 1 of 2** — TRUE by native evaluation (module header);
its in-kernel discharge is the measured-infeasible crank. -/
def exCheck : Bool :=
  match runWithLog exParams (seedFuel exParams.gas) with
  | some log => log.cleanb
  | none => false

/-- The recipient account is present (the flagship's `hself` at the witness). -/
theorem exParams_self_present : exParams.accounts.find? exParams.recipient = some exAcc := by
  rfl

/-- The witness gas floor (the flagship's `hgas` at the witness). -/
theorem exParams_gas_floor : GasConstants.Gjumpdest ≤ exParams.gas.toNat := by
  decide

/-! ## §5 — the R12a reduction (sorry-free; the two `Bool` leaves are the whole residue)

`entryCallsCodeOk exParams 4096 = true` is **R12a leaf 2 of 2** (fuel `4096` covers the
~hundred-step top-level chain with slack). -/

/-- **The R12a reduction.** From the two decidable leaves — the recorded run exists
and is clean (`exCheck`), and the seam trace check passes (`entryCallsCodeOk`)
— the FULL `exProg_satisfies_hypotheses` conjunction follows: the definitional pins
are `rfl`, presence/gas-floor are the closed lemmas above, `hrun`/`hclean` fall out of
the `exCheck` match, and the seam structure combines the engine-level
`beginCall_inr_noErase` theorem with the checker soundness lemmas
`callsCode_of_entryCheck` + `createResolves_of_entryCheck` (one shared `Bool`
evaluation covers both reachable-frame seam faces; `exProg` is create-free, so the
create face is exercised vacuously — no reachable `.needsCreate`).
R12a (`RealisabilitySpec.lean`) = this theorem + the two leaves. -/
theorem exProg_satisfies_hypotheses_of_checks
    (hchk : exCheck = true)
    (hcc : entryCallsCodeOk exParams 4096 = true) :
    ∃ (params : CallParams) (log : RunLog) (acc : Account),
      params.codeSource = .Code (Lir.lower exProg)
      ∧ params.canModifyState = true
      ∧ params.accounts.find? params.recipient = some acc
      ∧ GasConstants.Gjumpdest ≤ params.gas.toNat
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ log.clean
      ∧ PrecompileAssumptions exProg params := by
  unfold exCheck at hchk
  revert hchk
  cases hrun : runWithLog exParams (seedFuel exParams.gas) with
  | none => exact fun hchk => Bool.noConfusion hchk
  | some log =>
    intro hcleanb
    exact ⟨exParams, log, exAcc, rfl, rfl, exParams_self_present, exParams_gas_floor,
      hrun, RunLog.clean_of_cleanb hcleanb,
      { noErase := beginCall_inr_noErase
        callsCode := callsCode_of_entryCheck hcc
        createResolves := createResolves_of_entryCheck hcc }⟩

end Lir
