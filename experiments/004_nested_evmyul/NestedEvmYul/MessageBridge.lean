import NestedEvmYul.ObservableTriple

/-!
# T4 — `MessageBridge`: the general X-to-`runΘ` bridge
# (flat `messageCall_runs` analog) + the derived fuel envelope

Closes parity-verdict gap #2 (docs/planning/exp004-parity-verdict-2026-07-19.md
§4): a general, reusable bridge from the `X`-level reasoning layer to the
top-level fuel-free `runΘ` over an ARBITRARY `NestedWorld` seeding — the
endgame's inline steps (2)–(4) (ObservableTriple.lean:352–396) hoisted into one
theorem — plus the strongest honest treatment of the `seedFuel` side condition,
including a fragment where it is **derived from gas**, not assumed.

## The shape, against flat

Flat's bridge (EVM/BytecodeLayer/Spec.lean:70, `messageCall_runs`):
`EntersAsCode p fr₀` + `Runs fr₀ last` + halt ⟹ `messageCall p = .ok …`,
with **no numeric side condition**. That unconditionality rests on two flat
facts: `drive` fuel-monotonicity is TRUE and never-OOF is unconditional.
Nested `Θ` fuel-monotonicity is REFUTED (the CREATE/CREATE2 `| _ =>` catch-all
absorbs an inner `Lambda` `OutOfFuel` into an ordinary result — keystone
post-mortem, ThetaRuns.lean:231), so the nested bridge takes cofinal `X`
families and carries the `≤ seedFuel w` envelope. This file states exactly
which half of the flat bridge needs the envelope and which does not:

* `ΘRuns_of_X_family` — the **veneer** conclusion needs NO envelope (pure
  cofinal introduction): the side condition is entirely a property of the
  *adequacy* step (pinning the seeded `runΘ`), not of the layer crossing.
* `runΘ_of_X_family` — the **driver** conclusion carries `m + 4 ≤ seedFuel w`,
  the honest residue of the cofinal pivot.

## The risky half: deriving the envelope ("gas pays for fuel")

For **call-free straight-line chains** the envelope is DERIVED, not assumed:
every gas-witnessed chain link (`IterStepG` — an `IterStepU` whose opcode is
runnable and outside the CREATE/CALL family, witnessed at the top level) burns
`≥ 1` gas (`Z`'s two ℕ-guards + `gas_EVM_step_default` + `C'_pos_of_runnable`),
so a length-`n` chain forces `n ≤ w.g.toNat`, and `seedFuel`'s one guaranteed
copy of `(g + fuelHops)` (`fuelBound_ge`) absorbs `n + 4` outright. Headline:
`completedWith_of_gasDerived` — a top-level observable conclusion with **no
numeric fuel hypothesis at all** (only the structural `w.e ≤ 1024` depth cap).

## Obstruction record: why the derivation stops at the call-free fragment

The general per-link decrement (`IterStepU → gas strictly drops`) and the
general envelope derivation both FAIL, for reasons worth pinning precisely:

* **(A) CREATE-absorption leak (per-link decrement, statement-level).** A
  CREATE/CREATE2 link CAN inhabit `IterStepU`: its `∀`-fuel `step` clause pins
  ONE successor at every fuel, which excludes any fuel-*sensitive* inner
  `Lambda` — but an *eternally-failing* create (inner `Λ` erring for a
  fuel-independent reason, or absorbed at every fuel) satisfies the clause via
  the same `| _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)`
  catch-all that refuted the keystone (Semantics.lean:286/:344). Proving even
  those links debit `≥ 1` requires crossing the arm's gas reconstitution
  `.ofNat (a − L a + g′.toNat)`, whose wrap-safety needs `g′ ≤ L a` — child
  gas *conservation*, i.e. a `Lambda`-level gas-mono induction. So the
  per-link lemma is NOT independent of the descent machinery, and `IterStepG`
  carries `¬ isCallCreate` as a premise instead of deriving it. (This is also
  the one spot where UInt256 wraparound re-enters: `Z`'s own guards compare in
  ℕ via `toNat` *before* subtracting, so the chain lemma is wrap-safe; the
  CREATE arm's `gasAvailable + g′` UInt256 addition is guarded only AFTER the
  addition.)
* **(B) CALL-family links are refutable but not worth refuting.** `call 0 =
  .error .OutOfFuel` propagates honestly through the CALL arms' do-bind, so
  the `f = 0` instance of a `∀`-fuel step clause can never be `.ok` — a
  CALL-family `IterStepU` link is uninhabited. Discharging that inside the
  gas lemma would cost a CALL-arm unfolding sweep for a case real programs
  never enter through this door: call sites enter as `X_call_iter`'s cofinal
  families, not as chain links.
* **(C) Call OFFSETS are the irreducible residue.** In a composed family the
  offset is `m = n₁ + n₂ + k₁ + k₂ + c`: gas pays for the chain lengths `nᵢ`
  (derived here), but the `kᵢ` are the CHILDREN's fuel budgets. Fuel ≠ gas
  across a descent: the child must fund its own loop AND per-depth hop
  overhead, summing to exactly `fuelBound`'s PRODUCT `(1025 − e)·(g +
  fuelHops)`. A linear-in-gas premise (e.g. `Σ` per-link costs `≤ w.g.toNat`)
  bounds `Σ nᵢ` but can never bound `Σ kᵢ` — collapsing the depth factor to
  something linear is precisely re-proving NeverOutOfFuel's stage-2 descent
  recurrence. So for decompositions WITH call sites, `m + 4 ≤ seedFuel w` is
  the honest interface: callers discharge it by `fuelBound` arithmetic on
  their concrete `kᵢ`, not by execution data. Combined with the keystone
  refutation, the envelope on the general bridge is **permanent**, and now
  for a *quantitative* reason (product vs sum), not only the qualitative
  absorption argument.

## What was NOT done

The optional refactor (endgame consuming `runΘ_of_X_family` in place of its
inline steps (2)–(4)) is skipped on import-direction friction: the bridge lives
downstream of ObservableTriple (it consumes `Xi_forward`/`Θ_code_forward`), so
the endgame cannot consume it without a module reshuffle; the statement freeze
on `nested_twoCall_completedWith` (T2 depends on it) makes tonight the wrong
night. Duplication is confined to ~20 proof lines and flagged by this note
(ObservableTriple.lean is deliberately untouched).
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM
open XLoop

/-! ## 1. The core bridge: steps (2)–(4) of the endgame, hoisted -/

/-- **The `Θ` family behind both bridge conclusions.** From a cofinal `X`
success family on the caller's entry state (`callerEntry`), produce the
cofinal `Θ` family at offset `m + 4` — one `Ξ`-unfold (`Xi_forward`, +1) and
one `Θ`-unfold (`Θ_code_forward`, +1, transfer preamble + non-firing rollback
arm `hne`) over the family's own `+2`. This is the layer-crossing plumbing of
the endgame (ObservableTriple.lean:377–395) with the world and result held
general. PROVED — pure instantiation + offset bookkeeping. -/
theorem Θ_family_of_X_family (w : NestedWorld) (cd : ByteArray) (m : ℕ)
    {sH : EVM.State} {out : ByteArray}
    (hc : w.c = .Code cd)
    (hX : ∀ f, X (f + m + 2) (D_J cd ⟨0⟩) (callerEntry w cd)
      = .ok (.success sH out))
    (hne : (sH.accountMap == (∅ : AccountMap)) = false) :
    ∀ f, Θ ((m + 4) + f) w.blobVersionedHashes w.createdAccounts
      w.genesisBlockHeader w.blocks w.σ w.σ₀ w.A w.s w.o w.r w.c w.g w.p w.v
      w.v' w.d w.e w.H w.w
      = .ok (sH.createdAccounts, sH.accountMap, sH.gasAvailable, sH.substate,
          true, out) := by
  intro f
  have hΞfam := Xi_forward m w.createdAccounts w.genesisBlockHeader w.blocks
    (thetaTransfer w.σ w.s w.r w.v) w.σ₀ w.g w.A
    { codeOwner := w.r, sender := w.o, gasPrice := w.p.toNat, calldata := w.d,
      source := w.s, weiValue := w.v', depth := w.e, perm := w.w, code := cd,
      header := w.H, blobVersionedHashes := w.blobVersionedHashes }
    sH out hX
  have hΘfam := Θ_code_forward m hΞfam hne
  rw [hc, show (m + 4) + f = f + m + 4 from by omega]
  exact hΘfam f

/-- **The core bridge** (flat `messageCall_runs` analog, driver half): for ANY
world `w` running code `cd`, a cofinal `X` success family on `callerEntry w cd`
whose offset fits the seeding envelope (`m + 4 ≤ seedFuel w` — the honest,
permanent residue of the cofinal pivot; see the module docstring) and whose
final map does not trip `Θ`'s degenerate empty-map rollback (`hne`) pins the
top-level fuel-free `runΘ`. This is EXACTLY steps (2)–(4) of the endgame proof,
now reusable over arbitrary seeding. PROVED sorry-free. -/
theorem runΘ_of_X_family (w : NestedWorld) (cd : ByteArray) (m : ℕ)
    {sH : EVM.State} {out : ByteArray}
    (hc : w.c = .Code cd)
    (hfuel : m + 4 ≤ seedFuel w)
    (hX : ∀ f, X (f + m + 2) (D_J cd ⟨0⟩) (callerEntry w cd)
      = .ok (.success sH out))
    (hne : (sH.accountMap == (∅ : AccountMap)) = false) :
    runΘ w = .ok (sH.createdAccounts, sH.accountMap, sH.gasAvailable,
      sH.substate, true, out) :=
  ΘRuns.runΘ_complete' w _ (m + 4) hfuel (Θ_family_of_X_family w cd m hc hX hne)

/-- **The unbounded sibling** (veneer half): the SAME family, WITHOUT the
envelope, concludes the fuel-free relational veneer `ΘRuns`. Pure cofinal
introduction — this pins precisely which half of flat's bridge needs no side
condition on the nested side: the layer crossing itself is envelope-free; only
*adequacy* (pinning the seeded driver, `runΘ_of_X_family` above) pays
`≤ seedFuel w`. PROVED sorry-free. -/
theorem ΘRuns_of_X_family (w : NestedWorld) (cd : ByteArray) (m : ℕ)
    {sH : EVM.State} {out : ByteArray}
    (hc : w.c = .Code cd)
    (hX : ∀ f, X (f + m + 2) (D_J cd ⟨0⟩) (callerEntry w cd)
      = .ok (.success sH out))
    (hne : (sH.accountMap == (∅ : AccountMap)) = false) :
    ΘRuns w (sH.createdAccounts, sH.accountMap, sH.gasAvailable, sH.substate,
      true, out) :=
  ⟨m + 4, Θ_family_of_X_family w cd m hc hX hne⟩

/-! ## 2. The program-level driver: decomposition in, `runΘ` out

The nested analog of flat `messageCall_runs` at the PROGRAM level: segment
data enters as chain values (`ItersN` + `IterHaltU` — the same kind of
hypotheses as flat's `Runs` argument), and the conclusion is the top-level
fuel-free driver equation, plus the observable corollary. -/

/-- **Decomposition driver.** An `ItersN` chain from the caller's entry state
into `sEnd` plus a halting link (`X_decompose`'s inputs, XLoop.lean:446), under
the envelope, yields the `runΘ` equation with the result read off the halt
state's fields. PROVED — `X_decompose` feeds the core bridge. -/
theorem runΘ_of_decomposition (w : NestedWorld) (cd : ByteArray) {n : ℕ}
    {sEnd sHalt : EVM.State} {out : ByteArray}
    (hc : w.c = .Code cd)
    (hchain : XLoop.ItersN (D_J cd ⟨0⟩) n (callerEntry w cd) sEnd)
    (hhalt : XLoop.IterHaltU (D_J cd ⟨0⟩) sEnd sHalt out)
    (hfuel : n + 4 ≤ seedFuel w)
    (hne : (sHalt.accountMap == (∅ : AccountMap)) = false) :
    runΘ w = .ok (sHalt.createdAccounts, sHalt.accountMap, sHalt.gasAvailable,
      sHalt.substate, true, out) :=
  runΘ_of_X_family w cd n hc hfuel (XLoop.X_decompose hchain hhalt) hne

/-- **Observable corollary of the decomposition driver** — the program-level
flat-parity statement: chain data in, `completedWith` of the caller's
observable out, with the storage read taken at the halt state's post-map.
PROVED — the two projection lemmas over `runΘ_of_decomposition`. -/
theorem completedWith_of_decomposition (w : NestedWorld) (cd : ByteArray)
    {n : ℕ} {sEnd sHalt : EVM.State} {out : ByteArray} (addr key v : Nat)
    (hc : w.c = .Code cd)
    (hchain : XLoop.ItersN (D_J cd ⟨0⟩) n (callerEntry w cd) sEnd)
    (hhalt : XLoop.IterHaltU (D_J cd ⟨0⟩) sEnd sHalt out)
    (hfuel : n + 4 ≤ seedFuel w)
    (hne : (sHalt.accountMap == (∅ : AccountMap)) = false)
    (hread : (match sHalt.accountMap.toList.find? (fun p => p.1.val = addr) with
              | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
              | none => 0) = v) :
    completedWith (observe_nested (runΘ w)) addr key v := by
  have hrun := runΘ_of_decomposition w cd hc hchain hhalt hfuel hne
  exact ⟨observe_ok_tag w hrun,
    (observe_storageAt w addr key hrun).trans hread⟩

/-! ## 3. Gas pays for fuel: the derived envelope (call-free fragment)

The strongest weakening of the `≤ seedFuel w` side condition that survives the
obstructions in the module docstring: for chains whose links are gas-witnessed
(`IterStepG` below), the envelope is DERIVED from execution — each link burns
`≥ 1` gas, so the chain length is bounded by the world's own gas, which
`seedFuel` dominates linearly. -/

/-- Exact ℕ-value of a guarded UInt256 gas debit: `(g − .ofNat m).toNat =
g.toNat − m` when `m ≤ g.toNat` (no wrap; `m < size` follows). The `=`-sibling
of `GasArith.gas_sub_le`, same Fin-arithmetic script. -/
private theorem gas_sub_toNat (g : UInt256) (m : ℕ) (hle : m ≤ g.toNat) :
    (g - UInt256.ofNat m).toNat = g.toNat - m := by
  have htn : g.toNat = g.val.val := rfl
  have hgsz : g.val.val < UInt256.size := g.val.isLt
  have hm : m < UInt256.size := by rw [htn] at hle; omega
  have hcmod : (Fin.ofNat UInt256.size m).val = m := by
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hm
  show ((g.val - (Fin.ofNat _ m))).val = g.val.val - m
  rw [Fin.sub_def, hcmod]
  show (UInt256.size - m + g.val.val) % UInt256.size = g.val.val - m
  have hle' : m ≤ g.val.val := by rw [← htn]; exact hle
  have hrw : UInt256.size - m + g.val.val = (g.val.val - m) + UInt256.size := by
    omega
  rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
/-- **`Z` gas inversion.** A successful gate returns the post-memory-debit
state with (i) the cost pinned to `C'` at that state, (ii) the cost covered by
the remaining gas (`Z`'s second guard), and (iii) gas not increased (`Z`'s
first guard makes the memory debit wrap-free). All three comparisons run in ℕ
via `toNat` — this is why the chain-gas lemma below is UInt256-wrap-safe with
no extra hypotheses. Same inversion recipe (and heartbeat crank, hence the
`set_option`) as `XLoop.Z_ok_toState`. -/
theorem Z_ok_gas {vj : Array UInt256} {op : Operation} {s s' : EVM.State}
    {c : ℕ} (h : Z vj op s = .ok (s', c)) :
    c = C' s' op ∧ c ≤ s'.gasAvailable.toNat ∧
      s'.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  unfold Z at h
  simp only [pure, Except.pure, bind, Except.bind] at h
  generalize hm : memoryExpansionCost s op = m₁ at h
  by_cases hg1 : s.gasAvailable.toNat < m₁
  · rw [if_pos hg1] at h; exact absurd h (by simp)
  · rw [if_neg hg1] at h
    generalize hcc :
      C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ } op = c₂ at h
    by_cases hg2 : ({ s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ }
        : EVM.State).gasAvailable.toNat < c₂
    · rw [if_pos hg2] at h; exact absurd h (by simp)
    · rw [if_neg hg2] at h
      have hpc : s' = { s with gasAvailable := s.gasAvailable - UInt256.ofNat m₁ }
          ∧ c = c₂ := by
        revert h
        split_ifs <;> intro h <;>
          first
          | (have hp := Except.ok.inj h; rw [Prod.mk.injEq] at hp
             exact ⟨hp.1.symm, hp.2.symm⟩)
          | exact absurd h (by simp)
      obtain ⟨hs', hc'⟩ := hpc
      subst hs'; subst hc'
      refine ⟨hcc.symm, Nat.le_of_not_lt hg2, ?_⟩
      show (s.gasAvailable - UInt256.ofNat m₁).toNat ≤ s.gasAvailable.toNat
      exact NeverOutOfFuel.gas_sub_le s.gasAvailable m₁ (Nat.le_of_not_lt hg1)
        (Nat.lt_of_le_of_lt (Nat.le_of_not_lt hg1) s.gasAvailable.val.isLt)

/-- A **gas-witnessed** straight-line link: an `IterStepU` whose opcode is
additionally witnessed (at the top level, where the gas derivation can see it)
to be `runnable` (so `C' ≥ 1`, `C'_pos_of_runnable`) and outside the
CREATE/CALL family (so `step` debits exactly the gate cost,
`gas_EVM_step_default`). The two extra conjuncts are `decide`-discharged by
every concrete intro rule below; they cannot be *derived* from `IterStepU` —
obstruction items (A)/(B) in the module docstring. -/
def IterStepG (vj : Array UInt256) (s s' : EVM.State) : Prop :=
  ∃ (cost : ℕ) (op : Operation) (arg : Option (UInt256 × Nat)) (s₁ : EVM.State),
    (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (op, arg) ∧
    NeverOutOfFuel.runnable op ∧
    ¬ NeverOutOfFuel.isCallCreate op ∧
    Z vj op s = .ok (s₁, cost) ∧
    (∀ f, EVM.step (f+1) cost (some (op, arg)) s₁ = .ok s') ∧
    H s'.toMachineState op = none

/-- Forgetful map: every gas-witnessed link is a plain link, so `ItersG` chains
plug into the whole existing `ItersN` pipeline. -/
theorem IterStepG.toU {vj : Array UInt256} {s s' : EVM.State}
    (h : IterStepG vj s s') : XLoop.IterStepU vj s s' := by
  obtain ⟨cost, op, arg, s₁, h1, _, _, h4, h5, h6⟩ := h
  exact ⟨cost, op, arg, s₁, h1, h4, h5, h6⟩

/-- **Per-link gas decrement** — the "gas pays for fuel" cornerstone: every
gas-witnessed link strictly burns gas. `Z`'s guards give the wrap-free debit
frame, `gas_EVM_step_default` gives the exact step debit, and
`C'_pos_of_runnable` makes it strict. PROVED with no fuel-side hypotheses. -/
theorem IterStepG.gas_lt {vj : Array UInt256} {s s' : EVM.State}
    (h : IterStepG vj s s') :
    s'.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat := by
  obtain ⟨cost, op, arg, s₁, _hdec, hrun, hncc, hZ, hstep, _hH⟩ := h
  obtain ⟨hcost, hle, hmono⟩ := Z_ok_gas hZ
  have hpos : 1 ≤ cost := by
    rw [hcost]; exact NeverOutOfFuel.C'_pos_of_runnable s₁ op hrun
  have hdeb := NeverOutOfFuel.gas_EVM_step_default 0 cost op arg s₁ s' hncc
    (hstep 0)
  have hfin : s'.gasAvailable.toNat = s₁.gasAvailable.toNat - cost := by
    rw [hdeb]; exact gas_sub_toNat _ _ hle
  omega

/-! ### Gas-witnessed intro rules

The six straight-line rules of `XLoop`, re-packaged with the two decidable
witnesses. Bodies are verbatim copies of the `IterStepU.*` rules. -/

theorem IterStepG.push1 {vj : Array UInt256} {s s₁ : EVM.State}
    {v : UInt256} {n cost : ℕ}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none)
      = (.PUSH1, some (v, n)))
    (hZ : Z vj .PUSH1 s = .ok (s₁, cost)) :
    IterStepG vj s
      ((debit s₁ cost).replaceStackAndIncrPC ((debit s₁ cost).stack.push v)
        (pcΔ := n+1)) :=
  ⟨cost, _, _, s₁, hdec,
    by unfold NeverOutOfFuel.runnable; decide,
    by unfold NeverOutOfFuel.isCallCreate; decide, hZ,
    fun f => (step_eq_shared_push1 f cost _ s₁).trans (shared_step_push1 v n _),
    rfl⟩

theorem IterStepG.push0 {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.PUSH0, arg))
    (hZ : Z vj .PUSH0 s = .ok (s₁, cost)) :
    IterStepG vj s
      ((debit s₁ cost).replaceStackAndIncrPC ((debit s₁ cost).stack.push ⟨0⟩)) :=
  ⟨cost, _, _, s₁, hdec,
    by unfold NeverOutOfFuel.runnable; decide,
    by unfold NeverOutOfFuel.isCallCreate; decide, hZ,
    fun f => (step_eq_shared_push0 f cost arg s₁).trans (shared_step_push0 arg _),
    rfl⟩

theorem IterStepG.sstore {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {key val : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.SSTORE, arg))
    (hZ : Z vj .SSTORE s = .ok (s₁, cost))
    (hstk : s₁.stack = key :: val :: rest) :
    IterStepG vj s
      ({ debit s₁ cost with
          toState := s₁.toState.sstore key val }.replaceStackAndIncrPC rest) :=
  ⟨cost, _, _, s₁, hdec,
    by unfold NeverOutOfFuel.runnable; decide,
    by unfold NeverOutOfFuel.isCallCreate; decide, hZ,
    fun f => (step_eq_shared_sstore f cost arg s₁).trans
      (shared_step_sstore arg (debit s₁ cost) key val rest hstk), rfl⟩

theorem IterStepG.jump {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {dest : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMP, arg))
    (hZ : Z vj .JUMP s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: rest) :
    IterStepG vj s { debit s₁ cost with pc := dest, stack := rest } :=
  ⟨cost, _, _, s₁, hdec,
    by unfold NeverOutOfFuel.runnable; decide,
    by unfold NeverOutOfFuel.isCallCreate; decide, hZ,
    fun f => (step_eq_shared_jump f cost arg s₁).trans
      (shared_step_jump arg (debit s₁ cost) dest rest hstk), rfl⟩

theorem IterStepG.jumpi_taken {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {dest cond : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: cond :: rest)
    (hcond : cond ≠ ⟨0⟩) :
    IterStepG vj s { debit s₁ cost with pc := dest, stack := rest } :=
  ⟨cost, _, _, s₁, hdec,
    by unfold NeverOutOfFuel.runnable; decide,
    by unfold NeverOutOfFuel.isCallCreate; decide, hZ,
    fun f => (step_eq_shared_jumpi f cost arg s₁).trans
      (shared_step_jumpi_taken arg (debit s₁ cost) dest cond rest hstk hcond),
    rfl⟩

theorem IterStepG.jumpi_fallthrough {vj : Array UInt256} {s s₁ : EVM.State}
    {arg : Option (UInt256 × Nat)} {cost : ℕ}
    {dest : UInt256} {rest : Stack UInt256}
    (hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.JUMPI, arg))
    (hZ : Z vj .JUMPI s = .ok (s₁, cost))
    (hstk : s₁.stack = dest :: (⟨0⟩ : UInt256) :: rest) :
    IterStepG vj s
      { debit s₁ cost with pc := (debit s₁ cost).pc + ⟨1⟩, stack := rest } :=
  ⟨cost, _, _, s₁, hdec,
    by unfold NeverOutOfFuel.runnable; decide,
    by unfold NeverOutOfFuel.isCallCreate; decide, hZ,
    fun f => (step_eq_shared_jumpi f cost arg s₁).trans
      (shared_step_jumpi_fallthrough arg (debit s₁ cost) dest rest hstk), rfl⟩

/-- Length-indexed gas-witnessed chains (refl + tail), mirroring `ItersN`. -/
inductive ItersG (vj : Array UInt256) : ℕ → EVM.State → EVM.State → Prop
  | refl (s : EVM.State) : ItersG vj 0 s s
  | tail {n : ℕ} {s s' s'' : EVM.State} :
      ItersG vj n s s' → IterStepG vj s' s'' → ItersG vj (n+1) s s''

/-- A single gas-witnessed link is a length-1 chain. -/
theorem ItersG.single {vj : Array UInt256} {s s' : EVM.State}
    (h : IterStepG vj s s') : ItersG vj 1 s s' :=
  (ItersG.refl s).tail h

/-- Gas-witnessed chains concatenate (lengths add). -/
theorem ItersG.trans {vj : Array UInt256} {m n : ℕ} {s s' s'' : EVM.State}
    (h₁ : ItersG vj m s s') (h₂ : ItersG vj n s' s'') :
    ItersG vj (m + n) s s'' := by
  induction h₂ with
  | refl _ => exact h₁
  | tail hc hstep ih => exact (ih h₁).tail hstep

/-- Forgetful map to `ItersN`: the whole existing decomposition pipeline
(`ItersN_X`, `X_decompose`, `runΘ_of_decomposition`) consumes `ItersG` chains
through this. -/
theorem ItersG.toN {vj : Array UInt256} {n : ℕ} {s s' : EVM.State}
    (h : ItersG vj n s s') : XLoop.ItersN vj n s s' := by
  induction h with
  | refl s => exact .refl s
  | tail _ hstep ih => exact ih.tail hstep.toU

/-- **Gas pays for chain length**: a length-`n` gas-witnessed chain burns at
least `n` gas — pure induction over the per-link decrement. -/
theorem ItersG.gas_le {vj : Array UInt256} {n : ℕ} {s s' : EVM.State}
    (h : ItersG vj n s s') :
    s'.gasAvailable.toNat + n ≤ s.gasAvailable.toNat := by
  induction h with
  | refl s => omega
  | tail _ hstep ih => have := hstep.gas_lt; omega

/-- `seedFuel` dominates the world's gas linearly: the depth factor
`(1025 − e) ≥ 1` guarantees one full copy of `(g + fuelHops)` inside
`fuelBound` (`fuelBound_ge`), plus the seeding's `+3`. The arithmetic that
turns a gas-side bound into the envelope. -/
theorem seedFuel_ge_gas (w : NestedWorld) (he : w.e ≤ 1024) :
    w.g.toNat + 11 ≤ seedFuel w := by
  have hb := NeverOutOfFuel.fuelBound_ge w.g.toNat w.e he
  have hfh : NeverOutOfFuel.fuelHops = 8 := rfl
  unfold seedFuel
  omega

/-- **The derived envelope** — the strongest weakening achieved: for a
gas-witnessed (call-free) decomposition, the `n + 4 ≤ seedFuel w` side
condition is DERIVED from execution — the chain's own gas burn bounds its
length by `w.g.toNat` (`ItersG.gas_le` at the entry state, whose gas is `w.g`
by construction of `callerEntry`), and `seedFuel` dominates gas
(`seedFuel_ge_gas`). Only the structural depth cap `w.e ≤ 1024` remains — no
numeric fuel hypothesis. PROVED sorry-free. -/
theorem runΘ_of_decomposition_gasDerived (w : NestedWorld) (cd : ByteArray)
    {n : ℕ} {sEnd sHalt : EVM.State} {out : ByteArray}
    (hc : w.c = .Code cd) (he : w.e ≤ 1024)
    (hchain : ItersG (D_J cd ⟨0⟩) n (callerEntry w cd) sEnd)
    (hhalt : XLoop.IterHaltU (D_J cd ⟨0⟩) sEnd sHalt out)
    (hne : (sHalt.accountMap == (∅ : AccountMap)) = false) :
    runΘ w = .ok (sHalt.createdAccounts, sHalt.accountMap, sHalt.gasAvailable,
      sHalt.substate, true, out) := by
  have hgas := hchain.gas_le
  rw [show (callerEntry w cd).gasAvailable = w.g from rfl] at hgas
  have hsf := seedFuel_ge_gas w he
  exact runΘ_of_decomposition w cd hc hchain.toN hhalt (by omega) hne

/-- **Envelope-free observable headline**: a gas-witnessed decomposition yields
the caller's `completedWith` observable with NO numeric fuel side condition
anywhere — the closest the nested side can come to flat
`messageCall_runs`-style unconditionality, and (per obstruction item (C)) the
exact boundary of that possibility: one call site in the chain re-introduces
the child's fuel budget, which no linear-in-gas premise can bound. -/
theorem completedWith_of_gasDerived (w : NestedWorld) (cd : ByteArray)
    {n : ℕ} {sEnd sHalt : EVM.State} {out : ByteArray} (addr key v : Nat)
    (hc : w.c = .Code cd) (he : w.e ≤ 1024)
    (hchain : ItersG (D_J cd ⟨0⟩) n (callerEntry w cd) sEnd)
    (hhalt : XLoop.IterHaltU (D_J cd ⟨0⟩) sEnd sHalt out)
    (hne : (sHalt.accountMap == (∅ : AccountMap)) = false)
    (hread : (match sHalt.accountMap.toList.find? (fun p => p.1.val = addr) with
              | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
              | none => 0) = v) :
    completedWith (observe_nested (runΘ w)) addr key v := by
  have hrun := runΘ_of_decomposition_gasDerived w cd hc he hchain hhalt hne
  exact ⟨observe_ok_tag w hrun,
    (observe_storageAt w addr key hrun).trans hread⟩

end NestedEvmYul
