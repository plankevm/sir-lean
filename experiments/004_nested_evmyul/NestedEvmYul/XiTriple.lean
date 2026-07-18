import EvmYul.EVM.Semantics
import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement

/-!
# T2 — `XiTriple`/`ThetaTriple`: a Hoare-style procedure-call surface over the
# nested `Ξ`/`Θ` (the never-built B3 data point, PLAN.md:43-45)

**THIS FILE IS A LABELED EXPLORATORY SHAPE STUDY, NOT A FOUNDATION TO BUILD ON.**
It deliberately suspends the house proof-first/no-sorry rule, for the sole
purpose of measuring whether a Hoare-style procedure-call surface over the
nested `Ξ`/`Θ` is ergonomic.

Ground rules (per the track spec, verbatim): statements first; prove only the
genuinely easy ones (conseq, conj, frame, preservesAccount_stop,
twoCall_spec-given-call_spec); explicitly-classified sorry placeholders
(`-- SORRY-CLASS: easy|medium|hard — <reason>`) for theta_of_xi and call_spec;
LABELED EXPLORATORY ARTIFACT, not a foundation; `lake build` green after the
track.

OUTCOME NOTE (upgrades the plan, honestly): the two SORRY-CLASS-medium
candidates — `theta_of_xi` and `call_spec` — both went through with the
`call_result_gas_le` inversion recipe (`simp only [·, bind, Except.bind]` +
`split at` + ctor injection; the do-block matchers never touch `step`'s
140-arm match), so this file ships with ZERO sorries. The medium-class label
was priced for the σ₁/rollback bookkeeping; the recipe absorbed it.

## The central design move: ∀-fuel triples are fuel-free FOR FREE

`XiTriple`/`ThetaTriple` below quantify over **all** fuels. A triple is a
statement about *every* fueled run that succeeds, so it never has to transport
a result from one fuel to another: two triples compose by feeding the very same
fuel of the outer run into the inner hypothesis. Contrast the study's
**existential** encoding (now quarantined as `ΘRunsE`, ThetaRuns.lean's
`DeprecatedFuelExistential` section): there, gluing two `∃ fuel` witnesses
forces both runs to a common fuel, which needs the fuel-irrelevance keystone
(`Θ_fuel_mono_ok` — an unproved 6-layer mutual induction; the surviving
`ΘRuns` is offset-cofinal and keystone-free, T2 pivot). Universal-fuel
quantification is antitone-friendly — weakening to a specific fuel is just
instantiation — so the entire logical-rule layer (conseq/conj/frame) and the
call-site composition come out keystone-free. This is the cheap trick the
nested shape affords, and the flat side neither has nor needs (one interpreter,
one drive, no fuel in sight at the spec level).

The price (recorded honestly below at `twoCall_spec`): the triples only ever
*consume* success runs. Producing one — or discharging a `PreservesAccount`
footprint, or supplying the state between two calls — needs an execution logic
for the `X` loop that the nested side does not have.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## The triples -/

/-- **`XiTriple P I Q`** — success-only partial-correctness triple over the
code-execution function `Ξ`, quantified over **all** fuels (and all ambient
run arguments). Revert / semantic-error / OutOfFuel outcomes are vacuous:
the triple constrains only `.ok (.success r o)` runs.

`r : createdAccounts × σ' × g' × A'`, so `r.2.1` is the post-map and `r.2.2.2`
the post-substate. WHY fuel-free with no keystone: the `∀ fuel` makes the
triple a statement about every fueled run simultaneously, so composing triples
never moves a result across fuels — the antitone/instantiation direction is
free, unlike the quarantined existential `ΘRunsE` whose every cross-fuel lemma
funnels through the unproved `Θ_fuel_mono_ok` mutual induction (ThetaRuns.lean,
`DeprecatedFuelExistential`). -/
def XiTriple (P : AccountMap → Substate → Prop) (I : ExecutionEnv)
    (Q : AccountMap → Substate → ByteArray → Prop) : Prop :=
  ∀ (fuel : ℕ) (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (r : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)
    (o : ByteArray),
    P σ A →
    Ξ fuel cA gh blocks σ σ₀ g A I = .ok (.success r o) →
    Q r.2.1 r.2.2.2 o

/-- **`ThetaTriple P c Q`** — the procedure spec: success-only (`z = true`)
partial correctness of a message call executing callee code `c`, over all
fuels and all ambient arguments.

DESIGN DECISION (flagged): `P` is over the **PRE-transfer** `σ` — the map as
the caller hands it to `Θ`, *before* Θ's balance-transfer preamble
(`σ ↦ σ₁` via `find?`/`insert`). This makes the call-site rule (`call_spec`)
read off the caller state directly, at the cost of a fiddlier `theta_of_xi`
(the Θ-inversion has to push `P` through the transfer). A post-transfer-`σ₁`
variant would shrink the Θ-inversion proof but shift the transfer bookkeeping
onto every call site. -/
def ThetaTriple (P : AccountMap → Substate → Prop) (c : ToExecute)
    (Q : AccountMap → Substate → ByteArray → Prop) : Prop :=
  ∀ (fuel : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ)
    (Hd : BlockHeader) (w : Bool)
    (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (g' : UInt256)
    (A' : Substate) (z : Bool) (out : ByteArray),
    P σ A →
    Θ fuel bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w
      = .ok (cA', σ', g', A', z, out) →
    z = true →
    Q σ' A' out

/-! ## Logical rules — free (pure logic; the semantics is never touched) -/

/-- Consequence rule for `XiTriple`. PROVED — pure logic. -/
theorem XiTriple.conseq {P P' : AccountMap → Substate → Prop} {I : ExecutionEnv}
    {Q Q' : AccountMap → Substate → ByteArray → Prop}
    (hP : ∀ σ A, P' σ A → P σ A) (hQ : ∀ σ A o, Q σ A o → Q' σ A o)
    (h : XiTriple P I Q) : XiTriple P' I Q' :=
  fun fuel cA gh blocks σ σ₀ g A r o hpre hrun =>
    hQ _ _ _ (h fuel cA gh blocks σ σ₀ g A r o (hP _ _ hpre) hrun)

/-- Consequence rule for `ThetaTriple`. PROVED — pure logic. -/
theorem ThetaTriple.conseq {P P' : AccountMap → Substate → Prop} {c : ToExecute}
    {Q Q' : AccountMap → Substate → ByteArray → Prop}
    (hP : ∀ σ A, P' σ A → P σ A) (hQ : ∀ σ A o, Q σ A o → Q' σ A o)
    (h : ThetaTriple P c Q) : ThetaTriple P' c Q' :=
  fun fuel bvh cA gh blocks σ σ₀ A s o r g p v v' d e Hd w cA' σ' g' A' z out
      hpre hrun hz =>
    hQ _ _ _ (h fuel bvh cA gh blocks σ σ₀ A s o r g p v v' d e Hd w
      cA' σ' g' A' z out (hP _ _ hpre) hrun hz)

/-- Conjunction rule for `XiTriple`. PROVED — pure logic (feed the SAME fueled
run into both triples; no fuel-irrelevance needed, unlike the existential
encoding where two `∃ fuel` witnesses must first be reconciled). -/
theorem XiTriple.conj {P P' : AccountMap → Substate → Prop} {I : ExecutionEnv}
    {Q Q' : AccountMap → Substate → ByteArray → Prop}
    (h : XiTriple P I Q) (h' : XiTriple P' I Q') :
    XiTriple (fun σ A => P σ A ∧ P' σ A) I
      (fun σ A o => Q σ A o ∧ Q' σ A o) :=
  fun fuel cA gh blocks σ σ₀ g A r o hpre hrun =>
    ⟨h fuel cA gh blocks σ σ₀ g A r o hpre.1 hrun,
     h' fuel cA gh blocks σ σ₀ g A r o hpre.2 hrun⟩

/-- Conjunction rule for `ThetaTriple`. PROVED — pure logic. -/
theorem ThetaTriple.conj {P P' : AccountMap → Substate → Prop} {c : ToExecute}
    {Q Q' : AccountMap → Substate → ByteArray → Prop}
    (h : ThetaTriple P c Q) (h' : ThetaTriple P' c Q') :
    ThetaTriple (fun σ A => P σ A ∧ P' σ A) c
      (fun σ A o => Q σ A o ∧ Q' σ A o) :=
  fun fuel bvh cA gh blocks σ σ₀ A s o r g p v v' d e Hd w cA' σ' g' A' z out
      hpre hrun hz =>
    ⟨h fuel bvh cA gh blocks σ σ₀ A s o r g p v v' d e Hd w cA' σ' g' A' z out
        hpre.1 hrun hz,
     h' fuel bvh cA gh blocks σ σ₀ A s o r g p v v' d e Hd w cA' σ' g' A' z out
        hpre.2 hrun hz⟩

/-! ## Semantic framing -/

/-- **`PreservesAccount I a`** — a SEMANTIC footprint predicate: every
successful `Ξ`-run of code `I` leaves account `a`'s map entry untouched.
Definable without any opcode sweep — no syntactic "writes-footprint" analysis
of `I.code` is needed to even *state* framing. -/
def PreservesAccount (I : ExecutionEnv) (a : AccountAddress) : Prop :=
  ∀ (fuel : ℕ) (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (r : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)
    (o : ByteArray),
    Ξ fuel cA gh blocks σ σ₀ g A I = .ok (.success r o) →
    r.2.1.find? a = σ.find? a

/-- **Semantic frame rule.** PROVED — definition-chasing: once framing is a
semantic predicate on runs, the frame rule itself is trivial (conjoin, thread
the preservation equation through). HONEST CAVEAT (the real finding):
discharging `PreservesAccount` for real code is the hard part — it is
per-program `Ξ`-reasoning, i.e. exactly the missing X-loop program logic.
"Frame rule by construction" earns its keep only if footprints come from
somewhere (a static writes-analysis + soundness proof, or per-opcode
preservation rules); the rule itself was never the cost. -/
theorem XiTriple.frame {P : AccountMap → Substate → Prop} {I : ExecutionEnv}
    {Q : AccountMap → Substate → ByteArray → Prop} {a : AccountAddress}
    {acct : Option Account}
    (hpres : PreservesAccount I a) (h : XiTriple P I Q) :
    XiTriple (fun σ A => P σ A ∧ σ.find? a = acct) I
      (fun σ' A' o => Q σ' A' o ∧ σ'.find? a = acct) :=
  fun fuel cA gh blocks σ σ₀ g A r o hpre hrun =>
    ⟨h fuel cA gh blocks σ σ₀ g A r o hpre.1 hrun,
     (hpres fuel cA gh blocks σ σ₀ g A r o hrun).trans hpre.2⟩

/-! ### Non-vacuity witness for `PreservesAccount`: the single-`STOP` program

`Refinement.Xi_stop` gives the success shape at fuel `f+3`; fuels `0/1/2`
end in `.error .OutOfFuel` and are vacuous. The two small-fuel evaluation
lemmas below close those arms. -/

/-- `Ξ` at fuel `1` dies in `X 0`. (`rfl`-provable: the mutual block reduces
definitionally on literal fuel, cf. `NeverOutOfFuel.Ξ_zero`.) -/
theorem Xi_one {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {blocks : ProcessedBlocks} {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} :
    Ξ 1 cA gh blocks σ σ₀ g A I = .error .OutOfFuel := rfl

/-- One STOP-decode iteration at `X`-fuel `1`: decode → gate pass → `step 0`
dies. Mirrors `Refinement.X_stop` with the step-fuel at its floor. -/
theorem X_one_stop (vj : Array UInt256) (s : EVM.State)
    (hcode : s.executionEnv.code = ⟨#[0x00]⟩) (hpc : s.pc = ⟨0⟩)
    (hstk : s.stack = []) :
    X 1 vj s = .error .OutOfFuel := by
  unfold X
  simp only [hcode, hpc, decode_stop, Option.getD]
  rw [Z_stop vj s hstk]
  simp only [bind, Except.bind, NeverOutOfFuel.step_zero]

/-- `Ξ` at fuel `2` on single-`STOP` code dies in `step 0`. -/
theorem Xi_two_stop {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {blocks : ProcessedBlocks} {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} (hcode : I.code = ⟨#[0x00]⟩) :
    Ξ 2 cA gh blocks σ σ₀ g A I = .error .OutOfFuel := by
  rw [Ξ]
  simp only [bind, Except.bind]
  have hXfail := X_one_stop (D_J I.code ⟨0⟩)
    { (default : EVM.State) with
        accountMap := σ, σ₀ := σ₀, substate := A, executionEnv := I,
        blocks := blocks, genesisBlockHeader := gh, createdAccounts := cA,
        gasAvailable := g } hcode rfl rfl
  simp only [] at hXfail
  rw [hXfail]

/-- **Non-vacuity witness for the frame machinery.** PROVED — the single-`STOP`
program preserves EVERY account: fuels `0/1/2` are vacuous (OutOfFuel), and at
`f+3` the closed `Refinement.Xi_stop` returns the entry `σ` verbatim. -/
theorem preservesAccount_stop (I : ExecutionEnv) (a : AccountAddress)
    (hcode : I.code = ⟨#[0x00]⟩) : PreservesAccount I a := by
  intro fuel cA gh blocks σ σ₀ g A r o hΞ
  rcases fuel with _ | (_ | (_ | f))
  · rw [NeverOutOfFuel.Ξ_zero] at hΞ
    exact Except.noConfusion hΞ
  · have hΞ' : Ξ 1 cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [Xi_one] at hΞ'
    exact Except.noConfusion hΞ'
  · have hΞ' : Ξ 2 cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [Xi_two_stop hcode] at hΞ'
    exact Except.noConfusion hΞ'
  · obtain ⟨g', hstop⟩ := Xi_stop f cA gh blocks σ σ₀ g A I hcode
    have hΞ' : Ξ (f + 3) cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [hstop] at hΞ'
    injection hΞ' with hres
    injection hres with h1 h2
    rw [← h1]

/-! ## From code triples to procedure triples: absorbing Θ's preamble -/

/-- Θ's balance-transfer preamble, verbatim (`σ ↦ σ₁`, eqns 124–126):
credit the recipient `r` with `v` (creating the account when `v ≠ 0`),
then debit the sender `s`. -/
def thetaTransfer (σ : AccountMap) (s r : AccountAddress) (v : UInt256) :
    AccountMap :=
  let σ'₁ :=
    match σ.find? r with
      | none =>
        if v != ⟨0⟩ then σ.insert r { (default : Account) with balance := v }
        else σ
      | some acc => σ.insert r { acc with balance := acc.balance + v }
  match σ'₁.find? s with
    | none => σ'₁
    | some acc => σ'₁.insert s { acc with balance := acc.balance - v }

/-- **Procedure-spec introduction** (`Θ`'s `.Code cd` arm): an `XiTriple` for
the callee code — uniformly in the execution env Θ builds (only `I.code = cd`
is pinned; the rest of `I` varies with the ambient Θ arguments) — yields a
`ThetaTriple`, provided the caller-side predicates absorb

* the balance-transfer preamble (`habsorb`: `Pξ` holds at `thetaTransfer σ s r v`
  whenever `P` holds at the pre-transfer `σ`), and
* the `σ'' == ∅` rollback postprocessing (`hroll`: Θ eqns 127/129 collapse an
  empty-map `Ξ` result back to the ENTRY `σ`/`A`, so `Q` must transfer from the
  degenerate `Ξ` result to the entry state).

The `z = true` hypothesis of `ThetaTriple` forces the `Ξ`-success arm (revert
and semantic error both set `z = false`; OutOfFuel is thrown). -/
theorem theta_of_xi
    (P Pξ : AccountMap → Substate → Prop)
    (Q : AccountMap → Substate → ByteArray → Prop) (cd : ByteArray)
    (hΞ : ∀ I : ExecutionEnv, I.code = cd → XiTriple Pξ I Q)
    (habsorb : ∀ σ A s r v, P σ A → Pξ (thetaTransfer σ s r v) A)
    (hroll : ∀ (σ : AccountMap) (A : Substate) (σ'' : AccountMap) (A'' : Substate)
      (o : ByteArray), P σ A → (σ'' == (∅ : AccountMap)) = true →
      Q σ'' A'' o → Q σ A o) :
    ThetaTriple P (.Code cd) Q := by
  intro fuel bvh cA gh blocks σ σ₀ A s o r g p v v' d e Hd w cA' σ' g' A' z out
    hP hrun hz
  subst hz
  obtain _ | f := fuel
  · rw [NeverOutOfFuel.Θ_zero] at hrun
    exact Except.noConfusion hrun
  · simp only [Θ, bind, Except.bind] at hrun
    -- The pre-order first split candidate is the match on the `Ξ` result
    -- (the transfer matches sit deeper, inside `Ξ`'s `σ₁` argument, and are
    -- generalized away untouched — keeping `thetaTransfer` defeq applicable).
    split at hrun
    · -- `Ξ = .error e`: either rethrown OutOfFuel or a `z = false` package
      split at hrun
      · exact Except.noConfusion hrun
      · have hinj := Except.ok.inj hrun
        rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq,
            Prod.mk.injEq] at hinj
        exact Bool.noConfusion (show false = true from hinj.2.2.2.2.1)
    · -- `Ξ = .ok (.revert g' o)`: also a `z = false` package
      have hinj := Except.ok.inj hrun
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq,
          Prod.mk.injEq] at hinj
      exact Bool.noConfusion (show false = true from hinj.2.2.2.2.1)
    · -- `Ξ = .ok (.success (a, b, c, d) o)`: the genuine success path
      rename_i aa bb cc dd oo hΞeq
      have hQb := hΞ _ rfl _ _ _ _ (thetaTransfer σ s r v) _ _ _
        ⟨aa, bb, cc, dd⟩ oo (habsorb σ A s r v hP) hΞeq
      have hinj := Except.ok.inj hrun
      rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq,
          Prod.mk.injEq] at hinj
      obtain ⟨-, hσ, -, hA, -, hout⟩ := hinj
      rw [← hσ, ← hA, ← hout]
      by_cases hb : (bb == (∅ : AccountMap)) = true
      · rw [if_pos hb, if_pos hb]
        exact hroll σ A bb dd oo hP hb hQb
      · rw [if_neg hb, if_neg hb]
        exact hQb

/-! ## The call-site rule -/

/-- The substate `call` hands to `Θ`: the callee address is charged as an
accessed account (the gas debit on the machine state does not touch the
substate). -/
def callAccessSubstate (ev : EVM.State) (t : UInt256) : Substate :=
  ev.substate.addAccessedAccount (AccountAddress.ofUInt256 t)

set_option maxHeartbeats 2000000 in
/-- **The call-site rule**: a `ThetaTriple` for the resolved callee
(`toExecute ev.accountMap t'`, `t' = AccountAddress.ofUInt256 t`) folds into
the parent `call` result. KEY shape fact exploited: `x = ⟨1⟩` forces `z = true`
AND forces the covered Θ-branch (the else branch hardwires `z = false`, which
makes `x = ⟨0⟩`) — so NO balance/depth side conditions appear in the rule.
The result state literally sets `accountMap := σ'`, `substate := A'`,
`returnData := o`, so the callee's postcondition lands verbatim on the
caller-visible state. Inversion recipe mirrors the proved
`NeverOutOfFuel.call_result_gas_le` (generalize the heavy discriminants,
`split at`, never open the 140-arm `step` match). -/
theorem call_spec
    {P : AccountMap → Substate → Prop} {Q : AccountMap → Substate → ByteArray → Prop}
    {fuel gasCost : ℕ} {bvh : List ByteArray}
    {gas source recipient t v v' io is oo os : UInt256} {perm : Bool}
    {ev : EVM.State} {x : UInt256} {ev' : EVM.State}
    (hΘ : ThetaTriple P (toExecute ev.accountMap (AccountAddress.ofUInt256 t)) Q)
    (hcall : call fuel gasCost bvh gas source recipient t v v' io is oo os perm ev
      = .ok (x, ev'))
    (hP : P ev.accountMap (callAccessSubstate ev t))
    (hx : x = ⟨1⟩) :
    Q ev'.accountMap ev'.substate ev'.toMachineState.returnData := by
  subst hx
  obtain _ | f := fuel
  · rw [NeverOutOfFuel.call_zero] at hcall
    exact Except.noConfusion hcall
  · simp only [call, bind, Except.bind] at hcall
    split at hcall
    · -- covered branch: value ≤ balance ∧ depth < 1024 — the Θ recursion ran
      split at hcall
      · -- Θ errored: `call` propagates the error, contradicting `.ok`
        exact absurd hcall (by simp)
      · rename_i res hΘeq
        have hinj := Except.ok.inj hcall
        rw [Prod.mk.injEq] at hinj
        obtain ⟨hx1, hres⟩ := hinj
        -- `x = ⟨1⟩` kills the failure disjunction, in particular `!z`
        split at hx1
        · exact absurd hx1 (by decide)
        · rename_i hcond
          have hz : res.2.2.2.2.1 = true := by
            cases hzz : res.2.2.2.2.1
            · exact absurd (by rw [hzz]; simp) hcond
            · rfl
          have hQ := hΘ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            hP hΘeq hz
          rw [← hres]
          exact hQ
    · -- uncovered else-branch: `z` is hardwired `false`, so `x = ⟨0⟩ ≠ ⟨1⟩`
      have hinj := Except.ok.inj hcall
      rw [Prod.mk.injEq] at hinj
      have h01 : (⟨0⟩ : UInt256) = ⟨1⟩ := hinj.1
      exact absurd h01 (by decide)

/-! ## Two-call composition — the nested analog of flat `twoCall_runs` -/

/-- **The bake-off measurement** (nested analog of the flat
`twoCall_runs`, EVM/BytecodeLayer/Examples/TwoCallExample.lean:62).

Both halves of the finding, recorded per the track spec:

* **Nested win**: two-call composition is literally TWO FUNCTION APPLICATIONS
  of `call_spec` plus `And.intro`. No `Runs.trans` machinery, no interleaved
  step-chain gluing, no fuel accounting — the ∀-fuel triples compose by
  instantiation. The flat side had to *earn* its `Runs.call` composition rule.

* **Nested loss**: the middle of the sandwich is HYPOTHESIS-SUPPLIED. `ev₂` —
  the state the interpreter reaches after resuming from the first call and
  stepping to the second CALL site — enters as free data pinned only by
  `hP₂`/`hΘ₂` (exactly like flat's `hmiddle : Runs resumeFr₁ callFr₂ is`).
  But flat DOES have a discharge vocabulary for its middle hypothesis (the
  `runs_*` per-opcode rules step the machine from `resumeFr₁` to `callFr₂`);
  the nested side has NO X-loop opcode logic, so `hP₂` at `ev₂` cannot be
  established from within this surface at all. Caller-level conclusions stay
  blocked on that missing program logic. -/
theorem twoCall_spec
    {P₁ P₂ : AccountMap → Substate → Prop}
    {Q₁ Q₂ : AccountMap → Substate → ByteArray → Prop}
    {f₁ f₂ gc₁ gc₂ : ℕ} {bvh₁ bvh₂ : List ByteArray}
    {gas₁ src₁ rcp₁ t₁ v₁ w₁ io₁ is₁ oo₁ os₁ : UInt256}
    {gas₂ src₂ rcp₂ t₂ v₂ w₂ io₂ is₂ oo₂ os₂ : UInt256}
    {perm₁ perm₂ : Bool} {ev₀ ev₁ ev₂ ev₃ : EVM.State}
    (hΘ₁ : ThetaTriple P₁ (toExecute ev₀.accountMap (AccountAddress.ofUInt256 t₁)) Q₁)
    (hΘ₂ : ThetaTriple P₂ (toExecute ev₂.accountMap (AccountAddress.ofUInt256 t₂)) Q₂)
    (hP₁ : P₁ ev₀.accountMap (callAccessSubstate ev₀ t₁))
    (hcall₁ : call f₁ gc₁ bvh₁ gas₁ src₁ rcp₁ t₁ v₁ w₁ io₁ is₁ oo₁ os₁ perm₁ ev₀
      = .ok (⟨1⟩, ev₁))
    -- the middle run (resume after call 1, step to call 2) is
    -- hypothesis-supplied: `ev₂` is pinned only by `hP₂` (and `hΘ₂`'s index)
    (hP₂ : P₂ ev₂.accountMap (callAccessSubstate ev₂ t₂))
    (hcall₂ : call f₂ gc₂ bvh₂ gas₂ src₂ rcp₂ t₂ v₂ w₂ io₂ is₂ oo₂ os₂ perm₂ ev₂
      = .ok (⟨1⟩, ev₃)) :
    Q₁ ev₁.accountMap ev₁.substate ev₁.toMachineState.returnData ∧
    Q₂ ev₃.accountMap ev₃.substate ev₃.toMachineState.returnData :=
  ⟨call_spec hΘ₁ hcall₁ hP₁ rfl, call_spec hΘ₂ hcall₂ hP₂ rfl⟩

end NestedEvmYul
