import EvmYul.EVM.Semantics
import NestedEvmYul.SharedObservable
import NestedEvmYul.Refinement
import NestedEvmYul.XiTriple

/-!
# T5 — `LambdaTriple`: the CREATE-side procedure-call surface mirroring `XiTriple`

FOUNDATION FILE (proof-first, no sorry). This file seeds CREATE-side parity for
the nested `Ξ`/`Λ` pair, strictly mirroring the proven CALL-side surface in
`XiTriple.lean` (`ThetaTriple`/`theta_of_xi`/`call_spec`): a success-only,
∀-fuel triple over the contract-creation function `Lambda`, its pure-logic
rules (conseq/conj), the introduction rule `lambda_of_xi` bridging an init-code
`Ξ` triple through `Λ`'s preamble, and the creation-site rule `create_spec`
folding a `LambdaTriple` into the parent CREATE step (plus its output-slot pin
`lambda_success_out_empty`). CREATE is a wanted direction in this repo family;
this is the exp004-side seed (the endgame/observable layer for CREATE is future
work, NOT touched here).

TECHNIQUE NOTE (vs the planned `step_create_eq`): no CREATE-arm dispatcher
EQUATION was needed. Unlike CALL (whose arm is one helper call, so
`step_call_eq` is a small `rfl` statement), the CREATE arm is a 60-line inline
block — its equation would be a full transcription. `create_spec` instead
inverts the arm directly by the `create_result_gas_le` split sequence
(NeverOutOfFuel.lean:2796), so the equation theorem is not scaffolding anyone
needs; it was deliberately not built.

## Differences from the Θ mirror, read off `Lambda`'s definition (never assumed)

* **Result shape**: `Λ` returns a **7-tuple** `(a, cA', σ', g', A', z, out)` —
  the created `AccountAddress` comes FIRST, ahead of Θ's 6 components. The
  triple's postcondition is therefore `Q : AccountAddress → AccountMap →
  Substate → ByteArray → Prop`, parametric in the created address. This is
  forced, not chosen: the address is `KEC (RLP …)`-derived and `ffi.KEC` is
  FFI-opaque (the known CREATE-witness keccak wall), so no statement here ever
  evaluates a hash — `a` is carried as an opaque parameter throughout.
* **Success output is empty**: `Λ`'s success arm returns `.empty` as its output
  component (the init-code's return data becomes the deployed CODE, eqn (115),
  not the output). `Q` still receives the output slot for shape parity.
* **The preamble** is nonce-bump + endowment (`lambdaInit`, eqn (99)) plus the
  substate access-charge `A.addAccessedAccount a` (eqn (97)) — not Θ's plain
  balance transfer.
* **The EIP-7610 collision arm**: `Λ` swaps the init code for `⟨#[0xfe]⟩`
  (invalid opcode) when the target address is occupied. Since occupancy at the
  keccak-derived `a` cannot be decided without evaluating the hash, the client
  `Ξ`-hypothesis honestly covers BOTH codes (`I.code = i ∨ I.code = ⟨#[0xfe]⟩`);
  a client with a triple insensitive to the code (or willing to spec the
  invalid-opcode run) discharges it directly.
* **The `z = true` gate kills the deposit-failure flag**: `z = not F` where `F`
  bundles eqn (118)'s four failure checks (address occupied, deposit-cost
  overrun, `MAX_CODE_SIZE`, EOF-prefix `0xef`); success rewinds all the `if F`
  selectors to their else branches, exposing the code-deposit map
  `σ**[a ↦ {… with code := returnedData}]` that `hdeposit` absorbs.

The `theta_of_xi` inversion recipe applies verbatim (`simp only [Λ, bind,
Except.bind]` + `split at` + ctor injection; the do-block matchers never touch
`step`'s 140-arm match); the only new contact is the `L_A` Option-bind (RLP
serialization, lifted via the local `MonadLift Option (Except ·)`), which
`split` inverts without ever computing the RLP.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-- `Λ` at fuel `0` dies immediately. (`rfl`: the fuel match is outermost.)
Mirror of `NeverOutOfFuel.Θ_zero`. -/
@[simp] theorem Lambda_zero (bvh : List ByteArray)
    (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (s o : AccountAddress)
    (g p v : UInt256) (i : ByteArray) (e : UInt256) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool) :
    Lambda 0 bvh cA gh blocks σ σ₀ A s o g p v i e ζ H w
      = .error .OutOfFuel := rfl

/-! ## The triple -/

/-- **`LambdaTriple P i Q`** — success-only (`z = true`) partial correctness of
a contract creation running init code `i`, over all fuels and all ambient
arguments; the exact CREATE-side mirror of `ThetaTriple`. The postcondition is
parametric in the created address `a` (keccak-opaque — never evaluated). As
with `ThetaTriple`, `P` is over the **PRE-preamble** `σ` (before the
nonce-bump/endowment `σ*`), so creation sites read off the caller state
directly; `lambda_of_xi` pushes `P` through the preamble. -/
def LambdaTriple (P : AccountMap → Substate → Prop) (i : ByteArray)
    (Q : AccountAddress → AccountMap → Substate → ByteArray → Prop) : Prop :=
  ∀ (fuel : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate)
    (s o : AccountAddress) (g p v : UInt256) (e : UInt256) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool)
    (a : AccountAddress) (cA' : Batteries.RBSet AccountAddress compare)
    (σ' : AccountMap) (g' : UInt256) (A' : Substate) (z : Bool) (out : ByteArray),
    P σ A →
    Lambda fuel bvh cA gh blocks σ σ₀ A s o g p v i e ζ H w
      = .ok (a, cA', σ', g', A', z, out) →
    z = true →
    Q a σ' A' out

/-! ## Logical rules — free (pure logic; the semantics is never touched) -/

/-- Consequence rule for `LambdaTriple`. PROVED — pure logic
(mirror of `ThetaTriple.conseq`). -/
theorem LambdaTriple.conseq {P P' : AccountMap → Substate → Prop} {i : ByteArray}
    {Q Q' : AccountAddress → AccountMap → Substate → ByteArray → Prop}
    (hP : ∀ σ A, P' σ A → P σ A) (hQ : ∀ a σ A o, Q a σ A o → Q' a σ A o)
    (h : LambdaTriple P i Q) : LambdaTriple P' i Q' :=
  fun fuel bvh cA gh blocks σ σ₀ A s o g p v e ζ H w a cA' σ' g' A' z out
      hpre hrun hz =>
    hQ _ _ _ _ (h fuel bvh cA gh blocks σ σ₀ A s o g p v e ζ H w a cA' σ' g' A'
      z out (hP _ _ hpre) hrun hz)

/-- Conjunction rule for `LambdaTriple`. PROVED — pure logic (feed the SAME
fueled run into both triples; mirror of `ThetaTriple.conj`). -/
theorem LambdaTriple.conj {P P' : AccountMap → Substate → Prop} {i : ByteArray}
    {Q Q' : AccountAddress → AccountMap → Substate → ByteArray → Prop}
    (h : LambdaTriple P i Q) (h' : LambdaTriple P' i Q') :
    LambdaTriple (fun σ A => P σ A ∧ P' σ A) i
      (fun a σ A o => Q a σ A o ∧ Q' a σ A o) :=
  fun fuel bvh cA gh blocks σ σ₀ A s o g p v e ζ H w a cA' σ' g' A' z out
      hpre hrun hz =>
    ⟨h fuel bvh cA gh blocks σ σ₀ A s o g p v e ζ H w a cA' σ' g' A' z out
        hpre.1 hrun hz,
     h' fuel bvh cA gh blocks σ σ₀ A s o g p v e ζ H w a cA' σ' g' A' z out
        hpre.2 hrun hz⟩

/-! ## From code triples to creation triples: absorbing `Λ`'s preamble -/

/-- `Λ`'s state preamble at created address `a`, verbatim (`σ ↦ σ*`, eqn (99)):
bump the target account's nonce and credit it with the endowment `v`, then
debit the sender `s`. The `thetaTransfer` analog — transcribed from `Lambda`'s
definition, NOT pattern-matched off Θ's (the nonce-bump has no Θ counterpart).
Kept syntactically identical to the source so it stays defeq-applicable in
`lambda_of_xi`. -/
def lambdaInit (σ : AccountMap) (s a : AccountAddress) (v : UInt256) :
    AccountMap :=
  let existentAccount := σ.findD a default
  let newAccount : Account :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := v + existentAccount.balance
    }
  match σ.find? s with
    | none => σ
    | some ac =>
      σ.insert s {ac with balance := ac.balance - v}
        |>.insert a newAccount

/-- `!b = true → b = false` — tiny Bool shim for the `z = not F` gate. -/
private theorem bnot_eq_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact Bool.noConfusion h

set_option maxHeartbeats 1000000 in
/-- **Creation-spec introduction**: an `XiTriple` for the init code — uniformly
in the execution env `Λ` builds, covering the EIP-7610 collision swap
(`I.code = i ∨ I.code = ⟨#[0xfe]⟩`; the created address is keccak-opaque, so
occupancy cannot be decided here) — yields a `LambdaTriple`, provided the
client-side predicates absorb

* the nonce-bump/endowment preamble plus the substate access-charge
  (`habsorb`: `Pξ` holds at `lambdaInit σ s a v` / `A.addAccessedAccount a`
  whenever `P` holds at the entry `σ`/`A` — the `theta_of_xi` `habsorb` analog,
  now also touching the substate because eqn (97) charges the created address),
  and
* the code-deposit postprocessing (`hdeposit`: eqn (115) writes the init-code's
  return data as the new account's code, and the success output is `.empty`).

The `z = true` gate forces the `Ξ`-success arm AND `F = false` (eqn (118): no
collision, deposit affordable, size/EOF checks pass), which rewinds every
`if F` selector to its else branch — that is where `hdeposit`'s map shape comes
from. Proof mirrors `theta_of_xi`: the do-block inversion recipe; all
keccak/RLP terms ride along generalized-opaque. Heartbeats cranked (1M): the
defeq checks against `lambdaInit`/the zeta-expanded `Λ` body are wide. -/
theorem lambda_of_xi
    (P Pξ : AccountMap → Substate → Prop)
    (Qξ : AccountMap → Substate → ByteArray → Prop)
    (Q : AccountAddress → AccountMap → Substate → ByteArray → Prop)
    (i : ByteArray)
    (hΞ : ∀ I : ExecutionEnv, (I.code = i ∨ I.code = ⟨#[0xfe]⟩) →
      XiTriple Pξ I Qξ)
    (habsorb : ∀ (σ : AccountMap) (A : Substate) (s a : AccountAddress)
      (v : UInt256), P σ A → Pξ (lambdaInit σ s a v) (A.addAccessedAccount a))
    (hdeposit : ∀ (a : AccountAddress) (σ'' : AccountMap) (A'' : Substate)
      (ret : ByteArray), Qξ σ'' A'' ret →
      Q a (σ''.insert a { σ''.findD a default with code := ret }) A'' .empty) :
    LambdaTriple P i Q := by
  intro fuel bvh cA gh blocks σ σ₀ A s o g p v e ζ H w a cA' σ' g' A' z out
    hP hrun hz
  subst hz
  obtain _ | f := fuel
  · rw [Lambda_zero] at hrun
    exact Except.noConfusion hrun
  · simp only [Lambda, bind, Except.bind] at hrun
    -- the `L_A` Option-bind (RLP): `.error` arm impossible, `.ok lA` continues
    split at hrun
    · exact Except.noConfusion hrun
    · rename_i lA _hlA
      -- the match on the `Ξ` result (the collision-`if` and the `σ*` preamble
      -- sit inside `Ξ`'s ARGUMENTS, hence are not split candidates — they ride
      -- along generalized-opaque, keeping `lambdaInit` defeq-applicable)
      split at hrun
      · -- `Ξ = .error e`: either rethrown OutOfFuel or a `z = false` package
        split at hrun
        · exact Except.noConfusion hrun
        · have hinj := Except.ok.inj hrun
          simp only [Prod.mk.injEq] at hinj
          exact Bool.noConfusion (show false = true from hinj.2.2.2.2.2.1)
      · -- `Ξ = .ok (.revert g' o)`: also a `z = false` package
        have hinj := Except.ok.inj hrun
        simp only [Prod.mk.injEq] at hinj
        exact Bool.noConfusion (show false = true from hinj.2.2.2.2.2.1)
      · -- `Ξ = .ok (.success (cAr, σ**, g**, A**) ret)`: the genuine creation
        rename_i cAr σSS gSS ASS ret hΞeq
        have hinj := Except.ok.inj hrun
        simp only [Prod.mk.injEq] at hinj
        obtain ⟨ha, -, hσ, -, hA, hznot, hout⟩ := hinj
        -- `z = not F = true` forces the deposit-failure flag `F` to `false`
        have hFeq := bnot_eq_true hznot
        rw [hFeq] at hσ hA
        rw [if_neg Bool.false_ne_true] at hσ hA
        -- the init-code `Ξ` run, through the client's absorb hypothesis; the
        -- collision-`if` on the code is discharged by splitting IT (both arms
        -- are covered by the disjunctive code premise), never the hash
        have hQξ := hΞ _ ?hcode f _ gh blocks
            (lambdaInit σ s
              (Fin.ofNat AccountAddress.size
                (fromByteArrayBigEndian ((ffi.KEC lA).extract 12 32))) v)
            σ₀ g _ _ _
            (habsorb σ A s
              (Fin.ofNat AccountAddress.size
                (fromByteArrayBigEndian ((ffi.KEC lA).extract 12 32))) v hP)
            hΞeq
        case hcode => split <;> first | exact Or.inl rfl | exact Or.inr rfl
        rw [← ha, ← hσ, ← hA, ← hout]
        exact hdeposit _ _ _ _ hQξ

/-! ## The creation-site rule -/

/-- **Successful creations return no output**: `Λ`'s `z = true` arm hardwires
`.empty` (eqn (93) — the init-code's return data becomes the deployed CODE,
not the output). Same inversion skeleton as `lambda_of_xi`, consumed by
`create_spec` to pin the `out` slot. -/
theorem lambda_success_out_empty
    {fuel : ℕ} {bvh : List ByteArray}
    {cA cA' : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {blocks : ProcessedBlocks} {σ σ₀ σ' : AccountMap}
    {A A' : Substate} {s o : AccountAddress} {g p v g' : UInt256}
    {i out : ByteArray} {e : UInt256} {ζ : Option ByteArray} {H : BlockHeader}
    {w : Bool} {a : AccountAddress}
    (h : Lambda fuel bvh cA gh blocks σ σ₀ A s o g p v i e ζ H w
      = .ok (a, cA', σ', g', A', true, out)) :
    out = .empty := by
  obtain _ | f := fuel
  · rw [Lambda_zero] at h
    exact Except.noConfusion h
  · simp only [Lambda, bind, Except.bind] at h
    split at h
    · exact Except.noConfusion h
    · split at h
      · -- `Ξ = .error e`
        split at h
        · exact Except.noConfusion h
        · have hinj := Except.ok.inj h
          simp only [Prod.mk.injEq] at hinj
          exact Bool.noConfusion (show false = true from hinj.2.2.2.2.2.1)
      · -- `Ξ = .ok (.revert g' o)`
        have hinj := Except.ok.inj h
        simp only [Prod.mk.injEq] at hinj
        exact Bool.noConfusion (show false = true from hinj.2.2.2.2.2.1)
      · -- `Ξ` success: the arm returns `.empty` verbatim
        have hinj := Except.ok.inj h
        simp only [Prod.mk.injEq] at hinj
        exact hinj.2.2.2.2.2.2.symm

/-- The CREATE/CREATE2 caller-side preamble (`σ ↦ σ*`, Semantics.lean:247-248):
bump the creator's nonce. This is the state `Λ` receives from the CREATE arm —
NOT `lambdaInit` (that one is `Λ`-internal, at the created address); the
substate is passed through untouched (the access charge on the created address
also happens inside `Λ`). -/
def createInit (σ : AccountMap) (Iₐ : AccountAddress) : AccountMap :=
  let σ_Iₐ : Account := σ.find? Iₐ |>.getD default
  σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}

set_option maxHeartbeats 4000000 in
/-- **The creation-site rule**: a `LambdaTriple` for the init code read out of
memory folds into the parent CREATE step (mirror of `call_spec`; heartbeats
mirror `create_result_gas_le`, whose split sequence this reuses). KEY shape
difference from CALL, forced by the keccak wall: CREATE's result word is
`x = if z = false ∨ depth/funds/size-guards-fail then ⟨0⟩ else .ofNat a` with
`a` hash-derived, so the caller cannot pin `x = ⟨1⟩`. Instead the side
condition `hx : s'.stack ≠ ⟨0⟩ :: rest` (the pushed word is not the failure
word) forces the `Λ`-success branch AND `z = true`, and the conclusion is
existential in the created address — parametric, never evaluating the hash.
As with `call_spec`, the result state carries the callee's post-map/substate
verbatim (`accountMap := σ'`, `substate := A'`), so `Q` lands on the
caller-visible state; the output slot is pinned to `.empty` by
`lambda_success_out_empty`. -/
theorem create_spec
    {P : AccountMap → Substate → Prop}
    {Q : AccountAddress → AccountMap → Substate → ByteArray → Prop}
    {f gasCost : ℕ} {arg : Option (UInt256 × Nat)} {ev s' : EVM.State}
    {μ₀ μ₁ μ₂ : UInt256} {rest : Stack UInt256}
    (hstk : ev.stack = μ₀ :: μ₁ :: μ₂ :: rest)
    (hΛ : LambdaTriple P (ev.memory.readWithPadding μ₁.toNat μ₂.toNat) Q)
    (hP : P (createInit ev.accountMap ev.executionEnv.codeOwner) ev.substate)
    (hstep : step (f+1) gasCost (some (.CREATE, arg)) ev = .ok s')
    (hx : s'.stack ≠ ⟨0⟩ :: rest) :
    ∃ a : AccountAddress, s'.stack = .ofNat a.val :: rest ∧
      Q a s'.accountMap s'.substate .empty := by
  obtain ⟨sh, pc, stk, el⟩ := ev
  dsimp only at hstk
  subst hstk
  simp only [EVM.step, bind, Except.bind, pure, Except.pure, Stack.pop3]
    at hstep
  -- the `(a, evmState', g', z, o)` three-way branch (nonce-overflow /
  -- guarded-`Λ` / guard-else), then the OutOfGass guard, as in
  -- `create_result_gas_le`
  split at hstep
  · -- nonce-overflow branch: `z` is hardwired false, so the failure-word `if`
    -- REDUCES (its `Or`-instance short-circuits on `decide False = false`) and
    -- the pushed word is `⟨0⟩` by defeq, contradicting `hx`
    split at hstep
    · exact absurd hstep (by simp)
    · injection hstep with hs'
      subst hs'
      exact absurd rfl hx
  · -- the funds/depth/size guard
    split at hstep
    · -- `Λ` ran
      split at hstep
      · -- `Λ = .ok (a, cA, σ', g', A', z, o)`
        rename_i lama lamcA lamσ' lamg' lamA' lamz lamo hΛeq
        split at hstep
        · exact absurd hstep (by simp)
        · injection hstep with hs'
          subst hs'
          cases lamz
          · -- `z = false`: the pushed word defeq-reduces to `⟨0⟩`, against `hx`
            exact absurd rfl hx
          · -- `z = true`: peel the `returnData` `if` (first split candidate in
            -- record-field order), then the pushed-word `if`; its `⟨0⟩` arm
            -- contradicts `hx`, its live arm is the genuine creation
            split at hx
            · split at hx
              · exact absurd rfl hx
              · rename_i hc
                have hQ := hΛ f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  hP hΛeq rfl
                rw [lambda_success_out_empty hΛeq] at hQ
                rw [if_neg hc]
                exact ⟨lama, rfl, hQ⟩
            · rename_i hcz
              exact absurd rfl hcz
      · -- `Λ` errored: `z` hardwired false → pushed word `⟨0⟩`, against `hx`
        split at hstep
        · exact absurd hstep (by simp)
        · injection hstep with hs'
          subst hs'
          exact absurd rfl hx
    · -- guard-else branch: `z` hardwired false again
      split at hstep
      · exact absurd hstep (by simp)
      · injection hstep with hs'
        subst hs'
        exact absurd rfl hx

end NestedEvmYul
