import LirLean.V2.Machine

/-!
# LirLean v2 — the frame-free gas LAW and IR-run determinism

This module is the **frame-free core law** layer (`docs/ir-design-v2.md` §3.4,
`docs/ir-design-v3.md` §2, §4). It imports ONLY the IR core (`LirLean.V2.Machine`,
hence `LirLean.IR`/`Evm`) — **no `BytecodeLayer`, no `Frame`, no `Runs`**. Everything
here is a statement about `Trace`s and `IRRun`s alone; the realisability *witness*
that ties these to a bytecode `Runs` lives in the IR↔bytecode bridge
(`LirLean/V2/Realisability.lean`), never here.

It carries:

1. **The monotonicity law** (`Trace.gasMonotone`, §3.4) and its interface name
   `MonotoneGas` (§2) — the gas-read stream, monotone non-increasing on `.toNat`,
   in program order. The *only* gas fact the IR semantics may assume, never any
   per-opcode cost. Plus the pure-`GasOracle` lemmas about it (`gasMonotone_pair`) and the
   arithmetic the IR side uses to discharge a guard under the law
   (`lt_eq_zero_of_toNat_le`).

2. **`RunFrom`/`IRRun` determinism** (§4 item 2) — same program/start/trace ⇒ the
   *same* `Observable`. The prototype's `RunFrom` is acyclic-by-construction; structural
   induction closes it (`EvalStmt.det` → `RunStmts.det` → `RunFrom.det` → `IRRun.det`).
   This unlocks the `∀ O, IRRun … O → O = …` ("*the* observable") headline shape.
-/

namespace Lir.V2

open Evm

/-! ## 1. The monotonicity law on the gas stream (`docs/ir-design-v2.md` §3.4)

The ONE law the gas oracle carries. The stream *is* the gas-read values in program
order (`GasOracle = List Word`; there is no wrapper to extract from), so the law is the
chain "non-increasing on `.toNat`" stated directly over the list: each later read is `≤`
the one before. We state `≤` on the `toNat` of the words — the robust EVM "gas remaining"
order — which makes the discharge from the machine's `gasAvailable.toNat` descent
immediate. -/

/-- **The monotonicity law (§3.4).** The gas reads, in program order, are
monotone non-increasing: each consecutive pair `(earlier, later)` satisfies
`later.toNat ≤ earlier.toNat` (gas remaining only goes down). This is the *only* gas
fact the IR semantics is allowed to assume — never any per-opcode cost. -/
def Trace.gasMonotone (T : Trace) : Prop :=
  T.IsChain (fun earlier later => later.toNat ≤ earlier.toNat)

/-- **The one gas law (`docs/ir-design-v3.md` §2, §8).** The interface name for
`Trace.gasMonotone`: the gas-read stream `g`, in program order, monotone non-increasing
on `.toNat`. We alias rather than redefine so every existing fact (`gasMonotone_pair`, …)
transfers verbatim. `Word`-valued throughout; `ℕ` appears ONLY via `.toNat`. -/
abbrev MonotoneGas (g : GasOracle) : Prop := Trace.gasMonotone g

/-- For a two-read stream the law is exactly `g2 ≤ g1` (the case the milestone uses). -/
theorem gasMonotone_pair {g1 g2 : Word} :
    Trace.gasMonotone [g1, g2] ↔ g2.toNat ≤ g1.toNat :=
  -- `IsChain` on a pair is the relation
  List.isChain_pair

/-! ## 2. Using the law: `lt` of two monotone reads is `0`

`UInt256.lt a b = if a < b then 1 else 0`, and `<`/`≤` on `UInt256` are the `toBitVec`
(= `toNat`) order. So once monotonicity gives `g2.toNat ≤ g1.toNat` the "gas went up"
guard `lt g1 g2 = (g1 < g2)` is forced to `0`. This is the sole place the law is used
on the IR side. -/

/-- `b ≤ a` (on `toNat`) forces `UInt256.lt a b = 0` — the guard `lt g1 g2` is `0` when
`g2 ≤ g1`, i.e. the "did gas increase" test is false under monotonicity. -/
theorem lt_eq_zero_of_toNat_le {a b : Word} (h : b.toNat ≤ a.toNat) :
    UInt256.lt a b = 0 := by
  have hnlt : ¬ (a < b) := by
    intro hlt
    -- a < b is a.toBitVec < b.toBitVec, i.e. a.toNat < b.toNat
    have hbv : a.toBitVec.toNat < b.toBitVec.toNat := hlt
    simp only [← UInt256.toNat_eq_toBitVec_toNat] at hbv
    omega
  unfold UInt256.lt UInt256.fromBool
  rw [decide_eq_false hnlt, if_neg (by simp)]

/-! ## 3. `RunFrom` determinism (`docs/ir-design-v3.md` §4 item 2)

The prototype's `RunFrom` is acyclic-by-construction and its statement/block accessors are
functional, so the run is deterministic in the trace. We prove it bottom-up:
`EvalStmt` → `RunStmts` → `RunFrom`. This unlocks the "*the* observable" headline shape. -/

/-- `EvalStmt` is deterministic: same pre-state/trace/statement ⇒ same post-state/trace.
By cases on the two derivations; the `evalExpr` results agree by `Option.some.inj`. -/
theorem EvalStmt.det {prog : Program} {o : CallOracle} {st st₁ st₂ : IRState}
    {T T₁ T₂ : Trace} {s : Stmt}
    (h₁ : EvalStmt prog o st T s st₁ T₁) (h₂ : EvalStmt prog o st T s st₂ T₂) :
    st₁ = st₂ ∧ T₁ = T₂ := by
  cases h₁ with
  | assignPure hne hv =>
    cases h₂ with
    | assignPure _ hv' => exact ⟨by rw [Option.some.inj (hv.symm.trans hv')], rfl⟩
    | assignGas => exact absurd rfl hne
  | assignGas =>
    cases h₂ with
    | assignPure hne' _ => exact absurd rfl hne'
    | assignGas => exact ⟨rfl, rfl⟩
  | sstore hk hv =>
    cases h₂ with
    | sstore hk' hv' =>
      rw [Option.some.inj (hk.symm.trans hk'), Option.some.inj (hv.symm.trans hv')]
      exact ⟨rfl, rfl⟩
  | call hcallee hgas ho =>
    cases h₂ with
    | call hcallee' hgas' ho' =>
      -- callee/gasFwd words pinned by the (functional) `locals` lookups, the
      -- `(world', success)` bundle by the (functional) oracle.
      cases Option.some.inj (hcallee.symm.trans hcallee')
      cases Option.some.inj (hgas.symm.trans hgas')
      cases ho.symm.trans ho'
      exact ⟨rfl, rfl⟩

/-- `RunStmts` is deterministic: same pre-state/trace/statement-list ⇒ same post-state/trace.
Induction on the first derivation, `EvalStmt.det` at each head. -/
theorem RunStmts.det {prog : Program} {o : CallOracle} {st st₁ st₂ : IRState}
    {T T₁ T₂ : Trace} {ss : List Stmt}
    (h₁ : RunStmts prog o st T ss st₁ T₁) (h₂ : RunStmts prog o st T ss st₂ T₂) :
    st₁ = st₂ ∧ T₁ = T₂ := by
  induction h₁ generalizing st₂ T₂ with
  | nil => cases h₂ with | nil => exact ⟨rfl, rfl⟩
  | cons hh _ ih =>
    cases h₂ with
    | cons hh' ht' =>
      obtain ⟨hst, hT⟩ := EvalStmt.det hh hh'
      subst hst; subst hT
      exact ih ht'

/-- **`RunFrom` determinism (§4 item 2).** Same program, start state, trace and entry
label ⇒ the *same* observable. Structural induction on the first derivation; the
terminator is pinned by the block (`blockAt` is functional), the prefix state/trace by
`RunStmts.det`, and the branch direction by the (functional) condition lookup — so the two
runs never diverge. The acyclic-by-construction shape needs no fuel. -/
theorem RunFrom.det {prog : Program} {o : CallOracle} {st : IRState} {T : Trace} {L : Label}
    {O O' : Observable}
    (h₁ : RunFrom prog o st T L O) (h₂ : RunFrom prog o st T L O') : O = O' := by
  induction h₁ generalizing O' with
  | ret hb hss hterm hv =>
    cases h₂ with
    | ret hb' hss' hterm' hv' =>
      -- same block (`blockAt` functional) ⇒ same statements ⇒ same post-state
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, _⟩ := RunStmts.det hss hss'
      subst hst; rw [hterm] at hterm'; cases hterm'    -- same returned tmp
      rw [Option.some.inj (hv.symm.trans hv')]
    | stop hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchThen hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchElse hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | jump hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
  | stop hb hss hterm =>
    cases h₂ with
    | ret hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | stop hb' hss' hterm' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, _⟩ := RunStmts.det hss hss'; subst hst; rfl
    | branchThen hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchElse hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | jump hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
  | branchThen hb hss hterm hc hnz hrest ih =>
    cases h₂ with
    | ret hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | stop hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchThen hb' hss' hterm' hc' _ hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, hT⟩ := RunStmts.det hss hss'; subst hst; subst hT
      rw [hterm] at hterm'; cases hterm'    -- same `thenL`
      exact ih hrest'
    | branchElse hb' hss' hterm' hc' hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, _⟩ := RunStmts.det hss hss'; subst hst
      rw [hterm] at hterm'; cases hterm'    -- same condition tmp
      exact absurd (hc.symm.trans hc') (by simpa using hnz)
    | jump hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
  | branchElse hb hss hterm hc hrest ih =>
    cases h₂ with
    | ret hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | stop hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchThen hb' hss' hterm' hc' hnz' hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, _⟩ := RunStmts.det hss hss'; subst hst
      rw [hterm] at hterm'; cases hterm'
      exact absurd (hc'.symm.trans hc) (by simpa using hnz')
    | branchElse hb' hss' hterm' hc' hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, hT⟩ := RunStmts.det hss hss'; subst hst; subst hT
      rw [hterm] at hterm'; cases hterm'    -- same `elseL`
      exact ih hrest'
    | jump hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
  | jump hb hss hterm hrest ih =>
    cases h₂ with
    | ret hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | stop hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchThen hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | branchElse hb' _ hterm' =>
      cases Option.some.inj (hb.symm.trans hb'); rw [hterm] at hterm'; cases hterm'
    | jump hb' hss' hterm' hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, hT⟩ := RunStmts.det hss hss'; subst hst; subst hT
      rw [hterm] at hterm'; cases hterm'    -- same `dst`
      exact ih hrest'

/-- **`IRRun` determinism.** Same program/world/trace ⇒ the *same* observable — the §4
item-2 "*the* observable" fact at top level. -/
theorem IRRun.det {prog : Program} {o : CallOracle} {w₀ : World} {T : Trace} {O O' : Observable}
    (h₁ : IRRun prog o w₀ T O) (h₂ : IRRun prog o w₀ T O') : O = O' :=
  RunFrom.det h₁ h₂

end Lir.V2
