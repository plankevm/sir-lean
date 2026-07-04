import LirLean.Spec.Semantics

/-!
# LirLean v2 — IR-run determinism

This module is the **frame-free determinism** layer (`docs/ir-design-v3.md` §4). It
imports ONLY the IR core (`LirLean.Spec.Semantics`, hence `LirLean.Spec.IR`/`Evm`) — **no
`BytecodeLayer`, no `Frame`, no `Runs`**. Everything here is a statement about
`Trace`s and `IRRun`s alone.

It carries **`RunFrom`/`IRRun` determinism** (§4 item 2) — same program/start/trace ⇒
the *same* `Observable`. The prototype's `RunFrom` is acyclic-by-construction; structural
induction closes it (`EvalStmt.det` → `RunStmts.det` → `RunFrom.det` → `IRRun.det`).
This unlocks the `∀ O, IRRun … O → O = …` ("*the* observable") headline shape.

The gas-monotonicity law that used to live here (`Trace.gasMonotone`/`MonotoneGas`,
with `gasMonotone_pair`/`lt_eq_zero_of_toNat_le`) was deleted per `docs/gas-decision.md`:
proved-but-unused — gas is a log-fed exact-equality oracle, not a law-governed stream.
-/

namespace Lir.V2

open Evm

/-! ## `RunFrom` determinism (`docs/ir-design-v3.md` §4 item 2)

The prototype's `RunFrom` is acyclic-by-construction and its statement/block accessors are
functional, so the run is deterministic in the trace. We prove it bottom-up:
`EvalStmt` → `RunStmts` → `RunFrom`. This unlocks the "*the* observable" headline shape. -/

/-- `EvalStmt` is deterministic: same pre-state/trace/call-stream/statement ⇒ same
post-state/trace/call-stream. By cases on the two derivations; the `evalExpr` results agree
by `Option.some.inj`, and the popped stream heads are pinned by the shared input stream. -/
theorem EvalStmt.det {prog : Program} {st st₁ st₂ : IRState}
    {T T₁ T₂ : Trace} {C C₁ C₂ : CallStream} {s : Stmt}
    (h₁ : EvalStmt prog st T C s st₁ T₁ C₁) (h₂ : EvalStmt prog st T C s st₂ T₂ C₂) :
    st₁ = st₂ ∧ T₁ = T₂ ∧ C₁ = C₂ := by
  cases h₁ with
  | assignPure hne hv =>
    cases h₂ with
    | assignPure _ hv' => exact ⟨by rw [Option.some.inj (hv.symm.trans hv')], rfl, rfl⟩
    | assignGas => exact absurd rfl hne
  | assignGas =>
    cases h₂ with
    | assignPure hne' _ => exact absurd rfl hne'
    | assignGas => exact ⟨rfl, rfl, rfl⟩
  | sstore hk hv =>
    cases h₂ with
    | sstore hk' hv' =>
      rw [Option.some.inj (hk.symm.trans hk'), Option.some.inj (hv.symm.trans hv')]
      exact ⟨rfl, rfl, rfl⟩
  | call hcallee hgas =>
    cases h₂ with
    | call hcallee' hgas' =>
      -- the popped head `(world', success)` is pinned by the shared input call stream
      -- (`cases` unifies `(w',s') :: C₁ = (w'',s'') :: C₂`); callee/gasFwd are irrelevant to
      -- the post-state now (the head IS the effect), so the post-states coincide structurally.
      exact ⟨rfl, rfl, rfl⟩

/-- `RunStmts` is deterministic: same pre-state/trace/call-stream/statement-list ⇒ same
post-state/trace/call-stream. Induction on the first derivation, `EvalStmt.det` at each head. -/
theorem RunStmts.det {prog : Program} {st st₁ st₂ : IRState}
    {T T₁ T₂ : Trace} {C C₁ C₂ : CallStream} {ss : List Stmt}
    (h₁ : RunStmts prog st T C ss st₁ T₁ C₁) (h₂ : RunStmts prog st T C ss st₂ T₂ C₂) :
    st₁ = st₂ ∧ T₁ = T₂ ∧ C₁ = C₂ := by
  induction h₁ generalizing st₂ T₂ C₂ with
  | nil => cases h₂ with | nil => exact ⟨rfl, rfl, rfl⟩
  | cons hh _ ih =>
    cases h₂ with
    | cons hh' ht' =>
      obtain ⟨hst, hT, hC⟩ := EvalStmt.det hh hh'
      subst hst; subst hT; subst hC
      exact ih ht'

/-- **`RunFrom` determinism (§4 item 2).** Same program, start state, trace and entry
label ⇒ the *same* observable. Structural induction on the first derivation; the
terminator is pinned by the block (`blockAt` is functional), the prefix state/trace by
`RunStmts.det`, and the branch direction by the (functional) condition lookup — so the two
runs never diverge. The acyclic-by-construction shape needs no fuel. -/
theorem RunFrom.det {prog : Program} {st : IRState} {T : Trace} {C : CallStream} {L : Label}
    {O O' : Observable}
    (h₁ : RunFrom prog st T C L O) (h₂ : RunFrom prog st T C L O') : O = O' := by
  induction h₁ generalizing O' with
  | ret hb hss hterm hv =>
    cases h₂ with
    | ret hb' hss' hterm' hv' =>
      -- same block (`blockAt` functional) ⇒ same statements ⇒ same post-state
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, _, _⟩ := RunStmts.det hss hss'
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
      obtain ⟨hst, _, _⟩ := RunStmts.det hss hss'; subst hst; rfl
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
      obtain ⟨hst, hT, hC⟩ := RunStmts.det hss hss'; subst hst; subst hT; subst hC
      rw [hterm] at hterm'; cases hterm'    -- same `thenL`
      exact ih hrest'
    | branchElse hb' hss' hterm' hc' hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, _, _⟩ := RunStmts.det hss hss'; subst hst
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
      obtain ⟨hst, _, _⟩ := RunStmts.det hss hss'; subst hst
      rw [hterm] at hterm'; cases hterm'
      exact absurd (hc'.symm.trans hc) (by simpa using hnz')
    | branchElse hb' hss' hterm' hc' hrest' =>
      cases Option.some.inj (hb.symm.trans hb')
      obtain ⟨hst, hT, hC⟩ := RunStmts.det hss hss'; subst hst; subst hT; subst hC
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
      obtain ⟨hst, hT, hC⟩ := RunStmts.det hss hss'; subst hst; subst hT; subst hC
      rw [hterm] at hterm'; cases hterm'    -- same `dst`
      exact ih hrest'

/-- **`IRRun` determinism.** Same program/world/trace ⇒ the *same* observable — the §4
item-2 "*the* observable" fact at top level. -/
theorem IRRun.det {prog : Program} {w₀ : World} {T : Trace} {C : CallStream}
    {O O' : Observable}
    (h₁ : IRRun prog w₀ T C O) (h₂ : IRRun prog w₀ T C O') : O = O' :=
  RunFrom.det h₁ h₂

end Lir.V2
