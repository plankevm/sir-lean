import LirLean.Assembly.LowerConforms

/-!
# LirLean — `Acyclic` well-formedness ⇒ `MatFueled` (recompute-fuel sufficiency)

`WellFormedLowered` (`LowerConforms.lean`) carries `MatFueled (defsOf prog) (recomputeFuel
prog) e` for every materialised operand as a *structural* field — the honest well-formedness
tie that `recomputeFuel` is large enough to recompute every tmp's def-chain without bottoming
out. This module discharges that field from a clean **acyclicity** predicate on `defsOf prog`:
a rank function `rank : Tmp → ℕ` under which every definition's operands have strictly smaller
rank (an SSA-style well-founded def relation). Acyclicity + a fuel exceeding the maximum rank
gives `MatFueled` structurally — no `MatFueled` hypothesis survives for an acyclic program.

## The shape of `MatFueled`

`MatFueled defs f e` (`MatDecLower.lean`) is `False` exactly when fuel `f` hits `0` on a
non-leaf (`.tmp`/`.add`/`.lt`/`.sload`) — it is the structural negation of the
`materialiseExpr` recursion bottoming out. Each `.tmp` expansion (`defs t = some e'`) and each
`.add`/`.lt`/`.sload` *node* consumes one fuel before recursing into operand tmps. So
`MatFueled defs f e` holds iff `f` exceeds the *expansion height* of `e`: the longest chain of
definition-unfoldings, counting each structural node. That height is finite (and bounded)
exactly when the def-relation is acyclic.

## The acyclicity witness

`ExprRankLt rank e n` bounds the rank of every tmp occurring at the top level of `e`, with the
**structural cost** folded in: a bare `.tmp t` only needs `rank t < n` (its unfolding is the
next fuel step), while an `.add`/`.lt`/`.sload` *node* needs its operand tmps' ranks `+ 1 < n`
(the node itself spends a fuel step, then its `.tmp` operands spend another). `Acyclic defs
rank` says every definition body `defs t = some e` satisfies `ExprRankLt rank e (rank t)` —
unfolding a definition strictly decreases rank, so there are no cycles, and the structural cost
is accounted. The central lemma `matFueled_of_exprRankLt` shows `ExprRankLt rank e f` suffices
for `MatFueled defs f e`, by strong induction on the fuel `f`.

No `sorry`, no `axiom`, no `native_decide`. Imports `LowerConforms` only to phrase the
`WellFormedLowered.matFueled_*` discharge; the core is a pure fuel/rank argument over `Expr`.

**Note (2026-07-03).** The `## The headline restated over acyclicity` section — the four
`lower_conforms_acyclic*` theorems that supplied the vacuous `StmtTies`/`TermTies` — was
DELETED with the rest of the vacuous conformance surface (`docs/final-audit-2026-07-03.md`).
The acyclicity ⇒ `WellFormedLowered` core below is RETAINED as Phase-3 salvage: it is the
decidable static discharge of `WellLowered.wf` (R9). It is currently unreferenced in the
default build (its only consumers were the deleted headlines).
-/

namespace Lir

open Evm

/-! ## The rank-based acyclicity predicate -/

/-- **`ExprRankLt rank e n`** — the fuel-need bound: every tmp occurring at the top level of
`e` ranks low enough that `e` materialises within fuel `n`. A bare `.tmp t` needs `rank t < n`
(unfolding it is the next fuel step). A structural node (`.add`/`.lt`/`.sload`) spends one fuel
itself, so its operand tmps need `rank · + 1 < n`. Literals (`imm`) and `gas` are leaves
(vacuously fine). -/
def ExprRankLt (rank : Tmp → ℕ) : Expr → ℕ → Prop
  | .imm _,   _ => True
  | .gas,     n => 0 < n          -- `gas` lowers to a `GAS` opcode: needs one fuel step
  | .tmp t,   n => rank t < n
  | .add a b, n => rank a + 1 < n ∧ rank b + 1 < n
  | .lt a b,  n => rank a + 1 < n ∧ rank b + 1 < n
  | .sload k, n => rank k + 1 < n
  | .slot _, _ => True   -- a memory-readback leaf (no sub-tmps); like `imm`

/-- `ExprRankLt` is monotone in the fuel bound: a need satisfied at `n` survives any larger
`m ≥ n`. -/
theorem ExprRankLt.mono {rank : Tmp → ℕ} {e : Expr} {n m : ℕ}
    (h : ExprRankLt rank e n) (hnm : n ≤ m) : ExprRankLt rank e m := by
  cases e with
  | imm _ => trivial
  | gas => exact Nat.lt_of_lt_of_le h hnm
  | tmp t => exact Nat.lt_of_lt_of_le h hnm
  | add a b => exact ⟨Nat.lt_of_lt_of_le h.1 hnm, Nat.lt_of_lt_of_le h.2 hnm⟩
  | lt a b => exact ⟨Nat.lt_of_lt_of_le h.1 hnm, Nat.lt_of_lt_of_le h.2 hnm⟩
  | sload k => exact Nat.lt_of_lt_of_le h hnm
  | slot _ => trivial

/-- **`Acyclic defs rank`** — the def-relation respects the rank: every defining body's
top-level operands fit `ExprRankLt` below `rank t`, so unfolding a definition strictly
decreases rank (a topological order on the recompute-on-use def-graph; no cycles). -/
def Acyclic (defs : Tmp → Option Expr) (rank : Tmp → ℕ) : Prop :=
  ∀ t e, defs t = some e → ExprRankLt rank e (rank t)

/-! ## The central discharge: acyclicity + fuel ⇒ `MatFueled` -/

/-- **`MatFueled` from acyclicity (the core).** For an `Acyclic defs rank` program, any
expression satisfying the fuel-need bound `ExprRankLt rank e f` is materialisable within fuel
`f`: `MatFueled defs f e`. By induction on `f`. A `.tmp t` step unfolds `defs t = some e'`;
`Acyclic` bounds `e'` by `ExprRankLt rank e' (rank t)` with `rank t ≤ f-1`, so the IH at `f-1`
applies. A structural node recurses into its operand tmps at `f-1`, whose `rank · + 1 < f`
gives `rank · < f-1`, i.e. `ExprRankLt rank (.tmp ·) (f-1)`. -/
theorem matFueled_of_exprRankLt {defs : Tmp → Option Expr} {rank : Tmp → ℕ}
    (hac : Acyclic defs rank) :
    ∀ (f : ℕ) (e : Expr), ExprRankLt rank e f → MatFueled defs f e := by
  intro f
  induction f with
  | zero =>
    intro e he
    -- with zero fuel only literals survive; every non-leaf needs a `· < 0`, impossible.
    cases e with
    | imm _ => exact True.intro
    | slot _ => exact True.intro
    | gas => exact absurd he (Nat.not_lt_zero _)
    | tmp t => exact absurd he (Nat.not_lt_zero _)
    | add a b => exact absurd he.1 (Nat.not_lt_zero _)
    | lt a b => exact absurd he.1 (Nat.not_lt_zero _)
    | sload k => exact absurd he (Nat.not_lt_zero _)
  | succ f ih =>
    intro e he
    cases e with
    | imm _ => exact True.intro
    | slot _ => exact True.intro
    | gas => exact True.intro
    | tmp t =>
      cases hdt : defs t with
      | none => rw [matFueled_tmp_none defs f t hdt]; exact True.intro
      | some e' =>
        rw [matFueled_tmp_some defs f t e' hdt]
        -- `rank t < f + 1` ⟹ `rank t ≤ f`; `Acyclic` bounds `e'` below `rank t ≤ f`.
        exact ih e' ((hac t e' hdt).mono (Nat.lt_succ_iff.mp he))
    | add a b =>
      -- `rank a + 1 < f + 1` ⟹ `rank a < f` = `ExprRankLt rank (.tmp a) f`.
      exact ⟨ih (.tmp b) (Nat.lt_of_succ_lt_succ he.2), ih (.tmp a) (Nat.lt_of_succ_lt_succ he.1)⟩
    | lt a b =>
      exact ⟨ih (.tmp b) (Nat.lt_of_succ_lt_succ he.2), ih (.tmp a) (Nat.lt_of_succ_lt_succ he.1)⟩
    | sload k =>
      exact ih (.tmp k) (Nat.lt_of_succ_lt_succ he)

/-- **`MatFueled` for any tmp, from acyclicity + a fuel exceeding its rank.** The operands the
lowering materialises are all `.tmp` reads (the `sstore` key/value, the `ret` operand); this is
the form the `WellFormedLowered.matFueled_*` discharge consumes. -/
theorem matFueled_tmp_of_acyclic {defs : Tmp → Option Expr} {rank : Tmp → ℕ}
    (hac : Acyclic defs rank) {f : ℕ} {t : Tmp} (ht : rank t < f) :
    MatFueled defs f (.tmp t) :=
  matFueled_of_exprRankLt hac f (.tmp t) ht

/-! ## Discharging `WellFormedLowered.matFueled_*` from acyclicity

The lowering materialises only `.tmp` operands, so `WellFormedLowered`'s two `MatFueled` fields
(`matFueled_sstore`, `matFueled_ret`) are exactly `MatFueled (defsOf prog) (recomputeFuel prog)
(.tmp ·)` instances. Given an `Acyclic (defsOf prog) rank` witness whose ranks all sit below
`recomputeFuel prog`, both fields follow from `matFueled_tmp_of_acyclic`. The remaining
`WellFormedLowered` fields are the pure program-size pc/offset bounds (`bound_*`), independent
of `MatFueled`. -/

/-- **The acyclicity-based well-formedness predicate.** Bundles an `Acyclic (defsOf prog) rank`
witness with the rank-fits-fuel side-condition (`rank t < recomputeFuel prog` for every tmp)
and the program-size pc/offset bounds (`bounds`, verbatim the non-`MatFueled` fields of
`WellFormedLowered`). Discharging it is: pick a topological rank, check it bounds the def-graph
and fits the fuel, and the finite pc/offset bound check. -/
structure AcyclicWellFormed (prog : Program) where
  /-- A topological rank on the recompute-on-use def-graph. -/
  rank : Tmp → ℕ
  /-- The def-relation respects the rank (no cycles, structural cost accounted). -/
  acyclic : Acyclic (defsOf prog) rank
  /-- Every tmp's rank fits the recompute fuel **with one unit of slack** — so
  `MatFueled … (recomputeFuel prog) (.tmp t)` holds for every `t`, AND so does the **reduced**-fuel
  `MatFueled … (recomputeFuel prog - 1) (.tmp t)` the spilled-`sload` key materialise consumes (the
  SLOAD opcode costs one fuel unit, so the key recurses at `recomputeFuel - 1`). The `+1` slack is
  benign: `recomputeFuel = (Σ stmt counts) + 1` generously over-bounds any def-chain depth. -/
  rank_lt_fuel : ∀ t, rank t + 1 < recomputeFuel prog
  /-- `sstore` pc bound (a non-`MatFueled` `WellFormedLowered` field, carried verbatim). -/
  bound_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    pcOf prog L pc
      + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2 ^ 32
  /-- spilled-`sload` pc bound (carried verbatim into `WellFormedLowered.bound_sload`). -/
  bound_sload : ∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    pcOf prog L pc
      + ((materialiseExpr (defsOf prog) (recomputeFuel prog - 1) (.tmp k)).length + 35) < 2 ^ 32
  /-- `ret` pc bound. -/
  bound_ret : ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    termOf prog L
      + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length ≤ 2 ^ 32
  /-- `stop` pc bound. -/
  bound_stop : ∀ (L : Label) (b : Block),
    prog.blocks.toList[L.idx]? = some b → b.term = .stop →
    termOf prog L < 2 ^ 32
  /-- `jump` pc/offset bounds. -/
  bound_jump : ∀ (L : Label) (b : Block) (dst : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
    termOf prog L + 5 < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32
  /-- `branch` pc/offset bounds. -/
  bound_branch : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    termOf prog L
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length + 11 < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32
  /-- Call-result slot registration (a non-`MatFueled` `WellFormedLowered` field, verbatim):
  every registered call result carries its canonical `slotOf`. -/
  slots_slot : ∀ (tw : Tmp) (slot' : Nat),
    defsOf prog tw = some (.slot slot') → slot' = slotOf tw

/-- **`WellFormedLowered` from acyclicity.** The two `MatFueled` fields are discharged from the
`Acyclic` witness (`matFueled_tmp_of_acyclic`, since the lowering only materialises `.tmp`
operands); the pc/offset bounds carry over verbatim. So an `AcyclicWellFormed` program is
`WellFormedLowered` — the structural `MatFueled` hypotheses are gone, replaced by acyclicity. -/
theorem wellFormedLowered_of_acyclic {prog : Program} (h : AcyclicWellFormed prog) :
    WellFormedLowered prog where
  matFueled_sstore := fun _ _ _ key value _ _ =>
    ⟨matFueled_tmp_of_acyclic h.acyclic (by have := h.rank_lt_fuel value; omega),
     matFueled_tmp_of_acyclic h.acyclic (by have := h.rank_lt_fuel key; omega)⟩
  bound_sstore := h.bound_sstore
  matFueled_sload := fun _ _ _ _ k _ _ =>
    -- `recomputeFuel ≥ 1` (it is `Σ + 1`) and `rank k + 1 < recomputeFuel` gives the reduced-fuel
    -- `MatFueled … (recomputeFuel - 1) (.tmp k)` (the SLOAD costs one fuel unit).
    ⟨by have := h.rank_lt_fuel k; omega,
     matFueled_tmp_of_acyclic h.acyclic (by have := h.rank_lt_fuel k; omega)⟩
  bound_sload := h.bound_sload
  matFueled_ret := fun _ _ t _ _ => matFueled_tmp_of_acyclic h.acyclic (by have := h.rank_lt_fuel t; omega)
  matFueled_branch := fun _ _ cond _ _ _ _ =>
    matFueled_tmp_of_acyclic h.acyclic (by have := h.rank_lt_fuel cond; omega)
  bound_ret := h.bound_ret
  bound_stop := h.bound_stop
  bound_jump := h.bound_jump
  bound_branch := h.bound_branch
  slots_slot := h.slots_slot

end Lir
