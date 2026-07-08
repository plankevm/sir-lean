import LirLean.Materialise.MatDecLower

/-!
# LirLean — rank-based acyclicity ⇒ `MatFueled` (legacy generic-`defs` fuel core; P9-deletes)

Legacy support for the fuel-era materialisation: a rank function `rank : Tmp → ℕ` under which
every definition's operands have strictly smaller rank (an SSA-style well-founded def relation)
makes the fuel-sufficiency predicate `MatFueled defs f e` (`Materialise/MatDecLower.lean`)
discharge structurally for any fuel exceeding the maximum rank.

**Status (Phase 2A P6+P7).** The canonical pipeline is the total fold (`matCache` /
`MatDecC` / `materialise_runsC`), which terminates on the ordered def-env
(`DefEnvOrdered`) and carries NO fuel-sufficiency obligation — nothing in the canonical
cone consumes this module anymore. The former `AcyclicWellFormed` bundle and its
`wellFormedLowered_of_acyclic` discharge were DELETED with the fuel `WellFormedLowered`
fields they targeted. What remains is the generic-`defs` core (`ExprRankLt` / `Acyclic` /
`matFueled_of_exprRankLt` / `matFueled_tmp_of_acyclic`), kept compiling solely alongside
the residual fuel definitions; the whole file is deleted at P9 with them.

## The shape of `MatFueled`

`MatFueled defs f e` is `False` exactly when fuel `f` hits `0` on a non-leaf
(`.tmp`/`.add`/`.lt`/`.sload`) — the structural negation of the fuel `materialiseExpr`
recursion bottoming out. Each `.tmp` expansion (`defs t = some e'`) and each
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

No `sorry`, no `axiom`, no `native_decide`. Pure fuel/rank argument over `Expr`, generic in a
`defs : Tmp → Option Expr` environment.
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

/-- **`MatFueled` for any tmp, from acyclicity + a fuel exceeding its rank.** The `.tmp`-read
form of `matFueled_of_exprRankLt` (the shape the fuel-era operand materialisations consumed). -/
theorem matFueled_tmp_of_acyclic {defs : Tmp → Option Expr} {rank : Tmp → ℕ}
    (hac : Acyclic defs rank) {f : ℕ} {t : Tmp} (ht : rank t < f) :
    MatFueled defs f (.tmp t) :=
  matFueled_of_exprRankLt hac f (.tmp t) ht

end Lir
