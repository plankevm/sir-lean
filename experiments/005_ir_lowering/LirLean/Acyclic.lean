import LirLean.LowerConforms
import LirLean.V2.IRRun

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
  | .callResult _, _ => True   -- a memory-readback leaf (no sub-tmps); like `imm`

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
  | callResult _ => trivial

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
    | callResult _ => exact True.intro
    | gas => exact absurd he (Nat.not_lt_zero _)
    | tmp t => exact absurd he (Nat.not_lt_zero _)
    | add a b => exact absurd he.1 (Nat.not_lt_zero _)
    | lt a b => exact absurd he.1 (Nat.not_lt_zero _)
    | sload k => exact absurd he (Nat.not_lt_zero _)
  | succ f ih =>
    intro e he
    cases e with
    | imm _ => exact True.intro
    | callResult _ => exact True.intro
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
  /-- Every tmp's rank fits the recompute fuel — so `MatFueled … (recomputeFuel prog) (.tmp t)`
  holds for every `t`. -/
  rank_lt_fuel : ∀ t, rank t < recomputeFuel prog
  /-- `sstore` pc bound (a non-`MatFueled` `WellFormedLowered` field, carried verbatim). -/
  bound_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    pcOf prog L pc
      + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2 ^ 32
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
  slots_callResult : ∀ (tw : Tmp) (slot' : Nat),
    defsOf prog tw = some (.callResult slot') → slot' = slotOf tw

/-- **`WellFormedLowered` from acyclicity.** The two `MatFueled` fields are discharged from the
`Acyclic` witness (`matFueled_tmp_of_acyclic`, since the lowering only materialises `.tmp`
operands); the pc/offset bounds carry over verbatim. So an `AcyclicWellFormed` program is
`WellFormedLowered` — the structural `MatFueled` hypotheses are gone, replaced by acyclicity. -/
theorem wellFormedLowered_of_acyclic {prog : Program} (h : AcyclicWellFormed prog) :
    WellFormedLowered prog where
  matFueled_sstore := fun _ _ _ key value _ _ =>
    ⟨matFueled_tmp_of_acyclic h.acyclic (h.rank_lt_fuel value),
     matFueled_tmp_of_acyclic h.acyclic (h.rank_lt_fuel key)⟩
  bound_sstore := h.bound_sstore
  matFueled_ret := fun _ _ t _ _ => matFueled_tmp_of_acyclic h.acyclic (h.rank_lt_fuel t)
  bound_ret := h.bound_ret
  bound_stop := h.bound_stop
  bound_jump := h.bound_jump
  bound_branch := h.bound_branch
  slots_callResult := h.slots_callResult

/-! ## The headline restated over acyclicity

`lower_conforms_wf` (`LowerConforms.lean`) consumes `WellFormedLowered` (which carries the
`MatFueled` recompute-fuel fields). `lower_conforms_acyclic` restates it over the acyclicity
witness `AcyclicWellFormed`, so the `MatFueled` side-conditions are entirely **gone** from the
top-level hypothesis set — replaced by `Acyclic (defsOf prog) rank` + `rank < recomputeFuel`.
It delegates to `lower_conforms_wf` through `wellFormedLowered_of_acyclic`. -/

open BytecodeLayer BytecodeLayer.System BytecodeLayer.Hoare BytecodeLayer.Interpreter Lir.V2 in
/-- **`lower_conforms_acyclic` — the acyclicity-based world-channel compiler-correctness
headline.** Identical to `lower_conforms_wf` except the structural well-formedness is supplied
as an `AcyclicWellFormed` witness (a topological rank bounding the def-graph and fitting the
recompute fuel, plus the pc/offset bounds) rather than `WellFormedLowered` — so no `MatFueled`
hypothesis survives. -/
theorem lower_conforms_acyclic {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {O : V2.Observable} {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hsload : SloadRealises sloadChg { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    -- WELL-FORMEDNESS via acyclicity (replaces `WellFormedLowered`; no `MatFueled` carried):
    (hwf : AcyclicWellFormed prog)
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs (realisedCall log self) L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs (realisedCall log self) self L b)
    (hir : V2.IRRun prog (realisedCall log self) w₀ (realisedGas log) O) :
    O.world = (observe self log.observable).world :=
  lower_conforms_wf hwl hp hmod hentry0 hbentry hbound hstore hsload hgasr hgasj
    (wellFormedLowered_of_acyclic hwf) hstmtties htermties hir

/-! ## `hir` discharged — the single-`stop`-block world-channel theorem

For the base case of CFG totality — a program whose entry block is a `stop`-terminated,
gas-free/call-free, definable straight-line block — the IR run `hir` is no longer a carried
hypothesis: it is **constructed** by `V2.irRun_exists_stop` (`V2/IRRun.lean`) and its
observable is pinned (the IR is deterministic, but here we simply *use* the constructed run's
observable as the theorem's `O`). So `lower_conforms_acyclic_stop` is a fully closed instance
of the world-channel headline with the `hir` residual **eliminated** — the remaining
hypotheses are the recording run, the structural entry facts, the GENUINE entry-frame ties and
per-block §7 ties, and well-formedness. (The general multi-block `hir` construction needs a
CFG-acyclicity *block*-rank measure; see `V2/IRRun.lean`'s closing note.) -/

open BytecodeLayer BytecodeLayer.System BytecodeLayer.Hoare BytecodeLayer.Interpreter Lir.V2 in
/-- **`lower_conforms_acyclic_stop` — single-`stop`-block, `hir` discharged.** As
`lower_conforms_acyclic`, but the entry block is `stop`-terminated, gas-free/call-free, and
its statements are `StmtsDefinable` from the empty-locals/`w₀` start (`hdef`). The IR run is
**constructed** (`irRun_exists_stop`) rather than assumed, so no `hir` hypothesis survives; the
world equation is stated against the constructed run's post-statement world. -/
theorem lower_conforms_acyclic_stop {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hsload : SloadRealises sloadChg { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    (hwf : AcyclicWellFormed prog)
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs (realisedCall log self) L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs (realisedCall log self) self L b)
    -- the entry block is a `stop`-terminated, definable straight-line block (so `hir` builds):
    (hterm : bentry.term = .stop)
    (hdef : V2.StmtsDefinable { locals := fun _ => none, world := w₀ } bentry.stmts) :
    (V2.stmtsPost { locals := fun _ => none, world := w₀ } bentry.stmts).world
      = (observe self log.observable).world :=
  lower_conforms_acyclic hwl hp hmod hentry0 hbentry hbound hstore hsload hgasr hgasj
    hwf hstmtties htermties
    (V2.irRun_exists_stop (o := realisedCall log self) (T := realisedGas log)
      hbentry hterm hdef)

open BytecodeLayer BytecodeLayer.System BytecodeLayer.Hoare BytecodeLayer.Interpreter Lir.V2 in
/-- **`lower_conforms_acyclic_stop_canonical` — single-`stop`-block, `hir` AND `hstore`
discharged.** As `lower_conforms_acyclic_stop`, but the IR initial world is fixed to the entry
frame's own self-storage lens `selfStorage (codeFrame p (lower prog))`, which discharges the
entry STORAGE tie `hstore` **definitionally** (`entry_storageAgree_codeFrame`, by `rfl`). So
*both* `hir` (constructed) and `hstore` (definitional) residuals are eliminated — the surviving
entry-frame ties are exactly the genuine recording-correspondence ones (`hsload`/`hgasr`, which
constrain every same-address frame's warmth/gas). -/
theorem lower_conforms_acyclic_stop_canonical {prog : Program} {self : AccountAddress}
    {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hsload : SloadRealises sloadChg
                { locals := fun _ => none, world := selfStorage (codeFrame p (lower prog)) }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    (hwf : AcyclicWellFormed prog)
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs (realisedCall log self) L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs (realisedCall log self) self L b)
    (hterm : bentry.term = .stop)
    (hdef : V2.StmtsDefinable
              { locals := fun _ => none, world := selfStorage (codeFrame p (lower prog)) }
              bentry.stmts) :
    (V2.stmtsPost
        { locals := fun _ => none, world := selfStorage (codeFrame p (lower prog)) }
        bentry.stmts).world
      = (observe self log.observable).world :=
  lower_conforms_acyclic_stop hwl hp hmod hentry0 hbentry hbound
    (entry_storageAgree_codeFrame p (lower prog)) hsload hgasr hgasj
    hwf hstmtties htermties hterm hdef

/-! ## `hir` discharged for the general acyclic CFG — the multi-block world-channel theorem

`lower_conforms_acyclic_stop`/`_canonical` discharge `hir` only for a *single halt block*.
`lower_conforms_acyclic_cfg` discharges it for **any acyclic call-free gas-free CFG**: the IR run
is **constructed** by `V2.irRun_exists` (`V2/IRRun.lean`) from a control-flow `CFGAcyclic` rank
witness plus the state-threaded edge-definability supply `RunDefinable`, rather than assumed. So
no `hir` hypothesis survives; the world equation holds for the *constructed* run's (existential)
observable. The surviving hypotheses are exactly the recording run, the structural entry facts,
the GENUINE entry-frame ties + per-block §7 ties, def-graph well-formedness (`AcyclicWellFormed`),
and the new control-flow `CFGAcyclic` + `RunDefinable` — NO `hir`.

The two acyclicity witnesses are independent and complementary: `AcyclicWellFormed` ranks the
*def-graph* (value channel, recompute-fuel sufficiency); `CFGAcyclic` ranks the *control-flow*
graph (the `RunFrom` recursion). -/

open BytecodeLayer BytecodeLayer.System BytecodeLayer.Hoare BytecodeLayer.Interpreter Lir.V2 in
/-- **`lower_conforms_acyclic_cfg` — general acyclic-CFG, `hir` discharged.** As
`lower_conforms_acyclic`, but the IR run is **constructed** for any acyclic gas-free CFG
(`V2.irRun_exists`, from `CFGAcyclic prog` + `RunDefinable prog`) rather than assumed — so no
`hir` hypothesis survives. The world equation is stated against the constructed run's existential
observable `O`. -/
theorem lower_conforms_acyclic_cfg {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hsload : SloadRealises sloadChg { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    (hwf : AcyclicWellFormed prog)
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs (realisedCall log self) L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs (realisedCall log self) self L b)
    -- the program is an acyclic gas-free CFG with the edge-definability supply
    -- (so `hir` builds via `V2.irRun_exists`):
    (hcfg : V2.CFGAcyclic prog)
    (hdef : V2.RunDefinable prog) :
    ∃ O : V2.Observable, O.world = (observe self log.observable).world := by
  obtain ⟨O, hir⟩ :=
    V2.irRun_exists (o := realisedCall log self) (w₀ := w₀) (T := realisedGas log)
      hcfg hdef hbentry
  exact ⟨O, lower_conforms_acyclic hwl hp hmod hentry0 hbentry hbound hstore hsload hgasr hgasj
    hwf hstmtties htermties hir⟩

end Lir

-- Build-enforced axiom-cleanliness guards for the acyclicity→`MatFueled` discharge: the core
-- fuel/rank lemma and the `WellFormedLowered` constructor depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.matFueled_of_exprRankLt
#print axioms Lir.matFueled_tmp_of_acyclic
#print axioms Lir.wellFormedLowered_of_acyclic
#print axioms Lir.lower_conforms_acyclic
#print axioms Lir.lower_conforms_acyclic_stop
#print axioms Lir.lower_conforms_acyclic_stop_canonical
#print axioms Lir.lower_conforms_acyclic_cfg
