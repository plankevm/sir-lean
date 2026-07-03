import LirLean.V2.Law

/-!
# LirLean v2 — IR-run **existence** (the `hir` side of the conformance diagram)

`lower_conforms` carries the IR run `IRRun prog o w₀ T O` as a structured hypothesis
(`hir`): the IR side of the diagram, supplied for the program under study. This module
discharges that hypothesis **constructively** for the call-free fragment as far as
totality is tractable — banking the pieces of the "construct `hir`" milestone
(`docs/lower-conforms-plan.md`, missing scaffolding: *`RunFrom` determinism/totality*).

`RunFrom.det` (`Law.lean`) already gives the *uniqueness* half. This module gives the
**existence** half, bottom-up, mirroring the determinism ladder:

* `EvalStmt` existence — a **gas-free, non-call** statement whose operands are bound steps
  to a definite post-state (`evalStmt_exists`). Gas-free because `assign t .gas` *consumes*
  a trace read, so its existence is gated on the trace being non-empty (a separate, trace-
  threading concern); non-call because `Stmt.call` consults the oracle (handled by the
  call layer). Within that fragment the step is total — it never gets stuck.
* `RunStmts` existence — a **gas-free, call-free** statement list, each statement
  definable at its running state, runs to a definite post-state with the trace unchanged
  (`runStmts_exists`). By induction on the list, threading the post-state.
* `RunFrom`/`IRRun` existence (single halt block) — a program whose **entry block is a halt**
  (`stop` / `ret`), gas-free and call-free, with the `ret` operand bound at the post-statement
  state, has an IR run (`irRun_exists_stop` / `irRun_exists_ret`). The single-block DAG base case
  of the CFG-totality argument: no edges, so no CFG-acyclicity measure is needed.
* `RunFrom`/`IRRun` existence (**general acyclic CFG**) — `runFrom_exists`/`irRun_exists`
  generalise the above to any acyclic call-free gas-free program via a **block topological rank**
  (`CFGAcyclic`, a *control-flow* measure distinct from `Acyclic.lean`'s *def-graph* rank): by
  strong induction on the rank, halts bottom out and `jump`/`branch` recurse at the
  strictly-smaller-rank successor. The state-threaded definability supply is `RunDefinable`. This
  discharges the general `hir` for the call-free/gas-free fragment.

This is the **honest tractable floor** of `hir` construction. What remains (gas-read trace supply
coupling `hir` to the recording) is described in the module-end note.

Frame-free: imports only `LirLean.V2.Law` (hence `Machine`/`IR`/`Evm`) — no `BytecodeLayer`,
no `Frame`, no `Runs`. No `sorry`/`axiom`/`native_decide`.
-/

namespace Lir.V2

open Evm

/-! ## `EvalStmt` existence for the gas-free, non-call fragment

A statement is in the *gas-free, non-call* fragment when it is an `assign t e` with
`e ≠ .gas`, or an `sstore key value`. For such a statement, `EvalStmt` fires to a definite
post-state with the trace **unchanged** (only `assign t .gas` consumes a read), provided the
operands are bound:

* `assign t e` (`e ≠ .gas`): needs `evalExpr st 0 e` defined (`assignPure`);
* `sstore key value`: needs both `key` and `value` bound (`sstore`).

We phrase the operand-definedness as `StmtDefinable st s` and produce the witness post-state. -/

/-- **Operand-definedness of a gas-free, non-call statement at state `st`.** The minimal
side-condition for `EvalStmt` to fire to a definite post-state without consuming a trace read:
an `assign t e` (`e ≠ .gas`) needs `e` to evaluate; an `sstore key value` needs both operands
bound. `assign t .gas` and `call` are out of this fragment (they are `False` here). -/
def StmtDefinable (st : IRState) : Stmt → Prop
  | .assign _ e => e ≠ .gas ∧ ∃ w, evalExpr st 0 e = some w
  | .sstore key value => (∃ kw, st.locals key = some kw) ∧ (∃ vw, st.locals value = some vw)
  | .call _ => False

/-- The post-state a gas-free, non-call definable statement steps to: `assign` binds the
evaluated value; `sstore` writes the cell. (A total function on the fragment; the `call`
case is unreachable under `StmtDefinable` and pinned to `st`.) -/
def stmtPost (st : IRState) : Stmt → IRState
  | .assign t e => st.setLocal t (evalExpr st 0 e |>.getD 0)
  | .sstore key value =>
      st.setStorage (st.locals key |>.getD 0) (st.locals value |>.getD 0)
  | .call _ => st

/-- **`EvalStmt` existence (gas-free, non-call fragment).** A `StmtDefinable` statement
steps to `stmtPost st s` with the trace unchanged. The trace `T` is arbitrary and preserved:
no read is consumed (the only consuming statement, `assign t .gas`, is excluded by
`StmtDefinable`). -/
theorem evalStmt_exists {prog : Program} {o : CallOracle} {st : IRState} {T : Trace}
    {s : Stmt} (hdef : StmtDefinable st s) :
    EvalStmt prog o st T s (stmtPost st s) T := by
  cases s with
  | assign t e =>
    obtain ⟨hne, w, hw⟩ := hdef
    have : stmtPost st (.assign t e) = st.setLocal t w := by
      simp only [stmtPost, hw, Option.getD_some]
    rw [this]
    exact EvalStmt.assignPure hne hw
  | sstore key value =>
    obtain ⟨⟨kw, hk⟩, ⟨vw, hv⟩⟩ := hdef
    have : stmtPost st (.sstore key value) = st.setStorage kw vw := by
      simp only [stmtPost, hk, hv, Option.getD_some]
    rw [this]
    exact EvalStmt.sstore hk hv
  | call cs => exact absurd hdef (by simp [StmtDefinable])

/-! ## `RunStmts` existence for the gas-free, call-free fragment

Threading `stmtPost` through a statement list. The definability of each statement is at its
*running* state, so we phrase it as a fold: `StmtsDefinable st ss` says the head is definable
at `st` and the tail is definable at the head's post-state. The witness final state is the
left fold of `stmtPost`. -/

/-- **List-level definability**, threaded through `stmtPost`: every statement is definable at
the state reached by running the prefix before it. The fold companion of `StmtDefinable`. -/
def StmtsDefinable (st : IRState) : List Stmt → Prop
  | [] => True
  | s :: ss => StmtDefinable st s ∧ StmtsDefinable (stmtPost st s) ss

/-- The final state of running a gas-free, call-free statement list: the left fold of
`stmtPost`. -/
def stmtsPost (st : IRState) : List Stmt → IRState
  | [] => st
  | s :: ss => stmtsPost (stmtPost st s) ss

/-- **`RunStmts` existence (gas-free, call-free fragment).** A `StmtsDefinable` statement list
runs to `stmtsPost st ss` with the trace unchanged. By induction on the list; each head fires
via `evalStmt_exists`, the tail by the IH at the head's post-state. -/
theorem runStmts_exists {prog : Program} {o : CallOracle} {st : IRState} {T : Trace}
    {ss : List Stmt} (hdef : StmtsDefinable st ss) :
    RunStmts prog o st T ss (stmtsPost st ss) T := by
  induction ss generalizing st with
  | nil => exact RunStmts.nil
  | cons s ss ih =>
    obtain ⟨hhead, htail⟩ := hdef
    exact RunStmts.cons (evalStmt_exists hhead) (ih htail)

/-! ## `RunFrom`/`IRRun` existence for a single halting block

The base case of CFG totality: a program whose entry block is a **halt** terminator
(`stop` or `ret t`). No outgoing edges, so the `RunFrom` recursion bottoms out in one
constructor application — no CFG-acyclicity measure is needed. The block's statements run via
`runStmts_exists`; the `ret` arm additionally needs its operand bound at the post-statement
state. -/

/-- **`RunFrom` existence for a `stop`-terminated block.** From a present block `b` whose
statements are gas-free/call-free and definable, and whose terminator is `stop`, `RunFrom`
halts at the post-statement world with `.stopped`. -/
theorem runFrom_exists_stop {prog : Program} {o : CallOracle} {st : IRState} {T : Trace}
    {L : Label} {b : Block}
    (hb : blockAt prog L = some b)
    (hterm : b.term = .stop)
    (hdef : StmtsDefinable st b.stmts) :
    RunFrom prog o st T L { world := (stmtsPost st b.stmts).world, result := .stopped } :=
  RunFrom.stop hb (runStmts_exists hdef) hterm

/-- **`RunFrom` existence for a `ret`-terminated block.** As `runFrom_exists_stop`, with the
`ret t` operand bound at the post-statement state (`hv`); halts returning that value. -/
theorem runFrom_exists_ret {prog : Program} {o : CallOracle} {st : IRState} {T : Trace}
    {L : Label} {b : Block} {t : Tmp} {w : Word}
    (hb : blockAt prog L = some b)
    (hterm : b.term = .ret t)
    (hdef : StmtsDefinable st b.stmts)
    (hv : (stmtsPost st b.stmts).locals t = some w) :
    RunFrom prog o st T L { world := (stmtsPost st b.stmts).world, result := .returned w } :=
  RunFrom.ret hb (runStmts_exists hdef) hterm hv

/-- **`IRRun` existence for a single `stop`-block program.** If the entry block is present,
gas-free/call-free, definable from the empty-locals/`w₀` start, and `stop`-terminated, the
program has an IR run for *any* call oracle `o` and *any* trace `T` — the trace is unconsumed
(no gas reads). The produced observable is `⟨post-world, .stopped⟩`. -/
theorem irRun_exists_stop {prog : Program} {o : CallOracle} {w₀ : World} {T : Trace}
    {bentry : Block}
    (hb : blockAt prog prog.entry = some bentry)
    (hterm : bentry.term = .stop)
    (hdef : StmtsDefinable { locals := fun _ => none, world := w₀ } bentry.stmts) :
    IRRun prog o w₀ T
      { world := (stmtsPost { locals := fun _ => none, world := w₀ } bentry.stmts).world
        result := .stopped } :=
  runFrom_exists_stop hb hterm hdef

/-- **`IRRun` existence for a single `ret`-block program.** As `irRun_exists_stop`, with the
`ret` operand bound at the post-statement state; the observable returns that value. -/
theorem irRun_exists_ret {prog : Program} {o : CallOracle} {w₀ : World} {T : Trace}
    {bentry : Block} {t : Tmp} {w : Word}
    (hb : blockAt prog prog.entry = some bentry)
    (hterm : bentry.term = .ret t)
    (hdef : StmtsDefinable { locals := fun _ => none, world := w₀ } bentry.stmts)
    (hv : (stmtsPost { locals := fun _ => none, world := w₀ } bentry.stmts).locals t = some w) :
    IRRun prog o w₀ T
      { world := (stmtsPost { locals := fun _ => none, world := w₀ } bentry.stmts).world
        result := .returned w } :=
  runFrom_exists_ret hb hterm hdef hv

/-! ## CFG-acyclicity: the *block* topological rank (the DAG measure)

The single-block lemmas above bottom out in one constructor application because a halt block has
no outgoing edges. The general acyclic CFG needs a measure that *strictly decreases across every
control-flow edge*, so the `RunFrom` recursion through `jump`/`branch` is well-founded — the
**block** analogue of `Acyclic.lean`'s **def-graph** rank (this is control flow, not the
recompute-on-use def order; the two are entirely separate orders on a program).

`TermRankLt rank term n` bounds the rank of every successor label of `term` strictly below `n`
(halts have no successors, hence are vacuously fine). `CFGAcyclic prog` packages a
`blockRank : Label → ℕ` under which every present block's terminator satisfies `TermRankLt` below
that block's rank — i.e. taking any edge strictly decreases rank, so the CFG has **no loops**.

This mirrors `Acyclic.lean` verbatim in spirit: `ExprRankLt`/`Acyclic` ↦ `TermRankLt`/`CFGAcyclic`,
the def edge ↦ the control-flow edge. -/

/-- **`TermRankLt rank term n`** — every successor label of `term` ranks strictly below `n`. A
halt (`ret`/`stop`) has no successors (vacuously `True`); `jump dst` needs `rank dst < n`;
`branch _ thenL elseL` needs both targets below `n`. The control-flow analogue of
`Lir.ExprRankLt`. -/
def TermRankLt (rank : Label → ℕ) : Term → ℕ → Prop
  | .ret _, _ => True
  | .stop, _ => True
  | .jump dst, n => rank dst < n
  | .branch _ thenL elseL, n => rank thenL < n ∧ rank elseL < n

/-- The successor labels of a terminator (the control-flow edge targets). A halt has none. -/
def _root_.Lir.Term.succs : Term → List Label
  | .ret _ => []
  | .stop => []
  | .jump dst => [dst]
  | .branch _ thenL elseL => [thenL, elseL]

/-- **`CFGAcyclic prog`** — a topological rank on the *control-flow* graph: every present block's
terminator sends every edge to a strictly-smaller rank, and every edge target is itself a present
block. So following any `jump`/`branch` edge strictly decreases `blockRank` and stays inside the
program, witnessing the CFG is a DAG (NO loops). The control-flow analogue of `Lir.Acyclic`
(which ranks the def-graph). Both single-block example programs satisfy it trivially — a
`stop`/`ret` entry block has no edges, so any `blockRank` works (`TermRankLt` is vacuously `True`
on a halt) and `succ_present` is vacuous. -/
structure CFGAcyclic (prog : Program) where
  /-- A topological rank on the control-flow graph. -/
  blockRank : Label → ℕ
  /-- Every present block's terminator decreases rank across each edge (no loops). -/
  decreasing : ∀ (L : Label) (b : Block),
    blockAt prog L = some b → TermRankLt blockRank b.term (blockRank L)
  /-- Every edge target of a present block is itself a present block (the CFG is closed: no
  dangling jumps). Needed so the `RunFrom` recursion always lands on a runnable block. -/
  succ_present : ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ S ∈ b.term.succs, ∃ b', blockAt prog S = some b'

/-! ## Run-definability: the state-threaded definability supply

`runFrom_exists` runs each block's statements then recurses at the successor with the threaded
post-statement state. To fire it needs, at each block reached, the operand-definedness the
single-block lemmas needed *plus* the branch condition bound at the post-statement state. We
supply this for **every** state (a sound over-approximation of "every reachable state"): the
existence claim is then state-uniform, exactly matching how the former `StmtTies`/`TermTies`
(since reshaped into the run-DERIVED `StmtTies'`/`TermTies'` in `V2/RealisabilitySpec.lean`)
were quantified over all `(L, b)`.

`RunDefinable prog` bundles, for every present block:
* `stmts` — the block's statements are `StmtsDefinable` from any state (the §2 fold);
* `ret_def` — a `ret t` block's operand is bound at the post-statement state;
* `branch_def` — a `branch cond _ _` block's condition is bound at the post-statement state.

`jump`/`stop` need nothing beyond `stmts` (the jump's successor definability is the IH; `stop`
halts). The post-statement state is `stmtsPost st b.stmts`, threaded from the caller's `st`. -/

/-- **`RunDefinable prog`** — the state-uniform definability supply that lets `RunFrom` fire at
every present block: statements `StmtsDefinable` from any state, plus the halt/branch operands
bound at the post-statement state. Quantified over all states (a sound over-approximation of the
reachable ones), matching the all-`(L,b)` quantification of the §7 ties. -/
structure RunDefinable (prog : Program) where
  /-- Every present block's statements are `StmtsDefinable` from any starting state. -/
  stmts : ∀ (st : IRState) (L : Label) (b : Block),
    blockAt prog L = some b → StmtsDefinable st b.stmts
  /-- A `ret t` block's operand is bound at its post-statement state, from any start. -/
  ret_def : ∀ (st : IRState) (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    ∃ w, (stmtsPost st b.stmts).locals t = some w
  /-- A `branch cond _ _` block's condition is bound at its post-statement state, from any start.
  (The 0-vs-nonzero split — which edge is taken — is decided inside `runFrom_exists`.) -/
  branch_def : ∀ (st : IRState) (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    ∃ cw, (stmtsPost st b.stmts).locals cond = some cw

/-! ## `RunFrom`/`IRRun` existence for a general acyclic CFG

By strong induction on `blockRank L`. At block `L` (present, `b`): run the statements via
`runStmts_exists` to `stmtsPost st b.stmts`, then case on the terminator:

* `stop` / `ret t` — halt (base case, one constructor, no recursion);
* `jump dst` — `CFGAcyclic.decreasing` gives `blockRank dst < blockRank L`, so the strong-IH
  applies at `dst` with the threaded post-state, yielding the tail run;
* `branch cond thenL elseL` — the condition is bound (`RunDefinable.branch_def`); split on
  `cw = 0` and recurse via the strong-IH at the taken edge (`elseL` if `0`, else `thenL`), each
  strictly smaller by `decreasing`.

The trace is unchanged throughout (gas-free fragment: `runStmts_exists` preserves it). -/

/-- **`RunFrom` existence for a general acyclic CFG.** From any state `st` and a *present* label
`L` of an acyclic call-free gas-free program with the run-definability supply, the block at `L`
runs to *some* observable `O`. By strong induction on `blockRank L`: halts bottom out;
`jump`/`branch` recurse at the strictly-smaller-rank, still-present successor
(`CFGAcyclic.decreasing` + `succ_present`). The observable is existential (it depends on the
dynamic branch choices), not a closed form. The trace `T` is threaded unchanged (gas-free). -/
theorem runFrom_exists {prog : Program} {o : CallOracle}
    (hac : CFGAcyclic prog) (hdef : RunDefinable prog) :
    ∀ (n : ℕ) (st : IRState) (T : Trace) (L : Label) (b : Block),
      blockAt prog L = some b → hac.blockRank L = n →
      ∃ O, RunFrom prog o st T L O := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro st T L b hb hrank
    -- Run this block's statements (gas-free/call-free, definable from any state).
    have hss := runStmts_exists (prog := prog) (o := o) (T := T) (hdef.stmts st L b hb)
    set st' := stmtsPost st b.stmts with hst'
    -- Case on the terminator.
    cases hterm : b.term with
    | stop =>
      exact ⟨{ world := st'.world, result := .stopped }, RunFrom.stop hb hss hterm⟩
    | ret t =>
      obtain ⟨w, hv⟩ := hdef.ret_def st L b t hb hterm
      exact ⟨{ world := st'.world, result := .returned w }, RunFrom.ret hb hss hterm hv⟩
    | jump dst =>
      -- `dst` is present and strictly smaller rank.
      have hlt : hac.blockRank dst < hac.blockRank L := by
        have := hac.decreasing L b hb; rw [hterm] at this; exact this
      obtain ⟨b', hb'⟩ := hac.succ_present L b hb dst (by simp [hterm, Term.succs])
      obtain ⟨O, hO⟩ :=
        ih (hac.blockRank dst) (hrank ▸ hlt) st' T dst b' hb' rfl
      exact ⟨O, RunFrom.jump hb hss hterm hO⟩
    | branch cond thenL elseL =>
      obtain ⟨cw, hc⟩ := hdef.branch_def st L b cond thenL elseL hb hterm
      have hdec := hac.decreasing L b hb
      rw [hterm] at hdec
      obtain ⟨hltThen, hltElse⟩ := hdec
      obtain ⟨bT, hbT⟩ := hac.succ_present L b hb thenL (by simp [hterm, Term.succs])
      obtain ⟨bE, hbE⟩ := hac.succ_present L b hb elseL (by simp [hterm, Term.succs])
      by_cases hz : cw = 0
      · -- else-edge
        obtain ⟨O, hO⟩ :=
          ih (hac.blockRank elseL) (hrank ▸ hltElse) st' T elseL bE hbE rfl
        exact ⟨O, RunFrom.branchElse hb hss hterm (hz ▸ hc) hO⟩
      · -- then-edge
        obtain ⟨O, hO⟩ :=
          ih (hac.blockRank thenL) (hrank ▸ hltThen) st' T thenL bT hbT rfl
        exact ⟨O, RunFrom.branchThen hb hss hterm hc hz hO⟩

/-- **`IRRun` existence for a general acyclic CFG** (the general `hir` discharge). An acyclic,
call-free, gas-free program with a present entry block and the run-definability supply has an IR
run for *any* call oracle `o` and *any* trace `T` (the trace is unconsumed — no gas reads). The
observable is existential. Specialises `runFrom_exists` at the entry block from the
empty-locals/`w₀` start. -/
theorem irRun_exists {prog : Program} {o : CallOracle} {w₀ : World} {T : Trace}
    {bentry : Block}
    (hac : CFGAcyclic prog) (hdef : RunDefinable prog)
    (hb : blockAt prog prog.entry = some bentry) :
    ∃ O, IRRun prog o w₀ T O :=
  runFrom_exists hac hdef (hac.blockRank prog.entry)
    { locals := fun _ => none, world := w₀ } T prog.entry bentry hb rfl

/-! ## Remaining work for fully general `hir` construction (precise)

The acyclic CFG case is now closed (`runFrom_exists`/`irRun_exists`). What remains for the *fully*
general `hir = IRRun … (realisedGas log) …`:

1. **Gas-read supply** — `assign t .gas` consumes a trace read, so a program with gas reads needs
   the trace `T` to carry exactly one read per `gas` assign reached, in order. The gas-free
   fragment here sidesteps this (`RunDefinable` excludes `assign t .gas` via `StmtDefinable`); the
   general case threads `T` through the fold (each `gas` assign popping the head), and `hir`'s
   trace must be `realisedGas log` — tying totality to the **recorded** read count, i.e. to the
   forward-simulation correspondence. This couples `hir`'s trace to the recording, so the fully
   general `hir` is *not* independent of the recording-correspondence; it shares the bytecode↔IR
   alignment blocker (see `LowerConforms.lean`).
2. **Reachable-state definability** — `RunDefinable` is quantified over *all* states (a sound
   over-approximation). Tightening it to the *reachable* states (the ones actually threaded along
   the run) would weaken the hypothesis but needs a reachability predicate over the CFG; the
   all-states form is the honest, immediately-usable version and matches the §7 ties' shape. -/

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the IR-run existence ladder: the gas-free,
-- call-free `EvalStmt`/`RunStmts`/`RunFrom`/`IRRun` existence lemmas (single-block and the
-- general acyclic-CFG case) depend only on `[propext, Classical.choice, Quot.sound]`.
