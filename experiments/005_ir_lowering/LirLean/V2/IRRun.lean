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
* `RunFrom`/`IRRun` existence — a program whose **entry block is a halt** (`stop` / `ret`),
  gas-free and call-free, with the `ret` operand bound at the post-statement state, has an
  IR run (`irRun_exists_halt` / `irRun_exists_stop`). The single-block DAG base case of
  the CFG-totality argument: no edges, so no CFG-acyclicity measure is needed.

This is the **honest tractable floor** of `hir` construction. The general multi-block case
needs a CFG-acyclicity measure (a *block* topological rank, distinct from the *def-graph*
rank of `Acyclic.lean`) to bound the `RunFrom` recursion through `jump`/`branch`; that
measure does not yet exist in the development. See the module-end note for the precise
remaining work.

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

/-! ## Remaining work for general `hir` construction (precise)

The multi-block case needs, in addition to the above:

1. **A CFG-acyclicity measure** — a `blockRank : Label → ℕ` strictly decreasing across every
   `jump`/`branch` edge (`blockRank succ < blockRank L` for each successor of `L`). This is the
   *block* analogue of `Acyclic.lean`'s *def-graph* rank, and it is **not** in the development.
   It would bound the `RunFrom` recursion: existence by strong induction on `blockRank L`.
2. **Edge-target definability** — at each edge, the successor block's statements are definable
   from the post-statement state (the threaded `StmtsDefinable` across the edge), and the
   branch condition is bound (`branch cond _ _` needs `(stmtsPost …).locals cond` defined).
3. **Gas-read supply** — `assign t .gas` consumes a trace read, so a program with gas reads
   needs the trace `T` to carry exactly one read per `gas` assign reached, in order. The
   gas-free fragment above sidesteps this; the general case threads `T` through the fold
   (each `gas` assign popping the head), and `hir`'s trace must be `realisedGas log` — tying
   totality to the **recorded** read count, i.e. to the forward-simulation correspondence.

Items (1)–(2) are a self-contained CFG-totality development (a new `blockRank` predicate +
strong-induction existence). Item (3) couples `hir`'s trace to the recording, so the fully
general `hir = IRRun … (realisedGas log) …` is *not* independent of the recording-
correspondence — it shares the bytecode↔IR alignment blocker (see `LowerConforms.lean`). -/

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the IR-run existence ladder: the gas-free,
-- call-free `EvalStmt`/`RunStmts`/`RunFrom`/`IRRun` existence lemmas depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.V2.evalStmt_exists
#print axioms Lir.V2.runStmts_exists
#print axioms Lir.V2.runFrom_exists_stop
#print axioms Lir.V2.runFrom_exists_ret
#print axioms Lir.V2.irRun_exists_stop
#print axioms Lir.V2.irRun_exists_ret
