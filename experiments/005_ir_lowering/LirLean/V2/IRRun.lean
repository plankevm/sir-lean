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
  | .create _ => False

/-- The post-state a gas-free, non-call definable statement steps to: `assign` binds the
evaluated value; `sstore` writes the cell. (A total function on the fragment; the `call`
case is unreachable under `StmtDefinable` and pinned to `st`.) -/
def stmtPost (st : IRState) : Stmt → IRState
  | .assign t e => st.setLocal t (evalExpr st 0 e |>.getD 0)
  | .sstore key value =>
      st.setStorage (st.locals key |>.getD 0) (st.locals value |>.getD 0)
  | .call _ => st
  | .create _ => st

/-- **`EvalStmt` existence (gas-free, non-call fragment).** A `StmtDefinable` statement
steps to `stmtPost st s` with the trace unchanged. The trace `T` is arbitrary and preserved:
no read is consumed (the only consuming statement, `assign t .gas`, is excluded by
`StmtDefinable`). -/
theorem evalStmt_exists {prog : Program} {st : IRState} {T : Trace} {C : CallStream}
    {s : Stmt} (hdef : StmtDefinable st s) :
    EvalStmt prog st T C s (stmtPost st s) T C := by
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
  | create cs => exact absurd hdef (by simp [StmtDefinable])

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
theorem runStmts_exists {prog : Program} {st : IRState} {T : Trace} {C : CallStream}
    {ss : List Stmt} (hdef : StmtsDefinable st ss) :
    RunStmts prog st T C ss (stmtsPost st ss) T C := by
  induction ss generalizing st with
  | nil => exact RunStmts.nil
  | cons s ss ih =>
    obtain ⟨hhead, htail⟩ := hdef
    exact RunStmts.cons (evalStmt_exists hhead) (ih htail)

/-! ## Run-definability: the state-threaded definability supply

The cyclic drive walk (`V2/DriveSim.lean`) runs each block's statements then continues at the
successor with the threaded post-statement state. To fire it needs, at each block reached, the
operand-definedness of the statement fold *plus* the branch condition bound at the post-statement
state. We
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
reachable ones), matching the all-`(L,b)` quantification of the §7 ties. Consumed by the cyclic
drive simulation (`V2/DriveSim.lean`). -/
structure RunDefinable (prog : Program) where
  /-- Every present block's statements are `StmtsDefinable` from any starting state. -/
  stmts : ∀ (st : IRState) (L : Label) (b : Block),
    blockAt prog L = some b → StmtsDefinable st b.stmts
  /-- A `ret t` block's operand is bound at its post-statement state, from any start. -/
  ret_def : ∀ (st : IRState) (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    ∃ w, (stmtsPost st b.stmts).locals t = some w
  /-- A `branch cond _ _` block's condition is bound at its post-statement state, from any start.
  (The 0-vs-nonzero split — which edge is taken — is decided by the drive walk.) -/
  branch_def : ∀ (st : IRState) (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    ∃ cw, (stmtsPost st b.stmts).locals cond = some cw

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the IR-run definability ladder: the gas-free,
-- call-free `EvalStmt`/`RunStmts` existence lemmas and the `RunDefinable` supply depend only on
-- `[propext, Classical.choice, Quot.sound]`.
