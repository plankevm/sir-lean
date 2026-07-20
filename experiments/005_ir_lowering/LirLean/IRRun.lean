import LirLean.Law

/-!
# LirLean — IR-run existence bricks (the gas-free, call-free statement ladder)

`lower_conforms` carries the IR run `IRRun prog o w₀ T O` as a structured hypothesis
(`hir`). `RunFrom.det` (`Law.lean`) is the *uniqueness* half of discharging it; this
module banks the *existence-side* statement-level bricks for the **gas-free,
call-free fragment**:

* `EvalStmt` existence — a **gas-free, non-call** statement whose operands are bound
  (`StmtDefinable`) steps to the definite post-state `stmtPost`, trace unchanged
  (`evalStmt_exists`). Gas-free because `assign t .gas` *consumes* a trace read, so
  its existence is gated on the trace being non-empty (a separate, trace-threading
  concern); non-call because `Stmt.call` consults the oracle (handled by the call
  layer). Within the fragment the step is total — it never gets stuck.
* `RunStmts` existence — a **gas-free, call-free** statement list, each statement
  definable at its running state (`StmtsDefinable`), runs to the `stmtPost` fold
  `stmtsPost` with the trace unchanged (`runStmts_exists`).
* `RunDefinable` — the state-uniform definability supply (every block's statements
  definable from any state, halt/branch operands bound at the post-statement state).
  NOTE its scope: quantifying over *all* states makes it **unsatisfiable for gas/call
  programs** (see the audit header of `Realisability/RealisabilitySpec.lean`, lesson
  4); the flagship path instead uses the gas/call-aware `RunDefinableG`
  (`Spec/WellFormed.lean`). Its remaining consumer is the superseded drive-walk chain
  (`Drive/DriveSim.lean`), off the flagship path.

Historical note: the block/CFG-level existence theorems this module once carried
(`irRun_exists_stop`/`irRun_exists_ret`, `runFrom_exists`/`irRun_exists` over acyclic
CFGs via `CFGAcyclic`) were retired; what remains here is the statement-level ladder
plus the `RunDefinable` supply.

Frame-free: imports only `LirLean.Law` (hence `Machine`/`IR`/`Evm`) — no `BytecodeLayer`,
no `Frame`, no `Runs`. No `sorry`/`axiom`/`native_decide`.
-/

namespace Lir

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
    {D : CreateStream} {s : Stmt} (hdef : StmtDefinable st s) :
    EvalStmt prog st T C D s (stmtPost st s) T C D := by
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
    {D : CreateStream} {ss : List Stmt} (hdef : StmtsDefinable st ss) :
    RunStmts prog st T C D ss (stmtsPost st ss) T C D := by
  induction ss generalizing st with
  | nil => exact RunStmts.nil
  | cons s ss ih =>
    obtain ⟨hhead, htail⟩ := hdef
    exact RunStmts.cons (evalStmt_exists hhead) (ih htail)

/-! ## Run-definability: the state-threaded definability supply

The cyclic drive walk (`DriveSim.lean`) runs each block's statements then continues at the
successor with the threaded post-statement state. To fire it needs, at each block reached, the
operand-definedness of the statement fold *plus* the branch condition bound at the post-statement
state. We
supply this for **every** state (a sound over-approximation of "every reachable state"): the
existence claim is then state-uniform, exactly matching how the former `StmtTies`/`TermTies`
(since reshaped into the run-DERIVED `StmtTies'`/`TermTies'` in `Realisability/RealisabilitySpec.lean`)
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
drive simulation (`DriveSim.lean`). -/
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

end Lir

-- Build-enforced axiom-cleanliness guards for the IR-run definability ladder: the gas-free,
-- call-free `EvalStmt`/`RunStmts` existence lemmas and the `RunDefinable` supply depend only on
-- `[propext, Classical.choice, Quot.sound]`.
