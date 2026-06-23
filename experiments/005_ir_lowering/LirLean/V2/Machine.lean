import LirLean.IR
import Evm

/-!
# LirLean v2 — the gas-free, observable IR machine (call-free prototype)

This is the **call-free v2 prototype** (`docs/ir-design-v2.md` §6 step 1). It
validates the v2 theorem shape — gas-free machine + observable boundary + the
event trace — at low cost, *before* anyone ports `workedCall`'s external call.

Design decisions taken from `ir-design-v2.md`, verbatim:

* **No gas counter, no pc** (§3.1). `IRState` is `{ locals, world }`. The IR never
  mentions `Frame`, `gasAvailable`, or `pc`.
* **`World` is IR-native** (§3.1). For the call-free C1 scope it is exactly the
  self-account storage lens `Word → Word` — the same projection v1's
  `IRState.storage` carried, and the same `selfStorage`/`storageAt` lens the
  bytecode side reads (`LirLean/Match.lean`). The abstraction lens to a `Frame`
  is *not* part of the IR; it lives in the preservation proof.
* **The event trace** (§3.3–3.4). `Event` here has only `gasRead (observed)`; the
  `call` constructor is out of scope for the call-free prototype. `Expr.gas`
  **consumes** the next `gasRead` event — gas is an *observed value the run
  supplies*, NEVER a counter, NEVER opcode-cost accounting. There is deliberately
  no `matCost`/`gVerylow`/charge logic anywhere in v2.

Contrast with v1 (`LirLean/SmallStep.lean`), which is gas-aware: `IRState.gas`,
`IRState.charge`, `matCost`, and `evalExpr`'s `.gas := ofUInt64 st.gas`. v1 stays
green untouched as the reference.
-/

namespace Lir.V2

open Evm

/-! ## The observable machine state (no gas, no pc) -/

/-- The IR-native observable world. For the call-free prototype this is exactly
the self account's storage, read through the observable lens (`find?/lookupStorage`
on the bytecode side). A later step generalises this to a per-account map; the
theorem shape does not depend on the choice. -/
abbrev World := Word → Word

/-- The gas-free IR machine state: a register file and the observable world.
**No gas, no pc** (`ir-design-v2.md` §3.1). -/
structure IRState where
  /-- Register file: each temporary's bound value (if assigned). -/
  locals : Tmp → Option Word
  /-- The observable world (self-account storage lens). -/
  world  : World

/-- An IR halt result — the terminator outcomes (revert is out of scope, §7). -/
inductive IRHalt where
  /-- `STOP` — success, no output word. -/
  | stopped
  /-- `RETURN t` — success returning the word `t` evaluated to. -/
  | returned (w : Word)
deriving DecidableEq, Repr

/-! ## The event trace (§3.3–3.4)

`Event` is the unified sequence of *things the IR observes but does not model*.
For the call-free prototype the only constructor is `gasRead`; the `call`
constructor is added in the next migration step. -/

/-- An observed event the run supplies. `gasRead observed` is the word a `GAS`
opcode reports — an **observed value**, never a counter. -/
inductive Event where
  /-- The value a `GAS` opcode reports (gas introspection without accounting). -/
  | gasRead (observed : Word)
deriving DecidableEq, Repr

/-- The event trace threaded through an IR run. -/
abbrev Trace := List Event

/-! ## Helpers on `IRState` -/

/-- Bind a temporary to a value. -/
def IRState.setLocal (st : IRState) (t : Tmp) (w : Word) : IRState :=
  { st with locals := fun t' => if t' = t then some w else st.locals t' }

/-- Write a storage cell of the observable world. -/
def IRState.setStorage (st : IRState) (k v : Word) : IRState :=
  { st with world := fun k' => if k' = k then v else st.world k' }

/-! ## Expression evaluation (gas-free, event-threaded)

`evalExpr st obs e` evaluates `e` to a word in state `st`, where `obs` is the
observed-gas value to use *if* `e` is (or recurses through) `Expr.gas`. The
prototype's expressions are flat (operands are `tmp`s, by the recompute-on-use
lowering), so an expression mentions `gas` at most directly; we pass the single
observed value rather than threading a sub-trace. The arithmetic mirrors v1 /
exp003 (`UInt256.add`, `UInt256.lt`, the storage lens) so the IR value is
*definitionally* the lowered opcode's. **No gas counter appears.** -/

/-- Evaluate an expression. `obs` is the observed-gas word a `gasRead` event
supplies (used only by `Expr.gas`). Total via `Option` (`none` = undefined tmp). -/
def evalExpr (st : IRState) (obs : Word) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.world key)
  | .gas     => some obs

/-! ## Block accessor

`blockAt prog L` is the block at label `L` (if present) — the same projection as
v1's `Lir.Program.blockAt`, kept v2-local so this module depends only on
`IR.lean` (not the gas-aware `SmallStep.lean`). -/

/-- The block at label `L`, if present. -/
def blockAt (prog : Program) (L : Label) : Option Block :=
  prog.blocks[L.idx]?

/-! ## The gas-free big-step semantics

A big-step relation (simpler than small-step for the prototype, §3, "your call").
Three judgements, all threading a `Trace` left-to-right:

* `EvalStmt` — one statement maps `(st, T) → (st', T')`, consuming a `gasRead`
  event iff the statement's expression is `Expr.gas`. (The call-free fragment has
  only `assign`/`sstore`; `Stmt.call` is rejected — out of scope.)
* `RunStmts` — the reflexive/transitive closure over a statement list.
* `IRRun` — the CFG driver: run the entry block's statements, then its terminator;
  `branch`/`jump` recurse into the target block; `ret`/`stop` halt with an
  `Observable`.

An `assign t e` consuming the `gasRead obs` event happens exactly when `e = .gas`;
otherwise the trace is unchanged. This is the §3.4 event mechanism: the value of
`Expr.gas` is *drawn from the trace*, asserted nothing about. -/

/-- The trace event a statement consumes, and the resulting state. The only
trace-consuming statement is `assign t .gas`, which pops one `gasRead obs` and
binds `t := obs`. All other `assign`/`sstore` leave the trace unchanged. -/
inductive EvalStmt (prog : Program) : IRState → Trace → Stmt → IRState → Trace → Prop where
  /-- `t := e` for a **non-gas** expression `e`: evaluate `e` (no event), bind `t`.
  The `obs` argument of `evalExpr` is irrelevant here (it is only read by `.gas`),
  so we pin it to `0`. -/
  | assignPure {st : IRState} {T : Trace} {t : Tmp} {e : Expr} {w : Word}
      (hne : e ≠ .gas) (hv : evalExpr st 0 e = some w) :
      EvalStmt prog st T (.assign t e) (st.setLocal t w) T
  /-- `t := gas`: consume the next `gasRead obs` event, bind `t := obs`. -/
  | assignGas {st : IRState} {obs : Word} {T : Trace} {t : Tmp} :
      EvalStmt prog st (.gasRead obs :: T) (.assign t .gas) (st.setLocal t obs) T
  /-- `storage[key] := value` (non-zero value — the observable write the bytecode
  side establishes). -/
  | sstore {st : IRState} {T : Trace} {key value : Tmp} {kw vw : Word}
      (hk : st.locals key = some kw) (hv : st.locals value = some vw) :
      EvalStmt prog st T (.sstore key value) (st.setStorage kw vw) T

/-- Run a statement list left-to-right, threading the trace. -/
inductive RunStmts (prog : Program) : IRState → Trace → List Stmt → IRState → Trace → Prop where
  | nil {st : IRState} {T : Trace} : RunStmts prog st T [] st T
  | cons {st st' st'' : IRState} {T T' T'' : Trace} {s : Stmt} {ss : List Stmt}
      (hh : EvalStmt prog st T s st' T') (ht : RunStmts prog st' T' ss st'' T'') :
      RunStmts prog st T (s :: ss) st'' T''

/-! ### The observable boundary (§4) -/

/-- The observable boundary of a finished IR run: the final world and the halt
result. **No gas, no pc.** (`ir-design-v2.md` §4.) -/
structure Observable where
  /-- The final observable world (the storage delta, as the post-run lens). -/
  worldDelta : World
  /-- The halt result (`stop`/`return`). -/
  result     : IRHalt

/-- The CFG big-step driver. `IRRun prog w₀ T O`: starting at `prog.entry` with
empty locals and world `w₀`, consuming the whole trace `T`, the program halts with
observable `O`. The terminators:

* `ret t` halts with `returned (the value of t)`;
* `stop` halts with `stopped`;
* `branch cond thenL elseL` recurses into `thenL` if `cond ≠ 0`, else `elseL`;
* `jump dst` recurses into `dst`.

`branch`/`jump` are bounded by the program's acyclic shape in the prototype (the
example program's blocks form a DAG), so the inductive relation is well-founded by
construction at use sites — no fuel parameter is threaded. -/
inductive RunFrom (prog : Program) : IRState → Trace → Label → Observable → Prop where
  /-- `ret t`: run the block's statements, then halt returning `t`'s value. -/
  | ret {st st' : IRState} {T T' : Trace} {L : Label} {b : Block} {t : Tmp} {w : Word}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T b.stmts st' T')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFrom prog st T L { worldDelta := st'.world, result := .returned w }
  /-- `stop`: run the block's statements, then halt. -/
  | stop {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T b.stmts st' T')
      (hterm : b.term = .stop) :
      RunFrom prog st T L { worldDelta := st'.world, result := .stopped }
  /-- `branch cond thenL elseL`, condition non-zero ⇒ recurse into `thenL`. -/
  | branchThen {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      {cond : Tmp} {cw : Word} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T b.stmts st' T')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some cw) (hnz : cw ≠ 0)
      (hrest : RunFrom prog st' T' thenL O) :
      RunFrom prog st T L O
  /-- `branch cond thenL elseL`, condition zero ⇒ recurse into `elseL`. -/
  | branchElse {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      {cond : Tmp} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T b.stmts st' T')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some 0)
      (hrest : RunFrom prog st' T' elseL O) :
      RunFrom prog st T L O
  /-- `jump dst` ⇒ recurse into `dst`. -/
  | jump {st st' : IRState} {T T' : Trace} {L : Label} {b : Block} {dst : Label}
      {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T b.stmts st' T')
      (hterm : b.term = .jump dst)
      (hrest : RunFrom prog st' T' dst O) :
      RunFrom prog st T L O

/-- **The top-level gas-free IR run** (`ir-design-v2.md` §4). Start at `prog.entry`
with empty locals and world `w₀`, consume the whole trace `T`, halt with `O`. -/
def IRRun (prog : Program) (w₀ : World) (T : Trace) (O : Observable) : Prop :=
  RunFrom prog { locals := fun _ => none, world := w₀ } T prog.entry O

end Lir.V2
