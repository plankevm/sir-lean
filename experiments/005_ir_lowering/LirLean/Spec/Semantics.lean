import LirLean.Spec.IR
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
* **The gas stream** (§3.3–3.4, `ir-design-v3.md` §8). `GasOracle := List Word` —
  the `Word`s a `GAS` opcode reports, consumed in order. `Expr.gas` **consumes**
  the next gas read — gas is an *observed value the run supplies*, NEVER a counter,
  NEVER opcode-cost accounting. (Calls are a function oracle, not stream entries,
  so the stream carries only gas reads — no `Event` wrapper.) There is deliberately
  no `matCost`/`gVerylow`/charge logic anywhere in v2.

v1 (`LirLean/SmallStep.lean`) is the bytecode-coupled reference line: also gas-free
(no IR cost accounting), it carries `IRState.storage`/`locals`/`callResult` and the
`Match`/`sim_*` simulation bricks against exp003's `Runs`. Its `evalExpr` has no
value for `Expr.gas` (no counter to read); here `Expr.gas` is supplied by the gas
stream. v1 stays green as the bytecode-side reference.
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

/-! ## The gas oracle (§7–§8, `docs/ir-design-v3.md`)

Calls became a **function oracle** (`CallOracle`, below), so they are no longer
trace entries; the only thing the run still *consumes as a stream* is the gas-read
sequence. There is nothing left to wrap: the gas trace is exactly the list of the
`Word`s a `GAS` opcode reports, consumed in order (`ir-design-v3.md` §8). The old
`Event`/`Trace` wrapper was pure dead weight and has been collapsed away. -/

/-- The supplied gas-read stream: the `Word`s a `GAS` opcode reports, in program
order, consumed head-first as execution reaches each `GAS`. **An observed value
sequence, never a counter** (`ir-design-v3.md` §8). Zero IR-visible inputs. -/
abbrev GasOracle := List Word

/-- The gas stream threaded through an IR run. Thin alias for `GasOracle` kept so
the many `T : Trace` signatures below read as before; the canonical name in new and
signature positions is `GasOracle`, and the element type is `Word`. -/
abbrev Trace := GasOracle

/-! ## The external-call oracle (§3, §7 — SETTLED)

A call is **not** a trace entry. It is a **function oracle** of the call's IR-visible
inputs, *queried at the call site*, returning the bundle the semantics **applies as a
state change** (`docs/ir-design-v3.md` §7). This is the supplied-observation model for
chain state, exactly mirroring how the gas sequence supplies the gas counter the IR
deliberately lacks.

Minimal value-free / calldata-free first cut (§6 decision 3): the oracle takes the
callee address word, the gas-to-forward word, and the current `World`, and returns the
post-call `World` together with the `0`/`1` success flag. **Gas-free**: there is no
restored-gas field — V2 has no gas in state, so post-call gas reads come from the gas
sequence, not the bundle (§7). Returndata / value / calldata are deferred (§7).

It is held abstract — a PARAMETER threaded through the run, never instantiated here. The
v1 `evmCallOracle` instantiation (the realisability witness) is a later piece. -/
abbrev CallOracle := Word → Word → World → (World × Word)

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

/-- Evaluate an expression. `obs` is the observed-gas word a gas read
supplies (used only by `Expr.gas`). Total via `Option` (`none` = undefined tmp). -/
def evalExpr (st : IRState) (obs : Word) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.world key)
  | .gas     => some obs
  | .slot _ => none

/-! ## Block accessor

`blockAt prog L` is the block at label `L` (if present) — the same projection as
v1's `Lir.Program.blockAt`, kept v2-local so this module depends only on
`Spec/IR.lean` (not the gas-aware `SmallStep.lean`). -/

/-- The block at label `L`, if present. -/
def blockAt (prog : Program) (L : Label) : Option Block :=
  prog.blocks[L.idx]?

/-! ## The gas-free big-step semantics

A big-step relation (simpler than small-step for the prototype, §3, "your call").
Three judgements, all threading a `Trace` left-to-right:

* `EvalStmt` — one statement maps `(st, T) → (st', T')`, consuming the next gas read
  iff the statement's expression is `Expr.gas`. (The call-free fragment has
  only `assign`/`sstore`; `Stmt.call` is rejected — out of scope.)
* `RunStmts` — the reflexive/transitive closure over a statement list.
* `IRRun` — the CFG driver: run the entry block's statements, then its terminator;
  `branch`/`jump` recurse into the target block; `ret`/`stop` halt with an
  `Observable`.

An `assign t e` consuming a gas read happens exactly when `e = .gas`;
otherwise the stream is unchanged. This is the §3.4 mechanism: the value of
`Expr.gas` is *drawn from the gas stream*, asserted nothing about.

The call oracle `o : CallOracle` is a separate explicit parameter (alongside `prog` and
distinct from the gas stream): the gas channel is the consumed read sequence, the call
channel is a queried function. A `Stmt.call` consults `o` at the call site and applies
the returned `(world', success)` bundle as a state change — it does **not** touch the
stream (calls are not stream entries, §7). -/

/-- The gas read a statement consumes, and the resulting state, under the call oracle
`o`. The only stream-consuming statement is `assign t .gas`, which pops one read `obs`
and binds `t := obs`. `Stmt.call` queries `o` and applies its bundle (no stream change).
All other `assign`/`sstore` leave the stream unchanged. -/
inductive EvalStmt (prog : Program) (o : CallOracle) :
    IRState → Trace → Stmt → IRState → Trace → Prop where
  /-- `t := e` for a **non-gas** expression `e`: evaluate `e` (no event), bind `t`.
  The `obs` argument of `evalExpr` is irrelevant here (it is only read by `.gas`),
  so we pin it to `0`. -/
  | assignPure {st : IRState} {T : Trace} {t : Tmp} {e : Expr} {w : Word}
      (hne : e ≠ .gas) (hv : evalExpr st 0 e = some w) :
      EvalStmt prog o st T (.assign t e) (st.setLocal t w) T
  /-- `t := gas`: consume the next gas read `obs` from the stream, bind `t := obs`. -/
  | assignGas {st : IRState} {obs : Word} {T : Trace} {t : Tmp} :
      EvalStmt prog o st (obs :: T) (.assign t .gas) (st.setLocal t obs) T
  /-- `storage[key] := value` (non-zero value — the observable write the bytecode
  side establishes). -/
  | sstore {st : IRState} {T : Trace} {key value : Tmp} {kw vw : Word}
      (hk : st.locals key = some kw) (hv : st.locals value = some vw) :
      EvalStmt prog o st T (.sstore key value) (st.setStorage kw vw) T
  /-- `call cs`: read the callee and gas-to-forward words from `locals` (an undefined
  tmp ⇒ the rule does not fire, mirroring `sstore`), query the oracle
  `o calleeW gasFwdW st.world = (world', success)`, and apply the bundle as a state
  change: set `world := world'` and bind the success flag at `cs.resultTmp` if present.
  Gas-free (no gas notion touched) and trace-preserving (calls are not events, §7). -/
  | call {st : IRState} {T : Trace} {cs : CallSpec} {calleeW gasFwdW success : Word}
      {world' : World}
      (hcallee : st.locals cs.callee = some calleeW)
      (hgas : st.locals cs.gasFwd = some gasFwdW)
      (ho : o calleeW gasFwdW st.world = (world', success)) :
      EvalStmt prog o st T (.call cs)
        (match cs.resultTmp with
          | some t => { st with world := world' }.setLocal t success
          | none   => { st with world := world' })
        T

/-- Run a statement list left-to-right, threading the trace, under the call oracle `o`. -/
inductive RunStmts (prog : Program) (o : CallOracle) :
    IRState → Trace → List Stmt → IRState → Trace → Prop where
  | nil {st : IRState} {T : Trace} : RunStmts prog o st T [] st T
  | cons {st st' st'' : IRState} {T T' T'' : Trace} {s : Stmt} {ss : List Stmt}
      (hh : EvalStmt prog o st T s st' T') (ht : RunStmts prog o st' T' ss st'' T'') :
      RunStmts prog o st T (s :: ss) st'' T''

/-! ### The observable boundary (§4) -/

/-- The observable boundary of a finished IR run: the final world and the halt
result. **No gas, no pc.** (`ir-design-v2.md` §4.) -/
structure Observable where
  /-- The final observable world (the full final storage, as the post-run lens). -/
  world  : World
  /-- The halt result (`stop`/`return`). -/
  result : IRHalt

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
inductive RunFrom (prog : Program) (o : CallOracle) :
    IRState → Trace → Label → Observable → Prop where
  /-- `ret t`: run the block's statements, then halt returning `t`'s value. -/
  | ret {st st' : IRState} {T T' : Trace} {L : Label} {b : Block} {t : Tmp} {w : Word}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFrom prog o st T L { world := st'.world, result := .returned w }
  /-- `stop`: run the block's statements, then halt. -/
  | stop {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .stop) :
      RunFrom prog o st T L { world := st'.world, result := .stopped }
  /-- `branch cond thenL elseL`, condition non-zero ⇒ recurse into `thenL`. -/
  | branchThen {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      {cond : Tmp} {cw : Word} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some cw) (hnz : cw ≠ 0)
      (hrest : RunFrom prog o st' T' thenL O) :
      RunFrom prog o st T L O
  /-- `branch cond thenL elseL`, condition zero ⇒ recurse into `elseL`. -/
  | branchElse {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      {cond : Tmp} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some 0)
      (hrest : RunFrom prog o st' T' elseL O) :
      RunFrom prog o st T L O
  /-- `jump dst` ⇒ recurse into `dst`. -/
  | jump {st st' : IRState} {T T' : Trace} {L : Label} {b : Block} {dst : Label}
      {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .jump dst)
      (hrest : RunFrom prog o st' T' dst O) :
      RunFrom prog o st T L O

/-- **The top-level gas-free IR run** (`ir-design-v2.md` §4). Start at `prog.entry`
with empty locals and world `w₀`, consume the whole trace `T`, halt with `O`, under the
call oracle `o`. The oracle is threaded as an explicit parameter alongside `prog`, kept
separate from the consumed gas `Trace` (calls are a queried function, not events). -/
def IRRun (prog : Program) (o : CallOracle) (w₀ : World) (T : Trace) (O : Observable) : Prop :=
  RunFrom prog o { locals := fun _ => none, world := w₀ } T prog.entry O

end Lir.V2
