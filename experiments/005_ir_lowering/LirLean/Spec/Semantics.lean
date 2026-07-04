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

The run consumes **two** sibling streams, head-first: the gas-read sequence (here) and
the external-call result sequence (`CallStream`, below). Neither is wrapped in an `Event`;
each is a bare list consumed in program order. The gas trace is exactly the list of the
`Word`s a `GAS` opcode reports (`ir-design-v3.md` §8); the old `Event`/`Trace` wrapper was
pure dead weight and has been collapsed away. -/

/-- The supplied gas-read stream: the `Word`s a `GAS` opcode reports, in program
order, consumed head-first as execution reaches each `GAS`. **An observed value
sequence, never a counter** (`ir-design-v3.md` §8). Zero IR-visible inputs. -/
abbrev GasOracle := List Word

/-- The gas stream threaded through an IR run. Thin alias for `GasOracle` kept so
the many `T : Trace` signatures below read as before; the canonical name in new and
signature positions is `GasOracle`, and the element type is `Word`. -/
abbrev Trace := GasOracle

/-! ## The external-call stream (§3, §7 — SETTLED)

A call is a **consumed stream entry**, exactly like a gas read — NOT a function oracle. The
run threads a `CallStream` (a list of recorded call-results) alongside the gas `Trace`, and a
`Stmt.call` **pops the head** and applies it as a state change (`docs/ir-design-v3.md` §7,
R3′). This is the supplied-observation model for chain state, mirroring how the gas sequence
supplies the gas counter the IR deliberately lacks — and, crucially, it is *positional*: two
dynamic calls with identical IR-visible inputs but different EVM outcomes consume DIFFERENT
stream heads, so multi-call runs need no single-call restriction (the fatal flaw of the old
function oracle, which returned the same result for the same visible inputs).

Minimal value-free / calldata-free first cut (§6 decision 3): each stream entry is the
post-call `World` together with the `0`/`1` success flag. **Gas-free**: there is no
restored-gas field — V2 has no gas in state, so post-call gas reads come from the gas
sequence, not the entry (§7). Returndata / value / calldata are deferred (§7).

The stream is held abstract — a value threaded through the run, never instantiated here. The
realised stream (`callStreamOf log.calls self`, off v1's `evmCallOracle` projections) is a
later piece (`LirLean/Spec/Recorder.lean`). -/
abbrev CallStream := List (World × Word)

/-! ## The external-CREATE stream (R2 = option A — SETTLED, `docs/create/stream-decision.md`)

CREATE threads a **fourth channel** alongside the gas `Trace` and the `CallStream`, a
byte-for-byte twin of the latter and fully independent of it. Ordering across kinds lives in
the sequential statement walk (`RunStmts`/`RunFrom` thread each stream left-to-right; each
`Stmt` pops only its own kind's head), NOT in the stream — so two per-kind channels reconstruct
any `CALL; CREATE; CALL` interleaving correctly (stream-decision.md §1). Every existing
constructor threads `D` **unchanged** (inert), exactly as it threads `T` past a `.call` or `C`
past an `assignGas`; only the new `EvalStmt.create` pops it. -/

/-- The supplied external-CREATE result stream — twin of `CallStream` (:99). Each entry is the
post-create `World` paired with the deployed-address-or-`0` word CREATE pushes
(`createAddrOrZero`, `Frame/Create.lean:75`), exactly as `CallStream`'s carries the `0`/`1`
success flag. Positional, consumed head-first by `EvalStmt.create`; independent of the gas
`Trace` and the `CallStream`. -/
abbrev CreateStream := List (World × Word)

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
Three judgements, all threading a `Trace` **and** a `CallStream` left-to-right:

* `EvalStmt` — one statement maps `(st, T, C) → (st', T', C')`, consuming the next gas read
  iff the statement is `assign t .gas`, and the next call-result iff it is `Stmt.call`.
* `RunStmts` — the reflexive/transitive closure over a statement list.
* `IRRun` — the CFG driver: run the entry block's statements, then its terminator;
  `branch`/`jump` recurse into the target block; `ret`/`stop` halt with an
  `Observable`.

An `assign t e` consuming a gas read happens exactly when `e = .gas`; a `Stmt.call`
consumes a call-result. Otherwise both streams are unchanged. This is the §3.4 mechanism:
the value of `Expr.gas` is *drawn from the gas stream*, and the call's `(world', success)`
effect is *drawn from the call stream* — asserted nothing about, positional. The two
channels are independent: `assign t .gas` pops gas and leaves the call stream; `Stmt.call`
pops a call-result and leaves the gas stream (§7). -/

/-- One statement's step, consuming the head of the gas trace (`assign t .gas`) or the head
of the call stream (`Stmt.call`) and leaving the other channel unchanged; `assign`/`sstore`
of non-gas expressions touch neither channel. -/
inductive EvalStmt (prog : Program) :
    IRState → Trace → CallStream → CreateStream → Stmt →
    IRState → Trace → CallStream → CreateStream → Prop where
  /-- `t := e` for a **non-gas** expression `e`: evaluate `e` (no event), bind `t`.
  The `obs` argument of `evalExpr` is irrelevant here (it is only read by `.gas`),
  so we pin it to `0`. No channel is consumed. -/
  | assignPure {st : IRState} {T : Trace} {C : CallStream} {D : CreateStream}
      {t : Tmp} {e : Expr} {w : Word}
      (hne : e ≠ .gas) (hv : evalExpr st 0 e = some w) :
      EvalStmt prog st T C D (.assign t e) (st.setLocal t w) T C D
  /-- `t := gas`: consume the next gas read `obs` from the gas stream, bind `t := obs`; the
  call and create streams are unchanged. -/
  | assignGas {st : IRState} {obs : Word} {T : Trace} {C : CallStream} {D : CreateStream} {t : Tmp} :
      EvalStmt prog st (obs :: T) C D (.assign t .gas) (st.setLocal t obs) T C D
  /-- `storage[key] := value` — the observable write the bytecode side establishes; no
  channel is consumed. -/
  | sstore {st : IRState} {T : Trace} {C : CallStream} {D : CreateStream}
      {key value : Tmp} {kw vw : Word}
      (hk : st.locals key = some kw) (hv : st.locals value = some vw) :
      EvalStmt prog st T C D (.sstore key value) (st.setStorage kw vw) T C D
  /-- `call cs`: read the callee and gas-to-forward words from `locals` (an undefined tmp ⇒
  the rule does not fire, mirroring `sstore`), **pop the head `(world', success)` of the call
  stream**, and apply it as a state change: set `world := world'` and bind the success flag at
  `cs.resultTmp` if present. The gas and create streams are unchanged. Positional: the head IS
  this call's recorded result — no function of the visible inputs, so distinct dynamic calls
  consume distinct heads (multi-call, §7, R3′). -/
  | call {st : IRState} {T : Trace} {C : CallStream} {D : CreateStream} {cs : CallSpec}
      {calleeW gasFwdW success : Word} {world' : World}
      (hcallee : st.locals cs.callee = some calleeW)
      (hgas : st.locals cs.gasFwd = some gasFwdW) :
      EvalStmt prog st T ((world', success) :: C) D (.call cs)
        (match cs.resultTmp with
          | some t => { st with world := world' }.setLocal t success
          | none   => { st with world := world' })
        T C D
  /-- `create cs`: read the value / init-code window words from `locals` (an undefined tmp ⇒
  the rule does not fire, mirroring `.call`), **pop the head `(world', addrW)` of the CREATE
  stream**, set `world := world'`, and bind the deployed-address-or-`0` word `addrW` at
  `cs.resultTmp` if present. The gas `Trace` and the `CallStream` are unchanged. Positional:
  the head IS this create's recorded result. First cut is the empty-init case
  (`value = initOffset = initSize = 0`, `Frame/Create.lean:31`), but the guards read the tmps so
  CREATE2 (`salt = some`) needs no reshape — only an extra salt read (`docs/create/BUILD-PLAN.md`
  §4). Structurally identical to `.call` — pop the head, `world := world'`, bind at `resultTmp` —
  differing only in *which* channel is popped and *which* locals are read as guards; this
  structural identity keeps every existing arm's `D`-threading inert. -/
  | create {st : IRState} {T : Trace} {C : CallStream} {D : CreateStream}
      {cs : CreateSpec} {valueW initOffW initSizeW addrW : Word} {world' : World}
      (hvalue : st.locals cs.value = some valueW)
      (hoff   : st.locals cs.initOffset = some initOffW)
      (hsize  : st.locals cs.initSize = some initSizeW) :
      EvalStmt prog st T C ((world', addrW) :: D) (.create cs)
        (match cs.resultTmp with
          | some t => { st with world := world' }.setLocal t addrW
          | none   => { st with world := world' })
        T C D

/-- Run a statement list left-to-right, threading the gas trace, the call stream and the
create stream. -/
inductive RunStmts (prog : Program) :
    IRState → Trace → CallStream → CreateStream → List Stmt →
    IRState → Trace → CallStream → CreateStream → Prop where
  | nil {st : IRState} {T : Trace} {C : CallStream} {D : CreateStream} :
      RunStmts prog st T C D [] st T C D
  | cons {st st' st'' : IRState} {T T' T'' : Trace} {C C' C'' : CallStream}
      {D D' D'' : CreateStream} {s : Stmt} {ss : List Stmt}
      (hh : EvalStmt prog st T C D s st' T' C' D')
      (ht : RunStmts prog st' T' C' D' ss st'' T'' C'' D'') :
      RunStmts prog st T C D (s :: ss) st'' T'' C'' D''

/-! ### The observable boundary (§4) -/

/-- The observable boundary of a finished IR run: the final world and the halt
result. **No gas, no pc.** (`ir-design-v2.md` §4.) -/
structure Observable where
  /-- The final observable world (the full final storage, as the post-run lens). -/
  world  : World
  /-- The halt result (`stop`/`return`). -/
  result : IRHalt

/-- The CFG big-step driver. `IRRun prog w₀ T C O`: starting at `prog.entry` with
empty locals and world `w₀`, consuming the whole gas trace `T` and call stream `C`, the
program halts with observable `O`. The terminators:

* `ret t` halts with `returned (the value of t)`;
* `stop` halts with `stopped`;
* `branch cond thenL elseL` recurses into `thenL` if `cond ≠ 0`, else `elseL`;
* `jump dst` recurses into `dst`.

`branch`/`jump` are bounded by the program's acyclic shape in the prototype (the
example program's blocks form a DAG), so the inductive relation is well-founded by
construction at use sites — no fuel parameter is threaded. -/
inductive RunFrom (prog : Program) :
    IRState → Trace → CallStream → CreateStream → Label → Observable → Prop where
  /-- `ret t`: run the block's statements, then halt returning `t`'s value. -/
  | ret {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {t : Tmp} {w : Word}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFrom prog st T C D L { world := st'.world, result := .returned w }
  /-- `stop`: run the block's statements, then halt. -/
  | stop {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .stop) :
      RunFrom prog st T C D L { world := st'.world, result := .stopped }
  /-- `branch cond thenL elseL`, condition non-zero ⇒ recurse into `thenL`. -/
  | branchThen {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {cond : Tmp} {cw : Word} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some cw) (hnz : cw ≠ 0)
      (hrest : RunFrom prog st' T' C' D' thenL O) :
      RunFrom prog st T C D L O
  /-- `branch cond thenL elseL`, condition zero ⇒ recurse into `elseL`. -/
  | branchElse {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {cond : Tmp} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some 0)
      (hrest : RunFrom prog st' T' C' D' elseL O) :
      RunFrom prog st T C D L O
  /-- `jump dst` ⇒ recurse into `dst`. -/
  | jump {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {dst : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .jump dst)
      (hrest : RunFrom prog st' T' C' D' dst O) :
      RunFrom prog st T C D L O

/-- **The top-level gas-free IR run** (`ir-design-v2.md` §4). Start at `prog.entry`
with empty locals and world `w₀`, consume the whole gas trace `T`, call stream `C` and create
stream `D`, halt with `O`. All three streams are threaded alongside `prog`, consumed head-first
(gas by `assign t .gas`, calls by `Stmt.call`, creates by `Stmt.create`). -/
def IRRun (prog : Program) (w₀ : World) (T : Trace) (C : CallStream) (D : CreateStream)
    (O : Observable) : Prop :=
  RunFrom prog { locals := fun _ => none, world := w₀ } T C D prog.entry O

end Lir.V2
