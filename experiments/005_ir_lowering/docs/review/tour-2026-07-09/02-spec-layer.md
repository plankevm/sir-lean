# 02 — The Spec layer: the trusted statement surface

Part of the [exp005 tour](00-overview.md). Siblings: [01 trusted base](01-trusted-base.md) ·
[03 code geometry](03-code-geometry.md) · [04 value channel](04-value-channel.md) ·
[05 simulation](05-simulation.md) · [06 realisability](06-realisability.md) ·
[07 assembler](07-assembler.md).

**Scope.** Everything a skeptical reader must read and *believe* (not verify) to know what
the conformance flagship SAYS: `LirLean/Spec/` (9 files), the IR metatheory in
[`Law.lean`](../../../LirLean/Law.lean) and [`IRRun.lean`](../../../LirLean/IRRun.lean),
plus the recorder-adequacy and call-bridge companions
([`RecorderLemmas.lean`](../../../LirLean/RecorderLemmas.lean),
[`CallRealises.lean`](../../../LirLean/CallRealises.lean)) and the WIP file that holds the
flagship statement itself
([`Realisability/RealisabilitySpec.lean`](../../../LirLean/Realisability/RealisabilitySpec.lean)).

## TL;DR

The spec layer defines a small SSA-ish IR ([`Spec/IR.lean`](../../../LirLean/Spec/IR.lean)), an
**oracle-stream big-step semantics** in which storage is a modelled effect but gas reads, CALL
results and CREATE results are positional list streams the IR pops but never computes
([`Spec/Semantics.lean`](../../../LirLean/Spec/Semantics.lean)), a total lowering function
[`lower`](../../../LirLean/Spec/Lowering.lean#L186), and a **recording interpreter**
[`driveLog`](../../../LirLean/Spec/Recorder.lean#L51) — a hand-maintained twin of exp003's
[`drive`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36) whose
*result* channel is proved equal to the verified engine
([`driveLog_drive`](../../../LirLean/RecorderLemmas.lean#L82)) but whose *recorded* channels
are definitionally trusted. The flagship
[`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251) (R11,
**sorry'd, WIP lib**) says: run the lowered bytecode once under the recorder; then an IR run
exists at exactly the recorded streams and its final world/result agree with the machine's
([`Conforms`](../../../LirLean/Spec/Conformance.lean#L20)). The statement vocabulary is now
fully hoisted into `Spec/` (the exact-consumption mirror
[`RunFromAll`](../../../LirLean/Spec/Semantics.lean#L188) and the call/create entry projections
[`evmV2CallEntry`](../../../LirLean/Spec/Recorder.lean#L16) included — the earlier
"trusted surface is split" finding is **resolved on the vocabulary axis**, still open on the
import axis: several `Spec/` files import proof modules). Verification status, reported not
re-run: default `LirLean` lib builds green and is sorry-free (all 6 `sorry`s live in the
non-default `WIP` lib per [`lakefile.lean`](../../../lakefile.lean#L31)); axiom footprints of
the salvage layer are build-pinned in [`Audit.lean`](../../../LirLean/Audit.lean#L27); no
`native_decide`/`bv_decide` anywhere in `LirLean/`.

## 1. File map (everything in scope)

| File | Role | Trust class |
|---|---|---|
| [`Spec/IR.lean`](../../../LirLean/Spec/IR.lean) | IR grammar (`Expr`/`Stmt`/`Term`/`Block`/`Program`) | trusted spec |
| [`Spec/Semantics.lean`](../../../LirLean/Spec/Semantics.lean) | oracle-stream big-step: `IRState`, streams, `evalExpr`, `EvalStmt`, `RunFrom`, `IRRun`, `RunFromLeft`/`RunFromAll` | trusted spec (+2 tiny adapter proofs) |
| [`Spec/Lowering.lean`](../../../LirLean/Spec/Lowering.lean) | `Loc`/`Alloc`, `defsOf`, `matExpr`/`matCache`, `emit`, `lower` | trusted spec (+`rfl` simp lemmas) |
| [`Spec/Recorder.lean`](../../../LirLean/Spec/Recorder.lean) | `RunLog`, `driveLog`, `runWithLog`, `realisedGas/Call/Create`, `observe` | trusted spec — **the trust fence, §5** |
| [`Spec/Recorder.lean`](../../../LirLean/Spec/Recorder.lean) | recorder vocabulary and `evmV2CallEntry`/`evmV2CreateEntry` stream-entry projections | trusted spec |
| [`Spec/Conformance.lean`](../../../LirLean/Spec/Conformance.lean) | `entryState`, `RunLog.clean`, `Conforms`, `NoGasReads` | trusted spec |
| [`Spec/WellFormed.lean`](../../../LirLean/Spec/WellFormed.lean) | `IRWellFormed`, `codeFits`, `stackFits` + vocabulary | trusted spec **mixed with ~280 lines of `matCache` proofs** |
| [`Spec/Seams.lean`](../../../LirLean/Spec/Seams.lean) | `PrecompileAssumptions`, `ReachableFrom`, seam forwarders | trusted spec (forwards to proof-layer defs) |
| [`Spec/BudgetDerivations.lean`](../../../LirLean/Spec/BudgetDerivations.lean) | derives per-cursor pc/stack bounds from the two scalar budgets | derived convenience (proofs, not spec) |
| [`Law.lean`](../../../LirLean/Law.lean) | `EvalStmt.det` → `RunStmts.det` → `RunFrom.det` → `IRRun.det` | supporting metatheory |
| [`IRRun.lean`](../../../LirLean/IRRun.lean) | gas-free/call-free existence ladder, `RunDefinable` | supporting metatheory (partly superseded, §9) |
| [`RecorderLemmas.lean`](../../../LirLean/RecorderLemmas.lean) | `driveLog_drive`, `runWithLog_drive`, stream cons-projections | supporting (the proved half of the fence) |
| [`CallRealises.lean`](../../../LirLean/CallRealises.lean) | `callRealises_bridge`/`createRealises_bridge` | supporting (entry-projection faithfulness) |
| [`Realisability/Surface.lean`](../../../LirLean/Realisability/Surface.lean) | WIP hypothesis machinery (`WellLowered`, `RecorderCoupled`, `StmtTies'`/`TermTies'`) | **derived** hypothesis vocabulary — not on the flagship's statement surface |
| [`Realisability/RealisabilitySpec.lean`](../../../LirLean/Realisability/RealisabilitySpec.lean) | the flagships `lower_conforms`(+`_exact`,`_gasfree`), R-obligations | WIP; statements are the review target |

## 2. IR grammar — [`Spec/IR.lean`](../../../LirLean/Spec/IR.lean)

Temporaries, expressions over temporaries, four statement forms, four terminators; a program
is an array of blocks with an entry label.

```lean
-- Spec/IR.lean#L31
inductive Expr where
  | imm   (w : Word)
  | tmp   (t : Tmp)
  | add   (a b : Tmp)
  | lt    (a b : Tmp)
  | sload (key : Tmp)
  | gas

inductive Stmt where
  | assign (t : Tmp) (e : Expr)
  | sstore (key value : Tmp)
  | call   (cs : CallSpec)
  | create (cs : CreateSpec)

inductive Term where
  | ret    (t : Tmp)
  | stop
  | jump   (dst : Label)
  | branch (cond : Tmp) (thenL elseL : Label)
```

([`Expr`](../../../LirLean/Spec/IR.lean#L31), [`Stmt`](../../../LirLean/Spec/IR.lean#L40),
[`Term`](../../../LirLean/Spec/IR.lean#L47).) A [`CallSpec`](../../../LirLean/Spec/IR.lean#L17)
carries only `callee`/`gasFwd`/optional `resultTmp` — value, argument and return memory windows
are pinned to zero by the lowering (§4), an honest scope restriction. A
[`CreateSpec`](../../../LirLean/Spec/IR.lean#L23) carries `value`/`initOffset`/`initSize`/
optional `salt` (CREATE2)/optional `resultTmp`, but the lowering likewise pins
value/offset/size to zero bytes (empty init code).

## 3. Oracle-stream semantics — [`Spec/Semantics.lean`](../../../LirLean/Spec/Semantics.lean) (reviewer Q1)

### 3.1 The state and the three streams

```lean
-- Spec/Semantics.lean#L8
abbrev World := Word → Word

structure IRState where
  locals : Tmp → Option Word
  world  : World

abbrev GasOracle := List Word
-- Compatibility alias; declarations in this file use `GasOracle`.
abbrev Trace := GasOracle
abbrev CallStream := List (World × Word)
abbrev CreateStream := List (World × Word)
```

([`IRState`](../../../LirLean/Spec/Semantics.lean#L10),
[`GasOracle`](../../../LirLean/Spec/Semantics.lean#L19),
[`CallStream`](../../../LirLean/Spec/Semantics.lean#L24),
[`CreateStream`](../../../LirLean/Spec/Semantics.lean#L26).)

The design split:

* **Storage is a modelled effect.** `st.world : Word → Word` is the self account's storage;
  `sstore` writes it, `sload` reads it. It must be modelled because storage equality *is the
  conformance conclusion* — [`Conforms`](../../../LirLean/Spec/Conformance.lean#L20) compares
  the IR run's final `world` to the machine's post-run self-storage lens. The IR can compute
  storage: every write it does is its own.
* **Gas, call results, create results are observed, not modelled.** The IR has *no gas
  counter* (`IRState` has only `locals` and `world`) and no model of other contracts. What a
  `GAS` opcode returns depends on the machine's cost accounting of the *compiled* code; what a
  `CALL`/`CREATE` returns depends on chain state and callee code the IR does not represent.
  So these are inputs: positional list streams, consumed head-first, one entry per dynamic
  event in program order. This is the **permissive-semantics / restrictive-theorem** pattern:
  the semantics accepts *any* streams (`RunFrom` holds for arbitrary `T C D` that make the
  derivation go through), and all the truth is loaded into the theorem, which instantiates
  the streams at exactly the values the recorder observed on the real machine
  ([`realisedGas`](../../../LirLean/Spec/Recorder.lean#L103) /
  [`realisedCall`](../../../LirLean/Spec/Recorder.lean#L110) /
  [`realisedCreate`](../../../LirLean/Spec/Recorder.lean#L116)). A gas *law* (e.g.
  monotonicity) was deliberately deleted — gas is a log-fed exact-equality oracle
  ([`docs/gas-decision.md`](../../gas-decision.md), recorded in the
  [`Law.lean` header](../../../LirLean/Law.lean#L16)).
* Positional streams are also what killed the old single-call restriction: a syntactic
  `Stmt.call` inside a loop consumes one stream entry *per iteration*, so per-iteration
  child outcomes are represented faithfully
  ([`RealisabilitySpec.lean` header, lesson 7](../../../LirLean/Realisability/RealisabilitySpec.lean#L58)).

### 3.2 Where each channel is popped

Expression evaluation is total-modulo-locals and takes an awkward `obs` parameter that is
*only* consulted by `.gas` (flagged in §11):

```lean
-- Spec/Semantics.lean#L34
def evalExpr (st : IRState) (obs : Word) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.world key)
  | .gas     => some obs
```

[`EvalStmt`](../../../LirLean/Spec/Semantics.lean#L48) threads all three streams through every
statement; the popping discipline is one constructor per channel:

```lean
-- Spec/Semantics.lean#L48 (assignPure/assignGas/call shown; sstore/create at L58/L71)
inductive EvalStmt (prog : Program) :
    IRState → GasOracle → CallStream → CreateStream → Stmt →
    IRState → GasOracle → CallStream → CreateStream → Prop where
  | assignPure {st T C D t e w}
      (hne : e ≠ .gas) (hv : evalExpr st 0 e = some w) :
      EvalStmt prog st T C D (.assign t e) (st.setLocal t w) T C D
  | assignGas {st obs T C D t} :
      EvalStmt prog st (obs :: T) C D (.assign t .gas) (st.setLocal t obs) T C D
  | call {st T C D cs calleeW gasFwdW success world'}
      (hcallee : st.locals cs.callee = some calleeW)
      (hgas : st.locals cs.gasFwd = some gasFwdW) :
      EvalStmt prog st T ((world', success) :: C) D (.call cs)
        (match cs.resultTmp with
          | some t => { st with world := world' }.setLocal t success
          | none   => { st with world := world' })
        T C D
```

* `.assign t .gas` ([`assignGas`](../../../LirLean/Spec/Semantics.lean#L55)) pops one word off
  the gas stream and binds it — the *only* consumer of `T`. Pure assigns use
  `evalExpr st 0` with an explicit `e ≠ .gas` side condition, so the `obs := 0` is a pinned
  phantom, never observable.
* `.call` ([`call`](../../../LirLean/Spec/Semantics.lean#L62)) pops one `(world', success)`
  pair off `C`: the head **is** the effect — the whole `world` is *replaced* by the oracle's
  post-call world (that is how the callee's writes to the self account are threaded), and
  `success` lands in `resultTmp` if present. Note the callee/gasFwd operands must be *bound*
  but their *values* do not influence the post-state — faithfulness of the head to the actual
  call at those operands is exactly what the flagship, not the semantics, asserts.
* `.create` ([`create`](../../../LirLean/Spec/Semantics.lean#L71)) is the exact twin on `D`
  with an address-or-zero word instead of a success flag.
* `.sstore` ([`sstore`](../../../LirLean/Spec/Semantics.lean#L58)) touches no stream:
  `st.setStorage kw vw`, a modelled write.

[`RunStmts`](../../../LirLean/Spec/Semantics.lean#L82) folds `EvalStmt` over a block's
statement list; [`RunFrom`](../../../LirLean/Spec/Semantics.lean#L99) is the block-level
big-step (ret/stop halt; jump/branch recurse), and

```lean
-- Spec/Semantics.lean#L138
def IRRun (prog : Program) (w₀ : World) (T : GasOracle) (C : CallStream) (D : CreateStream)
    (O : Observable) : Prop :=
  RunFrom prog { locals := fun _ => none, world := w₀ } T C D prog.entry O
```

with [`Observable`](../../../LirLean/Spec/Semantics.lean#L93) `= { world : World, result : IRHalt }`
and [`IRHalt`](../../../LirLean/Spec/Semantics.lean#L14) `= stopped | returned w`.

### 3.3 `RunFrom` drops leftovers; `RunFromAll` pins them to `[]` (reviewer Q3)

Look at `RunFrom`'s halt rule: the streams after the last statement (`T' C' D'`) appear in the
premises and are **discarded** in the conclusion —

```lean
-- Spec/Semantics.lean#L101
  | ret {st st' T T' C C' D D' L b t w}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFrom prog st T C D L { world := st'.world, result := .returned w }
```

This is fine for soundness but weak against a specific vacuity channel: a theorem of shape
"∃ run at stream `T`" where the run may silently ignore a suffix of `T` is weaker than it
looks — you could hand the IR an over-long gas stream (or, worse, a proof strategy could
*choose* to consume fewer entries than the machine actually produced) and still "conform".
The anti-vacuity fix is the exact-consumption mirror
[`RunFromLeft`](../../../LirLean/Spec/Semantics.lean#L144), identical to `RunFrom` except the
halt rules *return* the leftover suffixes, and

```lean
-- Spec/Semantics.lean#L188
def RunFromAll (prog : Program) (st : IRState) (T : GasOracle) (C : CallStream) (D : CreateStream)
    (L : Label) (O : Observable) : Prop :=
  RunFromLeft prog st T C D L O [] [] []
```

which says: the run consumed **all** of every supplied stream. Two adapter lemmas keep the
mirrors aligned: [`runFrom_of_runFromLeft`](../../../LirLean/Spec/Semantics.lean#L192)
(exact ⇒ plain) and [`runFromLeft_exists`](../../../LirLean/Spec/Semantics.lean#L202)
(plain ⇒ *some* leftovers exist — deliberately not `[]`).

Usage: the main flagship [`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251)
concludes `RunFrom`; its strengthening
[`lower_conforms_exact`](../../../LirLean/Realisability/RealisabilitySpec.lean#L302) (R11-all)
concludes `RunFromAll` and carries an explicit proof-shell comment that exactness must come
from the producer, **not** be laundered through `runFromLeft_exists`
([RealisabilitySpec.lean#L320-L322](../../../LirLean/Realisability/RealisabilitySpec.lean#L320)).
Since the recorded streams are what is supplied, `RunFromAll` is what certifies "the IR
explains *every* recorded event", not just a prefix. The
[R11 plan](../../planning/r11-plan-2026-07-08.md) tracks the `RunFromAll`-producing recursion.

## 4. The lowering — [`Spec/Lowering.lean`](../../../LirLean/Spec/Lowering.lean)

The compiler under study, in five short definitional stages, all total:

```lean
-- Spec/Lowering.lean#L30
inductive Loc where
  | remat (e : Expr)   -- recompute the defining expression at every use
  | slot  (n : Nat)    -- spill to memory slot n; uses emit PUSH slot; MLOAD

abbrev Alloc := Tmp → Option Loc

def slotOf (t : Tmp) : Nat := t.id * 32
```

* [`defEnv`](../../../LirLean/Spec/Lowering.lean#L46) walks all blocks and registers each
  def-site: `t := gas`, `t := sload _`, call results and create results are **spilled**
  (`Loc.slot (slotOf t)` — non-recomputable effects); every other assign is `Loc.remat e`.
  [`defsOf`](../../../LirLean/Spec/Lowering.lean#L56) is *first*-find over that list (the
  shadowing subtlety behind the `DefsConsistent` hypothesis, §7.2).
* [`matExpr`](../../../LirLean/Spec/Lowering.lean#L66)/[`matCache`](../../../LirLean/Spec/Lowering.lean#L84)
  build, per tmp, the byte string that *materialises* its value on the stack (a fold over the
  ordered `defEnv`; slot tmps become `PUSH32 slot; MLOAD`, remat tmps recursively inline
  their operands' byte strings; unregistered tmps default to `PUSH32 0`).
* [`emitStmt`](../../../LirLean/Spec/Lowering.lean#L114): a spilled assign emits
  `matExpr … ++ PUSH32 slot ++ MSTORE`; **a remat assign emits `[]`** (no code — the value is
  reconstructed at use sites); `sstore` emits `mat value ++ mat key ++ SSTORE`; `call` emits
  five `PUSH32 0` (retSize/retOff/argsSize/argsOff/value) then callee, gas, `CALL`, then
  either a spill of the success flag or `POP`; `create` emits three zero pushes then
  `CREATE`/`CREATE2` and the same result handling.
* [`emitTerm`](../../../LirLean/Spec/Lowering.lean#L158): `ret t` emits
  `mat t ++ PUSH32 0 ++ MSTORE ++ PUSH32 32 ++ PUSH32 0 ++ RETURN` (returns one word from
  memory 0); `jump`/`branch` emit `PUSH4 offset` against the
  [`offsetTable`](../../../LirLean/Spec/Lowering.lean#L176) (block byte offsets; each block is
  prefixed with a `JUMPDEST`).

```lean
-- Spec/Lowering.lean#L179
def emit (a : Alloc) (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let labelOff := offsetTable cache a prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache a labelOff b)

def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)
```

([`lower`](../../../LirLean/Spec/Lowering.lean#L186).) Note `lower` is **total**: it happily
emits bytes for ill-formed programs (undefined tmps materialise as `PUSH32 0`, a shadowed
spill emits nothing at the shadowed site, out-of-range offsets truncate in `PUSH4`). No
soundness lives in the function; it is all recovered in the theorem via
[`IRWellFormed`](../../../LirLean/Spec/WellFormed.lean#L430) + the two budgets (§7.2) — a
legitimate design (spec stays simple), flagged in §11 so nobody reads `lower` alone as safe.

## 5. The recorder and its trust fence — [`Spec/Recorder.lean`](../../../LirLean/Spec/Recorder.lean) (reviewer Q2)

The flagship's runtime premise is `runWithLog params (seedFuel params.gas) = some log`. So a
skeptical reader must understand exactly what
[`runWithLog`](../../../LirLean/Spec/Recorder.lean#L93) computes. It is exp003's verified
driver [`drive`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L36),
**re-implemented by hand** with four recording accumulators spliced in:

```lean
-- Spec/Recorder.lean#L51
def driveLog (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
    (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord)
    (createAcc : List CreateRecord) :
    Except ExecutionException
      (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord) :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok (result, gasAcc, sloadAcc, callAcc, createAcc)
            | pending :: rest =>
              match pending.resume result with
                | .ok parent =>
                  driveLog fuel rest (.inl parent) gasAcc sloadAcc
                    (if rest.isEmpty then recordCall pending result callAcc else callAcc)
                    (if rest.isEmpty then recordCreate pending result createAcc else createAcc)
                | .error e => ...
        | .inl current =>
          match stepFrame current with
            | .next exec =>
              if isGasOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) sloadAcc callAcc createAcc
              else if isSloadOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  gasAcc (sloadAcc ++ [sloadWarmthOf current]) callAcc createAcc
              else
                driveLog fuel stack (.inl { current with exec := exec }) gasAcc sloadAcc callAcc createAcc
            | .halted halt => driveLog fuel stack (.inr (endFrame current halt)) gasAcc sloadAcc callAcc createAcc
            | .needsCall params pending => ...  -- descend; recording happens at resume
            | .needsCreate params pending => ...
```

and a [`RunLog`](../../../LirLean/Spec/Recorder.lean#L19) bundling
`observable : FrameResult` + the four channels.

**The fence, made crisp.** Split `driveLog` into two claims:

1. *"It computes what `drive` computes."* **Proved.**
   [`driveLog_drive`](../../../LirLean/RecorderLemmas.lean#L82):
   `(driveLog f …).map (·.1) = drive f …` for any accumulators (induction on fuel, branch-for-
   branch), lifted through the entry to
   [`runWithLog_drive`](../../../LirLean/RecorderLemmas.lean#L138):

   ```lean
   -- RecorderLemmas.lean#L138
   theorem runWithLog_drive {params : CallParams} {fuel : ℕ} {log : RunLog}
       (h : runWithLog params fuel = some log) :
       ∃ frame, beginCall params = .inl frame
         ∧ drive fuel [] (.inl frame) = .ok log.observable := by ...
   ```

   So `log.observable` is exactly the verified engine's output; nothing about the machine's
   behaviour is trusted twice.

2. *"It records the right events at the right moments."* **Definitionally trusted.** Adequacy
   says *nothing* about `gasAcc`/`sloadAcc`/`callAcc`/`createAcc` — a `driveLog` that recorded
   gas at every depth, or the pre-charge gas value, or calls in reverse order, would satisfy
   `driveLog_drive` just as well. The recorded-channel semantics is pure definition, and the
   reader must check it by eye:
   * **Which events**: [`isGasOp`](../../../LirLean/Spec/Recorder.lean#L26)/
     [`isSloadOp`](../../../LirLean/Spec/Recorder.lean#L29) decode the op at the *current* pc
     (pre-step), defaulting to `STOP` on decode failure;
   * **At which depth**: the `stack.isEmpty` gate — only the **top-level** frame's GAS/SLOAD
     reads are logged; a callee's internal reads are invisible, matching the IR, which
     black-boxes calls as one stream entry. Calls/creates are recorded at *result delivery*
     under `rest.isEmpty` — i.e. exactly when a **direct child** of the top-level frame
     returns, in return order;
   * **Which value**: gas records the **post-step** `exec.gasAvailable` — the value GAS pushes
     after paying its own `Gbase` (this is why the WIP tie pins
     `gS.head? = ofUInt64 (fr0.gasAvailable - Gbase)`,
     [`StmtTies'` arm 3](../../../LirLean/Realisability/Surface.lean#L397)); sload records
     the warmth *charge* [`sloadWarmthOf`](../../../LirLean/Spec/Recorder.lean#L32) (fed to the
     gas-charge machinery, **not** to the IR streams); calls record
     `(result.toCallResult, pendingCall)` verbatim
     ([`recordCall`](../../../LirLean/Spec/Recorder.lean#L39)).

   The channels acquire semantic force only downstream: the entry projections
   ([`evmV2CallEntry`](../../../LirLean/Spec/Recorder.lean#L16), §6) are proved to coincide
   with the actual lowered CALL/CREATE effect
   ([`callRealises_bridge`](../../../LirLean/CallRealises.lean#L77) /
   [`createRealises_bridge`](../../../LirLean/CallRealises.lean#L118), both `rfl`-clean
   projections of exp003's `resumeAfterCall`/`resumeAfterCreate`), and the (sorry'd)
   R-obligations must connect record positions to run positions. But *"the log's gas entries
   are the top-level GAS reads in program order"* is spec content you believe by reading
   `driveLog`, full stop. This is the layer's single biggest trust commitment after exp003
   itself.

The IR-facing stream projections are one `map` each:

```lean
-- Spec/Recorder.lean#L103
def realisedGas (log : RunLog) : GasOracle := log.gas
def callStreamOf (calls : List CallRecord) (self : AccountAddress) : CallStream :=
  calls.map (fun rec => evmV2CallEntry rec.result rec.pending self)
def realisedCall (log : RunLog) (self : AccountAddress) : CallStream := callStreamOf log.calls self
```

with cons-faithfulness lemmas
[`realisedCall_cons`](../../../LirLean/RecorderLemmas.lean#L64) /
[`realisedCreate_cons`](../../../LirLean/RecorderLemmas.lean#L164). The machine-side
observable projection is

```lean
-- Spec/Recorder.lean#L119
def resultStorageAt (fr : FrameResult) (addr : AccountAddress) (key : Word) : Word :=
  fr.toCallResult.accounts.find? addr |>.option 0 (·.lookupStorage key)

def observe (self : AccountAddress) (fr : FrameResult) : Observable :=
  { world  := fun key => resultStorageAt fr self key
    result := let out := fr.toCallResult.output
              if out.isEmpty then .stopped else .returned (uInt256OfByteArray out) }
```

([`observe`](../../../LirLean/Spec/Recorder.lean#L122); `uInt256OfByteArray` is exp003's
[UInt256.lean#L762](../../../../003_bytecode_layer/EVMLean/Evm/UInt256.lean#L762).) Note the
result channel is coarse: empty output ↦ `stopped`, otherwise the output bytes as one word —
adequate for this IR (whose `ret` returns exactly one word) but it identifies "STOP" with
"RETURN of zero bytes", and a 33-byte output would be silently truncated by the word
conversion. In-scope programs can't produce either, but the *definition* doesn't know that.

## 6. Call/create entries and the seams — [`Spec/Recorder.lean`](../../../LirLean/Spec/Recorder.lean), [`Spec/Seams.lean`](../../../LirLean/Spec/Seams.lean)

```lean
-- Spec/Recorder.lean
def evmV2CallEntry (result : CallResult) (pd : PendingCall) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCallOracle.postStorage result pd self key)
  , evmCallOracle.successWord result pd )
```

([`evmV2CallEntry`](../../../LirLean/Spec/Recorder.lean#L16),
[`evmV2CreateEntry`](../../../LirLean/Spec/Recorder.lean#L21).) These convert one recorded
`CallRecord` into one `CallStream` entry: the post-call self-storage lens and the 0/1 success
word, both projections of exp003's `resumeAfterCall` via
[`evmCallOracle`](../../../LirLean/Frame/Call.lean#L108) (whose `successWord` is proved equal
to exp003's CALL flag [`callSuccessFlag`](../../../LirLean/Frame/Call.lean#L120) by `rfl`).

[`Spec/Seams.lean`](../../../LirLean/Spec/Seams.lean) names the honest oracle seams the
flagship carries:

```lean
-- Spec/Seams.lean#L28
def ReachableFrom (params : Evm.CallParams) (fr' : Evm.Frame) : Prop :=
  ∃ fr₀, Evm.beginCall params = .inl fr₀ ∧ BytecodeLayer.Hoare.Runs fr₀ fr'

structure PrecompileAssumptions (prog : Program) (params : Evm.CallParams) : Prop where
  noErase : Lir.Spec.PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'
```

Glosses (definitions live in the proof layer and are *forwarded* here — see the inversion note
in §7.3): [`CallsCode fr'`](../../../LirLean/Decode/Modellable.lean#L410) — any CALL issued at
a reachable frame targets a code account, never a precompile;
[`CreateResolves fr'`](../../../LirLean/Decode/Modellable.lean#L421) — any CREATE's 63/64
gas-retention resume guard passes;
[`PrecompilesPreservePresence`](../../../LirLean/Spec/Seams.lean#L11) — a precompile fast-path
`beginCall` never erases an account's presence. **Flag:** `callsCode`/`createResolves`
quantify over *every reachable frame* — trace-quantified hypotheses of exactly the shape this
project has learned to distrust. They are honest here (they restrict *scope* — no
precompile calls, no pathological CREATE gas — rather than smuggling the conclusion; both are
vacuously true for call/create-free programs), but they are not statically checkable from
`prog`, and the reader should know they are the flagship's least-finite premises. This is the
known "conformance oracle surface" residue documented in
[`docs/headline-transitive-chain.md`](../../headline-transitive-chain.md).

## 7. What the flagship SAYS — [`Spec/Conformance.lean`](../../../LirLean/Spec/Conformance.lean) + the R11 statement (reviewer Q4)

### 7.1 The conformance vocabulary

```lean
-- Spec/Conformance.lean#L11
def entryState (params : CallParams) : IRState :=
  { locals := fun _ => none
    world  := fun k => (params.accounts.find? params.recipient).option 0 (·.lookupStorage k) }

def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False

def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world
  ∧ O.result = (observe self log.observable).result

def NoGasReads (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ (pc : Nat) (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) → e ≠ .gas
```

[`Conforms`](../../../LirLean/Spec/Conformance.lean#L20) is deliberately thin: final
self-storage lens and final stopped/returned result agree between the IR observable and the
recorded machine result. No gas totals, no intermediate states, no other accounts, no logs/
events. [`entryState`](../../../LirLean/Spec/Conformance.lean#L11) pins the IR's initial world
to the recipient's pre-call storage; [`RunLog.clean`](../../../LirLean/Spec/Conformance.lean#L15)
is the decidable scope premise excluding exceptional halts — with the documented conservative
corner that a genuine `REVERT` at *exactly* zero remaining gas is indistinguishable from an
exception on the log and therefore also excluded (sound: hypothesis false ⇒ theorem silent;
see the [scope-seam note](../../../LirLean/Realisability/RealisabilitySpec.lean#L91)).

### 7.2 The flagship statement (WIP, sorry'd via its producer)

```lean
-- Realisability/RealisabilitySpec.lean#L251  (WIP lib; proof delegates to the
-- sorry'd coupled run-producer runFrom_of_driveCorrLog in Producer.lean)
theorem lower_conforms {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O
```

Plain English: *if* the machine, started as a top-level call into an account holding
`lower prog`, runs to a clean halt under the recorder, *then* the IR semantics — fed the
recorded gas words, call results and create results positionally, from the recipient's actual
pre-storage — has a run, and that run's final storage and result are the machine's.
Siblings: [`lower_conforms_exact`](../../../LirLean/Realisability/RealisabilitySpec.lean#L302)
(same, `RunFromAll` — the anti-vacuity strengthening, §3.3) and
[`lower_conforms_gasfree`](../../../LirLean/Realisability/RealisabilitySpec.lean#L341)
(adds [`NoGasReads`](../../../LirLean/Spec/Conformance.lean#L24); de-risking co-flagship, to be
proved first). Non-vacuity guards:
[`exProg_satisfies_hypotheses`](../../../LirLean/Realisability/RealisabilitySpec.lean#L388) (R12a,
sorry'd) and [`exProg_nonvacuity`](../../../LirLean/Realisability/RealisabilitySpec.lean#L401)
(R12b, closed *modulo* R11/R12a) at the loop+gas+sload+call witness
[`exProg`](../../../LirLean/Realisability/Witness.lean#L38), whose budgets
[`codeFits_exProg`](../../../LirLean/Realisability/Witness.lean#L560)/
[`stackFits_exProg`](../../../LirLean/Realisability/Witness.lean#L565) close by `decide`.

Hypothesis ledger, classified:

| Premise | Nature | Comment |
|---|---|---|
| `hcode`, `hmod` | definitional pins | "the account runs `lower prog`", writable state |
| `hself`, `hgas` | decidable entry facts | recipient exists; ≥ 1 `Gjumpdest` of gas |
| `hwf : IRWellFormed` + `hcodeFits`/`hstk` | **static, per-program** | see below |
| `hrun` | the runtime premise | one recorded execution — the theorem is per-run |
| `hclean` | decidable scope | non-exception halt (zero-gas-revert corner excluded) |
| `hseams` | honest oracle seams | trace-quantified; see §6 flag |

The static bundle ([`IRWellFormed`](../../../LirLean/Spec/WellFormed.lean#L430)):

```lean
-- Spec/WellFormed.lean#L430
structure IRWellFormed (prog : Program) : Prop where
  defineBeforeUse : RunDefinableG prog
  defsConsistent  : DefsConsistent prog
  entry0          : prog.entry.idx = 0
  cfgClosed       : CFGClosed prog
  defEnvOrdered   : DefEnvOrdered prog
  revalidates     : RevalidatesPerBlock prog
  slotAddr        : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp), ...
```

plus [`codeFits`](../../../LirLean/Spec/WellFormed.lean#L390)
(`(flatBytes prog).length < 2^32`) and
[`stackFits`](../../../LirLean/Spec/WellFormed.lean#L413) (`maxChargeDepth prog ≤ 1024`).
Field glosses: [`RunDefinableG`](../../../LirLean/Spec/WellFormed.lean#L20) — along any run
prefix, each statement's operands are bound
([`StmtDefinableG`](../../../LirLean/Spec/WellFormed.lean#L14) treats `.gas` as always
definable, `.call` as needing only its two source operands — the gas/call-aware repair of the
unsatisfiable `RunDefinable`, §9); [`DefsConsistent`](../../../LirLean/Spec/WellFormed.lean#L37)
— every def-site agrees with `defsOf`'s first-find registration (closes the
shadowed-spill hole, [lesson 6](../../../LirLean/Realisability/RealisabilitySpec.lean#L48));
[`CFGClosed`](../../../LirLean/Spec/WellFormed.lean#L89) — entry present, jump/branch targets
present and in bounds; [`DefEnvOrdered`](../../../LirLean/Spec/WellFormed.lean#L99) — program
order topologically orders the recompute def-graph;
[`RevalidatesPerBlock`](../../../LirLean/Spec/WellFormed.lean#L85) — the per-block staleness
invalidation set ([`invalStep`](../../../LirLean/Spec/WellFormed.lean#L52)) empties out;
`slotAddr` — spilled slots are addressable. `RunDefinableG` and `RevalidatesPerBlock` are the
two fields quantifying over run prefixes/states rather than program text alone — decidable in
principle per program but not yet packaged as a checker (the map's "R9 checker territory").
The bridge [`wellLowered_of_IRWellFormed`](../../../LirLean/Realisability/RealisabilitySpec.lean#L125)
(closed, no sorry) re-derives the ~15 internal per-cursor bounds from the two scalars via
[`pcBounds_of_codeFits`](../../../LirLean/Spec/BudgetDerivations.lean#L213) and
[`stackBounds_of_stackFits`](../../../LirLean/Spec/BudgetDerivations.lean#L295), so the
*public* surface carries only `IRWellFormed + codeFits + stackFits` while the `Sim/` machinery
keeps consuming the internal [`WellLowered`](../../../LirLean/Realisability/Surface.lean#L151)
adapter.

### 7.3 Trusted import cone and the split-surface finding

Everything in the flagship's *statement* now resolves to `Spec/*` + exp003:
`lower` (Spec/Lowering), `runWithLog`/`realised*`/`observe` (Spec/Recorder →
Spec/Recorder), `RunFrom`/`RunFromAll`/streams (Spec/Semantics), `entryState`/`clean`/
`Conforms`/`NoGasReads` (Spec/Conformance), `IRWellFormed`/`codeFits`/`stackFits`
(Spec/WellFormed), `PrecompileAssumptions` (Spec/Seams), and exp003's
`CallParams`/`beginCall`/`Account`/`GasConstants`/
[`seedFuel`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean#L71)
(reviewed in [01-trusted-base](01-trusted-base.md)). The previously stranded vocabulary —
`RunFromLeft`/`RunFromAll` and `evmV2CallEntry`/`evmV2CreateEntry` — **has been hoisted**
(now at [Spec/Semantics.lean#L144](../../../LirLean/Spec/Semantics.lean#L144) and
[Spec/Recorder.lean](../../../LirLean/Spec/Recorder.lean); the
[`Surface.lean` §1 header](../../../LirLean/Realisability/Surface.lean#L24) records the
hoist). What remains outside `Spec/` is only *derived* hypothesis machinery
(`WellLowered`, `RecorderCoupled`, `StmtTies'`/`TermTies'`,
[`CallRealisesS`](../../../LirLean/Realisability/Surface.lean#L78)) — none of it appears in
any flagship signature, so a skeptic need not trust it, and the flagship *theorem* itself
still lives in the WIP file, not in `Spec/`.

**Import inversions — still present** (a `Spec/` reader cannot go bottom-up in import order):

* [`Spec/WellFormed.lean`](../../../LirLean/Spec/WellFormed.lean#L1) imports
  `Materialise/MaterialiseGas` (for [`chargeCache`](../../../LirLean/Materialise/MaterialiseGas.lean#L121)),
  `Materialise/DefsSound` (for [`usesInExpr`](../../../LirLean/Materialise/DefsSound.lean#L53),
  [`NonRecomputable`](../../../LirLean/Materialise/DefsSound.lean#L127), `isGasDef`…), and
  `Decode/DecodeLower` (for [`flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L45)).
* [`Spec/Seams.lean`](../../../LirLean/Spec/Seams.lean#L1) imports `Drive/CallPreservesSelf`,
  `Decode/Modellable`, `BytecodeLayer/Hoare/CleanHalt` and *forwards* their predicates
  ([`SelfPresent`](../../../LirLean/Drive/SelfPresent.lean#L353),
  [`CallsCode`](../../../LirLean/Decode/Modellable.lean#L410),
  [`CleanHaltsNonException`](../../../../../EVM/BytecodeLayer/Hoare/CleanHalt.lean#L62)).
* [`Spec/Recorder.lean`](../../../LirLean/Spec/Recorder.lean#L1) imports `Frame/Call`/
  `Frame/Create` (for the `evmCallOracle`/`evmCreateOracle` projections), pulling the whole v1
  frame layer under `Spec/Recorder` → `Spec/Conformance`.
* [`Spec/BudgetDerivations.lean`](../../../LirLean/Spec/BudgetDerivations.lean#L1) imports
  `CfgSim/LowerConforms` and `Sim/SimStmt` — the heaviest inversion, though this file is
  proofs (derived bricks), not statement vocabulary, and arguably belongs outside `Spec/`.

The definitions pulled through these imports are themselves definition-shaped (no proof
content leaks into the *meaning* of the flagship), but the layering makes "read `Spec/` and
stop" impossible without this report's links. Recommendation: hoist the handful of leaf
definitions (`chargeCache`'s fold, `flatBytes`, `usesInExpr`/`NonRecomputable`, the seam
predicates, the oracle projections) into `Spec/`-local homes and re-point the proof layer,
and move `BudgetDerivations.lean` out of `Spec/`.

## 8. Budget derivations — [`Spec/BudgetDerivations.lean`](../../../LirLean/Spec/BudgetDerivations.lean)

Pure derived bricks (no new spec content): from `codeFits` alone, every per-cursor pc/offset
bound the sim layer wants — bundled as
[`pcBounds_of_codeFits`](../../../LirLean/Spec/BudgetDerivations.lean#L213) (offset table,
sstore/sload cursors, ret/stop/jump/branch terminators, gas stash `+34`, ret epilogue `+100`);
from `stackFits`, the per-cursor stack-room bundle
[`stackBounds_of_stackFits`](../../../LirLean/Spec/BudgetDerivations.lean#L295) via the
`chargeDepth` folds ([`maxChargeDepth`](../../../LirLean/Spec/WellFormed.lean#L408)); plus
[`slots_slot_of_defsOf`](../../../LirLean/Spec/BudgetDerivations.lean#L334) (every registered
slot is canonical `slotOf`). Proofs are list-algebra + `omega`; nothing here is trusted.

## 9. IR metatheory — [`Law.lean`](../../../LirLean/Law.lean), [`IRRun.lean`](../../../LirLean/IRRun.lean)

The determinism ladder gives the "*the* observable" reading of the flagship's existential:

```lean
-- Law.lean#L173
theorem IRRun.det {prog : Program} {w₀ : World} {T : Trace} {C : CallStream}
    {D : CreateStream} {O O' : Observable}
    (h₁ : IRRun prog w₀ T C D O) (h₂ : IRRun prog w₀ T C D O') : O = O'
```

([`EvalStmt.det`](../../../LirLean/Law.lean#L34) →
[`RunStmts.det`](../../../LirLean/Law.lean#L68) →
[`RunFrom.det`](../../../LirLean/Law.lean#L86) → `IRRun.det`; structural induction, the
popped stream heads pinned by the shared input streams — this is where positional streams pay
off: same program + same streams ⇒ same observable, so `lower_conforms`'s `∃ O` is unique.)

[`IRRun.lean`](../../../LirLean/IRRun.lean) is the *existence* half for the gas-free,
call-free fragment ([`evalStmt_exists`](../../../LirLean/IRRun.lean#L81) →
[`runStmts_exists`](../../../LirLean/IRRun.lean#L122)), with the definability supply
[`RunDefinable`](../../../LirLean/IRRun.lean#L155). **Caveat verified:**
[`StmtDefinable`](../../../LirLean/IRRun.lean#L61) is literally `False` on `.call`/`.create`
and excludes `.gas`, so `RunDefinable` is unsatisfiable for any program using those features —
audited in [RealisabilitySpec lesson 4](../../../LirLean/Realisability/RealisabilitySpec.lean#L34)
and replaced on the flagship surface by
[`RunDefinableG`](../../../LirLean/Spec/WellFormed.lean#L20). `RunDefinable` remains consumed
only by the old default-lib producer `lower_conforms_cyclic'`
([DriveSim](../../../LirLean/Drive/DriveSim.lean#L512)), i.e. it is honest *fragment*
metatheory, not flagship vocabulary — but its name invites confusion with `RunDefinableG` and
a rename/deprecation note would help.

## 10. Results taxonomy

* **Headline (target) statements** — [`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L251),
  [`lower_conforms_exact`](../../../LirLean/Realisability/RealisabilitySpec.lean#L302),
  [`lower_conforms_gasfree`](../../../LirLean/Realisability/RealisabilitySpec.lean#L341):
  all **conditional on the sorry'd producer/obligations** (R11's
  `runFrom_of_driveCorrLog`, R10a, R11-all's producer, plus R12a) — statements to review, not
  results to cite. The closed pieces inside the same file:
  [`wellLowered_of_IRWellFormed`](../../../LirLean/Realisability/RealisabilitySpec.lean#L125),
  [`conforms_of_worldeq`](../../../LirLean/Realisability/RealisabilitySpec.lean#L204),
  [`termTies'_of_runWithLog`](../../../LirLean/Realisability/Producer.lean#L2642).
* **Trusted definitions** — everything in §§2–7 quoted above; no proof needed, only reading.
* **Supporting bricks (closed, default lib)** — the determinism ladder (§9), the recorder
  adequacy pair (§5), the entry bridges
  ([`callRealises_bridge`](../../../LirLean/CallRealises.lean#L77),
  [`createRealises_bridge`](../../../LirLean/CallRealises.lean#L118)), the budget bundle
  (§8), the `matCache` fixpoint algebra
  ([`matCache_unfold`](../../../LirLean/Spec/WellFormed.lean#L349),
  [`matCache_remat`](../../../LirLean/Spec/WellFormed.lean#L376),
  [`matCache_slot`](../../../LirLean/Spec/WellFormed.lean#L381)).
* **Examples** — [`exProg`](../../../LirLean/Realisability/Witness.lean#L38) and its
  `decide`d budgets: the designated non-vacuity witness; R12b consumes it, nothing else does.
* **Verification** — reported, not re-run: default lib sorry-free (all `sorry`s are in
  `WIP`-only `Machinery`/`Producer`/`RealisabilitySpec`), axiom guards green in
  [`Audit.lean`](../../../LirLean/Audit.lean#L27), no `native_decide`/`bv_decide` in `LirLean/`.

## 11. Smells & rough edges (each with its blast radius)

1. **The recorder fence (§5) is the big one** — definitional trust in *which* events are
   logged. The flagship depends on it wholly; there is no way to reduce it except reading
   `driveLog`. Contained (40 lines) but load-bearing.
2. **`Trace` alias** ([Semantics.lean#L22](../../../LirLean/Spec/Semantics.lean#L22)):
   "compatibility alias" for `GasOracle`, still used in ~49 binder sites including the trusted
   metatheory statements (`IRRun.det`). Two names for one stream in the trusted surface;
   cosmetic, but worth finishing the rename. No headline risk.
3. **`evalExpr`'s `obs` parameter** ([Semantics.lean#L34](../../../LirLean/Spec/Semantics.lean#L34)):
   a gas-as-expression special case that survives only as the pinned phantom `evalExpr st 0`
   plus `e ≠ .gas` side conditions ([`assignPure`](../../../LirLean/Spec/Semantics.lean#L51)).
   Harmless-but-awkward spec: `.gas` inside a *compound* expression is unrepresentable in the
   semantics (only top-level `assign t .gas` pops the stream) yet `Expr.gas` is a first-class
   constructor, so ill-formed uses are carved out by side conditions instead of by the
   grammar. Slated for deletion per the target-architecture notes; isolated.
4. **`lower` is total and emits garbage on ill-formed input** (§4): unregistered tmps
   materialise as `PUSH32 0`, `PUSH4` offsets truncate mod 2^32. Deliberate; soundness is
   recovered by `IRWellFormed` + `codeFits`/`stackFits` in the theorem. Fine, but any reader
   quoting `lower` without the static bundle overclaims.
5. **Spec files mixing proofs and imports upward** (§7.3): `WellFormed.lean` is half spec,
   half `matCache` proof development; `BudgetDerivations.lean` is all proofs inside `Spec/`;
   `Seams`/`Recorder` forward proof-layer definitions. No soundness issue, real
   review-ergonomics issue.
6. **`RunDefinable` vs `RunDefinableG`** (§9): an unsatisfiable-for-the-target-domain bundle
   still lives in the default lib under the better name. Rename or docstring-deprecate.
7. **`observe`'s result channel** (§5): STOP ≡ empty RETURN, >32-byte outputs truncated by
   `uInt256OfByteArray`. Within the IR's expressible outputs this is exact; as a spec
   definition it is coarser than it looks.
8. **`RunLog.clean` zero-gas-revert corner** (§7.1): documented, sound, scope-cutting.

## 12. Source-vs-doc discrepancies

* [`docs/codebase-map-2026-07-06.md`](../../codebase-map-2026-07-06.md) is **stale on two
  spec-layer findings** (both since fixed, per the recent R11 boundary-support commits):
  its §4.1/5.1 say `RunFromLeft`/`RunFromAll` and the exact-run vocabulary "still need
  hoisting" — they are now in [Spec/Semantics.lean#L144-L190](../../../LirLean/Spec/Semantics.lean#L144);
  and its §5.10 says `Spec/Recorder.lean` imports `CallRealises` — it now imports
  [`Spec/Recorder`](../../../LirLean/Spec/Recorder.lean#L1) instead (the deeper
  `Spec → Frame/Engine/Drive` inversions of §7.3 *do* remain, so §5.10 is half-fixed).
* [`docs/planning/r11-plan-2026-07-08.md`](../../planning/r11-plan-2026-07-08.md) matches
  source where checked (`RunFromAll` shape of `lower_conforms_exact`, the
  no-derive-from-`runFromLeft_exists` rule, the create-suffix deferral in
  [`RecorderCoupled.restart`](../../../LirLean/Realisability/Surface.lean#L244)).
* File docstrings that make status claims (`Surface.lean` "sorry-free §1",
  `IRRun.lean`/`CallRealises.lean` "no sorry/axiom") all verify against grep.

## 13. Recommendations

1. Finish the `Trace` → `GasOracle` rename and delete `evalExpr`'s `obs` parameter (fold
   `.gas` handling entirely into `EvalStmt`, or remove `Expr.gas` in favour of a dedicated
   statement) — both purely mechanical, both shrink the trusted reading surface.
2. Break the `Spec/` import inversions (§7.3): hoist `flatBytes`, `chargeCache`,
   `usesInExpr`/`NonRecomputable`, the seam predicate definitions and the oracle projections;
   move `BudgetDerivations.lean` (and `WellFormed.lean`'s proof half) out of `Spec/`.
3. Add a short "recorder trust fence" docstring on `driveLog` itself stating exactly what is
   proved (`driveLog_drive`) vs definitional (the channel gates) — §5's content belongs in
   the source, since it is the one thing adequacy does *not* cover.
4. Rename or deprecate `RunDefinable` (§9) to stop it shadowing `RunDefinableG`'s role.
