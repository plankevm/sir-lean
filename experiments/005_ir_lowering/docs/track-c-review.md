# Track C review — exp005: `LirLean` IR → EVM bytecode, lowering preserved (CLOSED)

Scope: the whole `experiments/005_ir_lowering` package (branch `exp005-ir`,
worktree `../evm-semantics-wt/ir-lowering`). All links are relative to this file's
directory (`experiments/005_ir_lowering/docs/`); source modules are one level up
(`../LirLean/…`), the exp003 reasoning layer two-and-over (`../../003_bytecode_layer/…`).

> **This refresh supersedes the pre-C3g version.** The previous report described the
> headline as carrying two honest hypotheses (the concrete child `CallReturns` and the
> post-CALL branch terminator). **Both are now discharged** (C3f / C3g), and the doc
> drift items the old report surfaced have been (mostly) reconciled in `ir-design.md`.
> See §6 and §7.

---

## TL;DR

Track C defines a fresh high-level IR ([`LirLean`](../LirLean/IR.lean#L54)) with
**storage arithmetic, external calls, branching, and gas introspection**, lowers it
to `Evm.decode`-compatible EVM bytecode ([`lower`](../LirLean/Lowering.lean#L197)),
and proves the lowering preserves semantics by reusing exp003's `Runs` /
`messageCall_runs` reasoning layer — *no new boundary theory*. The headline
[`wc_preserves`](../LirLean/WorkedCall.lean#L1688) is now **FULLY HYPOTHESIS-FREE**:
for the worked program (IR → bytecode through an external CALL + storage write +
arithmetic + a gas-shaped branch), running it as a top-level `messageCall` delivers the
`RETURN` frame's result, assuming only a gas knob `g ≥ 50000`. The two former honest
hypotheses are both closed — the concrete child `CallReturns`
([`wc_callReturns`](../LirLean/WorkedCall.lean#L718)) is hypothesis-free, and the
post-CALL branch terminator is discharged axiom-cleanly
([`wc_get_dest_414`](../LirLean/WorkedCall.lean#L796)) now that Track A detotalized
`validJumpDests`. The most important structural finding stands:
[`wc_preserves_twoCall`](../LirLean/WorkedCall.lean#L1711) shows **multi-call (C4)
needed zero new theory** — exp003's `Runs.call` constructor composes any number of
returning calls into one `Runs`.

Verification (I re-ran it): `lake build` green (1130 jobs); `#print axioms` on
`wc_preserves` / `wc_preserves_twoCall` / `wc_callReturns` / `wcPostRun` /
`wcRetFrame_halts` / `wc_get_dest_414` = `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, no `native_decide`/`bv_decide`, no `admit`. Grep confirms every
`sorry`/`axiom`/`native_decide` token in `LirLean/*.lean` lives in a comment. The
`set_option maxHeartbeats 2000000` flagged by the old report is **gone**; only
[`maxRecDepth 100000`](../LirLean/WorkedCall.lean#L90) remains (see Smells).

---

## 1. Goal & context

The real-world property: **a compiler back-end that lowers a structured IR to EVM
bytecode does not change observable behaviour.** Track C is the first *consumer* of
exp003's bytecode reasoning layer ([`PLAN.md` Goal](../PLAN.md#L6)), and it doubles
as the acceptance test for Track A's multi-call redesign: lowering a multi-call IR
program proves-or-disproves that A's `Runs.call` composes
([`currentplan.md`](../../../currentplan.md#L85)).

The IR is deliberately built around the three primitives the broader experiment
actually needs — storage arithmetic, external CALL, and branching — because
**branching is what makes gas-introspection reasoning meaningful** (a `GAS`-dependent
branch). The honesty constraint from project memory is encoded structurally: `gas` is
a first-class expression, the IR threads an honest gas counter, and gas-independence
of a given program is a *theorem about that program*, never a modelling shortcut
([`ir-design.md` "Why gas belongs in the IR"](ir-design.md#L109)).

End goal ([`currentplan.md` END GOAL](../../../currentplan.md#L68)): this lowering
currently targets exp003's *flat* surface (`messageCall` / `Runs`). The culminating
objective is a shared `EVMSemantics` interface that both the flat (exp003) and nested
(exp004) semantics instantiate; "Track C consumes whichever interface, ideally the
shared one" ([`currentplan.md`](../../../currentplan.md#L85)). See §7 for what
changes if the lowering retargets that interface.

---

## 2. The abstraction stack (bottom-up)

Eight source modules, layered so each rests only on the ones below it.

| Module | Role | Headline export(s) |
|---|---|---|
| [`IR.lean`](../LirLean/IR.lean) | IR datatypes (grammar) | [`Expr`](../LirLean/IR.lean#L54), [`Stmt`](../LirLean/IR.lean#L70), [`Term`](../LirLean/IR.lean#L82), [`CallSpec`](../LirLean/IR.lean#L43) |
| [`Lowering.lean`](../LirLean/Lowering.lean) | `lower : Program → ByteArray` (recompute-on-use, two-pass offsets) | [`lower`](../LirLean/Lowering.lean#L197) |
| [`SmallStep.lean`](../LirLean/SmallStep.lean) | small-step, gas-aware IR semantics | [`IRState`](../LirLean/SmallStep.lean#L56), [`evalExpr`](../LirLean/SmallStep.lean#L90) |
| [`DecodeLower.lean`](../LirLean/DecodeLower.lean) | generic decode-from-lowering bricks (the `bget`/`bextract` foundation) | [`decode_nonpush_of_list`](../LirLean/DecodeLower.lean#L88), [`decode_lower_push`](../LirLean/DecodeLower.lean#L139) |
| [`Layout.lean`](../LirLean/Layout.lean) | offset-table byte-layout arithmetic (prefix-sum, symbolic) | [`stmt_byte_anchor`](../LirLean/Layout.lean#L163) |
| [`Match.lean`](../LirLean/Match.lean) | the `Match` invariant + per-construct simulation lemmas + boundary discharge | [`Match`](../LirLean/Match.lean#L123), [`lower_preserves_discharge`](../LirLean/Match.lean#L333) |
| [`Decode.lean`](../LirLean/Decode.lean) | build-enforced decode round-trip on `workedCall` (the demo) | [`workedCall`](../LirLean/Decode.lean#L45) |
| [`WorkedCall.lean`](../LirLean/WorkedCall.lean) | concrete `Runs` assembly + `wc_preserves` for `workedCall` | [`wc_preserves`](../LirLean/WorkedCall.lean#L1688) |

Dependency edges feeding the headline:

```
IR ──> Lowering ──> DecodeLower ──> Layout ──┐
   └─> SmallStep ───────────────────────────┼─> Match ──> WorkedCall
                                             │            (wc_preserves)
exp003: Runs / Runs.call / messageCall_runs ─┘  (boundary discharge)
Track A: validJumpDests / ReachesBoundary ───┘  (branch terminator, §6)
```

`Match` is the hinge: it consumes `Layout`+`DecodeLower` (to discharge the pc clause
`M1` generically) and `SmallStep` (to read the IR side), and it consumes exp003's
opcode `runs_*` rules + the `messageCall_runs` bridge. `WorkedCall` assembles a
concrete `Runs` for one program and crosses the bridge once.

---

## 3. The IR design and its decision (§1–§3 of the design doc)

### 3.1 Fresh `LirLean` vs. extend exp002's `SirLean`

The decision was **a fresh IR**, not an extension of exp002's SSA/CFG IR. The
argument ([`ir-design.md` §1](ir-design.md#L9)) is concrete and, in my reading,
sound — these are not stylistic preferences but four hard incompatibilities:

1. **Word size.** `SirLean.Word = UInt32`; every exp003 quantity is 256-bit. Reusing
   it means rewriting `IR/State/Eval/SmallStep/Proof` to `UInt256` — nothing of the
   old proof layer survives, so there is no reuse to preserve.
2. **State model.** `SirLean.World = Word → Word` cannot name *which account* —
   exactly what an external CALL changes. The EVM lens is a map of accounts.
3. **No external CALL** in `SirLean.Op` — adding it is a new effect + re-proving
   `progress`/`eval?_iff_steps`, i.e. a rewrite.
4. **No gas / gas introspection** — the headline reason the IR needs branching.

What is kept is only the *structural idea*: a CFG of basic blocks ending in branch
terminators, which lowers cleanly (block → `JUMPDEST`-led run; terminator →
`JUMP`/`JUMPI`/`STOP`/`RETURN`). I find the decision well-justified.

### 3.2 The grammar

The IR is a **register (temporary) machine** — stack-free — over named `Tmp`s,
organised as a CFG. Verbatim ([`IR.lean`](../LirLean/IR.lean#L54)):

```lean
inductive Expr where
  | imm   (w : Word)        -- PUSH32 w
  | tmp   (t : Tmp)         -- read a local
  | add   (a b : Tmp)       -- ADD
  | lt    (a b : Tmp)       -- LT → 0/1
  | sload (key : Tmp)       -- SLOAD
  | gas                     -- GAS  ← introspection

inductive Stmt where
  | assign (t : Tmp) (e : Expr)
  | sstore (key value : Tmp)
  | call   (cs : CallSpec)

inductive Term where
  | ret    (t : Tmp)
  | stop
  | jump   (dst : Label)
  | branch (cond : Tmp) (thenL elseL : Label)   -- JUMPI
```

The external-call payload is the value-free, calldata-free shape exp003's bridge
already supports ([`CallSpec`](../LirLean/IR.lean#L43)):

```lean
structure CallSpec where
  callee    : Tmp
  gasFwd    : Tmp                 -- may be Expr.gas-derived — the introspection coupling
  resultTmp : Option Tmp          -- where to bind the 0/1 success flag
```

All three required primitives are first-class: storage arith (`sload`/`sstore`/`add`/
`lt`), CALL (`Stmt.call`), branching (`Term.branch`), and gas introspection
(`Expr.gas`, usable as a `branch` condition).

### 3.3 Small-step, gas-aware semantics

The semantics is **small-step with an explicit gas counter** so each IR step lines up
with one exp003 `Runs` segment ([`ir-design.md` §3](ir-design.md#L121)). The machine
state ([`SmallStep.lean`](../LirLean/SmallStep.lean#L56)):

```lean
structure IRState where
  locals  : Tmp → Option Word
  storage : Word → Word          -- self account's storage, observable lens
  gas     : UInt64               -- equals fr.exec.gasAvailable EXACTLY (M4)
```

A key modelling choice that pays off in `Match`: `gas` is a `UInt64`, not `ℕ`, so the
gas clause `M4` is a plain `UInt64` equality and each IR charge is the *same*
`UInt64.ofNat <const>` subtraction the EVM post-frame performs. Expression evaluation
reuses exp003's own arithmetic, so the IR value is **definitionally** the word the
lowered opcode pushes ([`evalExpr`](../LirLean/SmallStep.lean#L90)):

```lean
def evalExpr (st : IRState) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.storage key)
  | .gas     => some (UInt256.ofUInt64 st.gas)
```

`SmallStep.lean` ships the *ingredients* (`evalExpr`, `setLocal`, `setStorage`,
`charge`, cursor accessors), not a single `IRStep` inductive: the per-construct
simulation is stated frame-locally in `Match.lean`, and the program-global assembly is
done concretely per worked program in `WorkedCall.lean`. The design doc now reflects
this as-built (it no longer claims a generic `lower_simulates_step` engine — see §7).

---

## 4. The lowering (§4)

[`lower`](../LirLean/Lowering.lean#L197) is a two-pass, fixed-width emission:

```lean
def lower (prog : Program) : ByteArray :=
  let defs := defsOf prog
  let fuel := recomputeFuel prog
  let labelOff := offsetTable defs fuel prog.blocks
  let bytes : List UInt8 :=
    prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody defs fuel labelOff b)
  ⟨bytes.toArray⟩
```

Three design choices, all argued well:

- **Recompute-on-use.** Operands are materialised onto the stack by re-emitting the
  push-sequence of each tmp's defining expression
  ([`materialiseExpr`](../LirLean/Lowering.lean#L95)); an `assign` itself emits **no**
  bytes ([`emitStmt`](../LirLean/Lowering.lean#L132)). This mirrors exp003's
  hand-written programs (push a literal immediately before consuming it) and — the key
  payoff — it lets the `Match` invariant **drop the register↔slot map entirely**
  (§5.1). Its cost is code size and that it is correct only when each tmp has a single
  global definition ([`defsOf`](../LirLean/Lowering.lean#L164) takes the last `assign`).
- **Two-pass, fixed-width destinations.** Every destination push is a `PUSH4`
  ([`emitDest`](../LirLean/Lowering.lean#L90)), so block lengths are independent of
  the resolved offset table and layout is a simple prefix sum
  ([`offsetTable`](../LirLean/Lowering.lean#L190)) — no fixpoint over
  push-width-vs-offset. This is exactly what makes the offset table *provably* correct
  (the `Layout` lemmas, §5.2).
- **Per-construct templates** ([`emitStmt`](../LirLean/Lowering.lean#L132),
  [`emitTerm`](../LirLean/Lowering.lean#L147)) match the opcode `runs_*` rules exp003
  provides, so the simulation reads off cleanly.

Decode-compatibility is **build-enforced** in [`Decode.lean`](../LirLean/Decode.lean):
≈40 `example … := by rfl` checks pin `Evm.decode (lower workedCall) pc = expected` at
every emitted pc of the worked program (520 bytes, block JUMPDESTs at 0/414/518). The
two `PUSH4` branch destinations (414, 518) are shown to land on real `JUMPDEST`s via
`rfl` decode checks
([`Decode.lean` block-1/2](../LirLean/Decode.lean#L120)).

> **Internal stale comment (minor).** `Decode.lean`'s docstring
> ([L134](../LirLean/Decode.lean#L134)) still describes `validJumpDests` as a
> `partial def` to be avoided. That cautionary note predates Track A's detotalization
> (§6); `WorkedCall.lean` now uses `validJumpDests` directly and axiom-cleanly. The
> `Decode.lean` `rfl` checks are still correct and self-sufficient — but the comment's
> rationale ("the only way to evaluate it in a proof is `native_decide`") is no longer
> true and should be softened.

---

## 5. The preservation architecture (the specs that matter)

The architecture is **invariant + per-construct simulation + single-bridge
discharge**, not a monolith. Bottom-up:

### 5.1 The `Match` invariant — six fields, no slot map

[`Match`](../LirLean/Match.lean#L123) relates a running IR configuration to an EVM
`Frame`:

```lean
structure Match (prog : Program) (L : Label) (pc : Nat) (st : IRState) (fr : Frame) : Prop where
  pc_eq      : fr.exec.pc = UInt32.ofNat (pcOf prog L pc)          -- M1
  code_eq    : fr.exec.executionEnv.code = lower prog             -- M2
  storage_eq : ∀ k, selfStorage fr k = st.storage k              -- M3
  gas_eq     : fr.exec.gasAvailable = st.gas                     -- M4
  stack_nil  : fr.exec.stack = []                                -- M5
  can_modify : fr.exec.executionEnv.canModifyState = true
```

The `M5` empty-stack clause is the recompute-on-use payoff made formal: between
statements there is no register state on the stack, so `Match` needs no slot map. `M1`
is pinned to the offset-table address [`pcOf`](../LirLean/Match.lean#L64), a computable
prefix sum. `M3` reads storage through the same observable lens
([`selfStorage`](../LirLean/Match.lean#L111)) exp003's `sstoreFrame_storage_self` uses.

Honest assessment of `Match`'s hypotheses: nothing here smuggles the conclusion. The
clauses are exactly the correspondences a simulation needs; `can_modify` is a normal
top-level-call standing condition.

### 5.2 The `M1` discharge — generic byte-layout arithmetic

This is genuinely strong work, and the part that exp003 lacked. Two layers:

**Foundations** ([`DecodeLower.lean`](../LirLean/DecodeLower.lean)). exp003's decode
checks reduce the *whole* lowered array by kernel `rfl` per program. Track C factored
out the program-independent core via two list-backed-`ByteArray` lemmas
([`bget`](../LirLean/DecodeLower.lean#L56), [`bextract`](../LirLean/DecodeLower.lean#L65))
and two generic decode lemmas:

```lean
theorem decode_nonpush_of_list (l : List UInt8) (n : Nat) (byte : UInt8)
    (hn : n < 2 ^ 32) (hb : l[n]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0) :
    Evm.decode ⟨l.toArray⟩ (UInt32.ofNat n) = some (Evm.parseInstr byte, .none)
```

([`decode_push_of_list`](../LirLean/DecodeLower.lean#L104) is the PUSH analogue,
plus `lower`-specialised forms
[`decode_lower_nonpush`](../LirLean/DecodeLower.lean#L132) /
[`decode_lower_push`](../LirLean/DecodeLower.lean#L139)). A decode obligation over
`lower prog` reduces to a *list-local* fact: which byte `flatBytes prog` holds at the pc.

**The prefix-sum decomposition** ([`Layout.lean`](../LirLean/Layout.lean)). The payoff
is [`stmt_byte_anchor`](../LirLean/Layout.lean#L163): over an **arbitrary** program,
the byte at the offset-table address of a statement cursor is the head byte of that
statement's emitted opcodes. It composes
[`flatMap_split`](../LirLean/Layout.lean#L74), the offset-table-as-prefix-sum
([`blockPrefix_length`](../LirLean/Layout.lean#L94)), and the length-invariance lemma
([`emitBlockBody_length_labelOff`](../LirLean/Layout.lean#L53)) — the last being why
the fixed-width `PUSH4` choice matters formally. The `pcOf`-level wrapper
[`flatBytes_at_pcOf`](../LirLean/Match.lean#L99) ties this back to `pcOf` so the engine
gets `decode (lower prog) (pcOf …)` symbolically, not by per-program `rfl`. Proof
strategy (one sentence): `pcOf` collapses to the offset-table anchor when the block
exists, then `stmt_byte_anchor` indexes into a three-way list append. This is
exercised end-to-end at a *symbolic* cursor in
[`Decode.lean`](../LirLean/Decode.lean#L176).

### 5.3 Per-construct simulation lemmas (the bricks)

Each effecting construct gets one frame-local lemma wrapping the corresponding exp003
`runs_*` rule and reading back the IR-side post-frame fact. Representative
([`sim_sstore`](../LirLean/Match.lean#L212)):

```lean
theorem sim_sstore (fr : Frame) (key value : Word) (rest : Stack Word) (acc : Account)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: value :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key value ≤ fr.exec.gasAvailable.toNat)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (hnz : value ≠ 0) :
    Runs fr (sstoreFrame fr key value rest)
      ∧ storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address key = value
      ∧ ∀ k', k' ≠ key → storageAt (sstoreFrame …) … k' = storageAt fr … k'
```

The full brick set: [`sim_imm`](../LirLean/Match.lean#L149),
[`sim_gas`](../LirLean/Match.lean#L161), [`sim_add`](../LirLean/Match.lean#L173),
[`sim_lt`](../LirLean/Match.lean#L185), [`sim_sload`](../LirLean/Match.lean#L198),
[`sim_sstore`](../LirLean/Match.lean#L212), [`sim_jump`](../LirLean/Match.lean#L267),
[`sim_branch`](../LirLean/Match.lean#L282), [`sim_call`](../LirLean/Match.lean#L307);
plus the two halt steps [`halt_stop`](../LirLean/Match.lean#L240) /
[`halt_ret`](../LirLean/Match.lean#L249). Each is a thin discharge to its exp003 rule
— that is the intent: they wrap the rule with the IR-state reading. The
[`sim_call`](../LirLean/Match.lean#L307) brick is just a `Runs.call` node — the CALL is
never a `runs_*` step.

### 5.4 The boundary discharge → `messageCall_runs`

The construct-agnostic bridge half
([`lower_preserves_discharge`](../LirLean/Match.lean#L333)):

```lean
theorem lower_preserves_discharge (prog : Program) (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (_hcode : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin hruns hhalt
```

This is `messageCall_runs`
([exp003 `CallSequence.lean`](../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L132))
applied at the IR/lowering boundary; the two terminator instances are
[`lower_preserves_stop`](../LirLean/Match.lean#L345) /
[`lower_preserves_ret`](../LirLean/Match.lean#L358). Crucially, the bridge crosses
**regardless of how many `Runs.call` nodes** the assembled run contains.

---

## 6. The headline results — now hypothesis-free

The end-to-end results live in [`WorkedCall.lean`](../LirLean/WorkedCall.lean),
assembled on `lower workedCall` run as a top-level `messageCall` in exp003's
caller/callee world ([`wcParams`](../LirLean/WorkedCall.lean#L97)).

**The single-call headline** ([`wc_preserves`](../LirLean/WorkedCall.lean#L1688)):

```lean
theorem wc_preserves (g : UInt64) (hg : 50000 ≤ g.toNat) :
    ∃ halt, messageCall (wcParams g)
      = .ok (FrameResult.toCallResult (endFrame (wcRetFrame g) halt)) := by
  obtain ⟨halt, hhalt⟩ := wcRetFrame_halts g hg
  refine ⟨halt, ?_⟩
  have hruns : Runs (wcFrame g) (wcRetFrame g) :=
    (wc_prefix_runs g (by omega)).trans (Runs.call (wc_callReturns g hg) (wcPostRun g hg))
  exact lower_preserves_discharge Lir.Decode.workedCall (wcParams g)
    (wc_begin g) rfl hruns hhalt
```

**What it claims (plain English):** for any gas `g ≥ 50000`, executing the lowered
`workedCall` as a top-level `messageCall` runs the whole program — the straight-line
prefix, the external CALL to `0xCA11EE`, the post-CALL gas-shaped branch, and block 1's
`RETURN` — and delivers exactly the `RETURN` frame's halt result. **No hypotheses about
the call or the run remain**; the only knob is `g`. The proof glues three concrete
`Runs` segments into one `Runs (wcFrame g) (wcRetFrame g)` and crosses the bridge once.

The three concrete segments, all now closed:

- **The prefix** ([`wc_prefix_runs`](../LirLean/WorkedCall.lean#L339)) — the genuine
  straight-line run from entry to the CALL site: a kernel-checked `Runs.trans` chain of
  `runs_jumpdest`, two `runs_push`, `runs_sstore`, and seven CALL-arg `runs_push`, gas
  threaded through `subCharges`. (Unconditional given a small gas floor.)
- **The external CALL** — the `Runs.call` node carrying
  [`wc_callReturns`](../LirLean/WorkedCall.lean#L718) (see §6.1 below).
- **The post-CALL run** ([`wcPostRun`](../LirLean/WorkedCall.lean#L1454)) and its halt
  ([`wcRetFrame_halts`](../LirLean/WorkedCall.lean#L1614)) (see §6.2 below).

### 6.1 Former hypothesis (a) — the concrete child `CallReturns`, now CLOSED (C3f)

The earlier `wc_preserves` took `hcall : CallReturns (wcCallSite g) resumeFr` as a
hypothesis. It is now discharged by a genuine, hypothesis-free witness
([`wc_callReturns`](../LirLean/WorkedCall.lean#L718)):

```lean
theorem wc_callReturns (g : UInt64) (hg : 50000 ≤ g.toNat) :
    CallReturns (wcCallSite g) (wcResumed g)
```

**How it was discharged.** It builds the real child `drive` run of the `0xCA11EE`
callee (`PUSH1 5; PUSH1 7; SSTORE; STOP`,
[`wc_child_drive`](../LirLean/WorkedCall.lean#L672)) at the 63/64-capped forwarded gas,
over the **post-SSTORE** parent world, and packages the CALL step
([`wc_call_step`](../LirLean/WorkedCall.lean#L373)), the child entering as code
([`wc_beginCall_child`](../LirLean/WorkedCall.lean#L586)), and the resumed parent
([`wcResumed`](../LirLean/WorkedCall.lean#L711)). The kernel-cost wall — the call-site
`accounts` being the post-SSTORE world threaded through the deep `lower workedCall`
computation — is defeated by the exp003 NAMED-LEMMA pattern: a `g`-independent
[`wcStoredAccounts`](../LirLean/WorkedCall.lean#L434) (built from `callerXfer` + the
self write, **no** `lower` dependence) plus
[`sstore_accounts_congr`](../LirLean/WorkedCall.lean#L414), so the post-SSTORE world,
the SSTORE charge, and the cold-22106 floor
([`wcChildGas_lb`](../LirLean/WorkedCall.lean#L525)) are all derived from cheap,
code-free field facts — never by whole-map reduction. The `g ≥ 50000` floor is exactly
what clears the child's 22106 cold-SSTORE floor after the 63/64 cap.

### 6.2 Former hypothesis (b) — the post-CALL branch terminator, now CLOSED (C3g, on a Track A foundation)

The earlier `wc_preserves` took the post-CALL run `hpost`/`hhalt` as hypotheses,
because the branch could not be discharged: the `JUMPI` step needs
`Frame.get_dest 414 = some 414`, which reads `validJumpDests (lower workedCall) 0` — and
`validJumpDests` was a **`partial def`**, irreducible in a proof without `native_decide`
(which would break the axiom-clean bar). This was the report's single most important
caveat, gated on a *foundation* change.

**How it was discharged.** Track A **detotalized `validJumpDests`** into a total,
kernel-reducible def
([exp003 `Decode.lean`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L126))
with an unfolding equation
([`validJumpDestsAuxNat_eq`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L115))
and a characterization lemma
([`mem_validJumpDests_of_reachable_jumpdest`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L189))
keyed on a [`ReachesBoundary`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L167)
walk of the instruction stream, plus
[`Frame.get_dest_of_mem`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Frame.lean#L39).
Track C consumes these directly: [`wc_reaches_414`](../LirLean/WorkedCall.lean#L757)
walks the lowered byte stream from pc 0 to offset 414 (a 22-step
`ReachesBoundary` derivation, each boundary byte a kernel `decide`);
[`wc_414_mem_validJumps`](../LirLean/WorkedCall.lean#L785) feeds it to the
characterization lemma; and [`wc_get_dest_414`](../LirLean/WorkedCall.lean#L796) packages
the result for any frame whose `validJumps` is the lowered table — **no `native_decide`,
no hypothesis**:

```lean
theorem wc_get_dest_414 (fr : Frame)
    (hvj : fr.validJumps = validJumpDests (lower Lir.Decode.workedCall) 0) :
    fr.get_dest 414 = some 414 :=
  Frame.get_dest_of_mem fr (d := 414) (by decide) (hvj ▸ wc_414_mem_validJumps)
```

With the branch resolvable, [`wcPostRun`](../LirLean/WorkedCall.lean#L1454) is a real
`Runs.trans` chain: block-0 recompute (`PUSH 100; PUSH 9; PUSH 7; SLOAD=5; ADD=14;
LT=1`) → `PUSH4 414` → **taken** `JUMPI` to block 1 → `JUMPDEST` → block-1 recompute →
the `RETURN` frame [`wcRetFrame`](../LirLean/WorkedCall.lean#L1172) (pc 517, stack
`[1,1]`). Three sub-facts make it concrete and unconditional (for `g ≥ 50000`):
1. **Resumed gas (exact).** [`wcResumed_gas`](../LirLean/WorkedCall.lean#L986): the
   `callGasCap` **cancels** between the caller's post-CALL charge and the child's
   leftover, so resumed gas is `g − 46834`; for `g ≥ 50000` that is `≥ 3166`, and the
   post-CALL run spends only `244 (+3 RETURN mem)`.
2. **SLOAD value over the child-committed map.**
   [`wcResumed_sload7`](../LirLean/WorkedCall.lean#L920): the caller's slot 7 is still
   `5` (the child wrote `0xCA11EE`'s slot), so the recomputed `lt = (5+9) < 100 = 1` ⇒
   the `JUMPI` is taken; [`wcResumed_warm7`](../LirLean/WorkedCall.lean#L1013) gives the
   warm SLOAD cost 100.
3. **A general `RETURN` halt.**
   [`stepFrame_return_halts`](../LirLean/WorkedCall.lean#L1079) (existence form) →
   [`wcRetFrame_halts`](../LirLean/WorkedCall.lean#L1614): the materialised `ret t`
   consumes `offset = size = 1` (not exp003's `0,0` shape), `Cₘ 1 − Cₘ 0 = 3 ≤ gas`.

The `hg : 50000 ≤ g.toNat` floor is the single benign knob: enough to clear the cold
SSTORE + CALL costs and the 63/64-capped child floor. Not a smell.

### 6.3 The C4 multi-call corollary — zero new theory

[`wc_preserves_twoCall`](../LirLean/WorkedCall.lean#L1711):

```lean
theorem wc_preserves_twoCall (g : UInt64)
    {fr₀ callFr₁ resumeFr₁ callFr₂ resumeFr₂ last : Frame} {halt : FrameHalt}
    (hbegin  : EntersAsCode (wcParams g) fr₀)
    (hcode   : fr₀.exec.executionEnv.code = lower Lir.Decode.workedCall)
    (hpre    : Runs fr₀ callFr₁)
    (hcall₁  : CallReturns callFr₁ resumeFr₁)
    (hmiddle : Runs resumeFr₁ callFr₂)
    (hcall₂  : CallReturns callFr₂ resumeFr₂)
    (hpost   : Runs resumeFr₂ last)
    (hhalt   : stepFrame last = .halted halt) :
    messageCall (wcParams g)
      = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  lower_preserves_discharge Lir.Decode.workedCall (wcParams g) hbegin hcode
    (hpre.trans (Runs.call hcall₁ (hmiddle.trans (Runs.call hcall₂ hpost)))) hhalt
```

**The key finding, formalized.** This two-call result needed **no new theory**: it is
the same `lower_preserves_discharge`, with two `Runs.call` nodes threaded by
`Runs.trans` into one `Runs`. This works only because exp003's `Runs` makes `call` a
**constructor** ([exp003 `Hoare.lean`](../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L114)):

```lean
inductive Runs : Frame → Frame → Prop where
  | refl (fr : Frame) : Runs fr fr
  | step {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs mid fr') :
      Runs fr fr'
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'
```

So `(step | call)*` is a single `Runs` value, and `messageCall_runs` crosses it once
regardless of call count. This directly validates Track A's redesign: the C1 log flagged
the *old* `messageCall_call_runs` (one call only) as a hard multi-call blocker
([`PLAN.md` C1 log](../PLAN.md#L81)); A's `Runs.call` resolved it, and C4 is now a
structural corollary. **C was the test; A passed.**

> **Honest scope note.** `wc_preserves_twoCall` stays a generic **shape** lemma — it
> takes the two-call assembly as hypotheses — because `workedCall` has exactly **one**
> external CALL, so there is no concrete two-call program to instantiate it. The single
> fully-concrete deliverable is `wc_preserves`. The claim `wc_preserves_twoCall` makes is
> that each `CallReturns` node is closeable exactly like `wc_callReturns` (already shown
> hypothesis-free), so a genuine two-call program would close with no extra theory.

---

## 7. Results taxonomy, smells, and rough edges

**Headline / mainline:** [`wc_preserves`](../LirLean/WorkedCall.lean#L1688)
(fully hypothesis-free), the generic boundary
[`lower_preserves_discharge`](../LirLean/Match.lean#L333), and the multi-call shape
corollary [`wc_preserves_twoCall`](../LirLean/WorkedCall.lean#L1711).

**Supporting bricks (load-bearing):** the concrete `Runs` assembly —
[`wc_prefix_runs`](../LirLean/WorkedCall.lean#L339),
[`wc_callReturns`](../LirLean/WorkedCall.lean#L718),
[`wcPostRun`](../LirLean/WorkedCall.lean#L1454),
[`wcRetFrame_halts`](../LirLean/WorkedCall.lean#L1614),
[`wc_get_dest_414`](../LirLean/WorkedCall.lean#L796); the simulation lemmas
`sim_*`/`halt_*` (§5.3); the generic decode infra
[`decode_nonpush_of_list`](../LirLean/DecodeLower.lean#L88) +
[`bget`/`bextract`](../LirLean/DecodeLower.lean#L56); the layout arithmetic
[`stmt_byte_anchor`](../LirLean/Layout.lean#L163) +
[`flatBytes_at_pcOf`](../LirLean/Match.lean#L99); and the gas-threading /
storage-lens named lemmas (`wcResumed_gas`, `wcResumed_sload7`, `wcStoredAccounts`,
`sstore_accounts_congr`). The decode/layout bricks are the genuine new contribution
exp003 lacked; they are reusable for any program. The Track A foundation lemmas
([`mem_validJumpDests_of_reachable_jumpdest`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Decode.lean#L189),
[`Frame.get_dest_of_mem`](../../003_bytecode_layer/EVMLean/Evm/Semantics/Frame.lean#L39))
are load-bearing for the branch and now under the headline.

**Examples / demos:** [`workedCall`](../LirLean/Decode.lean#L45) and its ≈40 `rfl`
decode checks; the symbolic-`pcOf` example
([`Decode.lean`](../LirLean/Decode.lean#L176)). `wc_preserves` *does* consume
`workedCall` (so the demo program is load-bearing for the headline, but the per-pc `rfl`
checks themselves are leaves no theorem consumes).

**Smells / weak proofs:**

- [`maxRecDepth 100000`](../LirLean/WorkedCall.lean#L90) in `WorkedCall.lean`. `lower`
  produces 33-byte `PUSH32` literals and the decode facts reduce the byte stream in the
  kernel, so the recursion limit is raised. **The `maxHeartbeats 2000000` crank the old
  report flagged is gone** — the file's own comment records that factoring the decode
  facts into independent `wc_dec_*` lemmas (each reduces one literal pc) keeps every
  elaboration under the *default* heartbeat budget. **Does a headline depend on the
  remaining `maxRecDepth`?** Yes — transitively through `wc_prefix_runs`/`wcPostRun`. It
  is a contained recursion-depth knob (not a heartbeat blow-up), and it sits only under
  the concrete per-program assembly, not the generic `Layout`/`DecodeLower` lemmas. Lower
  risk than the prior heartbeat crank.
- `by decide`/`by rfl` are used pervasively but on small terms (gas arithmetic, single
  immediates, individual boundary bytes in `wc_reaches_414`); not flagged as brittle.

**Source-vs-doc status (the three old drift items):**

1. **`IRStep` / `lower_simulates_step` — RECONCILED in the doc.** The old report flagged
   `ir-design.md` §6 as over-claiming a generic engine. `ir-design.md` §6 is now titled
   **"AS-BUILT"** ([`ir-design.md` §6](ir-design.md#L291)) and states explicitly: *"That
   generic engine is not built"* ([L308](ir-design.md#L308)). It now describes the
   per-construct simulation bricks, the program-global `M1` discharge, and the **concrete
   per-program `Runs` assembly** that ships, matching the source. `wc_preserves` is
   correctly presented as the concrete deliverable, with the generic `lower_preserves`
   over arbitrary `prog` marked future work. **No remaining drift on this item.**
2. **`Match` invariant doc — RECONCILED.** `ir-design.md` §6.1 now quotes the actual
   Lean **`structure`** parameterized by `(prog L pc st fr)`
   ([`ir-design.md` §6.1](ir-design.md#L327)), matching
   [`Match`](../LirLean/Match.lean#L123) (six fields incl. `can_modify`). The old
   "5-clause anonymous conjunction" mismatch is gone.
3. **`maxHeartbeats 2000000` — REMOVED from source.** See Smells above; the only
   remaining `set_option` is `maxRecDepth 100000`.

**New, smaller drift I found:**

- **`WorkedCall.lean`'s file-header docstring is stale relative to its own theorem.**
  The module header ([L63–L71](../LirLean/WorkedCall.lean#L63)) still reads *"`wc_preserves`
  still takes `hpost`/`hhalt` — the post-CALL run … NOT stubbed"*, but the actual
  `wc_preserves` at [L1688](../LirLean/WorkedCall.lean#L1688) is hypothesis-free and the
  theorem's own docstring ([L1680](../LirLean/WorkedCall.lean#L1680)) correctly says *"the
  `hcall` AND the `hpost`/`hhalt` hypotheses … are all gone"*. The header was not updated
  when C3g closed the run. Cosmetic, but it contradicts the shipped signature — should be
  rewritten to match L1680.
- **`Decode.lean`'s `validJumpDests` `partial def` note** (§4 above) is likewise stale
  after Track A's detotalization.

**Rough edges read from the specs themselves:**

- **Single worked program.** Only `workedCall` is assembled end-to-end; the generic
  preservation theorem over arbitrary `prog` is still not stated (the layout/decode
  bricks already support a symbolic statement — see Recommendations).
- **CALL surface is value-free / calldata-free / zero memory window**
  ([`CallSpec`](../LirLean/IR.lean#L43)); no value transfer, no return-data binding
  beyond the success flag.
- **`defsOf` is program-global, last-`assign`-wins**
  ([`Lowering.lean`](../LirLean/Lowering.lean#L164)); correct for single-block /
  single-definition SSA-ish programs, not for general re-assignment or block-local
  scoping.
- **Gas knob `g ≥ 50000`.** The single remaining assumption; benign (a concrete cost
  floor), discharged by the gas-threading lemmas — not a modelling shortcut.

### Connection to the end goal

The lowering currently targets exp003's **flat** surface directly (`messageCall` /
`Runs` / `CallReturns`, all from `BytecodeLayer`). If Phase 2 retargets the shared
`EVMSemantics` interface ([`currentplan.md`](../../../currentplan.md#L76)), the
*architecture* survives unchanged — `Match`, the `sim_*` bricks, and the layout/decode
infra are about the lowering and the IR, not about which bridge crosses the boundary.
What would change is only the final discharge:
[`lower_preserves_discharge`](../LirLean/Match.lean#L333) would consume the interface's
abstract `messageCall_runs`-equivalent, and the opcode `runs_*` rules would need to be
interface-provided. Because C depends on the bridge only through `messageCall_runs` +
`Runs.call` + a fixed set of `runs_*` rules, the retarget is the mechanical substitution
Phase 2a is designed to make trivial — provided the shared interface exposes the same
`Runs.call`-style composition, which is precisely the design choice this review found to
be the linchpin (now empirically confirmed by `wc_preserves_twoCall`).

---

## Recommendations

1. **Update the stale internal comments.** Rewrite `WorkedCall.lean`'s file header
   ([L63–L71](../LirLean/WorkedCall.lean#L63)) to match the closed reality (the theorem
   docstring at [L1680](../LirLean/WorkedCall.lean#L1680) is already correct), and soften
   `Decode.lean`'s `validJumpDests`-`partial def` note
   ([L134](../LirLean/Decode.lean#L134)) since Track A detotalized it. Read-only on my
   part; these are doc fixes, not proof changes.
2. **State the generic preservation theorem** over arbitrary `prog`. The layout/decode
   bricks ([`stmt_byte_anchor`](../LirLean/Layout.lean#L163),
   [`flatBytes_at_pcOf`](../LirLean/Match.lean#L99)) and the `sim_*` bricks already
   support a symbolic statement; the only missing piece is the `IRStep`/
   `lower_simulates_step` engine `ir-design.md` §6 marks as future work. This is the
   natural next milestone now that the concrete witness is hypothesis-free.
3. **Land a genuine two-call program** to turn `wc_preserves_twoCall` from a shape lemma
   into a concrete hypothesis-free witness — by §6.1/§6.3 this needs no new theory, only a
   second `wc_callReturns`-style child.
4. **Widen the CALL surface** (value transfer, return-data binding) when the broader
   experiment needs it; the current value-free shape is a deliberate match to exp003's
   bridge, not a limitation of the architecture.
