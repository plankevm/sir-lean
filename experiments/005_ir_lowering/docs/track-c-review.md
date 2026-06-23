# Track C review — exp005: `LirLean` IR → EVM bytecode, lowering preserved

Scope: the whole `experiments/005_ir_lowering` package (branch `exp005-ir`,
worktree `../evm-semantics-wt/ir-lowering`). All links are relative to this file's
directory (`experiments/005_ir_lowering/docs/`); source modules are one level up
(`../LirLean/…`), the exp003 reasoning layer two-and-over (`../../003_bytecode_layer/…`).

---

## TL;DR

Track C defines a fresh high-level IR ([`LirLean`](../LirLean/IR.lean#L20)) with
**storage arithmetic, external calls, branching, and gas introspection**, lowers it
to `Evm.decode`-compatible EVM bytecode ([`lower`](../LirLean/Lowering.lean#L197)),
and proves the lowering preserves semantics by reusing exp003's `Runs` /
`messageCall_runs` reasoning layer — *no new boundary theory*. The headline
[`wc_preserves`](../LirLean/WorkedCall.lean#L395) (single-call) and
[`wc_preserves_twoCall`](../LirLean/WorkedCall.lean#L413) (the C4 multi-call
corollary) are **proved as the bridge half**: the lowered prefix run is genuine and
assembled in the kernel, but the statements carry **two honest, non-faked
hypotheses** — (a) the concrete child `CallReturns` for the `0xCA11EE` callee, and
(b) the post-CALL branch terminator, the latter genuinely **blocked by
`validJumpDests` being a `partial def`** (a foundation issue Track A is fixing by
detotalizing it). The most important finding: **C4 needed zero new theory** because
exp003's `Runs.call` constructor lets one `Runs` value carry any number of returning
calls — a direct payoff of Track A's design.

Verification (reported from PLAN.md C3d log, not re-run): `lake build` green (1129
jobs); `#print axioms` on every theorem = `[propext, Classical.choice, Quot.sound]`
— no `sorryAx`, no `native_decide`/`bv_decide`, no `admit`. I confirmed by grep that
no forbidden tactic appears in any `LirLean/*.lean` (only in docstrings describing
why they are avoided). `set_option maxHeartbeats 2000000` is set in one file
([`WorkedCall.lean`](../LirLean/WorkedCall.lean#L74)) — see Smells.

---

## 1. Goal & context

The real-world property: **a compiler back-end that lowers a structured IR to EVM
bytecode does not change observable behaviour.** Track C is the first *consumer* of
exp003's bytecode reasoning layer ([`PLAN.md` Goal](../PLAN.md#L7)), and it doubles
as the acceptance test for Track A's multi-call redesign: lowering a multi-call IR
program proves-or-disproves that A's `Runs.call` composes
([`currentplan.md`](../../../currentplan.md#L42)).

The IR is deliberately built around the three primitives the broader experiment
actually needs — storage arithmetic, external CALL, and branching — because
**branching is what makes gas-introspection reasoning meaningful** (a `GAS`-dependent
branch). The honesty constraint from project memory is encoded structurally: `gas` is
a first-class expression, the IR threads an honest gas counter, and gas-independence
of a given program is a *theorem about that program*, never a modelling shortcut
([`ir-design.md` §2 "Why gas belongs in the IR"](ir-design.md#L109)).

End goal ([`currentplan.md` Phase 2](../../../currentplan.md#L68)): this lowering
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
| [`IR.lean`](../LirLean/IR.lean) | IR datatypes (grammar) | `Expr`, `Stmt`, `Term`, `Block`, `Program`, `CallSpec` |
| [`Lowering.lean`](../LirLean/Lowering.lean) | `lower : Program → ByteArray` (recompute-on-use, two-pass offsets) | [`lower`](../LirLean/Lowering.lean#L197) |
| [`SmallStep.lean`](../LirLean/SmallStep.lean) | small-step, gas-aware IR semantics | [`IRState`](../LirLean/SmallStep.lean#L56), [`evalExpr`](../LirLean/SmallStep.lean#L90) |
| [`DecodeLower.lean`](../LirLean/DecodeLower.lean) | generic decode-from-lowering bricks (the `bget`/`bextract` foundation) | [`decode_lower_nonpush`](../LirLean/DecodeLower.lean#L132), [`decode_lower_push`](../LirLean/DecodeLower.lean#L139) |
| [`Layout.lean`](../LirLean/Layout.lean) | offset-table byte-layout arithmetic (prefix-sum, symbolic) | [`stmt_byte_anchor`](../LirLean/Layout.lean#L163) |
| [`Match.lean`](../LirLean/Match.lean) | the `Match` invariant + per-construct simulation lemmas + boundary discharge | [`Match`](../LirLean/Match.lean#L123), [`lower_preserves_discharge`](../LirLean/Match.lean#L333) |
| [`Decode.lean`](../LirLean/Decode.lean) | build-enforced decode round-trip on `workedCall` (the demo) | [`workedCall`](../LirLean/Decode.lean#L45) |
| [`WorkedCall.lean`](../LirLean/WorkedCall.lean) | concrete `Runs` assembly + `lower_preserves` for `workedCall` | [`wc_preserves`](../LirLean/WorkedCall.lean#L395) |

Dependency edges feeding the headline:

```
IR ──> Lowering ──> DecodeLower ──> Layout ──┐
   └─> SmallStep ───────────────────────────┼─> Match ──> WorkedCall
                                             │            (wc_preserves)
exp003: Runs / Runs.call / messageCall_runs ─┘  (boundary discharge)
```

`Match` is the hinge: it consumes `Layout`+`DecodeLower` (to discharge the pc clause
`M1` generically) and `SmallStep` (to read the IR side), and it consumes exp003's
opcode `runs_*` rules + the `messageCall_runs` bridge. `WorkedCall` assembles a
concrete `Runs` for one program and crosses the bridge.

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
`JUMP`/`JUMPI`/`STOP`/`RETURN`). I find the decision well-justified; carrying
`SirLean`'s SCCP scaffolding (>80 KB) forward would have been pure liability.

### 3.2 The grammar

The IR is a **register (temporary) machine** — stack-free — over named `Tmp`s,
organised as a CFG. Verbatim ([`IR.lean`](../LirLean/IR.lean#L52)):

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
  resultTmp : Option Tmp         -- where to bind the 0/1 success flag
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

Note: the design doc (§3) describes an `IRStep` *relation* as the primary object, but
the shipped `SmallStep.lean` provides the **ingredients** (`evalExpr`, `setLocal`,
`setStorage`, `charge`, `matCost`, cursor accessors) and the per-construct simulation
is stated frame-locally in `Match.lean` rather than as a single `IRStep` inductive +
`lower_simulates_step` engine. This is a real source-vs-doc gap (see §6/§7): the
generic engine `lower_simulates_step` of `ir-design.md` §6.2/§6.3 is **not** present;
the program-global assembly is done concretely per worked program instead.

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
  (§5.1). The alternative, a register/slot map with DUP/SWAP shuffling, would force
  `Match` to track which stack slot holds which tmp at every program point; the C
  author traded that for re-pushing. For straight-line SSA-ish programs this is
  correct and far simpler; its cost is code size and that it is correct only when each
  tmp has a single global definition (`defsOf` takes the last `assign`).
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
the relevant `rfl` decode checks — deliberately *not* via `validJumpDests`, which is a
`partial def` and would force `native_decide`
([`Decode.lean`](../LirLean/Decode.lean#L134)). This is the same `partial def` wall
that blocks the branch terminator (§6).

---

## 5. The preservation architecture (the specs that matter)

The architecture is **invariant + per-construct simulation + single-bridge
discharge**, not a monolith. Bottom-up:

### 5.1 The `Match` invariant — five clauses, no slot map

[`Match`](../LirLean/Match.lean#L123) relates a running IR configuration to an EVM
`Frame`:

```lean
structure Match (prog : Program) (L : Label) (pc : Nat) (st : IRState) (fr : Frame) : Prop where
  pc_eq      : fr.exec.pc = UInt32.ofNat (pcOf prog L pc)          -- M1
  code_eq    : fr.exec.executionEnv.code = lower prog             -- M2
  storage_eq : ∀ k, selfStorage fr k = st.storage k              -- M3
  gas_eq     : fr.exec.gasAvailable = st.gas                     -- M4
  stack_nil  : fr.exec.stack = []                               -- M5
  can_modify : fr.exec.executionEnv.canModifyState = true
```

The `M5` empty-stack clause is the recompute-on-use payoff made formal: between
statements there is no register state on the stack, so `Match` needs no slot map. `M1`
is pinned to the offset-table address [`pcOf`](../LirLean/Match.lean#L64), a computable
prefix sum. `M3` reads storage through the same observable lens
([`selfStorage`](../LirLean/Match.lean#L111)) exp003's `sstoreFrame_storage_self` uses.

Honest assessment of `Match`'s hypotheses: nothing here smuggles the conclusion. The
clauses are exactly the correspondences a simulation needs; the `can_modify` standing
condition is a normal top-level-call assumption.

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
plus `lower`-specialised forms [`decode_lower_nonpush`](../LirLean/DecodeLower.lean#L132)
/ [`decode_lower_push`](../LirLean/DecodeLower.lean#L139)). A decode obligation over
`lower prog` reduces to a *list-local* fact: which byte `flatBytes prog` holds at the pc.

**The prefix-sum decomposition** ([`Layout.lean`](../LirLean/Layout.lean)). The payoff
is [`stmt_byte_anchor`](../LirLean/Layout.lean#L163): over an **arbitrary** program,
the byte at the offset-table address of a statement cursor is the head byte of that
statement's emitted opcodes. It composes `flatMap_split`
([`flatMap_split`](../LirLean/Layout.lean#L74)), the offset-table-as-prefix-sum
([`blockPrefix_length`](../LirLean/Layout.lean#L94)), and the length-invariance lemmas
([`emitBlockBody_length_labelOff`](../LirLean/Layout.lean#L53)) — the last being why
the fixed-width `PUSH4` choice matters formally. The `pcOf`-level wrapper
[`flatBytes_at_pcOf`](../LirLean/Match.lean#L99) ties this back to `pcOf` so the
engine gets `decode (lower prog) (pcOf …)` symbolically, not by per-program `rfl`.
Proof strategy (one sentence): `pcOf` collapses to the offset-table anchor when the
block exists, then `stmt_byte_anchor` indexes into a three-way list append. This is
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
— the proofs are one-liners (`exact ⟨runs_… , rfl⟩` / `sloadFrame_storage_self`),
which is exactly the intent: they wrap the rule with the IR-state reading. The
[`sim_call`](../LirLean/Match.lean#L307) brick is just `Runs.call hcall rest` — the
CALL is a `Runs.call` node, never a `runs_*`.

### 5.4 The boundary discharge → `messageCall_runs`

The construct-agnostic bridge half ([`lower_preserves_discharge`](../LirLean/Match.lean#L333)):

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

This is `messageCall_runs` ([exp003 `CallSequence.lean`](../../003_bytecode_layer/BytecodeLayer/Hoare/CallSequence.lean#L132))
applied at the IR/lowering boundary; the two terminator instances are
[`lower_preserves_stop`](../LirLean/Match.lean#L345) /
[`lower_preserves_ret`](../LirLean/Match.lean#L358), supplying the halt from
`halt_stop`/`halt_ret`. Crucially, the bridge crosses **regardless of how many
`Runs.call` nodes** the assembled run contains.

---

## 6. The headline results and their honest hypotheses

The actual end-to-end results live in [`WorkedCall.lean`](../LirLean/WorkedCall.lean),
assembled on `lower workedCall` run as a top-level `messageCall` in exp003's
caller/callee world ([`wcParams`](../LirLean/WorkedCall.lean#L81)).

**What is genuinely, unconditionally proved** on the concrete program:
[`wc_begin`](../LirLean/WorkedCall.lean#L92) (enters as code),
[`wc_prefix_runs`](../LirLean/WorkedCall.lean#L316) (the **real** straight-line prefix
`Runs` from entry to the CALL site — a kernel-checked `Runs.trans` chain of
`runs_jumpdest`, two `runs_push`, `runs_sstore`, and seven CALL-arg `runs_push`, gas
threaded through `subCharges`), and [`wc_call_step`](../LirLean/WorkedCall.lean#L350)
(the CALL `stepFrame_call` to `0xCA11EE`).

**The single-call headline** ([`wc_preserves`](../LirLean/WorkedCall.lean#L395)):

```lean
theorem wc_preserves (g : UInt64) (hg : 30000 ≤ g.toNat)
    {resumeFr last : Frame} {halt : FrameHalt}
    (hcall : CallReturns (wcCallSite g) resumeFr)
    (hpost : Runs resumeFr last)
    (hhalt : stepFrame last = .halted halt) :
    messageCall (wcParams g)
      = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  have hruns : Runs (wcFrame g) last :=
    (wc_prefix_runs g hg).trans (Runs.call hcall hpost)
  exact lower_preserves_discharge Lir.Decode.workedCall (wcParams g)
    (wc_begin g) rfl hruns hhalt
```

This is the **bridge half**: it claims that *given* a returning external CALL and a
post-CALL run to a halting frame, the top-level `messageCall` delivers that frame's
result. The prefix run is genuine; the two assumptions are honest, verified-feasible
remainders, **not** `sorry`:

- **(a) The concrete child `CallReturns`** (`hcall`). What remains is the child
  `drive` run of the `0xCA11EE` callee at the 63/64-capped forwarded gas — the
  ~200-line `caller_callReturns` shape transposed onto `wcCallSite g`. Feasibility is
  checked in the docstring ([`WorkedCall.lean`](../LirLean/WorkedCall.lean#L44)):
  `toExecute … 0xCA11EE = .Code calleeProg` by `rfl`, and the forwarded gas clears the
  callee's 22106 floor. This is a *large mechanical* obligation, not a soundness gap.
- **(b) The post-CALL branch terminator** (`hpost`'s eventual `JUMPI`/`JUMP`). This is
  the real blocker. `Frame.get_dest` reads `validJumps`, which for the entry frame
  `codeFrame … (lower workedCall)` is `validJumpDests (lower workedCall) 0` — a
  **`partial def`**, so it cannot be reduced in a proof without `native_decide`, which
  would break the axiom-clean bar ([`WorkedCall.lean`](../LirLean/WorkedCall.lean#L48)).
  This is a *foundation* issue: exp003's own `BranchExample` sidesteps it with an
  explicit `validJumps`. **Track A is fixing it by detotalizing `validJumpDests`** (so
  it becomes a reducible, structurally-terminating function with a characterization
  lemma over `lower prog`). Until then, `hpost` is taken as a hypothesis. This is the
  single most important caveat in the report: the branch arm of the headline is gated
  on a Track A foundation change, not on Track C effort.

The `hg : 30000 ≤ g.toNat` hypothesis is a benign gas floor (enough to clear the cold
SSTORE + CALL costs of the prefix), discharged by the gas-threading lemmas; not a smell.

**The C4 multi-call corollary** ([`wc_preserves_twoCall`](../LirLean/WorkedCall.lean#L413)):

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
    messageCall (wcParams g) = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  lower_preserves_discharge Lir.Decode.workedCall (wcParams g) hbegin hcode
    (hpre.trans (Runs.call hcall₁ (hmiddle.trans (Runs.call hcall₂ hpost)))) hhalt
```

**The key finding, formalized.** This two-call result needed **no new theory**: it is
the same `lower_preserves_discharge`, with two `Runs.call` nodes threaded by
`Runs.trans` into one `Runs`. This works only because exp003's `Runs` makes `call` a
**constructor** ([exp003 `Hoare.lean`](../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L114)):

```lean
inductive Runs : Frame → Frame → Prop where
  | refl : Runs fr fr
  | step …
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'
```

So `(step | call)*` is a single `Runs` value, and `messageCall_runs` crosses it once
regardless of call count. This directly validates Track A's redesign: the C1 log had
flagged the *old* `messageCall_call_runs` (one call only) as a hard multi-call blocker
([`PLAN.md` C1 log](../PLAN.md#L77)); A's `Runs.call` resolved it, and C4 is now a
structural corollary. **C was the test; A passed.**

---

## 7. Results taxonomy, smells, and rough edges

**Headline / mainline:** [`wc_preserves`](../LirLean/WorkedCall.lean#L395),
[`wc_preserves_twoCall`](../LirLean/WorkedCall.lean#L413), and the generic boundary
[`lower_preserves_discharge`](../LirLean/Match.lean#L333). All proved as the bridge
half with the two honest hypotheses above.

**Supporting bricks (load-bearing):** the simulation lemmas `sim_*`/`halt_*`
(§5.3); the generic decode infra
[`decode_lower_*`](../LirLean/DecodeLower.lean#L132) + [`bget`/`bextract`](../LirLean/DecodeLower.lean#L56);
the layout arithmetic [`stmt_byte_anchor`](../LirLean/Layout.lean#L163) +
[`flatBytes_at_pcOf`](../LirLean/Match.lean#L99); and the concrete prefix
[`wc_prefix_runs`](../LirLean/WorkedCall.lean#L316). The decode/layout bricks are the
genuine new contribution exp003 lacked; they are reusable for any program.

**Examples / demos:** [`workedCall`](../LirLean/Decode.lean#L45) and its ≈40 `rfl`
decode checks; the symbolic-`pcOf` example
([`Decode.lean`](../LirLean/Decode.lean#L176)). These are witnesses; the headline
theorems do consume `workedCall` (so the demo program is load-bearing for the
headline, but the per-pc `rfl` checks themselves are leaves).

**Smells / weak proofs:**

- `set_option maxHeartbeats 2000000` in
  [`WorkedCall.lean`](../LirLean/WorkedCall.lean#L74) (plus `maxRecDepth 100000`).
  This is a real reduction blow-up: `lower` produces 33-byte `PUSH32` literals and the
  decode facts reduce the byte stream in the kernel. The author already mitigated it by
  factoring decode into independent `wc_dec_*` lemmas ("chaining them inline blew the
  heartbeat budget" — [`PLAN.md` C3d log](../PLAN.md#L519)). **Does a headline depend
  on this?** Yes — `wc_preserves` transitively uses `wc_prefix_runs`, which uses these
  cranked options. It is contained (only the concrete worked-program assembly, not the
  generic lemmas) but it does sit under a headline, and it signals the per-program
  `Runs` assembly is awkward at scale. The generic layer (`Layout`/`DecodeLower`) is
  the intended escape from per-program kernel reduction and does not crank heartbeats.
- `by decide`/`by rfl` are used pervasively (≈43 occurrences) but on small terms (gas
  arithmetic, single immediates); not flagged as brittle.

**Source-vs-doc discrepancies (surfaced):**

1. **`IRStep` / `lower_simulates_step` do not exist.** `ir-design.md` §3/§6.2/§6.3
   present an `IRStep` inductive, a `lower_simulates_step` engine, and a generic
   `lower_preserves` closed by induction over `IRRunsToHalt`. The shipped code has
   **no `IRStep` relation and no `lower_simulates_step`**; `SmallStep.lean` provides
   only the evaluation/charge ingredients, and the simulation lemmas are stated
   frame-locally in `Match.lean`. The "program-global assembly" the doc describes as
   the engine is done **concretely per worked program** in `WorkedCall.lean`, not
   generically. The `lower_preserves` of §6.3 (taking `IRRunsToHalt`) is therefore not
   the shipped theorem; `wc_preserves` is its concrete specialization. The PLAN.md C3
   log is honest about this ("the missing engine is `lower_simulates_step` proper", the
   program-global assembly "is the bulk of the remaining work" —
   [`PLAN.md`](../PLAN.md#L370)), but `ir-design.md` reads as if it were built. Treat
   `ir-design.md` §6 as plan-of-record, not as-built.
2. The doc's `Match` is a 5-clause anonymous conjunction quantified over a single
   frame ([`ir-design.md` §6.1](ir-design.md#L312)); the code's
   [`Match`](../LirLean/Match.lean#L123) is a named `structure` parameterized by
   `(prog L pc st fr)` with a sixth `can_modify` field. Minor; the code is the better form.

**Rough edges read from the specs themselves:**

- **Single worked program.** Only `workedCall` is assembled end-to-end; the generic
  preservation theorem over arbitrary `prog` is not stated.
- **CALL surface is value-free / calldata-free / zero memory window** ([`CallSpec`](../LirLean/IR.lean#L37));
  no value transfer, no return-data binding beyond the success flag.
- **`defsOf` is program-global, last-`assign`-wins** ([`Lowering.lean`](../LirLean/Lowering.lean#L164));
  correct for single-block / single-definition SSA-ish programs, not for general
  re-assignment or block-local scoping (flagged as a C3 refinement in the source).
- **The two honest hypotheses** of §6 — both feasible, one (the branch) blocked on
  Track A's `validJumpDests` detotalization.

### Connection to the end goal

The lowering currently targets exp003's **flat** surface directly (`messageCall` /
`Runs` / `CallReturns`, all from `BytecodeLayer`). If Phase 2 retargets the shared
`EVMSemantics` interface ([`currentplan.md`](../../../currentplan.md#L76)), the
*architecture* survives unchanged — `Match`, the `sim_*` bricks, and the
layout/decode infra are about the lowering and the IR, not about which bridge crosses
the boundary. What would change is only the final discharge:
[`lower_preserves_discharge`](../LirLean/Match.lean#L333) would consume the interface's
abstract `messageCall_runs`-equivalent instead of exp003's concrete one, and the
opcode `runs_*` rules would need to be interface-provided (or the interface would
abstract over a step relation). Because C depends on the bridge only through
`messageCall_runs` + `Runs.call` + a fixed set of `runs_*` rules, the retarget is the
mechanical substitution Phase 2a is designed to make trivial — provided the shared
interface exposes the same `Runs.call`-style composition, which is precisely the design
choice this review found to be the linchpin.

---

## Recommendations

1. **Resolve the `validJumpDests` `partial def`** (Track A) — it is the one true
   blocker for a hypothesis-free single-call closure and recurs in both `Decode.lean`
   and `WorkedCall.lean`. Everything else is mechanical.
2. **Reconcile `ir-design.md` §6 with the source** — either build the generic
   `IRStep`/`lower_simulates_step` engine it describes, or mark §6 explicitly as
   plan-of-record so a reader does not assume `lower_preserves` (the generic form)
   exists. Right now the doc over-claims relative to the code.
3. **Land the concrete child `CallReturns`** for `0xCA11EE` to discharge `wc_preserves`'s
   `hcall` — large but mechanical; it would also fully close C4 once (1) lands.
4. **Consider the generic preservation theorem** over arbitrary `prog` once the engine
   exists; the layout/decode bricks already support a symbolic statement.
