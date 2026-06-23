# exp005 — High-level IR → EVM bytecode (design)

Track C, milestone C1. Branch `exp005-ir`, dir `experiments/005_ir_lowering`.
This doc fixes the IR, its semantics, the lowering to exp003-decodable bytecode,
and the preservation statement we will *later* prove (C2/C3). No proofs here.

---

## 1. Extend exp002's `SirLean/` vs. fresh IR — decision

**Decision: a fresh IR (`LirLean/`), keeping only exp002's structural idea (a CFG
of basic blocks with explicit branch terminators).** We do *not* build on
`SirLean`. Reasons, concrete:

1. **Word size mismatch.** `SirLean` fixes `abbrev Word := UInt32`. EVM words —
   and every quantity in exp003's API (`UInt256` on the stack, storage values,
   gas as `UInt64`) — are 256-bit. Reusing `SirLean` would mean rewriting `IR`,
   `State`, `Eval`, `SmallStep`, `Proof` to `UInt256`. Nothing of the old proof
   layer survives that change, so there is no reuse to preserve.

2. **State model is disconnected from the EVM.** `SirLean.World` is an abstract
   `Word → Word` function (`State.lean`). The EVM's persistent state is a *map of
   accounts*, each with its own `StorageMap`, addressed by `AccountAddress`
   (exp003 `Account.lookupStorage`, `AccountMap.find?`). Lowering preservation has
   to relate the IR's storage to the *self account's* storage in `Evm.State`;
   `World = Word → Word` cannot express "which account", which is exactly what an
   external CALL changes. A fresh IR state that mirrors the EVM observable lens
   (storage of the self address, plus call results) is the right starting point.

3. **No external CALL.** `SirLean.Op` has `const / add32 / lessThan /
   persistentLoad / persistentStore` and `EndOp` has `exit / jump / jump_if`.
   There is **no call**. The brief requires external CALL first-class; adding it
   to `SirLean` means a new effect in `Env`, a new `Continuation`, and re-proving
   `progress`/`eval?_iff_steps`. That is a rewrite, not an extension.

4. **No gas, no gas introspection.** `SirLean` has no gas at all. Gas
   introspection (a `GAS`-dependent branch) is the headline reason the IR needs
   branching (`currentplan.md` Q2). It must be in the IR from the start.

5. **SSA/dominance scaffolding is dead weight here.** `SirLean.IR` carries
   `valid_in_cfg`, `InnerCFG.refs_valid`, SSA `Nodup`, `DefinedOnAllPaths`,
   block-IO `transfer_block_io`, and a 57 KB `Proof.lean` + 26 KB `SCCP.lean` —
   all in service of the SCCP optimisation pass (exp002's actual subject). Lowering
   to bytecode needs *none* of it. Carrying it forward is pure liability.

**What we keep from exp002 (as inspiration, not code):** the CFG shape — a finite
list of basic blocks, each a straight-line op list ending in a branch/return
terminator, with branches naming successor blocks by index. This shape lowers to
EVM bytecode cleanly (each block → a `JUMPDEST`-led run of opcodes; terminators →
`JUMP`/`JUMPI`/`STOP`/`RETURN`), and it is where branching lives.

The fresh IR lives in a new library `LirLean` ("Lowered IR") so it never collides
with the in-tree `SirLean` package.

---

## 2. The IR grammar

All values are EVM words `Evm.UInt256`. The IR is **stack-free**: it is a register
(temporary) machine over named locals `Tmp`, lowered to a stack machine. This
keeps the IR readable and makes the lowering's job — materialising operands onto
the EVM stack in the right order — explicit and provable.

```
Tmp     ::= ⟨Nat⟩                      -- a local/temporary (SSA-ish name)
Label   ::= ⟨Nat⟩                      -- a basic-block index

Expr    ::= imm  Word                  -- a literal 256-bit constant
          | tmp  Tmp                   -- read a local
          | add  Tmp Tmp               -- e1 + e2            (EVM ADD)
          | lt   Tmp Tmp               -- e1 < e2  → 0/1     (EVM LT)
          | sload Tmp                  -- storage[ key ]     (EVM SLOAD)
          | gas                        -- remaining gas      (EVM GAS)  ← introspection

Stmt    ::= assign Tmp Expr            -- t := e
          | sstore Tmp Tmp             -- storage[ key ] := value   (EVM SSTORE)
          | call  CallSpec             -- external CALL (see §5)

Term    ::= ret    Tmp                 -- RETURN the word in t (or exit code)
          | stop                       -- STOP
          | jump   Label               -- unconditional branch
          | branch Tmp Label Label     -- if t ≠ 0 then L_then else L_else  (EVM JUMPI)

Block   ::= { stmts : List Stmt, term : Term }
Program ::= { blocks : Array Block, entry : Label }
```

`CallSpec` (the external call payload) names: the callee address temporary, the
gas-to-forward temporary (which may itself be `gas`-derived — that is the
introspection coupling), value, and the in/out memory windows. For C1 we model the
**value-free, calldata-free** call that exp003's `callerProg` uses (the simplest
shape exp003's bridge already supports), recording the richer shape as future
work:

```
CallSpec ::= { callee : Tmp, gasFwd : Tmp,
               -- C1: value = 0, argWindow = (0,0), retWindow = (0,0)
               resultTmp : Option Tmp }   -- where to bind CALL's 0/1 success flag
```

This grammar has, first-class and as required by the brief:

- **storage read/write + arithmetic**: `sload`, `sstore`, `add`, `lt`;
- **external CALL**: `Stmt.call`;
- **conditional branching**: `Term.branch` (and `jump`);
- **gas introspection**: `Expr.gas`, usable as a `branch` condition input — e.g.
  `g := gas; c := lt g K; branch c L_lowgas L_normal`.

### Why `gas` belongs in the IR (honesty constraint)

Project memory ("keep theorems TRUE under gas introspection, earn gas-freedom as a
*proved* result"). `Expr.gas` makes the IR able to *observe* remaining gas and
branch on it. The IR semantics therefore must thread a gas counter (see §3); we do
**not** assume gas is irrelevant. Whether a given program's observable result is
gas-independent becomes a *theorem about that program*, never a modelling
shortcut. A program that never uses `Expr.gas` will be provably gas-insensitive;
one that branches on `gas` will not — and the IR can express both.

---

## 3. Semantics: small-step, gas-aware

**Choice: small-step operational semantics, with an explicit gas counter**, to
match exp003 (whose whole layer is a small-step `stepFrame`/`Runs` story) and so
the lowering-preservation proof can put IR steps and EVM `Runs` steps in
correspondence block-by-block. A denotational/`eval?` reading is *derivable* later
(exp002 has both and relates them via `eval?_iff_steps`), but the small-step
relation is primary because the preservation proof is a simulation argument.

IR machine state:

```
IRState ::= { locals  : Tmp → Option Word     -- register file
            , storage : Word → Word           -- the self account's storage
            , gas     : Nat }                 -- remaining gas (mirrors EVM gasAvailable)
IRConf  ::= running Label (pc : Nat) IRState  -- inside block `Label`, at stmt `pc`
          | halted  Halt                       -- STOP / RETURN word / reverted
```

The step relation `IRStep (prog) : IRConf → IRConf → Prop` advances one statement
or terminator. **Each statement carries the gas cost of the opcodes it lowers
to**, so the IR gas counter tracks the EVM `gasAvailable` exactly (this is the
invariant the preservation proof maintains). Gas accounting is the only subtle
part: `sstore`'s cost is state-dependent (cold/warm, zero/non-zero) exactly as in
exp003's `sstoreChargeOf`; `call` forwards a sub-budget. C1 fixes only the
*shape*; the exact cost functions are pinned in C2 against exp003's constants.

`call` semantics: an `IRStep` for `Stmt.call` consumes the call's gas, runs the
callee as a **black box that returns a `CallResult`** (success flag + the callee's
storage effect on its own account), and binds `resultTmp`. This is deliberately
the shape of exp003's `CallReturns` (a black-box terminating child) so the two
line up under lowering (see §5).

---

## 4. Lowering to exp003-decodable EVM bytecode

`lower : Program → ByteArray`, producing bytes that `Evm.decode` (exp003's
decoder, `EVMLean/Evm/Semantics/Decode.lean`) reads back as the intended opcode
stream. Opcode bytes (from `EVMLean/Evm/Instr.lean`, confirmed): `ADD 0x01`,
`LT 0x10`, `SLOAD 0x54`, `SSTORE 0x55`, `JUMP 0x56`, `JUMPI 0x57`, `GAS 0x5a`,
`JUMPDEST 0x5b`, `PUSH1 0x60` … `PUSH32 0x7f`, `STOP 0x00`, `RETURN 0xf3`,
`CALL 0xf1`.

### Block layout

The program lowers to a **concatenation of blocks**, each prefixed by a
`JUMPDEST` (so it is a legal jump target under `validJumpDests`). A side table
maps `Label → byte offset` of its `JUMPDEST`. Because EVM jump destinations are
absolute byte offsets pushed as immediates, lowering is **two-pass**:

1. *Layout pass*: lower each block to a byte length (every `PUSH<dest>` reserves a
   fixed width — we pick `PUSH4` / 4-byte immediates so a 32-bit `UInt32` pc, the
   type `decode` uses, always fits and widths are uniform regardless of address).
   Accumulate offsets into the `Label → offset` table.
2. *Emit pass*: emit bytes, resolving each branch's destination immediate from the
   table.

Using a fixed push width for destinations makes layout a simple prefix-sum (no
fixpoint over push-width-vs-offset), which is what makes the offset table provably
correct.

### Statement / expression lowering (operands onto the stack)

The IR is register-based; lowering materialises each operand by re-pushing /
recomputing. The simplest correct scheme for C1 is **recompute-on-use** for
`imm`/`tmp` operands of arithmetic, mirroring exp003's worked programs which push
literals immediately before the consuming opcode (see `seqProgram`,
`sstoreProgram`). Concretely:

| IR                       | EVM opcode stream (operands already on stack top → result on top) |
|--------------------------|-------------------------------------------------------------------|
| `add a b`                | `… push(b); push(a); ADD`                                         |
| `lt a b`                 | `… push(b); push(a); LT`                                          |
| `sload k`                | `… push(k); SLOAD`                                                |
| `gas`                    | `GAS`                                                             |
| `imm w`                  | `PUSH32 w` (uniform width; literal `w`)                           |
| `sstore k v`             | `push(v); push(k); SSTORE`                                        |
| `ret t`                  | `push(t)` then a `RETURN`-shaped return of one word (or exit)     |
| `stop`                   | `STOP`                                                            |
| `jump L`                 | `PUSH4 off(L); JUMP`                                              |
| `branch t L_then L_else` | `push(t); PUSH4 off(L_then); JUMPI; PUSH4 off(L_else); JUMP`      |
| `call cs`                | push the 7 CALL args (callee, gasFwd, zeros); `CALL`; bind result |

(How temporaries map to concrete stack slots — recompute vs. DUP/SWAP shuffling —
is a C2 detail; C1 fixes the per-op opcode templates above, which are exactly the
templates exp003 already has `Runs` rules for: `runs_push1`, `runs_push`,
`runs_sstore`, and the CALL-step facts inside `CallReturns`.)

### Decode-compatibility (the C1 acceptance bar)

The lowering is "exp003-decodable" iff for every emitted opcode at offset `o`,
`Evm.decode (lower prog) o` returns that opcode (and, for pushes, the immediate
and width). This is the lowering's analogue of exp003's `decode_seq_*` lemmas
(`Hoare/Sequence.lean`) — those are hand-written per-pc; ours will be generated by
a `decode (lower prog)` correctness lemma in C2.

---

## 5. External calls → the `Runs` / boundary-bridge API

This is the crux of Track C and its feedback edge to Track A.

exp003 exposes (re-exported in `BytecodeLayer.Spec`), in Track A's **new
`exp003-runs-call` API** (the one C3 targets — *not yet merged to this worktree's
base*):

- `Runs fr fr'` — an **index-free** reflexive-transitive closure of single
  non-halting steps **extended with returning external CALLs**. Three
  constructors: `Runs.refl`, `Runs.step` (one `StepsTo` opcode link), and
  `Runs.call` (a returning external CALL, payload `CallReturns`). Composed by
  `Runs.trans`; the one-step atom is `Runs.single`. **No `Nat` step index** — the
  boundary reconciles by never-out-of-fuel, not a numeric bound.
- `messageCall_runs (p) (hbegin : EntersAsCode p fr₀) (h : Runs fr₀ last)
  (hhalt : stepFrame last = .halted halt) : messageCall p = .ok (toCallResult
  (endFrame last halt))` — the **single** boundary bridge, fuel-free. The halt is
  taken by `hhalt` at the bridge (no separate halt `runs_*` lemma needed).
- `CallReturns callFr resumeFr` — bundles **one** returning external CALL: the
  CALL step (`stepFrame callFr = .needsCall cp pending`), the child entering as
  code (`EntersAsCode cp child`), the child's black-box terminating run
  (`drive (seedFuel cp.gas) [] (running child) = .ok childRes`), pinning
  `resumeFr = resumeAfterCall childRes.toCallResult pending`. This is the payload
  of `Runs.call`.
- `messageCall_runs_calls` — definitionally `messageCall_runs`, named to make the
  **multi-call composition** guarantee explicit: a single `Runs fr₀ last`
  interleaving **any number** of `Runs.call` nodes with `Runs.step`s, ending at a
  halting `last`, crosses the boundary in one shot.
- Opcode `Runs` rules currently provided: `runs_push1`, `runs_push` (any width),
  `runs_sstore` (+ framing lemmas `sstoreFrame_storage_self` /
  `sstoreFrame_storage_frame`). Post-frame transformers: `pushFrame`,
  `pushFrameW`, `sstoreFrame`. The rules C3 additionally needs are the **C→A
  opcode-rule request** (PLAN.md): `runs_sload` / `runs_add` / `runs_lt` /
  `runs_gas` / `runs_jump` / `runs_jumpi`.

**How a lowered IR program maps onto this:**

- A lowered **call-free** IR program is a single `Runs` chain (glue the per-op
  `Runs` rules with `Runs.trans`) ending at a `STOP`/`RETURN` halt → discharge via
  `messageCall_runs`. This is the C3 single-block / single-path target.
- A lowered IR program with `Stmt.call`s maps each CALL to a `Runs.call` node
  (`CallReturns`) and threads them into the **same** `Runs fr₀ last` as the opcode
  `Runs.step`s, by `Runs.trans`. The IR's black-box `call` semantics (§3) was
  chosen to match `CallReturns`'s black-box child precisely, so the simulation
  lines up. One CALL or many: it is the same single `Runs` value, crossed once by
  `messageCall_runs` / `messageCall_runs_calls`.

### ✅ Multi-call composition — RESOLVED by Track A's `Runs.call`

The C1/C2 logs flagged that exp003's *old* `messageCall_call_runs` admitted only
**one** `CallReturns` between a prefix and a suffix `Runs`, so a ≥2-call IR program
(`prefix → call → middle → call → suffix → halt`) was inexpressible. **Track A's
new `exp003-runs-call` API resolves this**: `call` is now a **constructor of
`Runs`** (`Runs.call hcall rest`), so a multi-call program is one `Runs` value
built by `Runs.trans` over both `Runs.step` (opcode) links and `Runs.call`
(returning-CALL) links — the regular-language shape `(step | call)*`. The worked
two-call composition is A's `Examples/TwoCallExample.lean`
(`twoCall_runs` / `twoCall_messageCall`), which is exactly Track C's shape:

```
fr₀ --prefix Runs--> callFr₁ --Runs.call(CR₁)--> resumeFr₁
    --middle Runs--> callFr₂ --Runs.call(CR₂)--> resumeFr₂
    --suffix Runs--> last  (stepFrame last = .halted halt)
```

So C3 has **no remaining multi-call blocker** — it is gated only on the merge of
A's branch (which carries the index-free `Runs` + `Runs.call` + the new opcode
rules) into this worktree's base, plus the C→A opcode-rule additions (PLAN.md).

---

## 6. The preservation architecture (AS-BUILT)

This section describes the preservation proof **as it is actually built** in the
source (`LirLean/{SmallStep,Match,Layout,DecodeLower,WorkedCall}.lean`). The shape
is: the `Match` invariant relating an IR small-step configuration to an EVM `Frame`
(§6.1); a set of **frame-local, per-construct simulation lemmas** that each wrap one
Track A `runs_*` rule (§6.2); the **concrete, per-program `Runs` assembly** that
chains those lemmas for the worked program `workedCall` (§6.3); and the per-construct
**obligation table** naming the exact rule each construct consumes (§6.4). It builds
on Track A's `exp003-runs-call` API (§5): index-free `Runs` with constructors
`Runs.refl` / `Runs.step` / `Runs.call`, glued by `Runs.trans`; boundary bridge
`messageCall_runs` (= `messageCall_runs_calls`).

> **AS-BUILT vs. a generic engine.** An earlier draft of this section described a
> *generic simulation engine* — an `IRStep` inductive plus a single
> `lower_simulates_step : IRStep prog c c' → Match c fr → ∃ fr', Runs fr fr' ∧
> Match c' fr'` lemma, closed over `IRRunsToHalt` by induction to give a generic
> `lower_preserves` over an arbitrary program. **That generic engine is not built.**
> What ships instead is: the per-construct simulation lemmas of §6.2 (the bricks the
> engine would have threaded), the program-global `M1` byte-layout discharge
> (`Layout.lean` + `Match.flatBytes_at_pcOf`, generic over `prog`), and a *concrete*
> assembly (`WorkedCall.lean`) that threads those bricks by hand for the single
> worked program `workedCall`. The generic engine — induction over the IR
> statement/terminator stream, plus the generic threading of `materialiseExpr`
> push-chains — remains **future work** (it would generalise `WorkedCall`'s concrete
> chain over an arbitrary `prog`; the `M1` and bridge halves it needs are already
> generic). §6.3 below reflects the concrete assembly that actually exists.

### 6.1 The `Match` invariant

`Match` (`LirLean/Match.lean`) is the simulation invariant. **As built it is a Lean
`structure`** — `Match (prog : Program) (L : Label) (pc : Nat) (st : IRState)
(fr : Frame) : Prop` — with **six named fields**, not an anonymous five-clause
conjunction:

```lean
structure Match (prog : Program) (L : Label) (pc : Nat) (st : IRState) (fr : Frame) : Prop where
  pc_eq      : fr.exec.pc = UInt32.ofNat (pcOf prog L pc)          -- M1
  code_eq    : fr.exec.executionEnv.code = lower prog             -- M2
  storage_eq : ∀ k, selfStorage fr k = st.storage k              -- M3
  gas_eq     : fr.exec.gasAvailable = st.gas                     -- M4
  stack_nil  : fr.exec.stack = []                               -- M5
  can_modify : fr.exec.executionEnv.canModifyState = true       -- standing well-formedness
```

It is **deliberately NOT a stack-shape equivalence**: because the lowering is
*recompute-on-use* (§4), an `IRState.locals` binding `t ↦ v` does **not** correspond
to any persistent stack slot — `t` is re-materialised from its defining expression at
each use, so between statements the EVM stack is empty. This is the key
simplification recompute-on-use buys: `Match` need not track a register↔slot map at
all (clause `M5`, `stack_nil`). The six fields:

- `pc_eq` (`M1`) — program counter at the offset-table address `pcOf prog L pc`.
- `code_eq` (`M2`) — the frame runs the lowered program.
- `storage_eq` (`M3`) — the IR self-storage equals the self account's storage,
  read through exp003's observable lens `selfStorage` (the same `find?/lookupStorage`
  `sstoreFrame_storage_self` uses).
- `gas_eq` (`M4`) — the IR gas counter equals `gasAvailable` (honest gas, §3); note
  `IRState.gas` is a `UInt64`, so this is a *plain* `UInt64` equality, not a `toNat`
  one.
- `stack_nil` (`M5`) — empty working stack at the statement boundary.
- `can_modify` — standing well-formedness for a state-modifying top-level call.

`pcOf prog L pc` is the offset-table address: `offsetTable defs fuel blocks L.idx`
(the block's `JUMPDEST`) `+ 1` (skip the `JUMPDEST`) `+` the byte length of the
emitted statements `0 .. pc` of block `L`. The two-pass layout (§4) makes this a
prefix sum, so `pcOf` is computable; `M1` is discharged *generically over `prog`* by
`Match.flatBytes_at_pcOf` (which composes the `Layout.lean` prefix-sum decomposition
`stmt_byte_anchor` with the generic decode lemmas `DecodeLower.decode_lower_*`) — not
by per-program `rfl`. See `Decode.lean` for the same `M1` discharge exercised at a
symbolic `pcOf` cursor.

### 6.2 The per-construct simulation lemmas (the bricks)

There is **no single `lower_simulates_step` engine** and **no `IRStep` inductive**
(see the AS-BUILT note above). Instead, each effecting construct gets one
**frame-local** simulation lemma in `Match.lean` that wraps the corresponding
Track A `runs_*` rule and reads back the IR-relevant post-frame fact. Each takes the
frame's *local* hypotheses (decode at `fr.exec.pc`, stack shape, gas bound) — exactly
what the `runs_*` rule wants — so the lemmas compose by `Runs.trans` independently of
`M1`'s program-global pc arithmetic:

- `sim_imm` → `runs_push (.PUSH32)`; leaves `w` on top (`evalExpr (.imm w)`).
- `sim_add` / `sim_lt` → `runs_add` / `runs_lt`; top = `UInt256.add`/`.lt a b`.
- `sim_sload` → `runs_sload`; top = `selfStorage fr key` (via `sloadFrame_storage_self`).
- `sim_gas` → `runs_gas`; gas drops by `gBase`, top = post-charge gas.
- `sim_sstore` → `runs_sstore`; the written cell reads back `value`, other cells unchanged.
- `sim_jump` → `runs_jump`; pc set to the resolved target.
- `sim_branch` → `runs_branch` (the CFG combinator; case-split on the runtime condition).
- `sim_call` → a `Runs.call` node from a `CallReturns` witness.
- `halt_stop` / `halt_ret` → `stepFrame_stop` / `stepFrame_return_empty`: the halt
  step the bridge consumes via its `hhalt` argument (terminators are **not** `runs_*`).

### 6.3 The concrete `Runs` assembly + boundary discharge

Two pieces ship, in place of a generic induction:

**(i) The construct-agnostic bridge half** (`Match.lower_preserves_discharge`):

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

This is `messageCall_runs` (§5) applied at the IR/lowering boundary. It crosses the
bridge for **any** assembled `Runs fr₀ last`, regardless of how many `Runs.call`
nodes it contains — so the multi-call discharge is free.

**(ii) The concrete assembly** (`WorkedCall.lean`), threading the §6.2 bricks by hand
for the single worked program `workedCall` run as a top-level `messageCall`
(`wcParams g`). It assembles one `Runs (wcFrame g) last`:

```
  wcFrame g  --wc_prefix_runs-->  wcCallSite g          (JUMPDEST; SSTORE operands; SSTORE; 7 CALL args)
             --Runs.call (wc_callReturns)-->  resumeFr   (the single external CALL to 0xCA11EE)
             --wc_post_runs-->  last                     (recompute c; JUMPI taken; block 1 RETURN)
             --halts (stepFrame last = .halted halt)
```

then crosses it once with `lower_preserves_discharge`. `wc_preserves` is the result;
`wc_preserves_twoCall` is the same discharge with two `Runs.call` nodes (C4). The
generic `lower_preserves` over an arbitrary `prog` of the earlier draft would
generalise this concrete chain by induction over the IR stream — it is future work
(see the AS-BUILT note); the `M1` discharge (§6.1) and the bridge half (i) it would
reuse are already generic.

### 6.4 Per-IR-construct proof-obligation table

Each row: the IR construct, the bytes `lower` emits (§4 / PLAN C2 log), the Track A
`runs_*` rule(s) that discharge each emitted opcode, and the post-frame transformer
the next rule consumes. Operand materialisation (`materialiseExpr`) is **always**
one or more `runs_push` (PUSH32 literals / PUSH4 destinations) glued by
`Runs.trans` ahead of the consuming opcode; the table abbreviates that as
"push·(operands)". Rules marked **[A-new]** are the C→A request (PLAN.md); the rest
already exist on A's branch.

| IR construct           | emitted opcodes                              | `Runs` rule(s) consumed (in order)                                  | post-frame |
|------------------------|----------------------------------------------|---------------------------------------------------------------------|------------|
| `Expr.imm w`           | `PUSH32 w`                                    | `runs_push (.PUSH32) w 32`                                          | `pushFrameW` |
| `Expr.tmp t`           | (recompute `defs t`)                          | the rules of `defs t` (no opcode of its own)                       | — |
| `Expr.add a b`         | push·b; push·a; `ADD`                         | push-rules ×2, then **`runs_add` [A-new]**                          | `addFrame` [A-new] |
| `Expr.lt a b`          | push·b; push·a; `LT`                          | push-rules ×2, then **`runs_lt` [A-new]**                           | `ltFrame` [A-new] |
| `Expr.sload k`         | push·k; `SLOAD`                               | push-rule, then **`runs_sload` [A-new]**                            | `sloadFrame` [A-new] |
| `Expr.gas`             | `GAS`                                         | **`runs_gas` [A-new]**                                              | `gasFrame` [A-new] |
| `Stmt.assign t e`      | (nothing)                                     | `Runs.refl` (recompute-on-use emits no bytes)                       | unchanged |
| `Stmt.sstore key val`  | push·val; push·key; `SSTORE`                  | push-rules ×2, then `runs_sstore`                                   | `sstoreFrame` |
| `Stmt.call cs`         | push ×7 (5×`PUSH32 0`, callee, gasFwd); `CALL`| push-rules ×7, then a **`Runs.call`** node from a `CallReturns` witness (CALL step is `stepFrame = .needsCall …`, **not** a `runs_*`) | `resumeAfterCall …` (inside `CallReturns`) |
| `Term.ret t`           | push·t; `RETURN`                             | push-rule(s); the `RETURN` halt is taken by `messageCall_runs`'s `hhalt` via `stepFrame_return_empty` (no `runs_*`) | `last` (halt) |
| `Term.stop`            | `STOP`                                        | the `STOP` halt is taken by `messageCall_runs`'s `hhalt` via `stepFrame_stop` (no `runs_*`)                | `last` (halt) |
| `Term.jump L`          | `PUSH4 off(L)`; `JUMP`                        | `runs_push (.PUSH4)`, then **`runs_jump` [A-new]** (CFG combinator) | `jumpFrame` [A-new] → pc = off(L) |
| `Term.branch c t e`    | push·c; `PUSH4 off(t)`; `JUMPI`; `PUSH4 off(e)`; `JUMP` | push·c, `runs_push (.PUSH4)`, **`runs_jumpi` [A-new]** (two post-frames: taken → pc=off(t); not-taken → fall through to the `PUSH4 off(e); JUMP`), then on the not-taken edge `runs_push` + **`runs_jump` [A-new]** | `jumpiFrame`/`jumpFrame` [A-new] |

Notes that shape the obligations:

- **Halts are not `runs_*`.** `STOP`/`RETURN` are discharged directly at the
  bridge: `messageCall_runs` takes the halt via its `hhalt : stepFrame last =
  .halted halt` argument, which C3 supplies from A's existing `stepFrame_stop` /
  `stepFrame_return_empty`. So C3 needs **no** halt `runs_*` wrapper — the C2 log's
  "thin `Runs … → halt` wrapper" note is superseded by A's bridge taking the halt.
- **CALL is not a `runs_*`.** The `CALL` opcode is a `Runs.call` node whose payload
  is a `CallReturns` witness (built from A's `stepFrame_call` + `EntersAsCode` +
  the child's black-box `drive`); it is glued by `Runs.trans`, never by a `runs_*`.
- **Gas equalities (`M4`).** Each opcode rule's post-frame subtracts that opcode's
  charge (`Gverylow` for PUSH/ADD/LT/GAS, `Gwarmsload`/cold for SLOAD,
  `sstoreChargeOf` for SSTORE, the call cost for CALL). The IR `IRStep` for the
  matching construct must subtract the **same** charge (§3), so `M4` is preserved
  step-by-step. A's `subCharges` / `toNat_subCharges` (Sequence.lean) is the
  gas-threading lemma C3 reuses to keep the prefix-sum side-goals linear.
- **Stack discipline (`M5`).** Because materialisation pushes exactly the operands
  a consuming opcode pops and the opcode pops them all, the stack returns to `[]`
  after each statement — so `M5` is re-established without a slot map. The one
  exception is `Stmt.call`'s success flag; C3's worked programs either bind it
  immediately (an `assign` from `resultTmp`, which under recompute-on-use is a no-op
  that the next use re-materialises) or `POP` it — pinned per worked program.

---

## 7. C1/C2 deliverable boundary (historical)

C1 shipped: this doc; a compiling `LirLean` skeleton (lakefile requiring exp003's
`bytecode_layer`; the IR datatypes of §2; the `lower : Program → ByteArray` type
signature with a `sorry`-free body); no `sorry`/`axiom`-backed theorems. C2 shipped
the decode-compatible single-call lowering body and the build-enforced round-trip
checks (`LirLean/Decode.lean`). The preservation architecture (§6) is C3, built on
Track A's now-merged `exp003-runs-call` API. §6 reflects the AS-BUILT source: a
small-step `SmallStep.lean`, the `Match` structure, frame-local simulation bricks,
and the concrete per-program `Runs` assembly in `WorkedCall.lean` — not a generic
`IRStep`/`lower_simulates_step` engine (which remains future work).
