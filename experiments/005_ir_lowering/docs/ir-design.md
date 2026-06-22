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

exp003 exposes (re-exported in `BytecodeLayer.Spec`):

- `Runs n fr fr'` — `n` non-halting steps, composed by `Runs.trans`;
- `messageCall_runs` — a call-free block that `Runs` to a halt becomes a
  `messageCall` result (fuel-free);
- `CallReturns callFr resumeFr` — bundles **one** external CALL: the CALL step
  (`stepFrame callFr = .needsCall cp pending`), the child entering as code, the
  child's black-box terminating run, pinning `resumeFr`;
- `messageCall_call_runs` — `EntersAsCode` ∧ prefix `Runs` to the CALL site ∧
  `CallReturns` ∧ suffix `Runs` to a halt ⇒ `messageCall` result (fuel-free).

**How a lowered IR program maps onto this:**

- A lowered **call-free** IR program is a single `Runs` chain (glue the per-op
  `Runs` rules with `Runs.trans`) ending at a `STOP`/`RETURN` halt → discharge via
  `messageCall_runs`. This is the C2/C3 single-block / single-path target.
- A lowered IR program with **one** `Stmt.call` is exactly the
  `messageCall_call_runs` shape: prefix `Runs` (everything before the call) →
  `CallReturns` (the `CALL` opcode + black-box callee) → suffix `Runs` (everything
  after) → halt. The IR's black-box `call` semantics (§3) was chosen to match
  `CallReturns`'s black-box child precisely, so the simulation lines up.

### ⚠️ Multi-call composition — the C4 question, surfaced now

**Studying the API already shows exp003's sequencing does NOT compose for IR
programs with ≥2 external calls.** `messageCall_call_runs` is hard-wired to *one*
`CallReturns` between a prefix and a suffix `Runs`:

```
prefix Runs → CallReturns → suffix Runs → halt
```

A `Runs` chain (`StepsTo` = one **non-halting `stepFrame`**) **cannot contain a
CALL step**: a CALL produces `stepFrame = .needsCall …` (a `Signal.needsCall`,
handled by `CallReturns`), not `Signal.next`, so it is not a `StepsTo` link and
cannot be glued in by `Runs.trans`. Hence the "suffix" after the first call is a
plain `Runs` that must run straight to a halt — it can have **no second CALL**.
A two-call IR program (`call; …; call; stop`) has the shape
`prefix → call → middle → call → suffix → halt`, which `messageCall_call_runs`
**cannot express**: there is no second `CallReturns` slot, and the `middle/suffix`
`Runs` cannot absorb the second CALL.

This is exactly the "intermediary calls" defect named in `currentplan.md` (§Why
these three, Q1) and is Track A's A1–A3 mandate: make `call` a **constructor of
`Runs`** so a multi-call program is one `Runs` value built by `.trans` over both
`StepsTo` links and `.call` links. **Flagging for Track A now:** Track C's
multi-call lowering (C3/C4) is blocked on Track A's `Runs.call` constructor; the
single-call lowering can proceed against the current `messageCall_call_runs`
without waiting.

---

## 6. Planned lowering-preservation statement (shape only — proved in C3)

The simulation we will prove. Informally: *running the lowered bytecode as a
top-level `messageCall` yields the same observable outcome (final self-storage and
exit) that the IR small-step semantics produces.* Two coupled pieces:

**(a) Per-step / per-block simulation (the engine).** A relation
`Match : IRConf → Frame → Prop` (locals ↔ stack contents the lowering would
materialise; IR `storage` ↔ self-account storage; IR `gas` ↔ `gasAvailable`; IR
`(label, pc)` ↔ `Frame.exec.pc` via the offset table) such that every IR step is
simulated by a `Runs` segment of the lowered code:

```
theorem lower_simulates_step (prog) {c c' : IRConf} {fr : Frame}
    (hstep : IRStep prog c c') (hmatch : Match c fr) :
    ∃ n fr', Runs n fr fr' ∧ Match c' fr'        -- non-call statements
                                                 -- (call statements: a CallReturns segment)
```

**(b) Top-level preservation (the user-facing statement).** Closing the IR run
under reflexive-transitive `IRStep` and discharging at the boundary with
`messageCall_runs` / `messageCall_call_runs`:

```
theorem lower_preserves (prog) (p : CallParams) (w : Word) (out : Halt)
    (hp : p.codeSource = .Code (lower prog))            -- p runs the lowered code
    (hentry : Match (prog.initialConf w) ⟨entry frame of p⟩)
    (hir : IRRunsToHalt prog (prog.initialConf w) out) :
    messageCall p = .ok (toCallResult ⟨the EVM halt matching out⟩)
```

i.e. *the lowered program's `messageCall` observable equals the IR's halt
observable.* For a call-free `prog` this is `messageCall_runs ∘ simulation`; for a
single-call `prog` it is `messageCall_call_runs ∘ simulation`; for multi-call it
needs Track A's `Runs.call` (see §5).

The exact `Match` invariant, the gas-cost equalities, and the stack-layout
discipline are the substance of C2/C3 and are intentionally left open here. C1's
job is the IR datatypes, the lowering *type signature*, and this statement *shape*.

---

## 7. C1 deliverable boundary

C1 ships: this doc; a compiling `LirLean` Lean skeleton (lakefile requiring
exp003's `bytecode_layer` for the EVM/`Runs` API; the IR datatypes of §2; the
`lower : Program → ByteArray` **type signature**, with a body only if it compiles
without `sorry`); no `sorry`/`axiom`-backed theorems. The semantics relation
(`IRStep`) and the lowering body/preservation proofs are C2/C3.
