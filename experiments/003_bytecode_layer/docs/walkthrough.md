# Experiment 003, explained from the ground up

This document assumes you know Lean but **not** the low-level EVM. It explains
what we are actually proving, at what level of abstraction, why the example
programs are hardcoded, what the puzzling counterexample means, how the proof is
structured, and where the limits are. It is the "understand the whole thing"
document; `results.md` is the terse evidence, `Spec.lean` is the audit surface.

---

## 1. The 5-minute EVM background you need

The Ethereum Virtual Machine runs **bytecode**: a flat array of 1-byte opcodes.
A contract account stores its code and a **storage** map (256-bit key → 256-bit
value, all cells default to 0). Execution is a stack machine. The handful of
opcodes that appear in this experiment:

| opcode | byte | meaning |
|---|---|---|
| `PUSH1 x` | `0x60 x` | push the 1-byte constant `x` onto the stack |
| `PUSH3`/`PUSH4` | `0x62`/`0x63` | push a 3- or 4-byte constant |
| `SSTORE` | `0x55` | pop `key`, pop `value`, set `storage[key] = value` |
| `CALL` | `0xF1` | pop 7 args, call another contract, push a 0/1 success flag |
| `STOP` | `0x00` | halt successfully |

**Gas.** Every opcode costs *gas*; a call is given a gas budget and aborts
("out of gas") if it runs out. Two gas facts matter here and *only* here:

- A first-time write of a nonzero value to a fresh storage cell (`SSTORE`) costs
  **22100** gas (plus a 6 for two pushes ⇒ **22106** total for our callee).
- **The 63/64 rule (EIP-150).** When contract A `CALL`s contract B, B does *not*
  get all of A's remaining gas — it gets at most **63/64** of it. This single
  rule is the reason the headline theorem needs a gas floor (§5).

**What a `CALL` actually does.** It looks up the code stored at the target
*address* in the world state and runs it as a nested execution with its own gas
budget. If that nested run fails (e.g. out of gas), **its effects are rolled
back, but the caller does not crash** — the caller just gets a `0` pushed (the
"failure" flag) and keeps going. That asymmetry is the whole story of §5.

---

## 2. What "the abstraction level" means here

leanevm (the vendored semantics we build on) defines execution in three layers.
You can picture a dial; we state our theorems at the **top** of it.

```
  messageCall p        ← THE BOUNDARY WE STATE THEOREMS AT
       │                  input:  a CallParams (world + which code + gas budget)
       │                  output: a CallResult (did it succeed? output bytes?
       │                          final account/storage map?)
       ▼
  drive (fuel) …        ← the interpreter loop (the only recursion in the EVM):
       │                  run one instruction, OR descend into a sub-call, OR
       │                  deliver a finished sub-call's result to its parent.
       ▼
  stepFrame frame       ← execute ONE opcode: mutate stack/pc/gas/storage,
                          or signal "halt" / "I need to make a call".
```

- **`beginCall p`** is the setup step *inside* `messageCall`: it applies any
  value transfer, builds the execution environment, loads the code from the
  account, and produces the initial `frame` (or, for built-in "precompiled"
  contracts, finishes immediately). After it, `drive` takes over.
- **A `frame`** is the messy internal state: program counter, operand stack,
  gas counter, memory, the storage being mutated. This is the stuff we want
  *out* of our theorem statements.
- **`messageCall`** hides all of that. It takes a `CallParams` and returns a
  `CallResult`. We state every theorem here, and we only look at *observables*
  of the `CallResult`: `success`, `output`, and a chosen `storage` cell. No
  frame, no pc, no stack, no gas counter appears in a theorem.

**The "fuel" subtlety (you read this correctly).** `drive` recurses on a `fuel`
counter purely so Lean accepts it as a terminating function. The fuel is seeded
from the gas budget at a generous ratio, and every real instruction costs ≥ 1
gas, so **fuel can never actually run out for a gas-respecting run**. `OutOfFuel`
therefore is not a program behaviour — it would only mean "the gas table is
broken." We discharge that concern *once* (a lemma `two_le_seedFuel` and the
`drive_*` equations) and fuel never appears again.

**Why this matters for the bigger project.** Because fuel is invisible, an
execution at this boundary effectively just **succeeds or reverts**. That is
exactly what lets a higher-level IR ignore gas and be modelled as
"succeeds / fails." *Except* — and this is the real caveat (§8) — gas becomes
*observable* in two places: the 63/64 cap at a `CALL`, and any opcode that reads
the remaining gas (`GAS`, `gasleft()`-style introspection), which this
experiment does **not** yet handle.

---

## 3. The programs are hardcoded examples — and that's the point (but also the limit)

Yes: **every theorem here is about specific, handwritten byte arrays**, not a
general statement about all programs. `Programs.lean` holds them:

```lean
def calleeProg : ByteArray := ⟨#[0x60,0x05, 0x60,0x07, 0x55, 0x00]⟩
-- disassembly:  PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP
```

Read it: push `5`, push `7`, then `SSTORE` pops the top two (`key = 7`,
`value = 5`) and does `storage[7] = 5`, then stop.

- **"Cell 7" is not special or random in any deep sense.** It is simply the slot
  *this toy callee chose to write to*. We picked the literals `7` and `5` so the
  contract has a visible, checkable persistent effect. The theorem then observes
  exactly that slot. If we'd written `SSTORE` of `42` at slot `9`, the theorem
  would observe slot `9 = 42`. There is no semantic content in the specific
  numbers — they're a fingerprint we can point at.

- **The theorem is program-specific.** `messageCall_call_storageAt` is a
  statement about *this* caller calling *this* callee. It is **not** "every CALL
  preserves storage" or anything general. (The call-free `stop`/`pushStop`
  theorems are general over the *world* `p`, but still about a fixed program.)

**Why hardcode?** Because experiment 003's goal is not a general CALL theorem —
it is to **build and validate a reusable reasoning layer** against the real
semantics, and *demonstrate* it composes on concrete programs end-to-end. The
durable, general output is the **bricks** in `Reasoning/` (e.g. the `CALL` rule
works for any value-0 call to any address; the `drive` equations are fully
general). The hardcoded programs are worked examples that exercise those bricks.
Generalising the *examples* into program-agnostic theorems is explicitly a next
step (§9), not something we claim to have done.

---

## 4. What we observe, and why a "named observable" would help

A finished call yields a `CallResult` with many fields (success flag, output
bytes, the whole post-execution account map, gas remaining, …). We don't want a
theorem dragging the whole account map around, so `Observables.lean` projects
just the world-independent pieces:

```lean
structure Observables where
  success : Bool
  output  : ByteArray

def CallResult.observe (r : CallResult) : Observables := { success := r.success, output := r.output }

-- and, separately, one storage cell, read exactly like the EVM's SLOAD:
def CallResult.storageAt (r : CallResult) (addr : AccountAddress) (key : UInt256) : UInt256 := …
```

Your instinct is right that this reads awkwardly: theorems destructure
`{ success := true, output := .empty }` inline and bolt on a separate
`storageAt`. A cleaner design (proposed in §9) is a single named observation
type with smart constructors — e.g. "succeeded with empty output and `storage`
at `(addr,key)` equal to `v`" as one named thing — so the spec reads as a
sentence instead of a tuple. I did **not** change this yet; it's a proposal.

---

## 5. The counterexample, explained slowly (this is the crux)

Two theorems sit side by side. Read them as a pair.

```lean
-- (A) there is a gas floor G₀ above which the callee's slot 7 ends up = 5
theorem messageCall_call_storageAt :
    ∃ G₀, ∀ g, G₀ ≤ g → (messageCall (callerParams g)).map (storageAt · addrCallee 7) = .ok 5

-- (B) at the specific modest gas g = 24000, that same slot ends up = 0
theorem call_counterexample :
    (messageCall (callerParams 24000)).map (storageAt · addrCallee 7) = .ok 0
```

Here is the scenario both describe. The **caller** contract pushes the 7 `CALL`
arguments and calls the **callee**; the callee tries to do its `SSTORE` (write
`5` to slot `7`); then the caller `STOP`s.

- **With lots of gas** (any `g ≥ G₀`, where the proof uses `G₀ = 100000`): the
  callee receives ≥ 22106 gas through the 63/64 cap, its `SSTORE` succeeds and
  commits, and afterwards slot 7 reads **5**. That's theorem (A).

- **With modest gas** (`g = 24000`): after the caller's own costs, 63/64 of
  what's left is **21045** gas handed to the callee — but the `SSTORE` needs
  **22106**. So the callee **runs out of gas**, and per §1 its write is **rolled
  back**. Crucially, the *caller does not crash*: it receives the `0` failure
  flag, ignores it, and `STOP`s **successfully**. So the overall `messageCall`
  completes fine — yet slot 7 still reads **0**. That's theorem (B).

**Why (B) exists at all — what it is *for*.** It proves the gas floor in (A) is
**not removable**. The tempting simpler statement would be:

> "if the message call completes, then slot 7 = 5."

(B) is a concrete witness that this simpler statement is **false**: at
`g = 24000` the call completes *and* slot 7 = 0. So you genuinely need the
"`∃ G₀, ∀ g ≥ G₀`" — the result holds only above a gas floor, because below it
the 63/64 cap silently starves the inner write while the outer call sails on.
This is the whole subtle danger of EVM external calls in one example: **a
sub-call can fail invisibly to its parent.** (B) is the executable proof that the
danger is real here, not hypothetical.

---

## 6. How the proof is built (the structure, not the tactics)

You don't care about tactic lines; you care about *what depends on what*. The
shape is a short ladder, each rung a reusable lemma, climbing from "one opcode"
to "a whole call."

```
  Reasoning/  (general, reusable — the "engine"; proved once, used everywhere)
    Step      : one lemma per opcode — "at this pc, with enough gas, stepFrame
                does exactly <this>."  (the gas/overflow guards discharged once)
    Call      : the CALL rule — stepFrame on a CALL emits "descend into the
                child", where the child's code is the REAL code at the target
                address (no oracle). 63/64 cap lives here.
    Drive     : the interpreter loop equations + the messageCall→drive bridge.
    DriveGen  : same loop, but with a suspended parent on the stack (needed once
                a sub-call is running).
    Begin     : beginCall on a code call = <this initial frame>.

  Proof/      (specific — the worked examples; never exported)
    each capstone proof = "unfold messageCall via the bridge, then replay the
    program one instruction at a time using the Step lemmas, take the CALL via
    the Call rule, run the child, deliver the result, read off the observable."
```

The single most important structural property (and what §B of the refactor
enforced): **the proofs never unfold the semantics themselves.** They never crack
open `messageCall`/`beginCall`/`stepFrame`/`drive`. Those are touched in exactly
four *bridge* lemmas in `Reasoning/`; everything else composes those bridges.
That's why the spec can be reshaped without the proofs collapsing.

**What we depended on.** (1) leanevm's executable semantics — which ships
*no* reasoning lemmas, so we proved all the bricks ourselves. (2) One upstream
leanevm fix (`9cefe5b`) that removed a non-standard axiom from the execution path
and made the `CALL` internals visible; without it, axiom-cleanliness was
impossible. Everything we export now reduces to only the three standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 7. "Capstone" — the name, and why it should change

A **capstone** just means "the crowning end-goal theorem a milestone builds up
to" — the top of the ladder for that milestone. You're right that
`Capstone1`/`Capstone3`/`CapstoneCall` are bad file names: they encode *the order
we happened to tackle them in*, not *what they prove*. They should be renamed to
describe their content, e.g.:

| now | proposed |
|---|---|
| `Proof/Capstone1.lean` | `Proof/CallFree.lean` (STOP, PUSH, single SSTORE) |
| `Proof/Capstone3.lean` | `Proof/Sequence.lean` (a straight-line run of several writes) |
| `Proof/CapstoneCall.lean` | `Proof/ExternalCall.lean` (the CALL story + counterexample) |

This is a proposal in §9, not yet applied.

---

## 8. What is exported vs. internal

Only the **meaningful end results** are exported on the audit surface
(`Spec.lean`): the four call-free observations and the two external-call
theorems. Everything else — and it is a *lot* — is internal `Proof.*`: dozens of
"the program decodes to this opcode at this offset," "the frame after the two
pushes is exactly this," "the child run delivers this result," gas arithmetic,
etc. These are necessary scaffolding to drive the concrete reductions but carry
no audit value, so they stay out of `Spec.lean`. (The reflexivity witness
`messageCall_child_reflexive` is internal for a different reason: its statement
necessarily names an internal frame, so it can't be frame-free.)

---

## 9. Limitations and next steps (honest)

**Limitations — what this does NOT yet cover:**

- **Program-specific, not general.** Every theorem is about fixed handwritten
  bytecode (§3). There is no "for all programs / all callees" theorem yet.
- **`value = 0` calls only**, a **single** callee, **no nesting / reentrancy**,
  and **no `RETURN`/return-data** (the callee's only effect is `SSTORE`).
- **Gas introspection is unaddressed.** The "executions just succeed or revert,
  ignore gas" picture (§2) holds *because* gas is invisible — but it is *not*
  invisible to (a) the 63/64 cap at a call, which we model, and (b) opcodes that
  read remaining gas (`GAS`, gas-dependent branching). A program that *observes*
  its own gas cannot be abstracted as gas-free, and we have not modelled that.
  This is the main conceptual gap for "IRs that ignore gas."
- **Proofs are concrete defeq reductions** with cranked heartbeats — they replay
  each program instruction-by-instruction, so they won't scale to large programs
  without the generalisation below.

**Next steps:**

1. **Generalise the examples into rules.** Turn the concrete capstones into
   callee-/program-agnostic theorems (a general CALL-preserves-storage rule, a
   general sequencing lemma), so the next layer reasons abstractly instead of
   replaying bytes.
2. **A named observation type** with smart constructors (§4), so specs read as
   sentences.
3. **Rename the proof files** by content (§7).
4. **Then** introduce a real source IR (Plank SIR) with an abstraction gap, and
   confront the gas-introspection question head-on.
