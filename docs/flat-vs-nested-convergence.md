# Flat vs. nested EVM — a convergence design report

*Cross-cutting synthesis for the project lead. Read-only on all Lean; every type and
theorem signature below is quoted verbatim from source on branch
`exp003-fuel-layer-cleanup`. Where a claim is a design judgment or an estimate rather
than a checked fact, it is flagged as such — final calls are Eduardo's, and the open
questions are collected in §7.*

---

## TL;DR

The project carries **two EVM semantics** that the END GOAL wants to converge:

- **FLAT** (exp003, `experiments/003_bytecode_layer/`): philogy's `EVMLean` — one
  tail-recursive `drive` over a shared `List Pending`, one fuel counter, CALL pushes the
  parent and continues the same loop (a defunctionalized trampoline; geth/revm lineage).
  It has a **full reasoning layer**: the `Runs` relation with a `call` constructor, the
  `messageCall` boundary bridge, `Behaves`/`Outcome`/`Observables` vocabulary, opcode
  rules, and a CFG combinator. Headline: `messageCall_never_outOfFuel` (unconditional).
- **NESTED** (exp004, `experiments/004_nested_evmyul/`): a Yul-stripped `EVMYulLean` — a
  `mutual` block `call`/`step`/`X`/`Ξ`/`Θ`/`Lambda`, fuel-passing, near-literal
  Yellow-Paper; `Ξ` builds a *fresh* child machine and returns a tuple, `Θ`/`call`
  consume it. Headline just CLOSED: `Θ_never_outOfFuel`, axiom-clean, with the
  linear-product bound `fuelBound g e = (1025 − e)·(g + 8)`.

**Headline recommendation (2–3 sentences).** A **shared observable-level interface** —
a `messageCall`-shaped method (world + code + gas → a three-way `Outcome` of storage
delta / halt result / output) plus a never-OOF obligation — is **feasible and largely
mechanical on the flat side, but is a real build on the nested side, because exp004
today has *no* reasoning surface above `Θ` at all** (no `Runs`, no observables, no
triple — only `Θ_never_outOfFuel`). A full proved equivalence `driveNested ≃ drive` is a
**substantially bigger lift** than the interface and is not on the critical path; the
fallback that is genuinely cheap and high-value is parameterizing Track C's lowering over
an *abstract* EVM interface so leanevm / EVMYulLean / verifereum become swappable
underneath. The single fact that makes convergence *more* tractable than the END-GOAL
framing assumes: the two state algebras are **siblings of one lineage**, sharing
`AccountMap`, `Substate`, `ExecutionEnv`, `ToExecute`, and an *identical*
`Account.lookupStorage` storage lens — so the observable projection lines up almost for
free. The fact that makes it *less* tractable than assumed: they are nonetheless **two
distinct Lean packages** (`«evm»` vs. `«evmyul»`) with genuinely divergent field types
(`gasAvailable`/`nonce` are `UInt64` flat vs. `UInt256` nested), so "both instantiate the
same typeclass" cannot mean "over the same `State` type" — the interface must be
state-polymorphic.

---

## 1. The two models, side by side

### 1.1 The execution core

**Flat — one `drive`, one fuel.** `experiments/003_bytecode_layer/EVMLean/Evm/Semantics/Interpreter.lean`:

```lean
def drive (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) :
    Except ExecutionException FrameResult
def messageCall (params : CallParams) : Except ExecutionException CallResult :=
  match beginCall params with
    | .inr result => .ok result
    | .inl frame => FrameResult.toCallResult <$> drive (seedFuel params.gas) [] (.inl frame)
def seedFuel (gas : UInt64) : ℕ := 2 * gas.toNat + 4096
```

A *nested* CALL never re-enters `messageCall`; it reaches `drive`'s `.needsCall` arm,
which `beginCall`s the child and recurses with the **same** `fuel` and the parent
`.call pending` consed onto the **same** `stack`. One counter for the whole tree
(verified in `docs/verifereum-nested-call.md` §A).

**Nested — a 6-layer `mutual` block, fuel-passing.**
`experiments/004_nested_evmyul/EVMYulLean/EvmYul/EVM/Semantics.lean` (signatures
verbatim, bodies elided):

```lean
mutual
def call (fuel : Nat) (gasCost : Nat) (blobVersionedHashes : List ByteArray)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool) (evmState : State) :
  Except EVM.ExecutionException (UInt256 × State)
def step (fuel : ℕ) (gasCost : ℕ) (instr : Option (Operation × Option (UInt256 × Nat)) := .none)
  : EVM.Transformer
def X (fuel : ℕ) (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State)
def Ξ (fuel : ℕ) (createdAccounts : …) (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
  (σ : AccountMap) (σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
  Except EVM.ExecutionException (ExecutionResult (… × AccountMap × UInt256 × Substate))
def Lambda (fuel : ℕ) … -- CREATE / CREATE2
def Θ (fuel : Nat) (blobVersionedHashes : List ByteArray) (createdAccounts : …)
  (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap)
  (A : Substate) (s o r : AccountAddress) (c : ToExecute) (g p v v' : UInt256)
  (d : ByteArray) (e : Nat) (H : BlockHeader) (w : Bool) :
  Except EVM.ExecutionException
    (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × Bool × ByteArray)
end
```

The nesting is *syntactic*: `Ξ` (line 559) seeds a `freshEvmState` and runs `X` on it,
returning an `ExecutionResult`; `Θ` (line 803) calls `Ξ` and pattern-matches its tuple;
`call` (line 167) calls `Θ` at `e := Iₑ + 1` with `g := .ofNat callgas` and folds the
returned `(σ', g', A', z, o)` back into the parent state. A child run is an honest
subterm with its own value — the Yellow-Paper `Θ`-invokes-`Ξ`-returns-tuple shape, almost
verbatim (`docs/verifereum-nested-call.md` §C: the same shape Verifereum gets from its
depth-sliced `OWHILE`).

### 1.2 The state algebras — sibling, not identical

Both descend from the same EVMYulLean/leanevm lineage, and it shows. The two `State`
records are field-for-field the same modulo two renames:

| flat `Evm.State` (`EVMLean/Evm/State.lean`) | nested `EvmYul.State` (`EVMYulLean/EvmYul/State.lean`) |
|---|---|
| `accounts : AccountMap` | `accountMap : AccountMap` |
| `originalAccounts : AccountMap` | `σ₀ : AccountMap` |
| `substate : Substate` | `substate : Substate` |
| `executionEnv : ExecutionEnv` | `executionEnv : ExecutionEnv` |
| `blocks`, `genesisBlockHeader`, `createdAccounts`, `totalGasUsedInBlock`, `transactionReceipts` | *(identical set, identical names)* |

The running machine state differs in *shape*: flat wraps everything in a `Frame`
(`EVMLean/Evm/Semantics/Frame.lean`):

```lean
structure Frame where
  kind       : FrameKind          -- .call checkpoint | .create address checkpoint
  validJumps : Array UInt32
  exec       : ExecutionState     -- extends Evm.State, Evm.MachineState
```

whereas nested uses `EVM.State` (`EVMYulLean/EvmYul/EVM/State.lean`):

```lean
structure State extends EvmYul.SharedState where
  pc : UInt256
  stack : Stack UInt256
  execLength : ℕ
```

The storage observable is **identical** on both sides — `Account.lookupStorage`
(`…/State/AccountOps.lean:11` in *both* packages):

```lean
def lookupStorage (self : Account) (k : UInt256) : UInt256 := self.storage.findD k 0
```

and `ToExecute` is byte-identical (`| Code (code : ByteArray) | Precompiled (precompiled : AccountAddress)`).

**But two genuine type divergences block any "same type" instantiation:**

1. **Distinct packages / namespaces.** `EVMLean/lakefile.lean` declares `package «evm»`;
   `EVMYulLean/lakefile.lean` declares `package «evmyul»`. Even where structures are
   field-identical, `Evm.AccountMap` and `EvmYul.AccountMap` are *different Lean types*.
   A shared interface cannot be "over `State`" — it must abstract the state type.
2. **Word-width divergence in the account/gas algebra.** Flat `Account.nonce : UInt64`
   and flat `gasAvailable : UInt64` (`EVMLean/Evm/Machine/MachineState.lean:23`); nested
   `Account.nonce : UInt256` and nested `gasAvailable : UInt256`
   (`EVMYulLean/EvmYul/MachineState.lean:24`). This is *not* a cosmetic rename — it
   changes the gas arithmetic and is the reason the never-OOF bounds are phrased
   differently (`seedFuel : UInt64 → ℕ` vs. `fuelBound : ℕ → ℕ → ℕ` on `g.toNat`).

### 1.3 The reasoning surface — asymmetric *today*

This is the single most important structural fact for any convergence plan and it cuts
against the END-GOAL framing's symmetry:

- **Flat has a complete reasoning layer.** `Runs` (`BytecodeLayer/Hoare.lean#L114`,
  `refl`/`step`/`call`), `Runs.trans`, seven `runs_*` opcode rules, `runs_branch` CFG
  combinator, the `messageCall_runs` bridge, the `Observables`/`Outcome`/`completedWith`
  vocabulary (`BytecodeLayer/Observables.lean`), and the `Behaves` for-all-programs
  predicate (`BytecodeLayer/Hoare/Behaves.lean#L45`). Track C already *consumes* this
  surface end-to-end.
- **Nested has essentially nothing above `Θ`.** A grep of `experiments/004_nested_evmyul/NestedEvmYul/`
  for `triple|behaves|outcome|observable|hoare|messageCall|completedWith` returns **only
  docstring mentions inside `NeverOutOfFuel.lean`**. The package root is two lines:
  ```lean
  import EvmYul.EVM.Semantics
  import NestedEvmYul.NeverOutOfFuel
  ```
  Everything else in `NestedEvmYul/` is the gas-arithmetic and precompile-gas brick
  libraries that feed the never-OOF proof. There is **no `Runs`, no observable
  projection, no `Ξ`-triple, no frame rule as a theorem.**

So the often-repeated framing — "flat: no frame rule but earned composition; nested:
textbook frame rule by construction" — is precise only if "by construction" is read as
**structurally available, not yet proven**. The nested `Ξ`/`Θ` *admit* a clean
procedure-call triple (the child is a subterm with its own value; cf.
`docs/verifereum-nested-call.md` §C), but that triple is **not a theorem in the repo
yet**. The flat side, conversely, has *paid for and shipped* its composition
(`Runs.call` + `drive_reconcile`). Right now the flat side is **ahead on built
reasoning**, and the nested side is ahead only on *latent* ergonomics.

### 1.4 The trade-off matrix

| Dimension | FLAT (exp003) | NESTED (exp004) |
|---|---|---|
| **Call model** | parent pushed on shared `List Pending`, one loop continues (trampoline) | `Θ`→`Ξ` builds a fresh child machine, returns a tuple `call` folds back |
| **Fuel / gas** | one `ℕ` fuel, pass-*by-position* on the shared stack; `seedFuel = 2·gas+4096` | one `ℕ` fuel **passed by value** into each child layer; gas `UInt256` |
| **Termination** | trivial — one structurally-decreasing `fuel` covers all of CALL/CREATE/reentrancy | mutual fuel-passing recursion; depth×gas measure |
| **never-OOF proof** | `messageCall_never_outOfFuel` — **unconditional**, one measure argument over `gasFundsDescent` (5 per-transition conjuncts) | `Θ_never_outOfFuel` — **conditional on `fuelBound g e + 3 ≤ fuel ∧ e ≤ 1024`**, 5-layer mutual induction + `gas_mono` + ~250-line depth-preservation keystone |
| **Fuel bound** | clean linear `2·gas + 4096`, **no depth term** | linear-product `(1025 − e)·(g + 8)` — linear in gas, depth *factor* |
| **Compositionality** | frame rule must be *earned* — was; `Runs.call` makes multi-call `Runs.trans` | frame rule *latent* by subterm structure — **not yet built** |
| **Built reasoning layer** | full (`Runs`, observables, CFG, `Behaves`, bridge) | **only `Θ_never_outOfFuel`** |
| **Conformance lineage** | executable spec (leanevm `lake exe conform`) | executable spec (EVMYulLean `lake exe conform`) |
| **YP fidelity** | further — defunctionalized CPS/trampoline | near-literal `Θ/Ξ` mutual recursion |

---

## 2. Same result, two models — the never-OOF worked example

Both formalizations have now **proved the same high-level property** — "a top-level
message call never reports `OutOfFuel`" — over two structurally unrelated execution
engines. This is the existence proof that the convergence END GOAL is *achievable in
principle*: the same theorem statement (modulo the interface's vocabulary) is a theorem
in both worlds. It is worth dwelling on *how differently* it is proved, because that
delta is exactly the ergonomics signal the bake-off is measuring.

**Flat — unconditional, one measure.** `BytecodeLayer/Semantics/Interpreter/NeverOutOfFuel.lean#L158`:

```lean
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel :=
  messageCall_never_outOfFuel_of_gasFundsDescent gasFundsDescent_holds p
```

No fuel hypothesis, no `Frame`, no depth side-condition — `seedFuel = 2·gas+4096` is
baked into `messageCall`, and the bound is discharged *internally* by
`gasFundsDescent_holds` (the five per-transition gas-decrease conjuncts) fed to a general
measure theorem. One mutual induction's worth of work; the statement a downstream caller
sees has **zero** premises.

**Nested — conditional, five mutual layers + a keystone.** `NestedEvmYul/NeverOutOfFuel.lean#L4665`:

```lean
theorem Θ_never_outOfFuel (fuel : ℕ) (bvh : List ByteArray) (cA : …) (gh : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (c : ToExecute) (g p v v' : UInt256) (d : ByteArray) (e : Nat) (Hd : BlockHeader) (w : Bool)
    (he : e ≤ 1024) (hfuel : fuelBound g.toNat e + 3 ≤ fuel) :
    Θ fuel bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w ≠ .error .OutOfFuel :=
  (never_oof fuel).2.2.1 bvh cA gh blocks σ σ₀ A s o r c g p v v' d e Hd w he hfuel

def fuelBound (g e : ℕ) : ℕ := (1025 - e) * (g + fuelHops)   -- fuelHops := 8
```

This is a one-line projection of `never_oof` (`#L4543`), a **5-layer mutual induction**
over `step`/`call`/`Θ`/`Ξ`/`X` by strong induction on `fuel`, with per-layer offsets
(`k_Θ = 3, k_Ξ = 2, k_X = 1, k_step = 0`). It rests on (per the file's own inventory,
`#L4709`): a `gas_mono` mutual induction, a ~250-line `step`/`Z` **depth-preservation
keystone** (so `fuelBound`'s depth index is a sound loop invariant,
`X_loop_noOOF_bound`), the `X`-loop gas-descent library, and precompile-gas plumbing. The
statement a caller sees carries **two premises** (`he`, `hfuel`).

**The honest read of the gap.** The asymmetry is real but *moderate* (and the
`EXPERIMENT-REPORT.md` "Sharpening" of 2026-06-23 already corrected the earlier
over-statement): the fuel bound is **linear in gas** on *both* sides; nested merely adds
a depth *factor* `(1025 − e)`, not the super-linear `(g+1)^(1025−d)` the overnight runs
feared. The cost difference is **mechanization effort** (two mutual inductions + a
depth-preservation keystone + a conditional statement vs. one induction + an
unconditional statement), not a complexity-class blow-up. **Design judgment, flagged:**
this is a genuine but contained termination-ergonomics advantage for flat; it does not by
itself decide the bake-off, because the property *did* close on both sides.

**Why this matters for the interface (§3).** A shared interface's never-OOF obligation
must be phrased to accommodate *both* — i.e. it must allow a fuel/depth side condition
(nested needs it) while letting flat discharge it trivially (flat has none). The natural
shape is "the implementation's own `messageCall`-analogue never yields `OutOfFuel` for
its own seeding discipline" — flat proves it unconditionally, nested proves it under its
`fuelBound` envelope, and the interface hides the seeding inside the method (see §3.2).

---

## 3. Can they implement the same interface? (plug-and-play)

### 3.1 The proposed `EVMSemantics` structure

Because the two state types are distinct (§1.2), the interface **must be polymorphic over
the state/world type** — it cannot be a typeclass "over `State`". A first concrete cut
(this is a *design proposal*, not shipped code):

```lean
-- proposed; not in the repo
structure EVMSemantics where
  World    : Type                              -- CallParams (flat) | the Θ arg bundle (nested)
  Result   : Type                              -- CallResult (flat) | the Θ output tuple (nested)
  /-- the boundary entry point both engines already have -/
  run      : World → Except ExecutionException Result
  /-- project a finished result to the shared three-way observable -/
  observe  : Except ExecutionException Result → Outcome
  /-- the never-OutOfFuel obligation, allowing an implementation-local envelope -/
  neverOOF : ∀ w : World, Adequate w → run w ≠ .error .OutOfFuel
```

with `Outcome` the **shared** observable vocabulary already shipped on the flat side
(`BytecodeLayer/Observables.lean#L72`):

```lean
inductive Outcome where
  | completed (out : ByteArray) (σ : AccountAddress → UInt256 → UInt256)
  | reverted  (out : ByteArray)
  | exception (e : ExecutionException)
```

and `Adequate` a per-implementation predicate that is `True` for flat and
`fuelBound g e + 3 ≤ fuel ∧ e ≤ 1024` for nested (folded into the `World` bundle, so the
top-level caller supplies the fuel). The higher-level theorems Track A flags as interface
candidates — `messageCall_runs_calls`, `messageCall_calls_completedWith`,
`messageCall_never_outOfFuel` — become *fields* (or derived lemmas) the structure
demands.

### 3.2 What lines up — and it is more than the framing assumes

- **The boundary entry point exists on both sides already.** Flat: `messageCall :
  CallParams → Except _ CallResult`. Nested: `Θ : (19 args) → Except _ (6-tuple)`. Both
  are total functions from "a described call" to "an `Except` of a result", with
  `OutOfFuel` a possible error — the `run` field is a real method on both.
- **The observable projection is nearly free.** The flat `Outcome` already reads its
  storage cell through `Account.lookupStorage`, which is **the identical function** in the
  nested package. So `observe` for nested is: split `Θ`'s output `(…, σ', g', A', z, o)`
  on the success flag `z`, and read storage as `fun a k => (σ'.find? a).option 0
  (·.lookupStorage k)` — exactly the flat `CallResult.storageAt` definition transcribed
  onto the nested tuple. **This is the cheapest part of the whole convergence** and is
  *more* compatible than the END-GOAL framing (which treats "different result encodings"
  as a friction) suggests, precisely because the storage lens is shared lineage.
- **The never-OOF obligation is expressible for both** (§2): unconditional discharge for
  flat, `fuelBound`-conditioned for nested, both hidden behind `Adequate`.

### 3.3 What does *not* line up — the concrete friction

1. **Distinct state types ⇒ the interface is polymorphic, and `observe` is the only
   bridge.** You cannot state `messageCall_runs_calls` *abstractly* in a way both
   instantiate, because its very statement mentions `Runs`/`Frame`/`stepFrame` — flat
   structures that **have no nested analogue** (§1.3). Only the *observable-level*
   theorems (`messageCall_calls_completedWith`, `messageCall_never_outOfFuel`) are
   state-agnostic enough to be shared interface obligations. The **frame-level**
   program-logic rules (`Runs.trans`, the `runs_*` rules, `messageCall_runs`) are
   exp003-specific by construction and **cannot** be interface fields without first
   building a `Runs`-analogue on the nested side. The flat side already self-flags this
   altitude tension (`BytecodeLayer/Spec.lean#L22`). **Consequence:** the shared
   interface is feasible only at the **observable level**; the frame-level surface stays
   per-implementation.
2. **Result encodings differ in arity and field types.** Flat `CallResult`
   (`createdAccounts, accounts, gasRemaining : UInt64, substate, success, output`) vs.
   nested `Θ`'s positional `(createdAccounts, σ', g' : UInt256, A', z : Bool, o)`. The
   `gasRemaining` width (`UInt64` vs `UInt256`) again bites. `observe` absorbs this — but
   only because `observe` deliberately *forgets* gas and createdAccounts, keeping just
   success/output/storage. Any interface obligation that needed to compare *gas
   remaining* across the two would hit the width mismatch head-on.
3. **The nested side has no `messageCall`-with-`seedFuel` wrapper.** Flat's `messageCall`
   hides fuel entirely (`seedFuel params.gas` internally). Nested's `Θ` takes `fuel`
   *explicitly* as its first argument. To match flat's "fuel-free" `run`, the nested
   instance must wrap `Θ` with a `seedFuel`-analogue `fun w => Θ (fuelBound w.g w.e + 3)
   …`, and *then* `neverOOF` is exactly `Θ_never_outOfFuel` applied at that seeding. This
   wrapper is small but it is **not yet written**.
4. **Argument bundling.** Flat already packs its 22 call parameters into the `CallParams`
   record; nested `Θ` takes 19 *positional* arguments. The nested `World` for the
   interface would need a record mirroring `CallParams` and an unpacking adaptor into
   `Θ`. Mechanical, but real surface.

### 3.4 Verdict on §2-question

**Plug-and-play is feasible at the observable level and infeasible at the frame
level — and that boundary is exactly where the flat side already drew its own altitude
caveat.** The shared interface can demand: `run`, `observe`, the observable external-call
rule (`completedWith`), and `neverOOF`. It *cannot* demand the `Runs`/CFG program logic,
because that machinery does not exist on the nested side and is not state-agnostic. So
"both instantiate the same theorems" is true **for the observable-level theorems only**,
and even those require, on the nested side, (a) building the `observe` projection and (b)
a `seedFuel`-style wrapper around `Θ` — neither hard, but both currently absent.

---

## 4. If full plug-and-play isn't feasible — the two fallbacks

### 4.1 Fallback (a): swap *Ethereum formalizations* under the IR/reasoning layer

This is the **strongest-value, lowest-risk** option and it is largely independent of the
flat-vs-nested question. Track C's lowering today consumes the flat surface *only through
a fixed, small contract*: `messageCall_runs` + the `Runs.call` constructor + a fixed set
of `runs_*` opcode rules (`track-c-review.md` §7). The Track C review states the retarget
explicitly: the lowering *architecture* (`Match`, the `sim_*` bricks, the layout/decode
infra) "are about the lowering and the IR, not about which bridge crosses the boundary";
only `lower_preserves_discharge` (`LirLean/Match.lean#L333`) consumes the concrete
`messageCall_runs`. So:

> **Parameterize the lowering's boundary discharge over an abstract `EVMSemantics` (the
> §3.1 structure) rather than over exp003's concrete `messageCall_runs`.** Then leanevm,
> EVMYulLean, and (in principle) verifereum are swappable *underneath the IR
> preservation proof* — provided each supplies the observable-level contract.

**Feasibility: high.** This is the "mechanical substitution Phase 2a is designed to make
trivial" the Track C review already anticipated, and it does **not** require a `Runs`
analogue on the nested side *if* the lowering is restated to depend only on the
observable-level `completedWith`/`run`/`observe` contract rather than on the frame-level
`Runs.call` composition. **Caveat / open question (§7):** Track C's *prefix* assembly
currently builds a concrete `Runs` value via the `runs_*` rules — so to be truly
backend-agnostic the lowering would need to express even the straight-line prefix through
an abstract step relation the interface provides, *or* accept that the prefix-assembly
stays flat-specific while only the call-boundary crossing is abstracted. The honest
assessment: the **call-boundary** retarget is mechanical; making the **whole** lowering
backend-agnostic (incl. opcode-level prefix runs) is a larger restructuring, because the
nested side has no opcode-level `runs_*` rules to offer.

### 4.2 Fallback (b): a proved behavioural equivalence `driveNested ≃ drive`

`docs/verifereum-nested-call.md` §E already recommends *against* reshaping `drive` and
*for* deferring any nested reformulation to "an optional, separate `driveNested` proved
equal to `drive`… strictly more work… only pursue if multiple downstream proofs start
re-deriving framing by hand." This report concurs, and sharpens what the equivalence
would actually require.

**At what observable granularity?** The right statement is **not** state-bisimulation
(the state types differ, §1.2) but **observable equivalence** through the shared
`Outcome`: for every call described in both worlds by corresponding `World` values,

```
observe_flat (messageCall p)  =  observe_nested (Θ (seedFuel…) … )
```

i.e. **same success/revert/exception, same return bytes, same storage delta** for every
top-level call. Gas-remaining and createdAccounts are deliberately outside the
granularity (they have width/encoding mismatches and the IR-v2 design already demotes gas
to internal bookkeeping — `EXPERIMENT-REPORT.md`, Track C-v2). Event/log trace *could* be
added if the substate's log list is projected identically (it is the same `Substate` type
modulo package).

**What the simulation relation would look like.** A relation `R : Frame⊕FrameResult →
EVM.State-tree → Prop` matching:

- a flat `running fr` whose `pending` stack has depth `n` ↔ a nested call-tree at depth
  `n` (flat's `List Pending` *is* the reified call stack that nested keeps implicitly in
  the Lean call stack of `Θ→Ξ→X→call→Θ`);
- flat's per-frame `exec : ExecutionState` ↔ the nested `X`-loop's `evmState`, field by
  field through the §1.2 rename table;
- flat's `Checkpoint` in `FrameKind.call` ↔ the nested `σ`/`A` snapshot that `Θ` restores
  on `z = false` (the rollback discipline matches — `docs/verifereum-nested-call.md` §B
  shows the nested commit/revert is `set_rollback snapshot`, flat's is the threaded
  `Checkpoint`).

The proof spine would be: a *step-correspondence* lemma (one flat `drive` iteration
advances `R` in lockstep with the nested engine's progress at the matching frame), lifted
over the recursion by fuel induction on the flat side and the `never_oof`-style mutual
induction on the nested side. The **hard part** is precisely the place where the two
models are most different: flat's `.needsCall`/`resumeAfterCall` *interleaves* parent and
child under one loop, whereas nested *returns a child tuple* — so the correspondence at a
CALL node must show that "flat pushes pending, drives the child to `.inr result`, then
`resumeAfterCall`" computes the **same** parent patch as "nested `Θ` returns `(σ', g', A',
z, o)` and `call` folds it in". This is the nested analogue of Track A's
`drive_descend_eq` lemma (which already proves the flat child-descent equals
`messageCall cp` on the child) — so **half the bridge already exists on the flat side**;
the equivalence would extend it to the nested `Θ` instead of the flat `messageCall`.

**Feasibility: a real, multi-week lift, and not on the critical path.** It needs the
nested side's gas/step lemmas (many of which `NeverOutOfFuel.lean` already proved as a
by-product — `gas_mono`, `step_depth`, the per-opcode `gas_EvmYul_step` sweep) plus a
full per-opcode correspondence between the two `step` functions, which are *separately
written* and only *intended* to agree. **Design judgment, flagged:** the equivalence is
the most intellectually satisfying outcome and the only one that would let the conformance
suite of *one* engine certify the *other*, but it is strictly dominated, for the immediate
IR-compiler goal, by fallback (a) + the observable interface. Pursue (b) only if a
downstream proof genuinely needs to transport a result proved in one engine into the
other.

---

## 5. Recommendation

A staged path, cheapest-first, each stage independently valuable:

1. **Build the observable `observe_nested` projection on the nested side** (small): split
   `Θ`'s output tuple on `z`, read storage via the shared `lookupStorage`, land in the
   existing `Outcome`. This is the keystone for everything else and is nearly mechanical
   because the storage lens is shared lineage (§3.2).
2. **Wrap `Θ` with a `seedFuel`-analogue and re-state `Θ_never_outOfFuel` fuel-free**
   (small): `runΘ w := Θ (fuelBound w.g w.e + 3) …`; then the never-OOF obligation reads
   like flat's. Gives the nested side a `messageCall`-shaped boundary.
3. **Define the polymorphic `EVMSemantics` structure (§3.1) at the observable level**, and
   instantiate it for both engines (flat trivially; nested from steps 1–2). **Do not**
   try to put the frame-level `Runs`/CFG rules in the interface — leave them
   exp003-specific (§3.4).
4. **Retarget Track C's call-boundary discharge to the abstract interface** (fallback a),
   so the IR lowering is certified against *any* conforming backend at the call boundary.
   Accept, for now, that the opcode-level prefix assembly stays flat-specific until/unless
   the nested side grows `runs_*`-style rules.
5. **Defer the full `driveNested ≃ drive` equivalence** (fallback b) unless a concrete
   downstream need arises; it is a large lift and the observable interface already
   delivers "interchangeable for IR reasoning."

This yields, mechanically and soon, the END GOAL's operative content — *the flat-vs-nested
choice becomes ergonomics-only for the IR compiler* — without paying for the full
behavioural-equivalence proof up front.

---

## 6. Where the two surfaces are MORE / LESS compatible than the END-GOAL framing assumes

**MORE compatible than assumed:**

- **The observable projection is nearly free**, because the storage lens
  (`Account.lookupStorage`) and `ToExecute`/`Substate`/`ExecutionEnv` are *shared
  lineage* — field-identical, same definitions, separately vendored. The END-GOAL framing
  treats "different `Outcome`/result encodings" as friction; in practice the *forgetful*
  observable (`success`/`output`/`storage`) lines up almost definitionally. (Caveat: only
  the *forgetful* part — see "LESS" below for gas.)
- **Both already have the never-OOF headline as a real theorem**, so the interface's
  hardest obligation is *discharged on both sides today* — the existence proof that "same
  result, two models" is achievable (§2).
- **The state records are renames of each other**, so the §4.2 simulation relation's
  *state* correspondence is bookkeeping, not invention.

**LESS compatible than assumed:**

- **There is no shared *type*.** `«evm»` and `«evmyul»` are distinct packages; the
  interface is *forced* to be state-polymorphic, and `gasAvailable`/`nonce` are genuinely
  `UInt64` vs `UInt256`. "Both instantiate the same typeclass over `State`" is not
  achievable; "over an abstract `World`/`Result`" is. The END-GOAL framing's "shared
  `EVMSemantics` interface both instantiate" is sound *only* read as state-polymorphic.
- **The nested side has no reasoning layer above `Θ` at all** (§1.3) — no `Runs`, no
  observables, no triple. The framing's "nested: textbook frame rule by construction"
  describes a *latent affordance*, not a built theorem; the flat side is currently the one
  with *more* shipped composition. Any interface that aspires to share the *frame-level*
  program logic is blocked until the nested side grows that layer.
- **The frame-level program-logic rules are not interface-able**, because their very
  statements mention flat-only structures (`Runs`/`Frame`/`stepFrame`). The shareable
  surface is strictly the observable level — narrower than "both prove the same theorems"
  reads at first glance.
- **Gas-remaining cannot be compared across the interface** without confronting the
  `UInt64`/`UInt256` width gap; the observable interface only works because it *drops*
  gas. An interface obligation that needed gas-equality would not type-check uniformly.

---

## 7. Open questions for Eduardo

1. **Interface altitude.** Confirm the shared `EVMSemantics` is **observable-level only**
   (run / observe / completedWith / neverOOF), with the frame-level `Runs`/CFG rules
   staying exp003-specific. This is the report's recommendation, but it is a design call:
   the alternative is to *invest in a `Runs`-analogue on the nested side* so the
   frame-level rules become shareable too (much larger; only worth it if you want the
   nested side as a first-class reasoning surface, not just a conformance mirror).
2. **`Adequate`/fuel in the interface.** Is folding nested's `fuelBound g e + 3 ≤ fuel ∧ e
   ≤ 1024` into the `World` bundle (so `run` is fuel-free and `neverOOF` is unconditional
   in the *interface's* eyes) acceptable — or do you want the fuel envelope visible at the
   interface so callers must reason about it? This decides whether flat and nested look
   *identical* at the boundary or merely *compatible*.
3. **Track C backend-agnosticism scope.** Retarget only the **call-boundary** discharge to
   the abstract interface (mechanical, recommended), or also the **opcode-level prefix
   assembly** (a larger restructuring, blocked on the nested side having no `runs_*`
   rules)? The former gives backend-swappability *at the call boundary* immediately; the
   latter is the fuller plug-and-play but needs nested-side reasoning machinery first.
4. **Equivalence granularity, if pursued.** If `driveNested ≃ drive` is ever wanted:
   storage-delta + halt-outcome + output only, or also the event/log trace (cheap to add,
   same `Substate`) and/or gas-remaining (expensive, width gap)? My recommendation:
   storage + outcome + output + logs; exclude gas.
5. **Is equivalence even a goal, or is the observable interface sufficient?** The report's
   position is that fallback (a) + the observable interface delivers the operative END
   GOAL (ergonomics-only choice) and that the full equivalence is a separate, optional,
   large investment justified only by a concrete need to transport one engine's
   conformance/results onto the other. Confirm whether you want the equivalence as a
   standing objective or as a contingency.
