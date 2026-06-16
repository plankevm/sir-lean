# Review — `messageCall` never returns `OutOfFuel` (unconditional)

*Review report for the project lead. Read-only on code; grounds every claim in
the actual `.lean`. Specs are quoted verbatim; proof bodies are never pasted.*

---

## TL;DR

The headline result is **proven and unconditional**:

```lean
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel :=
  messageCall_never_outOfFuel_of_descentDrops descentDrops_holds p
```
([`DescentDrops.lean#L1516`](../BytecodeLayer/Proof/DescentDrops.lean#L1516))

For **every** `CallParams` `p` — any program, any gas, **no termination /
budget / call-free hypothesis** — a top-level message call never produces the
`OutOfFuel` error. The earlier `HaltsWithinBudget`-gated and `NeverDescends`-gated
versions are no longer on the critical path.

- **Status: fully closed.** Zero `sorry`/`admit`/`native_decide`/`bv_decide` in
  `BytecodeLayer/` (verified by grep; the single textual hit is the word
  "sorry" inside a comment in [`Maps.lean#L11`](../BytecodeLayer/Reasoning/Maps.lean#L11)).
- **Build/axioms:** reported green (1126 jobs) and axiom-clean
  `[propext, Classical.choice, Quot.sound]` per [`docs/handoff.md`](handoff.md#L4)
  / [`docs/results.md`](results.md#L3). *Reported, not re-run this session* (a
  full `lake build` was intentionally not invoked).

The three questions the lead asked are answered in **§7 (dependency vs
supersession)**, **§5 (hypotheses & modeling)**, and **§6 (`NeverDescends`)**.

---

## 1. Goal & context

`drive` ([`Interpreter.lean#L36`](../../../forks/leanevm/Evm/Semantics/Interpreter.lean#L36))
is leanevm's CPS interpreter loop. It is structurally recursive on a `fuel : ℕ`
counter:

```lean
def drive (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) :
    Except ExecutionException FrameResult :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 => …
```

That `fuel` is a **proof artifact** — Lean needs a decreasing measure to accept
the definition; the EVM itself has no such counter. `OutOfFuel` is therefore a
"the model gave up" error that must **never** be a real program behavior. The
top-level entry point seeds the counter with

```lean
def seedFuel (gas : UInt64) : ℕ := 2 * gas.toNat + 4096
```
([`Interpreter.lean#L82`](../../../forks/leanevm/Evm/Semantics/Interpreter.lean#L82))

```lean
def messageCall (params : CallParams) : Except ExecutionException CallResult :=
  match beginCall params with
    | .inr result => .ok result
    | .inl frame => FrameResult.toCallResult <$> drive (seedFuel params.gas) [] (.inl frame)
```
([`Interpreter.lean#L84`](../../../forks/leanevm/Evm/Semantics/Interpreter.lean#L84))

The real-world property: **out-of-gas is itself a halt**, so the number of
`drive` recursions is bounded by the gas; `seedFuel gas = 2·gas + 4096`
overshoots that bound, so the counter never reaches `0`. Establishing this turns
`OutOfFuel` from "possible model artifact" into "provably dead branch," which is
what makes the whole reasoning layer trustworthy.

---

## 2. Abstraction levels / structure

Four layers, bottom-up, each closed before the next builds on it (matching the
[proof-first / always-green discipline](proof-structure.md#L22)):

| Layer | Module | Role |
|---|---|---|
| per-step gas burn | [`Reasoning/StepGas.lean`](../BytecodeLayer/Reasoning/StepGas.lean) (+ `StepGasBasics.lean`) | `stepFrame_next_lt`: every non-`System` `.next` step strictly burns gas, via the `charge`-bind chokepoint |
| fuel plumbing | [`Reasoning/Fuel.lean`](../BytecodeLayer/Reasoning/Fuel.lean) | `drive` fuel monotonicity |
| measure framework | [`Reasoning/NeverOutOfFuel.lean`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean) | `totalGas`/`μ`, the call-free corollary, the **general** `mu_bound` skeleton modulo `DescentDrops`, and the boundary theorem `messageCall_never_outOfFuel_of_descentDrops` |
| descent arithmetic | [`Proof/DescentDrops.lean`](../BytecodeLayer/Proof/DescentDrops.lean) | discharges `DescentDrops` and exposes the unconditional `messageCall_never_outOfFuel` |

The split that matters: **`mu_bound` is the engine, `DescentDrops` is its single
remaining input.** `NeverOutOfFuel.lean` proves "if the descent/fallback steps
drop the measure, the driver never starves" *abstractly* (the `DescentDrops`
hypothesis), and `DescentDrops.lean` then proves that hypothesis from the
leanevm `callArm`/`createArm` gas arithmetic. This is a clean
parameterize-then-discharge pattern.

---

## 3. The specs that matter

### The measure

```lean
def activeGas : (Frame ⊕ FrameResult) → ℕ
  | .inl fr => fr.exec.gasAvailable.toNat
  | .inr r  => FrameResult.gasRemaining r

def totalGas (stack : List Pending) (state : Frame ⊕ FrameResult) : ℕ :=
  activeGas state + (stack.map Pending.savedGas).sum

def μ (stack : List Pending) (state : Frame ⊕ FrameResult) : ℕ :=
  2 * totalGas stack state + 2 * stack.length + tagBit state
```
([`NeverOutOfFuel.lean#L69`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L69),
[`#L74`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L74),
[`#L87`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L87))

`μ` sums gas held by the active component *and every suspended parent*, scaled by
2, plus `2·stack.length` (each descent/return moves the stack and must still be
covered), plus a `tagBit` of `2` (running frame) or `1` (finished result). The
gap in `tagBit` ([`#L79`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L79))
exists so the `.inl → .inr` *halt delivery* step — which leaves gas and stack
untouched — still drops `μ` by 1. **Claim:** `μ` strictly decreases on *every*
`drive` recursion and starts below `seedFuel`.

### The general engine

```lean
theorem mu_bound (hd : DescentDrops) :
    ∀ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult),
      μ stack state ≤ f → drive f stack state ≠ .error .OutOfFuel
```
([`NeverOutOfFuel.lean#L848`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L848))

Plain English: if the fuel `f` is at least the measure `μ`, `drive` cannot
return `OutOfFuel`. Induction on `f`; every branch of `drive` is shown to either
finish or recurse on a state with strictly smaller `μ` (≤ `f - 1`). Obligations
1, 2, 6, 7 are discharged inline; the descent/fallback decreases are exactly the
hypothesis `DescentDrops`.

### The boundary theorem (modulo `DescentDrops`)

```lean
theorem messageCall_never_outOfFuel_of_descentDrops (hd : DescentDrops) (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel
```
([`NeverOutOfFuel.lean#L970`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L970))

It instantiates `mu_bound` at `f := seedFuel p.gas`, `stack := []`, the initial
frame, using `μ [] (.inl frame) = 2·p.gas.toNat + 2 ≤ seedFuel p.gas`.

### `DescentDrops` — the one input

```lean
def DescentDrops : Prop :=
  -- (3) System `.next` fallback: totalGas drops ≥ 1
  (∀ (fr) (exec') (stack), stepFrame fr = .next exec' →
      (∃ s, (decode … |>.getD (Operation.STOP, .none)).1 = .System s) →
      totalGas stack (.inl { fr with exec := exec' }) < totalGas stack (.inl fr))
  ∧ -- (4) needsCall descent into a code child
  (∀ (fr) (params) (pending) (child) (stack),
      stepFrame fr = .needsCall params pending → beginCall params = .inl child →
      activeGas (.inl child) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (5a) needsCall precompile (immediate result)
  (… FrameResult.gasRemaining (.call result) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (4') needsCreate descent into a child
  (… activeGas (.inl child) + Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (5b) needsCreate failure (zeroed result)
  (… Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr))
```
([`NeverOutOfFuel.lean#L822`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L822))

Five per-transition inequalities, one per non-trivial `drive` branch that
descends or falls back. Each says "the gas that re-enters the measure after the
transition, plus the `+2` slack the measure needs, is covered by the gas before
it." Discharged as `descentDrops_holds`
([`DescentDrops.lean#L1508`](../BytecodeLayer/Proof/DescentDrops.lean#L1508)).

### The per-step gas-burn foundation

```lean
theorem stepFrame_next_lt {fr : Frame} {exec' : ExecutionState}
    (hne : ∀ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none)).1 ≠ .System s)
    (h : stepFrame fr = .next exec') :
    exec'.gasAvailable.toNat < fr.exec.gasAvailable.toNat
```
([`StepGas.lean#L509`](../BytecodeLayer/Reasoning/StepGas.lean#L509))

Every non-`System` opcode that continues (`.next`) strictly burns gas. The
chokepoint is `chargeBind_lt`
([`StepGas.lean#L72`](../BytecodeLayer/Reasoning/StepGas.lean#L72)): a `.next`
from such an op is always the output of a final `charge cost` with `cost ≥ 1`
(memory expansion only lowers gas; post-charge continuations only reshuffle
stack/pc/state). `System` ops are excluded on purpose — their `.next` *fallbacks*
set gas via `resume…`, not a final `charge`, and are handled by `DescentDrops`
conjunct (3).

---

## 4. The two call-free specs (now off the critical path)

```lean
theorem messageCall_callFree_never_outOfFuel (hnd : NeverDescends) (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel
```
([`NeverOutOfFuel.lean#L792`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L792))

```lean
theorem drive_callFree_aux (hnd : NeverDescends) :
    ∀ (f : ℕ) (fr : Frame), 2 * fr.exec.gasAvailable.toNat + 2 ≤ f →
      drive f [] (.inl fr) ≠ .error .OutOfFuel
```
([`NeverOutOfFuel.lean#L752`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L752))

These are the earlier, **hypothesis-gated** rung. They run the same measure
argument but over a *permanently empty* pending stack, so `μ` collapses to
`2·gas + 2`. They require `NeverDescends` (see §6) and never touch the
descent/delivery arithmetic. See §7 for the supersession verdict.

---

## 5. Hypotheses & modeling

### Headline theorem — *no hypotheses*

`messageCall_never_outOfFuel (p : CallParams)` takes only the call params. No
termination, no budget, no call-free assumption, no `Frame`/fuel in the
statement. This is the clean win over the discarded `HaltsWithinBudget`-gated
attempt: that earlier hypothesis effectively smuggled the conclusion in
(assuming the run halts in budget to prove it never starves), which the lead
correctly flagged as a fake. The current statement assumes nothing.

`messageCall_never_outOfFuel_of_descentDrops` and `mu_bound` carry the single
hypothesis `DescentDrops`, which is then **discharged unconditionally** — so it
is an internal staging device, not a residual assumption of the headline.

### How the world/run is modeled

A `drive` configuration is `(stack : List Pending, state : Frame ⊕ FrameResult)`:
the active running frame or finished result, plus the stack of suspended parents
awaiting a child's return. The measure `μ` (§3) is the proof's model of "work
left." The subtle modeling decisions:

**`seedFuel gas = 2·gas + 4096`.** The factor 2 covers the `tagBit`/`+2`-slack
doubling in `μ`; the `+4096` constant covers zero-gas edge cases (e.g. an empty
program still takes a halt step at gas 0). Generous by design — the proof never
needs tightness.

**The kind-aware `Pending.savedGas` (the heart of the modeling).**

```lean
def Pending.savedGas : Pending → ℕ
  | .call pd   => pd.frame.exec.gasAvailable.toNat
  | .create pd => pd.frame.exec.gasAvailable.toNat
                    - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat
```
([`NeverOutOfFuel.lean#L63`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L63))

This asymmetry is **load-bearing and correct**, and it directly mirrors a real
asymmetry in leanevm's two descent arms:

- `callArm` **debits the parent** `gasCap + extraCost` *before* saving it
  ([`System.lean`](../../../forks/leanevm/Evm/Semantics/System.lean), the
  `charge (gasCap + extraCost) e1` step). The saved gas is genuinely "the
  parent's own," so for a CALL parent `savedGas` is the full saved
  `gasAvailable`.
- `createArm` saves the parent **undebited** — `{ fr with exec := exec }` at
  [`System.lean#L84`](../../../forks/leanevm/Evm/Semantics/System.lean#L84) —
  *while forwarding* `allButOneSixtyFourth exec.gas` to the child
  ([`#L112`](../../../forks/leanevm/Evm/Semantics/System.lean#L112)). The
  forwarded portion is therefore counted **twice** if measured naïvely: once in
  the child's `activeGas`, once in the parent's full saved gas.

The fix: for a CREATE parent, `savedGas` **withholds the forwarded
`allButOneSixtyFourth`** from the measure, exactly cancelling the double-count
during an open CREATE descent. On delivery, `resumeAfterCreate` returns that
lent part to the parent — and the measure's bookkeeping is reconciled by the
*tight* delivery bound

```lean
theorem resumeAfterCreate_gas_le_savedGas {result} {pd} {parent}
    (h : resumeAfterCreate result pd = .ok parent) :
    parent.exec.gasAvailable.toNat
      ≤ (pd.frame.exec.gasAvailable.toNat
          - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat)
        + result.gasRemaining.toNat
```
([`NeverOutOfFuel.lean#L600`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L600)),

which `mu_bound` uses in its create-resume case
([`#L885`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L885)). This is the
single most thoughtful piece of the modeling: the kind tag on `Pending` is not
cosmetic — it is what makes the create descent conserve the measure rather than
inflate it. The module note at
[`DescentDrops.lean#L1461`](../BytecodeLayer/Proof/DescentDrops.lean#L1461)
spells out the `g + 2 ≤ activeGas (.inl fr)` collapse this enables.

The `+2` slack in every `DescentDrops` conjunct is comfortably covered because
the call/create's *own* (non-forwarded) cost is a positive constant far larger
than 2: `callExtraCost ≥ 100` (warm access) or `≥ 9000` (value transfer); CREATE
pays `createCost ≥ Gcreate = 32000`. These bounds are proven generously in
[`callExtraCost_ge_100`](../BytecodeLayer/Proof/DescentDrops.lean#L38),
[`callExtraCost_ge_9000_of_val`](../BytecodeLayer/Proof/DescentDrops.lean#L49),
[`createCost_ge_2`](../BytecodeLayer/Proof/DescentDrops.lean#L625) — "the call's
own cost is bigger than 2 (resp. 2302)" is the entire arithmetic; nothing tight.

---

## 6. The `NeverDescends` hypothesis (Q3)

This is the lengthy call-free hypothesis the lead found off-putting. Verbatim:

```lean
def NeverDescends : Prop :=
  ∀ fr : Frame,
    (∀ exec', stepFrame fr = .next exec' →
      ∀ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 ≠ .System s)
    ∧ (∀ p pd, stepFrame fr ≠ .needsCall p pd)
    ∧ (∀ p pd, stepFrame fr ≠ .needsCreate p pd)
```
([`NeverOutOfFuel.lean#L741`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L741))

**In plain English:** for *every* frame `fr` reachable in the run,
1. whenever the step continues (`.next`), the decoded opcode is **not** a
   `System` op (so the strict gas-burn lemma `stepFrame_next_lt` applies); and
2. the step is **never** a `.needsCall`; and
3. the step is **never** a `.needsCreate`.

I.e. the program never descends into a child call/create — the pending stack
stays empty forever, so `μ` collapses to `2·gas + 2` and the whole
descent/delivery arithmetic is unnecessary.

**Why it was needed for the call-free argument.** `drive_callFree_aux` only knows
how to handle `.next` (gas drops) and `.halted` (delivery through the empty
stack). It has no story for `.needsCall`/`.needsCreate`, so it must *assume* they
never occur. That is precisely `NeverDescends`. The intended discharge for a
concrete program is a static "no CALL/CREATE opcode in the bytecode" check —
`CallFreeCode` ([`#L635`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L635))
plus `callFree_next_nonSystem`
([`#L690`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L690)) are the bridge —
but that discharge is left to the caller and is not done in-tree.

**The off-putting part is real:** `NeverDescends` is a `∀`-over-every-`Frame`
hypothesis that quantifies over the execution trace and bakes in a whole-program
structural assumption. It is genuinely load-bearing *for the call-free rung* (it
is not smuggling the conclusion — it is a stronger antecedent), but it is exactly
the kind of trace-shaped hypothesis a skeptical reviewer dislikes.

**The unconditional general theorem eliminates it entirely.**
`messageCall_never_outOfFuel` handles `.needsCall`/`.needsCreate` directly via
`DescentDrops`, so it needs no assumption about whether the program descends.
`NeverDescends` does not appear anywhere in the headline's dependency chain.

---

## 7. Dependency vs supersession of the call-free theorem (Q1)

**Concrete finding: independent supersession, not reuse.** I traced both chains:

- General: `messageCall_never_outOfFuel` →
  `messageCall_never_outOfFuel_of_descentDrops` (via `descentDrops_holds`) →
  `mu_bound` → (`stepFrame_next_lt`, `endFrame_gasRemaining_le`,
  `resumeAfterCall_gas_le`, `resumeAfterCreate_gas_le_savedGas`, the five
  `descentDrops_conj*`). **It never mentions `drive_callFree_aux`,
  `NeverDescends`, `CallFreeCode`, or `messageCall_callFree_never_outOfFuel`.**
- Call-free: `messageCall_callFree_never_outOfFuel` → `drive_callFree_aux`
  (under `NeverDescends`). A **separate** induction over the empty stack.

The two share only the leaf lemmas (`stepFrame_next_lt`,
`endFrame_gasRemaining_le`) and the `μ`/`totalGas`/`seedFuel` definitions — the
*inductive skeleton* is duplicated, not reused.

Since `messageCall_never_outOfFuel` is unconditional, it **logically implies**
`messageCall_callFree_never_outOfFuel` for free (the call-free statement is just
the same goal under an extra unused hypothesis). So the call-free theorem is now
**redundant** as a result.

**Dead-code check (grep over `BytecodeLayer/**.lean`, excluding `.lake` build
artifacts):** `messageCall_callFree_never_outOfFuel`, `drive_callFree_aux`,
`NeverDescends`, `CallFreeCode`, and `callFree_next_nonSystem` are referenced
**only within their own defining file** (`NeverOutOfFuel.lean`). No downstream
module consumes any of them. They are an isolated, self-contained island.

**Recommendation (do not apply):**
- Keep **one** headline theorem: the unconditional `messageCall_never_outOfFuel`.
- The call-free block (`NeverDescends`, `CallFreeCode`, `callFree_next_nonSystem`,
  `drive_callFree_aux`, `messageCall_callFree_never_outOfFuel`,
  `haltOp_not_next`) is now dead weight. Options:
  1. **Delete it** — cleanest; the general theorem covers it.
  2. **Demote** `messageCall_callFree_never_outOfFuel` to a one-line corollary of
     the unconditional theorem (drop the `NeverDescends` arg) and delete
     `drive_callFree_aux` + the `CallFree*` plumbing, if a call-free-labelled
     statement is wanted for documentation.
  Option 1 is preferable unless the call-free framing has external value. Either
  way, the duplicated empty-stack induction should not be maintained alongside
  `mu_bound`.

---

## 8. Proof structure (brief)

One line per headline, with a trust note:

- **`stepFrame_next_lt`** — per-opcode case split (10 constructor classes) onto a
  single `charge`-bind chokepoint `chargeBind_lt`; each class reduces to a proven
  helper. Mechanical and trustworthy; `maxHeartbeats 1000000` on `dispatch_next_lt`
  is the only heavy spot.
- **`mu_bound`** — induction on fuel `f`; per-branch `μ`-decrease closed by
  `omega` after unfolding `μ`/`totalGas`. The skeleton is small and readable.
- **`DescentDrops` conjuncts** — `systemOp`/`stepFrame` inversion onto
  `callArm`/`createArm`, then `omega` against the generous cost lower bounds.
  Long but routine (the bulk of `DescentDrops.lean` is `neverHalts`/`onlyNext`
  signal-shape bookkeeping per opcode).
- **`messageCall_never_outOfFuel`** — a single `def`-unfold composition
  (`messageCall_never_outOfFuel_of_descentDrops descentDrops_holds`). Trivial.

No `sorry`/`admit`/`native_decide`/`bv_decide` anywhere in scope (verified).
Axiom-cleanliness and green build are **reported** (`docs/handoff.md`,
`docs/results.md`), not re-run this session.

---

## 9. Redundancy & recommendations

1. **Consolidate to one theorem.** As §7: drop or demote the entire call-free
   island; `messageCall_never_outOfFuel` subsumes it. Highest-value cleanup.
2. **`resumeAfterCreate_gas_le` vs `resumeAfterCreate_gas_le_savedGas`.** The
   non-tight `resumeAfterCreate_gas_le`
   ([`#L577`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L577)) is used only
   by `callArm_next_gas` ([`DescentDrops.lean#L246`](../BytecodeLayer/Proof/DescentDrops.lean#L246)),
   while the tight `_savedGas` variant
   ([`#L600`](../BytecodeLayer/Reasoning/NeverOutOfFuel.lean#L600)) is what
   `mu_bound`'s create-resume case needs. Both are genuinely used — not
   redundant — but worth a comment cross-linking why two bounds coexist (one is
   the loose `≤ saved + child`, one withholds `allButOneSixtyFourth`).
3. **Docstring vs source — no discrepancies found.** The `NeverOutOfFuel.lean`
   header (lines 19–40) still describes the call-free rung as a live "Fully
   proven" item and `DescentDrops` as "the remaining work," language that
   predates the unconditional close. It is not *wrong* (those statements are all
   proven), but it under-sells that `DescentDrops` is now fully discharged and
   over-emphasizes the superseded call-free rung. Recommend trimming the header
   once the call-free island is removed. The `DescentDrops.lean` header (lines
   12–15) correctly states the result is unconditional.

---

## 10. Honest rough edges & open questions

- **Build not re-verified this session.** Green/1126-jobs/axiom-clean is cited
  from `docs/handoff.md` and `docs/results.md`, not from a fresh `lake build`.
- **`CallFreeCode`'s static discharge is not in-tree.** The call-free rung's
  intended escape hatch (turn a no-CALL/CREATE-opcode bytecode check into
  `NeverDescends`) is stated but never instantiated for a concrete program.
  Moot if the call-free island is deleted per §7/§9.
- **`seedFuel`/`μ` constants are deliberately loose.** `+4096` and the `×2`
  factor are over-provisioned; fine for the existential "never starves," but the
  proof says nothing tight about *how close* to starvation a run can get (nor
  should it need to).
- **`DescentDrops.lean` is large and repetitive.** The per-opcode `neverHalts` /
  `onlyNext` / `*_never_needsCall` / `*_never_needsCreate` families are
  near-identical boilerplate driven by signal shapes; not a soundness concern,
  but a maintenance surface (~1500 lines for what is conceptually five
  inequalities).
