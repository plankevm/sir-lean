# Experiment report — flat vs nested EVM semantics, and a verified IR lowering

**Status: LIVING DOCUMENT, updated as tracks land.** Operational state + milestones live
in `currentplan.md`; this file is the *results* synthesis for a human reader.

## The point of this experiment

We are building toward a **verified compiler** from a high-level IR to EVM bytecode. To do
that on solid ground we need a trustworthy EVM semantics and a reusable reasoning layer.
Two EVM semantics are in play, and the **end goal is to converge them** so we can pick
between them on merits, knowing they're equivalent:

- **Flat** — philogy's `EVMLean` (exp003): one tail-recursive `drive` over a shared
  pending stack, one fuel counter. Implementation-lineage (geth/revm-like). Trivial
  termination, fast; but proof compositionality (frame rule, per-call triple) must be
  *earned* as theorems.
- **Nested** — `EVMYulLean` with Yul stripped (exp004): Yellow-Paper `Θ/Ξ` mutual
  recursion, a child call is an honest subterm. Spec-lineage; compositional by
  construction; heavier termination (fuel-passing mutual recursion).

**Convergence (Phase 2):** a shared `EVMSemantics` interface (Lean type class/structure)
both instantiate with the same theorems, and/or a proved behavioural equivalence. Then the
flat-vs-nested choice is purely about ergonomics/conformance, not correctness.

## Tracks and their reports

| Track | What | Per-track report | Status |
|---|---|---|---|
| **A** | exp003 flat reasoning layer: `Runs` with a `call` constructor, multi-call composition, CFG combinator, opcode rules | `experiments/003_bytecode_layer/docs/track-a-review.md` *(pending: generated after opcode-rules + A→base merge)* | A1/A2/A3/CFG green; opcode rules in progress |
| **B** | exp004 nested EVM core: EVMYulLean monomorphized to EVM-only, nested never-`OutOfFuel`, `Ξ`-triple | `experiments/004_nested_evmyul/docs/track-b-review.md` *(pending: after B2)* | B0 (mono) green; B2 in progress |
| **C** | exp005 `LirLean` IR → bytecode lowering + semantics preservation | `experiments/005_ir_lowering/docs/track-c-review.md` *(pending: after C3)* | C1/C2 green; C3 gated on A→base merge |

Each per-track report argues the design decisions + alternatives — notably **why `call` is
a `Runs` constructor** (it's what makes the regular-language multi-call composition work)
and **why the CFG-combinator control-flow design** was chosen over alternatives.

## Results so far (synthesis — fill as tracks land)

- **The intermediary-call defect is FIXED (Track A).** exp003's old bridge could express
  only one call between a prefix and a halting suffix; making `call` a `Runs` constructor
  turned multi-call programs into ordinary `Runs.trans` composition, with NO new proof
  obligation (the index-free `drive_reconcile` already inducts through call nodes).
- **Full EVM-only nested semantics exists (Track B).** EVMYulLean's `Yul | EVM`
  polymorphism is entirely removed; the nested `Θ/Ξ` is plain EVM — the clean base for the
  bake-off and convergence.
- *(more as B2 / C3 / Phase 2 land)*

## What this means for how we proceed

*(synthesis written when the tracks mature — the flat-vs-nested verdict, the convergence
plan, and the path to lowering Plank SIR.)*
