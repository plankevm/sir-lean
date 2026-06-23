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
| **A** | exp003 flat reasoning layer: `Runs` with a `call` constructor, multi-call composition, CFG combinator, opcode rules | **[track-a-review.md](experiments/003_bytecode_layer/docs/track-a-review.md)** ✓ | **Core complete + merged to base** (1130 jobs, axiom-clean). Backlog: gas-introspection, `CREATE`, symbolic worlds |
| **B** | exp004 nested EVM core: EVMYulLean monomorphized to EVM-only, nested never-`OutOfFuel`, `Ξ`-triple | `experiments/004_nested_evmyul/docs/track-b-review.md` *(pending: after the nested headline closes)* | B0 (mono) green; **non-nesting leaf** never-`OutOfFuel` CLOSED + axiom-clean; all CALL **and** CREATE gas-descent bricks proved; **fully-nested headline `Θ_never_outOfFuel` — final mutual-induction assembly in progress** (4 partials; CREATE de-risk passed) |
| **C** | exp005 `LirLean` IR → bytecode lowering + semantics preservation | **[track-c-review.md](experiments/005_ir_lowering/docs/track-c-review.md)** ✓ *(refreshed to the hypothesis-free state, on `exp005-ir`)* | **DONE + merged to base.** `wc_preserves` is FULLY hypothesis-free + axiom-clean — a complete verified IR→bytecode lowering through an external CALL (only a gas knob `g ≥ 50000`). `wc_preserves_twoCall` is a generic multi-call shape lemma (all pieces proved). **A v2 redesign is now planned** (see below) |

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
- **Verified IR→bytecode lowering, hypothesis-free (Track C).** `wc_preserves` proves the
  lowered `workedCall` program's `messageCall` delivers the expected result — through an
  external CALL, a storage write, arithmetic, and a gas-dependent branch — depending only
  on a gas knob, axiom-clean. Multi-call composition needed ZERO new theory (Track A's
  `Runs.call` composes calls) — the end-to-end payoff of the `Runs.call` design bet.
- **Bake-off data point (Track B finding).** Nested never-`OutOfFuel` needs a **depth-aware,
  SUPER-LINEAR** fuel bound (`B (k+1) g = (g+1)·(B k g + c) + 2`, `k = 1025−depth`,
  i.e. `~(g+1)^(1025−depth)`) — because each frame's gas loop can spawn a child needing its
  own full budget. Flat (exp003) gets a clean linear `≈2·gas+c`. This is a concrete
  termination-simplicity advantage for the flat model. (Bound size is irrelevant to the
  theorem — fuel is a proof device — but it signals proof-engineering cost.) The non-nesting
  fragment is closed unconditionally; the fully-nested headline assembly is in flight.
- **Track C v2 reformulation — DESIGNED (`exp005-ir`).** Driven by Eduardo: the IR
  semantics should not be gas- or call-aware. Plan in
  **[ir-design-v2.md](experiments/005_ir_lowering/docs/ir-design-v2.md)**: an abstract,
  gas-free, pc-free IR machine; external calls modeled as **trace events** ("whatever the
  bytecode does", CompCert-style — not an oracle, no refinement obligation); preservation
  stated on **observables** (storage delta + halt result + event trace); gas/pc demoted
  from preserved invariants to *internal* bookkeeping inside the `Runs` witness, with a
  single caller-local "enough gas" adequacy envelope. Gas introspection is **kept**, modeled
  as a **monotone oracle** (`gasRead` event whose only law is non-increasing) — introspection
  without opcode-cost accounting. A call-free prototype is being proved now to validate the
  shape before porting `workedCall`.
- **Prior-art study — gas introspection.**
  **[gas-introspection-prior-art.md](experiments/005_ir_lowering/docs/gas-introspection-prior-art.md)**:
  both verifereum/vyper-hol and lfglabs-dev/verity keep their high-level semantics gas-free,
  state preservation over observables, and reconcile gas via a single "enough gas" envelope
  (vyper-hol's `codegen_fn_correct = ∃ gas_needed, …` is almost verbatim our v2 shape) —
  **strong independent validation of the v2 spine.** Crucially, **neither supports gas
  introspection** (both list it as future work); our monotone-oracle treatment is a genuine
  extension, not a port.
- *(more as the nested headline closes / the C-v2 prototype lands / Phase 2 begins)*

## What this means for how we proceed

*(synthesis written when the tracks mature — the flat-vs-nested verdict, the convergence
plan, and the path to lowering Plank SIR. Early signal: flat's linear fuel bound vs nested's
super-linear one is a real ergonomics point for the bake-off; the C-v2 observable/event
boundary is a candidate shared surface for Phase-2 convergence.)*
