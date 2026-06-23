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
| **B** | exp004 nested EVM core: EVMYulLean monomorphized to EVM-only, nested never-`OutOfFuel`, `Ξ`-triple | `experiments/004_nested_evmyul/docs/track-b-review.md` *(pending)* | B0 (mono) green; **fully-nested headline `Θ_never_outOfFuel` CLOSED + axiom-clean** (`exp004-nested`) — the 5-layer never-`OutOfFuel` mutual induction over `Θ/Ξ/X/step/call`, plus the `gas_mono` mutual induction and a ~250-line `step`/`Z` depth-preservation keystone, all proved + independently verified. Fuel bound is **LINEAR-PRODUCT** `B(g,e)=(1025−e)·(g+c)` (depth factor; linear in gas) — the earlier *super-linear* estimate was wrong. |
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
- **Bake-off data point (Track B finding) — CORRECTED + CLOSED.** Nested never-`OutOfFuel`
  `Θ_never_outOfFuel` is **proved, axiom-clean**, with a depth-aware **LINEAR-PRODUCT** fuel
  bound `B(g,e) = (1025−e)·(g+c)` — linear in gas, with a depth *factor*. (The earlier
  *super-linear* `~(g+1)^(1025−depth)` estimate was a mistake: it assumed a frame's `g`
  child-calls accumulate budget, but fuel is a **pass-by-value structural counter** — the
  parent loop resumes at the same `f` regardless of child consumption — so the binding
  constraint is the single worst loop iteration, not the sum.) Flat (exp003) still gets a
  cleaner *unconditional* linear `≈2·gas+c` with one mutual induction; nested needs a depth
  term + **two** mutual inductions (`gas_mono`, `never_oof`) + a ~250-line depth-preservation
  keystone + precompile plumbing. So the flat model keeps a real termination-ergonomics
  advantage — but milder than first thought, and the nested headline *does* close.
- **Track C v2 reformulation — DESIGNED (`exp005-ir`).** Driven by Eduardo: the IR
  semantics should not be gas- or call-aware. Plan in
  **[ir-design-v2.md](experiments/005_ir_lowering/docs/ir-design-v2.md)**: an abstract,
  gas-free, pc-free IR machine; external calls modeled as **trace events** ("whatever the
  bytecode does", CompCert-style — not an oracle, no refinement obligation); preservation
  stated on **observables** (storage delta + halt result + event trace); gas/pc demoted
  from preserved invariants to *internal* bookkeeping inside the `Runs` witness, with a
  single caller-local "enough gas" adequacy envelope. Gas introspection is **kept**, modeled
  as a **monotone oracle** (`gasRead` event whose only law is non-increasing) — introspection
  without opcode-cost accounting. **The call-free prototype is DONE and axiom-clean** — the
  gas-free + observable + event shape is validated (`lower_preserves_obs`, pc-free &
  gas-equality-free); gas introspection cost zero gas machinery. The **two-read monotonicity
  milestone is also DONE** (axiom-clean) — the monotone-oracle law validated on a sticky
  gas-guard, monotonicity *discharged* from exact gas accounting with no new gas theory.
  The general `Runs`-level **gas-monotonicity-across-calls lemma is now PROVED**
  (`Runs.gasAvailable_le`, hypothesis-free incl. the `.call` 63/64 net-debit), closing
  §3.4's last open obligation. The `call`-event step (and the general theorem) is held
  pending your returndata-model decision (`ir-design-v2.md §7.5`).
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
plan, and the path to lowering Plank SIR. Early signal: flat's clean unconditional linear
fuel bound vs nested's depth-factored linear-product one (both linear in gas; nested needs two
mutual inductions + a depth-preservation keystone) is a real but moderate ergonomics point for
the bake-off; the C-v2 observable/event boundary is a candidate shared surface for Phase-2
convergence.)*

**Sharpening (2026-06-23, updated after the nested headline CLOSED):** the bake-off
asymmetry is real but **milder than the overnight estimate**. Flat (exp003) proved
`messageCall_never_outOfFuel` **unconditionally, with a clean linear bound** in one mutual
induction. Nested (exp004) is **now also closed** — `Θ_never_outOfFuel`, axiom-clean — but
cost ~7 brick/assembly iterations: a library of gas-descent + gas-monotonicity bricks, a
`gas_mono` mutual induction, a ~250-line `step`/`Z` **depth-preservation keystone** (the
`fuelBound` depth index must be a sound loop invariant), the `never_oof` 5-layer mutual
induction, and precompile plumbing. The fuel bound is **LINEAR-PRODUCT**
`B(g,e)=(1025−e)·(g+c)` — linear in gas with a depth *factor*, **not** the super-linear
`~(g+1)^(1025−depth)` the overnight runs guessed (that estimate wrongly assumed children
accumulate budget; pass-by-value fuel means the worst single iteration binds). Net: a concrete
termination-ergonomics advantage for the flat foundation (fewer inductions, no depth term,
unconditional) — but the nested model is **fully mechanizable** for this property, and the gap
is mechanization cost, not a complexity-class blowup.
