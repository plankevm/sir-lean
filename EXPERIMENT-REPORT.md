# Experiment report — flat vs nested EVM semantics, and a verified IR lowering

**Status: LIVING DOCUMENT, updated as tracks land.** Operational state + milestones live
in `currentplan.md`; this file is the *results* synthesis for a human reader.

> **UPDATE (2026-07-03).** exp005 (Track C) — waves 1–4 of the honesty cleanup executed the
> structural reorg (HEAD `53c2063`); the Lean file homes cited below have MOVED (redirect map:
> `experiments/005_ir_lowering/docs/headline-transitive-chain.md`):
> (a) `LirLean/Spec/{IR,Semantics,Lowering,Recorder,Seams,Conformance}` extraction;
> (b) `experiments/003_bytecode_layer/BytecodeLayer/Hoare/*` + `LirLean/Drive/{SelfPresent,CallPreservesSelf,Headline}` split,
> `TieDischarge.lean` **DISSOLVED** (headline → `LirLean/Drive/Headline.lean`) and
> `RunLog.lean` **deleted** (recorder → `LirLean/Spec/Recorder.lean`); (c) Phase-2
> **deletion** of `{Mono,Oracle,HonestGasTie}.lean` + the gas-monotonicity law;
> (d) `LirLean/Audit.lean` guard net + `LirLean/RealisabilitySpec.lean` (`Nightly` lib) R0–R12
> sorry-skeleton. Plan-of-record: `experiments/005_ir_lowering/docs/target-architecture-2026-07-02.md`
> + `execution-plan-2026-07-02.md` (remediation plan superseded); the final audit fleet
> (`experiments/005_ir_lowering/docs/final-audit-2026-07-03.md`, being written) gates Phase 3.
>
> **CORRECTION (2026-07-03, later).** The banner above says the headline was moved to
> `LirLean/Drive/Headline.lean`. That relocation was **undone**: in commits "delete vacuous
> conformance surface 1/4..4/4" the vacuous headline `lower_conforms_cyclic_assembled` and the whole
> vacuous apparatus (`_tiefree`, `lower_conforms_wf`, the `lower_conforms_acyclic*` family,
> `StmtTies`/`TermTies`, the Plus assembly, and the `Spec` re-export layer) were **DELETED**, not
> moved. `LirLean/RealisabilitySpec.lean` (Nightly, R0–R12; ties DERIVED from the run) is now the
> **sole conformance surface**; the `Lir.DriveCorrPlus` structure and the value/gas channels in
> `Drive/Headline.lean` are retained as Phase-3 salvage (unreferenced in the default build). The
> table row / narrative below still name `lower_conforms_cyclic_assembled` as "the current headline"
> — read that as **historical**.
>
> **PHASE 3 (2026-07-04).** Final audit CLEAN (`docs/final-audit-2026-07-03.md`); the R0–R12 proof
> grind is underway. **13 of ~34 tracked obligations remain** in `LirLean/RealisabilitySpec.lean`:
> CLOSED axiom-clean = R0b, R7a–e, R1 (the "riskiest" gas bridge), R2, R4, R5, R8, R9 + the `exProg`
> non-vacuity witnesses; OPEN = the two hard leaves R3 (call realisation) + R6 (boundary walk), the
> assembly (R10a/b, R11 flagship, R11-all, gasfree co-flagship, R12a/b) and RunFromLeft adequacy.
> Default `LirLean` GREEN + sorry-free; `Nightly` green with the 13 tracked sorries. A recorder
> course-correction (Option B, gate `recordCall` on `rest.isEmpty`) closed R7e unconditionally. Arc
> summary for a human reader: `experiments/005_ir_lowering/docs/achievements-since-main.md`.

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
| **B** | exp004 nested EVM core: EVMYulLean monomorphized to EVM-only, nested never-`OutOfFuel`, `Ξ`-triple | **[track-b-review.md](experiments/004_nested_evmyul/docs/track-b-review.md)** ✓ | B0 (mono) green; **fully-nested headline `Θ_never_outOfFuel` CLOSED + axiom-clean** (`exp004-nested`) — the 5-layer never-`OutOfFuel` mutual induction over `Θ/Ξ/X/step/call`, plus the `gas_mono` mutual induction and a ~250-line `step`/`Z` depth-preservation keystone, all proved + independently verified. Fuel bound is **LINEAR-PRODUCT** `B(g,e)=(1025−e)·(g+c)` (depth factor; linear in gas) — the earlier *super-linear* estimate was wrong. |
| **C** | exp005 `LirLean` IR → bytecode lowering + semantics preservation | **[track-c-review.md](experiments/005_ir_lowering/docs/track-c-review.md)**; **[audit-2026-07-02.md](experiments/005_ir_lowering/docs/audit-2026-07-02.md)** + **[target-architecture-2026-07-02.md](experiments/005_ir_lowering/docs/target-architecture-2026-07-02.md)** | **Current headline: `lower_conforms_cyclic_assembled` — a general (arbitrary cyclic CFG) world-conformance theorem that is CONDITIONAL, and whose supplied ties were confirmed UNSATISFIABLE (vacuous as stated).** It *supplies* the per-block `StmtTies`/`TermTies` runtime ties + `hcall` as hypotheses and has **no end-to-end instantiation**; the realisability rebuild follows [target-architecture-2026-07-02.md](experiments/005_ir_lowering/docs/target-architecture-2026-07-02.md) + [execution-plan-2026-07-02.md](experiments/005_ir_lowering/docs/execution-plan-2026-07-02.md) (R0–R12 skeleton in `LirLean/RealisabilitySpec.lean`). Gas is now a **log-fed exact-equality oracle** (monotonicity law dropped; the apparatus was deleted in Phase 2). The v1 `wc_preserves` "hypothesis-free" milestone and the v2 monotone-oracle work below are superseded/historical. |

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
- **IR→bytecode lowering conformance (Track C) — now a general but CONDITIONAL theorem.**
  The current headline is `lower_conforms_cyclic_assembled` (`LirLean/Drive/Headline.lean`):
  a general (arbitrary cyclic CFG), axiom-clean, gas-free *world*-conformance theorem. It is
  **conditional** — it *supplies* the per-block runtime ties `hstmtties : ∀ L b, StmtTies …`,
  `htermties`, and `hcall : CallPreservesSelf` as hypotheses (the ties are INPUTS, not outputs),
  and there is **no concrete end-to-end instantiation** on a real `lower prog` — and the supplied
  ties were since confirmed **unsatisfiable** (2026-07-03), so the headline is vacuous as stated.
  The realisability rebuild that replaces it is governed by
  **[target-architecture-2026-07-02.md](experiments/005_ir_lowering/docs/target-architecture-2026-07-02.md)** +
  **[execution-plan-2026-07-02.md](experiments/005_ir_lowering/docs/execution-plan-2026-07-02.md)**
  (the remediation plan is superseded). (The earlier v1
  `wc_preserves` "fully hypothesis-free" milestone was a single concrete `workedCall` program;
  the general cyclic headline superseded it, at the cost of re-introducing the supplied ties.)
  Gas is now a **log-fed exact-equality oracle** (handled like an external call), and the
  gas-monotonicity law was **dropped** as proved-but-unused — see
  [audit-2026-07-02.md](experiments/005_ir_lowering/docs/audit-2026-07-02.md),
  [remediation-plan-2026-07-02.md](experiments/005_ir_lowering/docs/remediation-plan-2026-07-02.md),
  and [gas-decision.md](experiments/005_ir_lowering/docs/gas-decision.md).
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
- **Track C v2 reformulation — DESIGNED (`exp005-ir`).** *(Historical: the monotone-gas-oracle
  part of this bullet is superseded by `docs/gas-decision.md` — gas is now a log-fed
  exact-equality oracle and the monotonicity law [`realisedGas_monotone`,
  `lower_preserves_obs_mono`, `GasRealises.monotoneGas`] was dropped as proved-but-unused.)*
  Driven by Eduardo: the IR
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
