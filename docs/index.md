# Documentation Hub

This repository is a working notebook for studying how to formalize Plank's EVM
IRs in Lean — comparing existing EVM/compiler formalizations, recording what we
learn, and converging on a real SIR-to-bytecode correctness proof.

The docs are organized in three tiers:

- **[reference/](#reference)** — durable knowledge about the ecosystem and the
  concepts (the "textbook"). Stable; updated when facts change.
- **[planning/](#planning)** — where the work is going (the "roadmap"). Has a
  clear head-of-stack.
- **[archive/](#archive)** — superseded plans and raw agent transcripts, kept for
  provenance. Each carries a banner pointing to what replaced it.

> ## 📍 Current direction (head of stack)
>
> [**planning/bytecode-first-plan.md**](./planning/bytecode-first-plan.md) is the
> authoritative, agreed direction: retire the toy IR (experiment 001 is closed),
> vendor EVMYulLean EVM-only, build a reusable reasoning layer over the bytecode
> semantics, move the theorem boundary to the `Θ`/`Ξ` message call (observables
> only), and make Plank SIR the first IR with a real abstraction gap. **New work
> starts there.**

## Reference

Read roughly in this order on a first pass:

1. [Jargon and semantic styles](./reference/jargon.md) — small-step, big-step,
   block-step, interpreter, relational; the vocabulary the rest of the docs use.
2. [EVM state model and Yellow Paper notation](./reference/evm-state-model.md) —
   world / execution-env / machine-state layers; why SIR should not force a
   `pc`/stack until lowering.
3. [Repository map](./reference/repo-map.md) — directory and key-file guide to
   the five repos under `forks/`.
4. [Lean-based models: EVMYulLean and Verity](./reference/lean-models.md)
5. [Verity to EVMYulLean bridge](./reference/verity-bridge.md) — the
   state-projection + observable-matching pattern worth stealing.
6. [HOL-based models: Verifereum and Vyper-HOL](./reference/hol-models.md) —
   Verifereum's relational/Hoare layer; Vyper-HOL's Venom codegen architecture.
7. [Horizontal concept comparison](./reference/concept-comparison.md) — state,
   storage, memory, calls, return/revert, gas across all four formalizations.
8. [Plank IR modeling notes](./reference/plank-ir-modeling.md) — the Plank
   pipeline (CST→HIR→MIR→SIR→bytecode) and why SIR is the first target.
9. [EVMYulLean reading guide](./reference/EVMYulLean-reading-guide.md) —
   navigation of the EVMYulLean repo (decode → step → X → Ξ → Λ → Θ → Υ).

## Planning

1. [**Bytecode-first plan**](./planning/bytecode-first-plan.md) — head of stack
   (see callout above).
2. [Semantics choice for Plank](./planning/semantics-choice.md) — define a
   Plank-owned SIR semantics and bridge to EVMYulLean; do not own a fresh full
   EVM model.
3. [SIR to bytecode correctness](./planning/sir-to-bytecode.md) — the central
   theorem shape, the state relation, and where the program counter lives.
4. [Recommended formalization plan](./planning/formalization-plan.md) — the
   phased strategy from SIR semantics through pass correctness.

## Top-level packages

- **`EVM/`** — the consolidated bytecode reasoning layer: the vendored EVM-only
  EVMYulLean (`Evm`), the reusable proof engine `BytecodeLayer` (frame calculus,
  recorder, cyclic simulation, structured `Asm` assembler — folded in from the
  former experiments 003 + 005), and the `Conform` test cone.
- **`sir/`** — the canonical SIR package (basic-block CFG IR, small-step + eval
  semantics, world model). In progress; the go-forward IR that the lowering and
  value-channel work migrates onto.

## Experiments

Self-contained Lean packages exploring formalization choices. See
[experiments/README.md](../experiments/README.md).

- [Experiment 001: toy external call](../experiments/001_toy_external_call/docs/README.md)
  — **closed.** A straight-line IR with calldata load, add, and a real external
  `CALL`, proved against EVMYulLean's `EVM.X`. Produced the load-bearing finding
  that `CALL` consults gas (forcing `∃G₀`-shaped statements) and the cheap
  `EVM.call` frame-insensitivity proof.
- [Experiment 002: SSA CFG](../experiments/002_ssa_cfg) — **active.** Studies
  source-level CFG/SSA semantics and SCCP correctness in isolation.
- [Experiment 005: IR lowering](../experiments/005_ir_lowering/docs/index.md) —
  **active.** The `Lir` IR and its lowering to EVM bytecode, now built on the
  `EVM/` package. Its `lower_conforms` / `_exact` / `_gasfree` flagships are
  closed and axiom-clean; the non-default `WIP` cone carries the realisability
  development.

## Archive

Superseded but kept for provenance (each has a banner):
[pilot plan](./archive/pilot-sir-formalization-plan.md),
[lowering-v2 plan](./archive/lowering-v2-plan.md) (statement shape still cited),
[review follow-up](./archive/review-followup-plan.md) (done),
[agent-notes transcript](./archive/agent-notes.md) (distilled into the docs above).

## Short Takeaway

The closest reusable EVM semantics are `forks/EVMYulLean` (Lean executable EVM
and Yul, Yellow-Paper-shaped, fuel-bounded) and `forks/verifereum` (HOL
executable EVM with a monadic small-step interpreter *plus* a Hoare/spec layer —
the relational layer EVMYulLean lacks). The closest "source/IR into EVM" examples
are `forks/verity` (a Lean EDSL that lowers to Yul with bridge code toward
EVMYulLean) and `forks/vyper-hol` (HOL source + Venom IR + lowering relations +
codegen-to-Verifereum).

For Plank, the strongest first target is SIR/EthIR (already CFG-shaped, explicit
about storage/memory/calldata/calls/logs/returndata/bytecode), not the parser AST
or HIR. The architecture is **not** "prove Plank inside EVMYulLean"; it is "give
SIR an executable semantics, then prove the bytecode backend refines it, using
EVMYulLean as the target model."

## Documentation Conventions

When a page invokes a technical concept that affects proof architecture, it
should either explain it locally or link to a page that does. Short labels like
"small-step", "Yellow Paper state", "state relation", "fuel", "rollback", or
"observable projection" should not be left as unexplained decoration.

When a doc is superseded, move it to [archive/](./archive/) and add a top banner
pointing to what replaced it — do not delete it (the reasoning is often still
worth reading) and do not leave it in place unmarked (readers can't tell it is
stale).
