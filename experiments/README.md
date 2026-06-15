# Experiments

This directory contains small Lean packages used to explore Plank SIR formalization choices.

Each experiment should be self-contained and include:

- a local `lakefile.lean`;
- Lean source files;
- a `docs/` directory recording the plan, design decisions, what worked, what failed, and what should be reused.

An experiment may also carry its own `AGENTS.md`/`CLAUDE.md` with Lean coding
rules specific to that package (e.g. the `Spec.lean`/`Proof.lean` split in
`002_ssa_cfg`).

The point is not to keep every experiment polished. The point is to preserve what we learn while we converge on a real SIR formalization.

## Current Experiments

- [`001_toy_external_call`](./001_toy_external_call/docs/README.md) — **closed.**
  A tiny straight-line IR (calldata load, add-constant, external `CALL`) proved
  equivalent to EVMYulLean's `EVM.X`, with a gasless spec, reflexive calls, and
  observables export. Surfaced that `CALL` consults gas (forcing `∃G₀`
  statements) and that `EVM.call` is frame-insensitive.
- [`002_ssa_cfg`](./002_ssa_cfg) — **active.** A higher-level SIR: a CFG of basic
  blocks with SSA-style variables, small-step + executable semantics, and an
  SCCP optimization pass proved to preserve semantics. Explores SIR semantics and
  pass correctness in isolation (no bytecode lowering yet).

