# EVM Semantics Study Notes

This repository is a working notebook for comparing EVM formalizations and verified compiler architectures while building a Lean formalization path for Plank.

It pairs an ecosystem study with self-contained Lean experiments. The reference formalizations studied are:

- `EVMYulLean`: Lean executable semantics for EVM and Yul.
- `verity`: a Lean EDSL/compiler project that bridges generated Yul into EVMYulLean.
- `verifereum`: HOL executable EVM semantics with a relational/spec layer.
- `vyper-hol`: HOL source, IR, lowering, optimization, and codegen proof architecture for Vyper/Venom.
- `plank-monorepo`: Plank compiler and SIR/EthIR implementation.

For orientation (current direction, repo layout, conventions) read [`AGENTS.md`](AGENTS.md); for the docs themselves start at [`docs/index.md`](docs/index.md). The agreed direction is *bytecode-first*: see [`docs/planning/bytecode-first-plan.md`](docs/planning/bytecode-first-plan.md).

## Fetching Source Repositories

The source repositories are intentionally not tracked in git. They live under `forks/`, which is ignored.

Run:

```sh
./scripts/fetch-forks.sh
```

This clones the pinned revisions used by the documentation so links into `forks/` resolve locally.

## Current Recommendation

The current recommendation is to model Plank SIR/EthIR directly, then prove a bridge from SIR execution to emitted EVM bytecode using EVMYulLean as the low-level target semantics.

Relevant docs:

- [`docs/planning/semantics-choice.md`](docs/planning/semantics-choice.md)
- [`docs/planning/sir-to-bytecode.md`](docs/planning/sir-to-bytecode.md)
- [`docs/reference/verity-bridge.md`](docs/reference/verity-bridge.md)

