# EVM Semantics Study Notes

This repository is a working notebook for comparing EVM formalizations and verified compiler architectures while planning a Lean formalization path for Plank.

The current focus is not to define Plank semantics yet. It is to understand the surrounding ecosystem:

- `EVMYulLean`: Lean executable semantics for EVM and Yul.
- `verity`: a Lean EDSL/compiler project that bridges generated Yul into EVMYulLean.
- `verifereum`: HOL executable EVM semantics with a relational/spec layer.
- `vyper-hol`: HOL source, IR, lowering, optimization, and codegen proof architecture for Vyper/Venom.
- `plank-monorepo`: Plank compiler and SIR/EthIR implementation.

Start reading at [`docs/index.md`](docs/index.md).

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

- [`docs/semantics-choice.md`](docs/semantics-choice.md)
- [`docs/sir-to-bytecode.md`](docs/sir-to-bytecode.md)
- [`docs/verity-bridge.md`](docs/verity-bridge.md)

