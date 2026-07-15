# SIR

Lean 4 formalization of Plank's Sensei Intermediate Representation (SIR).

The library models a register-based control-flow graph with block inputs and
outputs, storage, calls, gas observations, and event-labelled small-step
semantics.

## Layout

- [`Sir/Core/`](Sir/Core/) — shared primitive types.
- [`Sir/IR/`](Sir/IR/) — SIR syntax and control-flow graphs.
- [`Sir/Semantics/`](Sir/Semantics/) — state, evaluation, world operations, and
  small-step semantics.
- [`Sir.lean`](Sir.lean) — library entry point.

## Build

```sh
lake build
```
