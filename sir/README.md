# SIR

Lean 4 formalization of Plank's Sensei Intermediate Representation (SIR).

The library models a register-based control-flow graph with block inputs and
outputs, storage, explicitly allocated memory, calls, gas observations, and
event-labelled small-step semantics.

Executions are indexed by traces of gas observations and external calls. A
program is deterministic when a shared trace history determines its next call
input and halted runs with the same trace agree on the final world.

## Layout

- [`Sir/IR/CFG.lean`](Sir/IR/CFG.lean) — Defines **what** SIR is (`Program` datatype)
- [`Sir/Semantics/SmallStep.lean`](Sir/Semantics/SmallStep.lean) — Defines
  **how** SIR behaves (`SmallStep` semantics)
- [`Sir/Core/Types.lean`](Sir/Core/Types.lean) — shared primitive types.

## Build

```sh
lake build
```
