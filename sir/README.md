# SIR

Lean 4 formalization of Plank's Sensei Intermediate Representation (SIR).

The library models a register-based control-flow graph with block inputs and
outputs, internal functions, storage, explicitly allocated memory, calls, gas
observations, and event-labelled mixed-step semantics: statements advance one
small step at a time, while an internal call completes a whole callee run as a
single step that splices the callee's trace inline.

Executions are indexed by traces of gas observations and external calls.
Observation covers partial executions of any callable function, and a trace
prefix may reach inside an internal call that never completes, so events
emitted before a callee diverges remain observable. A function is
deterministic when a shared trace history determines its next observable
outcome — a gas query, a call input, a halt with a final world, or a return
with its values. Program determinism is that property at the entry points,
where the entry ABI rules out the return outcome.

## Layout

- [`Sir/Spec/`](Sir/Spec/) — the definitions: `Ir → Memory → State → Step →
  Run → Observation`, with `WellFormed` alongside off `State`.
- [`Sir/Theorems.lean`](Sir/Theorems.lean) — every exported result, stated in
  `Spec` vocabulary.
- [`Sir/Proofs/`](Sir/Proofs/) — proof machinery.
- [`Sir/Examples/`](Sir/Examples/) — well-formedness, (non-)determinism,
  halting-callee, and diverging-callee observability witnesses.
- [`Sir/Audit.lean`](Sir/Audit.lean) — build-time audit of the exported
  surface.

## Build

```sh
lake build
```
