# SIR

Lean 4 formalization of Plank's Sensei Intermediate Representation (SIR).

This package defines native mixed-step semantics for `Vars`: named variables
and block arguments. Shared vocabulary (storage, memory, calls, gas, control,
traces) lives in `Core`. Instructions advance one small step at a time; an
internal call completes a whole callee run as a single step that splices the
callee's trace inline.

Executions are indexed by traces of gas observations and external calls.
Observation covers partial executions of the running function, and a completed
internal call contributes its events inline; a callee that never completes
contributes nothing observable. A function is deterministic when a shared
trace history determines its next observable outcome — a gas query, a call
input, a halt, or a return with its values. Program determinism is that
property at the entry points, where the entry ABI rules out the return
outcome.

Memory is flat: stores fault outside provisioned allocations, loads of
unprovisioned addresses read an oracle. `memoryPolicy` admits any disjoint
placement of the requested size. `bumpPolicy` is the release bump and
refines `memoryPolicy`.

## Layout

- [`Sir/Core/`](Sir/Core/) — shared values, effects, memory, control, and traces.
- [`Sir/Vars/`](Sir/Vars/) — `Spec`, `Proofs/`, and `Theorems`.
- [`Sir/Theorems.lean`](Sir/Theorems.lean) — the aggregate exported surface.
- [`Sir/Audit.lean`](Sir/Audit.lean) — build-time audit of the exported
  surface.

## Build

```sh
lake build
```
