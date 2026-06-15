# Experiment 001: Toy External Call — docs

> **Status: CLOSED.** The toy IR was proved equivalent to EVMYulLean's `EVM.X`
> (gasless spec, reflexive calls, observables export; `lake build` green, zero
> sorries, standard axioms only). It taught what it was built to teach and was
> then retired in favour of the bytecode-first direction. New work does **not**
> extend this IR — start at
> [`docs/planning/bytecode-first-plan.md`](../../../docs/planning/bytecode-first-plan.md).

## What this experiment was

A tiny straight-line instruction IR (calldata load, add-constant, external
`CALL`) with an executable semantics, a total lowering to EVM bytecode, and a
proved equivalence against EVMYulLean's `EVM.X`. It exists to stress-test the
proof architecture and surface the load-bearing constraints early.

## Read in this order

1. [`results-v2.md`](./results-v2.md) — what was achieved, the honest
   rough-edge list, and the verdict. The best single entry point.
2. [`handoff.md`](./handoff.md) — current state, the exported theorems, the file
   map, and the facts the next layer must not relearn.
3. [`findings.md`](./findings.md) — reusable proof-engineering patterns and
   dead ends (defeq bridging, guard alignment, list-first encodings,
   position-generalized chunk lemmas). Applies beyond this experiment.
4. [`spec.md`](./spec.md) — the in-depth specification (explains the v1 metered
   statement; still accurate for `Metered.lean`/`Preservation.lean`).
5. [`verity-state-relations.md`](./verity-state-relations.md) — distilled
   deep-dive of Verity's three-relation state-abstraction pattern
   (source↔IR coupling, source↔IR boundary, IR↔EVMYulLean projection). Reusable
   blueprint for stacking higher-level IRs.
6. [`related-work.md`](./related-work.md) — why targeting Yul (via `solc`)
   buys nothing, and how this experiment compares to Verity/vyper-hol at the
   call boundary.

## Permanent findings (do not relearn)

- **`CALL` consults gas.** Even with no `GAS` opcode, gas is observable through
  calls (63/64 forwarding cap; callee OOG → flag 0, caller continues). So
  `result ≠ OutOfGass → result = IR run` is **false** with calls; the exported
  form must be `∃ G₀, ∀ G ≥ G₀`. There is an executable counterexample.
- **`EVM.call` is frame-insensitive** — proved cheaply via defeq bridging,
  because the call is modeled reflexively (IR call = `EVM.call` itself).
- **Fuel debt.** Removing fuel from exported statements needs a
  fuel-monotonicity theorem about EVMYulLean's `Θ`/`Ξ`/`X` stack — real,
  unstarted work.

## Archive

[`archive/plan.md`](./archive/plan.md) (original phased plan, superseded) and
[`archive/wrong-attempts.md`](./archive/wrong-attempts.md) (dead-ends log).
