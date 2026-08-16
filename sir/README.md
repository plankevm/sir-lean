# SIR

Lean 4 formalization of Plank's Sensei Intermediate Representation (SIR).

The library splits SIR into two languages over one parametric machine. `Machine`
defines the small-step semantics generically over an operand frame (how instructions
reach their values), a decoder (what runs next), and a memory policy (which
allocations are admissible); `Vars` — named variables, block arguments — and
`Stack` — an operand stack plus spill slots — are its two instances, sharing block
inputs and outputs, internal functions, storage, memory, calls, and gas observations.
The semantics is mixed-step: statements advance one small step at a time, while an
internal call completes a whole callee run as a single step that splices the callee's
trace inline.

Executions are indexed by traces of gas observations and external calls. Observation
covers partial executions of the running function, and a completed internal call
contributes its events inline; a callee that never completes contributes nothing
observable. A function is deterministic when a shared trace history determines its
next observable outcome — a gas query, a call input, a halt, or a return with its
values. Program determinism is that property at the entry points, where the entry ABI
rules out the return outcome.

Memory is flat: stores fault outside provisioned allocations, loads of unprovisioned
addresses read an oracle. Allocation is nondeterministic — any valid region of the
requested size, constrained by the memory policy — with `bumpAlloc` as the
deterministic witness.

## Layout

- [`Sir/Machine/`](Sir/Machine/), [`Sir/Vars/`](Sir/Vars/), and
  [`Sir/Stack/`](Sir/Stack/) — each module's specification, proof machinery,
  and exported theorems. `Stack` is only a lowering target; its well-formedness and
  progress families arrive with the halting-operations work.
- [`Sir/Theorems.lean`](Sir/Theorems.lean) — the aggregate exported surface.
- [`Sir/Examples/`](Sir/Examples/) — well-formedness, (non-)determinism,
  halting-callee, machine-level execution, round-trip, and memory/allocation
  witnesses.
- [`Sir/Vars/Spec/Check.lean`](Sir/Vars/Spec/Check.lean) — one check, returning a
  proof of the well-formedness clause it discharges.
- [`Sir/Text/`](Sir/Text/) — the text format: printing a program and parsing it
  back returns the same program up to renaming, in canonical form; an extractor
  emits a parsed program as Lean source.
- [`Sir/Audit.lean`](Sir/Audit.lean) — build-time audit of the exported
  surface.

## Build

```sh
lake build
```

Extract a `.sir` file into a Lean module:

```sh
lake env lean --run SirExtract.lean input.sir Output.lean programName
```
