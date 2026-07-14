# Experiment 005: IR lowering

Experiment 005 is the repository's main SIR-to-EVM-bytecode lowering track. It defines a small CFG
IR with observable storage, gas reads, calls, and CREATE2; an executable stream-based semantics; a
fixed-layout lowering; and the EVM reasoning needed to connect recorded bytecode runs back to the
IR.

## Read in this order

1. [`ir-design-v3.md`](ir-design-v3.md) for the current IR design.
2. [`planning/r11-plan-2026-07-08.md`](planning/r11-plan-2026-07-08.md) for the live proof order,
   debt ledger, and guardrails.
3. [`review/spec-feedback-addressed-2026-07-09.md`](review/spec-feedback-addressed-2026-07-09.md)
   for the latest spec-surface review and deferred cleanup.
4. [`codebase-map-2026-07-06.md`](codebase-map-2026-07-06.md) for a broad map; treat its dated debt
   counts as historical.

## Current shape

- `LirLean/Spec/`: public syntax, semantics, lowering, recorder, conformance, seams, and static
  well-formedness.
- `../../../EVM/BytecodeLayer/Hoare/`: reusable, IR-free interpreter reasoning shared by
  the lowering proof.
- `LirLean/{Decode,Materialise,Sim,CfgSim}/`: lowering-specific bytecode reasoning.
- `LirLean/Realisability/`: the non-default `WIP` closure layer. `Surface.lean` defines the
  coupling vocabulary, `Machinery.lean` proves engine bridges, `Producer.lean` builds the coupled
  IR run, and `RealisabilitySpec.lean` contains the public theorem shells.

`lake build` and `lake build WIP` must remain green and sorry-free. The public
`lower_conforms`, `lower_conforms_exact`, and `lower_conforms_gasfree` theorems are closed and
axiom-clean; refactors must preserve their statements and axiom sets exactly.

## Cleanup rule

Do not globally strip comments. Spec files keep only short semantic orientation. Historical proof
status belongs in docs, not theorem headers. New helper lemmas must close a named obligation,
become private support for a consumed abstraction, or be deleted at the next green checkpoint.

The old root [`PLAN.md`](../PLAN.md) is a historical log and is not the active plan.
