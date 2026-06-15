# Experiment 001: Toy External Call — Plan

> **Archived — superseded.** Experiment 001 is closed; this original phased plan
> is history. For current state see [../handoff.md](../handoff.md) and
> [../results-v2.md](../results-v2.md).

## Goal (achieved)

A tiny straight-line IR (calldata load, add, external `CALL` via oracle)
with a gas-exact executable semantics, a total lowering to EVM bytecode,
and a proved equivalence against EVMYulLean's `EVM.X`:
`Preservation.lowering_correct` (no sorries, standard axioms only).

See `handoff.md` for the current state and `findings.md` for the
proof-engineering record. The original phased plan is superseded; the
remaining roadmap items are in the "Next steps" section of `handoff.md`:

1. prove `EVM.call` frame-insensitivity (discharges half of
   `CallOracleSound`);
2. returndata operations;
3. control flow (`JUMP`/`JUMPI` + `D_J` reasoning);
4. an abstract locals view with a separation discipline;
5. growth toward Plank SIR and the `Ξ`/`Θ` message-call boundary.
