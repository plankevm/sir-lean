# Semantics Choice for Plank

## Recommendation

Define a Plank SIR semantics and bridge it to EVMYulLean. Do not define a fresh full EVM semantics unless Plank wants to own an EVM model as a separate long-term project.

The architecture should look like Vyper-HOL's Venom layer, but implemented in Lean and targeting EVMYulLean:

```text
Plank SIR interpreter
  -> SIR optimization/pass simulations
  -> SIR-to-bytecode simulation
  -> EVMYulLean bytecode execution
```

## Why Not a Fresh Full EVM Semantics

Verifereum shows the real scope of owning EVM:

- account and storage model;
- call frames and rollback state;
- calldata, returndata, logs, and memory expansion;
- gas accounting and refunds;
- opcode dispatch;
- `CALL`, `DELEGATECALL`, `STATICCALL`, `CREATE`, `CREATE2`;
- transaction entry and exceptional halt behavior.

That is useful if the project goal is "build the Lean EVM semantics". It is scope creep if the project goal is "prove Plank SIR lowers correctly."

## Why Not Only Use EVMYulLean as the SIR Semantics

EVMYulLean is too low-level to be the only semantic interface for SIR. It is bytecode/Yellow-Paper-shaped: it has world state, machine state, stack, program counter, gas, returndata, substate, and transaction fields.

Using it directly would force early Plank proofs to mention:

- exact stack layout;
- exact bytecode offsets;
- jump destination validity;
- bytecode parsing;
- gas and memory expansion;
- revert/exception details;
- account-map rollback.

Those are backend proof obligations. They should not pollute the definition of what a SIR operation means.

## Why EVMYulLean Is Still Useful

EVMYulLean gives an executable Lean target for EVM/Yul. That is valuable because Plank likely wants Lean, and using an existing EVM semantics avoids rebuilding the whole VM.

The local checkout is not ancient: `forks/EVMYulLean` is at `047f63070309f436b66c61e276ab3b6d1169265a`, dated 2025-09-24. Verity actively uses a pinned `lfglabs-dev/EVMYulLean` fork at `7785a9bba344db917e42b7f1033ee8346197bb40`.

The risk is not merely staleness. The bigger risk is that EVMYulLean lacks Verifereum's mature relational/spec layer. Plank can compensate by adding its own relations around SIR and bytecode without reimplementing EVM itself.

## Practical Decision

Use:

- EVMYulLean for final low-level execution;
- a Plank-owned executable SIR semantics for the IR model;
- Vyper-HOL/Venom as proof-architecture inspiration;
- Verity as the Lean-native example of state projection and native EVMYulLean bridging.

Avoid:

- proving Plank source semantics first;
- modeling Plank as a Verity-style EDSL;
- rebuilding Verifereum in Lean before proving anything about Plank.

