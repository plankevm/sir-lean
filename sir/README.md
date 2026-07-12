# Sir

Lean 4 implementation of Plank's production SIR compiler pipeline.

The initial library contains a register-based CFG and an executable semantics:

- `Sir/Core/` — primitive shared types. `Word` reuses `Evm.UInt256` from
  `experiments/003_bytecode_layer`.
- `Sir/IR/` — expressions, effecting statements, terminators, basic blocks, and
  programs.
- `Sir/Semantics/World.lean` — the generic storage interface, its laws, and a
  lightweight account-indexed functional world.
- `Sir/Semantics/State.lean` — invocation-local state, call context, and the IR
  program counter.
- `Sir/Semantics/Interaction.lean` — first-order CALL/CREATE requests,
  continuations, and responses.
- `Sir/Semantics/Step.lean` — one intraprocedural statement or terminator step.
- `Sir/Interpreter/Replay.lean` — a fuel-bounded driver that supplies recorded
  CALL and CREATE responses at suspension points.

`GAS` consumes values from the invocation's concrete gas trace. `CALL` and
`CREATE` suspend the core machine before their effects; replay is only one driver
for that interface. A future nested driver can execute another IR program while
retaining the same caller continuation.

The intended later layers are analyses and validation, transformation passes,
assembly/lowering, and verification. They are deliberately not represented by
placeholder Lean modules yet.

```sh
lake build
```
