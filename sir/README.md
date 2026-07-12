# Sir

Lean 4 implementation of Plank's production SIR compiler pipeline.

The initial library contains a register-based CFG and its canonical small-step
semantics:

- `Sir/Core/` — primitive shared types. Words and addresses reuse
  `Evm.UInt256` and `Evm.AccountAddress` from `experiments/003_bytecode_layer`.
- `Sir/IR/` — expressions, statements, terminators, basic blocks, and programs.
- `Sir/Semantics/World.lean` — concrete storage operations over `Evm.AccountMap`.
- `Sir/Semantics/State.lean` — locals, call context, IR program counter, and
  complete machine state.
- `Sir/Semantics/Expr.lean` — deterministic, read-only expression evaluation.
- `Sir/Semantics/Terminator.lean` — deterministic control-flow evaluation.
- `Sir/Semantics/SmallStep.lean` — the program-indexed canonical transition
  relation.

`GAS` is a stateful statement that consumes a concrete trace entry and binds it
to a local. `CALL` atomically checks and consumes the next oracle record, updates
the account map and returndata, and binds its mandatory result variable. An empty
or mismatched oracle leaves the machine stuck.

There is currently no whole-program evaluator, interpreter, execution fuel,
CREATE operation, nested execution, lowering, or equivalence layer. Malformed
control flow, missing locals, exhausted gas traces, and unmet external inputs are
represented by stuck machine states. Halted control carries no stale program
counter, and invalid jump targets become stuck only when the next step attempts to
look them up.

```sh
lake build
```
