# Sir

Lean 4 implementation of Plank's production SIR compiler pipeline.

The initial library contains a register-based CFG and its canonical event-labelled
small-step semantics:

- `Sir/Core/` — primitive shared types.
- `Sir/IR/` — expressions, statements, terminators, basic blocks, and programs.
- `Sir/Semantics/World.lean` — concrete storage operations over `Evm.AccountMap`.
- `Sir/Semantics/State.lean` — locals, call context, IR control state, machine
  state, and execution events.
- `Sir/Semantics/Eval.lean` — deterministic evaluators for pure expressions,
  assignment, storage, calls given a result, and terminators. Control-flow edges
  simultaneously transfer a block's outputs by position into its successor's inputs.
- `Sir/Semantics/SmallStep.lean` — the program-indexed transition relation and
  its trace-accumulating multi-step closure.

The one-step relation has the shape:

```lean
SmallStep program context state trace state'
```

Internal transitions emit `[]`. `GAS` nondeterministically chooses an observed
word, binds it to a local, and emits a `.gas` event. `CALL` nondeterministically
accepts a result, resolves the target and forwarded gas from locals, updates the
account map, result local, and returndata, and emits the resulting checked
`CallRecord` as a `.call` event. Environmental choices are therefore recorded as
an output trace rather than supplied through oracle lists in machine state.

`MachineState` contains only the world, locals, returndata, and machine control.
`MachineControl` combines running program position with halted status, so a halted
state carries no stale program counter. Invalid control-flow targets, missing
locals, and otherwise undefined transitions are represented by stuck machine
states.

```sh
lake build
```
