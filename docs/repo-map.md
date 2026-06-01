# Repository Map

## EVMYulLean

Path: [`forks/EVMYulLean`](../forks/EVMYulLean)

Lean model of EVM and Yul. It models EVM state close to Yellow Paper notation:

- world state/account map,
- execution environment,
- machine state,
- stack/program counter for EVM,
- Yul state and variable store for Yul.

Key files:

- [`EvmYul/State.lean`](../forks/EVMYulLean/EvmYul/State.lean): shared world/execution state.
- [`EvmYul/MachineState.lean`](../forks/EVMYulLean/EvmYul/MachineState.lean): gas, memory, return data.
- [`EvmYul/EVM/Semantics.lean`](../forks/EVMYulLean/EvmYul/EVM/Semantics.lean): EVM step, iteration, call, transaction execution.
- [`EvmYul/Yul/Interpreter.lean`](../forks/EVMYulLean/EvmYul/Yul/Interpreter.lean): Yul evaluator/interpreter.

## Verity

Path: [`forks/verity`](../forks/verity)

Lean smart-contract EDSL plus compiler/proof infrastructure. It is not just an EVM model. It has:

- source-level `ContractState` and `Contract` monad,
- typed IR and compilation model,
- Yul AST/codegen,
- proof runtimes and bridge code toward EVMYulLean.

Key files:

- [`Verity/Core.lean`](../forks/verity/Verity/Core.lean): source EDSL state and contract monad.
- [`Verity/Core/Free/TypedIR.lean`](../forks/verity/Verity/Core/Free/TypedIR.lean): typed IR GADT and evaluator.
- [`Compiler/CompilationModel/Types.lean`](../forks/verity/Compiler/CompilationModel/Types.lean): declarative contract model.
- [`Compiler/IR.lean`](../forks/verity/Compiler/IR.lean): IR contract/function records.
- [`Compiler/Yul/Ast.lean`](../forks/verity/Compiler/Yul/Ast.lean): Yul AST.

## Verifereum

Path: [`forks/verifereum`](../forks/verifereum)

HOL EVM formalization. This is the most direct HOL EVM model in the workspace:

- account/storage state,
- call frames,
- gas and memory accounting,
- opcode stepping,
- transaction execution,
- Hoare/spec bridge in `prog/`.

Key files:

- [`spec/vfmStateScript.sml`](../forks/verifereum/spec/vfmStateScript.sml): account and storage model.
- [`spec/vfmContextScript.sml`](../forks/verifereum/spec/vfmContextScript.sml): call-frame and execution state.
- [`spec/vfmExecutionScript.sml`](../forks/verifereum/spec/vfmExecutionScript.sml): opcode execution, step, run, transactions.
- [`prog/vfmProgScript.sml`](../forks/verifereum/prog/vfmProgScript.sml): state-set and spec bridge.

## Vyper-HOL

Path: [`forks/vyper-hol`](../forks/vyper-hol)

HOL formalization around Vyper and Venom IR. It reuses Verifereum for EVM-level concepts and builds a compiler-correctness ladder:

```text
Vyper source call_external
  -> Venom run_context
  -> Venom passes
  -> asm/codegen
  -> Verifereum EVM run
```

Key files:

- [`semantics/vyperInterpreterScript.sml`](../forks/vyper-hol/semantics/vyperInterpreterScript.sml): source-level big-step interpreter.
- [`semantics/vyperSmallStepScript.sml`](../forks/vyper-hol/semantics/vyperSmallStepScript.sml): CPS/small-step-flavored source semantics.
- [`venom/defs/venomInstScript.sml`](../forks/vyper-hol/venom/defs/venomInstScript.sml): Venom instruction set.
- [`venom/defs/venomStateScript.sml`](../forks/vyper-hol/venom/defs/venomStateScript.sml): Venom state.
- [`venom/defs/venomExecSemanticsScript.sml`](../forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml): Venom operational semantics.
- [`lowering/vyperLoweringCorrectScript.sml`](../forks/vyper-hol/lowering/vyperLoweringCorrectScript.sml): top-level lowering theorem shape.

## Plank

Path: [`forks/plank-monorepo`](../forks/plank-monorepo)

Rust compiler stack:

```text
Plank source/CST
  -> HIR
  -> MIR
  -> SIR/EthIR
  -> stack scheduling/assembly/codegen
  -> EVM bytecode
```

Key files:

- [`plankc/frontend/hir/src/lib.rs`](../forks/plank-monorepo/plankc/frontend/hir/src/lib.rs): HIR expressions and instructions.
- [`plankc/frontend/mir/src/lib.rs`](../forks/plank-monorepo/plankc/frontend/mir/src/lib.rs): compact MIR.
- [`plankc/frontend/mir-lower/src/lib.rs`](../forks/plank-monorepo/plankc/frontend/mir-lower/src/lib.rs): MIR to SIR lowering.
- [`plankc/sir/crates/data/src/lib.rs`](../forks/plank-monorepo/plankc/sir/crates/data/src/lib.rs): SIR program, blocks, locals, data.
- [`plankc/sir/crates/data/src/operation/mod.rs`](../forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs): SIR operations and EVM opcode mapping.
- [`plankc/frontend/session/src/builtins.rs`](../forks/plank-monorepo/plankc/frontend/session/src/builtins.rs): Plank raw EVM builtins.

