# Recommended Formalization Plan

## Goal

Formalize enough of Plank IR to prove semantic preservation for lowering to EVM bytecode.

This plan assumes the architecture justified in [Semantics choice for Plank](./semantics-choice.md): Plank owns a SIR semantics and proves a bridge to EVMYulLean, rather than owning a fresh full EVM semantics. The bytecode bridge is expanded in [SIR to bytecode correctness](./sir-to-bytecode.md).

The likely theorem shape:

```text
If:
  compile_sir program = bytecode
  initial_state_rel sir_state evm_state
  run_sir program sir_state = sir_result
Then:
  exists evm_result,
    run_evm bytecode evm_state = evm_result
    and result_rel sir_result evm_result
```

For earlier milestones, replace full `run_evm` with a simpler target relation over emitted assembly or an instruction trace.

## Phase 1: Define SIR Semantics

Start with SIR/EthIR because it is:

- explicit CFG,
- close to EVM,
- already has an operation universe,
- already separates direct EVM ops from special IR ops.

Use an interpreter-based small-step/block-step semantics:

```text
step_op    : Program -> Operation -> State -> Result State
step_block : Program -> BasicBlock -> State -> Result State
run_func   : Program -> FunctionId -> State -> Result State
run        : Program -> EntryKind -> State -> Result State
```

This is the same broad pattern as Vyper-HOL Venom's `step_inst`, `exec_block`, `run_blocks`, and `run_context`.

## Phase 2: State Relation to EVM

Define `state_rel : SirState -> EvmState -> Prop`.

Core relation:

- SIR locals correspond to a scheduled stack layout or to abstract values before scheduling.
- SIR memory equals current EVM call-frame memory.
- SIR accounts/storage equal EVM world state.
- SIR transient storage equals EVM transient storage.
- SIR returndata equals EVM return data buffer.
- SIR logs equal EVM logs.
- call/tx/block contexts match EVM execution environment.

Do not hide return/revert/exhalt differences. They affect rollback, returndata, and gas.

## Phase 3: Direct Opcode Correctness

For operations that map literally to EVM opcodes, prove one-step correctness.

Plank anchor:

```rust
OperationKind::SLoad => op::SLOAD,
OperationKind::SStore => op::SSTORE,
OperationKind::Call => op::CALL,
OperationKind::StaticCall => op::STATICCALL,
OperationKind::Return => op::RETURN,
OperationKind::Revert => op::REVERT,
```

Source: [`forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs`](../forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs)

The proof can be staged:

1. arithmetic and bitwise operations,
2. memory reads/writes,
3. storage/transient storage,
4. logs,
5. calls and creates,
6. return/revert/exhalt.

## Phase 4: Special SIR Operations and Bytecode Segments

Special operations are not single EVM opcodes:

- `SetSmallConst`, `SetLargeConst`,
- `MemoryLoad`, `MemoryStore`,
- `DynamicAllocZeroed`, `DynamicAllocAnyBytes`,
- `StaticAllocZeroed`, `StaticAllocAnyBytes`,
- `InternalCall`,
- `RuntimeStartOffset`, `InitEndOffset`, `RuntimeLength`,
- `SetDataOffset`.

For these, prove correctness against their emitted opcode sequences. This is where the proof stops being one SIR op to one EVM opcode and becomes one SIR op to a bounded bytecode segment.

Example backend special case:

```rust
Operation::MemoryLoad(data) => self.emit_memory_load(data),
Operation::MemoryStore(data) => self.emit_memory_store(data),
Operation::SetSmallConst(args) => self.asm.push_minimal_u32(args.value),
Operation::InternalCall(args) => {
    self.emit_icall(state, icall_return_marks, op_idx, args.function)
}
```

Source: [`forks/plank-monorepo/plankc/sir/crates/release-backend/src/code_to_asm.rs`](../forks/plank-monorepo/plankc/sir/crates/release-backend/src/code_to_asm.rs)

## Phase 5: Function-Level Bytecode Simulation

After opcode and special-operation lemmas exist, prove that a whole emitted SIR function simulates the SIR interpreter.

The relation should include:

- current SIR block/op index to EVM program counter;
- SIR locals to scheduled stack/spill memory;
- SIR memory to EVM memory outside compiler spill regions;
- shared accounts/storage/transient storage;
- shared returndata/logs;
- compatible halt/revert/exception outcomes.

This follows the Vyper-HOL Venom codegen split: stack relation, spill/memory relation, full running-state relation, and terminal observable relation.

## Phase 6: Pass Correctness

Once SIR semantics exists, optimization pass correctness can be stated as simulation:

```text
program_rel p p' ->
run_sir p s = r ->
exists r', run_sir p' s = r' and result_rel r r'
```

Vyper-HOL's pass organization is a useful precedent: each pass has a transformation file and a correctness/proof file.

## Phase 7: MIR-to-SIR Lowering

MIR-to-SIR lowering flattens structs, maps MIR locals to one or more SIR locals, builds CFG segments, and maps runtime builtins to SIR operations.

Plank anchor:

```rust
fn lower_function(...) -> sir::FunctionId { ... }
fn lower_basic_block(...) -> CFGSegment { ... }
```

Source: [`forks/plank-monorepo/plankc/frontend/mir-lower/src/lib.rs`](../forks/plank-monorepo/plankc/frontend/mir-lower/src/lib.rs)

For the first MIR theorem, avoid the full source language:

```text
mir_to_sir m = p
mir_state_rel mir_state sir_state
run_mir m mir_state = mir_result
run_sir p sir_state = sir_result
result_rel mir_result sir_result
```

## Lean vs HOL Choice

Since the likely target is Lean, the most relevant implementation model is EVMYulLean, but the best proof architecture example is Vyper-HOL:

- EVMYulLean gives Lean definitions for EVM/Yul execution.
- Vyper-HOL shows how to build an IR semantics and connect it by relations to a lower-level EVM semantics.
- Verity shows Lean-side EDSL/compiler structuring and bridge patterns, but its source state is more abstract than Plank's low-level IR needs.

Pragmatic recommendation: define Plank SIR semantics in Lean using a Vyper-HOL/Venom-like structure, then prove a bridge either to EVMYulLean EVM execution or to an intermediate assembly semantics.
