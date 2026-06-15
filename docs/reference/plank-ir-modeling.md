# Plank IR Modeling Notes

## Compiler Shape

The current Plank compiler pipeline is:

```text
source/CST
  -> HIR
  -> MIR
  -> SIR/EthIR
  -> SIR passes
  -> stack scheduling / assembly
  -> EVM bytecode
```

The driver shows the main backend path:

```rust
let mut program = plank_mir_lower::lower(mir, &self.values);
let mut pass_manager = PassManager::new(&mut program);
pass_manager.run_ssa_transform();
if let Some(passes) = optimizations {
    pass_manager.run_optimizations(passes);
}
sir_release_backend::ir_to_bytecode(&program, &analyses, &mut bytecode);
```

Source: [`forks/plank-monorepo/plankc/frontend/driver/src/lib.rs`](../../forks/plank-monorepo/plankc/frontend/driver/src/lib.rs)

## HIR

HIR still contains language-level constructs: functions, comptime blocks, local mutation, branching, loops, member access, struct literals, and builtin calls.

```rust
pub enum InstructionKind {
    Param { comptime: bool, arg: LocalId, r#type: ParamType, idx: u32 },
    Set { local: LocalId, r#type: Option<LocalId>, expr: Expr },
    SetMut { local: LocalId, r#type: Option<LocalId>, expr: Expr },
    Assign { target: LocalId, expr: Expr },
    Eval(Expr),
    Return(Expr),
    If { condition: LocalId, then_block: BlockId, else_block: BlockId },
    While { condition_block: BlockId, condition: LocalId, body: BlockId },
    ComptimeBlock { body: BlockId },
}
```

Source: [`forks/plank-monorepo/plankc/frontend/hir/src/lib.rs`](../../forks/plank-monorepo/plankc/frontend/hir/src/lib.rs)

HIR is valuable for source-language reasoning, but it is not the first place to connect to EVM semantics.

## MIR

MIR is smaller and typed by local metadata:

```rust
pub enum Expr {
    LocalRef(LocalId),
    Const(ValueId),
    Call { callee: FnId, args: ArgsId },
    RuntimeBuiltinCall { builtin: RuntimeBuiltin, args: ArgsId },
    FieldAccess { object: LocalId, field_index: u32 },
    StructLit { ty: TypeId, fields: ArgsId },
}

pub enum Instruction {
    Set { target: LocalId, expr: Expr },
    Return(LocalId),
    If { condition: LocalId, then_block: BlockId, else_block: BlockId },
    While { condition_block: BlockId, condition: LocalId, body: BlockId },
}
```

Source: [`forks/plank-monorepo/plankc/frontend/mir/src/lib.rs`](../../forks/plank-monorepo/plankc/frontend/mir/src/lib.rs)

MIR is a reasonable semantics target if the goal is to reason about language constructs. But its runtime builtins already point below it.

## SIR/EthIR

SIR/EthIR is the best first formal IR boundary. It is CFG-shaped and close to EVM. It is also the right place to work downward to bytecode first; source/HIR/MIR semantics can come later.

```rust
pub struct EthIRProgram {
    pub init_entry: FunctionId,
    pub main_entry: Option<FunctionId>,
    pub functions: IndexVec<FunctionId, Function>,
    pub basic_blocks: IndexVec<BasicBlockId, BasicBlock>,
    pub operations: IndexVec<OperationIdx, Operation>,
    pub data_segments: ListOfLists<DataId, u8>,
    pub locals: IndexVec<LocalIdx, LocalId>,
    pub large_consts: IndexVec<LargeConstId, U256>,
    pub cases: IndexVec<CasesId, Cases>,
}
```

Source: [`forks/plank-monorepo/plankc/sir/crates/data/src/lib.rs`](../../forks/plank-monorepo/plankc/sir/crates/data/src/lib.rs)

The operation universe includes direct EVM operations plus IR-specific operations:

```rust
SLoad(InlineOperands<1, 1>) "sload",
SStore(InlineOperands<2, 0>) "sstore",
TLoad(InlineOperands<1, 1>) "tload",
TStore(InlineOperands<2, 0>) "tstore",
Log0(InlineOperands<2, 0>) "log0",
Call(AllocatedIns<7, 1>) "call",
DelegateCall(AllocatedIns<6, 1>) "delegatecall",
StaticCall(AllocatedIns<6, 1>) "staticcall",
Return(InlineOperands<2, 0>) "return",
Revert(InlineOperands<2, 0>) "revert",
```

Source: [`forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs`](../../forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs)

Many SIR operations lower literally to EVM opcodes:

```rust
pub fn as_literal_evm_op(self) -> Option<u8> {
    let evm_op = match self {
        OperationKind::Add => op::ADD,
        OperationKind::SLoad => op::SLOAD,
        OperationKind::SStore => op::SSTORE,
        OperationKind::Call => op::CALL,
        OperationKind::StaticCall => op::STATICCALL,
        OperationKind::Return => op::RETURN,
        OperationKind::Revert => op::REVERT,
        ...
    };
    Some(evm_op)
}
```

Source: [`forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs`](../../forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs)

## Raw EVM Builtins

Plank exposes blockchain/VM concepts mostly through runtime builtins:

```rust
SLOAD "@evm_sload" => SLoad;
SSTORE "@evm_sstore" => SStore;
TLOAD "@evm_tload" => TLoad;
TSTORE "@evm_tstore" => TStore;
CALL "@evm_call" => Call;
DELEGATECALL "@evm_delegatecall" => DelegateCall;
STATICCALL "@evm_staticcall" => StaticCall;
RETURN "@evm_return" => Return;
REVERT "@evm_revert" => Revert;
```

Source: [`forks/plank-monorepo/plankc/frontend/session/src/builtins.rs`](../../forks/plank-monorepo/plankc/frontend/session/src/builtins.rs)

These builtins lower directly into SIR operations:

```rust
RuntimeBuiltin::SLoad => OperationKind::SLoad,
RuntimeBuiltin::SStore => OperationKind::SStore,
RuntimeBuiltin::Call => OperationKind::Call,
RuntimeBuiltin::DelegateCall => OperationKind::DelegateCall,
RuntimeBuiltin::StaticCall => OperationKind::StaticCall,
```

Source: [`forks/plank-monorepo/plankc/frontend/mir-lower/src/builtins.rs`](../../forks/plank-monorepo/plankc/frontend/mir-lower/src/builtins.rs)

## Recommended SIR Semantic State

A Plank SIR semantics should be close to Vyper-HOL Venom and Verifereum:

```text
SirState =
  locals          : LocalId -> Word256
  memory          : ByteArray or List Byte
  returndata      : ByteArray
  accounts        : Address -> Account
  transient       : Address -> Slot -> Word256
  logs            : List Event
  currentFunction : FunctionId
  currentBlock    : BasicBlockId
  opIndex         : Nat
  callContext     : caller, address, callvalue, calldata, static flag
  txContext       : origin, gasprice, chainid, blob hashes
  blockContext    : coinbase, timestamp, number, basefee, blockhash
  dataSegments    : DataId -> ByteArray
```

Result type:

```text
SirResult =
  | Continue SirState
  | Halt SirState
  | Revert SirState
  | ExceptionalHalt SirState
  | InternalReturn (List Word256) SirState
  | Error String
```

This mirrors Venom's `OK`, `Halt`, `Abort Revert_abort`, `Abort ExHalt_abort`, `IntRet`, and `Error`.

See [SIR to bytecode correctness](../planning/sir-to-bytecode.md) for the state relation needed between this SIR state and EVMYulLean bytecode execution.

## What to Prove First

The first useful proof is probably not source-to-EVM end-to-end. Start at the lowest stable IR boundary:

1. Define executable SIR semantics.
2. Prove simple literal-op lowering correctness for operations where `as_literal_evm_op` returns `Some opcode`.
3. Prove special-op lowering correctness for `MemoryLoad`, `MemoryStore`, allocations, constants, data offsets, and internal calls.
4. Prove block/function simulation against emitted bytecode.
5. Prove pass simulations over SIR.
6. Then connect MIR-to-SIR lowering.

This mirrors Vyper-HOL's structure, where Venom gets its own semantics and only later connects to source Vyper and Verifereum EVM.
