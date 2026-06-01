# Lean-Based Models

## EVMYulLean

EVMYulLean is an executable Lean model of EVM and Yul. Its main design choice is a layered state model that mirrors Yellow Paper notation. See [EVM state model and Yellow Paper notation](./evm-state-model.md) for the expanded explanation of `sigma`, checkpoint state, machine state, and execution environment.

### State Layers

World/execution state:

```lean
structure State (tau : OperationType) where
  accountMap          : AccountMap tau
  sigma0              : AccountMap .EVM
  totalGasUsedInBlock : Nat
  transactionReceipts : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv tau
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Batteries.RBSet AccountAddress compare
```

Source: [`forks/EVMYulLean/EvmYul/State.lean`](../forks/EVMYulLean/EvmYul/State.lean)

Machine state:

```lean
structure MachineState where
  gasAvailable : UInt256
  activeWords  : UInt256
  memory       : ByteArray
  returnData   : ByteArray
  H_return     : ByteArray
```

Source: [`forks/EVMYulLean/EvmYul/MachineState.lean`](../forks/EVMYulLean/EvmYul/MachineState.lean)

Execution environment:

```lean
structure ExecutionEnv (tau : OperationType) where
  codeOwner : AccountAddress
  sender    : AccountAddress
  source    : AccountAddress
  weiValue  : UInt256
  calldata  : ByteArray
  code      : Yul.Ast.contractCode tau
  gasPrice  : Nat
  header    : BlockHeader
  depth     : Nat
  perm      : Bool
```

Source: [`forks/EVMYulLean/EvmYul/State/ExecutionEnv.lean`](../forks/EVMYulLean/EvmYul/State/ExecutionEnv.lean)

The EVM-specific state extends this with `pc`, `stack`, and `execLength`. This makes the executable EVM a program-counter-and-stack machine, while Yul uses the same world and machine state under a variable-store wrapper.

### EVM Semantics

The EVM semantics are an **interpreter-based small-step semantics** with fuel. A primitive transformer has shape:

```lean
def Transformer := EVM.State -> Except EVM.ExecutionException EVM.State
```

Then `step` executes one instruction:

```lean
def step (fuel : Nat) (gasCost : Nat)
  : EVM.Transformer :=
  match fuel with
  | 0 => fun _ => .error .OutOfFuel
  | .succ f => fun evmState => do
      let (instr, arg) <- fetchInstr evmState.toState.executionEnv evmState.pc
      let evmState := { evmState with execLength := evmState.execLength + 1 }
      match instr with
      | .CREATE => ...
```

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

This is "small step" because one call to `step` handles one EVM instruction. Larger Yellow Paper-style functions such as `X`, `Theta`, and `Upsilon` iterate or wrap the single-step semantics for message calls and transactions. See [Jargon and semantic styles](./jargon.md) for the distinction between `step`, `run`, big-step source evaluation, and relational proof layers.

### Yul Hook

Yul is not treated only as bytecode. The `OperationType` parameter chooses whether contract code is bytecode or a Yul contract:

```lean
abbrev contractCode (tau : OperationType) :=
  match tau with
  | .EVM => ByteArray
  | .Yul => YulContract
```

Source: [`forks/EVMYulLean/EvmYul/Yul/Ast.lean`](../forks/EVMYulLean/EvmYul/Yul/Ast.lean)

Yul has its own state wrapper:

```lean
inductive State where
  | Ok         : EvmYul.SharedState .Yul -> VarStore -> State
  | OutOfFuel : State
  | Checkpoint : Jump -> State
```

Source: [`forks/EVMYulLean/EvmYul/Yul/State.lean`](../forks/EVMYulLean/EvmYul/Yul/State.lean)

Yul execution is a **fuel-bounded interpreter over Yul syntax**, with mutually recursive expression and statement evaluators:

```lean
def eval (fuel : Nat) (expr : Expr) ... : Except Yul.Exception (State × Literal)
def exec (fuel : Nat) (stmt : Stmt) ... : Except Yul.Exception State
```

Source: [`forks/EVMYulLean/EvmYul/Yul/Interpreter.lean`](../forks/EVMYulLean/EvmYul/Yul/Interpreter.lean)

Design consequence: Yul is a useful intermediate target when the compiler already emits Yul-like structured code. Plank's SIR is lower-level than Verity's Yul layer and already has bytecode-oriented operations, so SIR should probably get its own semantics rather than being encoded as Yul just to reuse this interpreter.

## Verity

Verity is more compiler/EDSL-oriented than EVMYulLean. Its source semantics are intentionally abstract; its compiler/proof path lowers through IR and Yul toward EVMYulLean. The bridge is important enough to have its own page: [Verity to EVMYulLean bridge](./verity-bridge.md).

### Source Contract State

Verity source state is a high-level contract state, not a full EVM world:

```lean
structure ContractState where
  storage          : Nat -> Uint256
  transientStorage : Nat -> Uint256
  storageAddr      : Nat -> Address
  storageMap       : Nat -> Address -> Uint256
  storageMapUint   : Nat -> Uint256 -> Uint256
  storageMap2      : Nat -> Address -> Address -> Uint256
  storageArray     : Nat -> List Uint256
  sender           : Address
  thisAddress      : Address
  msgValue         : Uint256
  calldata         : List Nat := []
  memory           : Nat -> Uint256 := fun _ => 0
  events           : List Event := []
```

Source: [`forks/verity/Verity/Core.lean`](../forks/verity/Verity/Core.lean)

The contract monad is direct state-passing. The type parameter `alpha` is the return type of the computation:

```lean
abbrev Contract (alpha : Type) := ContractState -> ContractResult alpha
```

Source: [`forks/verity/Verity/Core.lean`](../forks/verity/Verity/Core.lean)

This is a big-step monadic source semantics: running a contract function computes a whole result from an initial `ContractState`.

### Typed IR

Verity also has a typed IR where ill-typed expressions are unrepresentable:

```lean
inductive Ty where
  | uint256 | address | bool | unit

structure TVar where
  id : Nat
  ty : Ty

inductive TExpr : Ty -> Type where
  | var (v : TVar) : TExpr v.ty
  | add (lhs rhs : TExpr .uint256) : TExpr .uint256
  | sender : TExpr .address
  | getStorage (slot : Nat) : TExpr .uint256
  | getMapping (slot : Nat) (key : TExpr .address) : TExpr .uint256
```

Source: [`forks/verity/Verity/Core/Free/TypedIR.lean`](../forks/verity/Verity/Core/Free/TypedIR.lean)

The typed IR has a fuel-bounded evaluator for statements:

```lean
def evalTStmtFuel : Nat -> TExecState -> TStmt -> TExecResult
  | 0, _, _ => .revert "out of fuel"
  | Nat.succ _, s, .setStorage slot value => ...
```

Source: [`forks/verity/Verity/Core/Free/TypedIR.lean`](../forks/verity/Verity/Core/Free/TypedIR.lean)

### Compiler Model and Yul

The compiler model describes Solidity-like contract structure:

```lean
inductive FieldType
  | uint256
  | address
  | dynamicArray (elemType : StorageArrayElemType)
  | mappingTyped (mt : MappingType)
  | mappingStruct (keyType : MappingKeyType) (members : List StructMember)
```

Source: [`forks/verity/Compiler/CompilationModel/Types.lean`](../forks/verity/Compiler/CompilationModel/Types.lean)

The simple IR is already Yul-shaped:

```lean
abbrev IRExpr := Yul.YulExpr
abbrev IRStmt := Yul.YulStmt

structure IRFunction where
  name     : String
  selector : Nat
  params   : List IRParam
  body     : List IRStmt
```

Source: [`forks/verity/Compiler/IR.lean`](../forks/verity/Compiler/IR.lean)

Compilation emits Yul statements:

```lean
def compileStmt ... : Stmt -> Except String (List YulStmt)
  | Stmt.letVar name value =>
      pure [YulStmt.let_ name (<- compileExpr fields dynamicSource value)]
  | Stmt.setStorage field value =>
      compileSetStorage fields dynamicSource field value
```

Source: [`forks/verity/Compiler/CompilationModel/Compile.lean`](../forks/verity/Compiler/CompilationModel/Compile.lean)

The useful lesson for Plank is that Verity separates:

- a comfortable source/contract model,
- a typed or structured IR model,
- a Yul/backend model,
- an explicit bridge to an EVM semantics.

That separation is a good pattern, but Plank's existing Rust SIR is already closer to the target than Verity's high-level contract model.

### Consequences for Plank

Verity's source semantics and EVMYulLean semantics are separate. The source side computes over `ContractState`; the native/backend side runs generated Yul in EVMYulLean and projects the result back to Verity observables. That is the relevant pattern:

- define a compact proof-side state for the language or IR being proved;
- lower to the target syntax or bytecode;
- build an EVMYulLean state from the proof-side state;
- compare observable results rather than demanding whole-world equality immediately.

For Plank, replace Verity's source `ContractState` with a SIR state and replace Verity's Yul lowering with SIR backend emission. The same bridge/projection idea should still apply.
