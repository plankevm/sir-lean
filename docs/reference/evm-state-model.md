# EVM State Model and Yellow Paper Notation

EVM formalizations tend to separate three levels of state:

- world state: accounts, balances, code, persistent storage;
- execution environment: calldata, caller, call value, current code, block header, static-call permission;
- machine state: stack, memory, program counter, gas, returndata for the current frame.

The Yellow Paper gives these pieces compact Greek names. EVMYulLean mirrors those names in comments and fields.

## EVMYulLean World State

`State tau` is the shared world/execution state. The comments identify the Yellow Paper names:

```lean
/--
The `State`. Section 9.3.

- `accountMap`   `sigma`
- `substate`     `A`
- `executionEnv` `I`
- `totalGasUsedInBlock` `Upsilon_g`
-/
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

Source: [`forks/EVMYulLean/EvmYul/State.lean`](../../forks/EVMYulLean/EvmYul/State.lean)

The actual field name is `sigma0` in this excerpt only because this documentation uses ASCII. In the source it is written as `σ₀`.

## Checkpoint State

`sigma0`/`σ₀` is the checkpoint account map used for transaction semantics and gas accounting. EVMYulLean creates it after charging the sender upfront:

```lean
-- The checkpoint state (73)
let sigma0 := sigma.insert sender senderAccount
```

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

Consequence: if a Plank proof relates SIR state directly to EVMYulLean transaction execution, it must account for precharged gas, nonce increment, checkpoint state, and rollback behavior. For early SIR-to-bytecode proofs, it is usually easier to target message-call execution or a prepared EVM frame.

## Machine State

Machine state is the per-frame execution machinery. It is not the account map; it is closer to the current VM activation record.

```lean
/--
The partial shared `MachineState` `mu`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `activeWords`  `i` - # active words.
- `returnData`   `o` - Data from the previous call from the current environment.
-/
structure MachineState where
  gasAvailable : UInt256
  activeWords  : UInt256
  memory       : ByteArray
  returnData   : ByteArray
  H_return     : ByteArray
```

Source: [`forks/EVMYulLean/EvmYul/MachineState.lean`](../../forks/EVMYulLean/EvmYul/MachineState.lean)

The EVM-specific state then adds program counter and operand stack:

```lean
structure State extends EvmYul.SharedState .EVM where
  pc         : UInt256
  stack      : Stack UInt256
  execLength : Nat
```

Source: [`forks/EVMYulLean/EvmYul/EVM/State.lean`](../../forks/EVMYulLean/EvmYul/EVM/State.lean)

Consequence: a SIR state should not be forced to contain a program counter and stack just because the final bytecode does. SIR has locals and CFG blocks. The compiler-correctness relation should explain how locals are represented on the EVM stack/memory at a particular bytecode program counter.

## HOL Verifereum Frame State

Verifereum makes the call frame explicit as a `context` record:

```sml
Datatype:
  context =
  <| stack      : bytes32 list
   ; memory     : byte list
   ; pc         : num
   ; jumpDest   : num option
   ; returnData : byte list
   ; gasUsed    : num
   ; addRefund  : num
   ; subRefund  : num
   ; logs       : event list
   ; msgParams  : message_parameters
   |>
End
```

Source: [`forks/verifereum/spec/vfmContextScript.sml`](../../forks/verifereum/spec/vfmContextScript.sml)

The full execution state is a stack of contexts plus rollback and transaction data:

```sml
Datatype:
  execution_state =
  <| contexts : (context # rollback_state) list
   ; txParams : transaction_parameters
   ; rollback : rollback_state
   ; msdomain : domain_mode
   |>
End
```

Source: [`forks/verifereum/spec/vfmContextScript.sml`](../../forks/verifereum/spec/vfmContextScript.sml)

Consequence: Verifereum is a useful reference for the minimum shape of a full EVM semantics. It also shows why reimplementing EVM in Lean is not a small task: call stack, rollback, gas, memory, returndata, logs, and transaction state are all semantic, not incidental.

