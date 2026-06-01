# Horizontal Concept Comparison

This page compares the same EVM concepts across the Lean and HOL repos.

## State Granularity

| Concept | EVMYulLean | Verifereum | Verity | Vyper-HOL |
|---|---|---|---|---|
| Accounts | `AccountMap tau` | `address -> account_state` | not full account world at source level | reuses Verifereum `evm_accounts` |
| Storage | per-account storage map | `bytes32 -> bytes32` | several function-valued storage surfaces | source layouts plus Verifereum storage |
| Memory | `ByteArray` in `MachineState` | byte list in current context | word-addressed source memory | byte list in Venom and Verifereum |
| Stack | EVM state has `Stack UInt256` | current context has `stack` | no source stack | Venom is register/SSA, not stack |
| PC | EVM state has `pc` | current context has `pc` | no source PC | Venom has `vs_current_bb` and `vs_inst_idx` |
| Calldata | `ExecutionEnv.calldata` | `message_parameters.data` | `ContractState.calldata` words | source tx args and Venom call context calldata |
| Calls | EVM/Yul call semantics | `step_call`, context stack | abstract/oracle or compiler Yul | source `run_ext_call` calls Verifereum |

## Storage

EVM storage is per-account persistent key-value storage. Both direct EVM models choose total maps with zero defaults.

Verifereum:

```sml
Type storage = ":bytes32 -> bytes32";
Definition empty_storage_def:
  empty_storage: bytes32 -> bytes32 = K 0w
End
```

EVMYulLean uses an ordered map representation:

```lean
abbrev StorageMap := Batteries.RBMap UInt256 UInt256 compare
```

Verity is much more abstract. It exposes multiple typed storage surfaces:

```lean
storage        : Nat -> Uint256
storageMap     : Nat -> Address -> Uint256
storageMap2    : Nat -> Address -> Address -> Uint256
storageArray   : Nat -> List Uint256
```

For a Plank IR model, use an EVM-shaped storage model at the SIR boundary: account-address plus slot to word. Higher-level helpers can be proved to implement layouts over this map.

## Memory

EVM memory is transient per call frame and byte-addressed. EVMYulLean stores it as a `ByteArray`; Verifereum and Vyper-HOL Venom use byte lists.

Verifereum explicitly separates memory expansion from reads/writes:

```sml
Definition memory_expansion_info_def:
  memory_expansion_info offset size = do
    context <- get_current_context;
    oldSize <<- LENGTH context.memory;
    newMinSize <<- if 0 < size then word_size (offset + size) * 32 else 0;
    return <| cost := memory_expansion_cost oldSize newMinSize;
              expand_by := MAX oldSize newMinSize - oldSize |>
  od
End
```

Plank SIR has both literal EVM memory operations and IR-level allocation operations. This suggests two semantic layers:

- Pure SIR memory semantics for `malloc`, `mloadN`, `mstoreN`, `mcopy`.
- Lowering proof that these operations compile to EVM memory instructions preserving memory bytes and observable behavior.

## Calls and Reentrancy

Reentrancy is not a primitive opcode. It emerges from:

- persistent storage,
- cross-contract calls,
- callbacks before or after state updates,
- call-depth/context stacks,
- revert/rollback behavior,
- transient storage locks.

Verifereum models calls by pushing/popping EVM contexts and rolling state back on revert. Vyper-HOL source calls can enter Verifereum through `run_ext_call`:

```sml
Definition run_ext_call_def:
  run_ext_call caller callee calldata value_opt accounts tStorage txParams =
    let code = (lookup_account callee accounts).code in
    let s0 = make_ext_call_state caller callee code calldata value_opt
                                 accounts tStorage txParams in
    case vfmExecution$run_call s0 of
    | SOME (result, final_state) =>
        extract_call_result accounts tStorage (result, final_state)
    | NONE => NONE
End
```

Source: [`forks/vyper-hol/semantics/vyperInterpreterScript.sml`](../forks/vyper-hol/semantics/vyperInterpreterScript.sml)

For Plank, any semantics for `call`, `delegatecall`, `staticcall`, `callcode`, `create`, and `create2` needs a world of accounts and a call-frame stack, even if most initial proofs abstract the callee.

## Return, Revert, and Exceptional Halt

You should distinguish at least:

- normal continuation,
- normal halt/return,
- revert with return data and state rollback,
- exceptional halt such as invalid/out-of-gas,
- meta-level timeout/fuel exhaustion.

Vyper-HOL Venom makes this distinction explicit:

```sml
Datatype:
  abort_type =
    | Revert_abort
    | ExHalt_abort

Datatype:
  exec_result =
    | OK venom_state
    | Halt venom_state
    | Abort abort_type venom_state
    | IntRet (bytes32 list) venom_state
    | Error string
End
```

Source: [`forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml`](../forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml)

This is a good shape for Plank SIR too. Do not collapse revert and exceptional halt if the goal is EVM correctness.

## Gas

EVMYulLean and Verifereum both track gas, but many source-level models abstract it. Verifereum is closer to real EVM gas accounting because each context tracks `gasUsed` and gas-limit-derived remaining gas.

For Plank, a pragmatic staged approach:

1. Define gas-erased functional correctness for most IR lowering.
2. Preserve halt/revert/return behavior and observable state.
3. Add gas accounting later for operations where gas-sensitive behavior affects success, failure, or call stipend.

This is defensible because many compiler correctness proofs first prove semantic preservation under adequate gas, then separately prove gas bounds or gas monotonicity.

