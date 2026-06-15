# HOL-Based Models

## Verifereum

Verifereum is the direct HOL EVM model. It is executable, monadic, and small-step at the opcode level.

### Account and Storage Model

Storage is a total map from 256-bit words to 256-bit words:

```sml
Type storage = ":bytes32 -> bytes32";

Definition lookup_storage_def:
  lookup_storage k (s: storage) = s k
End
```

Source: [`forks/verifereum/spec/vfmStateScript.sml`](../../forks/verifereum/spec/vfmStateScript.sml)

Accounts are total by address and contain nonce, balance, storage, and code:

```sml
Datatype:
  account_state =
  <| nonce   : num
   ; balance : num
   ; storage : storage
   ; code    : byte list
   |>
End

Type evm_accounts = ":address -> account_state"
```

Source: [`forks/verifereum/spec/vfmStateScript.sml`](../../forks/verifereum/spec/vfmStateScript.sml)

### Memory, Storage, and Calls

Memory is byte-list based and explicitly expanded:

```sml
Definition expand_memory_def:
  expand_memory expand_by = do
    context <- get_current_context;
    set_current_context $
      context with memory := context.memory ++ REPLICATE expand_by 0w
  od
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

Storage writes update the account map:

```sml
Definition write_storage_def:
  write_storage address key value =
  update_accounts (lambda accounts.
    let account = lookup_account address accounts in
    let newAccount = account with storage updated_by (update_storage key value);
    in update_account address newAccount accounts)
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

Calls are modeled inside the opcode-level small-step semantics by a large `step_call` handler. This is not "big-step semantics"; it is one EVM instruction whose one-step effect is large because `CALL` itself creates a new call frame. The handler consumes stack arguments, computes memory expansion and gas, checks value/static/depth conditions, then pushes a new call context or aborts.

```sml
Definition step_call_def:
  step_call op = do
    valueOffset <<- if call_has_value op then 1 else 0;
    args <- pop_stack (6 + valueOffset);
    gas <<- w2n $ EL 0 args;
    address <<- w2w $ EL 1 args;
    ...
    proceed_call op sender address value argsOffset argsSize code stipend
      (Memory <| offset := retOffset; size := retSize |>)
  od
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

Return/revert from a nested frame is handled by popping the current context and either incorporating logs/refunds or restoring rollback state:

```sml
Definition pop_and_incorporate_context_def:
  pop_and_incorporate_context success = do
    calleeGasLeft <- get_gas_left;
    callee_rb <- pop_context;
    callee <<- FST callee_rb;
    unuse_gas calleeGasLeft;
    if success then do
      push_logs callee.logs;
      update_gas_refund (callee.addRefund, callee.subRefund)
    od else
      set_rollback (SND callee_rb)
  od
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

### Small-Step EVM

Opcode semantics are dispatched by `step_inst`. The main `step` fetches the opcode at the current `pc`, executes it, and increments or jumps:

```sml
Definition step_def:
  step = handle do
    context <- get_current_context;
    code <<- context.msgParams.code;
    parsed <<- context.msgParams.parsed;
    if LENGTH code <= context.pc
    then step_inst Stop else
    do case FLOOKUP parsed context.pc of
      | NONE => step_inst Invalid
      | SOME op => do step_inst op; inc_pc_or_jump op od
    od
  od handle_step
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

`run` iterates `step` until termination:

```sml
Definition run_def:
  run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

### Spec Layer

The `prog/` layer projects execution states into sets of state components and packages a one-step relation:

```sml
Datatype:
  evm_el = Stack (bytes32 list)
         | Memory (byte list)
         | PC num
         | ReturnData (byte list)
         | GasUsed num
         | MsgParams message_parameters
         | Contexts ((context # rollback_state) list)
         | TxParams transaction_parameters
End
```

Source: [`forks/verifereum/prog/vfmProgScript.sml`](../../forks/verifereum/prog/vfmProgScript.sml)

This layer is useful when proving local specs without exposing the entire record state every time. The reason all components live in one sum type is that the generic `prog`/separation-logic machinery wants a set of resources. `Stack`, `Memory`, `PC`, `ReturnData`, `GasUsed`, and `MsgParams` become independently mentionable resources rather than fields in one indivisible record.

The next relation still wraps the executable interpreter:

```sml
Definition EVM_NEXT_REL_def:
  EVM_NEXT_REL (s: unit execution_result) s' =
    ((if ISR (FST s) then s else step (SND s)) = s')
End
```

Source: [`forks/verifereum/prog/vfmProgScript.sml`](../../forks/verifereum/prog/vfmProgScript.sml)

Design consequence: Verifereum pays for extra projection infrastructure but gains local Hoare/separation-style specifications. EVMYulLean currently gives a more direct executable model but not this mature relational wrapper.

## Vyper-HOL

Vyper-HOL reuses Verifereum's EVM definitions and adds a source semantics, Venom IR semantics, lowering correctness, optimization simulations, and codegen correctness statements.

### Source Vyper State

The source interpreter state keeps scopes plus externally visible EVM-like state:

```sml
Datatype:
  evaluation_state = <|
    immutables : (address, module_immutables) alist;
    logs       : log list;
    scopes     : scope list;
    accounts   : evm_accounts;
    tStorage   : transient_storage
  |>
End
```

Source: [`forks/vyper-hol/semantics/vyperStateScript.sml`](../../forks/vyper-hol/semantics/vyperStateScript.sml)

The whole source-level abstract machine stores deployed sources, exports, layouts, accounts, transient storage, and logs:

```sml
Datatype:
  abstract_machine = <|
    sources  : (address, (num option, toplevel list) alist) alist;
    exports  : (address, (string, num) alist) alist;
    accounts : evm_accounts;
    layouts  : (address, storage_layout # storage_layout) alist;
    tStorage : transient_storage;
    logs     : log list
  |>
End
```

Source: [`forks/vyper-hol/semantics/vyperInterpreterScript.sml`](../../forks/vyper-hol/semantics/vyperInterpreterScript.sml)

### Source Semantics

The main source semantics are a **big-step monadic interpreter**:

```sml
Definition evaluate_def:
  eval_stmt cx Pass = return () /\
  eval_stmt cx Continue = raise ContinueException /\
  eval_stmt cx (Return (SOME e)) = do
    tv <- eval_expr cx e;
    raise $ ReturnException (get_Value tv)
  od /\
  eval_stmts cx [] = return () /\
  eval_stmts cx (s::ss) = do eval_stmt cx s; eval_stmts cx ss od
```

Source: [`forks/vyper-hol/semantics/vyperInterpreterScript.sml`](../../forks/vyper-hol/semantics/vyperInterpreterScript.sml)

There is also a CPS/small-step-flavored source semantics with explicit continuations:

```sml
Datatype:
  eval_continuation
  = ReturnK eval_continuation
  | AssertK assert_reason eval_continuation
  | IfK (stmt list) (stmt list) eval_continuation
  | ExtCallK bool identifier (type list) type (expr option) eval_continuation
  | IntCallK ... eval_continuation
  | DoneK
End
```

Source: [`forks/vyper-hol/semantics/vyperSmallStepScript.sml`](../../forks/vyper-hol/semantics/vyperSmallStepScript.sml)

### Venom IR

Venom is register/SSA-style and explicitly CFG-based:

```sml
Datatype:
  opcode =
    | ADD | SUB | MUL | Div | SDIV | Mod
    | MLOAD | MSTORE | MCOPY | MEMTOP
    | SLOAD | SSTORE
    | TLOAD | TSTORE
    | JMP | JNZ | DJMP | RET | RETURN | REVERT | STOP
    | PHI | PARAM | ASSIGN | NOP
    | INVOKE
    | CALLER | CALLVALUE | CALLDATALOAD | CALLDATASIZE
    | CALL | STATICCALL | DELEGATECALL | CREATE | CREATE2
End
```

Source: [`forks/vyper-hol/venom/defs/venomInstScript.sml`](../../forks/vyper-hol/venom/defs/venomInstScript.sml)

Venom state contains memory, SSA variables, control-flow position, returndata, accounts, transient storage, contexts, logs, data section, code, parameters, and allocation metadata:

```sml
Datatype:
  venom_state = <|
    vs_memory     : byte list;
    vs_transient  : transient_storage;
    vs_vars       : var_env;
    vs_current_bb : string;
    vs_inst_idx   : num;
    vs_returndata : byte list;
    vs_accounts   : evm_accounts;
    vs_call_ctx   : call_context;
    vs_tx_ctx     : tx_context;
    vs_block_ctx  : block_context;
    vs_logs       : event list
  |>
End
```

Source: [`forks/vyper-hol/venom/defs/venomStateScript.sml`](../../forks/vyper-hol/venom/defs/venomStateScript.sml)

Venom execution is small-step at the instruction level and block-step at the CFG level:

```sml
Definition run_defs:
  (step_inst fuel ctx inst s =
    if inst.inst_opcode = INVOKE then ... else step_inst_base inst s)
  /\
  (exec_block fuel ctx bb s =
    case get_instruction bb s.vs_inst_idx of
    | NONE => Error "block not terminated"
    | SOME inst => ...)
  /\
  (run_blocks fuel ctx fn s =
    case fuel of
    | 0 => Error "out of fuel"
    | SUC fuel' => ...)
End
```

Source: [`forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml`](../../forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml)

### Lowering Correctness Shape

The top-level lowering file states the intended theorem as a relation between source execution and Venom execution:

```sml
Theorem vyper_to_venom_correct:
  !tenv selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    vs am tx sel fn_lbl htz cenv
    args dflts ret body mut nr.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    ...
    ==>
    ?fuel.
      external_call_result_rel tenv cenv
        (initial_evaluation_context am.sources am.layouts tx)
        ret (call_external am tx) (run_context fuel ctx vs)
```

Source: [`forks/vyper-hol/lowering/vyperLoweringCorrectScript.sml`](../../forks/vyper-hol/lowering/vyperLoweringCorrectScript.sml)

The proof is currently `cheat`ed, so this is a blueprint rather than completed evidence that the bridge is easy.

The codegen relation layer is even more directly relevant to Plank SIR-to-bytecode:

```sml
Definition plan_stack_rel_def:
  plan_stack_rel label_offsets vs ps_stack asm_stack <=>
    LENGTH ps_stack = LENGTH asm_stack /\
    !i. i < LENGTH ps_stack ==>
      let op = EL i (REVERSE ps_stack) in
      let val = EL i asm_stack in
      operand_val vs label_offsets op = SOME val
End

Definition venom_asm_rel_def:
  venom_asm_rel label_offsets ps vs as <=>
    plan_stack_rel label_offsets vs ps.ps_stack as.as_stack /\
    plan_spill_rel label_offsets vs ps.ps_spilled as.as_memory /\
    memory_rel ps.ps_alloc vs.vs_memory as.as_memory /\
    as.as_accounts = vs.vs_accounts /\
    as.as_transient = vs.vs_transient /\
    as.as_returndata = vs.vs_returndata /\
    as.as_logs = vs.vs_logs
End
```

Source: [`forks/vyper-hol/venom/codegen/defs/codegenRelScript.sml`](../../forks/vyper-hol/venom/codegen/defs/codegenRelScript.sml)

The result relation should include externally observable effects: storage/accounts, transient storage, logs, returndata, return/revert/exception mode, and call context. For Plank, see [SIR to bytecode correctness](../planning/sir-to-bytecode.md).
