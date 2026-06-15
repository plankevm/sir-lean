# Jargon and Semantic Styles

This page is about the semantic styles used in these repos, not about names in the abstract. The same project may use several styles at once: an executable interpreter for computation, a relational layer for proofs, and state relations to connect languages.

## Small-step

A small-step semantics explains one atomic transition. For EVM this is naturally one opcode. For an IR it may be one instruction or one basic block, depending on the proof layer.

Canonical shape:

```text
step : State -> Except Error State
run  : State -> Option Result
```

`step` is not the whole semantics; `run` or a reflexive-transitive closure of `step` is what executes a program.

EVMYulLean uses this shape directly. Primitive opcode transformers are one-state transitions:

```lean
def Transformer := EVM.State -> Except EVM.ExecutionException EVM.State
```

Source: [`forks/EVMYulLean/EvmYul/EVM/PrimOps.lean`](../../forks/EVMYulLean/EvmYul/EVM/PrimOps.lean)

Its `step` is one decoded EVM instruction, guarded by Lean fuel:

```lean
def step (fuel : ℕ) (gasCost : ℕ)
  (instr : Option (Operation .EVM × Option (UInt256 × Nat)) := .none)
  : EVM.Transformer :=
  match fuel with
  | 0 => fun _ => .error .OutOfFuel
  | .succ f => fun evmState => do
    let (instr, arg) ← ...
    match instr with
    | .CREATE => ...
```

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

Verifereum has the same conceptual split in HOL: `step` fetches the opcode at the current program counter, dispatches it, then increments or jumps. `run` iterates `step`.

```sml
Definition step_def:
  step = handle do
    context <- get_current_context;
    code <<- context.msgParams.code;
    parsed <<- context.msgParams.parsed;
    if LENGTH code ≤ context.pc
    then step_inst Stop else
    do case FLOOKUP parsed context.pc of
      | NONE => step_inst Invalid
      | SOME op => do step_inst op; inc_pc_or_jump op od
    od
  od handle_step
End

Definition run_def:
  run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

Consequence: small-step is the right style for EVM bytecode and SIR-to-bytecode proof because each backend emission rule can be connected to either one opcode step or a bounded sequence of opcode steps.

## Big-step

A big-step semantics evaluates a complete phrase of the source language: an expression, statement, function call, or transaction. It does not expose each internal instruction transition as the primary theorem interface.

Canonical shape:

```text
eval_stmt : Context -> Stmt -> State -> Result State
eval_expr : Context -> Expr -> State -> Result (Value × State)
```

Vyper-HOL's source interpreter is big-step in this sense. `eval_stmt` consumes a whole source statement, recursively evaluating subexpressions and substatements:

```sml
Definition evaluate_def:
  eval_stmt cx Pass = return () /\
  eval_stmt cx Continue = raise ContinueException /\
  eval_stmt cx Break = raise BreakException /\
  eval_stmt cx (Return NONE) = raise $ ReturnException NoneV /\
  eval_stmt cx (Return (SOME e)) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    raise $ ReturnException v
  od /\ ...
```

Source: [`forks/vyper-hol/semantics/vyperInterpreterScript.sml`](../../forks/vyper-hol/semantics/vyperInterpreterScript.sml)

Consequence: big-step is convenient for source-language reasoning because source users care that a statement or external function call finishes with a certain state. It is awkward for bytecode correctness because the target semantics is inherently program-counter driven.

## Block-step and fuel-bounded IR execution

IR semantics often sits between small-step and big-step. Vyper-HOL's Venom semantics runs a block, then iterates blocks with explicit fuel:

```sml
Definition run_block_def:
  run_block fuel ctx bb s =
    case eval_phis s bb.bb_instructions of
      OK s_phi =>
        exec_block fuel ctx bb
          (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    | Error e => Error e
End
```

```sml
Theorem run_blocks_unfold:
  run_blocks (SUC fuel) ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb =>
        case run_block fuel ctx bb s of
          OK s' =>
            if s'.vs_halted then Halt s'
            else run_blocks fuel ctx fn s'
```

Source: [`forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml`](../../forks/vyper-hol/venom/defs/venomExecSemanticsScript.sml)

This is the closest precedent for Plank SIR: define instruction/block execution over SIR state, then relate backend-emitted bytecode to the SIR operation or block.

## Interpreter-based semantics

An interpreter-based semantics is an executable function inside the prover. It computes the next state or final result. In these repos, both Lean and HOL examples use error/state monadic style.

Lean example:

```lean
def Transformer := EVM.State -> Except EVM.ExecutionException EVM.State
```

HOL example:

```sml
Definition step_def:
  step = handle do
    context <- get_current_context;
    ...
  od handle_step
End
```

Why use it:

- it can run tests and examples;
- it makes determinism mostly obvious by construction;
- compiler theorems can target actual execution, not only an abstract relation.

Why it is not enough:

- proofs about partial state updates become noisy if every theorem mentions the entire machine state;
- equivalence between two languages still needs a relation between their states and results;
- fuel or `OWHILE` introduces termination/adequacy obligations.

## Fuel and partiality

Lean requires recursive definitions to be structurally accepted, so EVMYulLean puts `Nat` fuel on `step` and `X`. Fuel exhaustion is a meta-level timeout, not EVM gas:

```lean
def X (fuel : ℕ) (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State) := do
  match fuel with
  | 0 => .error .OutOfFuel
  | .succ f => ...
```

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

Verifereum uses `OWHILE`, whose result is optional. Nontermination or failure to find a loop result appears as `NONE` at the outer level:

```sml
Definition run_def:
  run s = OWHILE (ISL o FST) (step o SND) (INL (), s)
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../../forks/verifereum/spec/vfmExecutionScript.sml)

Vyper-HOL Venom uses explicit fuel for block iteration. That is often easier for compiler proofs because the theorem can quantify over enough fuel or prove a fuel-monotonicity lemma.

## Relational semantics and proof layers

A relational layer describes when two states, traces, or executions correspond. It is not just another interpreter. It is used when the proof needs abstraction, partial ownership of state, or comparison between different machines.

Verifereum's `prog/` layer converts concrete EVM execution states into a set of observable components:

```sml
Datatype:
  evm_el = Stack      (bytes32 list)
         | Memory     (byte list)
         | PC         num
         | ReturnData (byte list)
         | GasUsed    num
         | MsgParams  message_parameters
         | Exception  (unit + exception option)
         | Contexts   ((context # rollback_state) list)
         | Rollback   rollback_state
         | Msdomain   domain_mode
End
```

Source: [`forks/verifereum/prog/vfmProgScript.sml`](../../forks/verifereum/prog/vfmProgScript.sml)

It then packages the concrete interpreter step as a relation:

```sml
Definition EVM_NEXT_REL_def:
  EVM_NEXT_REL (s: unit execution_result) s' =
    ((if ISR (FST s) then s else step (SND s)) = s')
End

Definition EVM_MODEL_def:
  EVM_MODEL = (evm2set, EVM_NEXT_REL, EVM_INSTR,
               (λx y. x = (y:unit execution_result)),
               (K F):unit execution_result -> bool)
End
```

Source: [`forks/verifereum/prog/vfmProgScript.sml`](../../forks/verifereum/prog/vfmProgScript.sml)

Why put many components in one sum type? It lets the separation-logic/spec framework talk about selected pieces of EVM state as resources. A local opcode spec can mention stack, memory, gas, and pc without having to restate every account and transaction field. The set representation also makes hiding/projection possible.

Vyper-HOL uses relations for compiler correctness. The theorem shape relates source execution to Venom execution; it is not trying to run one interpreter inside the other:

```sml
external_call_result_rel tenv cenv
  (initial_evaluation_context am.sources am.layouts tx)
  ret (call_external am tx) (run_context fuel ctx vs)
```

Source: [`forks/vyper-hol/venom/compiler/compilerCorrectnessDraftScript.sml`](../../forks/vyper-hol/venom/compiler/compilerCorrectnessDraftScript.sml)

Consequence for Plank: use executable SIR semantics for testing and direct proofs, but use relations for the compiler theorem:

```text
sir_state_rel : SirState -> EvmState -> Prop
result_rel    : SirResult -> EvmResult -> Prop
```

The interpreter computes. The relation explains which parts of two different machines are supposed to mean the same thing.
