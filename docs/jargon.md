# Jargon and Semantic Styles

## Operational Semantics

An operational semantics says how programs execute. In these repos it usually appears as executable functions over an explicit machine state, rather than paper inference rules.

Two common styles:

- **Small-step semantics**: one transition performs one machine or IR step. Example shape: `step : State -> Result State`.
- **Big-step semantics**: one evaluator consumes a whole expression, statement, function, or transaction. Example shape: `evalStmt : State -> Result State`, recursively evaluating subterms.

## Interpreter-Based Semantics

Most code here is a **definitional interpreter**: a total-ish function in Lean or HOL that directly computes the semantics. This is practical because EVM execution is naturally deterministic.

The interpreter is often **monadic**. That means the code uses `bind`/`return` or Lean `Except`/`StateT` to sequence state updates and propagate errors.

Example from Verifereum:

```sml
Type execution_result = ":(alpha + exception option) # execution_state";

Definition bind_def:
  bind g f s : alpha execution_result =
    case g s of
    | (INR e, s) => (INR e, s)
    | (INL x, s) => f x s
End
```

Source: [`forks/verifereum/spec/vfmExecutionScript.sml`](../forks/verifereum/spec/vfmExecutionScript.sml)

## Fuel-Bounded Evaluation

Lean requires recursive definitions to be accepted as terminating. EVM/Yul execution can loop, so EVMYulLean and Verity often use a `fuel : Nat` argument. Running out of fuel is a meta-level execution bound, not an EVM opcode.

Example from EVMYulLean:

```lean
def step (fuel : Nat) (gasCost : Nat)
  : EVM.Transformer :=
  match fuel with
  | 0 => fun _ => .error .OutOfFuel
  | .succ f => fun evmState => do
      let (instr, arg) <- fetchInstr evmState.toState.executionEnv evmState.pc
      ...
```

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

## Relational Semantics

A relational semantics defines a relation between before and after states rather than computing a result. Verifereum layers a relation over its executable interpreter:

```sml
Definition EVM_NEXT_REL_def:
  EVM_NEXT_REL (s: unit execution_result) s' =
    ((if ISR (FST s) then s else step (SND s)) = s')
End
```

Source: [`forks/verifereum/prog/vfmProgScript.sml`](../forks/verifereum/prog/vfmProgScript.sml)

This is useful for Hoare-style specs, simulation proofs, and extracting per-component state assertions.

## Refinement and Simulation

A compiler proof normally relates two executions:

- Source execution: high-level semantics.
- Target execution: IR, assembly, bytecode, or EVM semantics.

The proof obligation is usually a **simulation** or **refinement**: every target execution corresponds to a source execution, or vice versa, preserving observable behavior.

Vyper-HOL names this directly:

```sml
(* Connects Vyper big-step semantics (call_external) to Venom IR
 * execution (run_context) on the context produced by run_lowering. *)
```

Source: [`forks/vyper-hol/lowering/vyperLoweringCorrectScript.sml`](../forks/vyper-hol/lowering/vyperLoweringCorrectScript.sml)

For Plank, the same proof shape should be: Plank IR execution simulates or refines execution of the lowered EVM bytecode, under an explicit relation between Plank IR state and EVM state.

