# Experiment 001 Wrong Attempts

This file records mistakes in the toy SIR/EVM lowering attempt so future work does not repeat them.

## Opcode Trace Shortcut

An earlier module proved facts about an opcode-trace/primitive-step shortcut rather than bytecode execution through EVMYulLean `EVM.X`.

Why it was wrong:

- the requested target was bytecode execution;
- opcode traces bypass decoding, program counters, gas prechecks, halting, and `CALL` setup;
- proving against the shortcut did not establish anything about the actual lowered bytecode.

Fix:

- remove the shortcut module;
- keep `Bytecode.lower : Program -> ByteArray`;
- state target execution only through `EVM.X`.

Current status:

- `Correctness.lowerOps_preserve_semantics` is now a checked theorem over `Bytecode.lowerOps : Program -> List Bytecode.Op`;
- this is still not the final `EVM.X` theorem over assembled `ByteArray`;
- the remaining bytecode theorem must prove that EVMYulLean execution of `Bytecode.lower program` implements the structured lowered semantics.

## Unproved Spec Mistaken For Progress

After removing the opcode-trace shortcut, the next attempt stated a bytecode-level preservation spec without proving it.

Why it was wrong:

- a `Prop` definition is not a compiler-correctness result;
- it can hide missing decoding, PC, gas, memory-layout, and call lemmas;
- it gives no Lean evidence that the compiler works.

Fix:

- keep `LoweringPreservationSpec` only as the explicit future target;
- add the checked theorem `lowerOps_preserve_semantics`;
- treat the structured target theorem as an intermediate compiler proof, not as the EVM bytecode theorem.

## Unrestricted EVM.X Preservation

A theorem directly comparing current source `run` with `EVM.X (Bytecode.lower program)` for all programs and all initial states is false.

Why it is wrong:

- source `run` ignores gas, but `EVM.X` checks `memoryExpansionCost` and `C'` before every step;
- with zero target gas, a source program like `inputLoad 0 (const 0)` can succeed while lowered bytecode fails before executing its first `PUSH32`;
- source calls use an arbitrary `CallOracle`, but real `CALL` can only produce EVMYulLean call behavior and pushes a success word determined by that behavior.

Fix:

- either change the source semantics so gas and calls are EVM-backed;
- or prove a bytecode theorem under explicit enough-gas, exact-call, and memory-frame hypotheses.

## Canonical-Only Lowering

The first `Bytecode.lower` recognized only one or two hard-coded canonical programs and returned `none` for everything else.

Why it was wrong:

- it was not a compiler for the IR;
- it made the preservation statement about a hand-picked example rather than `Program`;
- it hid real local/register allocation issues.

Fix:

- make `Bytecode.lower` total over every `Program`;
- lower operands generically;
- store source locals in reserved EVM memory slots.

## Infinite Local Relation

The first state relation compared every `Nat` local:

```lean
∀ x, evm.lookupMemory (localSlot x) = locals x
```

Why it was wrong:

- bytecode can only initialize/use finitely many locals;
- arbitrary source states have infinitely many local values;
- full equality of all locals is stronger than the program can observe.

Fix:

- collect finite local sets from syntax;
- compare only `program.touchedLocals`.

## Uninitialized Source Locals

The source interpreter read locals from `ToyState.locals`, but the lowered bytecode read locals from EVM memory.

Why it was wrong:

- the initial EVM state did not encode source locals;
- any program reading a preexisting local could disagree immediately.

Fix:

- `withLoweredCodeAndLocals` seeds EVM memory for `program.readLocals` before execution.

## Arbitrary EVM Fuel

The earlier spec quantified over arbitrary `evmFuel`.

Why it was wrong:

- with `evmFuel = 0`, even the empty lowered program returns `OutOfFuel`;
- the source run can still succeed.

Fix:

- remove arbitrary target fuel from the preservation spec;
- use `Bytecode.lowerFuel program`.

## Arbitrary Call Oracle

The source semantics uses a `CallOracle`, but lowered bytecode uses real EVM `CALL`.

Why it was wrong:

- an arbitrary oracle can return any state, returndata, or success flag;
- real EVM bytecode cannot preserve arbitrary oracle behavior.

Fix:

- add `CallOracleSoundForLowering oracle`, relating oracle answers to EVMYulLean `EVM.call`;
- keep call preservation as an explicit proof obligation.

## Reserved Local Memory Clobbering

The total lowerer stores locals in reserved memory slots starting at `1048576`.

Why it was wrong to ignore:

- EVM calls can write returndata into caller memory;
- if `outOffset/outSize` overlaps reserved local slots, lowered locals can be corrupted;
- source locals are not stored in EVM memory, so source semantics would not see this corruption.

Fix:

- add `CallOraclePreservesReservedLocalSlots oracle program.touchedLocals`;
- later replace this assumption with a stronger memory-frame/layout discipline.

## Sequence-Specific EVM.X Lemmas

The bytecode proof attempt started adding hand-written `EVM.X` theorems for concrete bytecode fragments such as `PUSH32; STOP`.

Why that was wrong:

- EVMYulLean already gives the executable semantics through `EVM.X`; duplicating one theorem per bytecode sequence scales badly;
- sequence-specific lemmas hide the proof architecture needed for a compiler theorem over every `Program`;
- the reusable fact is not "this particular byte string runs", but "if decode, gas precheck, step, and halting classification line up, then `EVM.X` advances or halts accordingly."

Fix:

- factor EVMYulLean's local `X` helpers into named definitions `EVM.Z` and `EVM.H`;
- prove generic local lemmas `EVMBytecode.evmX_continue` and `EVMBytecode.evmX_halt_success`;
- keep opcode-specific facts at the `decode` and `EVM.step` layers, where they are actually reusable.
