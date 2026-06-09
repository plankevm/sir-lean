# Experiment 001 Findings

## What Built

The package builds as a local Lake package against `../../forks/EVMYulLean` with Lean `v4.22.0`.

```text
lake build
```

The implemented artifact is intentionally small:

- `Operand`: local or constant word;
- `Instr.inputLoad`: load one EVM calldata word into a local;
- `Instr.add`: add two word operands using `UInt256` arithmetic;
- `Instr.call`: evaluate the seven EVM `CALL` operands and delegate the call boundary to an oracle;
- `run`: fuel-bounded interpreter over a linear list of instructions.
- `Bytecode.lowerOps`: a total compiler from the existing `Program` type to a structured EVM-like target instruction list.
- `Bytecode.lower`: assembly from that structured instruction list to EVM bytecode.
- `Correctness.lowerOps_preserve_semantics`: a checked theorem, with no `sorry`, proving source semantics are preserved by `lowerOps` for every `Program`.
- `EVMBytecode`: checked decode lemmas for generated one-byte EVM opcodes.
- `Obstruction`: checked counterexample showing the current source semantics cannot be preserved by `EVM.X` for all initial EVM states because source execution is not gas-aware.
- `EVMBridgeSpec.LoweringPreservationSpec`: the remaining, unproved target spec relating source `run` to EVMYulLean `EVM.X` on `Bytecode.lower`.

## Main Design Decisions

### CALL Is An Instruction

The toy IR models external call as `Instr.call`. The `CallArgs` structure only bundles the seven EVM operands:

```text
gas, target, value, inOffset, inSize, outOffset, outSize
```

This answers the review concern: `CALL` is an EVM opcode and a SIR operation, not a meta-level expression. The struct is just a typed way to keep the operand list readable.

### State Is EVMYulLean State Plus Locals

The implemented state is:

```lean
structure ToyState where
  evm : EVM.State
  locals : Local -> Word
```

This commits to the review decision to use EVMYulLean memory, returndata, gas, account map, substate, and execution environment from day one. It avoids a parallel toy account or memory model and should make the first bytecode relation less artificial.

### Call Failure Is A Success Flag

The call oracle has this shape:

```lean
CallOracle : ToyState -> CallRequest -> Except EVM.ExecutionException CallResult
```

`CallResult.successFlag` is the exact `UInt256` word that EVM `CALL` pushes. In practice this is `0` for failure and `1` for success, but keeping the word avoids an unnecessary Boolean translation once we prove lowering. The toy interpreter continues and writes that flag to the destination local. The `Except` channel is reserved for caller-level exceptional halt.

This matters because callee revert is not the same thing as the caller reverting.

### Memory And Returndata Are Present

`CallRequest.input` is read from `s.evm.memory` using `inOffset` and `inSize`. `CallRequest` also keeps both `targetWord` and `target`: EVM receives a 256-bit stack word and converts it to a 160-bit account address internally. `CallResult.returnData` updates `s.evm.returnData`. Output copying through `outOffset` and `outSize` is not proved yet; the current oracle can include that update in the returned `EVM.State`.

The next theorem should make output copying explicit, at least as an observable memory-slice relation.

## What Changed From The Initial Plan

- The plan originally showed a separate EVM-shaped toy state. The implementation now uses full `EVM.State`.
- The plan originally risked treating callee revert as a top-level toy result. The implementation instead follows EVM `CALL`: failure is a `0` success flag.
- The first implementation stored call success as `Bool`; the model now stores the exact EVM success word so future lowering can compare against the EVM stack result directly.
- The plan used `to` as an operand name. Lean rejected it in this context, so the implementation uses `target`.
- `UInt256` does not use plain numeral notation here, so constants are written with `UInt256.ofNat`.

## Removed False Starts

An earlier `ToyExternalCall.Lowering` module was removed because it proved preservation only against an opcode-trace/primitive-step shortcut. That was not the requested theorem and it was not a clean model of lowering to bytecode.

The replacement uses the existing `Instr`/`Program` IR and produces `ByteArray`. It does not prove preservation against an opcode trace.

The next attempted theorem over bytecode also had a false shape: it stated an `EVM.X` preservation proposition without proving it. That is not useful as compiler formalization. The current checked theorem is intentionally narrower but real:

```lean
theorem lowerOps_preserve_semantics
    (oracle : CallOracle)
    (program : Program)
    (initial : ToyState) :
    runLoweredOps oracle { toy := initial, stack := [] } (Bytecode.lowerOps program) =
      run oracle (program.length + 1) initial program
```

This theorem says: for every toy IR program, running its structured lowered target program gives exactly the same `RunResult` as running the source interpreter with enough source fuel. It is proved by induction over `Program`, using instruction-level lemmas for operand compilation and instruction compilation.

## Current Lowering Status

The lowering has two levels:

```lean
Bytecode.lowerOps : Program -> List Bytecode.Op
Bytecode.lower : Program -> ByteArray
```

`lowerOps` is the target language currently used by the checked preservation theorem. It is structured enough to avoid re-proving byte decoding, program-counter movement, and EVM gas behavior before the core compiler proof exists.

The target `CALL` op in `lowerOps` does not carry `CallArgs`. The compiler lowers all seven call operands onto the target stack, and `CALL` pops:

```text
gas, target, value, inOffset, inSize, outOffset, outSize
```

The preservation proof therefore checks the operand order and call-request reconstruction instead of assuming the source call bundle survives lowering.

`lower` assembles those lowered operations into bytecode:

```lean
Bytecode.lower : Program -> ByteArray
```

Both functions handle every syntactically possible toy IR program. They do this by compiling each instruction independently and storing toy locals in reserved EVM memory slots:

```lean
localSlot x = UInt256.ofNat (1048576 + 32 * x)
```

Operand lowering:

```text
const w  => PUSH32 w
local x  => PUSH32 (localSlot x); MLOAD
```

Instruction lowering:

- `inputLoad dst offset`: lower `offset`, run `CALLDATALOAD`, store the result in `localSlot dst`.
- `add dst lhs rhs`: lower `rhs`, lower `lhs`, run `ADD`, store the result in `localSlot dst`.
- `call dst args`: lower the seven EVM `CALL` operands in stack order, run `CALL`, store the success flag in `localSlot dst`.

`lowerOps` appends `STOP` after the lowered body. `lower` assembles that list.

The proved lowering theorem is currently over `lowerOps`, not over `lower` executed by `EVM.X`. The bytecode-level theorem still needs an explicit memory-disjointness assumption: source locals are separate from EVM memory, while lowered locals live in reserved memory. Calls that read or write the reserved local-memory range can interfere with compiled locals unless ruled out or modeled through a stronger memory layout discipline.

The correctness file no longer contains prefix/canonical proof fragments. Its proved theorem is:

```lean
lowerOps_preserve_semantics
```

Its bytecode-level target spec is:

```lean
LoweringPreservationSpec oracle callFuel callGasCost program initial
```

which directly relates:

```lean
run oracle (program.length + 1) initial program
```

to:

```lean
EVM.X (Bytecode.lowerFuel program)
  (EVM.D_J (Bytecode.lower program) 0)
  (withLoweredCodeAndLocals initial program)
```

The result relation compares successful source runs against successful lowered EVM runs through `StateRelOn program.touchedLocals`; source exceptional halt against matching EVM exception; and source fuel exhaustion against EVM `OutOfFuel`.

The unproved bytecode-level spec fixes the previous false statement by:

- choosing EVM fuel with `Bytecode.lowerFuel program`;
- seeding EVM memory with source locals read by the program;
- comparing only finite program-touched locals;
- requiring `CallOracleSoundForLowering oracle callFuel callGasCost`, where `callFuel` and `callGasCost` identify the exact EVM call context the bytecode proof reaches;
- requiring `CallOraclePreservesReservedLocalSlots oracle program.touchedLocals`.

See [Wrong Attempts](./wrong-attempts.md) for the detailed audit of what was wrong.

What is proved now:

- operand compilation into structured target ops preserves operand values;
- every instruction compilation into structured target ops preserves one source step;
- every whole `Program` preserves source semantics under `lowerOps`;
- generated one-byte opcodes for `STOP`, `ADD`, `CALLDATALOAD`, `MLOAD`, `MSTORE`, and `CALL` decode through EVMYulLean;
- source call oracles can now be constrained by `CallOracleMatchesEVMCallAt`, an explicit equality relation against executable `EVM.call`;
- the theorem is fully checked by Lean and the package contains no `sorry`, `admit`, or `axiom`.

What is not proved yet:

- the corrected, assumption-bearing preservation theorem against `EVM.X`;
- a true theorem shape for all programs with calls and gas;
- instruction-level `EVM.X` lemmas for compiler-generated chunks;
- `EVM.X` executes the lowered `CALL` bytecode against a fixed callee;
- exact gas preservation.

The current unrestricted source-to-`EVM.X` theorem would be false for two independent reasons:

- source `run` does not charge gas, while `EVM.X` checks and subtracts gas before every step;
- source `run` accepts an arbitrary `CallOracle`, while real EVM `CALL` can only return behavior produced by EVMYulLean's call semantics.

The gas mismatch is now checked in Lean:

```lean
theorem current_evm_preservation_statement_is_false :
    ¬ EVMBridgeSpec.ResultRelOn
      addOnlyProgram.touchedLocals
      (run emptyOracle (addOnlyProgram.length + 1) zeroGasState addOnlyProgram)
      (EVM.X (Bytecode.lowerFuel addOnlyProgram)
        (EVM.D_J (Bytecode.lower addOnlyProgram) (UInt256.ofNat 0))
        (EVMBridgeSpec.withLoweredCodeAndLocals zeroGasState addOnlyProgram))
```

So the next implementation change must be semantic, not cosmetic: either make the source semantics gas-aware and EVM-backed at calls, or state the bytecode theorem with explicit enough-gas and exact-call-behavior hypotheses.

## Next Proof Targets

1. Prove the `PUSH32` byte round-trip lemma:
   `uInt256OfByteArray value.toByteArray = value`.
2. Prove `EVM.decode` lemmas for the compiler-generated bytecode chunks.
3. State and prove the memory-disjointness invariant for the reserved local slots.
4. Prove PC/gas/halting side conditions for compiler-generated bytecode.
5. Prove instruction-level preservation lemmas for `inputLoad`, `add`, and `call`.
6. Add the constrained fixed-callee theorem for `CALL`.
7. Compose the general `LoweringPreservationSpec` theorem by induction over `Program`.
