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
- `Bytecode.lower`: a total compiler from the existing `Program` type to EVM bytecode.
- `Correctness`: source-side semantic facts and the explicit `EVM.X` preservation predicate for the prefix.

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

## Removed False Start

An earlier `ToyExternalCall.Lowering` module was removed because it proved preservation only against an opcode-trace/primitive-step shortcut. That was not the requested theorem and it was not a clean model of lowering to bytecode.

The replacement uses the existing `Instr`/`Program` IR and produces `ByteArray`. It does not prove preservation against an opcode trace.

## Current Lowering Status

The lowering is now instruction-directed and total:

```lean
Bytecode.lower : Program -> ByteArray
```

It handles every syntactically possible toy IR program. It does this by compiling each instruction independently and storing toy locals in reserved EVM memory slots:

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

`lower` appends `STOP` after the lowered body.

This is a real total lowering, but the eventual preservation theorem now needs an explicit memory-disjointness assumption: source locals are separate from EVM memory, while lowered locals live in reserved memory. Calls that read or write the reserved local-memory range can interfere with compiled locals unless ruled out or modeled through a stronger memory layout discipline.

What is proved today:

- the source interpreter computes the expected local for calldata-load plus addition;
- the source interpreter computes the expected locals for the canonical fixed-call oracle;
- `Bytecode.lower` produces bytecode for every `Program`.

What is not proved yet:

- `EVM.X` executes the lowered prefix bytecode to the corresponding reserved-memory local observation;
- `EVM.X` executes the lowered `CALL` bytecode against a fixed callee;
- exact gas preservation.

## Next Proof Targets

1. Prove the `PUSH32` byte round-trip lemma:
   `uInt256OfByteArray value.toByteArray = value`.
2. Prove `EVM.decode` lemmas for the compiler-generated bytecode chunks.
3. State and prove the memory-disjointness invariant for the reserved local slots.
4. Prove PC/gas/halting side conditions for the prefix program.
5. Prove the prefix theorem against EVMYulLean `EVM.X`.
6. Add the constrained fixed-callee theorem for `CALL`.
7. Compose the whole canonical-program theorem and make output memory-copy observations explicit.
