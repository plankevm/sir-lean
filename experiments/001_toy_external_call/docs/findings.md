# Experiment 001 Findings

## What Built

The package builds as a local Lake package against `../../forks/EVMYulLean` with Lean `v4.22.0`.

```text
lake build
```

The implemented artifact is intentionally small:

- `Operand`: local or constant word;
- `Instr.inputLoad`: load one EVM calldata word into a local;
- `Instr.addConst`: add a constant to a local using `UInt256` arithmetic;
- `Instr.call`: evaluate the seven EVM `CALL` operands and delegate the call boundary to an oracle;
- `run`: fuel-bounded interpreter over a linear list of instructions.

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

`CallResult.success = false` represents the ordinary EVM `CALL` failure flag, including callee revert. The toy interpreter continues and writes `0` to the destination local. The `Except` channel is reserved for caller-level exceptional halt.

This matters because callee revert is not the same thing as the caller reverting.

### Memory And Returndata Are Present

`CallRequest.input` is read from `s.evm.memory` using `inOffset` and `inSize`. `CallResult.returnData` updates `s.evm.returnData`. Output copying through `outOffset` and `outSize` is not proved yet; the current oracle can include that update in the returned `EVM.State`.

The next theorem should make output copying explicit, at least as an observable memory-slice relation.

## What Changed From The Initial Plan

- The plan originally showed a separate EVM-shaped toy state. The implementation now uses full `EVM.State`.
- The plan originally risked treating callee revert as a top-level toy result. The implementation instead follows EVM `CALL`: failure is a `0` success flag.
- The plan used `to` as an operand name. Lean rejected it in this context, so the implementation uses `target`.
- `UInt256` does not use plain numeral notation here, so constants are written with `UInt256.ofNat`.

## Next Proof Targets

1. Define an observable relation between `ToyState` and `EVM.State`.
2. Prove generic lemmas for `inputLoad` and `addConst`.
3. Add a hand-written bytecode harness for the canonical program.
4. State an oracle-level call-boundary correspondence theorem.
5. Replace the oracle assumption with one constrained EVMYulLean `CALL` theorem for a fixed successful callee.
