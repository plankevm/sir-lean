# Experiment 001: Toy External Call

## Goal

Implement the first Lean pilot for a tiny instruction-like IR with:

- calldata word load;
- add constant;
- external `CALL` as an instruction writing a success local;
- gas, memory, return data, and EVM account state present from day one.

The purpose is learning-oriented: understand what the state, semantics, and correctness theorem should look like before moving to actual Plank SIR.

## Decisions From Review

- `CALL` is an EVM bytecode opcode and a Plank SIR operation. The toy IR should model it as an instruction, not as an opaque meta-level operation.
- Use EVMYulLean types where practical: `UInt256`, `ByteArray`, and the full `EVM.State`.
- Keep memory, return data, gas, account state, and call environment available immediately through `EVM.State`.
- Do not model storage operations yet, but keep account state because external calls need a world state.
- Use an independent teaching IR first.
- Use hand-written bytecode before the Plank backend.
- Define independent IR semantics, then prove lowering preserves that semantics.
- Use observables/state relations rather than full state equality.

## Why `CallArgs`

`CALL` is an instruction, but it has seven EVM stack operands:

```text
CALL(gas, to, value, inOffset, inSize, outOffset, outSize)
```

`CallArgs` is only a typed bundle for those operands. It is not meant to imply that `CALL` is not an opcode. In the current toy IR, each field is an `Operand`, so it can refer to a local or an immediate constant. This keeps the toy close to SIR's local-based operation model without hiding the EVM operand shape.

## State Shape

The first version uses:

```lean
structure ToyState where
  evm : EVM.State
  locals : Local -> Word
```

This is the design decision from review: do not build a parallel toy account/memory/gas/call-context state when EVMYulLean already has one. The independent part of the IR semantics is the local environment and instruction interpreter. The blockchain and machine state are carried in EVMYulLean's state, which should make later call/storage relations less artificial.

This is intentionally different from Verity's source-level state, which is more abstract and then related to lower layers. For this pilot, the abstraction payoff is not obvious enough to justify an extra translation layer.

## Current Abstraction Level

The first interpreter uses an oracle:

```lean
CallOracle : ToyState -> CallRequest -> Except EVM.ExecutionException CallResult
```

This makes the call boundary explicit while we build the state and interpreter. `CallRequest` contains the evaluated call operands plus the input memory slice. `CallResult` contains:

- `successFlag : UInt256`, the exact value that the EVM `CALL` instruction would push;
- `returnData : ByteArray`, the caller-visible returndata buffer;
- `evm : EVM.State`, the updated world/machine state after the call.

Important semantic distinction: a callee revert is represented by a `0` success flag and updated returndata; it is not a caller-level `revert` result. The caller-level interpreter only stops exceptionally when the call cannot be performed as an EVM instruction, for example stack/gas/static/depth-style exceptional failure once those checks are modeled.

The lowering proof is not implemented yet. The next attempt should lower this existing IR to bytecode and prove the whole-program theorem against EVMYulLean `EVM.X`; opcode-trace shortcuts are explicitly out of scope.

## Output Memory

EVM `CALL` takes `outOffset` and `outSize` because the callee's output is copied into a caller memory slice after the call. The current oracle returns an already-updated `EVM.State`, so output copying can either be included in the oracle's state update or exposed as a separate lemma later.

That keeps day-one memory and returndata visible without committing the first interpreter to exact memory expansion and copy gas proofs. The constrained EVM theorem should eventually say which memory slice is observable and how `returnData` relates to copied output.

## Intended Next Step

Add a bytecode/EVMYulLean harness:

1. build an EVMYulLean `EVM.State` from `ToyState`;
2. hand-write bytecode for calldata load/add/call;
3. prove generic input-load/add lemmas;
4. state the whole-program lowering theorem;
5. replace the call oracle with a fixed successful callee theorem.
