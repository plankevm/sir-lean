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
- `Lowering`: lower the toy instructions to EVMYulLean opcode-level traces and prove first preservation theorems;
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

`CallResult.successFlag` is the exact `UInt256` word that EVM `CALL` pushes. In practice this is `0` for failure and `1` for success, but keeping the word avoids an unnecessary Boolean translation in the first lowering proof. The toy interpreter continues and writes that flag to the destination local. The `Except` channel is reserved for caller-level exceptional halt.

This matters because callee revert is not the same thing as the caller reverting.

### Memory And Returndata Are Present

`CallRequest.input` is read from `s.evm.memory` using `inOffset` and `inSize`. `CallRequest` also keeps both `targetWord` and `target`: EVM receives a 256-bit stack word and converts it to a 160-bit account address internally. `CallResult.returnData` updates `s.evm.returnData`. Output copying through `outOffset` and `outSize` is not proved yet; the current oracle can include that update in the returned `EVM.State`.

The next theorem should make output copying explicit, at least as an observable memory-slice relation.

## What Changed From The Initial Plan

- The plan originally showed a separate EVM-shaped toy state. The implementation now uses full `EVM.State`.
- The plan originally risked treating callee revert as a top-level toy result. The implementation instead follows EVM `CALL`: failure is a `0` success flag.
- The first implementation stored call success as `Bool`; the lowering proof changed it to the exact EVM success word.
- The plan used `to` as an operand name. Lean rejected it in this context, so the implementation uses `target`.
- `UInt256` does not use plain numeral notation here, so constants are written with `UInt256.ofNat`.

## Lowering Proofs Added

`ToyExternalCall.Lowering` defines an opcode-level lowered trace:

- `PUSH32 offset; CALLDATALOAD` for `inputLoad`;
- `PUSH32 constant; ADD` for `addConst`;
- argument setup plus `CALL` for the external call boundary.

The non-call prefix uses EVMYulLean's primitive opcode transformer. The call boundary uses EVMYulLean `EVM.step` for `CALL`, because that is where the recursive message-call semantics lives.

Current proved theorems:

- `toy_inputLoad_preserved_by_lowering`: the toy local written by `inputLoad` equals the EVM stack top after the lowered `CALLDATALOAD` trace.
- `toy_addConst_preserved_by_lowering`: the toy local written by `addConst` equals the EVM stack top after `PUSH32 constant; ADD`.
- `toy_call_preserved_by_evm_step_oracle`: the toy call oracle derived from EVMYulLean `CALL` writes the same success flag as the EVM stack top.
- `toy_call_preserves_machine_obs_by_evm_step_oracle`: the toy call result and EVM call result agree on EVMYulLean world/machine observations when the call step produces a stack result.

This is not yet a theorem about byte-encoded code running through `EVM.X`. It is a supplied-opcode/primitive-step theorem that isolates semantic preservation before proving byte decoding, PC layout, gas prechecks, and halting.

## Next Proof Targets

1. Add a byte-encoded harness using EVMYulLean `decode`/`EVM.X`.
2. Prove PC/gas/halting side conditions for the canonical program.
3. Prove a whole canonical-program theorem rather than per-instruction preservation.
4. Replace the EVM-step call oracle with one constrained fixed-callee theorem.
5. Make output memory-copy observations explicit.
