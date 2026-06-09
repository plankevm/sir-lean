# Experiment 001 Handoff

## Current State

Repo: `/Users/eduardo/workspace/evm-semantics`

Experiment: `experiments/001_toy_external_call`

Recent commits:

```text
c656366 Document checked EVM preservation obstruction
a055025 Prove current EVM preservation target is false
8a8e487 Add reusable EVM bytecode proof lemmas
f718322 Model exact EVM call oracle agreement
2727b79 Expose EVM X proof helpers
```

Build status:

```bash
cd experiments/001_toy_external_call
lake build
```

This currently passes.

## What Exists

### Toy IR

File: `ToyExternalCall/IR.lean`

- `Operand := local | const`
- `Instr := inputLoad | add | call`
- `ToyState := EVM.State + locals`
- Source `run` is fuel-bounded but not gas-aware.

### Lowering

File: `ToyExternalCall/Bytecode.lean`

- `Bytecode.lowerOps : Program -> List Bytecode.Op`
- `Bytecode.lower : Program -> ByteArray`
- Lowering is total over every `Program`.
- Locals are stored in reserved EVM memory:

```lean
localSlot x = UInt256.ofNat (1048576 + 32 * x)
```

### Checked Structured Proof

File: `ToyExternalCall/Correctness.lean`

Main theorem:

```lean
lowerOps_preserve_semantics
```

This proves source semantics equals the structured lowered-op interpreter for all programs.
It is not an `EVM.X` bytecode theorem.

### EVM Bytecode Lemmas

File: `ToyExternalCall/EVMBytecode.lean`

Contains reusable lemmas for:

- decoding one-byte ops;
- decoding `PUSH32`;
- `EVM.Z`/`EVM.H` execution helpers;
- basic `step_*` lemmas;
- `empty_program_evmX`.

### EVM Bridge Spec

File: `ToyExternalCall/EVMBridgeSpec.lean`

Defines:

```lean
CallOracleMatchesEVMCallAt
CallOracleSoundForLowering
LoweringPreservationSpec
```

This is still only a spec, not a proved preservation theorem.

### Checked Obstruction

File: `ToyExternalCall/Obstruction.lean`

Main theorem:

```lean
current_evm_preservation_statement_is_false
```

This proves the current source semantics cannot preserve `EVM.X` for all initial states because source execution ignores EVM gas.

## Why The EVM.X Theorem Failed

The definitions are misaligned.

1. Source `run` ignores EVM gas.

   Example:

   ```lean
   add 0 (const 1) (const 2)
   ```

   This succeeds even when `initial.evm.gasAvailable = 0`.

2. Lowered bytecode runs through `EVM.X`.

   The first lowered instruction is `PUSH32`. `EVM.X` calls `EVM.Z`, and `Z` checks:

   ```lean
   C' PUSH32 = GasConstants.Gverylow = 3
   ```

   With zero gas, target execution fails with `.OutOfGass`.

3. Source `CALL` uses an arbitrary `CallOracle`.

   Real bytecode call goes through:

   ```text
   EVM.X -> EVM.Z -> EVM.step -> EVM.call
   ```

   An arbitrary oracle can return behavior impossible for EVM.

4. Source locals are not EVM memory.

   Lowered locals are stored in reserved memory slots. This needs a frame invariant, especially because `CALL` copies returndata into caller memory.

## EVMYulLean Fork Changes

In `forks/EVMYulLean`, helpers from `EVM.X` were exposed:

- `EVM.belongs`
- `EVM.notIn`
- `EVM.W`
- `EVM.Z`
- `EVM.H`

Files touched:

- `forks/EVMYulLean/EvmYul/EVM/Semantics.lean`
- `forks/EVMYulLean/EvmYul/UInt256.lean`
- `forks/EVMYulLean/EvmYul/Wheels.lean`

Caution: `Wheels.lean` and `UInt256.lean` were changed to make byte/array reasoning more tractable. Those changes should be reviewed against upstream EVMYulLean behavior.

## Next Work

Do not try to prove the current `LoweringPreservationSpec` as-is. It is false.

The clean next path:

1. Redesign IR semantics to be gas-aware.

   Source execution must either charge the same costs as lowered bytecode or the theorem must include explicit enough-gas assumptions.

2. Decide how source `CALL` is modeled.

   Either make it executable EVM-backed from day one, or keep the oracle and require a precise hypothesis tying each oracle answer to the exact reached `EVM.call`.

3. Prove bytecode execution compositionally.

   Needed reusable lemmas:

   - generic decode-at-prefix for `PUSH32`;
   - generic decode-at-prefix for one-byte ops;
   - `assembleOp_size`;
   - instruction chunk theorem for each source instruction;
   - `CALL; PUSH32 localSlot; MSTORE` theorem, not just `CALL`.

4. Add a memory-frame invariant.

   Either prove `CALL` output does not clobber reserved local slots, or choose a layout discipline that makes this impossible.

5. Replace `LoweringPreservationSpec` with an actual theorem only after the definitions line up.

## Useful Commands

```bash
cd /Users/eduardo/workspace/evm-semantics/experiments/001_toy_external_call
lake build
```

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b" ToyExternalCall ../../forks/EVMYulLean/EvmYul/EVM/Semantics.lean
```

## Relevant Docs

- `experiments/001_toy_external_call/docs/findings.md`
- `experiments/001_toy_external_call/docs/wrong-attempts.md`
- `experiments/001_toy_external_call/docs/plan.md`
