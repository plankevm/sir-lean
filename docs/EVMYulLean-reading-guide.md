# EVMYulLean — EVM reading guide

This repo is a Lean 4 formalization of the EVM closely following the **Yellow Paper** (functions are literally named `Υ`, `Θ`, `Ξ`, `Λ`, `X` with equation-number comments). Ignore everything under `EvmYul/Yul/`.

## Suggested reading order

### 1. Primitive types & state building blocks

- `EvmYul/UInt256.lean` — the 256-bit word type used everywhere.
- `EvmYul/State/Account.lean` + `EvmYul/Maps/AccountMap.lean` — account record (balance, nonce, code, storage) and the world-state map `σ : AccountMap`.
- `EvmYul/State/Substate.lean` — the accrued substate `A` (access lists, refunds, self-destruct set, logs).
- `EvmYul/State/ExecutionEnv.lean` — the per-frame environment `I` (code owner, sender, calldata, code, gas price, depth, perm/static flag, block header).
- `EvmYul/State/Transaction.lean`, `BlockHeader.lean`, `Block.lean` — tx variants (legacy/access/dynamic/blob), headers, processed blocks. Skim these.

### 2. The layered state types

Small files; read all of them:

- `EvmYul/State.lean` — `EvmYul.State`: world state `σ`, checkpoint `σ₀`, substate `A`, execution environment `I`, block context.
- `EvmYul/MachineState.lean` — `μ`: memory, gas, return data.
- `EvmYul/SharedState.lean` — glues `State + MachineState`.
- `EvmYul/EVM/State.lean` — `EVM.State` = `SharedState` + `pc`, `stack`, plus `ExecutionResult` (`success`/`revert`).

So a call frame's full state is:

```text
EVM.State ⊃ SharedState ⊃ (State σ/A/I + MachineState μ)
```

### 3. Operations & per-instruction semantics

- `EvmYul/Operations.lean` — the `Operation` ADT (all opcodes).
- `EvmYul/EVM/Instr.lean` + `EvmYul/EVM/PrimOps.lean` — dispatch from opcode to its state transformer (stack/memory/storage ops).
- Shared op implementations live in `EvmYul/Semantics.lean`, `StateOps.lean`, and `MachineStateOps.lean`.
- `EvmYul/EVM/Gas.lean` / `GasConstants.lean` — gas charging; read as needed.

### 4. The interpreter core — `EvmYul/EVM/Semantics.lean`

This is the main file (~950 lines). Read bottom-up in the Yellow Paper hierarchy, i.e. in this order within the file:

1. `decode` / `fetchInstr` (~lines 84–100) — bytecode → `Operation` at `pc`.
2. `step` (~line 221) — executes one instruction. `CALL`/`CREATE` family handled specially via `call` (~line 141), which builds the child frame and invokes `Θ`/`Λ`.
3. `X` (~line 429) — iterative execution loop: fetch, validate stack/static-perm/valid jumps, charge gas, `step`, recurse on fuel.
4. `Ξ` (~line 525) — **code execution**: initializes a fresh `EVM.State` from `(σ, gas, A, I)` (`pc = 0`, empty stack/memory), computes `validJumps`, runs `X`.
5. `Λ` / `Lambda` (~line 562) — **contract creation**: address derivation, nonce/balance setup, runs init code via `Ξ`, deposits code.
6. `Θ` (~line 717) — **message call**: value transfer, chooses precompile (`Ξ_ECREC` … `Ξ_PointEval`, in `EvmYul/EVM/PrecompiledContracts.lean`) or `Ξ` on the callee's code, handles revert/rollback.
7. `Υ` (~line 823) — **transaction-level**: intrinsic gas, effective gas price, sender nonce/balance debit/checkpoint `σ₀`, warm access-list setup, then `Θ` (call) or `Λ` (create), refunds and fee payment.

### 5. Top level / conformance harness

- `Conform/TestRunner.lean` — `processBlocks` / `processBlock` apply `Υ` per transaction against the official Ethereum conformance tests. Useful for seeing how everything is wired end-to-end.

## TL;DR path

```text
State/Account
→ State.lean / MachineState / SharedState / EVM/State
→ Operations
→ EVM/Semantics: fetchInstr → step → X → Ξ → Λ → Θ → Υ
```
