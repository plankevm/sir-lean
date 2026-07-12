This repository contains an executable formal model of the EVM in Lean 4
(Cancun fork), intended as a readable, citable semantics for verifying
compilers that target the EVM. It is validated against the Ethereum
BlockchainTests conformance fixtures.

Everything here is work in progress and is subject to change.

# Requirements
- [elan](https://github.com/leanprover/elan) (Lean 4 / Lake)
- Rust (cargo) — builds `tools/evmrs`, the native helper the conformance
  runner shells out to (built automatically by `lake build`).

# Project structure

## The instruction set
The `Operation` type describing all EVM instructions, and the decode /
gas-metadata tables (`parseInstr`, `serializeInstr`, `δ`/`α` stack arities):
```
Evm/Operations.lean
Evm/Instr.lean
```

## Words and state
The 256-bit word type — eight 32-bit limbs for execution speed, with the
arithmetic proven equivalent to `BitVec 256` so the limb code is not part of
the trust surface:
```
Evm/UInt256.lean
```

The world state (accounts, substate, environment) and its operations:
```
Evm/State.lean   Evm/StateOps.lean   Evm/State/   Evm/Maps/
```

The machine state (gas, memory, operand stack, pc) of a running frame:
```
Evm/Machine/
```

## Semantics
The interpreter is a yield/resume frame machine: executing one instruction
emits a `Signal` — continue the current frame, halt it (carrying the
RETURN/REVERT payload), or suspend it on a call or contract creation. All
opcode-specific logic lives in one central dispatcher match
(`Evm/Semantics/Dispatch.lean`): each arm pops its operands once, charges
its gas (named Appendix G formulas from `Gas.lean` applied to the popped
operands), runs its own validity checks, and executes; a tiny preamble
handles the purely syntactic δ/α stack-arity checks. The only recursion in
the spec is the driver loop `drive` (`Evm/Semantics/Interpreter.lean`),
which owns the frame stack. Calls and creations are split into non-recursive
`begin`/`end`/`resumeAfter` handlers (`Call.lean`, `Create.lean`), and the
public entry points are `messageCall` / `createContract` (the Yellow Paper's
`Θ` and `Λ`) plus `executeTransaction` (the YP's `Υ`) in `Evm/Semantics.lean`:
```
Evm/Semantics.lean         -- executeTransaction (Υ)
Evm/Semantics/Interpreter.lean
Evm/Semantics/Dispatch.lean
Evm/Semantics/Call.lean    Evm/Semantics/Create.lean
Evm/Semantics/Frame.lean   Evm/Semantics/Params.lean
Evm/Semantics/Decode.lean  Evm/Semantics/PrimOps.lean
```

Gas accounting and the precompiled contracts:
```
Evm/Semantics/Gas.lean   Evm/Semantics/GasConstants.lean
Evm/Semantics/Precompiles.lean
```

Cryptographic primitives (keccak via C FFI; ECDSA recovery, ripemd160,
alt_bn128, and the 4844 point evaluation via `tools/evmrs`):
```
Evm/Crypto/   Evm/FFI/
```

## Conformance testing
A git submodule with the EVM conformance fixtures is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

To execute conformance tests, make sure the `EthereumTests` directory is the
appropriate git submodule and run:
```
lake exe conform <NUM_THREADS>
```
where `<NUM_THREADS>` is the number of threads running conformance tests in
parallel (`nproc` does not exist on macOS, so always pass it explicitly).

The default run executes the **fast phase**: a curated representative sample
(`FastSample` in `Conform/Main.lean`, ~2,900 tests, <15s wall on 8 threads)
covering arithmetic/bitops, memory, storage (+transient), logs, all call
variants, creates, precompiles, reverts, static contexts, jumps, the Cancun
and Shanghai EIPs, and block-level processing. This is the iteration
default.

Flags:
- `--full` — the whole conformance phase (22,308 tests, ~2 minutes on 8
  threads). This is what CI runs.
- `--perf` — `--full` plus the throughput stress tests (`vmPerformance/` and
  blake2f max rounds — minutes per test).
- `--fail-fast` — abort the run on the first unexpected failure.

A second positional argument substring-filters fixture file paths, which is
the recommended way to run targeted samples while iterating:
```
lake exe conform 8 stMemoryTest
```

Per-test results (with elapsed times) land in `tests_<phase>.txt` (the fast
phase and filtered samples use phase 0, `--full` uses phase 1); expected
failures are listed in `Conform/Main.lean`.
