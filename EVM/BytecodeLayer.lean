-- The bytecode proof layer over the vendored Evm/ interpreter — this package's
-- sole proof layer (formerly "experiment 003", folded into EVM 2026-07-15).
-- Proof-first / always-green: every module's theorems are fully proved (zero
-- sorry). Abstractions are added only when a proof forces them.
--
-- NOTE the build is wider than this import list: `EVM/lakefile.lean` globs
-- `.andSubmodules BytecodeLayer`, so every module under `BytecodeLayer/`
-- compiles whether or not it is reachable from this root. The imports below are
-- a curated reading surface, not the build closure.
--
-- Layout (a topic tree mirroring `Evm/Semantics/`):
--   Spec.lean         — the audit surface of the Hoare program-logic layer
--                       (read this first; its header maps the rest).
--   Programs.lean     — the example bytecode contracts and message-call params.
--   Observables.lean  — the observable projections results are stated through.
--   Semantics/        — the reusable semantic facts (gas/system/dispatch/...) and
--                       the fuel-specific Interpreter/ measure argument.
--   Hoare/            — the compositional Hoare-style layer (Runs + opcode rules).
--   ExternalCall.lean — reusable bricks for the external-call rung.
--   Examples/         — worked example programs / demos.
--   Exec/, Exec.lean  — the SECOND export surface: the recording interpreter and
--                       its engine machinery (Recorder, CyclicSim, WitnessChecks,
--                       ...), consumed by experiments/005_ir_lowering (LirLean)
--                       via `require evm`, not by this root.
--   Asm.lean, Asm/    — the assembler + its Geometry layout facts (imports
--                       Exec/); also consumed from the LirLean side.
--   EVMSpec.lean      — DRAFT abstract engine interface, deliberately
--                       de-aggregated (28e01243); do NOT re-import it here. The
--                       canonical cross-engine interface today is
--                       `EVMSemantics`/`flatSem` in SharedObservable.lean.
import BytecodeLayer.Spec
-- Cross-engine convergence: the toolchain-neutral shared observable, the flat
-- `observe_flat` projection, the `EVMSemantics` interface + flat instance, and
-- the (stated-only) flat↔nested equivalence goal. Mirror on the nested side:
-- experiments/004_nested_evmyul/NestedEvmYul/SharedObservable.lean.
import BytecodeLayer.SharedObservable
import BytecodeLayer.Equivalence
-- The FLAT half of cross-engine refinement-through-a-shared-spec: the do-nothing
-- STOP call observes as the canonical `emptyObs`. Mirror on the nested side.
import BytecodeLayer.Refinement
