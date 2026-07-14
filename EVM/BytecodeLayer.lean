-- Experiment 003 — bytecode layer over leanevm.
-- Proof-first / always-green: this root imports only modules whose theorems are
-- fully proved (zero sorry). Abstractions are added only when a proof forces them.
--
-- Layout (a topic tree mirroring leanevm's Evm/Semantics/):
--   Spec.lean         — THE AUDIT SURFACE: every exported theorem (read this).
--   Programs.lean     — the example bytecode contracts and message-call params.
--   Observables.lean  — the observable projections results are stated through.
--   Semantics/        — the reusable semantic facts (gas/system/dispatch/...) and
--                       the fuel-specific Interpreter/ measure argument.
--   Hoare/            — our compositional Hoare-style layer (Runs + opcode rules).
--   ExternalCall.lean — reusable bricks for the external-call rung.
--   Examples/         — worked example programs / demos.
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
-- DRAFT: the abstract `EVMSpec` interface (bytecode + state as SEPARATE interp
-- args) and the flat instance `flatSpec` — the reshape of the interim
-- `EVMSemantics`/`flatSem`. Pending Eduardo's sign-off on the State/Result choice.
import BytecodeLayer.EVMSpec
