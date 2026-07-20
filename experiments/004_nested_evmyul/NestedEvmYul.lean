-- Experiment 004 root. The nested EVM reasoning core (Milestones B2-B4) builds here
-- on top of the vendored, Yul-stripped EVMYulLean (`import EvmYul.EVM.Semantics`).
-- B1 only wires the package up; reasoning content lands in later milestones.
import EvmYul.EVM.Semantics
import NestedEvmYul.NeverOutOfFuel
import NestedEvmYul.FuelMono
-- Cross-engine convergence: the toolchain-neutral shared observable, the
-- `observe_nested` projection above `Θ`, the `EVMSemantics` interface + nested
-- instance, and `runΘ_never_outOfFuel`. Mirror on the flat side:
-- EVM/BytecodeLayer/SharedObservable.lean.
import NestedEvmYul.SharedObservable
-- The NESTED refinement half: `emptyObs` literal + `nested_refines_emptyObs`
-- (single-STOP do-nothing call observes as the canonical do-nothing spec).
-- Mirror on the flat side: EVM/BytecodeLayer/Equivalence.lean.
import NestedEvmYul.Refinement
