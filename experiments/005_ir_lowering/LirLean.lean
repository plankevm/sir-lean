-- Experiment 005 — high-level IR (LirLean) → EVM bytecode, lowering preserved (Track C).
-- Root import list. Grouped by layer; `import LirLean.Audit` stays LAST (its #guard_msgs
-- axiom/signature guards fail the build on drift, and it directly imports the headline cone).
-- Design/history notes live in docs/ (ir-design*.md, execution-plan-2026-07-02.md,
-- reorg-legibility.md); archived leaf examples (`_attic/{Decode,WorkedCall,WorkedCallParity}`)
-- are off-cone by design (see docs/uniform-spill-alloc-plan.md, Phase-C bullet).

-- Spec core (reviewer-facing datatypes/semantics/lowering; Wave 3 spec-extract).
import LirLean.Spec.IR
import LirLean.Spec.Semantics
import LirLean.Decode.LoweringLemmas

-- Decode / pc-offset / jumpdest layer.
import LirLean.Decode.DecodeLower
import LirLean.Decode.SegAligned
import LirLean.Decode.Layout
import LirLean.Decode.DecodeAnchors
import LirLean.Decode.BoundaryReach
import LirLean.Decode.BoundaryCursor

-- v1 reference semantics + CALL/CREATE bricks + match.
import LirLean.Frame.SmallStep
import LirLean.Frame.Call
import LirLean.Frame.Create
import LirLean.Frame.Match

-- Materialise (spill/recompute value channel) + clean-halt extractor.
import LirLean.Materialise.MaterialiseGas
import LirLean.Materialise.DefsSound
import LirLean.Materialise.MaterialiseRuns
import BytecodeLayer.Hoare.CleanHalt
import LirLean.Materialise.CleanHaltExtract
import LirLean.Materialise.MaterialiseCleanHalt

-- Per-statement / terminator simulation.
import LirLean.Sim.SimTerm

-- Gas-free IR: determinism, existence, preservation, and the abstract CALL oracle.
import LirLean.Law
import LirLean.IRRun
import LirLean.Call
import LirLean.CallRealises

-- Cyclic-CFG drive simulation and account-preservation support.
import LirLean.Drive.DriveSim
import LirLean.Drive.CallPreservesSelf

-- IR well-formedness vocabulary + the `IRWellFormed` bundle and the two scalar budgets
-- (`codeFits`/`stackFits`) — the trusted-surface statement vocabulary (Spec hoist §1C).
import LirLean.Spec.WellFormed

-- The §1B budget-derivation lemmas (1B-lemmas): `codeFits`/`stackFits` plus
-- `IRWellFormed`'s static fields rebuild the internal `WellLowered` adapter. The
-- lowered-layout fields are pc/offset/stack facts over `matCache`/`chargeCache`, not
-- acyclicity or fuel obligations.
import LirLean.Spec.BudgetDerivations

-- Phase 2A P5a: the fuel-free charge fold twin's fixpoint `chargeCache_unfold` + the
-- chargeCache↔matCache length lockstep (twin of `matCache_unfold`, over the fold; no bridge).
import LirLean.Materialise.MatFoldChannel

-- Reviewer-facing `Lir.Spec` audit surface (Wave 3): seam register + conditional-headline
-- re-exports + the `RealisabilityObligations` bundle (Pattern C — downstream of the proofs).
import LirLean.Spec.Seams
import LirLean.Spec.Conformance

-- Audit net (Track A): #guard_msgs axiom + flagship-signature guards. MUST stay last.
import LirLean.Audit
