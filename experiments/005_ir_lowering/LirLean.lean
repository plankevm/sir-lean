-- Experiment 005 — high-level IR (LirLean) → EVM bytecode, lowering preserved (Track C).
-- Root import list. Grouped by layer; `import LirLean.Audit` stays LAST (its #guard_msgs
-- axiom/signature guards fail the build on drift, and it directly imports the headline cone).
-- Design/history notes live in docs/ (ir-design*.md, execution-plan-2026-07-02.md,
-- reorg-legibility.md); archived leaf examples (`_attic/{Decode,WorkedCall,WorkedCallParity}`)
-- are off-cone by design (see docs/uniform-spill-alloc-plan.md, Phase-C bullet).

-- Spec core (reviewer-facing datatypes/semantics/lowering; Wave 3 spec-extract).
import LirLean.Spec.IR
import LirLean.Spec.Semantics
import LirLean.LoweringLemmas

-- Decode / pc-offset / jumpdest layer.
import LirLean.DecodeLower
import LirLean.Layout
import LirLean.DecodeAnchors
import LirLean.BoundaryReach

-- v1 reference semantics + CALL/CREATE bricks + match.
import LirLean.SmallStep
import LirLean.Call
import LirLean.Create
import LirLean.Match

-- Materialise (spill/recompute value channel) + clean-halt extractor.
import LirLean.MaterialiseGas
import LirLean.DefsSound
import LirLean.MaterialiseRuns
import LirLean.Engine.CleanHalt
import LirLean.CleanHaltExtract
import LirLean.MaterialiseCleanHalt

-- Per-statement / terminator simulation.
import LirLean.SimTerm

-- v2 (exp005) gas-free IR: determinism, existence, preservation, abstract CALL oracle.
import LirLean.V2.Law
import LirLean.V2.IRRun
import LirLean.V2.Call
import LirLean.V2.CallRealises

-- Cyclic-CFG drive simulation + the assembled/tie-free headlines (over Engine/, Drive/).
import LirLean.Acyclic
import LirLean.V2.DriveSim
import LirLean.V2.Drive.Headline

-- Reviewer-facing `Lir.Spec` audit surface (Wave 3): seam register + conditional-headline
-- re-exports + the `RealisabilityObligations` bundle (Pattern C — downstream of the proofs).
import LirLean.Spec.Seams
import LirLean.Spec.Conformance

-- Audit net (Track A): #guard_msgs axiom + flagship-signature guards. MUST stay last.
import LirLean.Audit
