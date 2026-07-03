-- Experiment 005 — high-level IR (LirLean) → EVM bytecode, lowering preserved.
-- Track C. C1 = IR datatypes + lowering signature; C2 = decode-compatible
-- single-call lowering (operand materialisation) + build-enforced decode
-- round-trip checks (`LirLean/Decode.lean`); C3 adds the small-step semantics and
-- the lowering-preservation proof against exp003's `Runs` / `messageCall_runs`
-- API. See docs/ir-design.md.
import LirLean.Spec.IR
import LirLean.LoweringLemmas
-- NOTE: `Decode` (decode round-trip anchors) is a byte-coupled *leaf example* —
-- nothing in the headline cone imports it. Its `rfl`/`decide` byte checks are stale under
-- the Phase-C sload spill (the SLOAD def-site stash shifted byte offsets). It is SUPERSEDED
-- by the general `lower_conforms` and ARCHIVED under `_attic/Decode.lean` (no longer in-tree
-- as a `LirLean` module; the lib uses an explicit `roots := [`LirLean]` rather than the
-- submodule glob; see lakefile + the Phase-C bullet in docs/uniform-spill-alloc-plan.md).
-- Re-derivation of its anchors is deferred.
import LirLean.DecodeLower
import LirLean.Layout
import LirLean.SmallStep
import LirLean.Call
import LirLean.Create
import LirLean.Match
-- Layer A of the `lower_conforms` grind: decode-at-cursor anchors (A1–A3) —
-- statement-head / arbitrary-offset / terminator decode facts over `lower prog`.
import LirLean.DecodeAnchors
-- Layer E of the `lower_conforms` grind: block terminators + control-flow edges —
-- E1 `sim_term_halt` (stop/ret halt, world channel) + E2 `sim_term_edge` (jump/branch
-- to the successor block's entry, re-establishing `Corr` at `(succ, 0)`).
import LirLean.SimTerm
-- The boundary-reachability bricks (BOUNDARY): the converse of
-- `mem_validJumpDests_of_reachable_jumpdest` (a recorded jump destination is a reachable
-- boundary) and intermediate-boundary reachability from a `SegAligned` whole-program segment.
-- Feed the whole-run `AtReachableBoundary` invariant (`V2/BoundaryReach.lean`).
import LirLean.BoundaryReach
-- Layer B of the `lower_conforms` grind: B2 gas-charge envelope, B3 recompute
-- soundness (DefsSound), and B1 `materialise_runs` (the linchpin — pure-arithmetic
-- value channel + B2 gas contract).
import LirLean.MaterialiseGas
import LirLean.DefsSound
import LirLean.MaterialiseRuns
import LirLean.Engine.CleanHalt
-- NOTE: `WorkedCall` (a 1752-line concrete `Runs` proof) is a byte-coupled *leaf
-- example* — nothing in the headline cone imports it (decoupled in `e9bc04d`). Its byte layout
-- is stale under the Phase-C sload spill; it is SUPERSEDED by the general `lower_conforms` and
-- ARCHIVED under `_attic/WorkedCall.lean` (no longer in-tree). Re-derivation deferred (see docs/uniform-spill-alloc-plan.md).
-- v2 (exp005) prototype — gas-free, observable, event-trace IR + preservation.
import LirLean.Spec.Semantics
-- v2 (exp005) frame-free IRRun determinism (imports only LirLean.IR/Evm; zero
-- BytecodeLayer/Frame/Runs): EvalStmt.det → RunStmts.det → RunFrom.det → IRRun.det.
import LirLean.V2.Law
-- v2 (exp005) IRRun EXISTENCE (the `hir` side): constructive `RunStmts`/`RunFrom`/`IRRun`
-- existence for the gas-free, call-free, single-halting-block fragment (imports only
-- LirLean.V2.Law; frame-free). The tractable floor of the `hir`-construction milestone.
import LirLean.V2.IRRun
import LirLean.V2.Preserve
-- v2 (exp005) the abstract external-call oracle worked example (v3 §3, §7): the
-- frame-free `Stmt.call` arm run under an arbitrary `CallOracle` (no instantiation).
import LirLean.V2.Call
-- v2 (exp005) the CALL realisability bridge (v3 §3, §7): instantiate the abstract
-- `V2.CallOracle` to v1's `evmCallOracle`; the realised bundle = the lowered CALL's
-- observable effect. Bytecode-coupled.
import LirLean.V2.CallRealises
-- NOTE: `WorkedCallParity` (the with-CALL parity worked example coupling the byte-coupled
-- `WorkedCall`) is a *leaf example* — deliberately OFF the headline cone. SUPERSEDED by the
-- general `callRealises_bridge` / `lower_conforms`; ARCHIVED under `_attic/WorkedCallParity.lean`
-- (no longer in-tree) under the Phase-C sload spill (stale byte layout). Re-derivation deferred.
-- Acyclicity ⇒ `MatFueled`: discharges `WellFormedLowered`'s recompute-fuel-sufficiency
-- fields from a rank-based SSA acyclicity witness (`Acyclic (defsOf prog) rank`), so no
-- `MatFueled` hypothesis survives for an acyclic program (`wellFormedLowered_of_acyclic`).
import LirLean.Acyclic
-- The CYCLIC world-channel headlines (`lower_conforms_cyclic`/`_cyclic'`): the drive-recursion
-- simulation for any (possibly cyclic) CFG. Pulls in the full spine (LowerConforms, RunLog, …).
import LirLean.V2.DriveSim
-- The tie-discharge layer, dissolved into `V2/Drive/` (engine split, Wave 2): the headlines
-- (`lower_conforms_cyclic_tiefree`/`_assembled` in `Drive/Headline`), the seam-carrying
-- `callPreservesSelf` chain (`Drive/CallPreservesSelf`), and the positional alignment
-- foundation (`GasLogAligned`/`SloadLogAligned`, `FramesRun.snoc` in `Drive/SelfPresent`) —
-- all over the pure engine theory in `LirLean/Engine/`.
import LirLean.V2.Drive.Headline
-- The reviewer-facing `Lir.Spec` audit surface (Wave 3, spec-extract): the tracked-debt
-- seam register (`Spec/Seams.lean`) + the conditional-headline re-exports and the
-- `RealisabilityObligations` bundle (`Spec/Conformance.lean`). Pattern C — downstream of
-- the proof modules by design.
import LirLean.Spec.Seams
import LirLean.Spec.Conformance
-- Track 1 (EXTRACTOR): clean-halting ⟹ per-cursor gas/mem envelopes. The forward-from-real-run
-- producer that discharges the §7 ties' supplied gas/mem side-conditions from the drive thread's
-- entry clean-halt (`CleanHaltsSuccess` + per-op `.next`-inversion + the stash envelope family).
import LirLean.CleanHaltExtract
-- FoldLemma: the gas-dropping twin of B1. Derives B1's whole-expression gas envelope
-- (`materialise_charge_le_of_cleanHalt`) from a single entry `CleanHaltsNonException` witness via a
-- charge-descent fold (reusing B1 for frame production + the extractor's per-op `.next`-inversion),
-- and re-exports B1's bundle with the gas bound as a derived conjunct (`materialise_runs_of_cleanHalt`).
import LirLean.MaterialiseCleanHalt
-- AUDIT NET (Track A, 2026-07-02): #guard_msgs-pinned axiom + flagship-signature guards.
-- Must stay the LAST import of this root. Directly imports the guarded modules (incl.
-- V2.Drive.Headline), so the headline cone stays in the default target independent of the
-- other root imports. See docs/exec/audit-net.md.
import LirLean.Audit
