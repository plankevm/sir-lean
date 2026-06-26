-- Experiment 005 — high-level IR (LirLean) → EVM bytecode, lowering preserved.
-- Track C. C1 = IR datatypes + lowering signature; C2 = decode-compatible
-- single-call lowering (operand materialisation) + build-enforced decode
-- round-trip checks (`LirLean/Decode.lean`); C3 adds the small-step semantics and
-- the lowering-preservation proof against exp003's `Runs` / `messageCall_runs`
-- API. See docs/ir-design.md.
import LirLean.IR
import LirLean.Lowering
import LirLean.Decode
import LirLean.DecodeLower
import LirLean.Layout
import LirLean.SmallStep
import LirLean.Call
import LirLean.Match
-- Layer A of the `lower_conforms` grind: decode-at-cursor anchors (A1–A3) —
-- statement-head / arbitrary-offset / terminator decode facts over `lower prog`.
import LirLean.DecodeAnchors
-- Layer E of the `lower_conforms` grind: block terminators + control-flow edges —
-- E1 `sim_term_halt` (stop/ret halt, world channel) + E2 `sim_term_edge` (jump/branch
-- to the successor block's entry, re-establishing `Corr` at `(succ, 0)`).
import LirLean.SimTerm
-- Layer B of the `lower_conforms` grind: B2 gas-charge envelope, B3 recompute
-- soundness (DefsSound), and B1 `materialise_runs` (the linchpin — pure-arithmetic
-- value channel + B2 gas contract).
import LirLean.MaterialiseGas
import LirLean.DefsSound
import LirLean.MaterialiseRuns
import LirLean.WorkedCall
-- v2 (exp005) prototype — gas-free, observable, event-trace IR + preservation.
import LirLean.V2.Machine
-- v2 (exp005) frame-free gas LAW + IRRun determinism (imports only LirLean.IR/Evm;
-- zero BytecodeLayer/Frame/Runs): Trace.gasMonotone, MonotoneGas, RunFrom.det/IRRun.det.
import LirLean.V2.Law
import LirLean.V2.Preserve
-- v2 (exp005) two-read gas-monotonicity milestone (§3.4); IR↔bytecode bridge that
-- discharges the frame-free law from the bytecode's gas descent.
import LirLean.V2.Mono
-- v2 (exp005) the gas-oracle interface, law-first (v3 §2, §4–5, S1): the IR↔bytecode
-- bridge — GasRealises side-condition over Frame/Runs, realises→law discharge.
import LirLean.V2.Oracle
-- v2 (exp005) the abstract external-call oracle worked example (v3 §3, §7): the
-- frame-free `Stmt.call` arm run under an arbitrary `CallOracle` (no instantiation).
import LirLean.V2.Call
-- v2 (exp005) the CALL realisability bridge (v3 §3, §7): instantiate the abstract
-- `V2.CallOracle` to v1's `evmCallOracle`; the realised bundle = the lowered CALL's
-- observable effect (the call analogue of `GasRealises.monotoneGas`). Bytecode-coupled.
import LirLean.V2.CallRealises
