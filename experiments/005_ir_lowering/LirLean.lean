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
