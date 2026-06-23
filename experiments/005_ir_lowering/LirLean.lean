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
import LirLean.Match
import LirLean.WorkedCall
-- v2 (exp005) prototype — gas-free, observable, event-trace IR + preservation.
import LirLean.V2.Machine
import LirLean.V2.Preserve
-- v2 (exp005) two-read gas-monotonicity milestone (§3.4).
import LirLean.V2.Mono
