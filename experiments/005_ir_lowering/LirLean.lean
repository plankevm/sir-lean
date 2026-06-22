-- Experiment 005 — high-level IR (LirLean) → EVM bytecode, lowering preserved.
-- Track C. C1 = IR datatypes + lowering signature (this skeleton); C2/C3 add the
-- small-step semantics and the lowering-preservation proof against exp003's
-- `Runs` / `messageCall_runs` API. See docs/ir-design.md.
import LirLean.IR
import LirLean.Lowering
