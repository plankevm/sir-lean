import SirLean.Proof

/-!
# SIR specification

Audit surface: this file plus the definitions its statements reach —
`IR.lean` (program representation and validity), `State.lean` (execution
state), `Eval.lean` (executable semantics), `SmallStep.lean` (small-step
semantics), `SCCP.lean` (the SCCP pass). `Proof.lean` contains only proofs and proof-internal
definitions; it is kernel-checked and needs no human review. Proof-layer
names must not appear in the statements below.
-/

namespace Sir

theorem ControlFlowGraph.eval?_iff_steps
    (cfg : ControlFlowGraph) (w : World) (t : Termination) (w' : World) :
    (∃ fuel, cfg.eval? w fuel = .ok (t, w')) ↔
      CFGSteps cfg (cfg.initialConf w) (.done t w') :=
  ControlFlowGraph.eval?_iff_steps.proof cfg w t w'

theorem ControlFlowGraph.progress
    (cfg : ControlFlowGraph) (w : World) (c : Conf)
    (hreach : CFGSteps cfg (cfg.initialConf w) c) :
    (∃ t w', c = .done t w') ∨ (∃ c', StepCFG cfg c c') :=
  ControlFlowGraph.progress.proof cfg w c hreach

theorem SCCP.run_sccp_preserves : PreservesSemantics SCCP.run_sccp :=
  SCCP.run_sccp_preserves.proof

/--
info: 'Sir.ControlFlowGraph.eval?_iff_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ControlFlowGraph.eval?_iff_steps

/--
info: 'Sir.ControlFlowGraph.progress' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ControlFlowGraph.progress

/--
info: 'Sir.SCCP.run_sccp_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SCCP.run_sccp_preserves

end Sir
