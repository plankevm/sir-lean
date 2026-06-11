import SirLean.Proof

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

end Sir
