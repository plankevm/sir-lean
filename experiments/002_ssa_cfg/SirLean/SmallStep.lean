import Mathlib.Logic.Relation
import SirLean.IR
import SirLean.State
import SirLean.Eval

namespace Sir

def StepOp (ctx : Env) (op : Op) (ctx' : Env) : Prop :=
  op.eval? ctx = some ctx'

def StepEndOp (ctx : Env) (endOp : EndOp) (c : Continuation) : Prop :=
  endOp.eval? ctx = some c

inductive Conf where
  | running (bb : Nat) (pc : Nat) (env : Env)
  | done (t : Termination) (world : World)

def ControlFlowGraph.initialConf (cfg : ControlFlowGraph) (w : World) : Conf :=
  .running cfg.entry.val 0 { vars := .empty, world := w }

inductive StepCFG (cfg : ControlFlowGraph) : Conf → Conf → Prop where
  | op
      (hbb : bb < cfg.blocks.size)
      (hpc : pc < (cfg.blocks[bb]'hbb).ops.size)
      (hop : StepOp e ((cfg.blocks[bb]'hbb).ops[pc]'hpc) e') :
      StepCFG cfg (.running bb pc e) (.running bb (pc + 1) e')
  | exit
      (hbb : bb < cfg.blocks.size)
      (hpc : pc = (cfg.blocks[bb]'hbb).ops.size)
      (hend : StepEndOp e (cfg.blocks[bb]'hbb).last (.terminated t)) :
      StepCFG cfg (.running bb pc e) (.done t e.world)
  | goto
      (hbb : bb < cfg.blocks.size)
      (hpc : pc = (cfg.blocks[bb]'hbb).ops.size)
      (hend : StepEndOp e (cfg.blocks[bb]'hbb).last (.goto dst))
      (hdst : dst.idx < cfg.blocks.size)
      (htransfer :
        e.transfer_block_io
          (cfg.blocks[bb]'hbb).outputs
          (cfg.blocks[dst.idx]'hdst).inputs = some e') :
      StepCFG cfg (.running bb pc e) (.running dst.idx 0 e')

abbrev CFGSteps (cfg : ControlFlowGraph) := Relation.ReflTransGen (StepCFG cfg)

end Sir
