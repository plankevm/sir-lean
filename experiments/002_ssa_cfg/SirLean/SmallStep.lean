import Mathlib.Logic.Relation
import SirLean.IR
import SirLean.State

namespace Sir

inductive StepOp : Op → Env → Env → Prop where
  | const :
      StepOp (.const var value) ctx { ctx with vars := ctx.vars.set var value }
  | add32 (ctx : Env) (lhs_set : ctx.var_eq v1 x1) (rhs_set : ctx.var_eq v2 x2) :
      StepOp (.add32 out v1 v2) ctx { ctx with vars := ctx.vars.set out (x1 + x2) }
  | lessThan (ctx : Env) (lhs_set : ctx.var_eq v1 x1) (rhs_set : ctx.var_eq v2 x2) :
      StepOp (.lessThan out v1 v2) ctx { ctx with vars := ctx.vars.set out (if x1 < x2 then 1 else 0) }
  | persistentLoad (ctx : Env) (set : ctx.var_eq v k) :
      StepOp (.persistentLoad out v) ctx { ctx with vars := ctx.vars.set out (ctx.world.get k)  }
  | persistentStore
    (ctx : Env)
    (addr_set : ctx.var_eq addr_v addr)
    (value_set : ctx.var_eq value_v value)
    : StepOp (.persistentStore addr_v value_v) ctx { ctx with world := ctx.world.set addr value }

inductive StepEndOp : EndOp → Env → Continuation → Prop where
  | exit (set : s.var_eq v code) : StepEndOp (.exit v) s (.terminated (.exited code))
  | jump : StepEndOp (.jump dst) s (.goto dst)
  | jump_if_zero (set : s.var_eq j.cond 0) : StepEndOp (.jump_if j) s (.goto j.dst_if_zero)
  | jump_if_non_zero (x_non_zero : x ≠ 0) (set : s.var_eq j.cond x) : StepEndOp (.jump_if j) s (.goto j.dst_if_non_zero)

inductive BlockExecutionPos (bb : BasicBlock) where
  | op (op_idx : Fin bb.ops.size)
  | last
  | continuing (c : Continuation)

def BlockExecutionPos.initial (bb : BasicBlock) : BlockExecutionPos bb :=
  if at_least_one : 0 < bb.ops.size
  then .op ⟨ 0, at_least_one ⟩
  else .last

structure BlockExecState (bb : BasicBlock) where
  env : Env
  pos : BlockExecutionPos bb

inductive StepBlock {bb : BasicBlock} : BlockExecState bb → BlockExecState bb → Prop where
  | op_to_next
    (i : Fin bb.ops.size)
    (op_step : StepOp bb.ops[i] e e')
    (has_next : i.val + 1 < bb.ops.size)
    : StepBlock { env := e, pos := .op i } { env := e', pos := .op ⟨i.val + 1, has_next⟩  }
  | op_to_last
    (i : Fin bb.ops.size)
    (op_step : StepOp bb.ops[i] env env')
    (no_next : i.val + 1 = bb.ops.size)
    : StepBlock { env := env, pos := .op i } { env := env', pos := .last }
  | last (terminates : StepEndOp bb.last env c)
    : StepBlock { env := env, pos := .last } { env := env, pos := .continuing c }

abbrev BlockSteps {bb : BasicBlock} := Relation.ReflTransGen (StepBlock (bb := bb))

structure CFGExecState (cfg : ControlFlowGraph) where
  bb : Fin cfg.blocks.size
  state : BlockExecState cfg.blocks[bb]

inductive StepCFG {cfg : ControlFlowGraph} : CFGExecState cfg → CFGExecState cfg → Prop where
  | step_bb
    {s : CFGExecState cfg } { state' : BlockExecState cfg.blocks[s.bb] }
    (bb_step : StepBlock (bb := cfg.blocks[s.bb]) s.state state')
    : StepCFG s { bb := s.bb, state := state' }
  | goto
    { dst : BasicBlockId }
    (hto : dst ∈ cfg.blocks[bb].successors)
    (htransfer :
      e.transfer_block_io
        cfg.blocks[bb].outputs
        (cfg.blocks[cfg.succ_to_idx hto]).inputs
        (cfg.succ_io_size_eq bb hto) = some e' )
    : StepCFG
      { bb := bb, state := { env := e, pos := .continuing (.goto dst) } }
      {
        bb := cfg.succ_to_idx hto,
        state := {
          env := e',
          pos := BlockExecutionPos.initial (cfg.blocks[cfg.succ_to_idx hto])
        }
      }

end Sir
