import SirLean.IR
import SirLean.State

namespace Sir

def Op.eval? (ctx : Env) : Op → Option Env
  | .const var value =>
      let vars' := ctx.vars.set var value
      some { ctx with vars := vars' }
  | .add32 out lhs rhs => do
      let lValue ← ctx.vars.get? lhs
      let rValue ← ctx.vars.get? rhs
      let vars' := ctx.vars.set out (lValue + rValue)
      some { ctx with vars := vars' }
  | .lessThan out lhs rhs => do
      let lValue ← ctx.vars.get? lhs
      let rValue ← ctx.vars.get? rhs
      let vars' := ctx.vars.set out (if lValue < rValue then 1 else 0)
      some { ctx with vars := vars' }
  | .persistentLoad out addr => do
      let addrValue ← ctx.vars.get? addr
      some { ctx with vars := ctx.vars.set out (ctx.world.get addrValue) }
  | .persistentStore addr value => do
      let addrValue ← ctx.vars.get? addr
      let valueValue ← ctx.vars.get? value
      some { ctx with world := ctx.world.set addrValue valueValue }

def EndOp.eval? : EndOp → Env → Option Continuation
  | .exit codeVar, e => do
      let code ← e.vars.get? codeVar
      .some (.terminated (.exited code))
  | .jump dst, _ => some (.goto dst)
  | .jump_if j, e =>
    do
      let cond_value ← e.vars.get? j.cond
      let dst :=
        if cond_value = 0
        then j.dst_if_zero
        else j.dst_if_non_zero
      .some (.goto dst)


def BasicBlock.initialCtx (w : World) : Env :=
  { vars := .empty, world := w }

def BasicBlock.eval? (bb : BasicBlock) (w : World) (vars : VarCtx) : Option (World × VarCtx × Continuation) := do
  let ctx0 : Env := { vars := vars, world := w }
  let ctx ← bb.ops.foldlM (fun ctx op => Op.eval? ctx op) ctx0
  let cont ← bb.last.eval? ctx
  some (ctx.world, ctx.vars, cont)

inductive CFGEvalError where
  | outOfFuel
  | stuck
deriving DecidableEq, Repr

/-- `none` from a partial operation means evaluation got stuck. -/
instance : MonadLift Option (Except CFGEvalError) where
  monadLift
    | some x => .ok x
    | none => .error .stuck

def ControlFlowGraph.resolveSucc?
  (cfg : ControlFlowGraph)
  (bbIdx : Fin cfg.blocks.size)
  (dst : BasicBlockId) :
  Except CFGEvalError (Fin cfg.blocks.size)  :=
  if hsucc : dst ∈ cfg.blocks[bbIdx].successors then
    .ok (cfg.succ_to_idx (bb := bbIdx) hsucc)
  else
    throw .stuck

def ControlFlowGraph.eval?
    (cfg : ControlFlowGraph) (w : World) (fuel : Nat) :
    Except CFGEvalError (Termination × World) :=
  go fuel cfg.entry w .empty
where
  go : Nat → Fin cfg.blocks.size → World → VarCtx → Except CFGEvalError (Termination × World)
    | 0, _, _, _ => throw .outOfFuel
    | fuel + 1, bbIdx, w, vars => do
      let bb := cfg.blocks[bbIdx]
      let (w, vars, cont) ← bb.eval? w vars
      match cont with
      | .terminated t => return (t, w)
      | .goto dst =>
        let dstIdx ← cfg.resolveSucc? bbIdx dst
        let vars ← vars.transfer_block_io bb.outputs cfg.blocks[dstIdx].inputs
        go fuel dstIdx w vars

end Sir
