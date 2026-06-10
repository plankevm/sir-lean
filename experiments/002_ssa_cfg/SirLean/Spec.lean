import SirLean.Proof
import SirLean.SmallStep

namespace Sir

-- theorem BasicBlock.eval?_isSome : (BasicBlock.eval? bb w).isSome = true :=
--   BasicBlock.eval?_isSome.proof
-- 
-- def BasicBlock.eval (bb : BasicBlock) (w : World) := (bb.eval? w).get (BasicBlock.eval?_isSome)
-- 
-- def BasicBlock.execStart (bb : BasicBlock) (w : World) : BlockExecState bb :=
--   let pos :=
--     if h : 0 < bb.ops.size
--     then .op ⟨0, h⟩
--     else .last
--   { env := BasicBlock.initialCtx w, pos := pos }
-- 
-- def BasicBlock.execEnd (bb : BasicBlock) (w : World) : BlockExecState bb :=
--   let (env, t) := bb.eval w
--   { env := env, pos := .terminated t }
-- 
-- theorem BasicBlock.eval_is_blockSteps (bb : BasicBlock) (w : World) :
--     BlockSteps (bb.execStart w) (bb.execEnd w) := by
--   simp [BasicBlock.execStart, BasicBlock.execEnd, BasicBlock.eval]
--   exact BasicBlock.eval_is_blockSteps_proof bb w

end Sir
