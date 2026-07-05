import SirLean.Basic

namespace Sir.Source

structure BasicBlockId where
  idx : Nat
deriving DecidableEq, Repr

def BasicBlockId.ofNat (n : Nat) : BasicBlockId := ⟨n⟩
def BasicBlockId.toNat (v : BasicBlockId) : Nat := v.idx

inductive Op where
  | const (var : VarId) (value: Word)
  | add32 (res lhs rhs : VarId)
  | lt (res lhs rhs : VarId)
  | malloc (out size : VarId)
  | memwrite (addr value : VarId)
  | memread (out addr : VarId)
  | sload (out addr : VarId)
  | sstore (addr value : VarId)
deriving DecidableEq, Repr

structure JumpIf where
  cond : VarId
  dst_if_zero : BasicBlockId
  dst_if_non_zero : BasicBlockId
deriving DecidableEq, Repr

inductive EndOp where
  | exit (exit_code_var : VarId)
  | jump (dst : BasicBlockId)
  | jump_if (j : JumpIf)
deriving DecidableEq, Repr

structure BasicBlock where
  inputs : Array VarId
  ops : Array Op
  last : EndOp
  outputs : Array VarId

structure ControlFlowGraph where
  blocks: Array BasicBlock
  entry : BasicBlockId

end Sir.Source
