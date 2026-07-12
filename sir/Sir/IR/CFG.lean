import Sir.Core.Types

namespace Sir

structure Call where
  callee : VarId
  gas : VarId
deriving DecidableEq, Repr

inductive Expr where
  | constant (value : Word)
  | var (var : VarId)
  | add (lhs rhs : VarId)
  | lt (lhs rhs : VarId)
  | sload (key : VarId)
  | gas
  | call (call : Call)
deriving DecidableEq, Repr

inductive Stmt where
  | assign (result : VarId) (value : Expr)
  | sstore (key value : VarId)
deriving DecidableEq, Repr

inductive Terminator where
  | halt
  | jump (target : BlockId)
  | branch (condition : VarId) (thenTarget elseTarget : BlockId)
deriving DecidableEq, Repr

structure BasicBlock where
  statements : Array Stmt
  terminator : Terminator
deriving Repr

structure Program where
  blocks : Array BasicBlock
  entry : BlockId
deriving Repr

end Sir
