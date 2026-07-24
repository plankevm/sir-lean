import Evm.UInt256
import Evm.Wheels

namespace Sir

abbrev Word := Evm.UInt256
abbrev Address := Evm.AccountAddress

structure VarId where
  id : Nat
deriving DecidableEq, Repr

structure BlockId where
  id : Nat
deriving DecidableEq, Repr

structure FunctionId where
  id : Nat
deriving DecidableEq, Repr

structure Call where
  callee : VarId
  gas : VarId
  result : VarId
deriving DecidableEq, Repr

inductive Expr where
  | constant (value : Word)
  | var (var : VarId)
  | add (lhs rhs : VarId)
  | lt (lhs rhs : VarId)
  | sload (key : VarId)
deriving DecidableEq, Repr

inductive Stmt where
  | assign (result : VarId) (value : Expr)
  | sstore (key value : VarId)
  | gas (result : VarId)
  | call (call : Call)
  | mallocUninit (result size : VarId)
  | mstore32 (offset value : VarId)
  | mload32 (result offset : VarId)
  | icall (callee : FunctionId) (args dests : Array VarId)
deriving DecidableEq, Repr

inductive Terminator where
  | halt
  | jump (target : BlockId)
  | branch (condition : VarId) (thenTarget elseTarget : BlockId)
  | iret
deriving DecidableEq, Repr

structure BasicBlock where
  inputs : Array VarId
  statements : Array Stmt
  terminator : Terminator
  outputs : Array VarId
deriving Repr

structure Function where
  blocks : Array BasicBlock
  entry : BlockId
  outputs : Option Nat
deriving Repr

structure Program where
  functions : Array Function
  initEntry : FunctionId
  mainEntry : Option FunctionId
deriving Repr

end Sir
