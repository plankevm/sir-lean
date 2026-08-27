import Evm.UInt256

abbrev U256 := Evm.UInt256

structure VarId where
  id : Nat
deriving DecidableEq, Repr

structure BlockId where
  id : Nat
deriving DecidableEq, Repr

structure FunctionId where
  id : Nat
deriving DecidableEq, Repr

structure CallArgs where
  callee : VarId
  gas : VarId
deriving DecidableEq, Repr

inductive BinOp where
  | add
  | lt
deriving DecidableEq, Repr

inductive Expr where
  | constant (value : U256)
  | var (var : VarId)
  | binaryOp (op : BinOp) (lhs rhs : VarId)
  | sload (key : VarId)
  | gas
  | call (call : CallArgs)
  | malloc (size : VarId)
  | mallocUninit (size : VarId)
  | mload32 (offset : VarId)
deriving DecidableEq, Repr

inductive Stmt where
  | assign (result : VarId) (expr : Expr)
  | sstore (key value : VarId)
  | mstore32 (offset value : VarId)
  | icall (callee : FunctionId) (ins outs : Array VarId)
deriving DecidableEq, Repr

inductive Terminator where
  | halt
  | jump (target : BlockId)
  | branch (condition : VarId) (thenTarget elseTarget : BlockId)
  | iret
deriving DecidableEq, Repr

structure Block where
  inputs : Array VarId
  statements : Array Stmt
  terminator : Terminator
  outputs : Array VarId
deriving Repr

structure Func where
  entry : Block
  rest : Array Block
deriving Repr

def Func.blocks (f : Func) : List Block := f.entry :: f.rest.toList

structure Program where
  init : Func
  main : Option Func
  rest : Array Func
deriving Repr

def Program.functions (p : Program) : Array Func := #[p.init] ++ p.main.toArray ++ p.rest

def Program.function? (p : Program) (f : FunctionId) : Option Func := p.functions[f.id]?
