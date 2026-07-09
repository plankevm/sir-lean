import Evm

namespace Lir

open Evm

abbrev Word := UInt256

structure Tmp where
  id : Nat
deriving DecidableEq, Repr

structure Label where
  idx : Nat
deriving DecidableEq, Repr

structure CallSpec where
  callee : Tmp
  gasFwd : Tmp
  resultTmp : Option Tmp
deriving DecidableEq, Repr

structure CreateSpec where
  value : Tmp
  initOffset : Tmp
  initSize : Tmp
  salt : Tmp
  resultTmp : Option Tmp
deriving DecidableEq, Repr

inductive Expr where
  | imm   (w : Word)
  | tmp   (t : Tmp)
  | add   (a b : Tmp)
  | lt    (a b : Tmp)
  | sload (key : Tmp)
  | gas
deriving DecidableEq, Repr

inductive Stmt where
  | assign (t : Tmp) (e : Expr)
  | sstore (key value : Tmp)
  | call   (cs : CallSpec)
  | create (cs : CreateSpec)
deriving DecidableEq, Repr

inductive Term where
  | ret    (t : Tmp)
  | stop
  | jump   (dst : Label)
  | branch (cond : Tmp) (thenL elseL : Label)
deriving DecidableEq, Repr

structure Block where
  stmts : List Stmt
  term  : Term
deriving Repr

structure Program where
  blocks : Array Block
  entry  : Label
deriving Repr

def Program.blockAt (prog : Program) (L : Label) : Option Block :=
  prog.blocks[L.idx]?

end Lir
