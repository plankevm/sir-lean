import Sir.Core.Spec.Base

namespace Sir

inductive BlockPosition where
  | statement (index : Nat)
  | terminator
deriving DecidableEq, Repr

structure ProgramCursor where
  fn : FunctionId
  block : BlockId
  position : BlockPosition
deriving DecidableEq, Repr

inductive Control where
  | running (cursor : ProgramCursor)
  | returned (rs : Array Word)
  | halted
deriving DecidableEq, Repr

def FunctionOutcome.toControl : FunctionOutcome → Control
  | .returned results => .returned results
  | .halted => .halted

end Sir
