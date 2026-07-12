import Sir.Semantics.State

namespace Sir

structure CallRequest where
  callee : Address
  gas : Word
  successResultTarget : VarId
  resumePc : ProgramCounter

inductive StepResult where
  | next (pc : ProgramCounter)
  | needsCall (request : CallRequest)
  | halted

end Sir
