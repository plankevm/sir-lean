import Sir.Semantics.State

namespace Sir

def Expr.eval (ctx : CallContext) (state : MachineState) : Expr → Except IRError Word
  | Expr.constant value => .ok value
  | Expr.var id => state.locals.get id
  | Expr.add lhs rhs => do
      let lhsValue ← state.locals.get lhs
      let rhsValue ← state.locals.get rhs
      return Evm.UInt256.add lhsValue rhsValue
  | Expr.lt lhs rhs => do
      let lhsValue ← state.locals.get lhs
      let rhsValue ← state.locals.get rhs
      return Evm.UInt256.lt lhsValue rhsValue
  | Expr.sload key => do
      let keyValue ← state.locals.get key
      return state.world.loadStorage ctx.self keyValue

def eval_assign (ctx : CallContext) (s : MachineState) (result : VarId) (expr : Expr) :
    Except IRError MachineState := do
  let value ← Expr.eval ctx s expr
  .ok { s with locals := s.locals.set result value }

def eval_sstore (ctx : CallContext) (s : MachineState) (key value : VarId) :
    Except IRError MachineState := do
  let keyValue ← s.locals.get key
  let valueValue ← s.locals.get value
  return { s with world := s.world.storeStorage ctx.self keyValue valueValue }

def eval_call (call : Call) (result : CallResult) :
    StateT MachineState (Except IRError) CallRecord := do
  let callee ← Locals.getM call.callee
  let gas ← Locals.getM call.gas
  Locals.setM call.result (Evm.UInt256.fromBool result.success)
  modify ({ · with returnData := result.output, world := result.world })
  return { target := .ofUInt256 callee, gas := gas, result := result }

private def eval_jump (program : Program) (target : BlockId) :
    StateT MachineState (Except IRError) Unit := do
  let .running cursor := (← get).control | throw .invalidControl
  let source := cursor.block
  let some sourceBlock := program.block? source | throw (.invalidBlock source)
  let some targetBlock := program.block? target | throw (.invalidBlock target)
  Locals.transfer sourceBlock.outputs targetBlock.inputs
  let cursor := { block := target, position := targetBlock.startPosition }
  modify ({ · with control := .running cursor })

def eval_terminator (program : Program) :
    Terminator → StateT MachineState (Except IRError) Unit
  | .halt => modify (fun state => { state with control := .halted })
  | .jump target => eval_jump program target
  | .branch condition thenTarget elseTarget => do
      let state ← get
      let value ← state.locals.get condition
      eval_jump program (if value = 0 then elseTarget else thenTarget)

end Sir
