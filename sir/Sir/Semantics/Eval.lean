import Sir.Semantics.State

namespace Sir

def Expr.eval (ctx : CallContext) (state : MachineState) : Expr → Except IRError Word
  | Expr.constant value => .ok value
  | Expr.var id => state.locals.lookup id
  | Expr.add lhs rhs => do
      let lhsValue ← state.locals.lookup lhs
      let rhsValue ← state.locals.lookup rhs
      return Evm.UInt256.add lhsValue rhsValue
  | Expr.lt lhs rhs => do
      let lhsValue ← state.locals.lookup lhs
      let rhsValue ← state.locals.lookup rhs
      return Evm.UInt256.lt lhsValue rhsValue
  | Expr.sload key => do
      let keyValue ← state.locals.lookup key
      return state.world.loadStorage ctx.self keyValue

def eval_assign (ctx : CallContext) (s : MachineState) (result : VarId) (expr : Expr) :
    Except IRError MachineState := do
  let value ← Expr.eval ctx s expr
  .ok { s with locals := s.locals.assign result value }

def eval_sstore (ctx : CallContext) (s : MachineState) (key value : VarId) :
    Except IRError MachineState := do
  let keyValue ← s.locals.lookup key
  let valueValue ← s.locals.lookup value
  return { s with world := s.world.storeStorage ctx.self keyValue valueValue }

def eval_gas (result : VarId) (gas : Word) : MachineStateM Unit := do
  Locals.assignM result gas

def eval_call (call : Call) (result : CallResult) : MachineStateM CallRecord := do
  let callee ← Locals.lookupM call.callee
  let gas ← Locals.lookupM call.gas
  let input := { target := .ofUInt256 callee, gas := gas, world := (← get).world }
  Locals.assignM call.result (Evm.UInt256.fromBool result.success)
  modify ({ · with returnData := result.output, world := result.world' })
  return { input, result }

def eval_malloc_uninit (alloc : Allocation) (result size : VarId) : MachineStateM Unit := do
  let size ← Locals.lookupM size
  if alloc.size ≠ size.toNat then
    throw .invalidAlloc
  Locals.assignM result alloc.offset
  modify (fun s => { s with memory := s.memory.push alloc })

def eval_mstore32 (offset value : VarId) : MachineStateM Unit := do
  let offset ← Locals.lookupM offset
  let value ← Locals.lookupM value
  modify (fun s => { s with memory := s.memory.writeBytes offset value.toByteArray })

def eval_mload32 (assumed : ByteArray) (result offset : VarId) : MachineStateM Unit := do
  let offset ← Locals.lookupM offset
  let state ← get
  let bytes := state.memory.readBytes offset assumed
  Locals.assignM result (.ofNat <| Evm.fromByteArrayBigEndian bytes)

private def eval_jump (program : Program) (target : BlockId) : MachineStateM Unit := do
  let .running cursor := (← get).control | throw .invalidControl
  let source := cursor.block
  let some sourceBlock := program.block? source | throw (.invalidBlock source)
  let some targetBlock := program.block? target | throw (.invalidBlock target)
  Locals.transfer sourceBlock.outputs targetBlock.inputs
  let cursor := { block := target, position := targetBlock.startPosition }
  modify ({ · with control := .running cursor })

def eval_terminator (program : Program) : Terminator → MachineStateM Unit
  | .halt => modify (fun state => { state with control := .halted })
  | .jump target => eval_jump program target
  | .branch condition thenTarget elseTarget => do
      let value ← Locals.lookupM condition
      eval_jump program (if value = 0 then elseTarget else thenTarget)

end Sir
