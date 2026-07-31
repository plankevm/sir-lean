import Sir.Spec.State

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
      return state.globals.world.loadStorage ctx.self keyValue

def eval_assign (ctx : CallContext) (s : MachineState) (result : VarId) (expr : Expr) :
    Except IRError MachineState := do
  let value ← Expr.eval ctx s expr
  .ok { s with locals := s.locals.assign result value }

def eval_sstore (ctx : CallContext) (s : MachineState) (key value : VarId) :
    Except IRError MachineState := do
  let keyValue ← s.locals.lookup key
  let valueValue ← s.locals.lookup value
  return { s with globals :=
    { s.globals with world := s.globals.world.storeStorage ctx.self keyValue valueValue } }

def eval_gas (result : VarId) (gas : Word) : MachineStateM Unit := do
  Locals.assignM result gas

def eval_call (call : Call) (result : CallResult) : MachineStateM CallRecord := fun s => do
  let callee ← s.locals.lookup call.callee
  let gas ← s.locals.lookup call.gas
  let input : CallInput := { target := .ofUInt256 callee, gas := gas, world := s.globals.world }
  let state' := { s with
    locals := s.locals.assign call.result (Evm.UInt256.fromBool result.success)
    globals := { s.globals with returnData := result.output, world := result.world' } }
  .ok ({ input, result }, state')

def eval_malloc_uninit (alloc : Allocation) (result size : VarId) : MachineStateM Unit := do
  let size ← Locals.lookupM size
  if alloc.size ≠ size.toNat then
    throw .invalidAlloc
  Locals.assignM result alloc.offset
  modify (fun s => { s with globals := { s.globals with memory := s.globals.memory.push alloc } })

def eval_mstore32 (offset value : VarId) : MachineStateM Unit := do
  let offset ← Locals.lookupM offset
  let value ← Locals.lookupM value
  modify (fun s =>
    { s with globals :=
      { s.globals with memory := s.globals.memory.writeBytes offset value.toByteArray } })

def eval_mload32 (assumed : ByteArray) (result offset : VarId) : MachineStateM Unit := do
  let offset ← Locals.lookupM offset
  let state ← get
  let bytes := state.globals.memory.readBytes offset assumed
  Locals.assignM result (.ofNat <| Evm.fromByteArrayBigEndian bytes)

def eval_jump (program : Program) (target : BlockId) : MachineStateM Unit := do
  let .running cursor := (← get).control | throw .invalidControl
  let source := cursor.block
  let some sourceBlock := program.block? cursor | throw (.invalidBlock source)
  let targetCursor := { cursor with block := target }
  let some targetBlock := program.block? targetCursor | throw (.invalidBlock target)
  Locals.transfer sourceBlock.outputs targetBlock.inputs
  let targetCursor := { targetCursor with position := targetBlock.startPosition }
  modify ({ · with control := .running targetCursor })

def eval_terminator (program : Program) : Terminator → MachineStateM Unit
  | .halt => modify (fun state => { state with control := .halted })
  | .jump target => eval_jump program target
  | .branch condition thenTarget elseTarget => do
      let value ← Locals.lookupM condition
      eval_jump program (if value = 0 then elseTarget else thenTarget)
  | .iret => do
      let .running cursor := (← get).control | throw .invalidControl
      let some block := program.block? cursor | throw (.invalidBlock cursor.block)
      let state ← get
      let rs ← liftM (block.outputs.mapM state.locals.lookup)
      modify ({ · with control := .returned rs })

mutual

inductive SmallStep (program : Program) (ctx : CallContext) :
    MachineState → Trace → MachineState → Prop where
  | assign
      {state state' : MachineState}
      {nextControl : MachineControl}
      {result : VarId}
      {expr : Expr}
      (hstmt : program.decodeStmt state.control = some (nextControl, .assign result expr))
      (heval : eval_assign ctx state result expr = .ok state') :
      SmallStep program ctx state [] { state' with control := nextControl }
  | sstore
      {state state' : MachineState}
      {nextControl : MachineControl}
      {key value : VarId}
      (hstmt : program.decodeStmt state.control = some (nextControl, .sstore key value))
      (heval : eval_sstore ctx state key value = .ok state') :
      SmallStep program ctx state [] { state' with control := nextControl }
  | gas
      {state state' : MachineState}
      {nextControl : MachineControl}
      {result : VarId}
      {gas : Word}
      (hstmt : program.decodeStmt state.control = some (nextControl, .gas result))
      (heval : (eval_gas result gas).run state = .ok ((), state')) :
      SmallStep program ctx state [.gas gas] { state' with control := nextControl }
  | call
      {state state' : MachineState}
      {nextControl : MachineControl}
      {call : Call}
      {result : CallResult}
      {record : CallRecord}
      (hstmt : program.decodeStmt state.control = some (nextControl, .call call))
      (heval : (eval_call call result).run state = .ok (record, state')) :
      SmallStep program ctx state [.call record] { state' with control := nextControl }
  | mallocUninit
      {state state' : MachineState}
      {nextControl : MachineControl}
      {alloc : Allocation}
      {result size : VarId}
      (hstmt : program.decodeStmt state.control = some (nextControl, .mallocUninit result size))
      (halloc : state.globals.memory.IsValidNewAlloc alloc)
      (heval : (eval_malloc_uninit alloc result size).run state = .ok ((), state')) :
      SmallStep program ctx state [] { state' with control := nextControl }
  | mstore32
      {state state' : MachineState}
      {nextControl : MachineControl}
      {offset value : VarId}
      (hstmt : program.decodeStmt state.control = some (nextControl, .mstore32 offset value))
      (heval : (eval_mstore32 offset value).run state = .ok ((), state')) :
      SmallStep program ctx state [] { state' with control := nextControl }
  | mload32
      {state state' : MachineState}
      {nextControl : MachineControl}
      {assumed : Vector UInt8 32}
      {result offset : VarId}
      (hstmt : program.decodeStmt state.control = some (nextControl, .mload32 result offset))
      (heval : (eval_mload32 ⟨assumed.toArray⟩ result offset).run state = .ok ((), state')) :
      SmallStep program ctx state [] { state' with control := nextControl }
  | terminator
      {state state' : MachineState}
      {terminator : Terminator}
      (hterm : program.terminatorAt state.control = some terminator)
      (heval : (eval_terminator program terminator).run state = .ok ((), state')) :
      SmallStep program ctx state [] state'
  | icall
      {state : MachineState}
      {nextControl : MachineControl}
      {callee : FunctionId}
      {args dests : Array VarId}
      {vs rs : Array Word}
      {t : Trace}
      {g' : Globals}
      {locals' : Locals}
      (hstmt : program.decodeStmt state.control = some (nextControl, .icall callee args dests))
      (hargs : args.mapM (state.locals.lookup ·) = .ok vs)
      (hcallee : EvalFn program ctx callee state.globals vs t g' (.returned rs))
      (hbind : Locals.bindReturns state.locals dests rs = .ok locals') :
      SmallStep program ctx state t
        { state with globals := g', locals := locals', control := nextControl }
  | icallHalted
      {state : MachineState}
      {nextControl : MachineControl}
      {callee : FunctionId}
      {args dests : Array VarId}
      {vs : Array Word}
      {t : Trace}
      {g' : Globals}
      (hstmt : program.decodeStmt state.control = some (nextControl, .icall callee args dests))
      (hargs : args.mapM (state.locals.lookup ·) = .ok vs)
      (hcallee : EvalFn program ctx callee state.globals vs t g' .halted) :
      SmallStep program ctx state t { globals := g', control := .halted }

inductive Steps (program : Program) (ctx : CallContext) :
    MachineState → Trace → MachineState → Prop where
  | refl {s : MachineState} : Steps program ctx s [] s
  | tail
      {s mid s' : MachineState}
      {t₁ t₂ : Trace}
      (start : Steps program ctx s t₁ mid)
      (next : SmallStep program ctx mid t₂ s') :
      Steps program ctx s (t₁ ++ t₂) s'

inductive EvalFn (program : Program) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals → FunctionOutcome → Prop where
  | returned
      {f : FunctionId}
      {g : Globals}
      {args rs : Array Word}
      {t : Trace}
      {s₀ exit : MachineState}
      (hentry : program.callState? f g args = some s₀)
      (hrun : Steps program ctx s₀ t exit)
      (hret : exit.control = .returned rs) :
      EvalFn program ctx f g args t exit.globals (.returned rs)
  | halted
      {f : FunctionId}
      {g : Globals}
      {args : Array Word}
      {t : Trace}
      {s₀ exit : MachineState}
      (hentry : program.callState? f g args = some s₀)
      (hrun : Steps program ctx s₀ t exit)
      (hhalt : exit.control = .halted) :
      EvalFn program ctx f g args t exit.globals .halted

end
end Sir
