import Sir.Semantics.Eval

namespace Sir

/-- The canonical one-step operational semantics of a fixed IR program. -/
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
      {locals' : Locals}
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
      (halloc : state.memory.IsValidNewAlloc alloc)
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

inductive Steps (program : Program) (ctx : CallContext) :
    MachineState → Trace → MachineState → Prop where
  | refl {s : MachineState} : Steps program ctx s [] s
  | tail
      {s mid s' : MachineState}
      {t₁ t₂ : Trace}
      (start : Steps program ctx s t₁ mid)
      (next : SmallStep program ctx mid t₂ s') :
      Steps program ctx s (t₁ ++ t₂) s'

def Runs (program : Program) (ctx : CallContext) (w₀ : World)
    (trace : Trace) (state : MachineState) : Prop :=
  ∃ cursor,
    program.startCursor? = some cursor ∧
    Steps program ctx { world := w₀, control := .running cursor } trace state

inductive ObservableOutcome where
  | gas
  | call (input : CallInput)
  | halt (world : World)

def NextObservableEffect (p : Program) (ctx : CallContext) (w₀ : World) (trace : Trace) :
    ObservableOutcome → Prop
  | .gas =>
      ∃ gas s', Runs p ctx w₀ (trace ++ [.gas gas]) s'
  | .call input =>
      ∃ call s',
        call.input = input ∧
        Runs p ctx w₀ (trace ++ [.call call]) s'
  | .halt w' =>
      ∃ s',
        Runs p ctx w₀ trace s' ∧
        s'.control = .halted ∧
        s'.world = w'

def Deterministic (p : Program) : Prop :=
  ∀ ctx w₀ trace outcome₁ outcome₂,
    NextObservableEffect p ctx w₀ trace outcome₁ →
    NextObservableEffect p ctx w₀ trace outcome₂ →
    outcome₁ = outcome₂

end Sir
