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
      {state : MachineState}
      {nextControl : MachineControl}
      {result : VarId}
      {gas : Word}
      {locals' : Locals}
      (hstmt : program.decodeStmt state.control = some (nextControl, .gas result))
      (hlocals : locals' = state.locals.set result gas) :
      SmallStep program ctx state [.gas gas]
        { state with locals := locals', control := nextControl }
  | call
      {state state' : MachineState}
      {nextControl : MachineControl}
      {call : Call}
      {result : CallResult}
      {record : CallRecord}
      (hstmt : program.decodeStmt state.control = some (nextControl, .call call))
      (heval : (eval_call call result).run state = .ok (record, state')) :
      SmallStep program ctx state [.call record] { state' with control := nextControl }
  | terminator
      {state state' : MachineState}
      {terminator : Terminator}
      (hterm : program.terminatorAt state.control = some terminator)
      (heval : (eval_terminator program terminator).run state = .ok ((), state')) :
      SmallStep program ctx state [] state'

inductive Steps (program : Program) (ctx : CallContext) :
    MachineState → Trace → MachineState → Prop where
  | single
      {s s' : MachineState}
      {trace : Trace}
      (step : SmallStep program ctx s trace s') :
      Steps program ctx s trace s'
  | chain
      {s₀ s₁ s₂ : MachineState}
      {t₁ t₂ : Trace}
      (start : Steps program ctx s₀ t₁ s₁)
      (next : SmallStep program ctx s₁ t₂ s₂) :
      Steps program ctx s₀ (t₁ ++ t₂) s₂

end Sir
