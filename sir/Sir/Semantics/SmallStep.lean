import Sir.Semantics.Eval

namespace Sir

/-- The canonical one-step operational semantics of a fixed IR program. -/
inductive SmallStep (program : Program) (ctx : CallContext) : MachineState → Trace → MachineState → Prop where
  | assign
      (hstmt : program.decodeStmt state.control = some (nextControl, .assign result expr))
      (heval : eval_assign ctx state result expr = .ok state') :
      SmallStep program ctx state [] { state' with control := nextControl }
  | sstore
      (hstmt : program.decodeStmt state.control = some (nextControl, .sstore key value))
      (heval : eval_sstore ctx state key value = .ok state') :
      SmallStep program ctx state [] { state with control := nextControl }
  | gas
      (hstmt : program.decodeStmt state.control = some (nextControl, .gas result))
      (hlocals : locals' = state.locals.set result gas) :
      SmallStep program ctx state [.gas gas] { state with locals := locals', control := nextControl }
  | call
      (hstmt : program.decodeStmt state.control = some (nextControl, .call call))
      (heval : eval_call state call result = .ok (state', record)) :
      SmallStep program ctx state [.call record] { state' with control := nextControl }
  | terminator
      (hterm : program.terminatorAt state.control = some terminator)
      (heval : terminator.eval state = .ok nextControl) :
      SmallStep program ctx state [] { state with control := nextControl }

inductive Steps (program : Program) (ctx : CallContext) : MachineState → Trace → MachineState → Prop where
  | single 
      (step : SmallStep program ctx s trace s') : Steps program ctx s trace s'
  | chain
    (start : Steps program ctx s₀ t₁ s₁)
    (next : SmallStep program ctx s₁ t₂ s₂) :
    Steps program ctx s₀ (t₁ ++ t₂) s₂

end Sir
