import Sir.Spec.Step

namespace Sir

/-- Partial execution from a callable function exposes reachability before the function returns or halts. -/
def Program.RunsFunction (program : Program) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (state : MachineState) : Prop :=
  ∃ initial,
    program.callState? function globals args = some initial ∧
    Steps program ctx initial trace state

/-- Finite traces descend through the internal call that is currently active. -/
inductive FnPrefix (program : Program) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Prop where
  | steps
      {function : FunctionId}
      {globals : Globals}
      {args : Array Word}
      {trace : Trace}
      {initial state : MachineState}
      (hentry : program.callState? function globals args = some initial)
      (hrun : Steps program ctx initial trace state) :
      FnPrefix program ctx function globals args trace
  | descend
      {function callee : FunctionId}
      {globals : Globals}
      {args values : Array Word}
      {trace₁ trace₂ : Trace}
      {initial state : MachineState}
      {nextControl : MachineControl}
      {callArgs destinations : Array VarId}
      (hentry : program.callState? function globals args = some initial)
      (hrun : Steps program ctx initial trace₁ state)
      (hstmt :
        program.decodeStmt state.control = some (nextControl, .icall callee callArgs destinations))
      (hargs : callArgs.mapM (state.locals.lookup ·) = .ok values)
      (hinner : FnPrefix program ctx callee state.globals values trace₂) :
      FnPrefix program ctx function globals args (trace₁ ++ trace₂)

/-- Entry reachability specializes callable-function execution to an initial world and no arguments. -/
def Program.Runs (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (state : MachineState) : Prop :=
  program.RunsFunction ctx entry { world := world } #[] trace state

/-- A completed run: reachable and halted. -/
def Program.RunsTo (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (final : MachineState) : Prop :=
  program.Runs ctx entry world trace final ∧ final.control = .halted

/-- A completed run of the deployment entry. -/
def Program.RunsInit (program : Program) (ctx : CallContext)
    (world : World) (trace : Trace) (final : Globals) : Prop :=
  EvalFn program ctx program.initEntry { world := world } #[] trace final .halted

/-- A completed run of the main entry, when the program declares one. -/
def Program.RunsMain (program : Program) (ctx : CallContext)
    (world : World) (trace : Trace) (final : Globals) : Prop :=
  ∃ entry, program.mainEntry = some entry ∧
    EvalFn program ctx entry { world := world } #[] trace final .halted

end Sir
