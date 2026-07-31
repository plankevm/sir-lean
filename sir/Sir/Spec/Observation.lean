import Sir.Spec.Run

namespace Sir

inductive ObservableOutcome where
  | gas
  | call (input : CallInput)
  | halt (world : World)

inductive FunctionObservableOutcome where
  | gas
  | call (input : CallInput)
  | halt (world : World)
  | returned (world : World) (values : Array Word)

inductive Query where
  | gas
  | call (input : CallInput)

def Event.query : Event → Query
  | .gas _ => .gas
  | .call record => .call record.input

/-- Events are observed on the function's own step chain, so an event emitted inside a
callee that neither returns nor halts is observed nowhere. -/
def Program.NextFunctionObservableEffect (program : Program) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word)
    (history : Trace) : FunctionObservableOutcome → Prop
  | .gas =>
      ∃ gas trace rest state,
        program.RunsFunction ctx function globals args trace state ∧
        trace = history ++ .gas gas :: rest
  | .call input =>
      ∃ call trace rest state,
        call.input = input ∧
        program.RunsFunction ctx function globals args trace state ∧
        trace = history ++ .call call :: rest
  | .halt world =>
      ∃ finalGlobals,
        EvalFn program ctx function globals args history finalGlobals .halted ∧
        finalGlobals.world = world
  | .returned world values =>
      ∃ finalGlobals,
        EvalFn program ctx function globals args history finalGlobals (.returned values) ∧
        finalGlobals.world = world

def ObservableOutcome.functionOutcome : ObservableOutcome → FunctionObservableOutcome
  | .gas => .gas
  | .call input => .call input
  | .halt world => .halt world

def Program.NextObservableEffect (program : Program) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) (history : Trace) (outcome : ObservableOutcome) : Prop :=
  program.NextFunctionObservableEffect ctx entry { world := world₀ } #[] history
    outcome.functionOutcome

def Program.FunctionDeterministicFrom (program : Program) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) : Prop :=
  ∀ history outcome₁ outcome₂,
    program.NextFunctionObservableEffect ctx function globals args history outcome₁ →
    program.NextFunctionObservableEffect ctx function globals args history outcome₂ →
    outcome₁ = outcome₂

def Program.DeterministicFrom (program : Program) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) : Prop :=
  ∀ history outcome₁ outcome₂,
    program.NextObservableEffect ctx entry world₀ history outcome₁ →
    program.NextObservableEffect ctx entry world₀ history outcome₂ →
    outcome₁ = outcome₂

def Program.Deterministic (program : Program) : Prop :=
  ∀ ctx world₀,
    program.AtEntries (fun entry => program.DeterministicFrom ctx entry world₀)

def Stmt.isMemOracle : Stmt → Prop
  | .mallocUninit _ _ | .mload32 _ _ => True
  | _ => False

def Program.MemOracleFree (p : Program) : Prop :=
  ∀ s, p.HasStmt s → ¬ s.isMemOracle

def Trace.QueryDivergence (t₁ t₂ : Trace) : Prop :=
  ∃ pre a r₁ b r₂,
    t₁ = pre ++ a :: r₁ ∧ t₂ = pre ++ b :: r₂ ∧ a ≠ b ∧ a.query = b.query

def Program.FunctionDeterministic (program : Program) (function : FunctionId) : Prop :=
  ∀ ctx globals args trace₁ trace₂ finalGlobals₁ finalGlobals₂ outcome₁ outcome₂,
    EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁ →
    EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂ →
    (trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂) ∨
      trace₁.QueryDivergence trace₂

end Sir
