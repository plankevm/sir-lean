import Sir.Machine.Spec.Operation

namespace Sir.Machine

open Sir

inductive BlockPosition where
  | statement (index : Nat)
  | terminator
  deriving DecidableEq, Repr

structure ProgramCursor where
  fn : FunctionId
  block : BlockId
  position : BlockPosition
  deriving DecidableEq, Repr

inductive MachineControl where
  | running (cursor : ProgramCursor)
  | returned (rs : Array Word)
  | halted
  deriving DecidableEq, Repr

def _root_.Sir.FunctionOutcome.toControl : FunctionOutcome → MachineControl
  | .returned results => .returned results
  | .halted => .halted

structure OperandFrame where
  Environment : Type
  Source : Type
  Destination : Type
  fetch : Environment → Source → Except IRError (Array Word)
  store : Environment → Destination → Array Word → Except IRError Environment

inductive Instruction.Kind where
  | primitive (operation : Operation)
  | icall (callee : FunctionId)
deriving DecidableEq, Repr

structure Instruction (frame : OperandFrame) where
  kind : Instruction.Kind
  source : frame.Source
  destination : frame.Destination

structure State (frame : OperandFrame) where
  globals : Globals
  environment : frame.Environment
  control : MachineControl

structure Decoder (frame : OperandFrame) where
  decode : MachineControl → Option (Instruction frame × MachineControl)
  control : frame.Environment → Globals → MachineControl →
    Option (Trace × frame.Environment × Globals × MachineControl)
  resume : FunctionOutcome → frame.Environment → frame.Destination → MachineControl →
    Option (frame.Environment × MachineControl)
  entry : FunctionId → Globals → Array Word → Option (State frame)

def Decoder.Exclusive {frame : OperandFrame} (decoder : Decoder frame) : Prop :=
  ∀ env globals control instruction next,
    decoder.decode control = some (instruction, next) →
    decoder.control env globals control = none

def Decoder.Terminal {frame : OperandFrame} (decoder : Decoder frame) : Prop :=
  (∀ env globals results,
    decoder.decode (.returned results) = none ∧
    decoder.control env globals (.returned results) = none) ∧
  (∀ env globals,
    decoder.decode .halted = none ∧
    decoder.control env globals .halted = none)

def Decoder.NoMload {frame : OperandFrame} (decoder : Decoder frame) : Prop :=
  ∀ control src dst next,
    decoder.decode control = some (⟨Instruction.Kind.primitive .mload32, src, dst⟩, next) → False

def Decoder.NoMalloc {frame : OperandFrame} (decoder : Decoder frame) : Prop :=
  (∀ control src dst next,
    decoder.decode control = some (⟨Instruction.Kind.primitive .malloc, src, dst⟩, next) → False) ∧
  (∀ control src dst next,
    decoder.decode control = some (⟨Instruction.Kind.primitive .mallocUninit, src, dst⟩, next) → False)

inductive OperandFrame.Fires (frame : OperandFrame) (policy : MemoryPolicy) (ctx : CallContext)
    (operation : Operation) (src : frame.Source) (dst : frame.Destination) :
    frame.Environment → Globals → Trace → frame.Environment → Globals → Prop where
  | next
      {env env' : frame.Environment} {globals globals' : Globals}
      {operands results : Array Word} {trace : Trace} {oracle : operation.Oracle}
      (hadmissible : operation.Admissible policy globals operands oracle)
      (hfetch : frame.fetch env src = .ok operands)
      (hexecute : operation.execute ctx oracle globals operands =
        .ok (.next results globals' trace))
      (hstore : frame.store env dst results = .ok env') :
      frame.Fires policy ctx operation src dst env globals trace env' globals'

inductive OperandFrame.FiresHalt (frame : OperandFrame) (policy : MemoryPolicy) (ctx : CallContext)
    (operation : Operation) (src : frame.Source) :
    frame.Environment → Globals → Trace → Globals → Prop where
  | halted
      {env : frame.Environment} {globals globals' : Globals}
      {operands : Array Word} {trace : Trace} {oracle : operation.Oracle}
      (hadmissible : operation.Admissible policy globals operands oracle)
      (hfetch : frame.fetch env src = .ok operands)
      (hexecute : operation.execute ctx oracle globals operands =
        .ok (.halted globals' trace)) :
      frame.FiresHalt policy ctx operation src env globals trace globals'

mutual

inductive Step (frame : OperandFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    State frame → Trace → State frame → Prop where
  | operation
      {state : State frame} {operation : Operation}
      {src : frame.Source} {dst : frame.Destination} {next : MachineControl}
      {trace : Trace} {env' : frame.Environment} {globals' : Globals}
      (hdecode : decoder.decode state.control =
        some (⟨Instruction.Kind.primitive operation, src, dst⟩, next))
      (hfires : frame.Fires policy ctx operation src dst state.environment state.globals
        trace env' globals') :
      Step frame decoder policy ctx state trace
        { globals := globals', environment := env', control := next }
  | operationHalted
      {state : State frame} {operation : Operation}
      {src : frame.Source} {dst : frame.Destination} {next : MachineControl}
      {trace : Trace} {globals' : Globals}
      (hdecode : decoder.decode state.control =
        some (⟨Instruction.Kind.primitive operation, src, dst⟩, next))
      (hfires : frame.FiresHalt policy ctx operation src state.environment state.globals
        trace globals') :
      Step frame decoder policy ctx state trace
        { globals := globals', environment := state.environment, control := .halted }
  | internalCall
      {state : State frame} {callee : FunctionId}
      {src : frame.Source} {dst : frame.Destination} {next : MachineControl}
      {values : Array Word} {trace : Trace} {globals' : Globals}
      {outcome : FunctionOutcome} {env' : frame.Environment} {control' : MachineControl}
      (hdecode : decoder.decode state.control =
        some (⟨Instruction.Kind.icall callee, src, dst⟩, next))
      (hfetch : frame.fetch state.environment src = .ok values)
      (hcallee : FunctionEvaluation frame decoder policy ctx callee state.globals values
        trace globals' outcome)
      (hresume : decoder.resume outcome state.environment dst next = some (env', control')) :
      Step frame decoder policy ctx state trace
        { globals := globals', environment := env', control := control' }
  | control
      {state : State frame} {trace : Trace} {env' : frame.Environment}
      {globals' : Globals} {control' : MachineControl}
      (hcontrol : decoder.control state.environment state.globals state.control =
        some (trace, env', globals', control')) :
      Step frame decoder policy ctx state trace
        { globals := globals', environment := env', control := control' }

inductive Steps (frame : OperandFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    State frame → Trace → State frame → Prop where
  | refl {state : State frame} :
      Steps frame decoder policy ctx state [] state
  | tail
      {state middle final : State frame} {trace₁ trace₂ : Trace}
      (start : Steps frame decoder policy ctx state trace₁ middle)
      (next : Step frame decoder policy ctx middle trace₂ final) :
      Steps frame decoder policy ctx state (trace₁ ++ trace₂) final

inductive FunctionEvaluation (frame : OperandFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals →
      FunctionOutcome → Prop where
  | exit
      {function : FunctionId} {globals : Globals} {args : Array Word}
      {trace : Trace} {initial exit : State frame} {outcome : FunctionOutcome}
      (hentry : decoder.entry function globals args = some initial)
      (hrun : Steps frame decoder policy ctx initial trace exit)
      (hexit : exit.control = outcome.toControl) :
      FunctionEvaluation frame decoder policy ctx function globals args trace exit.globals outcome

end

def StepDialogue {frame : OperandFrame} (decoder : Decoder frame) (policy : MemoryPolicy)
    (ctx : CallContext) (state : State frame) (trace : Trace) (final : State frame) : Prop :=
  ∀ trace₂ final₂, Step frame decoder policy ctx state trace₂ final₂ →
    (trace = trace₂ ∧ final = final₂) ∨ Trace.QueryDivergence trace trace₂

def RunDialogue {frame : OperandFrame} (decoder : Decoder frame) (policy : MemoryPolicy)
    (ctx : CallContext) (state : State frame) (trace : Trace) (final : State frame) : Prop :=
  ∀ trace₂ final₂, Steps frame decoder policy ctx state trace₂ final₂ →
    (∃ suffix, Steps frame decoder policy ctx final suffix final₂ ∧ trace ++ suffix = trace₂) ∨
    (∃ suffix, Steps frame decoder policy ctx final₂ suffix final ∧ trace₂ ++ suffix = trace) ∨
      Trace.QueryDivergence trace trace₂

def EvalDialogue {frame : OperandFrame} (decoder : Decoder frame) (policy : MemoryPolicy)
    (ctx : CallContext) (function : FunctionId) (globals : Globals) (args : Array Word)
    (trace : Trace) (finalGlobals : Globals) (outcome : FunctionOutcome) : Prop :=
  ∀ trace₂ finalGlobals₂ outcome₂,
    FunctionEvaluation frame decoder policy ctx function globals args trace₂ finalGlobals₂ outcome₂ →
    (trace = trace₂ ∧ finalGlobals = finalGlobals₂ ∧ outcome = outcome₂) ∨
      Trace.QueryDivergence trace trace₂

end Sir.Machine
