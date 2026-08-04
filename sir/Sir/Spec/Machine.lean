import Sir.Spec.State

namespace Sir.Generic

open Sir

/-- Allocation remains a machine parameter so semantics can expose valid choices without fixing
an allocator strategy. -/
structure MemoryPolicy where
  Allows : MemoryState → Nat → Allocation → Prop

namespace MemoryPolicy

def Deterministic (policy : MemoryPolicy) : Prop :=
  ∀ memory size allocation₁ allocation₂,
    policy.Allows memory size allocation₁ →
    policy.Allows memory size allocation₂ →
    allocation₁ = allocation₂

end MemoryPolicy

/-- Operations isolate data and world effects from control flow so different instruction
representations can share one execution model. -/
inductive Operation where
  | constant (value : Word)
  | copy
  | add
  | lt
  | sload
  | sstore
  | gas
  | call
  | mallocUninit
  | mstore32
  | mload32
deriving DecidableEq, Repr

namespace Operation

def Oracle : Operation → Type
  | .gas => Word
  | .call => CallResult
  | .mallocUninit => Allocation
  | .mload32 => Vector UInt8 32
  | _ => Unit

def Admissible (policy : MemoryPolicy) :
    (operation : Operation) → Globals → Array Word → operation.Oracle → Prop
  | .mallocUninit, globals, operands, allocation =>
      ∃ size, operands[0]? = some size ∧
        policy.Allows globals.memory size.toNat allocation ∧
        globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = size.toNat
  | _, _, _, _ => True

inductive Outcome where
  | next (results : Array Word) (globals : Globals) (trace : Trace)
  | halted (globals : Globals) (trace : Trace)

def execute (ctx : CallContext) :
    (operation : Operation) → operation.Oracle → Globals → Array Word →
      Except IRError Outcome
  | .constant value, _, globals, _ => .ok (.next #[value] globals [])
  | .copy, _, globals, operands => do
      let some value := operands[0]? | throw (.blockArityMismatch operands.size 1)
      return .next #[value] globals []
  | .add, _, globals, operands => do
      let some lhs := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some rhs := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[Evm.UInt256.add lhs rhs] globals []
  | .lt, _, globals, operands => do
      let some lhs := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some rhs := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[Evm.UInt256.lt lhs rhs] globals []
  | .sload, _, globals, operands => do
      let some key := operands[0]? | throw (.blockArityMismatch operands.size 1)
      return .next #[globals.world.loadStorage ctx.self key] globals []
  | .sstore, _, globals, operands => do
      let some key := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some value := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[]
        { globals with world := globals.world.storeStorage ctx.self key value } []
  | .gas, answer, globals, _ =>
      .ok (.next #[answer] globals [Sir.Event.gas answer])
  | .call, result, globals, operands => do
      let some callee := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some gasValue := operands[1]? | throw (.blockArityMismatch operands.size 2)
      let input : CallInput :=
        { target := .ofUInt256 callee, gas := gasValue, world := globals.world }
      let record : CallRecord := { input, result }
      return .next #[Evm.UInt256.fromBool result.success]
        { globals with returnData := result.output, world := result.world' }
          [Sir.Event.call record]
  | .mallocUninit, allocation, globals, operands => do
      let some size := operands[0]? | throw (.blockArityMismatch operands.size 1)
      if allocation.size ≠ size.toNat then
        throw .invalidAlloc
      return .next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } []
  | .mstore32, _, globals, operands => do
      let some offset := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some value := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[]
        { globals with memory := globals.memory.writeBytes offset value.toByteArray } []
  | .mload32, assumed, globals, operands => do
      let some offset := operands[0]? | throw (.blockArityMismatch operands.size 1)
      let bytes := globals.memory.readBytes offset ⟨assumed.toArray⟩
      return .next #[.ofNat (Evm.fromByteArrayBigEndian bytes)] globals []

end Operation

/-- An operand frame abstracts operand access so the transition system can serve machines with
different environment, source, and destination representations. -/
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

/-- A decoded instruction packages ordinary operations or nested calls with operand locations,
keeping stepping independent of the concrete environment representation. -/
structure Instruction (frame : OperandFrame) where
  kind : Instruction.Kind
  source : frame.Source
  destination : frame.Destination

/-- Generic state keeps global effects, instance-specific operands, and control together so one
transition system can support multiple instruction representations. -/
structure GenericState (frame : OperandFrame) where
  globals : Globals
  environment : frame.Environment
  control : MachineControl

/-- A decoder supplies the representation-specific control and call hooks needed to instantiate
the generic transition system. -/
structure Decoder (frame : OperandFrame) where
  decode : MachineControl → Option (Instruction frame × MachineControl)
  control : frame.Environment → Globals → MachineControl →
    Option (Trace × frame.Environment × Globals × MachineControl)
  resume : FunctionOutcome → frame.Environment → frame.Destination → MachineControl →
    Option (frame.Environment × MachineControl)
  entry : FunctionId → Globals → Array Word → Option (GenericState frame)

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

/-- A generic step defines one observable transition while delegating operand access and control
interpretation to the machine instance. -/
inductive GenericStep (frame : OperandFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    GenericState frame → Trace → GenericState frame → Prop where
  | operation
      {state : GenericState frame} {operation : Operation}
      {src : frame.Source} {dst : frame.Destination} {next : MachineControl}
      {trace : Trace} {env' : frame.Environment} {globals' : Globals}
      (hdecode : decoder.decode state.control =
        some (⟨Instruction.Kind.primitive operation, src, dst⟩, next))
      (hfires : frame.Fires policy ctx operation src dst state.environment state.globals
        trace env' globals') :
      GenericStep frame decoder policy ctx state trace
        { globals := globals', environment := env', control := next }
  | operationHalted
      {state : GenericState frame} {operation : Operation}
      {src : frame.Source} {dst : frame.Destination} {next : MachineControl}
      {trace : Trace} {globals' : Globals}
      (hdecode : decoder.decode state.control =
        some (⟨Instruction.Kind.primitive operation, src, dst⟩, next))
      (hfires : frame.FiresHalt policy ctx operation src state.environment state.globals
        trace globals') :
      GenericStep frame decoder policy ctx state trace
        { globals := globals', environment := state.environment, control := .halted }
  | internalCall
      {state : GenericState frame} {callee : FunctionId}
      {src : frame.Source} {dst : frame.Destination} {next : MachineControl}
      {values : Array Word} {trace : Trace} {globals' : Globals}
      {outcome : FunctionOutcome} {env' : frame.Environment} {control' : MachineControl}
      (hdecode : decoder.decode state.control =
        some (⟨Instruction.Kind.icall callee, src, dst⟩, next))
      (hfetch : frame.fetch state.environment src = .ok values)
      (hcallee : GenericFunctionEvaluation frame decoder policy ctx callee state.globals values
        trace globals' outcome)
      (hresume : decoder.resume outcome state.environment dst next = some (env', control')) :
      GenericStep frame decoder policy ctx state trace
        { globals := globals', environment := env', control := control' }
  | control
      {state : GenericState frame} {trace : Trace} {env' : frame.Environment}
      {globals' : Globals} {control' : MachineControl}
      (hcontrol : decoder.control state.environment state.globals state.control =
        some (trace, env', globals', control')) :
      GenericStep frame decoder policy ctx state trace
        { globals := globals', environment := env', control := control' }

/-- Reflexive-transitive execution records finite runs while preserving their accumulated
observable traces. -/
inductive GenericSteps (frame : OperandFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    GenericState frame → Trace → GenericState frame → Prop where
  | refl {state : GenericState frame} :
      GenericSteps frame decoder policy ctx state [] state
  | tail
      {state middle final : GenericState frame} {trace₁ trace₂ : Trace}
      (start : GenericSteps frame decoder policy ctx state trace₁ middle)
      (next : GenericStep frame decoder policy ctx middle trace₂ final) :
      GenericSteps frame decoder policy ctx state (trace₁ ++ trace₂) final

/-- Generic function evaluation closes a finite run at return or halt, providing the call boundary
used by nested evaluations. -/
inductive GenericFunctionEvaluation (frame : OperandFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals →
      FunctionOutcome → Prop where
  | returned
      {function : FunctionId} {globals : Globals} {args results : Array Word}
      {trace : Trace} {initial exit : GenericState frame}
      (hentry : decoder.entry function globals args = some initial)
      (hrun : GenericSteps frame decoder policy ctx initial trace exit)
      (hreturn : exit.control = .returned results) :
      GenericFunctionEvaluation frame decoder policy ctx function globals args trace exit.globals
        (.returned results)
  | halted
      {function : FunctionId} {globals : Globals} {args : Array Word}
      {trace : Trace} {initial exit : GenericState frame}
      (hentry : decoder.entry function globals args = some initial)
      (hrun : GenericSteps frame decoder policy ctx initial trace exit)
      (hhalt : exit.control = .halted) :
      GenericFunctionEvaluation frame decoder policy ctx function globals args trace exit.globals .halted

end

end Sir.Generic
