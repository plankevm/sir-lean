import Sir.Spec.State

namespace Sir.Generic

open Sir

structure MemoryPolicy where
  Allows : MemoryState → Nat → Allocation → Prop

namespace MemoryPolicy

def Deterministic (policy : MemoryPolicy) : Prop :=
  ∀ memory size allocation₁ allocation₂,
    policy.Allows memory size allocation₁ →
    policy.Allows memory size allocation₂ →
    allocation₁ = allocation₂

end MemoryPolicy

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

structure OpFrame where
  Env : Type
  Src : Type
  Dst : Type
  fetch : Env → Src → Except IRError (Array Word)
  store : Env → Dst → Array Word → Except IRError Env

inductive Instr.Kind where
  | primitive (operation : Operation)
  | icall (callee : FunctionId)
deriving DecidableEq, Repr

structure Instr (frame : OpFrame) where
  kind : Instr.Kind
  src : frame.Src
  dst : frame.Dst

structure GenState (frame : OpFrame) where
  globals : Globals
  env : frame.Env
  control : MachineControl

structure Decoder (frame : OpFrame) where
  decode : MachineControl → Option (Instr frame × MachineControl)
  control : frame.Env → Globals → MachineControl →
    Option (Trace × frame.Env × Globals × MachineControl)
  resume : FunctionOutcome → frame.Env → frame.Dst → MachineControl →
    Option (frame.Env × MachineControl)
  entry : FunctionId → Globals → Array Word → Option (GenState frame)

inductive OpFrame.Fires (frame : OpFrame) (policy : MemoryPolicy) (ctx : CallContext)
    (operation : Operation) (src : frame.Src) (dst : frame.Dst) :
    frame.Env → Globals → Trace → frame.Env → Globals → Prop where
  | next
      {env env' : frame.Env} {globals globals' : Globals}
      {operands results : Array Word} {trace : Trace} {oracle : operation.Oracle}
      (hadmissible : operation.Admissible policy globals operands oracle)
      (hfetch : frame.fetch env src = .ok operands)
      (hexecute : operation.execute ctx oracle globals operands =
        .ok (.next results globals' trace))
      (hstore : frame.store env dst results = .ok env') :
      frame.Fires policy ctx operation src dst env globals trace env' globals'

inductive OpFrame.FiresHalt (frame : OpFrame) (policy : MemoryPolicy) (ctx : CallContext)
    (operation : Operation) (src : frame.Src) :
    frame.Env → Globals → Trace → Globals → Prop where
  | halted
      {env : frame.Env} {globals globals' : Globals}
      {operands : Array Word} {trace : Trace} {oracle : operation.Oracle}
      (hadmissible : operation.Admissible policy globals operands oracle)
      (hfetch : frame.fetch env src = .ok operands)
      (hexecute : operation.execute ctx oracle globals operands =
        .ok (.halted globals' trace)) :
      frame.FiresHalt policy ctx operation src env globals trace globals'

mutual

inductive GenStep (frame : OpFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    GenState frame → Trace → GenState frame → Prop where
  | op
      {state : GenState frame} {operation : Operation}
      {src : frame.Src} {dst : frame.Dst} {next : MachineControl}
      {trace : Trace} {env' : frame.Env} {globals' : Globals}
      (hdecode : decoder.decode state.control =
        some (⟨Instr.Kind.primitive operation, src, dst⟩, next))
      (hfires : frame.Fires policy ctx operation src dst state.env state.globals
        trace env' globals') :
      GenStep frame decoder policy ctx state trace
        { globals := globals', env := env', control := next }
  | opHalted
      {state : GenState frame} {operation : Operation}
      {src : frame.Src} {dst : frame.Dst} {next : MachineControl}
      {trace : Trace} {globals' : Globals}
      (hdecode : decoder.decode state.control =
        some (⟨Instr.Kind.primitive operation, src, dst⟩, next))
      (hfires : frame.FiresHalt policy ctx operation src state.env state.globals
        trace globals') :
      GenStep frame decoder policy ctx state trace
        { globals := globals', env := state.env, control := .halted }
  | icall
      {state : GenState frame} {callee : FunctionId}
      {src : frame.Src} {dst : frame.Dst} {next : MachineControl}
      {values : Array Word} {trace : Trace} {globals' : Globals}
      {outcome : FunctionOutcome} {env' : frame.Env} {control' : MachineControl}
      (hdecode : decoder.decode state.control =
        some (⟨Instr.Kind.icall callee, src, dst⟩, next))
      (hfetch : frame.fetch state.env src = .ok values)
      (hcallee : GenEvalFn frame decoder policy ctx callee state.globals values
        trace globals' outcome)
      (hresume : decoder.resume outcome state.env dst next = some (env', control')) :
      GenStep frame decoder policy ctx state trace
        { globals := globals', env := env', control := control' }
  | control
      {state : GenState frame} {trace : Trace} {env' : frame.Env}
      {globals' : Globals} {control' : MachineControl}
      (hcontrol : decoder.control state.env state.globals state.control =
        some (trace, env', globals', control')) :
      GenStep frame decoder policy ctx state trace
        { globals := globals', env := env', control := control' }

inductive GenSteps (frame : OpFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    GenState frame → Trace → GenState frame → Prop where
  | refl {state : GenState frame} :
      GenSteps frame decoder policy ctx state [] state
  | tail
      {state middle final : GenState frame} {trace₁ trace₂ : Trace}
      (start : GenSteps frame decoder policy ctx state trace₁ middle)
      (next : GenStep frame decoder policy ctx middle trace₂ final) :
      GenSteps frame decoder policy ctx state (trace₁ ++ trace₂) final

inductive GenEvalFn (frame : OpFrame) (decoder : Decoder frame)
    (policy : MemoryPolicy) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals →
      FunctionOutcome → Prop where
  | returned
      {function : FunctionId} {globals : Globals} {args results : Array Word}
      {trace : Trace} {initial exit : GenState frame}
      (hentry : decoder.entry function globals args = some initial)
      (hrun : GenSteps frame decoder policy ctx initial trace exit)
      (hreturn : exit.control = .returned results) :
      GenEvalFn frame decoder policy ctx function globals args trace exit.globals
        (.returned results)
  | halted
      {function : FunctionId} {globals : Globals} {args : Array Word}
      {trace : Trace} {initial exit : GenState frame}
      (hentry : decoder.entry function globals args = some initial)
      (hrun : GenSteps frame decoder policy ctx initial trace exit)
      (hhalt : exit.control = .halted) :
      GenEvalFn frame decoder policy ctx function globals args trace exit.globals .halted

end

end Sir.Generic
