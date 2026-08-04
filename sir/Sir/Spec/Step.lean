import Sir.Spec.State
import Sir.Spec.Machine

namespace Sir

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

open Generic in
/-- The SIR memory policy preserves allocation as an explicit semantic choice while requiring the
chosen allocation to be valid and of the requested size. -/
def sirMemoryPolicy : Generic.MemoryPolicy where
  Allows memory size allocation :=
    memory.IsValidNewAlloc allocation ∧ allocation.size = size

open Generic

abbrev localOperandFrame : OperandFrame where
  Environment := Locals
  Source := Array VarId
  Destination := Array VarId
  fetch env src := src.mapM env.lookup
  store env dst values := Locals.bindValues env dst values

/-- SIR expression and statement decoding expose ordinary syntax as generic instructions while
retaining SIR control positions. -/
def decodeExpression (result : VarId) : Expr → Instruction localOperandFrame
  | .constant value => ⟨Instruction.Kind.primitive (.constant value), #[], #[result]⟩
  | .var var => ⟨Instruction.Kind.primitive .copy, #[var], #[result]⟩
  | .add lhs rhs => ⟨Instruction.Kind.primitive .add, #[lhs, rhs], #[result]⟩
  | .lt lhs rhs => ⟨Instruction.Kind.primitive .lt, #[lhs, rhs], #[result]⟩
  | .sload key => ⟨Instruction.Kind.primitive .sload, #[key], #[result]⟩

def decodeSirStatement : Stmt → Instruction localOperandFrame
  | .assign result expr => decodeExpression result expr
  | .sstore key value => ⟨Instruction.Kind.primitive .sstore, #[key, value], #[]⟩
  | .gas result => ⟨Instruction.Kind.primitive .gas, #[], #[result]⟩
  | .call call => ⟨Instruction.Kind.primitive .call, #[call.callee, call.gas], #[call.result]⟩
  | .mallocUninit result size =>
      ⟨Instruction.Kind.primitive .mallocUninit, #[size], #[result]⟩
  | .mstore32 offset value => ⟨Instruction.Kind.primitive .mstore32, #[offset, value], #[]⟩
  | .mload32 result offset => ⟨Instruction.Kind.primitive .mload32, #[offset], #[result]⟩
  | .icall callee args dests => ⟨Instruction.Kind.icall callee, args, dests⟩

def sirDecode (program : Program) (control : MachineControl) :
    Option (Instruction localOperandFrame × MachineControl) :=
  (program.decodeStmt control).map fun (next, stmt) => (decodeSirStatement stmt, next)

def sirControl (program : Program) (env : Locals) (globals : Globals)
    (control : MachineControl) :
    Option (Trace × Locals × Globals × MachineControl) := do
  let terminator ← program.terminatorAt control
  let state : MachineState := { globals, locals := env, control }
  let .ok ((), state') := (eval_terminator program terminator).run state | none
  some ([], state'.locals, state'.globals, state'.control)

def sirResume (outcome : FunctionOutcome) (env : Locals) (dst : Array VarId)
    (next : MachineControl) : Option (Locals × MachineControl) :=
  match outcome with
  | .returned results =>
      match Locals.bindReturns env dst results with
      | .ok env' => some (env', next)
      | .error _ => none
  | .halted => some (.empty, .halted)

/-- This embedding exposes SIR machine states to the generic semantics without changing the public
SIR state type. -/
def MachineState.toGenericState (state : MachineState) : GenericState localOperandFrame :=
  ⟨state.globals, state.locals, state.control⟩

def sirEntry (program : Program) (function : FunctionId) (globals : Globals)
    (args : Array Word) : Option (GenericState localOperandFrame) :=
  (program.callState? function globals args).map MachineState.toGenericState

/-- The SIR decoder assembles statement, terminator, resumption, and entry behavior so the generic
machine retains SIR control and call semantics. -/
def sirDecoder (program : Program) : Decoder localOperandFrame where
  decode := sirDecode program
  control := sirControl program
  resume := sirResume
  entry := sirEntry program

/-- The public SIR one-step relation uses the shared machine while preserving its established name
for exported statements. -/
def SmallStep (program : Program) (ctx : CallContext)
    (state : MachineState) (trace : Trace) (final : MachineState) : Prop :=
  Generic.GenericStep localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
    state.toGenericState trace final.toGenericState

/-- The public SIR finite-run relation preserves accumulated traces across the shared machine. -/
def Steps (program : Program) (ctx : CallContext)
    (state : MachineState) (trace : Trace) (final : MachineState) : Prop :=
  Generic.GenericSteps localOperandFrame (sirDecoder program) sirMemoryPolicy ctx
    state.toGenericState trace final.toGenericState

/-- The public SIR function-evaluation relation retains the call boundary used by observations and
exported results. -/
def EvalFn (program : Program) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals → FunctionOutcome → Prop :=
  Generic.GenericFunctionEvaluation localOperandFrame (sirDecoder program) sirMemoryPolicy ctx

def Program.NonIcallControl (program : Program) (state : MachineState) : Prop :=
  (∃ nextControl statement,
      program.decodeStmt state.control = some (nextControl, statement) ∧
      ∀ callee callArgs destinations,
        statement ≠ .icall callee callArgs destinations) ∨
    ∃ terminator, program.terminatorAt state.control = some terminator

def Program.AllocationAvailable (program : Program) (state : MachineState) : Prop :=
  ∀ nextControl result size word,
    program.decodeStmt state.control = some (nextControl, .mallocUninit result size) →
    state.locals.lookup size = .ok word →
    ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
      allocation.size = word.toNat

def Program.BumpFits (program : Program) (state : MachineState) : Prop :=
  ∀ nextControl result size word,
    program.decodeStmt state.control = some (nextControl, .mallocUninit result size) →
    state.locals.lookup size = .ok word →
    state.globals.memory.watermark + word.toNat ≤ Evm.UInt256.size

end Sir
