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
def sirPolicy : Generic.MemoryPolicy where
  Allows memory size allocation :=
    memory.IsValidNewAlloc allocation ∧ allocation.size = size

open Generic

abbrev localsFrame : OpFrame where
  Env := Locals
  Src := Array VarId
  Dst := Array VarId
  fetch env src := src.mapM env.lookup
  store env dst values := Locals.bindValues env dst values

def decodeExpr (result : VarId) : Expr → Instr localsFrame
  | .constant value => ⟨Instr.Kind.primitive (.constant value), #[], #[result]⟩
  | .var var => ⟨Instr.Kind.primitive .copy, #[var], #[result]⟩
  | .add lhs rhs => ⟨Instr.Kind.primitive .add, #[lhs, rhs], #[result]⟩
  | .lt lhs rhs => ⟨Instr.Kind.primitive .lt, #[lhs, rhs], #[result]⟩
  | .sload key => ⟨Instr.Kind.primitive .sload, #[key], #[result]⟩

def decodeSirStmt : Stmt → Instr localsFrame
  | .assign result expr => decodeExpr result expr
  | .sstore key value => ⟨Instr.Kind.primitive .sstore, #[key, value], #[]⟩
  | .gas result => ⟨Instr.Kind.primitive .gas, #[], #[result]⟩
  | .call call => ⟨Instr.Kind.primitive .call, #[call.callee, call.gas], #[call.result]⟩
  | .mallocUninit result size =>
      ⟨Instr.Kind.primitive .mallocUninit, #[size], #[result]⟩
  | .mstore32 offset value => ⟨Instr.Kind.primitive .mstore32, #[offset, value], #[]⟩
  | .mload32 result offset => ⟨Instr.Kind.primitive .mload32, #[offset], #[result]⟩
  | .icall callee args dests => ⟨Instr.Kind.icall callee, args, dests⟩

def sirDecode (program : Program) (control : MachineControl) :
    Option (Instr localsFrame × MachineControl) :=
  (program.decodeStmt control).map fun (next, stmt) => (decodeSirStmt stmt, next)

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

def MachineState.gen (state : MachineState) : GenState localsFrame :=
  ⟨state.globals, state.locals, state.control⟩

def sirEntry (program : Program) (function : FunctionId) (globals : Globals)
    (args : Array Word) : Option (GenState localsFrame) :=
  (program.callState? function globals args).map MachineState.gen

def sirDecoder (program : Program) : Decoder localsFrame where
  decode := sirDecode program
  control := sirControl program
  resume := sirResume
  entry := sirEntry program

def SmallStep (program : Program) (ctx : CallContext)
    (state : MachineState) (trace : Trace) (final : MachineState) : Prop :=
  Generic.GenStep localsFrame (sirDecoder program) sirPolicy ctx
    state.gen trace final.gen

def Steps (program : Program) (ctx : CallContext)
    (state : MachineState) (trace : Trace) (final : MachineState) : Prop :=
  Generic.GenSteps localsFrame (sirDecoder program) sirPolicy ctx
    state.gen trace final.gen

def EvalFn (program : Program) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals → FunctionOutcome → Prop :=
  Generic.GenEvalFn localsFrame (sirDecoder program) sirPolicy ctx

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
