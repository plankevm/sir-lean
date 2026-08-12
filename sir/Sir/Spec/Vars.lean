import Sir.Spec.Machine

namespace Sir

structure Locals where
  values : VarId → Option Word

namespace Locals

def empty : Locals := ⟨fun _ => none⟩

def lookup? (locals : Locals) (var : VarId) : Option Word :=
  locals.values var

def lookup (locals : Locals) (var : VarId) : Except IRError Word :=
  match locals.lookup? var with
  | none => .error (.undefinedVariable var)
  | some value => .ok value

def lookupM (var : VarId) : StateT Locals (Except IRError) Word := StateT.get >>= (·.lookup var)

def assign (locals : Locals) (var : VarId) (value : Word) : Locals :=
  ⟨fun candidate => if candidate = var then some value else locals.values candidate⟩

def bindValues (dst : Locals) (targetVars : Array VarId) (vs : Array Word) :
    Except IRError Locals := do
  if targetVars.size != vs.size then
    throw (.blockArityMismatch vs.size targetVars.size)
  let mut out := dst
  for (t, v) in targetVars.zip vs do
    out := out.assign t v
  return out

def bindParams (inputs : Array VarId) (vs : Array Word) : Except IRError Locals :=
  Locals.bindValues Locals.empty inputs vs

def bindReturns (callerLocals : Locals) (dests : Array VarId) (rs : Array Word) :
    Except IRError Locals :=
  Locals.bindValues callerLocals dests rs

def transfer (outputs inputs : Array VarId) : StateT Locals (Except IRError) Unit :=
  fun locals₀ => do
    let vs ← outputs.mapM locals₀.lookup
    let locals' ← Locals.bindValues locals₀ inputs vs
    return ((), locals')

end Locals

structure MachineState where
  globals : Globals
  locals : Locals := .empty
  control : Machine.MachineControl

instance {m : Type → Type} [Monad m] :
    MonadLift (StateT Locals m) (StateT MachineState m) where
  monadLift action state := do
    let (result, locals') ← action.run state.locals
    return (result, { state with locals := locals' })

abbrev MachineStateM := StateT MachineState (Except IRError)

namespace Vars

structure Call where
  callee : VarId
  gas : VarId
  result : VarId
deriving DecidableEq, Repr

inductive Expr where
  | constant (value : Word)
  | var (var : VarId)
  | add (lhs rhs : VarId)
  | lt (lhs rhs : VarId)
  | sload (key : VarId)
deriving DecidableEq, Repr

inductive Stmt where
  | assign (result : VarId) (value : Expr)
  | sstore (key value : VarId)
  | gas (result : VarId)
  | call (call : Call)
  | malloc (result size : VarId)
  | mallocUninit (result size : VarId)
  | mstore32 (offset value : VarId)
  | mload32 (result offset : VarId)
  | icall (callee : FunctionId) (args dests : Array VarId)
deriving DecidableEq, Repr

inductive Terminator where
  | halt
  | jump (target : BlockId)
  | branch (condition : VarId) (thenTarget elseTarget : BlockId)
  | iret
deriving DecidableEq, Repr

structure Block where
  inputs : Array VarId
  statements : Array Stmt
  terminator : Terminator
  outputs : Array VarId
deriving Repr

structure Function where
  blocks : Array Block
  entry : BlockId
deriving Repr

structure Program where
  functions : Array Function
  initEntry : FunctionId
  mainEntry : Option FunctionId
deriving Repr

end Vars

def Vars.Function.block? (fn : Vars.Function) (bid : BlockId) : Option Vars.Block :=
  fn.blocks[bid.id]?

def Vars.Function.paramsOf (fn : Vars.Function) : Option (Array VarId) :=
  (fn.block? fn.entry).map (·.inputs)

def Vars.Function.outputs? (fn : Vars.Function) : Option Nat :=
  (fn.blocks.find? (fun block => decide (block.terminator = .iret))).map (·.outputs.size)

def Vars.Function.HasStmt (fn : Vars.Function) (stmt : Vars.Stmt) : Prop :=
  ∃ block ∈ fn.blocks, stmt ∈ block.statements

def Vars.Program.function? (program : Vars.Program) (f : FunctionId) : Option Vars.Function :=
  program.functions[f.id]?

def Vars.Program.block? (program : Vars.Program) (cursor : Machine.ProgramCursor) : Option Vars.Block := do
  let fn ← program.function? cursor.fn
  fn.block? cursor.block

def Vars.Program.HasStmt (program : Vars.Program) (stmt : Vars.Stmt) : Prop :=
  ∃ fn ∈ program.functions, fn.HasStmt stmt

def Vars.Program.FunctionInputOutputArity (program : Vars.Program) (inputCount : Nat)
    (outputCount : Option Nat) (functionId : FunctionId) : Prop :=
  ∃ fn, program.function? functionId = some fn ∧
    fn.paramsOf.map (·.size) = some inputCount ∧ fn.outputs? = outputCount

def Vars.Program.AtEntries (program : Vars.Program) (condition : FunctionId → Prop) : Prop :=
  condition program.initEntry ∧
    ∀ entry, program.mainEntry = some entry → condition entry

def Vars.Block.absoluteToPosition (block : Vars.Block) (index : Nat) : Machine.BlockPosition :=
  if index < block.statements.size then .statement index else .terminator

def Vars.Block.startPosition (block : Vars.Block) : Machine.BlockPosition :=
  block.absoluteToPosition 0

def Vars.Program.callState? (p : Vars.Program) (f : FunctionId) (g : Globals)
    (args : Array Word) : Option MachineState := do
  let fn ← p.function? f
  let bb ← fn.block? fn.entry
  let .ok locals₀ := Locals.bindParams bb.inputs args | none
  let state : MachineState :=
    { globals := g, locals := locals₀,
      control := .running { fn := f, block := fn.entry, position := bb.startPosition } }
  some state

def Vars.Program.decodeStmt (program : Vars.Program) (control : Machine.MachineControl) :
    Option (Machine.MachineControl × Vars.Stmt) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor
  let stmt ← block.statements[index]?
  some (.running { cursor with position := block.absoluteToPosition (index + 1) }, stmt)

def Vars.Program.terminatorAt (program : Vars.Program) (control : Machine.MachineControl) :
    Option Vars.Terminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor
  some block.terminator

end Sir

namespace Sir.Vars

def jump (program : Program) (target : BlockId) : MachineStateM Unit := do
  let .running cursor := (← get).control | throw .invalidControl
  let source := cursor.block
  let some sourceBlock := program.block? cursor | throw (.invalidBlock source)
  let targetCursor := { cursor with block := target }
  let some targetBlock := program.block? targetCursor | throw (.invalidBlock target)
  Locals.transfer sourceBlock.outputs targetBlock.inputs
  let targetCursor := { targetCursor with position := targetBlock.startPosition }
  modify ({ · with control := .running targetCursor })

def evaluateTerminator (program : Program) : Terminator → MachineStateM Unit
  | .halt => modify (fun state => { state with control := .halted })
  | .jump target => jump program target
  | .branch condition thenTarget elseTarget => do
      let value ← Locals.lookupM condition
      jump program (if value = 0 then elseTarget else thenTarget)
  | .iret => do
      let .running cursor := (← get).control | throw .invalidControl
      let some block := program.block? cursor | throw (.invalidBlock cursor.block)
      let state ← get
      let rs ← liftM (block.outputs.mapM state.locals.lookup)
      modify ({ · with control := .returned rs })

open Machine

abbrev frame : OperandFrame where
  Environment := Locals
  Source := Array VarId
  Destination := Array VarId
  fetch env src := src.mapM env.lookup
  store env dst values := Locals.bindValues env dst values

def decodeExpression (result : VarId) : Expr → Instruction frame
  | .constant value => ⟨Instruction.Kind.primitive (.constant value), #[], #[result]⟩
  | .var var => ⟨Instruction.Kind.primitive .copy, #[var], #[result]⟩
  | .add lhs rhs => ⟨Instruction.Kind.primitive .add, #[lhs, rhs], #[result]⟩
  | .lt lhs rhs => ⟨Instruction.Kind.primitive .lt, #[lhs, rhs], #[result]⟩
  | .sload key => ⟨Instruction.Kind.primitive .sload, #[key], #[result]⟩

def decodeStatement : Stmt → Instruction frame
  | .assign result expr => decodeExpression result expr
  | .sstore key value => ⟨Instruction.Kind.primitive .sstore, #[key, value], #[]⟩
  | .gas result => ⟨Instruction.Kind.primitive .gas, #[], #[result]⟩
  | .call call => ⟨Instruction.Kind.primitive .call, #[call.callee, call.gas], #[call.result]⟩
  | .malloc result size =>
      ⟨Instruction.Kind.primitive .malloc, #[size], #[result]⟩
  | .mallocUninit result size =>
      ⟨Instruction.Kind.primitive .mallocUninit, #[size], #[result]⟩
  | .mstore32 offset value => ⟨Instruction.Kind.primitive .mstore32, #[offset, value], #[]⟩
  | .mload32 result offset => ⟨Instruction.Kind.primitive .mload32, #[offset], #[result]⟩
  | .icall callee args dests => ⟨Instruction.Kind.icall callee, args, dests⟩

def decode (program : Program) (control : Machine.MachineControl) :
    Option (Instruction frame × Machine.MachineControl) :=
  (program.decodeStmt control).map fun (next, stmt) => (decodeStatement stmt, next)

def control (program : Program) (env : Locals) (globals : Globals)
    (control : Machine.MachineControl) :
    Option (Trace × Locals × Globals × Machine.MachineControl) := do
  let terminator ← program.terminatorAt control
  let state : MachineState := { globals, locals := env, control }
  let .ok ((), state') := (evaluateTerminator program terminator).run state | none
  some ([], state'.locals, state'.globals, state'.control)

def resume (outcome : FunctionOutcome) (env : Locals) (dst : Array VarId)
    (next : Machine.MachineControl) : Option (Locals × Machine.MachineControl) :=
  match outcome with
  | .returned results =>
      match Locals.bindReturns env dst results with
      | .ok env' => some (env', next)
      | .error _ => none
  | .halted => some (.empty, .halted)

end Sir.Vars

namespace Sir

def MachineState.toState (state : MachineState) : Machine.State Vars.frame :=
  ⟨state.globals, state.locals, state.control⟩

end Sir

namespace Sir.Vars

open Machine

def entry (program : Program) (function : FunctionId) (globals : Globals)
    (args : Array Word) : Option (State frame) :=
  (program.callState? function globals args).map MachineState.toState

def decoder (program : Program) : Decoder frame where
  decode := decode program
  control := control program
  resume := resume
  entry := entry program

def SmallStep (program : Program) (ctx : CallContext)
    (state : MachineState) (trace : Trace) (final : MachineState) : Prop :=
  Machine.Step frame (decoder program) memoryPolicy ctx
    state.toState trace final.toState

def Steps (program : Program) (ctx : CallContext)
    (state : MachineState) (trace : Trace) (final : MachineState) : Prop :=
  Machine.Steps frame (decoder program) memoryPolicy ctx
    state.toState trace final.toState

def EvalFn (program : Program) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals → FunctionOutcome → Prop :=
  Machine.FunctionEvaluation frame (decoder program) memoryPolicy ctx

def Program.NonIcallControl (program : Program) (state : MachineState) : Prop :=
  (∃ nextControl statement,
      program.decodeStmt state.control = some (nextControl, statement) ∧
      ∀ callee callArgs destinations,
        statement ≠ .icall callee callArgs destinations) ∨
    ∃ terminator, program.terminatorAt state.control = some terminator

def Program.AllocationAvailable (program : Program) (state : MachineState) : Prop :=
  (∀ nextControl result size word,
      program.decodeStmt state.control = some (nextControl, .malloc result size) →
      state.locals.lookup size = .ok word →
      ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = word.toNat ∧
        allocation.bytes = ByteArray.mk (Array.replicate word.toNat 0)) ∧
    ∀ nextControl result size word,
      program.decodeStmt state.control = some (nextControl, .mallocUninit result size) →
      state.locals.lookup size = .ok word →
      ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = word.toNat

def Program.BumpFits (program : Program) (state : MachineState) : Prop :=
  (∀ nextControl result size word,
      program.decodeStmt state.control = some (nextControl, .malloc result size) →
      state.locals.lookup size = .ok word →
      state.globals.memory.watermark + word.toNat ≤ Evm.UInt256.size) ∧
    ∀ nextControl result size word,
      program.decodeStmt state.control = some (nextControl, .mallocUninit result size) →
      state.locals.lookup size = .ok word →
      state.globals.memory.watermark + word.toNat ≤ Evm.UInt256.size

def Program.StoreInBounds (program : Program) (state : MachineState) : Prop :=
  ∀ nextControl offset value word,
    program.decodeStmt state.control = some (nextControl, .mstore32 offset value) →
    state.locals.lookup offset = .ok word →
    state.globals.memory.InBounds word.toNat 32

end Sir.Vars

namespace Sir.Vars

def Program.RunsFunction (program : Program) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (state : MachineState) : Prop :=
  ∃ initial,
    program.callState? function globals args = some initial ∧
    Steps program ctx initial trace state

def Program.Runs (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (state : MachineState) : Prop :=
  program.RunsFunction ctx entry { world := world } #[] trace state

def Program.RunsTo (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (final : MachineState) : Prop :=
  program.Runs ctx entry world trace final ∧ final.control = .halted

def Program.ReadyState (program : Program) (ctx : CallContext) (state : MachineState) : Prop :=
  (∃ function globals args trace,
      program.RunsFunction ctx function globals args trace state) ∧
    program.NonIcallControl state ∧
    (program.AllocationAvailable state ∨ program.BumpFits state) ∧
    program.StoreInBounds state

end Sir.Vars

namespace Sir.Vars

def Program.callEdge (p : Program) (caller callee : FunctionId) : Prop :=
  ∃ args dests fn, p.function? caller = some fn ∧ fn.HasStmt (.icall callee args dests)

def Expr.variablesRead : Expr → List VarId
  | .constant _ => []
  | .var identifier => [identifier]
  | .add lhs rhs | .lt lhs rhs => [lhs, rhs]
  | .sload key => [key]

def Stmt.variablesRead : Stmt → List VarId
  | .assign _ value => value.variablesRead
  | .sstore key value => [key, value]
  | .gas _ => []
  | .call callData => [callData.callee, callData.gas]
  | .malloc _ size | .mallocUninit _ size => [size]
  | .mstore32 offset value => [offset, value]
  | .mload32 _ offset => [offset]
  | .icall _ args _ => args.toList

def Stmt.variablesDefined : Stmt → List VarId
  | .assign result _ | .gas result | .malloc result _ | .mallocUninit result _
  | .mload32 result _ => [result]
  | .call callData => [callData.result]
  | .icall _ _ dests => dests.toList
  | .sstore _ _ | .mstore32 _ _ => []

def Terminator.variablesRead : Terminator → List VarId
  | .branch condition _ _ => [condition]
  | .halt | .jump _ | .iret => []

def Terminator.jumpTargets : Terminator → List BlockId
  | .jump target => [target]
  | .branch _ thenTarget elseTarget => [thenTarget, elseTarget]
  | .halt | .iret => []

def Block.variablesDefinedBefore (block : Block) : Nat → List VarId
  | 0 => block.inputs.toList
  | index + 1 =>
      match block.statements[index]? with
      | some statement =>
          block.variablesDefinedBefore index ++ statement.variablesDefined
      | none => block.variablesDefinedBefore index

def Block.VariablesDefinedBeforeUse (block : Block) : Prop :=
  (∀ index statement, block.statements[index]? = some statement →
    ∀ identifier ∈ statement.variablesRead,
      identifier ∈ block.variablesDefinedBefore index) ∧
  ∀ identifier ∈ block.terminator.variablesRead ++ block.outputs.toList,
    identifier ∈ block.variablesDefinedBefore block.statements.size

structure Program.WellFormed (p : Program) : Prop where
  icallArity :
    ∀ callee args dests, p.HasStmt (.icall callee args dests) →
      ∃ outputs, p.FunctionInputOutputArity args.size outputs callee ∧
        outputs.getD 0 = dests.size
  iretArity :
    ∀ fn ∈ p.functions, ∀ block ∈ fn.blocks,
      block.terminator = .iret → some block.outputs.size = fn.outputs?
  acyclicCalls : ∀ f, ¬ Relation.TransGen p.callEdge f f
  entryArity : p.AtEntries (p.FunctionInputOutputArity 0 none)
  validJumpTargets :
    ∀ fn ∈ p.functions,
      ∀ block ∈ fn.blocks, ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, fn.block? target = some targetBlock ∧
          targetBlock.inputs.size = block.outputs.size
  variablesDefinedBeforeUse :
    ∀ fn ∈ p.functions,
      ∀ block ∈ fn.blocks, block.VariablesDefinedBeforeUse

end Sir.Vars

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

def Vars.Program.NextFunctionObservableEffect (program : Vars.Program) (ctx : CallContext)
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
        Vars.EvalFn program ctx function globals args history finalGlobals .halted ∧
        finalGlobals.world = world
  | .returned world values =>
      ∃ finalGlobals,
        Vars.EvalFn program ctx function globals args history finalGlobals (.returned values) ∧
        finalGlobals.world = world

def ObservableOutcome.functionOutcome : ObservableOutcome → FunctionObservableOutcome
  | .gas => .gas
  | .call input => .call input
  | .halt world => .halt world

def Vars.Program.NextObservableEffect (program : Vars.Program) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) (history : Trace) (outcome : ObservableOutcome) : Prop :=
  program.NextFunctionObservableEffect ctx entry { world := world₀ } #[] history
    outcome.functionOutcome

def Vars.Program.FunctionDeterministicFrom (program : Vars.Program) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) : Prop :=
  ∀ history outcome₁ outcome₂,
    program.NextFunctionObservableEffect ctx function globals args history outcome₁ →
    program.NextFunctionObservableEffect ctx function globals args history outcome₂ →
    outcome₁ = outcome₂

def Vars.Program.DeterministicFrom (program : Vars.Program) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) : Prop :=
  ∀ history outcome₁ outcome₂,
    program.NextObservableEffect ctx entry world₀ history outcome₁ →
    program.NextObservableEffect ctx entry world₀ history outcome₂ →
    outcome₁ = outcome₂

def Vars.Program.Deterministic (program : Vars.Program) : Prop :=
  ∀ ctx world₀,
    program.AtEntries (fun entry => program.DeterministicFrom ctx entry world₀)

def Vars.Stmt.isMemOracle : Vars.Stmt → Prop
  | .malloc _ _ | .mallocUninit _ _ | .mload32 _ _ => True
  | _ => False

def Vars.Program.MemOracleFree (p : Vars.Program) : Prop :=
  ∀ s, p.HasStmt s → ¬ s.isMemOracle

def Vars.Program.FunctionDeterministic (program : Vars.Program) (function : FunctionId) : Prop :=
  ∀ ctx globals args trace₁ trace₂ finalGlobals₁ finalGlobals₂ outcome₁ outcome₂,
    Vars.EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁ →
    Vars.EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂ →
    (trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂) ∨
      trace₁.QueryDivergence trace₂

end Sir
