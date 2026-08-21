import Sir.Core.Spec

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

namespace Vars

structure State where
  globals : Globals
  environment : Locals
  control : Control

abbrev EvalM := StateT State (Except IRError)

abbrev State.lookup (state : State) (var : VarId) : Except IRError Word :=
  state.environment.lookup var

end Vars

instance {m : Type → Type} [Monad m] :
    MonadLift (StateT Locals m) (StateT Vars.State m) where
  monadLift action state := do
    let (result, environment') ← action.run state.environment
    return (result, { state with environment := environment' })

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
  entry : Block
  rest : Array Block
deriving Repr

structure Program where
  init : Function
  main : Option Function
  rest : Array Function
deriving Repr

end Vars

def Vars.Function.blocks (fn : Vars.Function) : Array Vars.Block := #[fn.entry] ++ fn.rest

def Vars.Function.block? (fn : Vars.Function) (bid : BlockId) : Option Vars.Block :=
  fn.blocks[bid.id]?

def Vars.Function.paramsOf (fn : Vars.Function) : Array VarId := fn.entry.inputs

def Vars.Function.outputs? (fn : Vars.Function) : Option Nat :=
  (fn.blocks.find? (fun block => decide (block.terminator = .iret))).map (·.outputs.size)

def Vars.Function.HasStmt (fn : Vars.Function) (stmt : Vars.Stmt) : Prop :=
  ∃ block ∈ fn.blocks, stmt ∈ block.statements

def Vars.Program.functions (program : Vars.Program) : Array Vars.Function :=
  #[program.init] ++ program.main.toArray ++ program.rest

def Vars.Program.function? (program : Vars.Program) (f : FunctionId) : Option Vars.Function :=
  program.functions[f.id]?

def Vars.Program.initId (_ : Vars.Program) : FunctionId := ⟨0⟩

def Vars.Program.mainId? (program : Vars.Program) : Option FunctionId :=
  program.main.map fun _ => ⟨1⟩

def Vars.Program.block? (program : Vars.Program) (cursor : ProgramCursor) : Option Vars.Block := do
  let fn ← program.function? cursor.fn
  fn.block? cursor.block

def Vars.Program.HasStmt (program : Vars.Program) (stmt : Vars.Stmt) : Prop :=
  ∃ fn ∈ program.functions, fn.HasStmt stmt

def Vars.Program.FunctionInputOutputArity (program : Vars.Program) (inputCount : Nat)
    (outputCount : Option Nat) (functionId : FunctionId) : Prop :=
  ∃ fn, program.function? functionId = some fn ∧
    fn.paramsOf.size = inputCount ∧ fn.outputs? = outputCount

def Vars.Block.absoluteToPosition (block : Vars.Block) (index : Nat) : BlockPosition :=
  if index < block.statements.size then .statement index else .terminator

def Vars.Block.startPosition (block : Vars.Block) : BlockPosition :=
  block.absoluteToPosition 0

def Vars.Program.callState? (p : Vars.Program) (f : FunctionId) (g : Globals)
    (args : Array Word) : Option Vars.State := do
  let fn ← p.function? f
  let .ok locals₀ := Locals.bindParams fn.entry.inputs args | none
  let state : Vars.State :=
    { globals := g, environment := locals₀,
      control := .running { fn := f, block := ⟨0⟩, position := fn.entry.startPosition } }
  some state

def Vars.Program.statementAt (program : Vars.Program) (control : Control) :
    Option (Control × Vars.Stmt) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor
  let stmt ← block.statements[index]?
  some (.running { cursor with position := block.absoluteToPosition (index + 1) }, stmt)

def Vars.Program.terminatorAt (program : Vars.Program) (control : Control) :
    Option Vars.Terminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor
  some block.terminator

abbrev Vars.Program.atStmt (program : Vars.Program) (state : Vars.State) :
    Option (Control × Vars.Stmt) :=
  program.statementAt state.control

abbrev Vars.Program.atTerm (program : Vars.Program) (state : Vars.State) :
    Option Vars.Terminator :=
  program.terminatorAt state.control

def Vars.Program.At (program : Vars.Program) (state : Vars.State) (next : Control)
    (stmt : Vars.Stmt) (binds : List (VarId × Word)) : Prop :=
  program.atStmt state = some (next, stmt) ∧
    (binds.map (·.1)).mapM state.lookup = .ok (binds.map (·.2))

theorem Vars.Program.At.stmt {program : Vars.Program} {state : Vars.State}
    {next : Control} {stmt : Vars.Stmt} {binds : List (VarId × Word)}
    (h : program.At state next stmt binds) :
    program.atStmt state = some (next, stmt) :=
  h.1

end Sir

namespace Sir.Vars

def jump (program : Program) (target : BlockId) : Vars.EvalM Unit := do
  let .running cursor := (← get).control | throw .invalidControl
  let source := cursor.block
  let some sourceBlock := program.block? cursor | throw (.invalidBlock source)
  let targetCursor := { cursor with block := target }
  let some targetBlock := program.block? targetCursor | throw (.invalidBlock target)
  Locals.transfer sourceBlock.outputs targetBlock.inputs
  let targetCursor := { targetCursor with position := targetBlock.startPosition }
  modify ({ · with control := .running targetCursor })

def evaluateTerminator (program : Program) : Terminator → Vars.EvalM Unit
  | .halt => modify (fun state => { state with control := .halted })
  | .jump target => jump program target
  | .branch condition thenTarget elseTarget => do
      let value ← Locals.lookupM condition
      jump program (if value = 0 then elseTarget else thenTarget)
  | .iret => do
      let .running cursor := (← get).control | throw .invalidControl
      let some block := program.block? cursor | throw (.invalidBlock cursor.block)
      let state ← get
      let rs ← liftM (block.outputs.mapM state.environment.lookup)
      modify ({ · with control := .returned rs })

def evalExpr (context : CallContext) (environment : Locals) (globals : Globals) :
    Expr → Except IRError Word
  | .constant value => .ok value
  | .var identifier => environment.lookup identifier
  | .add left right => do return .add (← environment.lookup left) (← environment.lookup right)
  | .lt left right => do return .lt (← environment.lookup left) (← environment.lookup right)
  | .sload key => do return globals.world.loadStorage context.self (← environment.lookup key)

def resume (outcome : FunctionOutcome) (env : Locals) (dst : Array VarId)
    (next : Control) : Option (Locals × Control) :=
  match outcome with
  | .returned results =>
      match Locals.bindReturns env dst results with
      | .ok env' => some (env', next)
      | .error _ => none
  | .halted => some (.empty, .halted)

end Sir.Vars

namespace Sir.Vars

set_option autoImplicit true in
mutual

inductive SmallStep (program : Program) (context : CallContext) :
    State → Trace → State → Prop where
  | assign
      (hstmt : program.atStmt state = some (next, .assign result expression))
      (heval : evalExpr context state.environment state.globals expression = .ok value) :
      SmallStep program context state []
        { state with environment := state.environment.assign result value, control := next }
  | sstore
      (h : program.At state next (.sstore keyVar valueVar) [(keyVar, key), (valueVar, value)]) :
      SmallStep program context state []
        { state with globals := state.globals.storeStorage context key value, control := next }
  | gas
      (h : program.At state next (.gas result) []) :
      SmallStep program context state [.gas answer]
        { state with environment := state.environment.assign result answer, control := next }
  | call
      (h : program.At state next (.call call) [(call.callee, target), (call.gas, gasLimit)]) :
      SmallStep program context state
        [.call { input := state.globals.callInput target gasLimit, result := answer }]
        { globals := state.globals.applyCall answer
          environment := state.environment.assign call.result (.fromBool answer.success)
          control := next }
  | malloc
      (h : program.At state next (.malloc result sizeVar) [(sizeVar, size)])
      (hallow : memoryPolicy.Allows state.globals.memory size.toNat allocation)
      (hzero : allocation.bytes = ByteArray.mk (Array.replicate size.toNat 0)) :
      SmallStep program context state []
        { globals := state.globals.pushAlloc allocation
          environment := state.environment.assign result allocation.offset
          control := next }
  | mallocUninit
      (h : program.At state next (.mallocUninit result sizeVar) [(sizeVar, size)])
      (hallow : memoryPolicy.Allows state.globals.memory size.toNat allocation) :
      SmallStep program context state []
        { globals := state.globals.pushAlloc allocation
          environment := state.environment.assign result allocation.offset
          control := next }
  | mstore32
      (h : program.At state next (.mstore32 offsetVar valueVar) [(offsetVar, offset), (valueVar, value)])
      (hbound : state.globals.memory.InBounds offset.toNat 32) :
      SmallStep program context state []
        { state with globals := state.globals.writeWord32 offset value, control := next }
  | mload32
      (h : program.At state next (.mload32 result offsetVar) [(offsetVar, offset)]) :
      SmallStep program context state []
        { state with
          environment := state.environment.assign result
            (state.globals.readWord32 offset assumed)
          control := next }
  | icall
      (hstmt : program.atStmt state = some (next, .icall callee args dests))
      (hargs : args.mapM state.lookup = .ok values)
      (hcall : EvalFn program context callee state.globals values trace globals outcome)
      (hresume : resume outcome state.environment dests next =
        some (environment, resumed)) :
      SmallStep program context state trace
        { globals := globals, environment := environment, control := resumed }
  | control
      (hterm : program.atTerm state = some terminator)
      (heval : (evaluateTerminator program terminator).run state = .ok ((), final)) :
      SmallStep program context state [] final

inductive Steps (program : Program) (context : CallContext) :
    State → Trace → State → Prop where
  | refl : Steps program context state [] state
  | tail
      (start : Steps program context state first middle)
      (next : SmallStep program context middle second final) :
      Steps program context state (first ++ second) final

inductive EvalFn (program : Program) (context : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals → FunctionOutcome → Prop where
  | exit
      (hentry : program.callState? function globals args = some initial)
      (hrun : Steps program context initial trace final)
      (hexit : final.control = outcome.toControl) :
      EvalFn program context function globals args trace final.globals outcome

end

def Steps.Extends (program : Program) (context : CallContext) (state₁ : State)
    (trace₁ : Trace) (state₂ : State) (trace₂ : Trace) : Prop :=
  ∃ suffix, Steps program context state₁ suffix state₂ ∧ trace₁ ++ suffix = trace₂

def Program.NonIcallControl (program : Program) (state : Vars.State) : Prop :=
  (∃ nextControl statement,
      program.atStmt state = some (nextControl, statement) ∧
      ∀ callee callArgs destinations,
        statement ≠ .icall callee callArgs destinations) ∨
    ∃ terminator, program.atTerm state = some terminator

def Program.AllocationAvailable (program : Program) (state : Vars.State) : Prop :=
  (∀ nextControl result size word,
      program.atStmt state = some (nextControl, .malloc result size) →
      state.environment.lookup size = .ok word →
      ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = word.toNat ∧
        allocation.bytes = ByteArray.mk (Array.replicate word.toNat 0)) ∧
    ∀ nextControl result size word,
      program.atStmt state = some (nextControl, .mallocUninit result size) →
      state.environment.lookup size = .ok word →
      ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = word.toNat

def Program.BumpFits (program : Program) (state : Vars.State) : Prop :=
  (∀ nextControl result size word,
      program.atStmt state = some (nextControl, .malloc result size) →
      state.environment.lookup size = .ok word →
      state.globals.memory.watermark + word.toNat ≤ Evm.UInt256.size) ∧
    ∀ nextControl result size word,
      program.atStmt state = some (nextControl, .mallocUninit result size) →
      state.environment.lookup size = .ok word →
      state.globals.memory.watermark + word.toNat ≤ Evm.UInt256.size

def Program.StoreInBounds (program : Program) (state : Vars.State) : Prop :=
  ∀ nextControl offset value word,
    program.atStmt state = some (nextControl, .mstore32 offset value) →
    state.environment.lookup offset = .ok word →
    state.globals.memory.InBounds word.toNat 32

end Sir.Vars

namespace Sir.Vars

def Program.RunsFunction (program : Program) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (state : Vars.State) : Prop :=
  ∃ initial,
    program.callState? function globals args = some initial ∧
    Steps program ctx initial trace state

def Program.Runs (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (state : Vars.State) : Prop :=
  program.RunsFunction ctx entry { world := world } #[] trace state

def Program.RunsTo (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (final : Vars.State) : Prop :=
  program.Runs ctx entry world trace final ∧ final.control = .halted

def Program.ReadyState (program : Program) (ctx : CallContext) (state : Vars.State) : Prop :=
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
  entryArity :
    (p.init.paramsOf.size = 0 ∧ p.init.outputs? = none) ∧
      ∀ m, p.main = some m → m.paramsOf.size = 0 ∧ m.outputs? = none
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
    program.DeterministicFrom ctx program.initId world₀ ∧
      ∀ entry, program.mainId? = some entry →
        program.DeterministicFrom ctx entry world₀

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
