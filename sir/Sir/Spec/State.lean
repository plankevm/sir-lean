import Sir.Spec.Memory
import Evm.Maps.AccountMap

universe u v

namespace Sir

instance {σ : Type u} {ε : Type v} : MonadLift (StateM σ) (StateT σ (Except ε)) where
  monadLift action state := .ok (action state)

abbrev World := Evm.AccountMap

namespace World

def loadStorage (world : World) (address : Address) (key : Word) : Word :=
  match world.find? address with
  | none => 0
  | some account => account.lookupStorage key

def storeStorage (world : World) (address : Address) (key value : Word) : World :=
  let account := (world.find? address).getD default
  world.insert address (account.updateStorage key value)

end World

inductive IRError where
  | undefinedVariable (var : VarId)
  | invalidBlock (block : BlockId)
  | invalidControl
  | invalidAlloc
  | blockArityMismatch (outputs inputs : Nat)
  deriving DecidableEq, Repr

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

def assignM (var : VarId) (value : Word) : StateM Locals Unit := modify (·.assign var value)

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

structure CallResult where
  world' : World
  success : Bool
  output : ByteArray

structure CallInput where
  target : Address
  gas : Word
  world : World

structure CallRecord where
  input : CallInput
  result : CallResult

structure CallContext where
  self : Address
  caller : Address
  value : Word
  calldata : ByteArray
  isStatic : Bool

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

/-- Separates a function's terminal result from the caller control state that consumes it. -/
inductive FunctionOutcome where
  | returned (rs : Array Word)
  | halted
  deriving DecidableEq, Repr

structure Globals where
  world : World
  memory : MemoryState := .empty
  returnData : ByteArray := ByteArray.empty

/-- No call stack: activation state lives in the derivation tree. -/
structure MachineState where
  globals : Globals
  locals : Locals := .empty
  control : MachineControl

instance {m : Type → Type} [Monad m] :
    MonadLift (StateT Locals m) (StateT MachineState m) where
  monadLift action state := do
    let (result, locals') ← action.run state.locals
    return (result, { state with locals := locals' })

inductive Event where
  | gas (value : Word)
  | call (call : CallRecord)

abbrev Trace := List Event

abbrev MachineStateM := StateT MachineState (Except IRError)

def Function.block? (fn : Function) (bid : BlockId) : Option BasicBlock :=
  fn.blocks[bid.id]?

/-- Names a block's terminator so CFG invariants can state edges without repeating block lookup. -/
def Function.terminatorOf (fn : Function) (block : BlockId) : Option Terminator :=
  (fn.block? block).map (·.terminator)

def Function.paramsOf (fn : Function) : Option (Array VarId) :=
  (fn.block? fn.entry).map (·.inputs)

/-- Records that a statement occurs in this function for function-scoped invariants. -/
def Function.HasStmt (fn : Function) (stmt : Stmt) : Prop :=
  ∃ block ∈ fn.blocks, stmt ∈ block.statements

def Program.function? (program : Program) (f : FunctionId) : Option Function :=
  program.functions[f.id]?

def Program.block? (program : Program) (cursor : ProgramCursor) : Option BasicBlock := do
  let fn ← program.function? cursor.fn
  fn.block? cursor.block

def Program.terminatorOf (program : Program) (cursor : ProgramCursor) : Option Terminator :=
  (program.block? cursor).map (·.terminator)

/-- Records that a statement occurs in the program, providing shared vocabulary for global statement invariants. -/
def Program.HasStmt (program : Program) (stmt : Stmt) : Prop :=
  ∃ fn ∈ program.functions, fn.HasStmt stmt

def Program.paramsOf (program : Program) (f : FunctionId) : Option (Array VarId) := do
  let fn ← program.function? f
  fn.paramsOf

/-- Shares the input count and declared return behavior used by call and entry invariants. -/
def Program.FunctionInputOutputArity (program : Program) (inputCount : Nat)
    (outputCount : Option Nat) (functionId : FunctionId) : Prop :=
  ∃ fn, program.function? functionId = some fn ∧
    fn.paramsOf.map (·.size) = some inputCount ∧ fn.outputs = outputCount

/-- Applies one entry-point condition to deployment and to main when main is declared. -/
def Program.AtEntries (program : Program) (condition : FunctionId → Prop) : Prop :=
  condition program.initEntry ∧
    ∀ entry, program.mainEntry = some entry → condition entry

def BasicBlock.absoluteToPosition (block : BasicBlock) (index : Nat) : BlockPosition :=
  if index < block.statements.size then .statement index else .terminator

def BasicBlock.startPosition (block : BasicBlock) : BlockPosition :=
  block.absoluteToPosition 0

/-- The machine state at `f`'s entry with `args` bound to its parameters. -/
def Program.callState? (p : Program) (f : FunctionId) (g : Globals)
    (args : Array Word) : Option MachineState := do
  let fn ← p.function? f
  let bb ← fn.block? fn.entry
  let .ok locals₀ := Locals.bindParams bb.inputs args | none
  let state : MachineState :=
    { globals := g, locals := locals₀,
      control := .running { fn := f, block := fn.entry, position := bb.startPosition } }
  some state

def Program.decodeStmt (program : Program) (control : MachineControl) : Option (MachineControl × Stmt) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor
  let stmt ← block.statements[index]?
  some (.running { cursor with position := block.absoluteToPosition (index + 1) }, stmt)

def Program.terminatorAt (program : Program) (control : MachineControl) : Option Terminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor
  some block.terminator

end Sir
