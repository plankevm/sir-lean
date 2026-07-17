import Sir.IR.CFG
import Sir.Semantics.World
import Sir.Semantics.Memory

universe u v

instance {σ : Type u} {ε : Type v} : MonadLift (StateM σ) (StateT σ (Except ε)) where
  monadLift action state := .ok (action state)

namespace Sir

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

def transfer (outputs inputs : Array VarId) : StateT Locals (Except IRError) Unit := do
  if outputs.size != inputs.size then
    throw (.blockArityMismatch outputs.size inputs.size)
  let locals₀ ← StateT.get
  for (input, output) in inputs.zip outputs do
    let value ← locals₀.lookup output
    assignM input value

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
  block : BlockId
  position : BlockPosition
  deriving DecidableEq, Repr

inductive MachineControl where
  | running (cursor : ProgramCursor)
  | halted
  deriving DecidableEq, Repr

structure MachineState where
  world : World
  memory : MemoryState := .empty
  locals : Locals := .empty
  returnData : ByteArray := ByteArray.empty
  control : MachineControl

instance {m : Type → Type} [Monad m] :
    MonadLift (StateT Locals m) (StateT MachineState m) where
  monadLift action state := do
    let (result, locals') ← action.run state.locals
    return (result, { state with locals := locals' })

instance {m : Type → Type} [Monad m] :
    MonadLift (StateT World m) (StateT MachineState m) where
  monadLift action state := do
    let (result, world') ← action.run state.world
    return (result, { state with world := world' })

inductive Event where
  | gas (value : Word)
  | call (call : CallRecord)

abbrev Trace := List Event

def MachineState.localSet (var : VarId) (value : Word) : StateM MachineState Unit :=
  modify (fun s => { s with locals := s.locals.assign var value })

abbrev MachineStateM := StateT MachineState (Except IRError)

def Program.block? (program : Program) (bid : BlockId) : Option BasicBlock :=
  program.blocks[bid.id]?

def BasicBlock.absoluteToPosition (block : BasicBlock) (index : Nat) : BlockPosition :=
  if index < block.statements.size then .statement index else .terminator

def BasicBlock.startPosition (block : BasicBlock) : BlockPosition :=
  block.absoluteToPosition 0

def Program.startCursor? (program : Program) : Option ProgramCursor := do
  let block ← program.block? program.entry
  return { block := program.entry, position := block.startPosition }

def Program.decodeStmt (program : Program) (control : MachineControl) : Option (MachineControl × Stmt) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor.block
  let stmt ← block.statements[index]?
  some (.running { cursor with position := block.absoluteToPosition (index + 1) }, stmt)

def Program.terminatorAt (program : Program) (control : MachineControl) : Option Terminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor.block
  some block.terminator

end Sir
