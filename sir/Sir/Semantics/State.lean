import Sir.IR.CFG
import Sir.Semantics.World

universe u v

instance {σ : Type u} {ε : Type v} : MonadLift (StateM σ) (StateT σ (Except ε)) where
  monadLift action state := .ok (action state)

namespace Sir

inductive IRError where
  | undefinedVariable (var : VarId)
  | invalidBlock (block : BlockId)
  | invalidControl
  | blockArityMismatch (outputs inputs : Nat)
  deriving DecidableEq, Repr

structure Locals where
  values : VarId → Option Word

namespace Locals

def empty : Locals := ⟨fun _ => none⟩

def get? (locals : Locals) (var : VarId) : Option Word :=
  locals.values var

def get (locals : Locals) (var : VarId) : Except IRError Word :=
  match locals.get? var with
  | none => .error (.undefinedVariable var)
  | some value => .ok value

def getM (var : VarId) : StateT Locals (Except IRError) Word := StateT.get >>= (·.get var)

def set (locals : Locals) (var : VarId) (value : Word) : Locals :=
  ⟨fun candidate => if candidate = var then some value else locals.values candidate⟩

def setM (var : VarId) (value : Word) : StateM Locals Unit := modify (·.set var value)

def transfer (outputs inputs : Array VarId) : StateT Locals (Except IRError) Unit := do
  if outputs.size != inputs.size then
    throw (.blockArityMismatch outputs.size inputs.size)
  let locals₀ ← StateT.get
  for (input, output) in inputs.zip outputs do
    let value ← locals₀.get output
    setM input value

end Locals

structure CallResult where
  world : World
  success : Bool
  output : ByteArray

structure CallRecord where
  target : Address
  gas : Word
  result : CallResult

structure CallContext where
  self : Address
  caller : Address
  value : Word
  calldata : ByteArray
  isStatic : Bool

structure StatementCursor where
  block : BlockId
  statement : Nat
  deriving DecidableEq, Repr

inductive MachineControl where
  | running (cursor : StatementCursor)
  | halted
  deriving DecidableEq, Repr

namespace MachineControl

def blockStart (bid : BlockId) : MachineControl := .running { block := bid, statement := 0 }

end MachineControl

structure MachineState where
  world : World
  locals : Locals := .empty
  returnData : ByteArray := ByteArray.empty
  control : MachineControl

instance {m : Type → Type} [Monad m] :
    MonadLift (StateT Locals m) (StateT MachineState m) where
  monadLift action state := do
    let (result, locals) ← action.run state.locals
    return (result, { state with locals := locals })

inductive Event where
  | gas (value : Word)
  | call (call : CallRecord)

abbrev Trace := List Event

def MachineState.localSet (var : VarId) (value : Word) : StateM MachineState Unit :=
  modify (fun s => { s with locals := s.locals.set var value })

def Program.block? (program : Program) (bid : BlockId) : Option BasicBlock :=
  program.blocks[bid.id]?

def Program.decodeStmt (program : Program) (control : MachineControl) : Option (MachineControl × Stmt) := do
  let .running cursor := control | none
  let block ← program.block? cursor.block
  let stmt ← block.statements[cursor.statement]?
  some (.running { cursor with statement := cursor.statement + 1 }, stmt)

def Program.terminatorAt (program : Program) (control : MachineControl) : Option Terminator := do
  let .running cursor := control | none
  let block ← program.block? cursor.block
  guard (cursor.statement = block.statements.size)
  some block.terminator

def Program.nextControl (program : Program) (control : MachineControl) : Option MachineControl := do
  let .running cursor := control | none
  let block ← program.block? cursor.block
  guard (block.statements[cursor.statement]?.isSome)
  some (.running { cursor with statement := cursor.statement + 1 })

end Sir
