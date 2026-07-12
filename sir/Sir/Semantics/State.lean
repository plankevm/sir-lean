import Sir.IR.CFG
import Sir.Semantics.Gas
import Sir.Semantics.World

namespace Sir

inductive IRError where
  | undefinedVariable (var : VarId)
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

def set (locals : Locals) (var : VarId) (value : Word) : Locals :=
  ⟨fun candidate => if candidate = var then some value else locals.values candidate⟩

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

/-- A statement cursor. The terminator is at `statement = block.statements.size`. -/
structure ProgramCounter where
  block : BlockId
  statement : Nat
  deriving DecidableEq, Repr

inductive MachineControl where
  | running (pc : ProgramCounter)
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

inductive Event where
  | gas (value : Word)
  | call (call : CallRecord)

abbrev Trace := List Event

def MachineState.localSet (var : VarId) (value : Word) : StateM MachineState Unit :=
  modify (fun s => { s with locals := s.locals.set var value })

private def Program.block? (program : Program) (bid : BlockId) : Option BasicBlock :=
  program.blocks[bid.id]?

def Program.decodeStmt (program : Program) (control : MachineControl) : Option (MachineControl × Stmt) := do
  let .running pc := control | none
  let block ← program.block? pc.block
  let stmt ← block.statements[pc.statement]?
  some (.running { pc with statement := pc.statement + 1 }, stmt)

def Program.terminatorAt (program : Program) (control : MachineControl) : Option Terminator := do
  let .running pc := control | none
  let block ← program.block? pc.block
  guard (pc.statement = block.statements.size)
  some block.terminator

def Program.nextControl (program : Program) (control : MachineControl) : Option MachineControl := do
  let .running pc := control | none
  let block ← program.block? pc.block
  guard (block.statements[pc.statement]?.isSome)
  some (.running { pc with statement := pc.statement + 1 })

end Sir
