import Sir.IR.CFG
import Sir.Semantics.World

namespace Sir

inductive BlockPosition where
  | statement (index : Nat)
  | terminator
deriving DecidableEq, Repr

structure ProgramCounter where
  block : BlockId
  position : BlockPosition
deriving DecidableEq, Repr

inductive IRError where
  | outOfFuel
  | unknownBlock (block : BlockId)
  | invalidProgramCounter (pc : ProgramCounter)
  | undefinedVariable (var : VarId)
deriving DecidableEq, Repr

abbrev IRResult := Except IRError

structure Locals where
  values : VarId → Option Word

namespace Locals

def empty : Locals := ⟨fun _ => none⟩

def get? (locals : Locals) (var : VarId) : IRResult Word :=
  match locals.values var with
  | none => .error (.undefinedVariable var)
  | some x => .ok x

def set (l₀ : Locals) (var : VarId) (value : Word) : Locals :=
  ⟨fun v => if v = var then some value else l₀.values v⟩

def stateSet (var : VarId) (value : Word) : StateM Locals Unit := modify (Locals.set · var value)

end Locals

structure LocalState where
  gas : UInt64
  locals : Locals := .empty

structure CallContext where
  self : Address
  caller : Address
  value : Word
  calldata : ByteArray
  isStatic : Bool

inductive Halt where
  | stopped
  | returned (value : Word)
deriving DecidableEq, Repr

private def BlockPosition.nextPosition (block : BasicBlock) : BlockPosition → Option BlockPosition
  | .terminator => none
  | .statement index =>
    let next := index + 1
    some $ if next < block.statements.size
      then .statement next
      else .terminator

private def BasicBlock.entryPosition (block : BasicBlock) : BlockPosition :=
  if block.statements.isEmpty then .terminator else .statement 0

def Program.block? (program : Program) (id : BlockId) : Except IRError BasicBlock :=
  match program.blocks[id.id]? with
  | none => .error (.unknownBlock id)
  | some block => .ok block

def Program.blockEntryPC (program : Program) (bid : BlockId) : Except IRError ProgramCounter := do
  let block ← program.block? bid
  return { block := bid, position := block.entryPosition }

def Program.entryPC (program : Program) : Except IRError ProgramCounter :=
  program.blockEntryPC program.entry

def Program.nextPC (program : Program) (pc : ProgramCounter) : Except IRError ProgramCounter := do
  let block ← program.block? pc.block
  match pc.position.nextPosition block with
  | none => .error (.invalidProgramCounter pc)
  | some pos' => .ok { pc with position := pos' }

end Sir
