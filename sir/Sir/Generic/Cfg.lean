import Sir.Generic.Machine

namespace Sir.Generic

open Sir

structure StackDestination where
  consume : Nat
  produce : Nat
deriving DecidableEq, Repr

structure StackEnv where
  stack : List Word
  slots : Nat → Option Word

namespace StackEnv

def empty : StackEnv := ⟨[], fun _ => none⟩

def storeSlot (env : StackEnv) (slot : Nat) (value : Word) : StackEnv :=
  { env with slots := fun candidate => if candidate = slot then some value else env.slots candidate }

end StackEnv

def stackFetch (env : StackEnv) (count : Nat) : Except IRError (Array Word) :=
  if count ≤ env.stack.length then
    .ok (env.stack.take count).toArray
  else
    .error (.blockArityMismatch env.stack.length count)

def stackStore (env : StackEnv) (dst : StackDestination) (values : Array Word) :
    Except IRError StackEnv :=
  if dst.consume ≤ env.stack.length ∧ values.size = dst.produce then
    .ok { env with stack := values.toList ++ env.stack.drop dst.consume }
  else
    .error (.blockArityMismatch values.size dst.produce)

abbrev stackFrame : OpFrame where
  Env := StackEnv
  Src := Nat
  Dst := StackDestination
  fetch := stackFetch
  store := stackStore

inductive CfgInstr where
  | swap (depth : Nat)
  | dup (depth : Nat)
  | pop
  | op (operation : Operation)
  | icall (callee : FunctionId) (argumentCount resultCount : Nat)
  | store (slot : Nat)
  | load (slot : Nat)
deriving DecidableEq, Repr

inductive CfgTerminator where
  | halt
  | jump (target : BlockId)
  | branch (thenTarget elseTarget : BlockId)
  | iret
deriving DecidableEq, Repr

structure CfgBlock where
  inputCount : Nat
  instructions : Array CfgInstr
  terminator : CfgTerminator
  outputCount : Nat
deriving Repr

structure CfgFunction where
  blocks : Array CfgBlock
  entry : BlockId
deriving Repr

structure CfgProgram where
  functions : Array CfgFunction
  initEntry : FunctionId
deriving Repr

def CfgFunction.block? (function : CfgFunction) (block : BlockId) : Option CfgBlock :=
  function.blocks[block.id]?

def CfgProgram.function? (program : CfgProgram) (function : FunctionId) :
    Option CfgFunction :=
  program.functions[function.id]?

def CfgProgram.block? (program : CfgProgram) (cursor : ProgramCursor) : Option CfgBlock := do
  let function ← program.function? cursor.fn
  function.block? cursor.block

def CfgBlock.absoluteToPosition (block : CfgBlock) (index : Nat) : BlockPosition :=
  if index < block.instructions.size then .statement index else .terminator

def CfgBlock.startPosition (block : CfgBlock) : BlockPosition :=
  block.absoluteToPosition 0

def CfgProgram.decodeInstruction (program : CfgProgram) (control : MachineControl) :
    Option (MachineControl × CfgInstr) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor
  let instruction ← block.instructions[index]?
  let next := MachineControl.running
    { cursor with position := block.absoluteToPosition (index + 1) }
  some (next, instruction)

def CfgProgram.terminatorAt (program : CfgProgram) (control : MachineControl) :
    Option CfgTerminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor
  some block.terminator

def cfgDecode (program : CfgProgram) (control : MachineControl) :
    Option (Instr stackFrame × MachineControl) :=
  match program.decodeInstruction control with
  | some (next, .op operation) =>
      some (⟨Instr.Kind.primitive operation, operation.inputCount,
        ⟨operation.inputCount, operation.outputCount⟩⟩, next)
  | some (next, .icall callee argumentCount resultCount) =>
      some (⟨Instr.Kind.icall callee, argumentCount,
        ⟨argumentCount, resultCount⟩⟩, next)
  | _ => none

def swapStack (stack : List Word) (depth : Nat) : Option (List Word) := do
  let top ← stack[0]?
  let other ← stack[depth]?
  some ((stack.set 0 other).set depth top)

def cfgJump (program : CfgProgram) (env : StackEnv) (cursor : ProgramCursor)
    (target : BlockId) : Option (StackEnv × MachineControl) := do
  let source ← program.block? cursor
  let targetCursor := { cursor with block := target }
  let targetBlock ← program.block? targetCursor
  if env.stack.length ≠ source.outputCount ∨ source.outputCount ≠ targetBlock.inputCount then
    none
  let next := { targetCursor with position := targetBlock.startPosition }
  some (env, .running next)

def cfgControl (program : CfgProgram) (env : StackEnv) (globals : Globals)
    (control : MachineControl) :
    Option (Trace × StackEnv × Globals × MachineControl) :=
  match program.decodeInstruction control with
  | some (next, .swap depth) => do
      let stack ← swapStack env.stack depth
      some ([], { env with stack }, globals, next)
  | some (next, .dup depth) => do
      let value ← env.stack[depth]?
      some ([], { env with stack := value :: env.stack }, globals, next)
  | some (next, .pop) => do
      let _ :: stack := env.stack | none
      some ([], { env with stack }, globals, next)
  | some (next, .store slot) => do
      let value :: stack := env.stack | none
      let env' := (env.storeSlot slot value)
      some ([], { env' with stack }, globals, next)
  | some (next, .load slot) => do
      let value ← env.slots slot
      some ([], { env with stack := value :: env.stack }, globals, next)
  | some (_, .op _) | some (_, .icall _ _ _) => none
  | none => do
      let .running cursor := control | none
      let terminator ← program.terminatorAt control
      match terminator with
      | .halt => some ([], env, globals, .halted)
      | .jump target => do
          let (env', next) ← cfgJump program env cursor target
          some ([], env', globals, next)
      | .branch thenTarget elseTarget => do
          let condition :: stack := env.stack | none
          let target := if condition = 0 then elseTarget else thenTarget
          let (env', next) ← cfgJump program { env with stack } cursor target
          some ([], env', globals, next)
      | .iret => do
          let block ← program.block? cursor
          if env.stack.length ≠ block.outputCount then none
          some ([], env, globals, .returned env.stack.toArray)

def cfgResume (outcome : FunctionOutcome) (env : StackEnv)
    (dst : StackDestination) (next : MachineControl) :
    Option (StackEnv × MachineControl) :=
  match outcome with
  | .returned results =>
      match stackStore env dst results with
      | .ok env' => some (env', next)
      | .error _ => none
  | .halted => some (.empty, .halted)

def cfgEntry (program : CfgProgram) (functionId : FunctionId) (globals : Globals)
    (args : Array Word) : Option (GenState stackFrame) := do
  let function ← program.function? functionId
  let block ← function.block? function.entry
  if args.size ≠ block.inputCount then none
  some
    { globals
      env := { StackEnv.empty with stack := args.toList }
      control := .running
        { fn := functionId, block := function.entry, position := block.startPosition } }

def cfgDecoder (program : CfgProgram) : Decoder stackFrame where
  decode := cfgDecode program
  control := cfgControl program
  resume := cfgResume
  entry := cfgEntry program

end Sir.Generic
