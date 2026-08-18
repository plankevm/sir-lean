import Sir.Machine.Spec

namespace Sir.Stack

open Sir Machine

structure Destination where
  consume : Nat
  produce : Nat
deriving DecidableEq, Repr

structure Environment where
  stack : List Word
  slots : Nat → Option Word

namespace Environment

def empty : Environment := ⟨[], fun _ => none⟩

def storeSlot (env : Environment) (slot : Nat) (value : Word) : Environment :=
  { env with slots := fun candidate => if candidate = slot then some value else env.slots candidate }

end Environment

def fetch (env : Environment) (count : Nat) : Except IRError (Array Word) :=
  if count ≤ env.stack.length then
    .ok (env.stack.take count).toArray
  else
    .error (.blockArityMismatch env.stack.length count)

def store (env : Environment) (dst : Destination) (values : Array Word) :
    Except IRError Environment :=
  if dst.consume ≤ env.stack.length ∧ values.size = dst.produce then
    .ok { env with stack := values.toList ++ env.stack.drop dst.consume }
  else
    .error (.blockArityMismatch values.size dst.produce)

inductive Source where
  | inOrder (count : Nat)
  | reversedPair
deriving DecidableEq, Repr

instance (count : Nat) : OfNat Source count where
  ofNat := .inOrder count

def sourceFetch (env : Environment) : Source → Except IRError (Array Word)
  | .inOrder count => fetch env count
  | .reversedPair =>
      match env.stack with
      | first :: second :: _ => .ok #[second, first]
      | stack => .error (.blockArityMismatch stack.length 2)

abbrev frame : OperandFrame where
  Environment := Environment
  Source := Source
  Destination := Destination
  fetch := sourceFetch
  store := store

inductive Instr where
  | swap (depth : Nat)
  | exchange (firstDepth secondDepth : Nat)
  | dup (depth : Nat)
  | pop
  | op (operation : Operation)
  | flippedOp (operation : Operation)
  | icall (callee : FunctionId) (argumentCount resultCount : Nat)
  | store (slot : Nat)
  | load (slot : Nat)
deriving DecidableEq, Repr

inductive Terminator where
  | halt
  | jump (target : BlockId)
  | branch (thenTarget elseTarget : BlockId)
  | iret
deriving DecidableEq, Repr

structure Block where
  inputCount : Nat
  instructions : Array Instr
  terminator : Terminator
  outputCount : Nat
deriving Repr

structure Function where
  entry : Block
  rest : Array Block
deriving Repr

structure Program where
  init : Function
  rest : Array Function
deriving Repr

def Function.blocks (function : Function) : Array Block := #[function.entry] ++ function.rest

def Program.functions (program : Program) : Array Function := #[program.init] ++ program.rest

def Function.HasInstr (function : Function) (instruction : Instr) : Prop :=
  ∃ block ∈ function.blocks, instruction ∈ block.instructions

def Program.HasInstr (program : Program) (instruction : Instr) : Prop :=
  ∃ function ∈ program.functions, function.HasInstr instruction

def Instr.isMemOracle : Instr → Prop
  | .op .mload32 | .op .malloc | .op .mallocUninit => True
  | .flippedOp .mload32 | .flippedOp .malloc | .flippedOp .mallocUninit => True
  | _ => False

def Program.MemOracleFree (program : Program) : Prop :=
  ∀ instruction, program.HasInstr instruction → ¬ instruction.isMemOracle

def Function.block? (function : Function) (block : BlockId) : Option Block :=
  function.blocks[block.id]?

def Program.function? (program : Program) (function : FunctionId) :
    Option Function :=
  program.functions[function.id]?

def Program.block? (program : Program) (cursor : Machine.ProgramCursor) : Option Block := do
  let function ← program.function? cursor.fn
  function.block? cursor.block

def Block.absoluteToPosition (block : Block) (index : Nat) : Machine.BlockPosition :=
  if index < block.instructions.size then .statement index else .terminator

def Block.startPosition (block : Block) : Machine.BlockPosition :=
  block.absoluteToPosition 0

def Program.decodeInstruction (program : Program) (control : Machine.MachineControl) :
    Option (Machine.MachineControl × Instr) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor
  let instruction ← block.instructions[index]?
  let next := Machine.MachineControl.running
    { cursor with position := block.absoluteToPosition (index + 1) }
  some (next, instruction)

def Program.terminatorAt (program : Program) (control : Machine.MachineControl) :
    Option Terminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor
  some block.terminator

def decode (program : Program) (control : Machine.MachineControl) :
    Option (Instruction frame × Machine.MachineControl) :=
  match program.decodeInstruction control with
  | some (next, .op operation) =>
      some (⟨Instruction.Kind.primitive operation, .inOrder operation.inputCount,
        ⟨operation.inputCount, operation.outputCount⟩⟩, next)
  | some (next, .flippedOp .add) =>
      some (⟨Instruction.Kind.primitive .add, .reversedPair, ⟨2, 1⟩⟩, next)
  | some (next, .flippedOp .lt) =>
      some (⟨Instruction.Kind.primitive .lt, .reversedPair, ⟨2, 1⟩⟩, next)
  | some (_, .flippedOp _) => none
  | some (next, .icall callee argumentCount resultCount) =>
      some (⟨Instruction.Kind.icall callee, .inOrder argumentCount,
        ⟨argumentCount, resultCount⟩⟩, next)
  | _ => none

def exchange (stack : List Word) (firstDepth secondDepth : Nat) : Option (List Word) := do
  let first ← stack[firstDepth]?
  let second ← stack[secondDepth]?
  some ((stack.set firstDepth second).set secondDepth first)

def jump (program : Program) (env : Environment) (cursor : Machine.ProgramCursor)
    (target : BlockId) : Option (Environment × Machine.MachineControl) := do
  let source ← program.block? cursor
  let targetCursor := { cursor with block := target }
  let targetBlock ← program.block? targetCursor
  if env.stack.length ≠ source.outputCount ∨ source.outputCount ≠ targetBlock.inputCount then
    none
  let next := { targetCursor with position := targetBlock.startPosition }
  some (env, .running next)

def control (program : Program) (env : Environment) (globals : Globals)
    (control : Machine.MachineControl) :
    Option (Trace × Environment × Globals × Machine.MachineControl) :=
  match program.decodeInstruction control with
  | some (next, .swap depth) => do
      let stack ← exchange env.stack 0 depth
      some ([], { env with stack }, globals, next)
  | some (next, .exchange firstDepth secondDepth) => do
      if firstDepth = secondDepth then none
      let stack ← exchange env.stack firstDepth secondDepth
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
  | some (_, .op _) | some (_, .flippedOp _) | some (_, .icall _ _ _) => none
  | none => do
      let .running cursor := control | none
      let terminator ← program.terminatorAt control
      match terminator with
      | .halt => some ([], env, globals, .halted)
      | .jump target => do
          let (env', next) ← jump program env cursor target
          some ([], env', globals, next)
      | .branch thenTarget elseTarget => do
          let condition :: stack := env.stack | none
          let target := if condition = 0 then elseTarget else thenTarget
          let (env', next) ← jump program { env with stack } cursor target
          some ([], env', globals, next)
      | .iret => do
          let block ← program.block? cursor
          if env.stack.length ≠ block.outputCount then none
          some ([], env, globals, .returned env.stack.toArray)

def resume (outcome : FunctionOutcome) (env : Environment)
    (dst : Destination) (next : Machine.MachineControl) :
    Option (Environment × Machine.MachineControl) :=
  match outcome with
  | .returned results =>
      match store env dst results with
      | .ok env' => some (env', next)
      | .error _ => none
  | .halted => some (.empty, .halted)

def entry (program : Program) (functionId : FunctionId) (globals : Globals)
    (args : Array Word) : Option (State frame) := do
  let function ← program.function? functionId
  if args.size ≠ function.entry.inputCount then none
  some
    { globals
      environment := { Environment.empty with stack := args.toList }
      control := .running
        { fn := functionId, block := ⟨0⟩, position := function.entry.startPosition } }

def decoder (program : Program) : Decoder frame where
  decode := decode program
  control := control program
  resume := resume
  entry := entry program
  exclusive := by
    intro env globals point instruction next hdecode
    cases hinstruction : program.decodeInstruction point with
    | none => simp [Stack.decode, hinstruction] at hdecode
    | some decoded =>
        rcases decoded with ⟨nextControl, instruction'⟩
        cases instruction' <;>
          simp [Stack.decode, Stack.control, hinstruction] at hdecode ⊢
  terminal := by
    refine ⟨fun env globals results => ?_, fun env globals => ?_⟩ <;>
      simp [Stack.decode, Stack.control, Program.decodeInstruction]

def Steps.Extends (program : Program) (policy : MemoryPolicy) (ctx : CallContext)
    (state₁ : State frame) (trace₁ : Trace) (state₂ : State frame) (trace₂ : Trace) : Prop :=
  Machine.Steps.Extends frame (decoder program) policy ctx state₁ trace₁ state₂ trace₂

def EvalFn (program : Program) (ctx : CallContext) :
    FunctionId → Globals → Array Word → Trace → Globals → FunctionOutcome → Prop :=
  Machine.FunctionEvaluation frame (decoder program) Machine.memoryPolicy ctx

end Sir.Stack
