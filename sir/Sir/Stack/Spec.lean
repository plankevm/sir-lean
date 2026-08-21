import Sir.Core.Spec

namespace Sir.Stack

open Sir

structure Destination where
  consume : Nat
  produce : Nat
deriving DecidableEq, Repr

structure Environment where
  stack : List Word
  slots : Nat → Option Word

namespace Environment

def empty : Environment := ⟨[], fun _ => none⟩

def storeSlot (environment : Environment) (slot : Nat) (value : Word) : Environment :=
  { environment with
    slots := fun candidate => if candidate = slot then some value else environment.slots candidate }

end Environment

def sourceFetch (environment : Environment) (count : Nat) : Except IRError (Array Word) :=
  if count ≤ environment.stack.length then
    .ok (environment.stack.take count).toArray
  else
    .error (.blockArityMismatch environment.stack.length count)

def sourceFetchFlipped (environment : Environment) : Except IRError (Array Word) :=
  match environment.stack with
  | first :: second :: _ => .ok #[second, first]
  | stack => .error (.blockArityMismatch stack.length 2)

def push (environment : Environment) (destination : Destination) (values : Array Word) :
    Except IRError Environment :=
  if destination.consume ≤ environment.stack.length ∧ values.size = destination.produce then
    .ok { environment with
      stack := values.toList ++ environment.stack.drop destination.consume }
  else
    .error (.blockArityMismatch values.size destination.produce)

structure State where
  globals : Globals
  environment : Environment
  control : Control

abbrev State.fetch (state : State) (count : Nat) : Except IRError (Array Word) :=
  sourceFetch state.environment count

def State.halted (globals : Globals) : State :=
  { globals, environment := .empty, control := .halted }

inductive Op where
  | add
  | lt
  | sload
  | sstore
  | gas
  | call
  | malloc
  | mallocUninit
  | mstore32
  | mload32
deriving DecidableEq, Repr

inductive Binary where
  | add
  | lt
deriving DecidableEq, Repr

def Binary.apply : Binary → Word → Word → Word
  | .add => .add
  | .lt => .lt

inductive Instr where
  | push (value : Word)
  | swap (depth : Nat)
  | exchange (firstDepth secondDepth : Nat)
  | dup (depth : Nat)
  | pop
  | op (operation : Op)
  | flippedOp (operation : Binary)
  | icall (callee : FunctionId) (argumentCount resultCount : Nat)
  | store (slot : Nat)
  | load (slot : Nat)
deriving DecidableEq, Repr

def Instr.isMemOracle : Instr → Prop
  | .op .malloc | .op .mallocUninit | .op .mload32 => True
  | _ => False

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

def Block.absoluteToPosition (block : Block) (index : Nat) : BlockPosition :=
  if index < block.instructions.size then .statement index else .terminator

def Block.startPosition (block : Block) : BlockPosition := block.absoluteToPosition 0

structure Function where
  entry : Block
  rest : Array Block
deriving Repr

def Function.blocks (function : Function) : Array Block := #[function.entry] ++ function.rest

def Function.block? (function : Function) (block : BlockId) : Option Block :=
  function.blocks[block.id]?

def Function.HasInstr (function : Function) (instruction : Instr) : Prop :=
  ∃ block ∈ function.blocks, instruction ∈ block.instructions

structure Program where
  init : Function
  rest : Array Function
deriving Repr

def Program.functions (program : Program) : Array Function := #[program.init] ++ program.rest

def Program.function? (program : Program) (function : FunctionId) : Option Function :=
  program.functions[function.id]?

def Program.block? (program : Program) (cursor : ProgramCursor) : Option Block := do
  let function ← program.function? cursor.fn
  function.block? cursor.block

def Program.HasInstr (program : Program) (instruction : Instr) : Prop :=
  ∃ function ∈ program.functions, function.HasInstr instruction

def Program.MemOracleFree (program : Program) : Prop :=
  ∀ instruction, program.HasInstr instruction → ¬ instruction.isMemOracle

def Program.instructionAt (program : Program) (control : Control) :
    Option (Control × Instr) := do
  let .running cursor := control | none
  let .statement index := cursor.position | none
  let block ← program.block? cursor
  let instruction ← block.instructions[index]?
  some (.running { cursor with position := block.absoluteToPosition (index + 1) }, instruction)

def Program.terminatorAt (program : Program) (control : Control) : Option Terminator := do
  let .running cursor := control | none
  let .terminator := cursor.position | none
  let block ← program.block? cursor
  some block.terminator

abbrev Program.atInstr (program : Program) (state : State) : Option (Control × Instr) :=
  program.instructionAt state.control

abbrev Program.atTerm (program : Program) (state : State) : Option Terminator :=
  program.terminatorAt state.control

@[simp] def Program.AtInstr (program : Program) (state : State) (next : Control)
    (instruction : Instr) : Prop :=
  program.atInstr state = some (next, instruction)

@[simp] def Program.AtTerm (program : Program) (state : State) (terminator : Terminator) : Prop :=
  program.atTerm state = some terminator

def State.allows (state : State) (size : Word) (allocation : Allocation) : Prop :=
  memoryPolicy.Allows state.globals.memory size.toNat allocation

def State.inBounds (state : State) (offset : Word) : Prop :=
  state.globals.memory.InBounds offset.toNat 32

def State.pushValues (state : State) (destination : Destination) (values : Array Word) :
    Except IRError Environment :=
  push state.environment destination values

def exchange (stack : List Word) (firstDepth secondDepth : Nat) : Option (List Word) := do
  let first ← stack[firstDepth]?
  let second ← stack[secondDepth]?
  some ((stack.set firstDepth second).set secondDepth first)

def evalBinary (operation : Word → Word → Word) (environment : Environment)
    (operands : Except IRError (Array Word)) : Except IRError Environment := do
  let values ← operands
  let some left := values[0]? | throw (.blockArityMismatch values.size 2)
  let some right := values[1]? | throw (.blockArityMismatch values.size 2)
  push environment ⟨2, 1⟩ #[operation left right]

def evalSload (context : CallContext) (globals : Globals) (environment : Environment) :
    Except IRError Environment := do
  let values ← sourceFetch environment 1
  let some key := values[0]? | throw (.blockArityMismatch values.size 1)
  push environment ⟨1, 1⟩ #[globals.world.loadStorage context.self key]

def evalInstr (context : CallContext) (globals : Globals) (environment : Environment) :
    Instr → Except IRError Environment
  | .push value => push environment ⟨0, 1⟩ #[value]
  | .swap depth =>
      match exchange environment.stack 0 depth with
      | some stack => .ok { environment with stack }
      | none => .error .invalidControl
  | .exchange firstDepth secondDepth =>
      if firstDepth = secondDepth then .error .invalidControl else
        match exchange environment.stack firstDepth secondDepth with
        | some stack => .ok { environment with stack }
        | none => .error .invalidControl
  | .dup depth =>
      match environment.stack[depth]? with
      | some value => .ok { environment with stack := value :: environment.stack }
      | none => .error .invalidControl
  | .pop =>
      match environment.stack with
      | _ :: stack => .ok { environment with stack }
      | [] => .error .invalidControl
  | .store slot =>
      match environment.stack with
      | value :: stack => .ok { environment.storeSlot slot value with stack }
      | [] => .error .invalidControl
  | .load slot =>
      match environment.slots slot with
      | some value => .ok { environment with stack := value :: environment.stack }
      | none => .error .invalidControl
  | .op .add => evalBinary .add environment (sourceFetch environment 2)
  | .op .lt => evalBinary .lt environment (sourceFetch environment 2)
  | .flippedOp operation =>
      evalBinary operation.apply environment (sourceFetchFlipped environment)
  | .op .sload => evalSload context globals environment
  | .op .sstore | .op .gas | .op .call | .op .malloc | .op .mallocUninit |
    .op .mstore32 | .op .mload32 | .icall _ _ _ => .error .invalidControl

def State.evaluate (state : State) (context : CallContext) (instruction : Instr) :
    Except IRError Environment :=
  evalInstr context state.globals state.environment instruction

def jump (program : Program) (environment : Environment) (cursor : ProgramCursor)
    (target : BlockId) : Option (Environment × Control) := do
  let source ← program.block? cursor
  let targetCursor := { cursor with block := target }
  let targetBlock ← program.block? targetCursor
  if environment.stack.length ≠ source.outputCount ∨ source.outputCount ≠ targetBlock.inputCount then
    none
  some (environment,
    .running { targetCursor with position := targetBlock.startPosition })

def evaluateTerminator (program : Program) (environment : Environment)
    (control : Control) : Terminator → Option (Environment × Control)
  | .halt => some (environment, .halted)
  | .jump target => do
      let .running cursor := control | none
      jump program environment cursor target
  | .branch thenTarget elseTarget => do
      let .running cursor := control | none
      let condition :: stack := environment.stack | none
      jump program { environment with stack } cursor
        (if condition = 0 then elseTarget else thenTarget)
  | .iret => do
      let .running cursor := control | none
      let block ← program.block? cursor
      if environment.stack.length ≠ block.outputCount then none
      some (environment, .returned environment.stack.toArray)

def resume (outcome : FunctionOutcome) (environment : Environment)
    (destination : Destination) (next : Control) : Option (Environment × Control) :=
  match outcome with
  | .returned results =>
      match push environment destination results with
      | .ok environment => some (environment, next)
      | .error _ => none
  | .halted => some (.empty, .halted)

def entry (program : Program) (functionId : FunctionId) (globals : Globals)
    (args : Array Word) : Option State := do
  let function ← program.function? functionId
  if args.size ≠ function.entry.inputCount then none
  some
    { globals
      environment := { Environment.empty with stack := args.toList }
      control := .running
        { fn := functionId, block := ⟨0⟩, position := function.entry.startPosition } }

set_option autoImplicit true in
mutual

inductive SmallStep (program : Program) (context : CallContext) :
    State → Trace → State → Prop where
  | pure
      (hinstr : program.AtInstr state next instruction)
      (heval : state.evaluate context instruction = .ok environment) :
      SmallStep program context state [] { state with environment, control := next }
  | sstore
      (hinstr : program.AtInstr state next (.op .sstore))
      (hfetch : state.fetch 2 = .ok #[key, value])
      (hpush : state.pushValues ⟨2, 0⟩ #[] = .ok environment) :
      SmallStep program context state []
        { globals := state.globals.storeStorage context key value, environment, control := next }
  | gas
      (hinstr : program.AtInstr state next (.op .gas))
      (hpush : state.pushValues ⟨0, 1⟩ #[answer] = .ok environment) :
      SmallStep program context state [.gas answer]
        { state with environment, control := next }
  | call
      (hinstr : program.AtInstr state next (.op .call))
      (hfetch : state.fetch 2 = .ok #[target, gasLimit])
      (hpush : state.pushValues ⟨2, 1⟩ #[.fromBool answer.success] = .ok environment) :
      SmallStep program context state
        [.call { input := state.globals.callInput target gasLimit, result := answer }]
        { globals := state.globals.applyCall answer, environment, control := next }
  | malloc
      (hinstr : program.AtInstr state next (.op .malloc))
      (hfetch : state.fetch 1 = .ok #[size])
      (hallow : state.allows size allocation)
      (hzero : allocation.bytes = ByteArray.mk (Array.replicate size.toNat 0))
      (hpush : state.pushValues ⟨1, 1⟩ #[allocation.offset] = .ok environment) :
      SmallStep program context state []
        { globals := state.globals.pushAlloc allocation, environment, control := next }
  | mallocUninit
      (hinstr : program.AtInstr state next (.op .mallocUninit))
      (hfetch : state.fetch 1 = .ok #[size])
      (hallow : state.allows size allocation)
      (hpush : state.pushValues ⟨1, 1⟩ #[allocation.offset] = .ok environment) :
      SmallStep program context state []
        { globals := state.globals.pushAlloc allocation, environment, control := next }
  | mstore32
      (hinstr : program.AtInstr state next (.op .mstore32))
      (hfetch : state.fetch 2 = .ok #[offset, value])
      (hbound : state.inBounds offset)
      (hpush : state.pushValues ⟨2, 0⟩ #[] = .ok environment) :
      SmallStep program context state []
        { globals := state.globals.writeWord32 offset value, environment, control := next }
  | mload32
      (hinstr : program.AtInstr state next (.op .mload32))
      (hfetch : state.fetch 1 = .ok #[offset])
      (hpush : state.pushValues ⟨1, 1⟩ #[state.globals.readWord32 offset assumed] =
        .ok environment) :
      SmallStep program context state [] { state with environment, control := next }
  | icall
      (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
      (hargs : state.fetch argumentCount = .ok args)
      (hcall : EvalFn program context callee state.globals args trace globals outcome)
      (hresume : resume outcome state.environment ⟨argumentCount, resultCount⟩ next =
        some (environment, resumed)) :
      SmallStep program context state trace
        { globals := globals, environment := environment, control := resumed }
  | control
      (hterm : program.AtTerm state terminator)
      (heval : evaluateTerminator program state.environment state.control terminator =
        some (environment, finalControl)) :
      SmallStep program context state []
        { state with environment := environment, control := finalControl }

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
      (hentry : entry program function globals args = some initial)
      (hrun : Steps program context initial trace final)
      (hexit : final.control = outcome.toControl) :
      EvalFn program context function globals args trace final.globals outcome

end

def Steps.Extends (program : Program) (context : CallContext) (state₁ : State)
    (trace₁ : Trace) (state₂ : State) (trace₂ : Trace) : Prop :=
  ∃ suffix, Steps program context state₁ suffix state₂ ∧ trace₁ ++ suffix = trace₂

end Sir.Stack
