import Sir.Core.Spec

namespace Sir.Stack

open Sir

structure Destination where
  consume : Nat
  produce : Nat
deriving DecidableEq, Repr

def Destination.after (destination : Destination) (height : Nat) : Nat :=
  height - destination.consume + destination.produce

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

def State.of (globals : Globals) (environment : Environment) (control : Control) : State :=
  ⟨globals, environment, control⟩

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

def Op.effect : Op → Destination
  | .gas => ⟨0, 1⟩
  | .add | .lt | .call => ⟨2, 1⟩
  | .sload | .malloc | .mallocUninit | .mload32 => ⟨1, 1⟩
  | .sstore | .mstore32 => ⟨2, 0⟩

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

def Instr.effect : Instr → Destination
  | .push _ | .load _ => ⟨0, 1⟩
  | .pop | .store _ => ⟨1, 0⟩
  | .swap depth => ⟨depth + 1, depth + 1⟩
  | .dup depth => ⟨depth + 1, depth + 2⟩
  | .exchange firstDepth secondDepth =>
      ⟨max firstDepth secondDepth + 1, max firstDepth secondDepth + 1⟩
  | .flippedOp _ => ⟨2, 1⟩
  | .icall _ argumentCount resultCount => ⟨argumentCount, resultCount⟩
  | .op operation => operation.effect

def Instr.slotsStored : Instr → List Nat
  | .store slot => [slot]
  | _ => []

def Instr.slotsRead : Instr → List Nat
  | .load slot => [slot]
  | _ => []

inductive Terminator where
  | halt
  | jump (target : BlockId)
  | branch (thenTarget elseTarget : BlockId)
  | iret
deriving DecidableEq, Repr

def Terminator.HeightFits : Terminator → Nat → Nat → Prop
  | .halt, _, _ => True
  | .jump _, height, outputCount => height = outputCount
  | .branch _ _, height, outputCount => height = outputCount + 1
  | .iret, height, outputCount => height = outputCount

structure Block where
  inputCount : Nat
  instructions : Array Instr
  terminator : Terminator
  outputCount : Nat
deriving Repr

def Block.absoluteToPosition (block : Block) (index : Nat) : BlockPosition :=
  if index < block.instructions.size then .statement index else .terminator

def Block.startPosition (block : Block) : BlockPosition := block.absoluteToPosition 0

def Block.heightBefore (block : Block) : Nat → Nat
  | 0 => block.inputCount
  | index + 1 =>
      match block.instructions[index]? with
      | some instruction => instruction.effect.after (block.heightBefore index)
      | none => block.heightBefore index

def Block.slotsStoredBefore (block : Block) : Nat → List Nat
  | 0 => []
  | index + 1 =>
      match block.instructions[index]? with
      | some instruction => block.slotsStoredBefore index ++ instruction.slotsStored
      | none => block.slotsStoredBefore index

def Block.StackHeightsFit (block : Block) : Prop :=
  (∀ index instruction, block.instructions[index]? = some instruction →
    instruction.effect.consume ≤ block.heightBefore index) ∧
  block.terminator.HeightFits (block.heightBefore block.instructions.size) block.outputCount

def Block.SlotsStoredBeforeLoad (block : Block) : Prop :=
  ∀ index instruction, block.instructions[index]? = some instruction →
    ∀ slot ∈ instruction.slotsRead, slot ∈ block.slotsStoredBefore index

structure Function where
  entry : Block
  rest : Array Block
deriving Repr

def Function.blocks (function : Function) : Array Block := #[function.entry] ++ function.rest

def Function.block? (function : Function) (block : BlockId) : Option Block :=
  function.blocks[block.id]?

def Function.outputs? (function : Function) : Option Nat :=
  (function.blocks.find? (fun block => decide (block.terminator = .iret))).map (·.outputCount)

def Terminator.jumpTargets : Terminator → List BlockId
  | .jump target => [target]
  | .branch thenTarget elseTarget => [thenTarget, elseTarget]
  | .halt | .iret => []


def Function.HasInstr (function : Function) (instruction : Instr) : Prop :=
  ∃ block ∈ function.blocks, instruction ∈ block.instructions

structure Program where
  init : Function
  main : Option Function
  rest : Array Function
deriving Repr

def Program.functions (program : Program) : Array Function :=
  #[program.init] ++ program.main.toArray ++ program.rest

def Program.initId (_ : Program) : FunctionId := ⟨0⟩

def Program.mainId? (program : Program) : Option FunctionId :=
  program.main.map fun _ => ⟨1⟩

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
    Instr → Except IRError (Globals × Environment)
  | .push value =>
      (push environment ⟨0, 1⟩ #[value]).map fun environment => (globals, environment)
  | .swap depth =>
      match exchange environment.stack 0 depth with
      | some stack => .ok (globals, { environment with stack })
      | none => .error .invalidControl
  | .exchange firstDepth secondDepth =>
      if firstDepth = secondDepth then .error .invalidControl else
        match exchange environment.stack firstDepth secondDepth with
        | some stack => .ok (globals, { environment with stack })
        | none => .error .invalidControl
  | .dup depth =>
      match environment.stack[depth]? with
      | some value => .ok (globals, { environment with stack := value :: environment.stack })
      | none => .error .invalidControl
  | .pop =>
      match environment.stack with
      | _ :: stack => .ok (globals, { environment with stack })
      | [] => .error .invalidControl
  | .store slot =>
      match environment.stack with
      | value :: stack => .ok (globals, { environment.storeSlot slot value with stack })
      | [] => .error .invalidControl
  | .load slot =>
      match environment.slots slot with
      | some value => .ok (globals, { environment with stack := value :: environment.stack })
      | none => .error .invalidControl
  | .op .add =>
      (evalBinary .add environment (sourceFetch environment 2)).map (globals, ·)
  | .op .lt =>
      (evalBinary .lt environment (sourceFetch environment 2)).map (globals, ·)
  | .flippedOp operation =>
      (evalBinary operation.apply environment (sourceFetchFlipped environment)).map (globals, ·)
  | .op .sload =>
      (evalSload context globals environment).map (globals, ·)
  | .op .sstore => do
      let values ← sourceFetch environment 2
      let some key := values[0]? | throw (.blockArityMismatch values.size 2)
      let some value := values[1]? | throw (.blockArityMismatch values.size 2)
      let environment ← push environment ⟨2, 0⟩ #[]
      return (globals.storeStorage context key value, environment)
  | .op .gas | .op .call | .op .malloc | .op .mallocUninit |
    .op .mstore32 | .op .mload32 | .icall _ _ _ => .error .invalidControl

def State.evaluate (state : State) (context : CallContext) (instruction : Instr) :
    Except IRError (Globals × Environment) :=
  evalInstr context state.globals state.environment instruction

def jump (program : Program) (environment : Environment) (cursor : ProgramCursor)
    (target : BlockId) : Except IRError (Environment × Control) := do
  let some source := program.block? cursor | .error (.invalidBlock cursor.block)
  let some targetBlock := program.block? { cursor with block := target } |
    .error (.invalidBlock target)
  if environment.stack.length ≠ source.outputCount then
    throw (.blockArityMismatch environment.stack.length source.outputCount)
  if source.outputCount ≠ targetBlock.inputCount then
    throw (.blockArityMismatch source.outputCount targetBlock.inputCount)
  .ok (environment, .running
    { cursor with block := target, position := targetBlock.startPosition })

def evaluateTerminator (program : Program) (environment : Environment)
    (control : Control) : Terminator → Except IRError (Environment × Control)
  | .halt => .ok (environment, .halted)
  | .jump target => do
      let .running cursor := control | .error .invalidControl
      jump program environment cursor target
  | .branch thenTarget elseTarget => do
      let .running cursor := control | .error .invalidControl
      let condition :: stack := environment.stack | .error (.blockArityMismatch 0 1)
      jump program { environment with stack } cursor
        (if condition = 0 then elseTarget else thenTarget)
  | .iret => do
      let .running cursor := control | .error .invalidControl
      let some block := program.block? cursor | .error (.invalidBlock cursor.block)
      if environment.stack.length ≠ block.outputCount then
        throw (.blockArityMismatch environment.stack.length block.outputCount)
      .ok (environment, .returned environment.stack.toArray)

def resume (outcome : FunctionOutcome) (environment : Environment)
    (destination : Destination) (next : Control) : Except IRError (Environment × Control) := do
  match outcome with
  | .returned results => do
      let environment ← push environment destination results
      .ok (environment, next)
  | .halted => .ok (.empty, .halted)

def Program.callState? (program : Program) (functionId : FunctionId) (globals : Globals)
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
  -- matches: push, swap, exchange, dup, pop, store, load, flippedOp, op add/lt/sload/sstore
  | evaluate
      (hinstr : program.AtInstr state next instruction)
      (heval : state.evaluate context instruction = .ok (globals, environment)) :
      SmallStep program context state [] (State.of globals environment next)
  | gas {answer : Word}
      (hinstr : program.AtInstr state next (.op .gas))
      (hpush : state.pushValues ⟨0, 1⟩ #[answer] = .ok environment) :
      SmallStep program context state [.gas answer]
        (State.of state.globals environment next)
  | call {answer : CallResult}
      (hinstr : program.AtInstr state next (.op .call))
      (hfetch : state.fetch 2 = .ok #[target, gasLimit])
      (hpush : state.pushValues ⟨2, 1⟩ #[.fromBool answer.success] = .ok environment) :
      SmallStep program context state
        [.call { input := state.globals.callInput target gasLimit, result := answer }]
        (State.of (state.globals.applyCall answer) environment next)
  | malloc {allocation : Allocation}
      (hinstr : program.AtInstr state next (.op .malloc))
      (hfetch : state.fetch 1 = .ok #[size])
      (hallow : state.allows size allocation)
      (hzero : allocation.bytes = ByteArray.mk (Array.replicate size.toNat 0))
      (hpush : state.pushValues ⟨1, 1⟩ #[allocation.offset] = .ok environment) :
      SmallStep program context state []
        (State.of (state.globals.pushAlloc allocation) environment next)
  | mallocUninit {allocation : Allocation}
      (hinstr : program.AtInstr state next (.op .mallocUninit))
      (hfetch : state.fetch 1 = .ok #[size])
      (hallow : state.allows size allocation)
      (hpush : state.pushValues ⟨1, 1⟩ #[allocation.offset] = .ok environment) :
      SmallStep program context state []
        (State.of (state.globals.pushAlloc allocation) environment next)
  | mstore32
      (hinstr : program.AtInstr state next (.op .mstore32))
      (hfetch : state.fetch 2 = .ok #[offset, value])
      (hbound : state.inBounds offset)
      (hpush : state.pushValues ⟨2, 0⟩ #[] = .ok environment) :
      SmallStep program context state []
        (State.of (state.globals.writeWord32 offset value) environment next)
  | mload32 {assumed : Vector UInt8 32}
      (hinstr : program.AtInstr state next (.op .mload32))
      (hfetch : state.fetch 1 = .ok #[offset])
      (hpush : state.pushValues ⟨1, 1⟩ #[state.globals.readWord32 offset assumed] =
        .ok environment) :
      SmallStep program context state [] (State.of state.globals environment next)
  | icall
      (hinstr : program.AtInstr state next (.icall callee argumentCount resultCount))
      (hargs : state.fetch argumentCount = .ok args)
      (hcall : EvalFn program context callee state.globals args trace globals outcome)
      (hresume : resume outcome state.environment ⟨argumentCount, resultCount⟩ next =
        .ok (environment, resumed)) :
      SmallStep program context state trace (State.of globals environment resumed)
  | control
      (hterm : program.AtTerm state terminator)
      (heval : evaluateTerminator program state.environment state.control terminator =
        .ok (environment, finalControl)) :
      SmallStep program context state []
        (State.of state.globals environment finalControl)

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

def Program.FunctionInputOutputArity (program : Program) (inputCount : Nat)
    (outputCount : Option Nat) (functionId : FunctionId) : Prop :=
  ∃ fn, program.function? functionId = some fn ∧
    fn.entry.inputCount = inputCount ∧ fn.outputs? = outputCount

def Program.callEdge (program : Program) (caller callee : FunctionId) : Prop :=
  ∃ argumentCount resultCount function,
    program.function? caller = some function ∧
      function.HasInstr (.icall callee argumentCount resultCount)

def Program.NonIcallControl (program : Program) (state : State) : Prop :=
  (∃ next instruction,
      program.AtInstr state next instruction ∧
      ∀ callee argumentCount resultCount,
        instruction ≠ .icall callee argumentCount resultCount) ∨
    ∃ terminator, program.AtTerm state terminator

def Program.AllocationAvailable (program : Program) (state : State) : Prop :=
  (∀ next size,
      program.AtInstr state next (.op .malloc) →
      state.fetch 1 = .ok #[size] →
      ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = size.toNat ∧
        allocation.bytes = ByteArray.mk (Array.replicate size.toNat 0)) ∧
    ∀ next size,
      program.AtInstr state next (.op .mallocUninit) →
      state.fetch 1 = .ok #[size] →
      ∃ allocation, state.globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = size.toNat

def Program.BumpFits (program : Program) (state : State) : Prop :=
  (∀ next size,
      program.AtInstr state next (.op .malloc) →
      state.fetch 1 = .ok #[size] →
      state.globals.memory.watermark + size.toNat ≤ Evm.UInt256.size) ∧
    ∀ next size,
      program.AtInstr state next (.op .mallocUninit) →
      state.fetch 1 = .ok #[size] →
      state.globals.memory.watermark + size.toNat ≤ Evm.UInt256.size

def Program.StoreInBounds (program : Program) (state : State) : Prop :=
  ∀ next offset value,
    program.AtInstr state next (.op .mstore32) →
    state.fetch 2 = .ok #[offset, value] →
    state.inBounds offset

def Program.RunsFunction (program : Program) (ctx : CallContext) (function : FunctionId)
    (globals : Globals) (args : Array Word) (trace : Trace) (state : State) : Prop :=
  ∃ initial,
    program.callState? function globals args = some initial ∧
    Steps program ctx initial trace state

def Program.Runs (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (state : State) : Prop :=
  program.RunsFunction ctx entry { world := world } #[] trace state

def Program.RunsTo (program : Program) (ctx : CallContext) (entry : FunctionId)
    (world : World) (trace : Trace) (final : State) : Prop :=
  program.Runs ctx entry world trace final ∧ final.control = .halted

def Program.ReadyState (program : Program) (ctx : CallContext) (state : State) : Prop :=
  (∃ function globals args trace,
      program.RunsFunction ctx function globals args trace state) ∧
    program.NonIcallControl state ∧
    (program.AllocationAvailable state ∨ program.BumpFits state) ∧
    program.StoreInBounds state

structure Program.WellFormed (program : Program) : Prop where
  icallArity :
    ∀ callee argumentCount resultCount, program.HasInstr (.icall callee argumentCount resultCount) →
      ∃ outputs, program.FunctionInputOutputArity argumentCount outputs callee ∧
        outputs.getD 0 = resultCount
  iretArity :
    ∀ function ∈ program.functions, ∀ block ∈ function.blocks,
      block.terminator = .iret → some block.outputCount = function.outputs?
  acyclicCalls : ∀ f, ¬ Relation.TransGen program.callEdge f f
  entryArity :
    (program.init.entry.inputCount = 0 ∧ program.init.outputs? = none) ∧
      ∀ main, program.main = some main → main.entry.inputCount = 0 ∧ main.outputs? = none
  validJumpTargets :
    ∀ function ∈ program.functions,
      ∀ block ∈ function.blocks, ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, function.block? target = some targetBlock ∧
          targetBlock.inputCount = block.outputCount
  exchangeDepthsDistinct :
    ∀ firstDepth secondDepth, program.HasInstr (.exchange firstDepth secondDepth) →
      firstDepth ≠ secondDepth
  stackHeightsFit :
    ∀ function ∈ program.functions, ∀ block ∈ function.blocks, block.StackHeightsFit
  slotsStoredBeforeLoad :
    ∀ function ∈ program.functions, ∀ block ∈ function.blocks, block.SlotsStoredBeforeLoad

def Program.FnNextEffect (program : Program) (ctx : CallContext)
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
        EvalFn program ctx function globals args history finalGlobals .halted ∧
        finalGlobals.world = world
  | .returned world values =>
      ∃ finalGlobals,
        EvalFn program ctx function globals args history finalGlobals (.returned values) ∧
        finalGlobals.world = world

def Program.NextEffect (program : Program) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) (history : Trace) (outcome : ObservableOutcome) : Prop :=
  program.FnNextEffect ctx entry { world := world₀ } #[] history
    outcome.functionOutcome

def Program.FunctionDeterministicFrom (program : Program) (ctx : CallContext)
    (function : FunctionId) (globals : Globals) (args : Array Word) : Prop :=
  ∀ history outcome₁ outcome₂,
    program.FnNextEffect ctx function globals args history outcome₁ →
    program.FnNextEffect ctx function globals args history outcome₂ →
    outcome₁ = outcome₂

def Program.DeterministicFrom (program : Program) (ctx : CallContext)
    (entry : FunctionId) (world₀ : World) : Prop :=
  ∀ history outcome₁ outcome₂,
    program.NextEffect ctx entry world₀ history outcome₁ →
    program.NextEffect ctx entry world₀ history outcome₂ →
    outcome₁ = outcome₂

def Program.Deterministic (program : Program) : Prop :=
  ∀ ctx world₀,
    program.DeterministicFrom ctx program.initId world₀ ∧
      ∀ entry, program.mainId? = some entry →
        program.DeterministicFrom ctx entry world₀

def Program.FunctionDeterministic (program : Program) (function : FunctionId) : Prop :=
  ∀ ctx globals args trace₁ trace₂ finalGlobals₁ finalGlobals₂ outcome₁ outcome₂,
    EvalFn program ctx function globals args trace₁ finalGlobals₁ outcome₁ →
    EvalFn program ctx function globals args trace₂ finalGlobals₂ outcome₂ →
    (trace₁ = trace₂ ∧ finalGlobals₁ = finalGlobals₂ ∧ outcome₁ = outcome₂) ∨
      trace₁.QueryDivergence trace₂

end Sir.Stack
