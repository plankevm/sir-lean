import Sir.Lowering.Spec.Symbolic

namespace Sir.Lowering

namespace StackSchedule.Block

structure Source where
  inputs : Array VarId
  statements : Array Vars.Stmt
  terminator : Vars.Terminator
  outputs : Array VarId
  entryLayout : Array Symbolic.Value
  exitLayout : Array Symbolic.Value
deriving DecidableEq, Repr

def Source.toBlock (source : Source) : Vars.Block :=
  { inputs := source.inputs
    statements := source.statements
    terminator := source.terminator
    outputs := source.outputs }

structure Target (entryCount exitCount : Nat) where
  instructions : Array Stack.Instr
  terminator : Stack.Terminator
deriving DecidableEq, Repr

def Target.toBlock {entryCount exitCount : Nat}
    (target : Target entryCount exitCount) : Stack.Block :=
  { inputCount := entryCount
    instructions := target.instructions
    terminator := target.terminator
    outputCount := exitCount }

end StackSchedule.Block

structure StackSchedule.Block where
  vars : StackSchedule.Block.Source
  stack : StackSchedule.Block.Target vars.entryLayout.size vars.exitLayout.size
deriving DecidableEq, Repr

structure StackSchedule where
  entry : StackSchedule.Block
  rest : Array StackSchedule.Block
deriving DecidableEq, Repr

def StackSchedule.blocks (schedule : StackSchedule) : Array StackSchedule.Block :=
  #[schedule.entry] ++ schedule.rest

inductive StackSchedule.Error where
  | inputLayoutMismatch (expected got : Array VarId)
  | outputLayoutMismatch (expected got : Array VarId)
  | outputsAtHalt (outputs : Array VarId)
  | useBeforeDefinition (statement : Vars.Stmt) (identifier : VarId)
  | operandMismatch (instruction : Stack.Instr)
  | unsupportedInstruction (instruction : Stack.Instr)
  | notSingleAssignment (identifier : VarId)
  | unfiredStatements (remaining : Array Vars.Stmt)
  | terminatorMismatch
  | residualStackAtNonHalt
  | boundaryArityMismatch (edge : BlockId × BlockId) (expected got : Nat)
  | missingBlock (block : BlockId)
deriving DecidableEq

def StackSchedule.ofBlock (block : StackSchedule.Block) : StackSchedule where
  entry := block
  rest := #[]

def StackSchedule.varsFunction (schedule : StackSchedule) : Vars.Function :=
  { entry := schedule.entry.vars.toBlock
    rest := schedule.rest.map fun block => block.vars.toBlock }

def StackSchedule.stackFunction (schedule : StackSchedule) : Stack.Function :=
  { entry := schedule.entry.stack.toBlock
    rest := schedule.rest.map fun block => block.stack.toBlock }

def StackSchedule.Block.terminatorsAgree : Vars.Terminator → Stack.Terminator → Bool
  | .halt, .halt => true
  | .jump sourceTarget, .jump targetTarget => sourceTarget == targetTarget
  | .branch _ sourceThen sourceElse, .branch targetThen targetElse =>
      sourceThen == targetThen && sourceElse == targetElse
  | _, _ => false

def StackSchedule.Block.finalStack (terminator : Vars.Terminator)
    (exitLayout : Array Symbolic.Value) (residualStack : List Symbolic.Value) :
    Option (List Symbolic.Value) :=
  match terminator with
  | .halt => some residualStack
  | .jump _ => some exitLayout.toList
  | .branch condition _ _ => some (.variable condition :: exitLayout.toList)
  | .iret => none

def StackSchedule.identifierUnavailable (available : List VarId) (identifier : VarId) : Bool :=
  !available.contains identifier

def StackSchedule.firstUnavailable (statements : List Vars.Stmt) (available : List VarId) :
    Option (Vars.Stmt × VarId) :=
  match statements with
  | [] => none
  | statement :: remaining =>
      if let some identifier :=
          statement.variablesRead.find? (StackSchedule.identifierUnavailable available) then
        some (statement, identifier)
      else
        StackSchedule.firstUnavailable remaining (statement.variablesDefined ++ available)

def StackSchedule.firstDuplicate (identifiers : List VarId) : Option VarId :=
  match identifiers with
  | [] => none
  | identifier :: remaining =>
      if remaining.contains identifier then
        some identifier
      else
        StackSchedule.firstDuplicate remaining

def StackSchedule.unfiredStatements (statements : List Vars.Stmt) (fired : List Nat)
    (index : Nat := 0) : List Vars.Stmt :=
  match statements with
  | [] => []
  | statement :: remaining =>
      if fired.contains index then
        StackSchedule.unfiredStatements remaining fired (index + 1)
      else
        statement :: StackSchedule.unfiredStatements remaining fired (index + 1)

def StackSchedule.rejection : Stack.Instr → StackSchedule.Error
  | .icall callee argumentCount resultCount =>
      .unsupportedInstruction (.icall callee argumentCount resultCount)
  | instruction => .operandMismatch instruction

def StackSchedule.Block.execute (sourceStatements : Array Vars.Stmt) :
    List Stack.Instr → Symbolic.State → Except StackSchedule.Error Symbolic.State
  | [], state => .ok state
  | instruction :: remaining, state =>
      match Symbolic.execute sourceStatements state instruction with
      | none => .error (StackSchedule.rejection instruction)
      | some next => StackSchedule.Block.execute sourceStatements remaining next

def StackSchedule.Block.checkFinalStack (block : StackSchedule.Block)
    (finalState : Symbolic.State) : Except StackSchedule.Error Unit := do
  match block.vars.terminator with
  | .halt => pure ()
  | .jump _ =>
      if finalState.stack = block.vars.exitLayout.toList then
        pure ()
      else
        throw .residualStackAtNonHalt
  | .branch condition _ _ =>
      if finalState.stack = .variable condition :: block.vars.exitLayout.toList then
        pure ()
      else
        throw .residualStackAtNonHalt
  | .iret => throw .terminatorMismatch

def StackSchedule.Block.check (block : StackSchedule.Block) :
    Except StackSchedule.Error Unit := do
  let entryIdentifiers := block.vars.entryLayout.map Symbolic.Value.identifier
  let exitIdentifiers := block.vars.exitLayout.map Symbolic.Value.identifier
  if entryIdentifiers != block.vars.inputs then
    throw (.inputLayoutMismatch block.vars.inputs entryIdentifiers)
  if exitIdentifiers != block.vars.outputs then
    throw (.outputLayoutMismatch block.vars.outputs exitIdentifiers)
  if block.vars.terminator = .halt && block.vars.outputs != #[] then
    throw (.outputsAtHalt block.vars.outputs)

  let finalState ← StackSchedule.Block.execute block.vars.statements block.stack.instructions.toList
      (Symbolic.State.initial block.vars.entryLayout)

  if let some (statement, identifier) := StackSchedule.firstUnavailable block.vars.statements.toList
        (block.vars.entryLayout.toList.map Symbolic.Value.identifier) then
    throw (.useBeforeDefinition statement identifier)

  let identifiers := (block.vars.entryLayout.toList.map Symbolic.Value.identifier) ++
      block.vars.statements.toList.flatMap Vars.Stmt.variablesDefined
  if let some identifier := StackSchedule.firstDuplicate identifiers then
    throw (.notSingleAssignment identifier)

  if finalState.firedCount != block.vars.statements.size then
    throw (.unfiredStatements
      (StackSchedule.unfiredStatements block.vars.statements.toList
        finalState.firedStatementIndices).toArray)
  if !StackSchedule.Block.terminatorsAgree block.vars.terminator block.stack.terminator then
    throw .terminatorMismatch

  block.checkFinalStack finalState

def StackSchedule.layoutAgreesAt (schedule : StackSchedule)
    (exitLayout : Array Symbolic.Value) (successor : BlockId) : Bool :=
  match schedule.blocks[successor.id]? with
  | some successorBlock => exitLayout.size == successorBlock.vars.entryLayout.size
  | none => false

def StackSchedule.blockEdgesAgree (schedule : StackSchedule) (block : StackSchedule.Block) : Bool :=
  match block.vars.terminator with
  | .halt => true
  | .jump successor => schedule.layoutAgreesAt block.vars.exitLayout successor
  | .branch _ thenSuccessor elseSuccessor =>
      schedule.layoutAgreesAt block.vars.exitLayout thenSuccessor &&
        schedule.layoutAgreesAt block.vars.exitLayout elseSuccessor
  | .iret => false

def StackSchedule.checkBlocks : List StackSchedule.Block → Except StackSchedule.Error Unit
  | [] => .ok ()
  | block :: remaining => do
      block.check
      StackSchedule.checkBlocks remaining

def StackSchedule.checkEdge (schedule : StackSchedule) (source successor : BlockId)
    (exitLayout : Array Symbolic.Value) : Except StackSchedule.Error Unit := do
  let some successorBlock := schedule.blocks[successor.id]? | throw (.missingBlock successor)
  let expected := successorBlock.vars.entryLayout.size
  let got := exitLayout.size
  if expected = got then
    pure ()
  else
    throw (.boundaryArityMismatch (source, successor) expected got)

def StackSchedule.checkBlockEdges (schedule : StackSchedule) (source : BlockId)
    (block : StackSchedule.Block) : Except StackSchedule.Error Unit := do
  match block.vars.terminator with
  | .halt => pure ()
  | .jump successor => schedule.checkEdge source successor block.vars.exitLayout
  | .branch _ thenSuccessor elseSuccessor => do
      schedule.checkEdge source thenSuccessor block.vars.exitLayout
      schedule.checkEdge source elseSuccessor block.vars.exitLayout
  | .iret => pure ()

def StackSchedule.checkEdges (schedule : StackSchedule) (blocks : List StackSchedule.Block)
    (index : Nat := 0) : Except StackSchedule.Error Unit :=
  match blocks with
  | [] => .ok ()
  | block :: remaining => do
      schedule.checkBlockEdges ⟨index⟩ block
      schedule.checkEdges remaining (index + 1)

def StackSchedule.check (schedule : StackSchedule) : Except StackSchedule.Error Unit := do
  StackSchedule.checkBlocks schedule.blocks.toList
  schedule.checkEdges schedule.blocks.toList

structure ProgramSchedule where
  init : StackSchedule
  main : Option StackSchedule
deriving DecidableEq, Repr

def StackSchedule.program (schedule : StackSchedule) : ProgramSchedule :=
  { init := schedule, main := none }

def ProgramSchedule.vars (schedule : ProgramSchedule) : Vars.Program :=
  { init := schedule.init.varsFunction
    main := schedule.main.map StackSchedule.varsFunction
    rest := #[] }

def ProgramSchedule.stack (schedule : ProgramSchedule) : Stack.Program :=
  { init := schedule.init.stackFunction
    rest := schedule.main.toArray.map StackSchedule.stackFunction }

def ProgramSchedule.check (schedule : ProgramSchedule) : Except StackSchedule.Error Unit := do
  schedule.init.check
  match schedule.main with
  | none => pure ()
  | some main => main.check

end Sir.Lowering
