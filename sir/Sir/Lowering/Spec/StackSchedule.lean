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
  blocks : Array StackSchedule.Block
  entry : BlockId
deriving DecidableEq, Repr

def StackSchedule.ofBlock (block : StackSchedule.Block) : StackSchedule where
  blocks := #[block]
  entry := ⟨0⟩

def StackSchedule.vars (schedule : StackSchedule) : Vars.Program :=
  { functions := #[
      { blocks := schedule.blocks.map fun block => block.vars.toBlock
        entry := schedule.entry }]
    initEntry := ⟨0⟩
    mainEntry := none }

def StackSchedule.stack (schedule : StackSchedule) : Stack.Program :=
  { functions := #[
      { blocks := schedule.blocks.map fun block => block.stack.toBlock
        entry := schedule.entry }]
    initEntry := ⟨0⟩ }

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

def StackSchedule.Block.check (block : StackSchedule.Block) : Bool :=
  decide (block.vars.entryLayout.map Symbolic.Value.identifier = block.vars.inputs ∧
      block.vars.exitLayout.map Symbolic.Value.identifier = block.vars.outputs ∧
      (block.vars.terminator = .halt →
        block.vars.exitLayout = #[] ∧ block.vars.outputs = #[])) &&
    match Symbolic.executeAll block.vars.statements block.stack.instructions
      (Symbolic.State.initial block.vars.entryLayout) with
    | none => false
    | some finalState =>
        match StackSchedule.Block.finalStack block.vars.terminator block.vars.exitLayout
            finalState.stack with
        | some expectedStack =>
            Symbolic.readsAvailable block.vars.statements block.vars.entryLayout &&
            Symbolic.definesOnce block.vars.statements block.vars.entryLayout &&
            decide (finalState.firedCount = block.vars.statements.size ∧
              StackSchedule.Block.terminatorsAgree block.vars.terminator
                block.stack.terminator = true ∧
              finalState.stack = expectedStack ∧ block.vars.entryLayout.toList.Nodup)
        | none => false

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

def StackSchedule.check (schedule : StackSchedule) : Bool :=
  decide (schedule.entry.id < schedule.blocks.size) &&
    schedule.blocks.all StackSchedule.Block.check &&
    schedule.blocks.all schedule.blockEdgesAgree

end Sir.Lowering
