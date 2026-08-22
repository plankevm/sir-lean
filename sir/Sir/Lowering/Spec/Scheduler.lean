import Sir.Lowering.Spec.StackSchedule

namespace Sir.Lowering

inductive Scheduler.Error where
  | unavailableVariable
  | unsupportedStatementKind
  | duplicateAssignment
deriving DecidableEq

def Scheduler := Array Vars.Stmt → Except Scheduler.Error StackSchedule

def Scheduler.Accepted (scheduler : Scheduler) : Prop :=
  ∀ statements schedule, scheduler statements = .ok schedule →
    schedule.entry.vars.statements = statements ∧ schedule.check = .ok ()

def spillAll.lowerStatement : Vars.Stmt → Option (Array Stack.Instr)
  | .assign result (.constant value) =>
      some #[.op (.constant value), .store result.id]
  | .assign result (.var source) =>
      some #[.load source.id, .op .copy, .store result.id]
  | .assign result (.add lhs rhs) =>
      some #[.load rhs.id, .load lhs.id, .op .add, .store result.id]
  | .assign result (.lt lhs rhs) =>
      some #[.load rhs.id, .load lhs.id, .op .lt, .store result.id]
  | _ => none

def spillAll.lowerStatements (statements : Array Vars.Stmt) : Option (Array Stack.Instr) :=
  (statements.mapM spillAll.lowerStatement).map (Array.flatten ·)

def spillAll.definitions (statements : Array Vars.Stmt) : Option (List VarId) :=
  statements.toList.foldlM Symbolic.recordDefinitions []

def spillAll.singleAssignment (statements : Array Vars.Stmt) : Bool :=
  decide (statements.toList.flatMap Vars.Stmt.variablesDefined).Nodup

def spillAll.schedule (sourceStatements : Array Vars.Stmt)
    (targetInstructions : Array Stack.Instr) : StackSchedule :=
  StackSchedule.ofBlock {
    vars := {
      inputs := #[]
      statements := sourceStatements
      terminator := .halt
      outputs := #[]
      entryLayout := #[]
      exitLayout := #[] }
    stack := {
      instructions := targetInstructions
      terminator := .halt } }

def spillAll : Scheduler := fun statements =>
  if spillAll.singleAssignment statements then
    match spillAll.definitions statements with
    | none => .error .unavailableVariable
    | some _ =>
        match spillAll.lowerStatements statements with
        | none => .error .unsupportedStatementKind
        | some targetInstructions => .ok (spillAll.schedule statements targetInstructions)
  else
    .error .duplicateAssignment

end Sir.Lowering
