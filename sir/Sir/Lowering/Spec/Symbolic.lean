import Sir.Stack.Spec
import Sir.Vars.Spec

namespace Sir.Lowering.Symbolic

inductive Value where
  | variable (identifier : VarId)
deriving DecidableEq, Repr

def Value.identifier : Value → VarId
  | .variable identifier => identifier

structure State where
  stack : List Value
  slotBindings : Array (Nat × Value)
  entryVariables : List VarId
  firedStatementIndices : List Nat
deriving DecidableEq, Repr

def State.initial (entryLayout : Array Value) : State :=
  ⟨entryLayout.toList, #[], entryLayout.toList.map Value.identifier, []⟩

def State.firedCount (state : State) : Nat :=
  state.firedStatementIndices.length

def State.slotValue? (state : State) (slot : Nat) : Option Value :=
  (state.slotBindings.find? fun binding => binding.1 = slot).map Prod.snd

def State.slotFree (state : State) (operandCount : Nat) (result : Value) : Bool :=
  !(state.stack.drop operandCount).contains result &&
    state.slotBindings.all fun binding => binding.2 != result

def operationOf : Vars.Stmt → Option (Machine.Operation × List Value × Value)
  | .assign result (.constant value) => some (.constant value, [], .variable result)
  | .assign result (.var source) => some (.copy, [.variable source], .variable result)
  | .assign result (.add lhs rhs) =>
      some (.add, [.variable lhs, .variable rhs], .variable result)
  | .assign result (.lt lhs rhs) =>
      some (.lt, [.variable lhs, .variable rhs], .variable result)
  | _ => none

def definesVariable (sourceStatements : Array Vars.Stmt) (identifier : VarId)
    (statementIndex : Nat) : Bool :=
  match sourceStatements[statementIndex]? with
  | some statement => statement.variablesDefined.contains identifier
  | none => false

def State.available (state : State) (sourceStatements : Array Vars.Stmt)
    (identifier : VarId) : Bool :=
  state.entryVariables.contains identifier ||
    state.firedStatementIndices.any (definesVariable sourceStatements identifier)

def State.fireable (state : State) (sourceStatements : Array Vars.Stmt)
    (operation : Machine.Operation) (candidate : Vars.Stmt × Nat) : Bool :=
  match operationOf candidate.1 with
  | none => false
  | some (expectedOperation, operands, result) =>
      decide (candidate.2 ∉ state.firedStatementIndices ∧ expectedOperation = operation ∧
        operands.length ≤ state.stack.length ∧ state.stack.take operands.length = operands ∧
        state.slotFree operands.length result = true ∧
        candidate.1.variablesRead.all (state.available sourceStatements) = true)

def State.firstFireable (state : State) (sourceStatements : Array Vars.Stmt)
    (operation : Machine.Operation) : Option (Vars.Stmt × Nat) :=
  sourceStatements.toList.zipIdx.find? (state.fireable sourceStatements operation)

def recordDefinitions (defined : List VarId) (statement : Vars.Stmt) : Option (List VarId) :=
  if statement.variablesRead.all defined.contains then
    some (statement.variablesDefined ++ defined)
  else
    none

def readsAvailable (sourceStatements : Array Vars.Stmt) (entryLayout : Array Value) : Bool :=
  (sourceStatements.toList.foldlM recordDefinitions
    (entryLayout.toList.map Value.identifier)).isSome

def definesOnce (sourceStatements : Array Vars.Stmt) (entryLayout : Array Value) : Bool :=
  decide ((entryLayout.toList.map Value.identifier) ++
    sourceStatements.toList.flatMap Vars.Stmt.variablesDefined).Nodup

def exchange (stack : List Value) (firstDepth secondDepth : Nat) : Option (List Value) :=
  match stack[firstDepth]?, stack[secondDepth]? with
  | some first, some second => some ((stack.set firstDepth second).set secondDepth first)
  | _, _ => none

def State.fireNextStatement (sourceStatements : Array Vars.Stmt)
    (operation : Machine.Operation) (state : State) : Option State :=
  match state.firstFireable sourceStatements operation with
  | none => none
  | some (statement, statementIndex) =>
      match operationOf statement with
      | none => none
      | some (_, operands, result) =>
          some { state with
            stack := result :: state.stack.drop operands.length
            firedStatementIndices := statementIndex :: state.firedStatementIndices }

def execute (sourceStatements : Array Vars.Stmt) (state : State) : Stack.Instr → Option State
  | .swap depth => do
      guard (1 ≤ depth ∧ depth ≤ 16)
      let stack ← exchange state.stack 0 depth
      some { state with stack }
  | .exchange firstDepth secondDepth => do
      guard (firstDepth ≠ secondDepth ∧ max firstDepth secondDepth ≤ 16)
      let stack ← exchange state.stack firstDepth secondDepth
      some { state with stack }
  | .dup depth => do
      guard (depth ≤ 15)
      let value ← state.stack[depth]?
      some { state with stack := value :: state.stack }
  | .pop => do
      let _ :: stack := state.stack | none
      some { state with stack }
  | .store slot => do
      let value :: stack := state.stack | none
      let none := state.slotValue? slot | none
      some { state with stack, slotBindings := state.slotBindings.push (slot, value) }
  | .load slot =>
      (state.slotValue? slot).map fun value => { state with stack := value :: state.stack }
  | .op operation => state.fireNextStatement sourceStatements operation
  | .flippedOp operation => do
      guard (operation.inputCount = 2)
      let stack ← exchange state.stack 0 1
      ({ state with stack } : State).fireNextStatement sourceStatements operation
  | .icall _ _ _ => none

def executeAll (sourceStatements : Array Vars.Stmt) (targetInstructions : Array Stack.Instr)
    (initialState : State) : Option State :=
  targetInstructions.foldlM (execute sourceStatements) initialState

end Sir.Lowering.Symbolic
