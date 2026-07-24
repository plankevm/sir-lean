import Sir.Spec.State

namespace Sir

/-- `callEdge callee caller`: some block of `caller` icalls `callee` (note the argument order). -/
def Program.callEdge (p : Program) (callee caller : FunctionId) : Prop :=
  ∃ args dests fn, p.function? caller = some fn ∧ fn.HasStmt (.icall callee args dests)

/-- Lists expression operands so well-formedness can require a preceding local definition. -/
def Expr.variablesRead : Expr → List VarId
  | .constant _ => []
  | .var identifier => [identifier]
  | .add lhs rhs | .lt lhs rhs => [lhs, rhs]
  | .sload key => [key]

/-- Lists statement operands so cursor-indexed well-formedness covers every local lookup. -/
def Stmt.variablesRead : Stmt → List VarId
  | .assign _ value => value.variablesRead
  | .sstore key value => [key, value]
  | .gas _ => []
  | .call callData => [callData.callee, callData.gas]
  | .mallocUninit _ size => [size]
  | .mstore32 offset value => [offset, value]
  | .mload32 _ offset => [offset]
  | .icall _ args _ => args.toList

/-- Lists statement results so later uses can be checked against the definitions accumulated so far. -/
def Stmt.variablesDefined : Stmt → List VarId
  | .assign result _ | .gas result | .mallocUninit result _
  | .mload32 result _ => [result]
  | .call callData => [callData.result]
  | .icall _ _ dests => dests.toList
  | .sstore _ _ | .mstore32 _ _ => []

/-- Lists terminator operands so readiness of terminal control is implied by static definitions. -/
def Terminator.variablesRead : Terminator → List VarId
  | .branch condition _ _ => [condition]
  | .halt | .jump _ | .iret => []

/-- Lists outgoing CFG references so well-formedness can validate every possible transfer. -/
def Terminator.jumpTargets : Terminator → List BlockId
  | .jump target => [target]
  | .branch _ thenTarget elseTarget => [thenTarget, elseTarget]
  | .halt | .iret => []

/-- Tracks the variables available before a statement so static use checks align with the execution cursor. -/
def BasicBlock.variablesDefinedBefore (block : BasicBlock) : Nat → List VarId
  | 0 => block.inputs.toList
  | index + 1 =>
      match block.statements[index]? with
      | some statement =>
          block.variablesDefinedBefore index ++ statement.variablesDefined
      | none => block.variablesDefinedBefore index

/-- Ensures every local lookup is preceded by a parameter or statement result that supplies it. -/
def BasicBlock.VariablesDefinedBeforeUse (block : BasicBlock) : Prop :=
  (∀ index statement, block.statements[index]? = some statement →
    ∀ identifier ∈ statement.variablesRead,
      identifier ∈ block.variablesDefinedBefore index) ∧
  ∀ identifier ∈ block.terminator.variablesRead ++ block.outputs.toList,
    identifier ∈ block.variablesDefinedBefore block.statements.size

structure Program.WellFormed (p : Program) : Prop where
  /-- Consumed by the icall bind lemmas; excluding `none` targets mirrors the compiler's returning-call invariant. -/
  icallArity :
    ∀ callee args dests, p.HasStmt (.icall callee args dests) →
      p.FunctionInputOutputArity args.size (some dests.size) callee
  /-- Consumed by `Program.WellFormed.evalFn_arity`; the non-returning case mirrors the compiler invariant. -/
  iretArity :
    ∀ f fn, p.function? f = some fn →
      (∀ n, fn.outputs = some n →
        ∀ block ∈ fn.blocks, block.terminator = .iret → block.outputs.size = n) ∧
      (fn.outputs = none → ∀ block ∈ fn.blocks, block.terminator ≠ .iret)
  /-- An invariant mirrored from the Legalizer's rejection of recursive calls, reserved for the lowering proof. -/
  acyclicCalls : ∀ f, ¬ Relation.TransGen p.callEdge f f
  /-- Consumed by `Program.WellFormed.evalFn_entry_not_returned`; entries follow the compiler's non-returning ABI. -/
  entryArity : p.AtEntries (p.FunctionInputOutputArity 0 none)
  /-- Consumed by `Program.WellFormed.terminatorReady_of_localsCoverCursor`; every CFG transfer resolves with matching arity. -/
  validJumpTargets :
    ∀ f fn, p.function? f = some fn →
      ∀ block ∈ fn.blocks, ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, fn.block? target = some targetBlock ∧
          targetBlock.inputs.size = block.outputs.size
  /-- Consumed by `Program.WellFormed.localsCoverCursor_step`; every lookup is dominated by a local definition. -/
  variablesDefinedBeforeUse :
    ∀ f fn, p.function? f = some fn →
      ∀ block ∈ fn.blocks, block.VariablesDefinedBeforeUse

def Locals.Defined (locals : Locals) (var : VarId) : Prop :=
  ∃ w, locals.lookup var = .ok w

def Locals.ExprReady (locals : Locals) : Expr → Prop
  | .constant _ => True
  | .var v => locals.Defined v
  | .add a b | .lt a b => locals.Defined a ∧ locals.Defined b
  | .sload k => locals.Defined k

def MachineState.StmtReady (s : MachineState) : Stmt → Prop
  | .assign _ e => s.locals.ExprReady e
  | .sstore key value => s.locals.Defined key ∧ s.locals.Defined value
  | .gas _ => True
  | .call c => s.locals.Defined c.callee ∧ s.locals.Defined c.gas
  | .mallocUninit _ size =>
      ∃ w alloc, s.locals.lookup size = .ok w ∧
        s.globals.memory.IsValidNewAlloc alloc ∧ alloc.size = w.toNat
  | .mstore32 offset value => s.locals.Defined offset ∧ s.locals.Defined value
  | .mload32 _ offset => s.locals.Defined offset
  | .icall _ _ _ => False

def Program.JumpReady (program : Program) (fn : FunctionId) (s : MachineState)
    (src : BasicBlock) (target : BlockId) : Prop :=
  (∃ vs, src.outputs.mapM (s.locals.lookup ·) = .ok vs) ∧
    ∃ targetBlock,
      program.block? { fn := fn, block := target, position := .terminator } = some targetBlock ∧
      targetBlock.inputs.size = src.outputs.size

def Program.TerminatorReady (program : Program) (fn : FunctionId) (s : MachineState)
    (src : BasicBlock) : Prop :=
  match src.terminator with
  | .halt => True
  | .jump target => program.JumpReady fn s src target
  | .branch condition thenTarget elseTarget =>
      ∃ w, s.locals.lookup condition = .ok w ∧
        program.JumpReady fn s src (if w = 0 then elseTarget else thenTarget)
  | .iret => ∃ rs, src.outputs.mapM (s.locals.lookup ·) = .ok rs
end Sir
