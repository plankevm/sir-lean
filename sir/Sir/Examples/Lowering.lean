import Sir.Lowering.Proofs.Paths
import Sir.Vars.Proofs.Determinism
import Sir.Vars.Proofs.Steps
import Sir.Theorems

namespace Sir.Lowering

private theorem functionCertificate_evaluation_equivalence
    (certificate : StackSchedule)
    (accepted : certificate.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn certificate.vars ctx ⟨0⟩ globals args trace finalGlobals outcome ↔
      Stack.EvalFn certificate.stack ctx
        ⟨0⟩ globals args trace finalGlobals outcome := by
  exact certificate.equiv accepted ctx ⟨0⟩ globals args trace finalGlobals outcome

def firstFireableExampleState : Symbolic.State :=
  Symbolic.State.initial #[.variable ⟨0⟩]

theorem firstFireable_skips_operation_mismatch :
    firstFireableExampleState.firstFireable #[
      .assign ⟨1⟩ (.constant 7),
      .assign ⟨2⟩ (.var ⟨0⟩)] .copy =
        some (.assign ⟨2⟩ (.var ⟨0⟩), 1) := by
  simp [Symbolic.State.firstFireable,
    Symbolic.State.fireable, Symbolic.operationOf,
    firstFireableExampleState, Symbolic.State.initial,
    Symbolic.State.available, Symbolic.State.slotFree,
    Symbolic.Value.identifier, Vars.Stmt.variablesRead, Vars.Expr.variablesRead]

def unavailableOperandExampleState : Symbolic.State where
  stack := [.variable ⟨0⟩]
  slotBindings := #[]
  entryVariables := []
  firedStatementIndices := []

theorem firstFireable_rejects_unavailable_operand :
    unavailableOperandExampleState.firstFireable #[
      .assign ⟨0⟩ (.constant 7),
      .assign ⟨1⟩ (.var ⟨0⟩)] .copy = none := by
  simp [Symbolic.State.firstFireable,
    Symbolic.State.fireable, Symbolic.operationOf,
    Symbolic.State.available,
    Symbolic.State.slotFree, unavailableOperandExampleState,
    Vars.Stmt.variablesRead, Vars.Expr.variablesRead]

def replayScheduledExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[]
    statements := #[
      .assign ⟨0⟩ (.constant 7),
      .assign ⟨1⟩ (.var ⟨0⟩),
      .assign ⟨2⟩ (.add ⟨0⟩ ⟨1⟩)]
    terminator := .halt
    outputs := #[]
    entryLayout := #[]
    exitLayout := #[] }
  stack := {
    instructions := #[
      .op (.constant 7),
      .dup 0,
      .op .copy,
      .swap 1,
      .op .add,
      .dup 0,
      .store 10,
      .pop,
      .load 10]
    terminator := .halt } }

theorem replayScheduledExample_accepted :
    replayScheduledExampleCertificate.check = .ok () := by decide +kernel

theorem replayScheduledExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn replayScheduledExampleCertificate.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn replayScheduledExampleCertificate.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence replayScheduledExampleCertificate
    replayScheduledExample_accepted ctx globals finalGlobals #[] trace outcome

def replayEntryExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[⟨0⟩]
    statements := #[.assign ⟨1⟩ (.var ⟨0⟩)]
    terminator := .halt
    outputs := #[]
    entryLayout := #[.variable ⟨0⟩]
    exitLayout := #[] }
  stack := {
    instructions := #[.op .copy]
    terminator := .halt } }

theorem replayEntryExample_accepted :
    replayEntryExampleCertificate.check = .ok () := by decide +kernel

theorem replayEntryExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (argument : Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn replayEntryExampleCertificate.vars ctx ⟨0⟩ globals #[argument] trace
        finalGlobals outcome ↔
      Stack.EvalFn replayEntryExampleCertificate.stack ctx
        ⟨0⟩ globals #[argument] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence replayEntryExampleCertificate
    replayEntryExample_accepted ctx globals finalGlobals #[argument] trace outcome

def exchangeExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[⟨0⟩, ⟨1⟩, ⟨2⟩]
    statements := #[]
    terminator := .halt
    outputs := #[]
    entryLayout := #[.variable ⟨0⟩, .variable ⟨1⟩, .variable ⟨2⟩]
    exitLayout := #[] }
  stack := {
    instructions := #[.exchange 1 2]
    terminator := .halt } }

theorem exchangeExample_accepted : exchangeExampleCertificate.check = .ok () := by decide +kernel

theorem exchangeExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (first second third : Word)
    (trace : Trace) (outcome : FunctionOutcome) :
    Vars.EvalFn exchangeExampleCertificate.vars ctx ⟨0⟩ globals #[first, second, third]
        trace finalGlobals outcome ↔
      Stack.EvalFn exchangeExampleCertificate.stack ctx ⟨0⟩
        globals #[first, second, third] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence exchangeExampleCertificate exchangeExample_accepted
    ctx globals finalGlobals #[first, second, third] trace outcome

def equalDepthExchangeExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[⟨0⟩, ⟨1⟩]
    statements := #[]
    terminator := .halt
    outputs := #[]
    entryLayout := #[.variable ⟨0⟩, .variable ⟨1⟩]
    exitLayout := #[] }
  stack := {
    instructions := #[.exchange 1 1]
    terminator := .halt } }

theorem equalDepthExchangeExample_rejected :
    equalDepthExchangeExampleCertificate.check =
      .error (.operandMismatch (.exchange 1 1)) := by decide +kernel

def flippedLessThanExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[⟨1⟩, ⟨0⟩]
    statements := #[.assign ⟨2⟩ (.lt ⟨0⟩ ⟨1⟩)]
    terminator := .halt
    outputs := #[]
    entryLayout := #[.variable ⟨1⟩, .variable ⟨0⟩]
    exitLayout := #[] }
  stack := {
    instructions := #[.flippedOp .lt]
    terminator := .halt } }

theorem flippedLessThanExample_accepted :
    flippedLessThanExampleCertificate.check = .ok () := by decide +kernel

theorem flippedLessThanExample_concrete_result
    (ctx : CallContext) (globals : Globals) (left right : Word) :
    Stack.sourceFetch
          ({ stack := [right, left], slots := fun _ => none } : Stack.Environment)
          .reversedPair = .ok #[left, right] ∧
      Machine.Operation.execute ctx .lt () globals #[left, right] =
        .ok (.next #[Evm.UInt256.lt left right] globals []) := by
  constructor
  · rfl
  · exact Machine.Operation.execute_lt_ok ctx left right globals

theorem flippedLessThanExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (left right : Word)
    (trace : Trace) (outcome : FunctionOutcome) :
    Vars.EvalFn flippedLessThanExampleCertificate.vars ctx ⟨0⟩ globals #[right, left]
        trace finalGlobals outcome ↔
      Stack.EvalFn flippedLessThanExampleCertificate.stack ctx
        ⟨0⟩ globals #[right, left] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence flippedLessThanExampleCertificate
    flippedLessThanExample_accepted ctx globals finalGlobals #[right, left] trace outcome

def straightLineExampleStatements : Array Vars.Stmt := #[
  .assign ⟨0⟩ (.constant 7),
  .assign ⟨1⟩ (.constant 7),
  .assign ⟨2⟩ (.add ⟨0⟩ ⟨1⟩),
  .assign ⟨3⟩ (.lt ⟨2⟩ ⟨0⟩)]

def straightLineExampleCertificate : StackSchedule :=
  (spillAll straightLineExampleStatements).toOption.get (by decide +kernel)

theorem straightLineExample_lowered :
    spillAll straightLineExampleStatements = .ok straightLineExampleCertificate := by
  decide +kernel

theorem straightLineExample_accepted : straightLineExampleCertificate.check = .ok () := by
  decide +kernel

theorem straightLineExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn straightLineExampleCertificate.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn straightLineExampleCertificate.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence straightLineExampleCertificate
    straightLineExample_accepted ctx globals finalGlobals #[] trace outcome

def twoBlockJumpExampleCertificate : StackSchedule where
  blocks := #[
    { vars := {
        statements := #[.assign ⟨0⟩ (.constant 7)]
        inputs := #[]
        terminator := .jump ⟨1⟩
        outputs := #[⟨0⟩]
        entryLayout := #[]
        exitLayout := #[.variable ⟨0⟩] }
      stack := {
        instructions := #[.op (.constant 7)]
        terminator := .jump ⟨1⟩ } },
    { vars := {
        statements := #[.assign ⟨1⟩ (.var ⟨0⟩)]
        inputs := #[⟨0⟩]
        terminator := .halt
        outputs := #[]
        entryLayout := #[.variable ⟨0⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[.op .copy]
        terminator := .halt } }]
  entry := ⟨0⟩

theorem twoBlockJumpExample_accepted :
    twoBlockJumpExampleCertificate.check = .ok () := by decide +kernel

theorem twoBlockJumpExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn twoBlockJumpExampleCertificate.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn twoBlockJumpExampleCertificate.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence twoBlockJumpExampleCertificate
    twoBlockJumpExample_accepted ctx globals finalGlobals #[] trace outcome

def renamedBoundaryExampleCertificate : StackSchedule where
  blocks := #[
    { vars := {
        statements := #[
        .assign ⟨1⟩ (.constant 7),
        .assign ⟨2⟩ (.constant 8)]
        inputs := #[]
        terminator := .jump ⟨1⟩
        outputs := #[⟨2⟩, ⟨1⟩]
        entryLayout := #[]
        exitLayout := #[.variable ⟨2⟩, .variable ⟨1⟩] }
      stack := {
        instructions := #[
        .op (.constant 7),
        .op (.constant 8)]
        terminator := .jump ⟨1⟩ } },
    { vars := {
        statements := #[.assign ⟨5⟩ (.add ⟨3⟩ ⟨4⟩)]
        inputs := #[⟨3⟩, ⟨4⟩]
        terminator := .halt
        outputs := #[]
        entryLayout := #[.variable ⟨3⟩, .variable ⟨4⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[.op .add]
        terminator := .halt } }]
  entry := ⟨0⟩

theorem renamedBoundaryExample_accepted :
    renamedBoundaryExampleCertificate.check = .ok () := by decide +kernel

theorem renamedBoundaryExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn renamedBoundaryExampleCertificate.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn renamedBoundaryExampleCertificate.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence renamedBoundaryExampleCertificate
    renamedBoundaryExample_accepted ctx globals finalGlobals #[] trace outcome

def mismatchedBoundaryArityExampleCertificate : StackSchedule where
  blocks := #[
    { vars := {
        statements := #[]
        inputs := #[⟨0⟩]
        terminator := .jump ⟨1⟩
        outputs := #[⟨0⟩]
        entryLayout := #[.variable ⟨0⟩]
        exitLayout := #[.variable ⟨0⟩] }
      stack := {
        instructions := #[]
        terminator := .jump ⟨1⟩ } },
    { vars := {
        statements := #[]
        inputs := #[]
        terminator := .halt
        outputs := #[]
        entryLayout := #[]
        exitLayout := #[] }
      stack := {
        instructions := #[]
        terminator := .halt } }]
  entry := ⟨0⟩

theorem mismatchedBoundaryArityExample_rejected :
    mismatchedBoundaryArityExampleCertificate.check =
      .error (.boundaryArityMismatch (⟨0⟩, ⟨1⟩) 0 1) := by decide +kernel

def branchLoopExampleCertificate : StackSchedule where
  blocks := #[
    { vars := {
        statements := #[]
        inputs := #[⟨0⟩]
        terminator := .branch ⟨0⟩ ⟨0⟩ ⟨1⟩
        outputs := #[⟨0⟩]
        entryLayout := #[.variable ⟨0⟩]
        exitLayout := #[.variable ⟨0⟩] }
      stack := {
        instructions := #[.dup 0]
        terminator := .branch ⟨0⟩ ⟨1⟩ } },
    { vars := {
        statements := #[]
        inputs := #[⟨0⟩]
        terminator := .halt
        outputs := #[]
        entryLayout := #[.variable ⟨0⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[]
        terminator := .halt } }]
  entry := ⟨0⟩

theorem branchLoopExample_accepted :
    branchLoopExampleCertificate.check = .ok () := by decide +kernel

theorem branchLoopExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (condition : Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn branchLoopExampleCertificate.vars ctx ⟨0⟩ globals #[condition] trace
        finalGlobals outcome ↔
      Stack.EvalFn branchLoopExampleCertificate.stack ctx
        ⟨0⟩ globals #[condition] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence branchLoopExampleCertificate
    branchLoopExample_accepted ctx globals finalGlobals #[condition] trace outcome

def renamedBackEdgeLoopExampleCertificate : StackSchedule where
  blocks := #[
    { vars := {
        statements := #[]
        inputs := #[⟨2⟩, ⟨3⟩]
        terminator := .branch ⟨2⟩ ⟨1⟩ ⟨2⟩
        outputs := #[⟨2⟩, ⟨3⟩]
        entryLayout := #[.variable ⟨2⟩, .variable ⟨3⟩]
        exitLayout := #[.variable ⟨2⟩, .variable ⟨3⟩] }
      stack := {
        instructions := #[.dup 0]
        terminator := .branch ⟨1⟩ ⟨2⟩ } },
    { vars := {
        statements := #[
        .assign ⟨6⟩ (.var ⟨4⟩),
        .assign ⟨8⟩ (.var ⟨5⟩)]
        inputs := #[⟨4⟩, ⟨5⟩]
        terminator := .jump ⟨0⟩
        outputs := #[⟨8⟩, ⟨6⟩]
        entryLayout := #[.variable ⟨4⟩, .variable ⟨5⟩]
        exitLayout := #[.variable ⟨8⟩, .variable ⟨6⟩] }
      stack := {
        instructions := #[.op .copy, .swap 1, .op .copy]
        terminator := .jump ⟨0⟩ } },
    { vars := {
        statements := #[]
        inputs := #[⟨10⟩, ⟨11⟩]
        terminator := .halt
        outputs := #[]
        entryLayout := #[.variable ⟨10⟩, .variable ⟨11⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[]
        terminator := .halt } }]
  entry := ⟨0⟩

theorem renamedBackEdgeLoopExample_accepted :
    renamedBackEdgeLoopExampleCertificate.check = .ok () := by decide +kernel

theorem renamedBackEdgeLoopExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (first second : Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn renamedBackEdgeLoopExampleCertificate.vars ctx ⟨0⟩ globals
        #[first, second] trace finalGlobals outcome ↔
      Stack.EvalFn renamedBackEdgeLoopExampleCertificate.stack ctx
        ⟨0⟩ globals #[first, second] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence renamedBackEdgeLoopExampleCertificate
    renamedBackEdgeLoopExample_accepted ctx globals finalGlobals #[first, second] trace outcome

def reorderedIndependentExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[⟨2⟩]
    statements := #[
      .assign ⟨0⟩ (.constant 7),
      .assign ⟨1⟩ (.var ⟨2⟩)]
    terminator := .halt
    outputs := #[]
    entryLayout := #[.variable ⟨2⟩]
    exitLayout := #[] }
  stack := {
    instructions := #[
      .op .copy,
      .op (.constant 7)]
    terminator := .halt } }

theorem reorderedIndependentExample_accepted :
    reorderedIndependentExampleCertificate.check = .ok () := by decide +kernel

theorem reorderedIndependentExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (argument : Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn reorderedIndependentExampleCertificate.vars ctx ⟨0⟩ globals #[argument]
        trace finalGlobals outcome ↔
      Stack.EvalFn reorderedIndependentExampleCertificate.stack ctx ⟨0⟩ globals
        #[argument] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence reorderedIndependentExampleCertificate
    reorderedIndependentExample_accepted ctx globals finalGlobals #[argument] trace outcome

def useBeforeDefinitionExampleCertificate : StackSchedule := StackSchedule.ofBlock {
  vars := {
    inputs := #[]
    statements := #[
      .assign ⟨1⟩ (.var ⟨0⟩),
      .assign ⟨0⟩ (.constant 7)]
    terminator := .halt
    outputs := #[]
    entryLayout := #[]
    exitLayout := #[] }
  stack := {
    instructions := #[
      .op (.constant 7),
      .op .copy]
    terminator := .halt } }

theorem useBeforeDefinitionExample_rejected :
    useBeforeDefinitionExampleCertificate.check =
      .error (.useBeforeDefinition (.assign ⟨1⟩ (.var ⟨0⟩)) ⟨0⟩) := by decide +kernel

def reorderedLoopExampleCertificate : StackSchedule where
  blocks := #[
    { vars := {
        statements := #[
        .assign ⟨1⟩ (.constant 7),
        .assign ⟨2⟩ (.var ⟨0⟩)]
        inputs := #[⟨0⟩]
        terminator := .branch ⟨0⟩ ⟨0⟩ ⟨1⟩
        outputs := #[⟨0⟩]
        entryLayout := #[.variable ⟨0⟩]
        exitLayout := #[.variable ⟨0⟩] }
      stack := {
        instructions := #[
        .dup 0,
        .op .copy,
        .op (.constant 7),
        .pop,
        .pop,
        .dup 0]
        terminator := .branch ⟨0⟩ ⟨1⟩ } },
    { vars := {
        statements := #[]
        inputs := #[⟨0⟩]
        terminator := .halt
        outputs := #[]
        entryLayout := #[.variable ⟨0⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[]
        terminator := .halt } }]
  entry := ⟨0⟩

theorem reorderedLoopExample_accepted :
    reorderedLoopExampleCertificate.check = .ok () := by decide +kernel

theorem reorderedLoopExample_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (condition : Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn reorderedLoopExampleCertificate.vars ctx ⟨0⟩ globals #[condition] trace
        finalGlobals outcome ↔
      Stack.EvalFn reorderedLoopExampleCertificate.stack ctx
        ⟨0⟩ globals #[condition] trace finalGlobals outcome := by
  exact functionCertificate_evaluation_equivalence reorderedLoopExampleCertificate
    reorderedLoopExample_accepted ctx globals finalGlobals #[condition] trace outcome

end Sir.Lowering
