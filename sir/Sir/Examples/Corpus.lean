import Sir.Theorems

namespace Sir.Lowering

private theorem schedule_evaluation_equivalence
    (schedule : StackSchedule)
    (accepted : schedule.check = .ok ())
    (ctx : CallContext) (globals finalGlobals : Globals) (args : Array Word) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn schedule.vars ctx ⟨0⟩ globals args trace finalGlobals outcome ↔
      Stack.EvalFn schedule.stack ctx
        ⟨0⟩ globals args trace finalGlobals outcome := by
  exact schedule.equiv accepted ctx ⟨0⟩ globals args trace finalGlobals outcome

def straightLineCorpusSchedule : StackSchedule where
  entry := {
    vars := {
      statements := #[
        .assign ⟨0⟩ (.constant 1),
        .assign ⟨1⟩ (.constant 2),
        .assign ⟨2⟩ (.add ⟨0⟩ ⟨1⟩)]
      inputs := #[]
      terminator := .halt
      outputs := #[]
      entryLayout := #[]
      exitLayout := #[] }
    stack := {
      instructions := #[
        .op (.constant 1),
        .op (.constant 2),
        .swap 1,
        .op .add]
      terminator := .halt } }
  rest := #[]

theorem straightLineCorpus_accepted :
    straightLineCorpusSchedule.check = .ok () := by decide +kernel

theorem straightLineCorpus_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn straightLineCorpusSchedule.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn straightLineCorpusSchedule.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact schedule_evaluation_equivalence straightLineCorpusSchedule
    straightLineCorpus_accepted ctx globals finalGlobals #[] trace outcome

def diamondCorpusSchedule : StackSchedule where
  entry :=
    { vars := {
        statements := #[
        .assign ⟨0⟩ (.constant 0),
        .assign ⟨1⟩ (.constant 7),
        .assign ⟨2⟩ (.lt ⟨0⟩ ⟨1⟩)]
        inputs := #[]
        terminator := .jump ⟨1⟩
        outputs := #[⟨2⟩, ⟨1⟩]
        entryLayout := #[]
        exitLayout := #[.variable ⟨2⟩, .variable ⟨1⟩] }
      stack := {
        instructions := #[
        .op (.constant 0),
        .op (.constant 7),
        .dup 0,
        .swap 2,
        .op .lt]
        terminator := .jump ⟨1⟩ } }
  rest := #[
    { vars := {
        statements := #[]
        inputs := #[⟨3⟩, ⟨4⟩]
        terminator := .branch ⟨3⟩ ⟨2⟩ ⟨3⟩
        outputs := #[⟨4⟩]
        entryLayout := #[.variable ⟨3⟩, .variable ⟨4⟩]
        exitLayout := #[.variable ⟨4⟩] }
      stack := {
        instructions := #[]
        terminator := .branch ⟨2⟩ ⟨3⟩ } },
    { vars := {
        statements := #[
        .assign ⟨6⟩ (.constant 1),
        .assign ⟨7⟩ (.add ⟨5⟩ ⟨6⟩)]
        inputs := #[⟨5⟩]
        terminator := .jump ⟨4⟩
        outputs := #[]
        entryLayout := #[.variable ⟨5⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[
        .op (.constant 1),
        .swap 1,
        .op .add,
        .pop]
        terminator := .jump ⟨4⟩ } },
    { vars := {
        statements := #[
        .assign ⟨9⟩ (.constant 2),
        .assign ⟨10⟩ (.add ⟨8⟩ ⟨9⟩)]
        inputs := #[⟨8⟩]
        terminator := .jump ⟨4⟩
        outputs := #[]
        entryLayout := #[.variable ⟨8⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[
        .op (.constant 2),
        .swap 1,
        .op .add,
        .pop]
        terminator := .jump ⟨4⟩ } },
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

theorem diamondCorpus_accepted :
    diamondCorpusSchedule.check = .ok () := by decide +kernel

theorem diamondCorpus_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn diamondCorpusSchedule.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn diamondCorpusSchedule.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact schedule_evaluation_equivalence diamondCorpusSchedule
    diamondCorpus_accepted ctx globals finalGlobals #[] trace outcome

def loopCorpusSchedule : StackSchedule where
  entry :=
    { vars := {
        statements := #[
        .assign ⟨0⟩ (.constant 0),
        .assign ⟨1⟩ (.constant 3)]
        inputs := #[]
        terminator := .jump ⟨1⟩
        outputs := #[⟨0⟩, ⟨1⟩]
        entryLayout := #[]
        exitLayout := #[.variable ⟨0⟩, .variable ⟨1⟩] }
      stack := {
        instructions := #[
        .op (.constant 0),
        .op (.constant 3),
        .swap 1]
        terminator := .jump ⟨1⟩ } }
  rest := #[
    { vars := {
        statements := #[.assign ⟨4⟩ (.lt ⟨2⟩ ⟨3⟩)]
        inputs := #[⟨2⟩, ⟨3⟩]
        terminator := .branch ⟨4⟩ ⟨2⟩ ⟨3⟩
        outputs := #[⟨2⟩, ⟨3⟩]
        entryLayout := #[.variable ⟨2⟩, .variable ⟨3⟩]
        exitLayout := #[.variable ⟨2⟩, .variable ⟨3⟩] }
      stack := {
        instructions := #[
        .dup 1,
        .dup 1,
        .op .lt]
        terminator := .branch ⟨2⟩ ⟨3⟩ } },
    { vars := {
        statements := #[
        .assign ⟨7⟩ (.constant 1),
        .assign ⟨8⟩ (.add ⟨5⟩ ⟨7⟩)]
        inputs := #[⟨5⟩, ⟨6⟩]
        terminator := .jump ⟨1⟩
        outputs := #[⟨8⟩, ⟨6⟩]
        entryLayout := #[.variable ⟨5⟩, .variable ⟨6⟩]
        exitLayout := #[.variable ⟨8⟩, .variable ⟨6⟩] }
      stack := {
        instructions := #[
        .op (.constant 1),
        .swap 1,
        .op .add]
        terminator := .jump ⟨1⟩ } },
    { vars := {
        statements := #[]
        inputs := #[⟨9⟩, ⟨10⟩]
        terminator := .halt
        outputs := #[]
        entryLayout := #[.variable ⟨9⟩, .variable ⟨10⟩]
        exitLayout := #[] }
      stack := {
        instructions := #[]
        terminator := .halt } }]

theorem loopCorpus_accepted : loopCorpusSchedule.check = .ok () := by decide +kernel

theorem loopCorpus_evaluation_equivalence
    (ctx : CallContext) (globals finalGlobals : Globals) (trace : Trace)
    (outcome : FunctionOutcome) :
    Vars.EvalFn loopCorpusSchedule.vars ctx ⟨0⟩ globals #[] trace
        finalGlobals outcome ↔
      Stack.EvalFn loopCorpusSchedule.stack ctx
        ⟨0⟩ globals #[] trace finalGlobals outcome := by
  exact schedule_evaluation_equivalence loopCorpusSchedule
    loopCorpus_accepted ctx globals finalGlobals #[] trace outcome

end Sir.Lowering
