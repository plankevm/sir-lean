import Sir.Stack.Theorems

namespace Sir.Stack

open Sir

def witnessEntry : FunctionId := ⟨0⟩
def witnessBlock : BlockId := ⟨0⟩
def witnessSum : Word := Evm.UInt256.add 3 2

def witnessProgram : Program :=
  { init :=
      { entry :=
          { inputCount := 0
            instructions := #[.push 2, .push 3, .op .add]
            terminator := .halt
            outputCount := 1 }
        rest := #[] }
    main := none
    rest := #[] }

def witnessState (globals : Globals) (stack : List Word) (position : BlockPosition) :
    State :=
  { globals
    environment := { Environment.empty with stack }
    control := .running { fn := witnessEntry, block := witnessBlock, position } }

theorem witness_memOracleFree : witnessProgram.MemOracleFree := by
  intro instruction hinstruction
  rcases hinstruction with ⟨function, hfunction, block, hblock, hinstruction⟩
  simp [Program.functions, witnessProgram] at hfunction
  subst function
  simp [Function.blocks] at hblock
  subst block
  simp at hinstruction
  rcases hinstruction with rfl | rfl | rfl
  all_goals simp [Instr.isMemOracle]

theorem witness_step_constant₂ (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [] (.statement 0)) []
      (witnessState globals [2] (.statement 1)) := by
  exact SmallStep.evaluate rfl (by rfl)

theorem witness_step_constant₃ (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [2] (.statement 1)) []
      (witnessState globals [3, 2] (.statement 2)) := by
  exact SmallStep.evaluate rfl (by rfl)

theorem witness_step_add (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [3, 2] (.statement 2)) []
      (witnessState globals [witnessSum] .terminator) := by
  exact SmallStep.evaluate rfl (by rfl)

theorem witness_step_halt (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [witnessSum] .terminator) []
      (State.of globals { Environment.empty with stack := [witnessSum] } .halted) :=
  SmallStep.control rfl rfl

theorem witness_runs (ctx : CallContext) (globals : Globals) :
    Steps witnessProgram ctx
      (witnessState globals [] (.statement 0)) []
      (State.of globals { Environment.empty with stack := [witnessSum] } .halted) :=
  .tail
    (.tail
      (.tail
        (.tail .refl (witness_step_constant₂ ctx globals))
        (witness_step_constant₃ ctx globals))
      (witness_step_add ctx globals))
    (witness_step_halt ctx globals)

theorem witness_confluence (ctx : CallContext) (globals : Globals) :
    (∃ suffix,
      Steps witnessProgram ctx
        (State.of globals { Environment.empty with stack := [witnessSum] } .halted)
        suffix
        (State.of globals { Environment.empty with stack := [witnessSum] } .halted) ∧
          [] ++ suffix = []) ∨
    (∃ suffix,
      Steps witnessProgram ctx
        (State.of globals { Environment.empty with stack := [witnessSum] } .halted)
        suffix
        (State.of globals { Environment.empty with stack := [witnessSum] } .halted) ∧
          [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  .inl ⟨[], .refl, rfl⟩

theorem witness_wellFormed : witnessProgram.WellFormed where
  icallArity := by
    intro callee argumentCount resultCount hinstr
    simp [Program.HasInstr, Program.functions, Function.HasInstr, Function.blocks,
      witnessProgram] at hinstr
  iretArity := by
    intro function hfunction block hblock hiret
    simp [Program.functions, witnessProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    subst block
    simp at hiret
  acyclicCalls := by
    have hedge : ∀ caller callee, ¬ witnessProgram.callEdge caller callee := by
      rintro ⟨caller⟩ callee ⟨argumentCount, resultCount, function, hfunction, hinstr⟩
      match caller with
      | 0 =>
          simp [Program.function?, Program.functions, witnessProgram] at hfunction
          subst function
          simp [Function.HasInstr, Function.blocks] at hinstr
      | n + 1 => simp [Program.function?, Program.functions, witnessProgram] at hfunction
    intro f hcycle
    cases hcycle with
    | single hedge' => exact hedge _ _ hedge'
    | tail _ hedge' => exact hedge _ _ hedge'
  entryArity := ⟨⟨rfl, rfl⟩, by simp [witnessProgram]⟩
  validJumpTargets := by
    intro function hfunction block hblock target htarget
    simp [Program.functions, witnessProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    subst block
    simp [Terminator.jumpTargets] at htarget
  exchangeDepthsDistinct := by
    intro firstDepth secondDepth hinstr
    simp [Program.HasInstr, Program.functions, Function.HasInstr, Function.blocks,
      witnessProgram] at hinstr
  stackHeightsFit := by
    intro function hfunction block hblock
    simp [Program.functions, witnessProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    subst block
    refine ⟨?_, trivial⟩
    intro index instruction hindex
    match index with
    | 0 | 1 | 2 => simp at hindex; subst hindex; decide
    | n + 3 => simp at hindex
  slotsStoredBeforeLoad := by
    intro function hfunction block hblock
    simp [Program.functions, witnessProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    subst block
    intro index instruction hindex
    match index with
    | 0 | 1 | 2 => simp at hindex; subst hindex; decide
    | n + 3 => simp at hindex

theorem witness_ready (ctx : CallContext) (globals : Globals) :
    witnessProgram.ReadyState ctx (witnessState globals [] (.statement 0)) := by
  have hat : witnessProgram.instructionAt (witnessState globals [] (.statement 0)).control =
      some (.running { fn := witnessEntry, block := witnessBlock, position := .statement 1 },
        .push 2) := rfl
  have hop : ∀ next operation,
      ¬ witnessProgram.AtInstr (witnessState globals [] (.statement 0)) next (.op operation) := by
    intro next operation hinstr
    simp [hat] at hinstr
  exact ⟨⟨witnessEntry, globals, #[], [], _, rfl, .refl⟩,
    .inl ⟨_, _, hat, by simp⟩,
    .inr ⟨fun next _ hinstr => absurd hinstr (hop next .malloc),
      fun next _ hinstr => absurd hinstr (hop next .mallocUninit)⟩,
    fun next _ _ hinstr => absurd hinstr (hop next .mstore32)⟩

theorem witness_progress (ctx : CallContext) (globals : Globals) :
    ∃ trace state',
      SmallStep witnessProgram ctx (witnessState globals [] (.statement 0)) trace state' :=
  witness_wellFormed.progress (witness_ready ctx globals)

def slottedSlot : Nat := 0
def slottedTarget : BlockId := ⟨1⟩

def slottedProgram : Program :=
  { init :=
      { entry :=
          { inputCount := 0
            instructions :=
              #[.push 5, .store slottedSlot, .push 2, .push 3, .load slottedSlot,
                .exchange 0 2, .op .add]
            terminator := .jump slottedTarget
            outputCount := 2 }
        rest :=
          #[{ inputCount := 2
              instructions := #[.op .add]
              terminator := .halt
              outputCount := 1 }] }
    main := none
    rest := #[] }

theorem slotted_wellFormed : slottedProgram.WellFormed where
  icallArity := by
    intro callee argumentCount resultCount hinstr
    simp [Program.HasInstr, Program.functions, Function.HasInstr, Function.blocks,
      slottedProgram] at hinstr
  iretArity := by
    intro function hfunction block hblock hiret
    simp [Program.functions, slottedProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    rcases hblock with rfl | rfl <;> simp at hiret
  acyclicCalls := by
    have hedge : ∀ caller callee, ¬ slottedProgram.callEdge caller callee := by
      rintro ⟨caller⟩ callee ⟨argumentCount, resultCount, function, hfunction, hinstr⟩
      match caller with
      | 0 =>
          simp [Program.function?, Program.functions, slottedProgram] at hfunction
          subst function
          simp [Function.HasInstr, Function.blocks] at hinstr
      | n + 1 => simp [Program.function?, Program.functions, slottedProgram] at hfunction
    intro f hcycle
    cases hcycle with
    | single hedge' => exact hedge _ _ hedge'
    | tail _ hedge' => exact hedge _ _ hedge'
  entryArity := ⟨⟨rfl, rfl⟩, by simp [slottedProgram]⟩
  validJumpTargets := by
    intro function hfunction block hblock target htarget
    simp [Program.functions, slottedProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    rcases hblock with rfl | rfl
    · simp [Terminator.jumpTargets] at htarget
      subst htarget
      exact ⟨_, rfl, rfl⟩
    · simp [Terminator.jumpTargets] at htarget
  exchangeDepthsDistinct := by
    intro firstDepth secondDepth hinstr
    simp [Program.HasInstr, Program.functions, Function.HasInstr, Function.blocks,
      slottedProgram] at hinstr
    omega
  stackHeightsFit := by
    intro function hfunction block hblock
    simp [Program.functions, slottedProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    rcases hblock with rfl | rfl
    · refine ⟨?_, rfl⟩
      intro index instruction hindex
      match index with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => simp at hindex; subst hindex; decide
      | n + 7 => simp at hindex
    · refine ⟨?_, trivial⟩
      intro index instruction hindex
      match index with
      | 0 => simp at hindex; subst hindex; decide
      | n + 1 => simp at hindex
  slotsStoredBeforeLoad := by
    intro function hfunction block hblock
    simp [Program.functions, slottedProgram] at hfunction
    subst function
    simp [Function.blocks] at hblock
    rcases hblock with rfl | rfl
    · intro index instruction hindex
      match index with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => simp at hindex; subst hindex; decide
      | n + 7 => simp at hindex
    · intro index instruction hindex
      match index with
      | 0 => simp at hindex; subst hindex; decide
      | n + 1 => simp at hindex

end Sir.Stack
