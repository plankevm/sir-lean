import Sir.Stack.Spec

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
  exact SmallStep.pure rfl (by rfl)

theorem witness_step_constant₃ (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [2] (.statement 1)) []
      (witnessState globals [3, 2] (.statement 2)) := by
  exact SmallStep.pure rfl (by rfl)

theorem witness_step_add (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [3, 2] (.statement 2)) []
      (witnessState globals [witnessSum] .terminator) := by
  exact SmallStep.pure rfl (by rfl)

theorem witness_step_halt (ctx : CallContext) (globals : Globals) :
    SmallStep witnessProgram ctx
      (witnessState globals [witnessSum] .terminator) []
      { globals, environment := { Environment.empty with stack := [witnessSum] },
        control := .halted } :=
  SmallStep.control rfl rfl

theorem witness_runs (ctx : CallContext) (globals : Globals) :
    Steps witnessProgram ctx
      (witnessState globals [] (.statement 0)) []
      { globals, environment := { Environment.empty with stack := [witnessSum] },
        control := .halted } :=
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
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted }
        suffix
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    (∃ suffix,
      Steps witnessProgram ctx
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted }
        suffix
        { globals, environment := { Environment.empty with stack := [witnessSum] },
          control := .halted } ∧ [] ++ suffix = []) ∨
    Trace.QueryDivergence [] [] :=
  .inl ⟨[], .refl, rfl⟩

end Sir.Stack
