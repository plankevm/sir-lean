import Sir.Vars.Spec.Normalize

namespace Sir.Vars.Proofs

@[simp] theorem Expr.renameVariables_id (value : Expr) :
    value.renameVariables id = value := by
  cases value <;> rfl

@[simp] theorem Expr.renameVariables_compose (outer inner : VarId → VarId) (value : Expr) :
    (value.renameVariables inner).renameVariables outer =
      value.renameVariables (outer ∘ inner) := by
  cases value <;> rfl

@[simp] theorem Stmt.renameVariables_id (statement : Stmt) :
    statement.renameVariables id = statement := by
  cases statement <;> simp [Stmt.renameVariables]

@[simp] theorem Stmt.renameVariables_compose (outer inner : VarId → VarId)
    (statement : Stmt) :
    (statement.renameVariables inner).renameVariables outer =
      statement.renameVariables (outer ∘ inner) := by
  cases statement <;> simp [Stmt.renameVariables, Function.comp_def]

@[simp] theorem Terminator.renameVariables_id (terminator : Terminator) :
    terminator.renameVariables id = terminator := by
  cases terminator <;> rfl

@[simp] theorem Terminator.renameVariables_compose (outer inner : VarId → VarId)
    (terminator : Terminator) :
    (terminator.renameVariables inner).renameVariables outer =
      terminator.renameVariables (outer ∘ inner) := by
  cases terminator <;> rfl

@[simp] theorem Block.renameVariables_id (block : Block) :
    block.renameVariables id = block := by
  have hstatement : Stmt.renameVariables id = id := funext Stmt.renameVariables_id
  cases block
  simp [Block.renameVariables, hstatement]

@[simp] theorem Block.renameVariables_compose (outer inner : VarId → VarId)
    (block : Block) :
    (block.renameVariables inner).renameVariables outer =
      block.renameVariables (outer ∘ inner) := by
  cases block
  simp [Block.renameVariables, Function.comp_def]

@[simp] theorem Function.renameVariables_id (function : Function) :
    function.renameVariables id = function := by
  have hblock : Block.renameVariables id = id := funext Block.renameVariables_id
  cases function
  simp [Function.renameVariables, hblock]

@[simp] theorem Function.renameVariables_compose (outer inner : VarId → VarId)
    (function : Function) :
    (function.renameVariables inner).renameVariables outer =
      function.renameVariables (outer ∘ inner) := by
  cases function
  simp [Function.renameVariables, Function.comp_def]

@[simp] theorem Function.blocks_renameVariables (rename : VarId → VarId)
    (function : Function) :
    (function.renameVariables rename).blocks =
      function.blocks.map (Block.renameVariables rename) := by
  simp [Function.renameVariables, Function.blocks]

@[simp] theorem Program.functions_renameVariables (rename : VarId → VarId)
    (program : Program) :
    (program.renameVariables rename).functions =
      program.functions.map (Function.renameVariables rename) := by
  rcases program with ⟨init, main, rest⟩
  cases main <;> simp [Program.renameVariables, Program.functions]

theorem Program.renameVariables_id (program : Program) :
    program.renameVariables id = program := by
  have hfunction : Function.renameVariables id = id := funext Function.renameVariables_id
  cases program
  simp [Program.renameVariables, hfunction]

theorem Program.renameVariables_compose (outer inner : VarId → VarId) (program : Program) :
    (program.renameVariables inner).renameVariables outer =
      program.renameVariables (outer ∘ inner) := by
  cases program
  simp [Program.renameVariables, Function.comp_def]

@[simp] theorem Expr.variableOccurrences_renameVariables (rename : VarId → VarId)
    (value : Expr) :
    (value.renameVariables rename).variableOccurrences =
      value.variableOccurrences.map rename := by
  cases value <;> rfl

@[simp] theorem Stmt.variableOccurrences_renameVariables (rename : VarId → VarId)
    (statement : Stmt) :
    (statement.renameVariables rename).variableOccurrences =
      statement.variableOccurrences.map rename := by
  cases statement <;> simp [Stmt.renameVariables, Stmt.variableOccurrences]

@[simp] theorem Terminator.variableOccurrences_renameVariables (rename : VarId → VarId)
    (terminator : Terminator) :
    (terminator.renameVariables rename).variableOccurrences =
      terminator.variableOccurrences.map rename := by
  cases terminator <;> rfl

@[simp] theorem Block.variableOccurrences_renameVariables (rename : VarId → VarId)
    (block : Block) :
    (block.renameVariables rename).variableOccurrences =
      block.variableOccurrences.map rename := by
  cases block
  simp [Block.renameVariables, Block.variableOccurrences, List.map_append,
    List.map_flatMap, List.flatMap_map]

@[simp] theorem Function.variableOccurrences_renameVariables (rename : VarId → VarId)
    (function : Function) :
    (function.renameVariables rename).variableOccurrences =
      function.variableOccurrences.map rename := by
  simp [Function.variableOccurrences, List.map_flatMap, List.flatMap_map]

@[simp] theorem Program.variableOccurrences_renameVariables (rename : VarId → VarId)
    (program : Program) :
    (program.renameVariables rename).variableOccurrences =
      program.variableOccurrences.map rename := by
  simp [Program.variableOccurrences, List.map_flatMap, List.flatMap_map]

theorem Expr.renameVariables_congr {left right : VarId → VarId} {value : Expr}
    (h : ∀ identifier ∈ value.variableOccurrences, left identifier = right identifier) :
    value.renameVariables left = value.renameVariables right := by
  cases value <;> simp_all [Expr.renameVariables, Expr.variableOccurrences]

theorem Stmt.renameVariables_congr {left right : VarId → VarId} {statement : Stmt}
    (h : ∀ identifier ∈ statement.variableOccurrences,
      left identifier = right identifier) :
    statement.renameVariables left = statement.renameVariables right := by
  cases statement with
  | assign result value =>
      have hresult := h result (by simp [Stmt.variableOccurrences])
      have hvalue : value.renameVariables left = value.renameVariables right := by
        apply Expr.renameVariables_congr
        intro identifier hidentifier
        exact h identifier (by simp [Stmt.variableOccurrences, hidentifier])
      simp [Stmt.renameVariables, hresult, hvalue]
  | sstore key value => simp_all [Stmt.renameVariables, Stmt.variableOccurrences]
  | gas result => simp_all [Stmt.renameVariables, Stmt.variableOccurrences]
  | call callData =>
      simp_all [Stmt.renameVariables, Stmt.variableOccurrences]
  | malloc result size | mallocUninit result size =>
      simp_all [Stmt.renameVariables, Stmt.variableOccurrences]
  | mstore32 offset value => simp_all [Stmt.renameVariables, Stmt.variableOccurrences]
  | mload32 result offset => simp_all [Stmt.renameVariables, Stmt.variableOccurrences]
  | icall callee args dests =>
      have hargs : args.map left = args.map right := by
        apply Array.map_congr_left
        intro identifier hidentifier
        exact h identifier (by simp [Stmt.variableOccurrences, hidentifier])
      have hdests : dests.map left = dests.map right := by
        apply Array.map_congr_left
        intro identifier hidentifier
        exact h identifier (by simp [Stmt.variableOccurrences, hidentifier])
      simp [Stmt.renameVariables, hargs, hdests]

theorem Terminator.renameVariables_congr {left right : VarId → VarId}
    {terminator : Terminator}
    (h : ∀ identifier ∈ terminator.variableOccurrences,
      left identifier = right identifier) :
    terminator.renameVariables left = terminator.renameVariables right := by
  cases terminator <;>
    simp_all [Terminator.renameVariables, Terminator.variableOccurrences]

theorem Block.renameVariables_congr {left right : VarId → VarId}
    {block : Block}
    (h : ∀ identifier ∈ block.variableOccurrences,
      left identifier = right identifier) :
    block.renameVariables left = block.renameVariables right := by
  have hinputs : block.inputs.map left = block.inputs.map right := by
    apply Array.map_congr_left
    intro identifier hidentifier
    exact h identifier (by simp [Block.variableOccurrences, hidentifier])
  have hstatements : block.statements.map (Stmt.renameVariables left) =
      block.statements.map (Stmt.renameVariables right) := by
    apply Array.map_congr_left
    intro statement hstatement
    apply Stmt.renameVariables_congr
    intro identifier hidentifier
    have hstatement' : statement ∈ block.statements.toList := by simpa using hstatement
    exact h identifier (by
      simp only [Block.variableOccurrences, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨statement, hstatement', hidentifier⟩))
  have hterminator : block.terminator.renameVariables left =
      block.terminator.renameVariables right := by
    apply Terminator.renameVariables_congr
    intro identifier hidentifier
    exact h identifier (by simp [Block.variableOccurrences, hidentifier])
  have houtputs : block.outputs.map left = block.outputs.map right := by
    apply Array.map_congr_left
    intro identifier hidentifier
    exact h identifier (by simp [Block.variableOccurrences, hidentifier])
  simp [Block.renameVariables, hinputs, hstatements, hterminator, houtputs]

theorem Function.renameVariables_congr {left right : VarId → VarId}
    {function : Function}
    (h : ∀ identifier ∈ function.variableOccurrences,
      left identifier = right identifier) :
    function.renameVariables left = function.renameVariables right := by
  have hblock : ∀ block ∈ function.blocks,
      block.renameVariables left = block.renameVariables right := by
    intro block hblock
    apply Block.renameVariables_congr
    intro identifier hidentifier
    have hblock' : block ∈ function.blocks.toList := by simpa using hblock
    exact h identifier (by
      simp only [Function.variableOccurrences, List.mem_flatMap]
      exact ⟨block, hblock', hidentifier⟩)
  have hentry : function.entry.renameVariables left =
      function.entry.renameVariables right :=
    hblock function.entry (by simp [Function.blocks])
  have hrest : function.rest.map (Block.renameVariables left) =
      function.rest.map (Block.renameVariables right) := by
    apply Array.map_congr_left
    intro block hblock'
    exact hblock block (by simp [Function.blocks, hblock'])
  simp [Function.renameVariables, hentry, hrest]

theorem Program.renameVariables_congr {left right : VarId → VarId} {program : Program}
    (h : ∀ identifier ∈ program.variableOccurrences,
      left identifier = right identifier) :
    program.renameVariables left = program.renameVariables right := by
  have hfunction : ∀ function ∈ program.functions,
      function.renameVariables left = function.renameVariables right := by
    intro function hfunction
    apply Function.renameVariables_congr
    intro identifier hidentifier
    have hfunction' : function ∈ program.functions.toList := by simpa using hfunction
    exact h identifier (by
      simp only [Program.variableOccurrences, List.mem_flatMap]
      exact ⟨function, hfunction', hidentifier⟩)
  have hinit : program.init.renameVariables left = program.init.renameVariables right :=
    hfunction program.init (by simp [Program.functions])
  have hmain : program.main.map (Function.renameVariables left) =
      program.main.map (Function.renameVariables right) := by
    cases hmainEq : program.main with
    | none => rfl
    | some function =>
        simp [hfunction function (by simp [Program.functions, hmainEq])]
  have hrest : program.rest.map (Function.renameVariables left) =
      program.rest.map (Function.renameVariables right) := by
    apply Array.map_congr_left
    intro function hfunction'
    exact hfunction function (by simp [Program.functions, hfunction'])
  simp [Program.renameVariables, hinit, hmain, hrest]

private theorem eraseDups_map_of_injective_on {rename : VarId → VarId}
    {identifiers : List VarId}
    (hinjective : ∀ left ∈ identifiers, ∀ right ∈ identifiers,
      rename left = rename right → left = right) :
    (identifiers.map rename).eraseDups = identifiers.eraseDups.map rename := by
  match identifiers with
  | [] => rfl
  | head :: tail =>
      have htail : ∀ left ∈ tail, ∀ right ∈ tail,
          rename left = rename right → left = right := by
        intro left hleft right hright hequal
        exact hinjective left (by simp [hleft]) right (by simp [hright]) hequal
      have hfilter :
          (tail.map rename).filter (fun identifier => !identifier == rename head) =
            (tail.filter fun identifier => !identifier == head).map rename := by
        rw [List.filter_map]
        apply congrArg (List.map rename)
        apply List.filter_congr
        intro identifier hidentifier
        by_cases hequal : identifier = head
        · subst identifier
          simp
        · have hrenamed : rename identifier ≠ rename head := by
            intro hrename
            exact hequal (hinjective identifier (by simp [hidentifier]) head (by simp) hrename)
          simp [Function.comp_apply, beq_eq_false_iff_ne.mpr hequal,
            beq_eq_false_iff_ne.mpr hrenamed]
      rw [List.eraseDups_cons, List.map_cons, List.eraseDups_cons, hfilter]
      congr 1
      apply eraseDups_map_of_injective_on
      intro left hleft right hright hequal
      exact htail left (List.mem_of_mem_filter hleft) right
        (List.mem_of_mem_filter hright) hequal
termination_by identifiers.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem idxOf_map_of_injective_on {rename : VarId → VarId}
    {identifiers : List VarId} {identifier : VarId}
    (hidentifier : identifier ∈ identifiers)
    (hinjective : ∀ left ∈ identifiers, ∀ right ∈ identifiers,
      rename left = rename right → left = right) :
    (identifiers.map rename).idxOf (rename identifier) = identifiers.idxOf identifier := by
  induction identifiers with
  | nil => simp_all
  | cons head tail induction =>
      by_cases hequal : head = identifier
      · subst head
        simp
      · have hrename : rename head ≠ rename identifier := by
          intro hrenamed
          exact hequal (hinjective head (by simp) identifier hidentifier hrenamed)
        have hinTail : identifier ∈ tail := by
          simp only [List.mem_cons] at hidentifier
          exact hidentifier.resolve_left (fun equality => hequal equality.symm)
        rw [List.map_cons, List.idxOf_cons, List.idxOf_cons,
          beq_eq_false_iff_ne.mpr hrename,
          beq_eq_false_iff_ne.mpr hequal]
        apply congrArg (fun index => index + 1)
        apply induction hinTail
        intro left hleft right hright hrenamed
        exact hinjective left (by simp [hleft]) right (by simp [hright]) hrenamed

theorem Program.AlphaEquiv.refl (program : Program) : Program.AlphaEquiv program program := by
  exact ⟨id, id, Program.renameVariables_id program, Program.renameVariables_id program⟩

theorem Program.AlphaEquiv.symm {left right : Program} :
    Program.AlphaEquiv left right → Program.AlphaEquiv right left := by
  rintro ⟨forward, backward, hforward, hbackward⟩
  exact ⟨backward, forward, hbackward, hforward⟩

theorem Program.AlphaEquiv.trans {first second third : Program} :
    Program.AlphaEquiv first second → Program.AlphaEquiv second third →
      Program.AlphaEquiv first third := by
  rintro ⟨forward₁, backward₁, hforward₁, hbackward₁⟩
    ⟨forward₂, backward₂, hforward₂, hbackward₂⟩
  refine ⟨forward₂ ∘ forward₁, backward₁ ∘ backward₂, ?_, ?_⟩
  · rw [← Program.renameVariables_compose, hforward₁, hforward₂]
  · rw [← Program.renameVariables_compose, hbackward₂, hbackward₁]

theorem Program.normalize_alphaEquiv (program : Program) :
    Program.AlphaEquiv program.normalize program := by
  let identifiers := program.variableOccurrences.eraseDups
  let restore : VarId → VarId := fun identifier =>
    identifiers.getD identifier.id ⟨0⟩
  refine ⟨restore, program.normalVariable, ?_, rfl⟩
  rw [Program.normalize, Program.renameVariables_compose]
  calc
    program.renameVariables (restore ∘ program.normalVariable) =
        program.renameVariables id := by
      apply Program.renameVariables_congr
      intro identifier hidentifier
      simp only [Function.comp_apply, id_eq]
      have hinIdentifiers : identifier ∈ identifiers := by
        exact List.mem_eraseDups.mpr hidentifier
      have hindex := List.idxOf_lt_length_of_mem hinIdentifiers
      change identifiers.getD (identifiers.idxOf identifier) ⟨0⟩ = identifier
      rw [← List.getElem_eq_getD (h := hindex) ⟨0⟩]
      exact List.getElem_idxOf hindex
    _ = program := Program.renameVariables_id program

private theorem normalVariable_renameVariables {left right : Program}
    {rename : VarId → VarId}
    (hrenamed : left.renameVariables rename = right)
    (hinjective : ∀ first ∈ left.variableOccurrences,
      ∀ second ∈ left.variableOccurrences,
      rename first = rename second → first = second)
    {identifier : VarId} (hidentifier : identifier ∈ left.variableOccurrences) :
    right.normalVariable (rename identifier) = left.normalVariable identifier := by
  have hoccurrences := congrArg Program.variableOccurrences hrenamed
  rw [Program.variableOccurrences_renameVariables] at hoccurrences
  simp only [Program.normalVariable]
  rw [← hoccurrences]
  rw [eraseDups_map_of_injective_on hinjective]
  apply congrArg VarId.mk
  apply idxOf_map_of_injective_on
  · exact List.mem_eraseDups.mpr hidentifier
  · intro first hfirst second hsecond hequal
    exact hinjective first (List.mem_eraseDups.mp hfirst) second
      (List.mem_eraseDups.mp hsecond) hequal

theorem Program.alphaEquiv_iff_normalize_eq {left right : Program} :
    Program.AlphaEquiv left right ↔ left.normalize = right.normalize := by
  constructor
  · rintro ⟨forward, backward, hforward, hbackward⟩
    have hforwardOccurrences := congrArg Program.variableOccurrences hforward
    have hbackwardOccurrences := congrArg Program.variableOccurrences hbackward
    rw [Program.variableOccurrences_renameVariables] at hforwardOccurrences
    rw [Program.variableOccurrences_renameVariables] at hbackwardOccurrences
    have hinverse : ∀ identifier ∈ left.variableOccurrences,
        backward (forward identifier) = identifier := by
      have hmapped : left.variableOccurrences.map (backward ∘ forward) =
          left.variableOccurrences.map id := by
        rw [← List.map_map, hforwardOccurrences, hbackwardOccurrences]
        simp
      exact List.map_inj_left.mp hmapped
    have hinjective : ∀ first ∈ left.variableOccurrences,
        ∀ second ∈ left.variableOccurrences,
        forward first = forward second → first = second := by
      intro first hfirst second hsecond hequal
      rw [← hinverse first hfirst, ← hinverse second hsecond, hequal]
    rw [Program.normalize, Program.normalize, ← hforward,
      Program.renameVariables_compose]
    apply Program.renameVariables_congr
    intro identifier hidentifier
    simpa only [Function.comp_apply, hforward] using
      (normalVariable_renameVariables hforward hinjective hidentifier).symm
  · intro hequal
    exact Program.AlphaEquiv.trans (Program.AlphaEquiv.symm (Program.normalize_alphaEquiv left))
      (hequal ▸ Program.normalize_alphaEquiv right)

theorem Program.normalize_normal (program : Program) :
    program.normalize.Normal :=
  Program.alphaEquiv_iff_normalize_eq.mp (Program.normalize_alphaEquiv program)

end Sir.Vars.Proofs
