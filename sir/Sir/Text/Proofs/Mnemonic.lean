import Sir.Text.Spec.Mnemonic
import Sir.Vars.Spec.Normalize

namespace Sir.Vars.Text

private theorem vector_toList_zero {α : Type} (vector : Vector α 0) : vector.toList = [] :=
  List.eq_nil_of_length_eq_zero (by simp)

private theorem vector_toList_one {α : Type} (vector : Vector α 1) :
    vector.toList = [vector[0]] := by
  obtain ⟨⟨l⟩, h⟩ := vector
  match l, h with | [a], _ => rfl

private theorem vector_toList_two {α : Type} (vector : Vector α 2) :
    vector.toList = [vector[0], vector[1]] := by
  obtain ⟨⟨l⟩, h⟩ := vector
  match l, h with | [a, b], _ => rfl

theorem spelling_build {entry : Mnemonic} (member : entry ∈ mnemonics)
    (results : Vector VarId entry.results) (operands : Vector VarId entry.operands) :
    spelling (entry.build results operands) =
      ⟨entry.name, results.toList, operands.toList⟩ := by
  simp only [mnemonics, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [spelling, vector_toList_zero, vector_toList_one, vector_toList_two]

theorem mnemonic_name {entry : Mnemonic} (member : entry ∈ mnemonics) :
    entry.name ≠ "const" ∧ entry.name ≠ "icall" := by
  simp only [mnemonics, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem variableOccurrences_spelling (statement : Stmt) :
    statement.variableOccurrences =
      (spelling statement).results ++ (spelling statement).operands := by
  cases statement with
  | assign result value => cases value <;> rfl
  | _ => rfl

theorem build_spelling (statement : Stmt) (rename : VarId → VarId)
    (notConst : (spelling statement).name ≠ "const")
    (notIcall : (spelling statement).name ≠ "icall") :
    ∃ entry, mnemonics.find? (·.name == (spelling statement).name) = some entry ∧
      ∃ (resultsOk : ((spelling statement).results.map rename).toArray.size = entry.results)
        (operandsOk : ((spelling statement).operands.map rename).toArray.size = entry.operands),
        entry.build ⟨_, resultsOk⟩ ⟨_, operandsOk⟩ = statement.renameVariables rename := by
  cases statement with
  | assign result value =>
      cases value with
      | constant => exact (notConst rfl).elim
      | _ => exact ⟨_, rfl, rfl, rfl, rfl⟩
  | icall => exact (notIcall rfl).elim
  | _ => exact ⟨_, rfl, rfl, rfl, rfl⟩

end Sir.Vars.Text
