import Sir.Vars.Spec

namespace Sir.Vars

theorem lt_size_of_getElem? {α : Type} {xs : Array α} {index : Nat} {x : α}
    (h : xs[index]? = some x) : index < xs.size := by
  by_contra hle
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hle)] at h
  simp at h

def Block.DefinedBeforeUseAt (block : Block) (index : Nat) : Prop :=
  ∀ statement, block.statements[index]? = some statement →
    ∀ identifier ∈ statement.variablesRead, identifier ∈ block.variablesDefinedBefore index

instance (block : Block) (index : Nat) : Decidable (block.DefinedBeforeUseAt index) :=
  match h : block.statements[index]? with
  | none =>
      isTrue (by
        intro statement hstatement
        rw [h] at hstatement
        simp at hstatement)
  | some statement =>
      decidable_of_iff
        (∀ identifier ∈ statement.variablesRead,
          identifier ∈ block.variablesDefinedBefore index)
        ⟨fun hall _ hother => by rw [h] at hother; cases hother; exact hall,
          fun hall => hall statement h⟩

theorem Block.variablesDefinedBeforeUse_iff (block : Block) :
    ((∀ index ∈ List.range block.statements.size, block.DefinedBeforeUseAt index) ∧
      ∀ identifier ∈ block.terminator.variablesRead ++ block.outputs.toList,
        identifier ∈ block.variablesDefinedBefore block.statements.size) ↔
      block.VariablesDefinedBeforeUse := by
  constructor
  · rintro ⟨hstatements, houtputs⟩
    refine ⟨fun index statement hstatement => ?_, houtputs⟩
    exact hstatements index (List.mem_range.mpr (lt_size_of_getElem? hstatement)) statement
      hstatement
  · rintro ⟨hstatements, houtputs⟩
    exact ⟨fun index _ statement hstatement => hstatements index statement hstatement, houtputs⟩

end Sir.Vars
