import Sir.Stack.Proofs.Dialogue

namespace Sir

variable {program : Stack.Program}

theorem Stack.Program.WellFormed.callEdge_wellFounded
    (hwf : program.WellFormed) : WellFounded (Function.swap program.callEdge) := by
  classical
  let validFunctions := (Finset.range program.functions.size).image FunctionId.mk
  let ancestors (f : FunctionId) := validFunctions.filter fun predecessor =>
    Relation.TransGen (Function.swap program.callEdge) predecessor f
  let rank (f : FunctionId) :=
    if f.id < program.functions.size then (ancestors f).card + 1 else 0
  apply Subrelation.wf (r := fun predecessor caller => rank predecessor < rank caller) _
    (measure rank).wf
  intro predecessor caller hEdge
  have callerValid : caller.id < program.functions.size := by
    rcases hEdge with ⟨argumentCount, resultCount, function, hfunction, hinstr⟩
    exact (Array.getElem?_eq_some_iff.mp hfunction).1
  by_cases predecessorValid : predecessor.id < program.functions.size
  · have ancestorsSubset : ancestors predecessor ⊆ ancestors caller := by
      intro f hf
      simp only [ancestors, Finset.mem_filter] at hf ⊢
      exact ⟨hf.1, hf.2.tail hEdge⟩
    have predecessorMem : predecessor ∈ ancestors caller := by
      simp only [ancestors, Finset.mem_filter, validFunctions, Finset.mem_image,
        Finset.mem_range]
      exact ⟨⟨predecessor.id, predecessorValid, rfl⟩,
        Relation.TransGen.single hEdge⟩
    have predecessorNotMem : predecessor ∉ ancestors predecessor := by
      intro h
      exact hwf.acyclicCalls predecessor (Finset.mem_filter.mp h).2.swap
    have ancestorsStrict : ancestors predecessor ⊂ ancestors caller :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨ancestorsSubset, fun h => predecessorNotMem (h ▸ predecessorMem)⟩
    simp only [rank, predecessorValid, callerValid, ↓reduceIte]
    exact Nat.add_lt_add_right (Finset.card_lt_card ancestorsStrict) 1
  · simp [rank, predecessorValid, callerValid]

end Sir
