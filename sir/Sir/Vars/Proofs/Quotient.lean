import Sir.Vars.Spec.Quotient

namespace Sir.Vars.Proofs

private def normalProgramEquivalenceClass :
    { program : Program // program.Normal } → Quotient Program.alphaEquivalenceSetoid :=
  fun program => Quotient.mk Program.alphaEquivalenceSetoid program

private theorem normalProgramEquivalenceClass_leftInverse :
    Function.LeftInverse normalProgramEquivalenceClass
      Program.normalizeEquivalenceClass := by
  intro equivalenceClass
  refine Quotient.inductionOn equivalenceClass ?_
  intro program
  exact Quotient.sound (Program.normalize_alphaEquiv program)

theorem Program.normalizeEquivalenceClass_bijective :
    Function.Bijective Vars.Program.normalizeEquivalenceClass := by
  constructor
  · exact normalProgramEquivalenceClass_leftInverse.injective
  · intro program
    refine ⟨normalProgramEquivalenceClass program, ?_⟩
    exact Subtype.ext program.property

end Sir.Vars.Proofs
