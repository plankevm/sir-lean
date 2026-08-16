import Sir.Vars.Spec.Quotient

namespace Sir.Vars.Proofs

private def canonicalProgramEquivalenceClass :
    { program : Program // program.Canonical } → Quotient Program.alphaEquivalenceSetoid :=
  fun program => Quotient.mk Program.alphaEquivalenceSetoid program

private theorem canonicalProgramEquivalenceClass_leftInverse :
    Function.LeftInverse canonicalProgramEquivalenceClass
      Program.canonicalizeEquivalenceClass := by
  intro equivalenceClass
  refine Quotient.inductionOn equivalenceClass ?_
  intro program
  exact Quotient.sound (Program.canonicalize_alphaEquiv program)

theorem Program.canonicalizeEquivalenceClass_bijective :
    Function.Bijective Vars.Program.canonicalizeEquivalenceClass := by
  constructor
  · exact canonicalProgramEquivalenceClass_leftInverse.injective
  · intro program
    refine ⟨canonicalProgramEquivalenceClass program, ?_⟩
    exact Subtype.ext program.property

end Sir.Vars.Proofs
