import Sir.Vars.Proofs.Canonical

namespace Sir.Vars

instance Program.alphaEquivalenceSetoid : Setoid Program where
  r := Program.AlphaEquiv
  iseqv := {
    refl := Program.AlphaEquiv.refl
    symm := Program.AlphaEquiv.symm
    trans := Program.AlphaEquiv.trans }

def Program.canonicalizeEquivalenceClass :
    Quotient Program.alphaEquivalenceSetoid → { program : Program // program.Canonical } :=
  Quotient.lift
    (fun program => ⟨program.canonicalize, Program.canonicalize_canonical program⟩)
    (fun _ _ equivalent =>
      Subtype.ext (Program.alphaEquiv_iff_canonicalize_eq.mp equivalent))

end Sir.Vars
