import Sir.Vars.Proofs.Normalize

namespace Sir.Vars

instance Program.alphaEquivalenceSetoid : Setoid Program where
  r := Program.AlphaEquiv
  iseqv := {
    refl := Proofs.Program.AlphaEquiv.refl
    symm := Proofs.Program.AlphaEquiv.symm
    trans := Proofs.Program.AlphaEquiv.trans }

def Program.normalizeEquivalenceClass :
    Quotient Program.alphaEquivalenceSetoid → { program : Program // program.Normal } :=
  Quotient.lift
    (fun program => ⟨program.normalize, Proofs.Program.normalize_normal program⟩)
    (fun _ _ equivalent =>
      Subtype.ext (Proofs.Program.alphaEquiv_iff_normalize_eq.mp equivalent))

end Sir.Vars
