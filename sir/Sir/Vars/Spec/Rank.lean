import Sir.Vars.Spec

namespace Sir.Vars

def RankDecreases (p : Program) (rank : FunctionId → Nat) : Prop :=
  ∀ f g, p.callEdge f g → rank g < rank f

end Sir.Vars
