import Sir.Vars.Spec.Rank

namespace Sir.Vars.Proofs

theorem rank_lt_of_transGen {p : Program} {rank : FunctionId → Nat}
    (decreasing : RankDecreases p rank) {f g} (path : Relation.TransGen p.callEdge f g) :
    rank g < rank f := by
  induction path with
  | single edge => exact decreasing _ _ edge
  | tail _ edge ih => exact Nat.lt_trans (decreasing _ _ edge) ih

theorem acyclic_of_rank {p : Program} {rank : FunctionId → Nat}
    (decreasing : RankDecreases p rank) (f : FunctionId) :
    ¬ Relation.TransGen p.callEdge f f :=
  fun path => Nat.lt_irrefl _ (rank_lt_of_transGen decreasing path)

end Sir.Vars.Proofs
