import SirLean.IR

namespace Sir

example : ControlFlowGraph := {
  blocks := #[
    {
      inputs := #[]
      ops := #[
        .const ⟨0⟩ 67
      ]
      last := .jump ⟨1⟩
      outputs := #[]
    },
    {
      inputs := #[]
      ops := #[
        .add32 ⟨1⟩ ⟨0⟩ ⟨0⟩
      ]
      last := .exit ⟨1⟩
      outputs := #[]
    }
  ]
  entry := ⟨0, by decide⟩
  entry_no_inputs := by decide
  blocks_valid := by simp [BasicBlock.valid_in_cfg, BasicBlock.successors, EndOp.successors]
  refs_valid := by
    simp [InnerCFG.refs_valid, InnerCFG.op_refs_valid, InnerCFG.end_op_refs_valid]
    constructor
    · intro bi
      rcases bi with ⟨i, hi⟩
      cases i with
      | zero =>
          intro opi ref href
          rcases opi with ⟨j, hj⟩
          cases j with
          | zero =>
              simp [Op.refs] at href
          | succ j =>
              simp at hj
      | succ i =>
          cases i with
          | zero =>
              intro opi ref href
              rcases opi with ⟨j, hj⟩
              cases j with
              | zero =>
                  right
                  simp [Op.refs] at href
                  rcases href with rfl
                  intro h
                  rcases Relation.ReflTransGen.cases_tail h with hEq | ⟨b, _hprev, hedge⟩
                  · simp at hEq
                  · rcases hedge with ⟨hedge, hundef⟩
                    rcases b with ⟨k, hk⟩
                    cases k with
                    | zero =>
                        simp [BasicBlock.defs, Op.defs] at hundef
                    | succ k =>
                        cases k with
                        | zero =>
                            simp [BasicBlock.successors, EndOp.successors] at hedge
                        | succ k =>
                            simp at hk
                            omega
              | succ j =>
                  simp at hj
          | succ i =>
              intro opi ref href
              simp at hi
              omega
    · intro bi ref href
      rcases bi with ⟨i, hi⟩
      cases i with
      | zero =>
          simp [EndOp.var_refs] at href
      | succ i =>
          cases i with
          | zero =>
              left
              simp [BasicBlock.defs, Op.defs, EndOp.var_refs] at href ⊢
              exact href
          | succ i =>
              simp at hi
              omega
}

end Sir
