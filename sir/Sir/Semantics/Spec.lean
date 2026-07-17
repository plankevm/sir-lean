import Sir.Semantics.SmallStep

namespace Sir

def Deterministic (program : Program) : Prop :=
  (∀ ctx initialWorld trace record₁ record₂ state₁ state₂,
    Runs program ctx initialWorld (trace ++ [.call record₁]) state₁ →
    Runs program ctx initialWorld (trace ++ [.call record₂]) state₂ →
    record₁.input = record₂.input) ∧
  (∀ ctx initialWorld trace state₁ state₂,
    Runs program ctx initialWorld trace state₁ →
    state₁.control = .halted →
    Runs program ctx initialWorld trace state₂ →
    state₂.control = .halted →
    state₁.world = state₂.world)

end Sir
