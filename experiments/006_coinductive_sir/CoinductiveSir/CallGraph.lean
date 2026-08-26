import CoinductiveSir.Data
import Mathlib.Logic.Relation

def Program.CallEdge (p : Program) (src dst : FunctionId) : Prop :=
  ∃ fn ∈ p.function? src, ∃ b ∈ fn.blocks, ∃ stmt ∈ b.statements, ∃ ins outs, stmt = .icall dst ins outs


def Program.CallGraphAcyclic (p : Program) : Prop := ¬∃ a, Relation.TransGen p.CallEdge a a


