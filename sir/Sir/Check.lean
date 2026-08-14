import Sir.Vars.Proofs.WellFormed

namespace Sir.Vars

inductive Diagnostic where
  | icallArity (callee : FunctionId) (args dests : Nat)
  | iretArity (function : Nat) (block : Nat)
  | recursiveCall (caller : FunctionId)
  | entryArity (function : FunctionId)
  | badJumpTarget (function : Nat) (block target : Nat)
  | undefinedLocal (function : Nat) (block : Nat) (local_ : VarId)
deriving Repr

abbrev CheckM := Except Diagnostic

-- A check that hands back a proof of `P` when it succeeds.
abbrev Ensures (P : Prop) := CheckM (PLift P)

def ensure (diagnostic : Diagnostic) (P : Prop) [Decidable P] : Ensures P :=
  if h : P then .ok ⟨h⟩ else .error diagnostic

def Ensures.isOk {P : Prop} : Ensures P → Bool
  | .ok _ => true
  | .error _ => false

theorem Ensures.sound {P : Prop} : ∀ e : Ensures P, e.isOk = true → P
  | .ok proof, _ => proof.down
  | .error _, h => by simp [Ensures.isOk] at h

def ensureAll {α : Type} {P : α → Prop} : (xs : List α) →
    ((x : α) → x ∈ xs → Ensures (P x)) → Ensures (∀ x ∈ xs, P x)
  | [], _ => .ok ⟨by simp⟩
  | x :: rest, check => do
      let ⟨head⟩ ← check x (List.mem_cons_self ..)
      let ⟨tail⟩ ← ensureAll rest fun y hy => check y (List.mem_cons_of_mem _ hy)
      return ⟨by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact head
        · exact tail y hy⟩

def ensureAllArray {α : Type} {P : α → Prop} (xs : Array α)
    (check : (x : α) → x ∈ xs → Ensures (P x)) : Ensures (∀ x ∈ xs, P x) := do
  let ⟨proof⟩ ← ensureAll xs.toList fun x hx => check x (Array.mem_toList_iff.mp hx)
  return ⟨fun x hx => proof x (Array.mem_toList_iff.mpr hx)⟩

def checkIretArity (p : Program) :
    Ensures (∀ fn ∈ p.functions, ∀ block ∈ fn.blocks,
      block.terminator = .iret → some block.outputs.size = fn.outputs?) :=
  ensureAllArray p.functions fun fn _ =>
    ensureAllArray fn.blocks fun block _ =>
      ensure (.iretArity p.functions.size block.outputs.size) _

def RankDecreases (p : Program) (rank : FunctionId → Nat) : Prop :=
  ∀ f g, p.callEdge f g → rank g < rank f

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

structure Verified where
  program : Program
  wellFormed : program.WellFormed

end Sir.Vars
