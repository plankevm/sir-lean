import Sir.Vars.Spec

namespace Sir.Vars

inductive Diagnostic where
  | iretArity (declared actual : Nat)

abbrev CheckM := Except Diagnostic

abbrev Ensures (P : Prop) := CheckM (PLift P)

def ensure (diagnostic : Diagnostic) (P : Prop) [Decidable P] : Ensures P :=
  if h : P then .ok ⟨h⟩ else .error diagnostic

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
      ensure (.iretArity (fn.outputs?.getD 0) block.outputs.size) _

def RankDecreases (p : Program) (rank : FunctionId → Nat) : Prop :=
  ∀ f g, p.callEdge f g → rank g < rank f

end Sir.Vars
