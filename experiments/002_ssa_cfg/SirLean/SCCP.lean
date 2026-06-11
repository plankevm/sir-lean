import SirLean.IR
import Mathlib.Order.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Sir.SCCP

/-! ## The per-variable lattice

`undef ⊑ const w ⊑ overdefined`: nothing known yet, known constant,
known non-constant. -/

inductive Value where
  | undef
  | const (w : Word)
  | overdefined
deriving DecidableEq, Repr

@[grind]
def Value.le : Value → Value → Prop
  | .undef, _ => True
  | _, .overdefined => True
  | .const _, .undef => False
  | .const a, .const b => a = b
  | .overdefined, .undef => False
  | .overdefined, .const _ => False

instance : Decidable (Value.le a b) := by
  unfold Value.le
  cases a <;> cases b <;> infer_instance

instance : SemilatticeSup Value where
  le := Value.le
  le_refl := by unfold Value.le; grind
  le_trans := by unfold Value.le; grind
  le_antisymm := by unfold Value.le; grind

  sup
  | .undef, b => b
  | a, .undef => a
  | .const a, .const b => if a = b then .const a else .overdefined
  | .overdefined, _ => .overdefined
  | _, .overdefined => .overdefined

  le_sup_left := by unfold Value.le; grind
  le_sup_right := by unfold Value.le; grind
  sup_le := by unfold Value.le; grind

/-- Position in the lattice; ascending chains strictly increase it, which is
what bounds the fixpoint iteration. -/
def Value.height : Value → Nat
  | .undef => 0
  | .const _ => 1
  | .overdefined => 2

theorem Value.height_le_two (v : Value) : v.height ≤ 2 := by
  cases v <;> simp [Value.height]

theorem Value.height_mono {a b : Value} (h : a ≤ b) : a.height ≤ b.height := by
  have h' : Value.le a b := h
  cases a <;> cases b <;> simp_all [Value.le, Value.height]

theorem Value.height_strict_mono {a b : Value} (hle : a ≤ b) (hne : a ≠ b) :
    a.height < b.height := by
  have h' : Value.le a b := hle
  cases a <;> cases b <;> simp_all [Value.le, Value.height]

/-- Abstract binary operation: any overdefined operand poisons the result,
otherwise an undef operand means the op was never executed. -/
def Value.binop (f : Word → Word → Word) : Value → Value → Value
  | .overdefined, _ => .overdefined
  | _, .overdefined => .overdefined
  | .undef, _ => .undef
  | _, .undef => .undef
  | .const a, .const b => .const (f a b)

/-! ## Abstract state

One lattice value per variable defined anywhere in the CFG, plus a
reachability flag per block. Vectors keep the domain finite and fixed,
which is what makes the iteration provably convergent. -/

def allDefs (cfg : ControlFlowGraph) : Array VarId :=
  cfg.blocks.flatMap BasicBlock.defs

structure AbsState (cfg : ControlFlowGraph) where
  reachable : Vector Bool cfg.blocks.size
  vals : Vector Value (allDefs cfg).size
deriving DecidableEq

variable {cfg : ControlFlowGraph}

namespace AbsState

instance : Preorder (AbsState cfg) where
  le s t :=
    (∀ (i : Nat) (h : i < cfg.blocks.size), s.reachable[i] = true → t.reachable[i] = true)
    ∧ ∀ (i : Nat) (h : i < (allDefs cfg).size), s.vals[i] ≤ t.vals[i]
  le_refl s := ⟨fun _ _ h => h, fun _ _ => le_refl _⟩
  le_trans s t u hst htu :=
    ⟨fun i h hs => htu.1 i h (hst.1 i h hs), fun i h => le_trans (hst.2 i h) (htu.2 i h)⟩

theorem le_iff {s t : AbsState cfg} :
    s ≤ t ↔
      (∀ (i : Nat) (h : i < cfg.blocks.size), s.reachable[i] = true → t.reachable[i] = true)
      ∧ ∀ (i : Nat) (h : i < (allDefs cfg).size), s.vals[i] ≤ t.vals[i] :=
  Iff.rfl

/-- Bottom element: only the entry block reachable, every variable undef. -/
def init (cfg : ControlFlowGraph) : AbsState cfg where
  reachable := (Vector.replicate cfg.blocks.size false).set cfg.entry.val true cfg.entry.isLt
  vals := Vector.replicate (allDefs cfg).size .undef

def get (s : AbsState cfg) (v : VarId) : Value :=
  match (allDefs cfg).finIdxOf? v with
  | some i => s.vals[i]
  | none => .overdefined

def join (s : AbsState cfg) (v : VarId) (x : Value) : AbsState cfg :=
  match (allDefs cfg).finIdxOf? v with
  | some i => { s with vals := s.vals.set i.val (s.vals[i] ⊔ x) i.isLt }
  | none => s

def markReachable (s : AbsState cfg) (b : Nat) (h : b < cfg.blocks.size) : AbsState cfg :=
  { s with reachable := s.reachable.set b true h }

theorem le_join (s : AbsState cfg) (v : VarId) (x : Value) : s ≤ s.join v x := by
  unfold join
  split
  · rename_i i _
    refine ⟨fun _ _ h => h, fun j hj => ?_⟩
    show s.vals[j] ≤ (s.vals.set i.val (s.vals[i] ⊔ x) i.isLt)[j]
    rw [Vector.getElem_set]
    split
    · rename_i hij
      subst hij
      exact le_sup_left
    · exact le_rfl
  · exact le_rfl

theorem le_markReachable (s : AbsState cfg) (b : Nat) (h : b < cfg.blocks.size) :
    s ≤ s.markReachable b h := by
  refine ⟨fun i hi hr => ?_, fun _ _ => le_rfl⟩
  show (s.reachable.set b true h)[i] = true
  rw [Vector.getElem_set]
  split
  · rfl
  · exact hr

/-! ### Convergence measure -/

def score (s : AbsState cfg) : Nat :=
  (∑ i : Fin cfg.blocks.size, (s.reachable[i]).toNat)
    + ∑ i : Fin (allDefs cfg).size, (s.vals[i]).height

def _root_.Sir.SCCP.maxScore (cfg : ControlFlowGraph) : Nat :=
  cfg.blocks.size + 2 * (allDefs cfg).size

theorem score_le_maxScore (s : AbsState cfg) : s.score ≤ maxScore cfg := by
  have h1 : (∑ i : Fin cfg.blocks.size, (s.reachable[i]).toNat)
      ≤ ∑ _i : Fin cfg.blocks.size, 1 :=
    Finset.sum_le_sum fun i _ => Bool.toNat_le _
  have h2 : (∑ i : Fin (allDefs cfg).size, (s.vals[i]).height)
      ≤ ∑ _i : Fin (allDefs cfg).size, 2 :=
    Finset.sum_le_sum fun i _ => Value.height_le_two _
  have e1 : (∑ _i : Fin cfg.blocks.size, 1) = cfg.blocks.size := by simp
  have e2 : (∑ _i : Fin (allDefs cfg).size, 2) = 2 * (allDefs cfg).size := by
    simp [Finset.sum_const, Finset.card_univ, Nat.mul_comm]
  unfold score maxScore
  omega

theorem score_lt_of_lt {s t : AbsState cfg} (hle : s ≤ t) (hne : s ≠ t) :
    s.score < t.score := by
  obtain ⟨hr, hv⟩ := hle
  have hrle : ∀ i : Fin cfg.blocks.size, (s.reachable[i]).toNat ≤ (t.reachable[i]).toNat := by
    intro i
    have := hr i.val i.isLt
    cases hs : s.reachable[i.val] <;> cases ht : t.reachable[i.val] <;> simp_all
  have hvle : ∀ i : Fin (allDefs cfg).size, (s.vals[i]).height ≤ (t.vals[i]).height :=
    fun i => Value.height_mono (hv i.val i.isLt)
  have h1le : (∑ i : Fin cfg.blocks.size, (s.reachable[i]).toNat)
      ≤ ∑ i : Fin cfg.blocks.size, (t.reachable[i]).toNat :=
    Finset.sum_le_sum fun i _ => hrle i
  have h2le : (∑ i : Fin (allDefs cfg).size, (s.vals[i]).height)
      ≤ ∑ i : Fin (allDefs cfg).size, (t.vals[i]).height :=
    Finset.sum_le_sum fun i _ => hvle i
  have hcomp : s.reachable ≠ t.reachable ∨ s.vals ≠ t.vals := by
    by_contra hc
    push Not at hc
    refine hne ?_
    cases s
    cases t
    simp_all
  unfold score
  rcases hcomp with hc | hc
  · have hex : ∃ i : Fin cfg.blocks.size, s.reachable[i] ≠ t.reachable[i] := by
      by_contra hcc
      push Not at hcc
      exact hc (Vector.ext fun i hi => hcc ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    have hstrict : (s.reachable[i]).toNat < (t.reachable[i]).toNat := by
      have := hr i.val i.isLt
      cases hs : s.reachable[i.val] <;> cases ht : t.reachable[i.val] <;>
        simp_all [Fin.getElem_fin]
    have h1 : (∑ i : Fin cfg.blocks.size, (s.reachable[i]).toNat)
        < ∑ i : Fin cfg.blocks.size, (t.reachable[i]).toNat :=
      Finset.sum_lt_sum (fun j _ => hrle j) ⟨i, Finset.mem_univ i, hstrict⟩
    omega
  · have hex : ∃ i : Fin (allDefs cfg).size, s.vals[i] ≠ t.vals[i] := by
      by_contra hcc
      push Not at hcc
      exact hc (Vector.ext fun i hi => hcc ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    have hstrict : (s.vals[i]).height < (t.vals[i]).height :=
      Value.height_strict_mono (hv i.val i.isLt) hi
    have h2 : (∑ i : Fin (allDefs cfg).size, (s.vals[i]).height)
        < ∑ i : Fin (allDefs cfg).size, (t.vals[i]).height :=
      Finset.sum_lt_sum (fun j _ => hvle j) ⟨i, Finset.mem_univ i, hstrict⟩
    omega

end AbsState

/-! ## Transfer functions

Every update goes through `join`/`markReachable`, so one round of `step`
is inflationary by construction: `s ≤ step s`. -/

/-- Flow one block-output value into the matching successor input. -/
def transferArg (s : AbsState cfg) (p : VarId × VarId) : AbsState cfg :=
  s.join p.2 (s.get p.1)

def transferOp (s : AbsState cfg) : Op → AbsState cfg
  | .const v w => s.join v (.const w)
  | .add32 r a b => s.join r (Value.binop (· + ·) (s.get a) (s.get b))
  | .lessThan r a b =>
      s.join r (Value.binop (fun x y => if x < y then 1 else 0) (s.get a) (s.get b))
  | .persistentLoad out _ => s.join out .overdefined
  | .persistentStore _ _ => s

/-- Mark an edge executable: the target becomes reachable and the source's
outputs flow into the target's inputs. -/
def transferEdge (s : AbsState cfg) (outputs : Array VarId) (dst : BasicBlockId) :
    AbsState cfg :=
  if h : dst.idx < cfg.blocks.size then
    (outputs.zip (cfg.blocks[dst.idx]'h).inputs).foldl transferArg
      (s.markReachable dst.idx h)
  else s

/-- The conditional part of SCCP: a `jump_if` on a known constant only makes
the taken edge executable, and on `undef` (terminator never executed) none. -/
def transferLast (s : AbsState cfg) (bb : BasicBlock) : AbsState cfg :=
  match bb.last with
  | .exit _ => s
  | .jump dst => transferEdge s bb.outputs dst
  | .jump_if j =>
    match s.get j.cond with
    | .undef => s
    | .const w =>
        transferEdge s bb.outputs (if w = 0 then j.dst_if_zero else j.dst_if_non_zero)
    | .overdefined =>
        transferEdge (transferEdge s bb.outputs j.dst_if_zero) bb.outputs j.dst_if_non_zero

def transferBlock (s : AbsState cfg) (b : Fin cfg.blocks.size) : AbsState cfg :=
  if s.reachable[b] then transferLast (cfg.blocks[b].ops.foldl transferOp s) cfg.blocks[b]
  else s

/-- One dense round: re-run the abstract transfer of every reachable block. -/
def step (s : AbsState cfg) : AbsState cfg :=
  (List.finRange cfg.blocks.size).foldl transferBlock s

/-! ### `step` is inflationary -/

theorem foldl_le {α β : Type*} [Preorder α] {f : α → β → α} (hf : ∀ a b, a ≤ f a b) :
    ∀ (l : List β) (a : α), a ≤ l.foldl f a := by
  intro l
  induction l with
  | nil => exact fun a => le_rfl
  | cons x xs ih => exact fun a => le_trans (hf a x) (ih (f a x))

theorem foldl_le_array {α β : Type*} [Preorder α] {f : α → β → α} (hf : ∀ a b, a ≤ f a b)
    (xs : Array β) (a : α) : a ≤ xs.foldl f a := by
  rw [← Array.foldl_toList]
  exact foldl_le hf xs.toList a

theorem le_transferArg (s : AbsState cfg) (p : VarId × VarId) : s ≤ transferArg s p :=
  AbsState.le_join s p.2 (s.get p.1)

theorem le_transferOp (s : AbsState cfg) (op : Op) : s ≤ transferOp s op := by
  cases op with
  | const v w => exact AbsState.le_join s v _
  | add32 r a b => exact AbsState.le_join s r _
  | lessThan r a b => exact AbsState.le_join s r _
  | persistentLoad out addr => exact AbsState.le_join s out _
  | persistentStore addr v => exact le_rfl

theorem le_transferEdge (s : AbsState cfg) (outputs : Array VarId) (dst : BasicBlockId) :
    s ≤ transferEdge s outputs dst := by
  unfold transferEdge
  split
  · rename_i h
    exact le_trans (AbsState.le_markReachable s dst.idx h)
      (foldl_le_array (fun a p => le_transferArg a p) _ _)
  · exact le_rfl

theorem le_transferLast (s : AbsState cfg) (bb : BasicBlock) : s ≤ transferLast s bb := by
  unfold transferLast
  split
  · exact le_rfl
  · exact le_transferEdge ..
  · split
    · exact le_rfl
    · exact le_transferEdge ..
    · exact le_trans (le_transferEdge ..) (le_transferEdge ..)

theorem le_transferBlock (s : AbsState cfg) (b : Fin cfg.blocks.size) :
    s ≤ transferBlock s b := by
  unfold transferBlock
  split
  · exact le_trans (foldl_le_array (fun a op => le_transferOp a op) _ _) (le_transferLast _ _)
  · exact le_rfl

theorem le_step (s : AbsState cfg) : s ≤ step s :=
  foldl_le (fun a b => le_transferBlock a b) _ s

/-! ## Fixpoint

No fuel: each non-fixpoint round strictly increases `score`, which is
bounded by `maxScore`, so the recursion is well-founded. -/

def solve (s : AbsState cfg) : AbsState cfg :=
  if _h : step s = s then s else solve (step s)
termination_by maxScore cfg - s.score
decreasing_by
  have hlt := AbsState.score_lt_of_lt (le_step s) (fun e => _h e.symm)
  have hmax := AbsState.score_le_maxScore (step s)
  omega

def analyze (cfg : ControlFlowGraph) : AbsState cfg :=
  solve (AbsState.init cfg)

/-! ## Rewriting

Fold ops whose result the analysis proved constant, and conditional jumps
whose condition it proved constant. Block shapes (inputs, outputs, defs)
and block indices are untouched. -/

def rewriteOp (σ : AbsState cfg) : Op → Op
  | .add32 r a b =>
    match σ.get r with
    | .const w => .const r w
    | _ => .add32 r a b
  | .lessThan r a b =>
    match σ.get r with
    | .const w => .const r w
    | _ => .lessThan r a b
  | op => op

def rewriteLast (σ : AbsState cfg) : EndOp → EndOp
  | .jump_if j =>
    match σ.get j.cond with
    | .const w => .jump (if w = 0 then j.dst_if_zero else j.dst_if_non_zero)
    | _ => .jump_if j
  | last => last

theorem rewriteOp_defs (σ : AbsState cfg) (op : Op) : (rewriteOp σ op).defs = op.defs := by
  cases op <;> simp only [rewriteOp] <;> (try split) <;> rfl

theorem rewriteOp_refs (σ : AbsState cfg) (op : Op) :
    ∀ r ∈ (rewriteOp σ op).refs, r ∈ op.refs := by
  intro r hr
  cases op <;> simp only [rewriteOp] at hr <;> first
    | exact hr
    | (split at hr
       · simp [Op.refs] at hr
       · exact hr)

theorem rewriteLast_successors (σ : AbsState cfg) (l : EndOp) :
    ∀ b ∈ (rewriteLast σ l).successors, b ∈ l.successors := by
  intro b hb
  cases l with
  | exit v => exact hb
  | jump d => exact hb
  | jump_if j =>
    simp only [rewriteLast] at hb
    split at hb
    · simp only [EndOp.successors] at hb ⊢
      split at hb <;> simp_all
    · exact hb

theorem rewriteLast_var_refs (σ : AbsState cfg) (l : EndOp) :
    ∀ r ∈ (rewriteLast σ l).var_refs, r ∈ l.var_refs := by
  intro r hr
  cases l with
  | exit v => exact hr
  | jump d => exact hr
  | jump_if j =>
    simp only [rewriteLast] at hr
    split at hr
    · simp [EndOp.var_refs] at hr
    · exact hr

theorem rewriteLast_outputs_match (σ : AbsState cfg) {outputs : Array VarId} {l : EndOp}
    (h : EndOp.outputs_match outputs l) :
    EndOp.outputs_match outputs (rewriteLast σ l) := by
  cases l with
  | exit v => exact h
  | jump d => exact h
  | jump_if j =>
    simp only [rewriteLast]
    split
    · trivial
    · exact h

def rewriteBlock (σ : AbsState cfg) (bb : BasicBlock) : BasicBlock where
  inputs := bb.inputs
  ops := bb.ops.map (rewriteOp σ)
  last := rewriteLast σ bb.last
  outputs := bb.outputs
  outputs_valid_for_last := rewriteLast_outputs_match σ bb.outputs_valid_for_last

theorem rewriteBlock_inputs (σ : AbsState cfg) (bb : BasicBlock) :
    (rewriteBlock σ bb).inputs = bb.inputs := rfl

theorem rewriteBlock_ops (σ : AbsState cfg) (bb : BasicBlock) :
    (rewriteBlock σ bb).ops = bb.ops.map (rewriteOp σ) := rfl

theorem rewriteBlock_last (σ : AbsState cfg) (bb : BasicBlock) :
    (rewriteBlock σ bb).last = rewriteLast σ bb.last := rfl

theorem rewriteBlock_outputs (σ : AbsState cfg) (bb : BasicBlock) :
    (rewriteBlock σ bb).outputs = bb.outputs := rfl

theorem rewriteBlock_defs (σ : AbsState cfg) (bb : BasicBlock) :
    (rewriteBlock σ bb).defs = bb.defs := by
  have hfun : (fun op => Op.defs (rewriteOp σ op)) = Op.defs := funext (rewriteOp_defs σ)
  show bb.inputs ++ (bb.ops.map (rewriteOp σ)).flatMap Op.defs
      = bb.inputs ++ bb.ops.flatMap Op.defs
  rw [Array.flatMap_map, hfun]

theorem rewriteBlock_defs_up_to (σ : AbsState cfg) (bb : BasicBlock)
    (i : Fin (rewriteBlock σ bb).ops.size) (h : i.val < bb.ops.size) :
    (rewriteBlock σ bb).defs_up_to i = bb.defs_up_to ⟨i.val, h⟩ := by
  have hfun : (fun op => Op.defs (rewriteOp σ op)) = Op.defs := funext (rewriteOp_defs σ)
  show bb.inputs ++ ((bb.ops.map (rewriteOp σ)).take i.val).flatMap Op.defs
      = bb.inputs ++ (bb.ops.take i.val).flatMap Op.defs
  rw [Array.take_eq_extract, ← Array.map_extract, Array.flatMap_map, hfun,
    ← Array.take_eq_extract]

theorem rewriteBlock_successors (σ : AbsState cfg) (bb : BasicBlock) :
    ∀ s ∈ (rewriteBlock σ bb).successors, s ∈ bb.successors :=
  rewriteLast_successors σ bb.last

/-! ## Reassembling a valid CFG -/

def rewriteBlocks (cfg : ControlFlowGraph) (σ : AbsState cfg) : Array BasicBlock :=
  cfg.blocks.map (rewriteBlock σ)

theorem size_rewriteBlocks (cfg : ControlFlowGraph) (σ : AbsState cfg) :
    (rewriteBlocks cfg σ).size = cfg.blocks.size :=
  Array.size_map

theorem getElem_rewriteBlocks (cfg : ControlFlowGraph) (σ : AbsState cfg)
    (i : Nat) (h : i < (rewriteBlocks cfg σ).size) :
    (rewriteBlocks cfg σ)[i]
      = rewriteBlock σ (cfg.blocks[i]'(size_rewriteBlocks cfg σ ▸ h)) :=
  Array.getElem_map ..

theorem rewriteBlocks_valid (cfg : ControlFlowGraph) (σ : AbsState cfg) :
    ∀ block ∈ rewriteBlocks cfg σ, block.valid_in_cfg (rewriteBlocks cfg σ) := by
  intro block hblock
  obtain ⟨bb, hbb, rfl⟩ := Array.mem_map.mp hblock
  intro succ hsucc
  obtain ⟨hlt, hsz⟩ := cfg.blocks_valid bb hbb succ (rewriteBlock_successors σ bb succ hsucc)
  refine ⟨by simpa [size_rewriteBlocks] using hlt, ?_⟩
  rw [getElem_rewriteBlocks]
  simpa [rewriteBlock_outputs, rewriteBlock_inputs] using hsz

/-- Rewritten edges are a subset of the original ones and defs are unchanged,
so any undef-path in the rewritten CFG already existed. -/
theorem pathWhereUndef_rewrite (cfg : ControlFlowGraph) (σ : AbsState cfg)
    {entry' : Fin (rewriteBlocks cfg σ).size}
    {valid' : ∀ block ∈ rewriteBlocks cfg σ, block.valid_in_cfg (rewriteBlocks cfg σ)}
    {var : VarId} {p q : Fin (rewriteBlocks cfg σ).size}
    (h : InnerCFG.PathWhereUndef ⟨rewriteBlocks cfg σ, entry', valid'⟩ var p q) :
    cfg.inner.PathWhereUndef var
      (Fin.cast (size_rewriteBlocks cfg σ) p) (Fin.cast (size_rewriteBlocks cfg σ) q) := by
  refine Relation.ReflTransGen.lift (Fin.cast (size_rewriteBlocks cfg σ)) ?_ h
  rintro a c ⟨hsucc, hdefs⟩
  have ha : a.val < cfg.blocks.size := by
    have := a.isLt
    simpa [size_rewriteBlocks] using this
  have hblk : (rewriteBlocks cfg σ)[a.val]'a.isLt
      = rewriteBlock σ (cfg.blocks[a.val]'ha) := getElem_rewriteBlocks cfg σ a.val a.isLt
  refine ⟨?_, ?_⟩
  · have hsucc' : (⟨(c : Nat)⟩ : BasicBlockId)
        ∈ (rewriteBlock σ (cfg.blocks[a.val]'ha)).successors := by
      rw [← hblk]
      exact hsucc
    exact rewriteBlock_successors σ _ _ hsucc'
  · have hd : var ∉ (rewriteBlock σ (cfg.blocks[a.val]'ha)).defs := by
      rw [← hblk]
      exact hdefs
    rw [rewriteBlock_defs] at hd
    exact hd

theorem definedOnAllPaths_rewrite (cfg : ControlFlowGraph) (σ : AbsState cfg)
    {entry' : Fin (rewriteBlocks cfg σ).size}
    {valid' : ∀ block ∈ rewriteBlocks cfg σ, block.valid_in_cfg (rewriteBlocks cfg σ)}
    (hentry : entry'.val = cfg.entry.val)
    {var : VarId} {bi : Fin (rewriteBlocks cfg σ).size}
    (h : cfg.inner.DefinedOnAllPaths var (Fin.cast (size_rewriteBlocks cfg σ) bi)) :
    InnerCFG.DefinedOnAllPaths ⟨rewriteBlocks cfg σ, entry', valid'⟩ var bi := by
  intro hpath
  apply h
  have hp : cfg.inner.PathWhereUndef var
      (Fin.cast (size_rewriteBlocks cfg σ) entry')
      (Fin.cast (size_rewriteBlocks cfg σ) bi) := pathWhereUndef_rewrite cfg σ hpath
  have hcast : cfg.inner.entry = Fin.cast (size_rewriteBlocks cfg σ) entry' := by
    apply Fin.ext
    simpa using hentry.symm
  rw [hcast]
  exact hp

theorem rewriteCFG_refs_valid (cfg : ControlFlowGraph) (σ : AbsState cfg)
    (entry' : Fin (rewriteBlocks cfg σ).size) (hentry : entry'.val = cfg.entry.val)
    (valid' : ∀ block ∈ rewriteBlocks cfg σ, block.valid_in_cfg (rewriteBlocks cfg σ)) :
    InnerCFG.refs_valid ⟨rewriteBlocks cfg σ, entry', valid'⟩ := by
  obtain ⟨hop, hend, hout⟩ := cfg.refs_valid
  refine ⟨?_, ?_, ?_⟩
  · intro bi
    have hbi : bi.val < cfg.blocks.size := by
      have := bi.isLt
      simpa [size_rewriteBlocks] using this
    suffices H : ∀ b : BasicBlock, b = rewriteBlock σ (cfg.blocks[bi.val]'hbi) →
        ∀ opi : Fin b.ops.size, ∀ ref ∈ b.ops[opi].refs,
          ref ∈ b.defs_up_to opi
            ∨ InnerCFG.DefinedOnAllPaths ⟨rewriteBlocks cfg σ, entry', valid'⟩ ref bi by
      intro opi ref href
      exact H _ (getElem_rewriteBlocks cfg σ bi.val bi.isLt) opi ref href
    rintro b rfl opi ref href
    have hsize : opi.val < (cfg.blocks[bi.val]'hbi).ops.size := by
      have := opi.isLt
      simpa [rewriteBlock_ops] using this
    have href' : ref ∈ ((cfg.blocks[bi.val]'hbi).ops[opi.val]'hsize).refs := by
      apply rewriteOp_refs
      have hgo : (rewriteBlock σ (cfg.blocks[bi.val]'hbi)).ops[opi.val]'opi.isLt
          = rewriteOp σ ((cfg.blocks[bi.val]'hbi).ops[opi.val]'hsize) := by
        simp [rewriteBlock_ops]
      rw [Fin.getElem_fin, hgo] at href
      exact href
    rcases hop ⟨bi.val, hbi⟩ ⟨opi.val, hsize⟩ ref href' with hd | hp
    · left
      rw [rewriteBlock_defs_up_to σ _ opi hsize]
      exact hd
    · right
      exact definedOnAllPaths_rewrite cfg σ hentry hp
  · intro bi
    have hbi : bi.val < cfg.blocks.size := by
      have := bi.isLt
      simpa [size_rewriteBlocks] using this
    suffices H : ∀ b : BasicBlock, b = rewriteBlock σ (cfg.blocks[bi.val]'hbi) →
        ∀ ref ∈ b.last.var_refs,
          ref ∈ b.defs
            ∨ InnerCFG.DefinedOnAllPaths ⟨rewriteBlocks cfg σ, entry', valid'⟩ ref bi by
      intro ref href
      exact H _ (getElem_rewriteBlocks cfg σ bi.val bi.isLt) ref href
    rintro b rfl ref href
    have href' : ref ∈ (cfg.blocks[bi.val]'hbi).last.var_refs :=
      rewriteLast_var_refs σ _ ref (by simpa [rewriteBlock_last] using href)
    rcases hend ⟨bi.val, hbi⟩ ref href' with hd | hp
    · left
      rw [rewriteBlock_defs]
      exact hd
    · right
      exact definedOnAllPaths_rewrite cfg σ hentry hp
  · intro bi
    have hbi : bi.val < cfg.blocks.size := by
      have := bi.isLt
      simpa [size_rewriteBlocks] using this
    suffices H : ∀ b : BasicBlock, b = rewriteBlock σ (cfg.blocks[bi.val]'hbi) →
        ∀ ref ∈ b.outputs,
          ref ∈ b.defs
            ∨ InnerCFG.DefinedOnAllPaths ⟨rewriteBlocks cfg σ, entry', valid'⟩ ref bi by
      intro ref href
      exact H _ (getElem_rewriteBlocks cfg σ bi.val bi.isLt) ref href
    rintro b rfl ref href
    have href' : ref ∈ (cfg.blocks[bi.val]'hbi).outputs := by
      simpa [rewriteBlock_outputs] using href
    rcases hout ⟨bi.val, hbi⟩ ref href' with hd | hp
    · left
      rw [rewriteBlock_defs]
      exact hd
    · right
      exact definedOnAllPaths_rewrite cfg σ hentry hp

def rewriteCFG (cfg : ControlFlowGraph) (σ : AbsState cfg) : ControlFlowGraph where
  blocks := rewriteBlocks cfg σ
  entry := Fin.cast (size_rewriteBlocks cfg σ).symm cfg.entry
  entry_no_inputs := by
    simp only [Fin.getElem_fin, Fin.val_cast]
    rw [getElem_rewriteBlocks]
    simpa [rewriteBlock_inputs] using cfg.entry_no_inputs
  blocks_valid := rewriteBlocks_valid cfg σ
  refs_valid := rewriteCFG_refs_valid cfg σ _ (by simp) (rewriteBlocks_valid cfg σ)

theorem rewriteCFG_is_ssa (cfg : ControlFlowGraph) (σ : AbsState cfg)
    (h : cfg.is_ssa) : (rewriteCFG cfg σ).is_ssa := by
  have hfun : (fun b => BasicBlock.defs (rewriteBlock σ b)) = BasicBlock.defs :=
    funext (rewriteBlock_defs σ)
  show ((cfg.blocks.map (rewriteBlock σ)).flatMap BasicBlock.defs).toList.Nodup
  rw [Array.flatMap_map, hfun]
  exact h

/-! ## The pass -/

def run_sccp (cfg : SSACFG) : SSACFG :=
  ⟨rewriteCFG cfg.val (analyze cfg.val),
    rewriteCFG_is_ssa cfg.val (analyze cfg.val) cfg.property⟩

/-! ## Sanity checks -/

/-- All references resolve within their own block, so the (undecidable)
`DefinedOnAllPaths` disjunct is never needed. -/
theorem refs_valid_of_local (icfg : InnerCFG)
    (hop : ∀ bi : Fin icfg.blocks.size, ∀ opi : Fin icfg.blocks[bi].ops.size,
      ∀ ref ∈ icfg.blocks[bi].ops[opi].refs,
        ref ∈ (icfg.blocks[bi].defs_up_to opi).toList)
    (hend : ∀ bi : Fin icfg.blocks.size, ∀ ref ∈ icfg.blocks[bi].last.var_refs.toList,
      ref ∈ icfg.blocks[bi].defs.toList)
    (hout : ∀ bi : Fin icfg.blocks.size, ∀ ref ∈ icfg.blocks[bi].outputs.toList,
      ref ∈ icfg.blocks[bi].defs.toList) :
    icfg.refs_valid := by
  refine ⟨fun bi opi ref href => Or.inl ?_, fun bi ref href => Or.inl ?_,
    fun bi ref href => Or.inl ?_⟩
  · simpa using hop bi opi ref href
  · simpa using hend bi ref (by simpa using href)
  · simpa using hout bi ref (by simpa using href)

/-- Entry jumps on a constant condition to block 1, which computes `41 + 1`;
block 2 is therefore unreachable. -/
private def testBlocks : Array BasicBlock := #[
  { inputs := #[]
    ops := #[.const ⟨0⟩ 0]
    last := .jump_if ⟨⟨0⟩, ⟨1⟩, ⟨2⟩⟩
    outputs := #[] },
  { inputs := #[]
    ops := #[.const ⟨1⟩ 41, .const ⟨2⟩ 1, .add32 ⟨3⟩ ⟨1⟩ ⟨2⟩]
    last := .exit ⟨3⟩
    outputs := #[] },
  { inputs := #[]
    ops := #[.const ⟨5⟩ 7, .persistentLoad ⟨4⟩ ⟨5⟩]
    last := .exit ⟨4⟩
    outputs := #[] }]

private def testCFG : ControlFlowGraph := {
  blocks := testBlocks
  entry := ⟨0, by decide⟩
  entry_no_inputs := by decide
  blocks_valid := by
    simp only [BasicBlock.valid_in_cfg]
    decide
  refs_valid := refs_valid_of_local _ (by decide) (by decide) (by decide)
}

private def testSSA : SSACFG :=
  ⟨testCFG, by show (testCFG.blocks.flatMap BasicBlock.defs).toList.Nodup; decide⟩

#guard (analyze testCFG).reachable.toList = [true, true, false]

#guard ((run_sccp testSSA).val.blocks.map BasicBlock.ops) = #[
  #[.const ⟨0⟩ 0],
  #[.const ⟨1⟩ 41, .const ⟨2⟩ 1, .const ⟨3⟩ 42],
  #[.const ⟨5⟩ 7, .persistentLoad ⟨4⟩ ⟨5⟩]]

#guard ((run_sccp testSSA).val.blocks.map BasicBlock.last)
  = #[.jump ⟨1⟩, .exit ⟨3⟩, .exit ⟨4⟩]

end Sir.SCCP
