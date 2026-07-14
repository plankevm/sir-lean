import Evm
import Batteries.Data.RBMap
import Batteries.Classes.Order
import BytecodeLayer.Semantics.Maps
import BytecodeLayer.Hoare.AccountMap
import BytecodeLayer.Semantics.System

/-!
# `RBMap` erase read-back bricks (proof-internal)

`Evm.Storage = Batteries.RBMap UInt256 UInt256 compare`, and clearing a slot
(`SSTORE key 0`) is implemented as `Account.updateStorage key 0`, which — because
`0 == default` — takes the **erase** branch: `storage := storage.erase key`.

Reading the effect back through the `find?/findD` lens therefore needs the value
characterisation of `RBMap.erase`, which Batteries deliberately does **not**
provide (it proves `del`'s ordering/balance preservation and the *insert*
membership lemmas, but no `find?_erase`). This file supplies exactly the two
equations the zero-write SSTORE rule needs:

* `Evm.Storage.findD_erase_self`  — the cleared slot reads back `0`;
* `Evm.Storage.findD_erase_of_ne` — every **other** slot is unchanged.

They are derived bottom-up from a `toList` characterisation of `erase` (via
Batteries' `zoom`/`del` machinery), with no new axioms
(`[propext, Classical.choice, Quot.sound]` only). These are pure data-structure
facts; they mention no EVM execution concept.
-/

namespace Batteries.RBNode
open RBColor

universe u

variable {α : Type u} {cmp : α → α → Ordering} {cut cut2 : α → Ordering}

/-- `append`'s inorder traversal is the concatenation of its arguments'. -/
theorem append_toList (l r : RBNode α) :
    (append l r).toList = l.toList ++ r.toList := by
  fun_induction append l r <;>
    simp_all only [balLeft_toList, toList_node, toList_nil,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil] <;>
    grind

/-- `Path.del` rebuilds the tree filling the hole with `t`'s inorder list. -/
theorem Path.del_toList (p : Path α) (t : RBNode α) (c : RBColor) :
    (p.del t c).toList = p.withList t.toList := by
  induction p generalizing t c with
  | root => cases c <;> simp [Path.del, Path.withList, Path.listL, Path.listR, setBlack_toList]
  | left c' parent y b ih =>
    cases c <;>
      · simp only [Path.del, ih, Path.withList, Path.listL, Path.listR,
          balLeft_toList, toList_node, List.append_assoc, List.cons_append]
  | right c' a y parent ih =>
    cases c <;>
      · simp only [Path.del, ih, Path.withList, Path.listL, Path.listR,
          balRight_toList, toList_node, List.append_assoc, List.cons_append, List.nil_append]

/-- The inorder list of `erase cut t`, expressed through the `zoom` of the cut:
the hole `t'` (the located subtree) contributes `t'.delRoot` (its root removed),
filled back into the path. -/
theorem erase_toList_zoom {t t' : RBNode α} {p' : Path α}
    (e : t.zoom cut = (t', p')) :
    (t.erase cut).toList = p'.withList t'.delRoot.toList := by
  have hzd := Path.zoom_del (path := .root) e
  simp only [Path.del] at hzd
  show (t.del cut).setBlack.toList = _
  rw [hzd, Path.del_toList]

/-- **Membership after erase.** In an ordered tree, `x` survives `erase cut t`
iff it was present and does *not* match the cut. (`IsStrictCut` makes the matching
element unique, so `erase` removes exactly it.) -/
theorem mem_erase [Std.TransCmp cmp] [IsStrictCut cmp cut]
    {t : RBNode α} (ht : t.Ordered cmp) {x : α} :
    x ∈ t.erase cut ↔ (x ∈ t ∧ cut x ≠ .eq) := by
  obtain ⟨t', p', e⟩ : ∃ t' p', t.zoom cut = (t', p') := ⟨_, _, rfl⟩
  have hetl := erase_toList_zoom e
  have httl : t.toList = p'.withList t'.toList := (zoom_toList e).symm
  cases t' with
  | nil =>
    -- element not found: erase is a no-op on the list, and nothing matches the cut
    have hnf : t.find? cut = none := by rw [find?_eq_zoom (p := .root), e]; rfl
    have hnomatch : ∀ y ∈ t, cut y ≠ .eq := by
      intro y hy hcy
      exact absurd (ht.memP_iff_find?.1 (memP_def.2 ⟨y, hy, hcy⟩)) (by simp [hnf])
    have hlist : (t.erase cut).toList = t.toList := by
      rw [hetl, httl]; simp [delRoot]
    constructor
    · intro hx
      have hxt : x ∈ t := mem_toList.1 (hlist ▸ mem_toList.2 hx)
      exact ⟨hxt, hnomatch x hxt⟩
    · exact fun ⟨hx, _⟩ => mem_toList.1 (hlist ▸ mem_toList.2 hx)
  | node c a w b =>
    have hcw : cut w = .eq := by
      have := Path.zoom_zoomed₁ (path := .root) e; simpa using this
    have hwmem : w ∈ t :=
      mem_toList.1 (by rw [httl]; simp [Path.withList, toList_node])
    -- flattened membership on both lists, for an arbitrary element `z`
    have hE : ∀ z, z ∈ (t.erase cut).toList ↔
        z ∈ p'.listL ∨ z ∈ a.toList ∨ z ∈ b.toList ∨ z ∈ p'.listR := by
      intro z
      rw [hetl]; simp [Path.withList, delRoot, append_toList, List.mem_append]
    have hT : ∀ z, z ∈ t.toList ↔
        z ∈ p'.listL ∨ z ∈ a.toList ∨ z = w ∨ z ∈ b.toList ∨ z ∈ p'.listR := by
      intro z
      rw [httl]; simp [Path.withList, toList_node, List.mem_append, List.mem_cons]
    -- w does not reappear in the erased list (sortedness ⇒ no duplicate)
    have hsorted : (t.toList).Pairwise (cmpLT cmp) := ht.toList_sorted
    have hself : cmp w w = .eq := Std.ReflCmp.compare_self (cmp := cmp)
    have hwnotE : w ∉ (t.erase cut).toList := by
      intro hw
      have hwdup : w ∈ p'.listL ∨ w ∈ a.toList ∨ w ∈ b.toList ∨ w ∈ p'.listR := (hE w).1 hw
      have hsplit : t.toList = (p'.listL ++ a.toList) ++ w :: (b.toList ++ p'.listR) := by
        rw [httl]; simp [Path.withList, toList_node, List.append_assoc]
      rw [hsplit, List.pairwise_append] at hsorted
      obtain ⟨_, hpc, hcross⟩ := hsorted
      rw [List.pairwise_cons] at hpc
      obtain ⟨hhead, _⟩ := hpc
      have hbad : cmpLT cmp w w := by
        rcases hwdup with h | h | h | h
        · exact hcross w (List.mem_append_left _ h) w (List.mem_cons_self ..)
        · exact hcross w (List.mem_append_right _ h) w (List.mem_cons_self ..)
        · exact hhead w (List.mem_append_left _ h)
        · exact hhead w (List.mem_append_right _ h)
      rw [cmpLT_iff, hself] at hbad
      exact absurd hbad (by decide)
    constructor
    · intro hx
      have hxmemE : x ∈ (t.erase cut).toList := mem_toList.2 hx
      have hxt : x ∈ t := mem_toList.1 (by
        rw [hT]
        rcases (hE x).1 hxmemE with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      refine ⟨hxt, ?_⟩
      intro hcx
      have hxweq : cmp x w = .eq := by
        have h := IsStrictCut.exact (cmp := cmp) hcx (y := w); rw [hcw] at h; exact h
      have hxw : x = w := ht.unique hxt hwmem hxweq
      exact hwnotE (hxw ▸ hxmemE)
    · intro ⟨hx, hcx⟩
      have hxt : x ∈ t.toList := mem_toList.2 hx
      refine mem_toList.1 ((hE x).2 ?_)
      rcases (hT x).1 hxt with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd (h ▸ hcw) hcx
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))

/-- **Self read-back after erase.** Reading the just-erased cut returns nothing. -/
theorem find?_erase_self [Std.TransCmp cmp] [IsStrictCut cmp cut]
    {t : RBNode α} (ht : t.Ordered cmp) : (t.erase cut).find? cut = none := by
  cases hf : (t.erase cut).find? cut with
  | none => rfl
  | some x =>
    exact absurd (find?_some_eq_eq hf) ((mem_erase ht).1 (find?_some_mem hf)).2

/-- **Framing read-back after erase.** A cut `cut2` disjoint from the erased cut
(no present element matches both) reads exactly what it read before. -/
theorem find?_erase_of_ne [Std.TransCmp cmp] [IsStrictCut cmp cut] [IsStrictCut cmp cut2]
    {t : RBNode α} (ht : t.Ordered cmp)
    (hdisj : ∀ z ∈ t, cut2 z = .eq → cut z ≠ .eq) :
    (t.erase cut).find? cut2 = t.find? cut2 := by
  have hto : (t.erase cut).Ordered cmp := ht.erase
  cases hf : t.find? cut2 with
  | none =>
    cases hf2 : (t.erase cut).find? cut2 with
    | none => rfl
    | some x =>
      exfalso
      have hxt : x ∈ t := ((mem_erase ht).1 (find?_some_mem hf2)).1
      obtain ⟨y, hy⟩ := ht.memP_iff_find?.1 (memP_def.2 ⟨x, hxt, find?_some_eq_eq hf2⟩)
      rw [hf] at hy; exact absurd hy (by simp)
  | some x =>
    have hxt : x ∈ t := find?_some_mem hf
    have hcx : cut2 x = .eq := find?_some_eq_eq hf
    have hxe : x ∈ t.erase cut := (mem_erase ht).2 ⟨hxt, hdisj x hxt hcx⟩
    exact (hto.find?_some (cut := cut2)).2 ⟨hxe, hcx⟩

end Batteries.RBNode

/-! ## Storage-map specialisation (`Evm.Storage = RBMap UInt256 UInt256 compare`) -/

namespace Evm.Storage
open Batteries

/-- Reading a slot after **clearing** it (`erase`) returns the default `0`. -/
theorem findD_erase_self (s : Storage) (k : UInt256) :
    (s.erase k).findD k 0 = 0 := by
  have hord : s.1.Ordered (Ordering.byKey Prod.fst compare) := s.2.out.1
  have hnone : (s.1.erase (fun p => compare k p.1)).find? (fun p => compare k p.1) = none :=
    RBNode.find?_erase_self hord
  show (((s.erase k).findEntry? k).map (·.2)).getD 0 = 0
  simp only [RBMap.findEntry?, RBSet.findP?, RBMap.erase, RBSet.erase, hnone,
    Option.map_none, Option.getD_none]

/-- Reading **another** slot after clearing `k` returns its old value. -/
theorem findD_erase_of_ne (s : Storage) {k' k : UInt256} (h : k' ≠ k) :
    (s.erase k).findD k' 0 = s.findD k' 0 := by
  have hord : s.1.Ordered (Ordering.byKey Prod.fst compare) := s.2.out.1
  have hdisj : ∀ z ∈ s.1, (fun p => compare k' p.1) z = .eq → (fun p => compare k p.1) z ≠ .eq := by
    intro z _ hz
    -- `compare k' z.1 = eq ⇒ z.1 = k'`; then `compare k z.1 = compare k k' ≠ eq`
    have hzk' : z.1 = k' := by
      by_contra hne
      exact (BytecodeLayer.Maps.uint256_compare_ne_eq_of_ne (fun he => hne he.symm)) hz
    show compare k z.1 ≠ Ordering.eq
    rw [hzk']
    exact BytecodeLayer.Maps.uint256_compare_ne_eq_of_ne (Ne.symm h)
  have hfr : (s.1.erase (fun p => compare k p.1)).find? (fun p => compare k' p.1)
      = s.1.find? (fun p => compare k' p.1) :=
    RBNode.find?_erase_of_ne hord hdisj
  show (((s.erase k).findEntry? k').map (·.2)).getD 0 = ((s.findEntry? k').map (·.2)).getD 0
  simp only [RBMap.findEntry?, RBSet.findP?, RBMap.erase, RBSet.erase, hfr]

end Evm.Storage

namespace BytecodeLayer.Exec.Invariants

open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Maps
open BytecodeLayer.System

def SelfPresent (fr : Frame) : Prop :=
  ∃ acc : Account, fr.exec.accounts.find? fr.exec.executionEnv.address = some acc

theorem accounts_ne_empty_of_selfPresent {fr : Frame} (h : SelfPresent fr) :
    ¬ (fr.exec.accounts == (∅ : Evm.AccountMap)) = true := by
  obtain ⟨acc, hf⟩ := h
  exact find?_some_ne_empty _ _ _ hf

theorem resumeAfterCall_self_of_accounts (result : Evm.CallResult) (pd : Evm.PendingCall)
    (h : ∃ acc, result.accounts.find? pd.frame.exec.executionEnv.address = some acc) :
    SelfPresent (Evm.resumeAfterCall result pd) := h

theorem selfPresent_codeFrame (params : Evm.CallParams) (code : ByteArray) {acc : Account}
    (hwf : params.accounts.find? params.recipient = some acc) :
    SelfPresent (codeFrame params code) := by
  show ∃ a, (codeAccounts params).find? params.recipient = some a
  unfold codeAccounts
  simp only [hwf]
  have hrec₁ : (params.accounts.insert params.recipient
        { acc with balance := acc.balance + params.value }).find? params.recipient
      = some { acc with balance := acc.balance + params.value } :=
    accounts_find?_insert_self params.accounts params.recipient _
  cases hcal : (params.accounts.insert params.recipient
      { acc with balance := acc.balance + params.value }).find? params.caller with
  | none => exact ⟨_, hrec₁⟩
  | some cacc =>
    by_cases hcr : params.caller = params.recipient
    · rw [hcr]; exact ⟨_, accounts_find?_insert_self _ params.recipient _⟩
    · rw [accounts_find?_insert_of_ne _ _ (fun hc => hcr hc.symm)]
      exact ⟨_, hrec₁⟩

end BytecodeLayer.Exec.Invariants
