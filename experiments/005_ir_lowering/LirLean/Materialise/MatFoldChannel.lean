import LirLean.Spec.WellFormed
import LirLean.Materialise.MatDecLower

open Lir.Frame

/-! # `MatFoldChannel` — the charge fold twin's fixpoint + the chargeCache↔matCache lockstep

Phase 2A P5a. The fuel-free charge fold twin `chargeCache` (definition, reduction lemmas, and the
`sloadChg`-length-independence `chargeCache_length_sloadChg_eq` all live in
`Materialise/MaterialiseGas.lean`, kept BELOW `Spec/WellFormed.lean` in the import DAG so the
`StackRoomOK`/`maxChargeDepth` stack-room folds there can read the charge fold) gets HERE its
**fold fixpoint** `chargeCache_unfold` — the exact twin of `matCache_unfold`
(`Spec/WellFormed.lean` §P3) — proved by the SAME def-env induction (`DefsConsistent` +
`DefEnvOrdered`), reusing that section's *Loc-level* def-env machinery
(`matCache_last_eq_first`, `defEnv_findIdx_entry`, `defEnv_operand_findIdx_lt`, `operand_mem_take`)
verbatim: those facts are about which entry defines a tmp and where its operands sit, independent
of whether the cache carries bytes (`matCache`) or charge lists (`chargeCache`). No fuel, no
fuel predicates, and no bridge to the deleted fuel materialisation path.

The **chargeCache↔matCache length lockstep** (bottom): for a `t` present in `defEnv prog`, the
charge cache and the byte cache unfold *in lockstep* — the SAME membership hypothesis
`(t, loc) ∈ defEnv prog` drives parallel `chargeExpr`/`matExpr` (resp. `.slot` / absent)
conclusions — so the future fuel-free restatement of the `StackRoomOK`/`maxChargeDepth` folds and
the P5 `materialise_runsC` recursion can read a charge-list LENGTH that decomposes exactly as
`matCache prog t`'s operand structure does. -/

namespace Lir

/-! ### Operand-locality of `chargeExpr` (the `matExpr_congr` twin) -/

/-- **Operand-locality of `chargeExpr`.** `chargeExpr` reads its cache only at the tmps the
expression uses, so two caches agreeing on every used tmp emit identical charge lists (the
`matExpr_congr` twin; drives the `.remat` step of `chargeCache_unfold`). -/
theorem chargeExpr_congr {sc : Tmp → ℕ} {c c' : Tmp → List ℕ} {e : Expr}
    (h : ∀ t, usesInExpr t e ≠ 0 → c t = c' t) : chargeExpr sc c e = chargeExpr sc c' e := by
  cases e with
  | imm w => rfl
  | gas => rfl
  | tmp t => simp only [chargeExpr_tmp]; exact h t (by simp [usesInExpr])
  | add a b =>
      simp only [chargeExpr_add]
      rw [h a (by simp [usesInExpr]), h b (by simp [usesInExpr])]
  | lt a b =>
      simp only [chargeExpr_lt]
      rw [h a (by simp [usesInExpr]), h b (by simp [usesInExpr])]
  | sload k => simp only [chargeExpr_sload]; rw [h k (by simp [usesInExpr])]

/-! ### `chargeFold` structural readouts (the `matFold_notMem`/`matFold_split` twins) -/

/-- **A `chargeFold` that never rebinds `t` leaves `t` at its initial value** (`matFold_notMem`
twin). -/
theorem chargeFold_notMem (sc : Tmp → ℕ) {t : Tmp} :
    ∀ (l : List (Tmp × Loc)) (c : Tmp → List ℕ),
      t ∉ l.map Prod.fst → chargeFold sc c l t = c t
  | [], _, _ => rfl
  | p :: l, c, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [chargeFold_cons, chargeFold_notMem sc l (chargeStep sc c p) h.2]
      exact Function.update_of_ne h.1 _ _

/-- **Last-occurrence split of a `chargeFold` value** (`matFold_split` twin). Either `t` is never
a key (fold value = initial), or the list splits at `t`'s LAST occurrence and the fold value at
`t` is `chargeLoc` of that entry's `Loc` under the prefix-fold. The readout of the last-wins
`Function.update` fold. -/
theorem chargeFold_split (sc : Tmp → ℕ) (c : Tmp → List ℕ) (t : Tmp) :
    ∀ (l : List (Tmp × Loc)),
      (t ∉ l.map Prod.fst ∧ chargeFold sc c l t = c t) ∨
      (∃ pre loc post, l = pre ++ (t, loc) :: post ∧ t ∉ post.map Prod.fst ∧
         chargeFold sc c l t = chargeLoc sc (chargeFold sc c pre) loc) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => exact Or.inl ⟨by simp, rfl⟩
  | append_singleton l x ih =>
      have hval : chargeFold sc c (l ++ [x]) t
          = if t = x.1 then chargeLoc sc (chargeFold sc c l) x.2 else chargeFold sc c l t := by
        have hfold : chargeFold sc c (l ++ [x]) = chargeStep sc (chargeFold sc c l) x := by
          simp only [chargeFold, List.foldl_append]; rfl
        rw [hfold]; simp only [chargeStep, Function.update_apply]
      by_cases hx : t = x.1
      · refine Or.inr ⟨l, x.2, [], ?_, by simp, ?_⟩
        · have hxe : x = (t, x.2) := by rw [hx]
          rw [hxe]
        · rw [hval, if_pos hx]
      · cases ih with
        | inl h =>
            refine Or.inl ⟨?_, ?_⟩
            · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨h.1, hx⟩
            · rw [hval, if_neg hx]; exact h.2
        | inr h =>
            obtain ⟨pre, loc, post, heq, hpost, hvv⟩ := h
            refine Or.inr ⟨pre, loc, post ++ [x], ?_, ?_, ?_⟩
            · rw [heq, List.append_assoc, List.cons_append]
            · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨hpost, hx⟩
            · rw [hval, if_neg hx]; exact hvv

/-! ### Prefix stability (the `matFold_take_eq_matCache` twin) -/

/-- **Prefix stability of `chargeCache`** — the induction engine of `chargeCache_unfold`
(`matFold_take_eq_matCache` twin). Any def-env prefix already containing an occurrence of `t'`
agrees with the full `chargeCache` at `t'`. Well-founded on `t'`'s first index (`DefEnvOrdered`
via `defEnv_operand_findIdx_lt`); SSA single-binding (`matCache_last_eq_first`) aligns the two
last-occurrence entries; operand-locality (`chargeExpr_congr`) closes the `.remat` step. Reuses
the Loc-level def-env facts of the byte channel verbatim. -/
theorem chargeFold_take_eq_chargeCache (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog) :
    ∀ (t' : Tmp) (p : Nat), t' ∈ ((defEnv prog).take p).map Prod.fst →
      chargeFold sc chargeInit ((defEnv prog).take p) t' = chargeCache prog sc t' := by
  have key : ∀ (n : Nat) (t' : Tmp),
      (defEnv prog).findIdx (fun p => p.1 == t') = n →
      ∀ (p : Nat), t' ∈ ((defEnv prog).take p).map Prod.fst →
        chargeFold sc chargeInit ((defEnv prog).take p) t' = chargeCache prog sc t' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t' hn p hmem
      have hmemFull : t' ∈ (defEnv prog).map Prod.fst := by
        obtain ⟨y, hy, hy2⟩ := List.mem_map.mp hmem
        exact List.mem_map.mpr ⟨y, List.take_subset p _ hy, hy2⟩
      rcases chargeFold_split sc chargeInit t' ((defEnv prog).take p) with hA | hA
      · exact absurd hmem hA.1
      obtain ⟨preA, locA, postA, hsplitA, _hpostA, hvalA⟩ := hA
      rcases chargeFold_split sc chargeInit t' (defEnv prog) with hB | hB
      · exact absurd hmemFull hB.1
      obtain ⟨preB, locB, postB, hsplitB, _hpostB, hvalB⟩ := hB
      have hmemA : (t', locA) ∈ defEnv prog :=
        List.take_subset p _ (by rw [hsplitA]; simp)
      have hmemB : (t', locB) ∈ defEnv prog := by rw [hsplitB]; simp
      have hll : locA = locB := matCache_last_eq_first prog hdc hmemA hmemB
      rw [hvalA, chargeCache_eq_chargeFold, hvalB, ← hll]
      have hpreA : preA = (defEnv prog).take preA.length := by
        have h1 : preA <+: (defEnv prog).take p := by
          rw [hsplitA]; exact List.prefix_append _ _
        exact List.prefix_iff_eq_take.mp (h1.trans (List.take_prefix p _))
      have hpreB : preB = (defEnv prog).take preB.length := by
        have h1 : preB <+: defEnv prog := by rw [hsplitB]; exact List.prefix_append _ _
        exact List.prefix_iff_eq_take.mp h1
      have hlenA : preA.length < p := by
        have hlen : ((defEnv prog).take p).length ≤ p := by
          rw [List.length_take]; exact Nat.min_le_left _ _
        rw [hsplitA] at hlen
        simp only [List.length_append, List.length_cons] at hlen
        omega
      have hgetA : (defEnv prog)[preA.length]? = some (t', locA) := by
        have h0 : ((defEnv prog).take p)[preA.length]? = some (t', locA) := by
          rw [hsplitA, List.getElem?_append_right (Nat.le_refl _)]; simp
        rwa [List.getElem?_take_of_lt hlenA] at h0
      have hgetB : (defEnv prog)[preB.length]? = some (t', locB) := by
        rw [hsplitB, List.getElem?_append_right (Nat.le_refl _)]; simp
      cases locA with
      | slot n => rfl
      | remat e =>
          simp only [chargeLoc_remat]
          apply chargeExpr_congr
          intro t'' hu
          have hlt : (defEnv prog).findIdx (fun p => p.1 == t'') < n := by
            rw [← hn]
            exact defEnv_operand_findIdx_lt hord (defEnv_findIdx_entry prog hdc hmemA) hu
          have hmemA'' : t'' ∈ ((defEnv prog).take preA.length).map Prod.fst :=
            operand_mem_take hord hgetA hu
          have hgetB' : (defEnv prog)[preB.length]? = some (t', Loc.remat e) := by
            rw [hgetB, hll]
          have hmemB'' : t'' ∈ ((defEnv prog).take preB.length).map Prod.fst :=
            operand_mem_take hord hgetB' hu
          have hAeq := ih _ hlt t'' rfl preA.length hmemA''
          have hBeq := ih _ hlt t'' rfl preB.length hmemB''
          rw [← hpreA] at hAeq
          rw [← hpreB] at hBeq
          rw [hAeq, hBeq]
  intro t' p hmem
  exact key _ t' rfl p hmem

/-! ### The fold fixpoint `chargeCache_unfold` (the `matCache_unfold` twin) -/

/-- **`chargeCache_unfold` — the charge fold fixpoint.** For a `t` PRESENT in `defEnv prog`, the
charge list of `t` is `chargeLoc` of its (unique, SSA-canonical) `Loc` resolved under the FULL
charge cache. The exact twin of `matCache_unfold`; proved from the prefix-stability engine, NO
fold↔fuel bridge. -/
theorem chargeCache_unfold (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {loc : Loc} (hmem : (t, loc) ∈ defEnv prog) :
    chargeCache prog sc t = chargeLoc sc (chargeCache prog sc) loc := by
  rcases chargeFold_split sc chargeInit t (defEnv prog) with hB | hB
  · exact absurd (List.mem_map.mpr ⟨(t, loc), hmem, rfl⟩) hB.1
  obtain ⟨preB, locB, postB, hsplitB, _hpostB, hvalB⟩ := hB
  have hmemB : (t, locB) ∈ defEnv prog := by rw [hsplitB]; simp
  have hll : loc = locB := matCache_last_eq_first prog hdc hmem hmemB
  rw [chargeCache_eq_chargeFold, hvalB, hll]
  have hpreB : preB = (defEnv prog).take preB.length := by
    have h1 : preB <+: defEnv prog := by rw [hsplitB]; exact List.prefix_append _ _
    exact List.prefix_iff_eq_take.mp h1
  have hgetB : (defEnv prog)[preB.length]? = some (t, locB) := by
    rw [hsplitB, List.getElem?_append_right (Nat.le_refl _)]; simp
  cases locB with
  | slot n => rfl
  | remat e =>
      simp only [chargeLoc_remat]
      apply chargeExpr_congr
      intro t'' hu
      have hgetB' : (defEnv prog)[preB.length]? = some (t, Loc.remat e) := hgetB
      have hmem'' : t'' ∈ ((defEnv prog).take preB.length).map Prod.fst :=
        operand_mem_take hord hgetB' hu
      have heq := chargeFold_take_eq_chargeCache prog sc hdc hord t'' preB.length hmem''
      rw [← hpreB] at heq
      rw [heq, chargeCache_eq_chargeFold]

/-- **Corollary — rematerialised tmp.** The charge list of a `.remat e` tmp is `chargeExpr` of `e`
under the full cache (the `matCache_remat` twin). -/
theorem chargeCache_remat (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {e : Expr} (hmem : (t, Loc.remat e) ∈ defEnv prog) :
    chargeCache prog sc t = chargeExpr sc (chargeCache prog sc) e := by
  rw [chargeCache_unfold prog sc hdc hord hmem, chargeLoc_remat]

/-- **Corollary — spilled tmp.** The charge list of a `.slot n` tmp is the spill-load charge
`[Gverylow, Gverylow]` (`PUSH n; MLOAD`; the `matCache_slot` twin). -/
theorem chargeCache_slot (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {n : Nat} (hmem : (t, Loc.slot n) ∈ defEnv prog) :
    chargeCache prog sc t = [GasConstants.Gverylow, GasConstants.Gverylow] := by
  rw [chargeCache_unfold prog sc hdc hord hmem, chargeLoc_slot]

/-- **Corollary — absent tmp.** A tmp with no `defEnv` entry falls back to the `chargeInit` leaf
`[Gverylow]` (the `matCache_absent` twin: the charge of `matInit`'s `emitImm 0` PUSH). -/
theorem chargeCache_absent (prog : Program) (sc : Tmp → ℕ) {t : Tmp}
    (hmem : t ∉ (defEnv prog).map Prod.fst) :
    chargeCache prog sc t = [GasConstants.Gverylow] := by
  rw [chargeCache_eq_chargeFold, chargeFold_notMem sc (defEnv prog) chargeInit hmem]; rfl

/-! ### The chargeCache↔matCache length lockstep

The charge fold and the byte fold unfold *in lockstep*: driven by the SAME membership hypothesis
`(t, loc) ∈ defEnv prog`, they expose parallel operand structure (`chargeExpr`/`matExpr` for a
`.remat`, the fixed spill-load list/bytes for a `.slot`, the init leaf when absent). The bundled
`matCache_chargeCache_unfold` states the lockstep directly; the `chargeCache_length_*` corollaries
give the charge-list LENGTH in the decomposed form the fuel-free `StackRoomOK`/`maxChargeDepth`
folds (and the P5 `materialise_runsC` recursion) read. -/

/-- **The chargeCache↔matCache unfold lockstep.** For a `t` present in `defEnv prog`, the byte
cache and the charge cache unfold together under the identical `Loc` — the load-bearing
statement that the value/gas channels stay in step (byte side = `matCache_unfold`, gas side =
`chargeCache_unfold`). -/
theorem matCache_chargeCache_unfold (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {loc : Loc} (hmem : (t, loc) ∈ defEnv prog) :
    matCache prog t = matLoc (matCache prog) loc ∧
      chargeCache prog sc t = chargeLoc sc (chargeCache prog sc) loc :=
  ⟨matCache_unfold prog hdc hord hmem, chargeCache_unfold prog sc hdc hord hmem⟩

/-- **Length lockstep — rematerialised tmp.** The charge-list LENGTH of a `.remat e` tmp is the
LENGTH of `chargeExpr` of `e` (the operand-decomposed form the stack-room folds read). -/
theorem chargeCache_length_remat (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {e : Expr} (hmem : (t, Loc.remat e) ∈ defEnv prog) :
    (chargeCache prog sc t).length = (chargeExpr sc (chargeCache prog sc) e).length := by
  rw [chargeCache_remat prog sc hdc hord hmem]

/-- **Length lockstep — spilled tmp.** A `.slot n` tmp contributes exactly the two spill-load
charge slots (`PUSH n; MLOAD`). -/
theorem chargeCache_length_slot (prog : Program) (sc : Tmp → ℕ)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {n : Nat} (hmem : (t, Loc.slot n) ∈ defEnv prog) :
    (chargeCache prog sc t).length = 2 := by
  rw [chargeCache_slot prog sc hdc hord hmem]; rfl

/-- **Length lockstep — absent tmp.** An undefined tmp contributes the single `chargeInit` slot. -/
theorem chargeCache_length_absent (prog : Program) (sc : Tmp → ℕ) {t : Tmp}
    (hmem : t ∉ (defEnv prog).map Prod.fst) :
    (chargeCache prog sc t).length = 1 := by
  rw [chargeCache_absent prog sc hmem]; rfl

/-! ## §P5b — the decode fold twin `MatDecC` (Phase 2A P5b, design §3.3)

The cache-keyed decode bundle recurses through
tmp *definitions* via `allocate` (`.tmp t` with `allocate prog t = some (.remat e)`); the fold twin
recurses through them along the **def-env graph**, which is well-founded because `DefEnvOrdered`
places every operand of a `.remat` entry strictly earlier in `defEnv prog`. So `MatDecC`:

* is **structural** for the composite arms (`.add`/`.lt`/`.sload` recurse to their operand
  `.tmp`s, anchoring the sub-decodes at the **operand cache lengths** `(matCache prog t').length`
  — the fold analogue of "bytes for operand `t'`"), and
* **unfolds `.tmp t` via `matCache_unfold`**: it dispatches on `allocate prog t` (the tmp's
  canonical `Loc`, which `matCache_unfold` resolves `matCache prog t` to) — a `.remat e` recurses
  into `e`, a `.slot n` is the spill-load `PUSH n; MLOAD` decode, an absent tmp is the `PUSH32 0`
  leaf.

Termination is the replacement for the deleted fuel index: the measure
`matDecMeasure prog e = 3·(def-env first-index of e's outermost operands) + arm-tag` strictly
decreases at every recursive call — the composite→operand steps by arithmetic, the
`.tmp t`→definiens step by `DefEnvOrdered` (`matDecMeasure_remat_lt`). -/

open Evm

/-- A tmp's **def-env first index** — the position `matCache`/`defsOf` read it back at
(`findIdx`). The well-founded rank the fuel-free `MatDecC` recursion descends. -/
def tmpIdx (prog : Program) (t : Tmp) : Nat := (defEnv prog).findIdx (fun p => p.1 == t)

/-- The `MatDecC` **termination measure**: `3·rank + arm-tag`, fuel-free. The rank is the
outermost operands' def-env index (`tmpIdx`); the `+1`/`+2` tags order the structural
composite→operand steps within one rank. Strictly decreases at every `MatDecC` recursive
call (`matDecMeasure_remat_lt` + arithmetic). -/
def matDecMeasure (prog : Program) : Expr → Nat
  | .imm _   => 0
  | .gas     => 0
  | .tmp t   => 3 * tmpIdx prog t + 1
  | .add a b => 3 * max (tmpIdx prog a) (tmpIdx prog b) + 2
  | .lt  a b => 3 * max (tmpIdx prog a) (tmpIdx prog b) + 2
  | .sload k => 3 * tmpIdx prog k + 2

/-- **`allocate` ⇒ `defEnv` membership.** If `t`'s canonical location is `some loc`, the
`(t, loc)` pair sits in `defEnv prog` — the converse of `defEnv_entry_eq_allocate`, directly
through the `defsOf`/`find?` view (`defsOf_eq_defEnv_find`; `allocate = defsOf` by the shim).
The `hdc` parameter is kept for signature stability with the converse direction. -/
theorem mem_defEnv_of_allocate (prog : Program) (_hdc : DefsConsistent prog)
    {t : Tmp} {loc : Loc} (h : allocate prog t = some loc) : (t, loc) ∈ defEnv prog := by
  have hdefs : defsOf prog t = some loc := h
  rw [defsOf_eq_defEnv_find, Option.map_eq_some_iff] at hdefs
  obtain ⟨⟨tt, loc'⟩, hfind, hsnd⟩ := hdefs
  have htt : tt = t := by have := List.find?_some hfind; simpa using this
  subst htt
  have hl : loc' = loc := hsnd
  rw [← hl]
  exact List.mem_of_find?_eq_some hfind

/-- **`allocate = none` ⇒ absent from `defEnv`.** An unallocated tmp is not a `defEnv` key, so
`matCache prog t` falls to the `matInit` leaf (`matCache_absent`). -/
theorem not_mem_defEnv_of_allocate_none (prog : Program) {t : Tmp}
    (h : allocate prog t = none) : t ∉ (defEnv prog).map Prod.fst := by
  have hdefs : defsOf prog t = none := h
  rw [defsOf_eq_defEnv_find] at hdefs
  have hfind : (defEnv prog).find? (fun p => p.1 == t) = none := by
    cases hf : (defEnv prog).find? (fun p => p.1 == t) with
    | none => rfl
    | some x => rw [hf] at hdefs; simp at hdefs
  intro hmem
  obtain ⟨a, ha, hfst⟩ := List.mem_map.mp hmem
  have := (List.find?_eq_none).mp hfind a ha
  simp only [hfst, beq_self_eq_true, not_true] at this

/-- **The `MatDecC` recursion decreases at the `.tmp`→definiens step.** For a rematerialised
`t` (`allocate prog t = some (.remat e)`) the measure of the definiens `e` is strictly below
`matDecMeasure prog (.tmp t)`: `DefEnvOrdered` places every operand of `e` at a smaller def-env
index than `t` (`defEnv_operand_findIdx_lt` on `t`'s `findIdx` entry). The single termination
obligation that needs well-formedness (the composite→operand steps are pure arithmetic). -/
theorem matDecMeasure_remat_lt (prog : Program) (hdc : DefsConsistent prog)
    (hord : DefEnvOrdered prog) {t : Tmp} {e : Expr} (h : allocate prog t = some (Loc.remat e)) :
    matDecMeasure prog e < matDecMeasure prog (.tmp t) := by
  have hentry : (defEnv prog)[(defEnv prog).findIdx (fun p => p.1 == t)]? = some (t, Loc.remat e) :=
    defEnv_findIdx_entry prog hdc (mem_defEnv_of_allocate prog hdc h)
  cases e with
  | imm _ => simp only [matDecMeasure, tmpIdx]; omega
  | gas => simp only [matDecMeasure, tmpIdx]; omega
  | tmp t'' =>
      have := defEnv_operand_findIdx_lt hord hentry (t' := t'') (by simp [usesInExpr])
      simp only [matDecMeasure, tmpIdx]; omega
  | add a b =>
      have ha := defEnv_operand_findIdx_lt hord hentry (t' := a) (by simp [usesInExpr])
      have hb := defEnv_operand_findIdx_lt hord hentry (t' := b) (by simp [usesInExpr])
      simp only [matDecMeasure, tmpIdx]; omega
  | lt a b =>
      have ha := defEnv_operand_findIdx_lt hord hentry (t' := a) (by simp [usesInExpr])
      have hb := defEnv_operand_findIdx_lt hord hentry (t' := b) (by simp [usesInExpr])
      simp only [matDecMeasure, tmpIdx]; omega
  | sload k =>
      have := defEnv_operand_findIdx_lt hord hentry (t' := k) (by simp [usesInExpr])
      simp only [matDecMeasure, tmpIdx]; omega

/-- Ordered rematerialisation environments have a finite closure, and the empty
invalidation set excludes none of it. -/
def rematClosureFree_empty (prog : Program) (hdc : DefsConsistent prog)
    (hord : DefEnvOrdered prog) : (e : Expr) → RematClosureFree prog (fun _ => False) e
  | .imm w => .imm w
  | .gas => .gas
  | .sload k => .sload k
  | .tmp t => .tmp t not_false (fun e' h => rematClosureFree_empty prog hdc hord e')
  | .add a b => .add a b (rematClosureFree_empty prog hdc hord (.tmp a))
      (rematClosureFree_empty prog hdc hord (.tmp b))
  | .lt a b => .lt a b (rematClosureFree_empty prog hdc hord (.tmp a))
      (rematClosureFree_empty prog hdc hord (.tmp b))
  termination_by e => matDecMeasure prog e
  decreasing_by
    · exact matDecMeasure_remat_lt prog hdc hord h
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega

/-- **`MatDecC` — the cache-keyed decode bundle.** One `decode`
clause per opcode `matExpr (matCache prog) e` emits, anchored at the running pc; composite arms
anchor their sub-decodes at the **operand cache lengths** `(matCache prog t').length`, and the
`.tmp t` arm unfolds via `allocate prog t` (`matCache_unfold`'s `Loc`). -/
def MatDecC (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (code : ByteArray) : UInt32 → Expr → Prop
  | p, .imm w  => decode code p = some (.Push .PUSH32, some (w, 32))
  | p, .gas    => decode code p = some (.Smsf .GAS, .none)
  | p, .add a b =>
      MatDecC prog hdc hord code p (.tmp b)
      ∧ MatDecC prog hdc hord code (p + UInt32.ofNat (matCache prog b).length) (.tmp a)
      ∧ decode code (p + UInt32.ofNat (matCache prog b).length
                       + UInt32.ofNat (matCache prog a).length)
          = some (.ArithLogic .ADD, .none)
  | p, .lt a b =>
      MatDecC prog hdc hord code p (.tmp b)
      ∧ MatDecC prog hdc hord code (p + UInt32.ofNat (matCache prog b).length) (.tmp a)
      ∧ decode code (p + UInt32.ofNat (matCache prog b).length
                       + UInt32.ofNat (matCache prog a).length)
          = some (.ArithLogic .LT, .none)
  | p, .sload k =>
      MatDecC prog hdc hord code p (.tmp k)
      ∧ decode code (p + UInt32.ofNat (matCache prog k).length)
          = some (.Smsf .SLOAD, .none)
  | p, .tmp t  =>
      match h : allocate prog t with
      | some (.remat e) => MatDecC prog hdc hord code p e
      | some (.slot n)  =>
          decode code p = some (.Push .PUSH32, some (UInt256.ofNat n, 32))
          ∧ decode code (p + UInt32.ofNat (emitImm (UInt256.ofNat n)).length)
              = some (.Smsf .MLOAD, .none)
      | none            => decode code p = some (.Push .PUSH32, some ((0 : Word), 32))
  termination_by _ e => matDecMeasure prog e
  decreasing_by
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega
    · simp only [matDecMeasure]; omega
    · exact matDecMeasure_remat_lt prog hdc hord h

/-! ### `MatDecC` reduction lemmas (pair with `matExpr (matCache prog)`'s byte shape) -/

section Reductions
variable (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
  (code : ByteArray)

@[simp] theorem matDecC_imm (p : UInt32) (w : Word) :
    MatDecC prog hdc hord code p (.imm w)
      = (decode code p = some (.Push .PUSH32, some (w, 32))) := by
  rw [MatDecC]

@[simp] theorem matDecC_gas (p : UInt32) :
    MatDecC prog hdc hord code p .gas = (decode code p = some (.Smsf .GAS, .none)) := by
  rw [MatDecC]

@[simp] theorem matDecC_add (p : UInt32) (a b : Tmp) :
    MatDecC prog hdc hord code p (.add a b)
      = (MatDecC prog hdc hord code p (.tmp b)
         ∧ MatDecC prog hdc hord code (p + UInt32.ofNat (matCache prog b).length) (.tmp a)
         ∧ decode code (p + UInt32.ofNat (matCache prog b).length
                          + UInt32.ofNat (matCache prog a).length)
             = some (.ArithLogic .ADD, .none)) := by
  rw [MatDecC]

@[simp] theorem matDecC_lt (p : UInt32) (a b : Tmp) :
    MatDecC prog hdc hord code p (.lt a b)
      = (MatDecC prog hdc hord code p (.tmp b)
         ∧ MatDecC prog hdc hord code (p + UInt32.ofNat (matCache prog b).length) (.tmp a)
         ∧ decode code (p + UInt32.ofNat (matCache prog b).length
                          + UInt32.ofNat (matCache prog a).length)
             = some (.ArithLogic .LT, .none)) := by
  rw [MatDecC]

@[simp] theorem matDecC_sload (p : UInt32) (k : Tmp) :
    MatDecC prog hdc hord code p (.sload k)
      = (MatDecC prog hdc hord code p (.tmp k)
         ∧ decode code (p + UInt32.ofNat (matCache prog k).length)
             = some (.Smsf .SLOAD, .none)) := by
  rw [MatDecC]

/-- **`.tmp` arm — rematerialised.** The tmp's decode bundle IS its definiens `e`'s
(`allocate prog t = some (.remat e)`; `matCache prog t = matExpr (matCache prog) e`). -/
theorem matDecC_tmp_remat (p : UInt32) (t : Tmp) (e : Expr)
    (h : allocate prog t = some (Loc.remat e)) :
    MatDecC prog hdc hord code p (.tmp t) = MatDecC prog hdc hord code p e := by
  rw [MatDecC]
  split
  next e' heq => rw [h] at heq; injection heq with heq'; injection heq' with heq''; rw [heq'']
  next n heq => rw [h] at heq; exact absurd heq (by simp)
  next heq => rw [h] at heq; exact absurd heq (by simp)

/-- **`.tmp` arm — spilled.** The tmp reads back its slot: `PUSH n; MLOAD`. -/
theorem matDecC_tmp_slot (p : UInt32) (t : Tmp) (n : Nat)
    (h : allocate prog t = some (Loc.slot n)) :
    MatDecC prog hdc hord code p (.tmp t)
      = (decode code p = some (.Push .PUSH32, some (UInt256.ofNat n, 32))
         ∧ decode code (p + UInt32.ofNat (emitImm (UInt256.ofNat n)).length)
             = some (.Smsf .MLOAD, .none)) := by
  rw [MatDecC]
  split
  next e' heq => rw [h] at heq; exact absurd heq (by simp)
  next n' heq => rw [h] at heq; injection heq with heq'; injection heq' with heq''; rw [heq'']
  next heq => rw [h] at heq; exact absurd heq (by simp)

/-- **`.tmp` arm — absent.** An undefined tmp is the `PUSH32 0` leaf (`matInit`). -/
theorem matDecC_tmp_none (p : UInt32) (t : Tmp)
    (h : allocate prog t = none) :
    MatDecC prog hdc hord code p (.tmp t)
      = (decode code p = some (.Push .PUSH32, some ((0 : Word), 32))) := by
  rw [MatDecC]
  split
  next e' heq => rw [h] at heq; exact absurd heq (by simp)
  next n heq => rw [h] at heq; exact absurd heq (by simp)
  next heq => rfl

end Reductions

/-! ### `matDecC_of_seg` — the byte-segment bridge over the fold

The fuel-free segment bridge (successor of the deleted fuel-era `matDec_of_seg`): from a
segment hypothesis that the
bytes `matExpr (matCache prog) e` sit in `flatBytes prog` at `[base, base+len)`, the full
`MatDecC` bundle holds at `UInt32.ofNat base` over `lower prog`. Proved by **structural
recursion on `e`** (composite arms split their operand sub-segments off the parent) plus the
**def-env recursion** for the `.tmp t` arm (its bytes `matCache prog t` unfold via
`matCache_unfold` to the definiens `e'`'s bytes, and `matDecMeasure_remat_lt` justifies the
descent). The per-`lower` leaf decodes reuse `MatDecLower`'s
lowering-independent `extract_toList_eq`/`uInt256_wordBytesBE` through the `decode_lower_*`
specialisations. -/

/-- Generic prefix-of-a-segment (over an arbitrary byte list). -/
theorem segF_prefix (bytes : List UInt8) (base : ℕ) (pre suf : List UInt8)
    (h : ∀ j, j < (pre ++ suf).length → bytes[base + j]? = (pre ++ suf)[j]?) :
    ∀ j, j < pre.length → bytes[base + j]? = pre[j]? := by
  intro j hj
  rw [h j (by rw [List.length_append]; omega), List.getElem?_append_left hj]

/-- Generic suffix-of-a-segment (over an arbitrary byte list). -/
theorem segF_suffix (bytes : List UInt8) (base : ℕ) (pre suf : List UInt8)
    (h : ∀ j, j < (pre ++ suf).length → bytes[base + j]? = (pre ++ suf)[j]?) :
    ∀ j, j < suf.length → bytes[base + pre.length + j]? = suf[j]? := by
  intro j hj
  have := h (pre.length + j) (by rw [List.length_append]; omega)
  rw [show base + (pre.length + j) = base + pre.length + j from by ring] at this
  rw [this, List.getElem?_append_right (by omega), show pre.length + j - pre.length = j from by omega]

/-- **`.imm` leaf decode over `lower`**: `PUSH32 w` reads back `w` (`uInt256_wordBytesBE`). -/
theorem imm_leaf_decodeF (prog : Program) (base : ℕ) (w : Word)
    (hbound : base + 33 ≤ 2 ^ 32)
    (hseg : ∀ j, j < (emitImm w).length → (flatBytes prog)[base + j]? = (emitImm w)[j]?) :
    decode (lower prog) (UInt32.ofNat base) = some (.Push .PUSH32, some (w, 32)) := by
  have hemit : (emitImm w).length = 33 := emitImm_length w
  have hbyte : (flatBytes prog)[base]? = some Byte.push32 := by
    have := hseg 0 (by omega); simpa [emitImm] using this
  have hwin : ((flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)).toList = BytecodeLayer.Exec.wordBytesBE w := by
    apply extract_toList_eq (flatBytes prog) (base + 1) 32 (BytecodeLayer.Exec.wordBytesBE w) (by simp [BytecodeLayer.Exec.wordBytesBE])
    intro j hj
    have := hseg (1 + j) (by rw [hemit]; omega)
    rw [show base + (1 + j) = base + 1 + j from by ring] at this
    rw [this, show (1 + j) = j + 1 from by ring]
    simp [emitImm, List.getElem?_cons_succ]
  have himm : uInt256OfByteArray ⟨(flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)⟩ = w := by
    have hh : uInt256OfByteArray ⟨(flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)⟩
        = uInt256OfByteArray ⟨(BytecodeLayer.Exec.wordBytesBE w).toArray⟩ := by
      unfold uInt256OfByteArray
      congr 2
      show ((flatBytes prog).toArray.extract (base + 1) (base + 1 + 32)).toList.reverse = _
      rw [hwin]
    rw [hh, uInt256_wordBytesBE]
  have hp : Evm.pushArgWidth (Evm.parseInstr Byte.push32) = (32 : UInt8) := by decide
  have h32 : (32 : UInt8).toNat = 32 := by decide
  have hres := decode_lower_push prog base Byte.push32 32 w (by omega) hbyte hp (by decide)
    (by rw [h32]; exact himm)
  rw [hres]; rfl

/-- **Non-push opcode leaf decode over `lower`** (covers `ADD`/`LT`/`SLOAD`/`GAS`/`MLOAD`). -/
theorem nonpush_leaf_decodeF (prog : Program) (base off : ℕ) (byte : UInt8) (seg : List UInt8)
    (hbound : base + off < 2 ^ 32)
    (hoff : seg[off]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0)
    (hseg : ∀ j, j < seg.length → (flatBytes prog)[base + j]? = seg[j]?) :
    decode (lower prog) (UInt32.ofNat (base + off)) = some (Evm.parseInstr byte, .none) := by
  have hoffl : off < seg.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hoff; exact absurd hoff (by simp)
  have hbyte : (flatBytes prog)[base + off]? = some byte := by rw [hseg off hoffl]; exact hoff
  exact decode_lower_nonpush prog (base + off) byte hbound hbyte hnp

/-- **`.slot` leaf decode over `lower`**: `PUSH n ; MLOAD` (the spill readback pair). -/
theorem slot_leaf_decodeF (prog : Program) (base slot : ℕ)
    (hbound : base + (emitImm (UInt256.ofNat slot) ++ [Byte.mload]).length ≤ 2 ^ 32)
    (hseg : ∀ j, j < (emitImm (UInt256.ofNat slot) ++ [Byte.mload]).length →
      (flatBytes prog)[base + j]? = (emitImm (UInt256.ofNat slot) ++ [Byte.mload])[j]?) :
    decode (lower prog) (UInt32.ofNat base) = some (.Push .PUSH32, some (UInt256.ofNat slot, 32))
    ∧ decode (lower prog) (UInt32.ofNat base
        + UInt32.ofNat (emitImm (UInt256.ofNat slot)).length) = some (.Smsf .MLOAD, .none) := by
  have hlen : (emitImm (UInt256.ofNat slot)).length = 33 := emitImm_length _
  rw [List.length_append, hlen, List.length_singleton] at hbound
  refine ⟨imm_leaf_decodeF prog base (UInt256.ofNat slot) (by omega)
      (segF_prefix (flatBytes prog) base (emitImm (UInt256.ofNat slot)) [Byte.mload] hseg), ?_⟩
  rw [hlen, ofNat_add']
  have hmload := nonpush_leaf_decodeF prog base 33 Byte.mload
      (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) (by omega)
      (by rw [List.getElem?_append_right (by rw [hlen]), hlen]; rfl)
      (by decide) hseg
  simpa using hmload

/-- **`matDecC_of_seg` (core deliverable).** The whole `MatDecC` bundle over `lower prog` from a
segment of the fold bytes `matExpr (matCache prog) e` at `base`. Structural on `e`; the `.tmp`
arm descends the def-env via `matCache_unfold` (`matDecMeasure_remat_lt`). -/
theorem matDecC_of_seg (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (e : Expr) (base : ℕ)
    (hbound : base + (matExpr (matCache prog) e).length ≤ 2 ^ 32)
    (hseg : ∀ j, j < (matExpr (matCache prog) e).length →
        (flatBytes prog)[base + j]? = (matExpr (matCache prog) e)[j]?) :
    MatDecC prog hdc hord (lower prog) (UInt32.ofNat base) e := by
  match e, hbound, hseg with
  | .imm w, hbound, hseg =>
      rw [matDecC_imm]
      simp only [matExpr_imm] at hseg hbound
      exact imm_leaf_decodeF prog base w (by rw [emitImm_length] at hbound; omega) hseg
  | .gas, hbound, hseg =>
      rw [matDecC_gas]
      simp only [matExpr_gas] at hseg hbound
      have := nonpush_leaf_decodeF prog base 0 Byte.gas [Byte.gas]
        (by simp only [List.length_singleton] at hbound; omega) (by decide) (by decide) hseg
      simpa using this
  | .add a b, hbound, hseg =>
      rw [matDecC_add]
      have hmat : matExpr (matCache prog) (.add a b)
          = matCache prog b ++ matCache prog a ++ [Byte.add] := by simp only [matExpr_add]
      rw [hmat] at hseg hbound
      have hsegBA := segF_prefix (flatBytes prog) base (matCache prog b ++ matCache prog a)
        [Byte.add] hseg
      have hsegb := segF_prefix (flatBytes prog) base (matCache prog b) (matCache prog a) hsegBA
      have hsega := segF_suffix (flatBytes prog) base (matCache prog b) (matCache prog a) hsegBA
      have hbnd : base + ((matCache prog b).length + (matCache prog a).length + 1) ≤ 2 ^ 32 := by
        simp only [List.length_append, List.length_singleton] at hbound; omega
      refine ⟨?_, ?_, ?_⟩
      · exact matDecC_of_seg prog hdc hord (.tmp b) base (by simp only [matExpr_tmp]; omega)
          (by simp only [matExpr_tmp]; exact hsegb)
      · rw [ofNat_add']
        exact matDecC_of_seg prog hdc hord (.tmp a) (base + (matCache prog b).length)
          (by simp only [matExpr_tmp]; omega) (by simp only [matExpr_tmp]; exact hsega)
      · rw [ofNat_add', ofNat_add']
        have := nonpush_leaf_decodeF prog base ((matCache prog b).length + (matCache prog a).length)
          Byte.add (matCache prog b ++ matCache prog a ++ [Byte.add]) (by omega) (by simp)
          (by decide) hseg
        rw [show base + ((matCache prog b).length + (matCache prog a).length)
              = base + (matCache prog b).length + (matCache prog a).length from by ring] at this
        simpa using this
  | .lt a b, hbound, hseg =>
      rw [matDecC_lt]
      have hmat : matExpr (matCache prog) (.lt a b)
          = matCache prog b ++ matCache prog a ++ [Byte.lt] := by simp only [matExpr_lt]
      rw [hmat] at hseg hbound
      have hsegBA := segF_prefix (flatBytes prog) base (matCache prog b ++ matCache prog a)
        [Byte.lt] hseg
      have hsegb := segF_prefix (flatBytes prog) base (matCache prog b) (matCache prog a) hsegBA
      have hsega := segF_suffix (flatBytes prog) base (matCache prog b) (matCache prog a) hsegBA
      have hbnd : base + ((matCache prog b).length + (matCache prog a).length + 1) ≤ 2 ^ 32 := by
        simp only [List.length_append, List.length_singleton] at hbound; omega
      refine ⟨?_, ?_, ?_⟩
      · exact matDecC_of_seg prog hdc hord (.tmp b) base (by simp only [matExpr_tmp]; omega)
          (by simp only [matExpr_tmp]; exact hsegb)
      · rw [ofNat_add']
        exact matDecC_of_seg prog hdc hord (.tmp a) (base + (matCache prog b).length)
          (by simp only [matExpr_tmp]; omega) (by simp only [matExpr_tmp]; exact hsega)
      · rw [ofNat_add', ofNat_add']
        have := nonpush_leaf_decodeF prog base ((matCache prog b).length + (matCache prog a).length)
          Byte.lt (matCache prog b ++ matCache prog a ++ [Byte.lt]) (by omega) (by simp)
          (by decide) hseg
        rw [show base + ((matCache prog b).length + (matCache prog a).length)
              = base + (matCache prog b).length + (matCache prog a).length from by ring] at this
        simpa using this
  | .sload k, hbound, hseg =>
      rw [matDecC_sload]
      have hmat : matExpr (matCache prog) (.sload k)
          = matCache prog k ++ [Byte.sload] := by simp only [matExpr_sload]
      rw [hmat] at hseg hbound
      have hsegk := segF_prefix (flatBytes prog) base (matCache prog k) [Byte.sload] hseg
      have hbnd : base + ((matCache prog k).length + 1) ≤ 2 ^ 32 := by
        simp only [List.length_append, List.length_singleton] at hbound; omega
      refine ⟨?_, ?_⟩
      · exact matDecC_of_seg prog hdc hord (.tmp k) base (by simp only [matExpr_tmp]; omega)
          (by simp only [matExpr_tmp]; exact hsegk)
      · rw [ofNat_add']
        have := nonpush_leaf_decodeF prog base (matCache prog k).length Byte.sload
          (matCache prog k ++ [Byte.sload]) (by omega) (by simp) (by decide) hseg
        simpa using this
  | .tmp t, hbound, hseg =>
      cases hal : allocate prog t with
      | none =>
          rw [matDecC_tmp_none prog hdc hord (lower prog) (UInt32.ofNat base) t hal]
          have hc : matCache prog t = emitImm 0 :=
            matCache_absent prog (not_mem_defEnv_of_allocate_none prog hal)
          simp only [matExpr_tmp, hc] at hseg hbound
          exact imm_leaf_decodeF prog base (0 : Word) (by rw [emitImm_length] at hbound; omega) hseg
      | some loc =>
          cases loc with
          | remat e' =>
              rw [matDecC_tmp_remat prog hdc hord (lower prog) (UInt32.ofNat base) t e' hal]
              have hc : matCache prog t = matExpr (matCache prog) e' :=
                matCache_remat prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              apply matDecC_of_seg prog hdc hord e' base
              · simp only [matExpr_tmp, hc] at hbound; exact hbound
              · simp only [matExpr_tmp, hc] at hseg; exact hseg
          | slot n =>
              rw [matDecC_tmp_slot prog hdc hord (lower prog) (UInt32.ofNat base) t n hal]
              have hc : matCache prog t = emitImm (UInt256.ofNat n) ++ [Byte.mload] :=
                matCache_slot prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              simp only [matExpr_tmp, hc] at hseg hbound
              exact slot_leaf_decodeF prog base n hbound hseg
  termination_by matDecMeasure prog e
  decreasing_by
    all_goals
      first
        | (simp only [matDecMeasure]; omega)
        | (exact matDecMeasure_remat_lt prog hdc hord (by assumption))

/-! ## §P5c — the value-channel linchpin over the fold: `MatRunsC` / `materialise_runsC`

The fuel-free value-channel linchpin (successor of the deleted fuel-era `materialise_runs`),
stated and proved
DIRECTLY over the fold. `matExpr (matCache prog) e` reconstructs `evalExpr st obs e` on the EVM
stack, via a per-tmp recursion along `defEnv` (`matDecMeasure`, well-founded by `DefEnvOrdered`)
that unfolds `.tmp t` through `matCache_unfold`. The `.imm`/`.add`/`.lt` arms reuse
`sim_imm`/`sim_add`/`sim_lt` verbatim; the `.tmp t`
readback arm reuses the `MemRealises` MLOAD channel; the `.gas`/`.sload`/`.slot` arms are
unreachable (spilled / no IR value). The gas contract reads `chargeExpr sloadChg (chargeCache …)`
in lockstep with the bytes (P5a). -/

section ValueChannel

open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ### Charge-list positivity (the `chargeOf_length_pos_of_matDec` twin, cache-driven) -/

/-- `chargeExpr` emits at least one charge whenever the cache is everywhere non-empty. -/
theorem chargeExpr_length_pos {sloadChg : Tmp → ℕ} {cache : Tmp → List ℕ}
    (hc : ∀ t, 1 ≤ (cache t).length) (e : Expr) :
    1 ≤ (chargeExpr sloadChg cache e).length := by
  cases e with
  | imm w => simp [chargeExpr_imm]
  | tmp t => rw [chargeExpr_tmp]; exact hc t
  | gas => simp [chargeExpr_gas]
  | add a b => simp only [chargeExpr_add, List.length_append, List.length_singleton]; omega
  | lt a b => simp only [chargeExpr_lt, List.length_append, List.length_singleton]; omega
  | sload k => simp only [chargeExpr_sload, List.length_append, List.length_singleton]; omega

/-- One `chargeStep` preserves the everywhere-non-empty cache invariant. -/
theorem chargeStep_length_pos {sloadChg : Tmp → ℕ} {c : Tmp → List ℕ}
    (hc : ∀ t, 1 ≤ (c t).length) (p : Tmp × Loc) :
    ∀ t, 1 ≤ (chargeStep sloadChg c p t).length := by
  intro t
  simp only [chargeStep, Function.update_apply]
  by_cases ht : t = p.1
  · simp only [if_pos ht]
    cases p.2 with
    | remat e => exact chargeExpr_length_pos hc e
    | slot n => simp [chargeLoc_slot]
  · simp only [if_neg ht]; exact hc t

/-- The whole `chargeFold` preserves the everywhere-non-empty cache invariant. -/
theorem chargeFold_length_pos {sloadChg : Tmp → ℕ} :
    ∀ (l : List (Tmp × Loc)) (c : Tmp → List ℕ), (∀ t, 1 ≤ (c t).length) →
      ∀ t, 1 ≤ (chargeFold sloadChg c l t).length
  | [], _, hc, t => hc t
  | p :: l, c, hc, t => by
      rw [chargeFold_cons]; exact chargeFold_length_pos l _ (chargeStep_length_pos hc p) t

/-- **`chargeCache` is everywhere non-empty** (the `chargeOf_length_pos_of_matDec` twin): every
tmp materialises at least one opcode, so its charge list carries at least one entry. -/
theorem chargeCache_length_pos (prog : Program) (sloadChg : Tmp → ℕ) (t : Tmp) :
    1 ≤ (chargeCache prog sloadChg t).length := by
  rw [chargeCache_eq_chargeFold]
  exact chargeFold_length_pos (defEnv prog) chargeInit (fun _ => by simp [chargeInit]) t

/-! ### `allocate` → `defsOf` bridges (route the `.tmp t` arm to the recompute / readback env) -/

/-- A spilled allocation is a spilled `defsOf` entry (definitional through the `allocate`
shim). -/
theorem defsOf_of_allocate_slot (prog : Program) {t : Tmp} {n : Nat}
    (h : allocate prog t = some (Loc.slot n)) : defsOf prog t = some (.slot n) := h

/-- A rematerialised allocation, read back through the `rematOf` projection: the definiens
is registered for recompute and is never a spilled leaf (`rematOf_ne_gas` /
`rematOf_ne_sload`) — exactly what `materialise_runsC`'s remat arm feeds `DefsSound`. -/
theorem defsOf_of_allocate_remat (prog : Program) {t : Tmp} {e : Expr}
    (h : allocate prog t = some (Loc.remat e)) :
    rematOf prog t = some e ∧ e ≠ .gas ∧ ∀ k, e ≠ .sload k := by
  have hrem : rematOf prog t = some e := rematOf_of_defsOf h
  exact ⟨hrem, fun hg => rematOf_ne_gas prog t (hg ▸ hrem),
    fun k hk => rematOf_ne_sload prog t k (hk ▸ hrem)⟩

/-! ### The binop gas-charge gluing (the `materialiseGasCharge_binop` twin, over raw charge lists) -/

/-- Gluing the two operand sub-charge endpoints and the final op-charge into the whole binop
`subCharges` (the fuel-free `materialiseGasCharge_binop` core; pure `subCharges_append`). -/
theorem gasCharge_binop_glue (g : UInt64) (cb ca : List ℕ) (frb fra fr' : Frame)
    (hb : frb.exec.gasAvailable = subCharges g cb)
    (ha : fra.exec.gasAvailable = subCharges frb.exec.gasAvailable ca)
    (hf : fr'.exec.gasAvailable = subCharges fra.exec.gasAvailable [Gverylow]) :
    fr'.exec.gasAvailable = subCharges g (cb ++ ca ++ [Gverylow]) := by
  rw [hf, ha, hb, subCharges_append, subCharges_append]

/-! ### The endpoint bundle `MatRunsC` -/

/-- The fold-based materialise endpoint bundle: everything running `matExpr (matCache prog) e`
from `fr` delivers about the endpoint `fr'`. Byte length and gas contract read the fold caches
(`matCache` / `chargeCache`). -/
structure MatRunsC (prog : Program) (sloadChg : Tmp → ℕ) (e : Expr) (w : Word) (fr fr' : Frame) :
    Prop where
  runs       : Runs fr fr'
  stack      : fr'.exec.stack = fr.exec.stack.push w
  code       : fr'.exec.executionEnv.code = fr.exec.executionEnv.code
  validJumps : fr'.validJumps = fr.validJumps
  addr       : fr'.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod     : fr'.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  accounts   : fr'.exec.accounts = fr.exec.accounts
  storage    : ∀ k, selfStorage fr' k = selfStorage fr k
  pc         : fr'.exec.pc = fr.exec.pc + UInt32.ofNat (matExpr (matCache prog) e).length
  gasCharge  : fr'.exec.gasAvailable
                 = subCharges fr.exec.gasAvailable (chargeExpr sloadChg (chargeCache prog sloadChg) e)
  gasToNat   : fr'.exec.gasAvailable.toNat
                 = fr.exec.gasAvailable.toNat
                     - (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum
  memBytes   : fr'.exec.toMachineState.memory = fr.exec.toMachineState.memory
  memActive  : fr.exec.toMachineState.activeWords.toNat
                 ≤ fr'.exec.toMachineState.activeWords.toNat
  activeWordsEq : fr'.exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords

/-! ### `materialise_runsC` — the crux (P5c) -/

/-- **P5c — `materialise_runsC` (total over `Expr`, fuel-free).** Running `matExpr (matCache prog)
e` from a frame `fr` whose code decodes as `MatDecC` prescribes, with the IR state recompute-sound
(`DefsSound`), define-before-use-scoped, storage-agreeing, memory-realising, and the materialised
expression neither a bare gas read nor a bare sload, reproduces `evalExpr st obs e = some w` on the
bytecode stack and delivers the whole `MatRunsC` bundle. The `.tmp t` arm resolves through
`allocate prog t` (`matCache_unfold`): a `.remat e'` recomputes (recurse via `matDecMeasure_remat_lt`),
a `.slot n` reads the memory spill back (`MemRealises`), an undefined tmp is ruled out by scoping.
All recursion follows the fold measure. -/
theorem materialise_runsC {prog : Program} (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (sloadChg : Tmp → ℕ) (st : IRState) (obs : Word)
    (I : Tmp → Prop) (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSoundS prog I st)
    (hfree : RematClosureFree prog I e)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hstore : StorageAgree st fr)
    (hne : e ≠ .gas)
    (hnsl : ∀ k, e ≠ .sload k)
    (hmemreal : MemRealises prog st fr)
    (heval : evalExpr st obs e = some w)
    (hgas : (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + (chargeExpr sloadChg (chargeCache prog sloadChg) e).length ≤ 1024) :
    ∃ fr', MatRunsC prog sloadChg e w fr fr' := by
  match e, hfree, hdec, hne, hnsl, heval, hgas, hstk with
  | .imm v, _, hdec, _, _, heval, hgas, hstk =>
      have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
          = some (.Push .PUSH32, some (v, 32)) := by rw [matDecC_imm] at hdec; exact hdec
      have hvw : v = w := Option.some.inj heval
      subst hvw
      have hg3 : 3 ≤ fr.exec.gasAvailable.toNat := by
        simp only [chargeExpr_imm, List.sum_cons, List.sum_nil] at hgas
        simpa [show (Gverylow : ℕ) = 3 from rfl] using hgas
      have hstk1 : fr.exec.stack.size + 1 ≤ 1024 := by
        simp only [chargeExpr_imm, List.length_cons, List.length_nil] at hstk; omega
      refine ⟨pushFrameW fr v 32,
        { runs := (sim_imm fr v hdec' hg3 hstk1).1
          stack := (sim_imm fr v hdec' hg3 hstk1).2
          code := rfl, validJumps := rfl, addr := rfl, canMod := rfl
          accounts := rfl, storage := fun _ => rfl
          pc := ?_, gasCharge := ?_, gasToNat := ?_
          memBytes := rfl, memActive := le_refl _, activeWordsEq := rfl }⟩
      · rw [pushFrameW_pc, push32_pcΔ]; simp [matExpr_imm, emitImm_length]
      · rw [chargeExpr_imm]
        show (fr.exec.gasAvailable - UInt64.ofNat Gverylow) = subCharges fr.exec.gasAvailable [Gverylow]
        rw [subCharges_singleton]
      · rw [chargeExpr_imm]
        show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
        have h3 : (3 : ℕ) ≤ fr.exec.gasAvailable.toNat := hg3
        rw [show (Gverylow : ℕ) = 3 from rfl,
            BytecodeLayer.UInt64.toNat_sub_ofNat _ 3 h3 (by omega)]
        simp [List.sum_cons]
  | .gas, _, _, hne, _, _, _, _ => exact absurd rfl hne
  | .sload k, _, _, _, hnsl, _, _, _ => exact absurd rfl (hnsl k)
  | .tmp t, hfree, hdec, _, _, heval, hgas, hstk =>
      have hloc : st.locals t = some w := heval
      cases hal : allocate prog t with
      | none =>
          exfalso
          have hdn : defsOf prog t = none := hal
          exact (hscoped t (by rw [hloc]; simp)).2 hdn
      | some loc =>
          cases loc with
          | remat e' =>
              -- == the pure recompute path (DefsSound) ==
              have hmc : matCache prog t = matExpr (matCache prog) e' :=
                matCache_remat prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              have hcc : chargeCache prog sloadChg t
                  = chargeExpr sloadChg (chargeCache prog sloadChg) e' :=
                chargeCache_remat prog sloadChg hdc hord (mem_defEnv_of_allocate prog hdc hal)
              obtain ⟨hremt, he'ng, he'nsl⟩ := defsOf_of_allocate_remat prog hal
              have htmd : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e' := by
                rw [matDecC_tmp_remat prog hdc hord fr.exec.executionEnv.code fr.exec.pc t e' hal]
                  at hdec
                exact hdec
              have hnr : ¬ NonRecomputable prog t := by
                rcases (hscoped t (by rw [hloc]; simp)).1 with hnr | ⟨s, hcrdef⟩
                · exact hnr
                · exfalso
                  have hdeft : defsOf prog t = some (Loc.remat e') := hal
                  rw [hdeft] at hcrdef
                  exact absurd hcrdef (by simp)
              obtain ⟨hfree_t, hfree_remat⟩ := RematClosureFree.tmp_inv hfree
              have hdfs : some w = evalExpr st 0 e' :=
                hsound t e' w hremt hnr hfree_t hloc
              have heval' : evalExpr st obs e' = some w := by
                rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
              have hgas' : (chargeExpr sloadChg (chargeCache prog sloadChg) e').sum
                  ≤ fr.exec.gasAvailable.toNat := by
                have hx := hgas; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              have hstk' : fr.exec.stack.size
                  + (chargeExpr sloadChg (chargeCache prog sloadChg) e').length ≤ 1024 := by
                have hx := hstk; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              obtain ⟨fr', hmr⟩ := materialise_runsC hdc hord sloadChg st obs I e' w fr htmd hsound
                (hfree_remat e' hal) hscoped hstore he'ng he'nsl hmemreal heval' hgas' hstk'
              have hpcE : matExpr (matCache prog) (Expr.tmp t) = matExpr (matCache prog) e' := by
                simp only [matExpr_tmp]; exact hmc
              have hchgE : chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)
                  = chargeExpr sloadChg (chargeCache prog sloadChg) e' := by
                simp only [chargeExpr_tmp]; exact hcc
              exact ⟨fr',
                { runs := hmr.runs, stack := hmr.stack, code := hmr.code
                  validJumps := hmr.validJumps, addr := hmr.addr, canMod := hmr.canMod
                  accounts := hmr.accounts, storage := hmr.storage
                  pc := by rw [hpcE]; exact hmr.pc
                  gasCharge := by rw [hchgE]; exact hmr.gasCharge
                  gasToNat := by rw [hchgE]; exact hmr.gasToNat
                  memBytes := hmr.memBytes, memActive := hmr.memActive
                  activeWordsEq := hmr.activeWordsEq }⟩
          | slot n =>
              -- == the memory value-channel readback arm (PUSH n ; MLOAD) ==
              have hdeft : defsOf prog t = some (.slot n) := defsOf_of_allocate_slot prog hal
              have hmd := hdec
              rw [matDecC_tmp_slot prog hdc hord fr.exec.executionEnv.code fr.exec.pc t n hal] at hmd
              obtain ⟨hdpush, hdmload⟩ := hmd
              have hmexp : matExpr (matCache prog) (Expr.tmp t)
                  = emitImm (UInt256.ofNat n) ++ [Byte.mload] := by
                simp only [matExpr_tmp]
                exact matCache_slot prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              have hchg : chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)
                  = [Gverylow, Gverylow] := by
                simp only [chargeExpr_tmp]
                exact chargeCache_slot prog sloadChg hdc hord (mem_defEnv_of_allocate prog hdc hal)
              obtain ⟨hcm, ham, hreal, hval⟩ := hmemreal t n w hdeft hloc
              have hsum2 : (chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)).sum
                  = Gverylow + Gverylow := by rw [hchg]; simp [List.sum_cons]
              have hgv3 : (Gverylow : ℕ) = 3 := rfl
              have hgasPush : 3 ≤ fr.exec.gasAvailable.toNat := by rw [hsum2, hgv3] at hgas; omega
              have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
                rw [hchg] at hstk; simp only [List.length_cons, List.length_nil] at hstk; omega
              -- step 1: PUSH32 n
              obtain ⟨hpushrun, hpushstk⟩ := sim_imm fr (UInt256.ofNat n) hdpush hgasPush hszfr
              set frp := pushFrameW fr (UInt256.ofNat n) 32 with hfrp
              have hfrpcode : frp.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
              have hfrpmem : frp.exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl
              have hfrpaw : frp.exec.toMachineState.activeWords
                  = fr.exec.toMachineState.activeWords := rfl
              have hfrppc : frp.exec.pc = fr.exec.pc + UInt32.ofNat 33 := by
                rw [hfrp, pushFrameW_pc, push32_pcΔ]
              have hfrpstk : frp.exec.stack = (UInt256.ofNat n) :: fr.exec.stack := by
                rw [hpushstk]; rfl
              have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; simp; omega
              -- step 2: MLOAD at `n` (covered ⇒ zero memory expansion)
              have hreal' : (UInt256.ofNat n).toNat + 63 < 2 ^ 64 := by
                rw [show (UInt256.ofNat n).toNat = n from by
                  rw [BytecodeLayer.Hoare.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
                exact hreal
              have hMeq : MachineState.M frp.exec.toMachineState.activeWords
                  (UInt256.ofNat n).toUInt64 32 = frp.exec.toMachineState.activeWords := by
                rw [hfrpaw]; exact M_32_eq_self_of_covered _ _ ham hreal'
              have hnoexp : memoryExpansionWords? frp.exec.activeWords (UInt256.ofNat n) 32
                  = some frp.exec.activeWords := by
                show memoryExpansionWords? frp.exec.toMachineState.activeWords _ _ = _
                rw [hfrpaw]
                exact memoryExpansionWords?_ofNat_32_of_covered _ ham hreal
              have hzcost : BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
                  frp.exec.activeWords = 0 := by
                show Evm.Cₘ frp.exec.activeWords - Evm.Cₘ frp.exec.activeWords = 0
                omega
              have hmloaddec : decode frp.exec.executionEnv.code frp.exec.pc
                  = some (.Smsf .MLOAD, .none) := by
                rw [hfrpcode, hfrppc]
                have hemitlen : (emitImm (UInt256.ofNat n)).length = 33 := emitImm_length _
                rw [show fr.exec.pc + UInt32.ofNat 33
                      = fr.exec.pc + UInt32.ofNat (emitImm (UInt256.ofNat n)).length from by
                      rw [hemitlen]]
                exact hdmload
              have hgMem : BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
                  frp.exec.activeWords ≤ frp.exec.gasAvailable.toNat := by rw [hzcost]; omega
              have hfrpgasN : frp.exec.gasAvailable.toNat
                  = fr.exec.gasAvailable.toNat - Gverylow := by
                show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
                rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow (by rw [hgv3]; omega)
                  (by rw [hgv3]; omega)]
              have hgMl : GasConstants.Gverylow
                  ≤ (frp.exec.gasAvailable
                      - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
                          frp.exec.activeWords)).toNat := by
                rw [hzcost, BytecodeLayer.UInt64.toNat_sub_ofNat frp.exec.gasAvailable 0
                      (Nat.zero_le _) (by norm_num), Nat.sub_zero, hfrpgasN, hgv3]
                rw [hsum2, hgv3] at hgas; omega
              obtain ⟨hmloadrun, hmloadhd⟩ :=
                sim_mload frp (UInt256.ofNat n) frp.exec.activeWords fr.exec.stack
                  hmloaddec hfrpstk hfrpsz hnoexp hgMem hgMl
              set frm := mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords fr.exec.stack
                with hfrm
              have hmval : ((BytecodeLayer.Dispatch.memChargedState frp.exec
                  frp.exec.activeWords).toMachineState.mload (UInt256.ofNat n)).1 = w := by
                rw [BytecodeLayer.Hoare.MemAlgebra.mload_congr (UInt256.ofNat n)
                      (show (BytecodeLayer.Dispatch.memChargedState frp.exec
                          frp.exec.activeWords).toMachineState.memory
                        = fr.exec.toMachineState.memory from by rw [← hfrpmem]; rfl)
                      (show (BytecodeLayer.Dispatch.memChargedState frp.exec
                          frp.exec.activeWords).toMachineState.activeWords
                        = fr.exec.toMachineState.activeWords from by rw [← hfrpaw]; rfl)]
                exact hval
              have hfrmstk : frm.exec.stack = fr.exec.stack.push w := by
                show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.stack = _
                rw [← hmval]; rfl
              have hfrmmem : frm.exec.toMachineState.memory = fr.exec.toMachineState.memory := by
                show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.toMachineState.memory = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.toMachineState.memory
                    = frp.exec.toMachineState.memory from rfl, hfrpmem]
              have hfrmaw : frm.exec.toMachineState.activeWords
                  = fr.exec.toMachineState.activeWords := by
                show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.toMachineState.activeWords = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.toMachineState.activeWords
                    = MachineState.M frp.exec.toMachineState.activeWords
                        (UInt256.ofNat n).toUInt64 32 from rfl, hMeq, hfrpaw]
              have hexp0 : frp.exec.gasAvailable
                  - UInt64.ofNat (memExpansionChargeOf frp.exec frp.exec.activeWords)
                  = frp.exec.gasAvailable := by
                apply UInt64.toNat_inj.mp
                rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ _
                  (by rw [hzcost]; omega) (by rw [hzcost]; norm_num), hzcost, Nat.sub_zero]
              have hfrmgas : frm.exec.gasAvailable
                  = (fr.exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow := by
                show ((BytecodeLayer.Dispatch.memChargedState frp.exec
                  frp.exec.activeWords).gasAvailable) = _
                show ((frp.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf frp.exec
                  frp.exec.activeWords)) - UInt64.ofNat Gverylow) = _
                rw [hexp0, hfrp]; rfl
              refine ⟨frm,
                { runs := hpushrun.trans hmloadrun
                  stack := hfrmstk
                  code := ?_, validJumps := ?_, addr := ?_, canMod := ?_, accounts := ?_
                  storage := ?_, pc := ?_, gasCharge := ?_, gasToNat := ?_
                  memBytes := hfrmmem
                  memActive := by rw [hfrmaw]
                  activeWordsEq := hfrmaw }⟩
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.executionEnv.code = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.executionEnv.code = frp.exec.executionEnv.code from rfl,
                    hfrpcode]
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).validJumps = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.executionEnv.address = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.executionEnv.canModifyState = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.accounts = _
                rfl
              · intro k
                show selfStorage (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack) k = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.pc = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.pc = frp.exec.pc + 1 from rfl, hfrppc, hmexp]
                rw [List.length_append, emitImm_length,
                    show ([Byte.mload] : List UInt8).length = 1 from rfl,
                    show (33 : ℕ) + 1 = 34 from rfl,
                    show (UInt32.ofNat 34) = UInt32.ofNat 33 + 1 from by decide]
                ac_rfl
              · rw [hchg]
                show frm.exec.gasAvailable = subCharges fr.exec.gasAvailable [Gverylow, Gverylow]
                rw [hfrmgas]
                show (fr.exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow
                  = subCharges fr.exec.gasAvailable [Gverylow, Gverylow]
                rfl
              · rw [hsum2, hfrmgas]
                have h2 : (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat
                    = fr.exec.gasAvailable.toNat - Gverylow :=
                  BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow
                    (by rw [hgv3]; omega) (by rw [hgv3]; omega)
                rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow
                      (by rw [h2, hgv3]; omega) (by rw [hgv3]; omega), h2]
                rw [hsum2, hgv3] at hgas; omega
  | .add a b, hfree, hdec, _, _, heval, hgas, hstk =>
      obtain ⟨va, hla, vb, hlb, hwadd⟩ :
          ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb ∧ w = UInt256.add va vb := by
        simp only [evalExpr] at heval
        cases hla : st.locals a with
        | none => simp [hla] at heval
        | some va =>
            cases hlb : st.locals b with
            | none => simp [hla, hlb] at heval
            | some vb => refine ⟨va, rfl, vb, rfl, ?_⟩; simp [hla, hlb] at heval; exact heval.symm
      subst hwadd
      rw [matDecC_add] at hdec
      obtain ⟨hdb, hda, hop⟩ := hdec
      have hcadd := chargeExpr_add sloadChg (chargeCache prog sloadChg) a b
      have hevb : evalExpr st obs (.tmp b) = some vb := hlb
      have heva : evalExpr st obs (.tmp a) = some va := hla
      have hgasb : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).sum
          ≤ fr.exec.gasAvailable.toNat := by
        have hx := hgas; rw [hcadd] at hx
        simp only [List.sum_append] at hx
        show (chargeCache prog sloadChg b).sum ≤ _; omega
      have hstkb : fr.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).length ≤ 1024 := by
        have hx := hstk; rw [hcadd] at hx
        simp only [List.length_append] at hx
        show fr.exec.stack.size + (chargeCache prog sloadChg b).length ≤ 1024; omega
      obtain ⟨hfreea, hfreeb⟩ := RematClosureFree.add_inv hfree
      obtain ⟨frb, hmrb⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp b) vb fr hdb hsound
        hfreeb hscoped hstore (by nofun) (by nofun) hmemreal hevb hgasb hstkb
      have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
      have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog b).length := by
        have := hmrb.pc; simpa only [matExpr_tmp] using this
      have hda' : MatDecC prog hdc hord frb.exec.executionEnv.code frb.exec.pc (.tmp a) := by
        rw [hbcode, hbpc]; exact hda
      have hsum_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)).sum
          = (chargeCache prog sloadChg b).sum + (chargeCache prog sloadChg a).sum + Gverylow := by
        rw [hcadd]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
      have hlen_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)).length
          = (chargeCache prog sloadChg b).length + (chargeCache prog sloadChg a).length + 1 := by
        rw [hcadd]; simp only [List.length_append, List.length_singleton]
      have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
        rw [hmrb.stack]; simp [Stack.push]
      have hgasa : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).sum
          ≤ frb.exec.gasAvailable.toNat := by
        rw [hmrb.gasToNat]; show (chargeCache prog sloadChg a).sum ≤ _
        rw [hsum_split] at hgas; simp only [chargeExpr_tmp] at hgas ⊢; omega
      have hstka : frb.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).length ≤ 1024 := by
        have hpb1 : 1 ≤ (chargeCache prog sloadChg b).length := chargeCache_length_pos prog sloadChg b
        rw [hlen_split] at hstk; rw [hfrbsz]
        show fr.exec.stack.size + 1 + (chargeCache prog sloadChg a).length ≤ 1024; omega
      obtain ⟨fra, hmra⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp a) va frb hda' hsound
        hfreea hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
        (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hgasa hstka
      have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
        rw [hmra.code, hbcode]
      have hapc : fra.exec.pc
          = fr.exec.pc + UInt32.ofNat (matCache prog b).length
              + UInt32.ofNat (matCache prog a).length := by
        have := hmra.pc; simp only [matExpr_tmp] at this; rw [this, hbpc]
      have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
        rw [hmra.stack, hmrb.stack]; rfl
      have hadec : decode fra.exec.executionEnv.code fra.exec.pc
          = some (.ArithLogic .ADD, .none) := by rw [hacode, hapc]; exact hop
      have haszle : fra.exec.stack.size ≤ 1024 := by
        have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length := chargeCache_length_pos prog sloadChg a
        rw [hlen_split] at hstk; rw [hfrasz]; omega
      have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
        rw [hmra.gasToNat, hmrb.gasToNat]
        simp only [chargeExpr_tmp]; rw [hsum_split] at hgas; omega
      obtain ⟨hadrun, hadstk⟩ := sim_add fra va vb fr.exec.stack hadec hastk haszle hagas
      have hgc : (addFrame fra va vb fr.exec.stack).exec.gasAvailable
          = subCharges fr.exec.gasAvailable
              (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)) := by
        rw [hcadd]
        exact gasCharge_binop_glue fr.exec.gasAvailable (chargeCache prog sloadChg b)
          (chargeCache prog sloadChg a) frb fra (addFrame fra va vb fr.exec.stack)
          hmrb.gasCharge hmra.gasCharge (charge_binOpPost_gas fra UInt256.add va vb fr.exec.stack)
      refine ⟨addFrame fra va vb fr.exec.stack,
        { runs := (hmrb.runs.trans hmra.runs).trans hadrun
          stack := ?_, code := ?_, validJumps := ?_, addr := ?_, canMod := ?_, accounts := ?_
          storage := ?_, pc := ?_, gasCharge := hgc, gasToNat := ?_
          memBytes := by rw [addFrame_memory]; exact hmra.memBytes.trans hmrb.memBytes
          memActive := le_trans hmrb.memActive
            (le_trans hmra.memActive (by rw [addFrame_activeWords]))
          activeWordsEq := by
            rw [addFrame_activeWords, hmra.activeWordsEq, hmrb.activeWordsEq] }⟩
      · rw [hadstk]
      · rw [addFrame_code, hacode]
      · rw [addFrame_validJumps, hmra.validJumps, hmrb.validJumps]
      · rw [addFrame_addr, hmra.addr, hmrb.addr]
      · show (addFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState = _
        rw [show (addFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState
              = fra.exec.executionEnv.canModifyState from rfl, hmra.canMod, hmrb.canMod]
      · show (addFrame fra va vb fr.exec.stack).exec.accounts = _
        rw [show (addFrame fra va vb fr.exec.stack).exec.accounts
              = fra.exec.accounts from rfl, hmra.accounts, hmrb.accounts]
      · intro k; rw [addFrame_selfStorage, hmra.storage, hmrb.storage]
      · rw [addFrame_pc, hapc, matExpr_add]
        simp only [List.length_append, List.length_singleton]
        rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1 : UInt32) = 1 from rfl]
        ac_rfl
      · rw [hgc]; exact toNat_subCharges fr.exec.gasAvailable _ hgas
  | .lt a b, hfree, hdec, _, _, heval, hgas, hstk =>
      obtain ⟨va, hla, vb, hlb, hwlt⟩ :
          ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb ∧ w = UInt256.lt va vb := by
        simp only [evalExpr] at heval
        cases hla : st.locals a with
        | none => simp [hla] at heval
        | some va =>
            cases hlb : st.locals b with
            | none => simp [hla, hlb] at heval
            | some vb => refine ⟨va, rfl, vb, rfl, ?_⟩; simp [hla, hlb] at heval; exact heval.symm
      subst hwlt
      rw [matDecC_lt] at hdec
      obtain ⟨hdb, hda, hop⟩ := hdec
      have hclt := chargeExpr_lt sloadChg (chargeCache prog sloadChg) a b
      have hevb : evalExpr st obs (.tmp b) = some vb := hlb
      have heva : evalExpr st obs (.tmp a) = some va := hla
      have hgasb : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).sum
          ≤ fr.exec.gasAvailable.toNat := by
        have hx := hgas; rw [hclt] at hx
        simp only [List.sum_append] at hx
        show (chargeCache prog sloadChg b).sum ≤ _; omega
      have hstkb : fr.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).length ≤ 1024 := by
        have hx := hstk; rw [hclt] at hx
        simp only [List.length_append] at hx
        show fr.exec.stack.size + (chargeCache prog sloadChg b).length ≤ 1024; omega
      obtain ⟨hfreea, hfreeb⟩ := RematClosureFree.lt_inv hfree
      obtain ⟨frb, hmrb⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp b) vb fr hdb hsound
        hfreeb hscoped hstore (by nofun) (by nofun) hmemreal hevb hgasb hstkb
      have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
      have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog b).length := by
        have := hmrb.pc; simpa only [matExpr_tmp] using this
      have hda' : MatDecC prog hdc hord frb.exec.executionEnv.code frb.exec.pc (.tmp a) := by
        rw [hbcode, hbpc]; exact hda
      have hsum_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)).sum
          = (chargeCache prog sloadChg b).sum + (chargeCache prog sloadChg a).sum + Gverylow := by
        rw [hclt]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
      have hlen_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)).length
          = (chargeCache prog sloadChg b).length + (chargeCache prog sloadChg a).length + 1 := by
        rw [hclt]; simp only [List.length_append, List.length_singleton]
      have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
        rw [hmrb.stack]; simp [Stack.push]
      have hgasa : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).sum
          ≤ frb.exec.gasAvailable.toNat := by
        rw [hmrb.gasToNat]; show (chargeCache prog sloadChg a).sum ≤ _
        rw [hsum_split] at hgas; simp only [chargeExpr_tmp] at hgas ⊢; omega
      have hstka : frb.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).length ≤ 1024 := by
        have hpb1 : 1 ≤ (chargeCache prog sloadChg b).length := chargeCache_length_pos prog sloadChg b
        rw [hlen_split] at hstk; rw [hfrbsz]
        show fr.exec.stack.size + 1 + (chargeCache prog sloadChg a).length ≤ 1024; omega
      obtain ⟨fra, hmra⟩ := materialise_runsC hdc hord sloadChg st obs I (.tmp a) va frb hda' hsound
        hfreea hscoped (hstore.transport hmrb.storage) (by nofun) (by nofun)
        (hmemreal.transport hmrb.memBytes hmrb.memActive) heva hgasa hstka
      have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
        rw [hmra.code, hbcode]
      have hapc : fra.exec.pc
          = fr.exec.pc + UInt32.ofNat (matCache prog b).length
              + UInt32.ofNat (matCache prog a).length := by
        have := hmra.pc; simp only [matExpr_tmp] at this; rw [this, hbpc]
      have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
        rw [hmra.stack, hmrb.stack]; rfl
      have hadec : decode fra.exec.executionEnv.code fra.exec.pc
          = some (.ArithLogic .LT, .none) := by rw [hacode, hapc]; exact hop
      have haszle : fra.exec.stack.size ≤ 1024 := by
        have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length := chargeCache_length_pos prog sloadChg a
        rw [hlen_split] at hstk; rw [hfrasz]; omega
      have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
        rw [hmra.gasToNat, hmrb.gasToNat]
        simp only [chargeExpr_tmp]; rw [hsum_split] at hgas; omega
      obtain ⟨hadrun, hadstk⟩ := sim_lt fra va vb fr.exec.stack hadec hastk haszle hagas
      have hgc : (ltFrame fra va vb fr.exec.stack).exec.gasAvailable
          = subCharges fr.exec.gasAvailable
              (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)) := by
        rw [hclt]
        exact gasCharge_binop_glue fr.exec.gasAvailable (chargeCache prog sloadChg b)
          (chargeCache prog sloadChg a) frb fra (ltFrame fra va vb fr.exec.stack)
          hmrb.gasCharge hmra.gasCharge (charge_binOpPost_gas fra UInt256.lt va vb fr.exec.stack)
      refine ⟨ltFrame fra va vb fr.exec.stack,
        { runs := (hmrb.runs.trans hmra.runs).trans hadrun
          stack := ?_, code := ?_, validJumps := ?_, addr := ?_, canMod := ?_, accounts := ?_
          storage := ?_, pc := ?_, gasCharge := hgc, gasToNat := ?_
          memBytes := by rw [ltFrame_memory]; exact hmra.memBytes.trans hmrb.memBytes
          memActive := le_trans hmrb.memActive
            (le_trans hmra.memActive (by rw [ltFrame_activeWords]))
          activeWordsEq := by
            rw [ltFrame_activeWords, hmra.activeWordsEq, hmrb.activeWordsEq] }⟩
      · rw [hadstk]
      · rw [ltFrame_code, hacode]
      · rw [ltFrame_validJumps, hmra.validJumps, hmrb.validJumps]
      · rw [ltFrame_addr, hmra.addr, hmrb.addr]
      · show (ltFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState = _
        rw [show (ltFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState
              = fra.exec.executionEnv.canModifyState from rfl, hmra.canMod, hmrb.canMod]
      · show (ltFrame fra va vb fr.exec.stack).exec.accounts = _
        rw [show (ltFrame fra va vb fr.exec.stack).exec.accounts
              = fra.exec.accounts from rfl, hmra.accounts, hmrb.accounts]
      · intro k; rw [ltFrame_selfStorage, hmra.storage, hmrb.storage]
      · rw [ltFrame_pc, hapc, matExpr_lt]
        simp only [List.length_append, List.length_singleton]
        rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1 : UInt32) = 1 from rfl]
        ac_rfl
      · rw [hgc]; exact toNat_subCharges fr.exec.gasAvailable _ hgas
  termination_by matDecMeasure prog e
  decreasing_by
    all_goals
      first
        | (simp only [matDecMeasure]; omega)
        | (exact matDecMeasure_remat_lt prog hdc hord (by assumption))

end ValueChannel

/-! ## `matDecC_of_lower` / `matDecC_of_term` — `MatDecC` at statement / terminator cursors

The cursor-level specialisations of `matDecC_of_seg` (the fuel-free successors of the deleted
fuel-era `matDec_of_lower`/`matDec_of_term`): the fold bytes `matExpr (matCache prog) e` of a
statement (resp. terminator) operand form a contiguous sub-list of `emitStmt` (resp. `emitTerm`),
so the byte-segment hypothesis holds at `pcOf prog L pc + offset` (resp. `termOf prog L + offset`)
via the byte anchors `flatBytes_at_pcOf_offset` / `flatBytes_at_termOf`
(`Decode/DecodeAnchors.lean`), and the whole `MatDecC` bundle over `lower prog` follows. This is
the generic discharge of the value channel's carried `MatDecC` hypothesis at any statement /
terminator cursor. -/

/-- **`MatDecC` at a statement cursor.** For an operand `e` whose fold bytes form the sub-list of
statement `s`'s lowering at byte `offset`, the whole `MatDecC` bundle holds over `lower prog` at
`UInt32.ofNat (pcOf prog L pc + offset)` — `matDecC_of_seg` anchored by
`flatBytes_at_pcOf_offset`. -/
theorem matDecC_of_lower (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (L : Label) (b : Block) (pc : ℕ) (s : Stmt) (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hsub : ∀ j, j < (matExpr (matCache prog) e).length →
        (emitStmt (matCache prog) (defsOf prog) s)[offset + j]?
          = (matExpr (matCache prog) e)[j]?)
    (hin : offset + (matExpr (matCache prog) e).length
        ≤ (emitStmt (matCache prog) (defsOf prog) s).length)
    (hbound : pcOf prog L pc + offset + (matExpr (matCache prog) e).length ≤ 2 ^ 32) :
    MatDecC prog hdc hord (lower prog) (UInt32.ofNat (pcOf prog L pc + offset)) e :=
  matDecC_of_seg prog hdc hord e (pcOf prog L pc + offset) (by omega)
    (fun j hj => by
      have hanchor := flatBytes_at_pcOf_offset prog L b pc s (offset + j) hb hs (by omega)
      rw [show pcOf prog L pc + (offset + j) = pcOf prog L pc + offset + j from by ring]
        at hanchor
      rw [hanchor]; exact hsub j hj)

/-- **`MatDecC` at a terminator cursor.** For an operand `e` whose fold bytes form the sub-list
of `emitTerm … b.term` at byte `offset`, the whole `MatDecC` bundle holds over `lower prog` at
`UInt32.ofNat (termOf prog L + offset)` — `matDecC_of_seg` anchored by `flatBytes_at_termOf`.
The branch's cond materialise is this at `offset = 0`. -/
theorem matDecC_of_term (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (L : Label) (b : Block) (offset : ℕ) (e : Expr)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hsub : ∀ j, j < (matExpr (matCache prog) e).length →
        (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[offset + j]?
          = (matExpr (matCache prog) e)[j]?)
    (hin : offset + (matExpr (matCache prog) e).length
        ≤ (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length)
    (hbound : termOf prog L + offset + (matExpr (matCache prog) e).length ≤ 2 ^ 32) :
    MatDecC prog hdc hord (lower prog) (UInt32.ofNat (termOf prog L + offset)) e :=
  matDecC_of_seg prog hdc hord e (termOf prog L + offset) (by omega)
    (fun j hj => by
      have hanchor := flatBytes_at_termOf prog L b (offset + j) hb (by omega)
      rw [show termOf prog L + (offset + j) = termOf prog L + offset + j from by ring]
        at hanchor
      rw [hanchor]; exact hsub j hj)

end Lir
