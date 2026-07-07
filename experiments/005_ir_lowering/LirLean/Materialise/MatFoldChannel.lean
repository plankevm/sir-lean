import LirLean.Spec.WellFormed

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
`MatFueled`, and — like `matCache_unfold` — **NO bridge to the fuel `chargeOf`** (unsound in
exactly the way the `matCache = materialiseExpr` bridge is, design §2.2).

The **chargeCache↔matCache length lockstep** (bottom): for a `t` present in `defEnv prog`, the
charge cache and the byte cache unfold *in lockstep* — the SAME membership hypothesis
`(t, loc) ∈ defEnv prog` drives parallel `chargeExpr`/`matExpr` (resp. `.slot` / absent)
conclusions — so the future fuel-free restatement of the `StackRoomOK`/`maxChargeDepth` folds and
the P5 `materialise_runsC` recursion can read a charge-list LENGTH that decomposes exactly as
`matCache prog t`'s operand structure does. -/

namespace Lir.V2

/-! ### Operand-locality of `chargeExpr` (the `matExpr_congr` twin) -/

/-- **Operand-locality of `chargeExpr`.** `chargeExpr` reads its cache only at the tmps the
expression uses, so two caches agreeing on every used tmp emit identical charge lists (the
`matExpr_congr` twin; drives the `.remat` step of `chargeCache_unfold`). -/
theorem chargeExpr_congr {sc : Tmp → ℕ} {c c' : Tmp → List ℕ} {e : Expr}
    (h : ∀ t, usesInExpr t e ≠ 0 → c t = c' t) : chargeExpr sc c e = chargeExpr sc c' e := by
  cases e with
  | imm w => rfl
  | gas => rfl
  | slot n => rfl
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

The fuel-free, cache-keyed twin of `MatDec` (`MaterialiseRuns.lean`). `MatDec` recurses through
tmp *definitions* on `fuel` (`.tmp t` with `defs t = some e` ⇒ `MatDec … f p e`); the fold twin
recurses through them along the **def-env graph**, which is well-founded because `DefEnvOrdered`
places every operand of a `.remat` entry strictly earlier in `defEnv prog`. So `MatDecC`:

* is **structural** for the composite arms (`.add`/`.lt`/`.sload` recurse to their operand
  `.tmp`s, anchoring the sub-decodes at the **operand cache lengths** `(matCache prog t').length`
  — the fold analogue of `MatDec`'s `(materialiseExpr defs f (.tmp t')).length`), and
* **unfolds `.tmp t` via `matCache_unfold`**: it dispatches on `allocate prog t` (the tmp's
  canonical `Loc`, which `matCache_unfold` resolves `matCache prog t` to) — a `.remat e` recurses
  into `e`, a `.slot n` is the spill-load `PUSH n; MLOAD` decode, an absent tmp is the `PUSH32 0`
  leaf.

Termination is the fuel-free replacement for `MatDec`'s `fuel` index: the measure
`matDecMeasure prog e = 3·(def-env first-index of e's outermost operands) + arm-tag` strictly
decreases at every recursive call — the composite→operand steps by arithmetic, the
`.tmp t`→definiens step by `DefEnvOrdered` (`matDecMeasure_remat_lt`). NO `MatFueled`, NO fuel
cases, NO `matCache = materialiseExpr` bridge. -/

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
  | .slot _  => 0
  | .gas     => 0
  | .tmp t   => 3 * tmpIdx prog t + 1
  | .add a b => 3 * max (tmpIdx prog a) (tmpIdx prog b) + 2
  | .lt  a b => 3 * max (tmpIdx prog a) (tmpIdx prog b) + 2
  | .sload k => 3 * tmpIdx prog k + 2

/-- **`allocate` ⇒ `defEnv` membership.** If `t`'s canonical location is `some loc`, the
`(t, loc)` pair sits in `defEnv prog` — the converse of `defEnv_entry_eq_allocate`, via the
`defsOf`/`find?` view (`defsOf_eq_defEnv_find`) and the SSA single-binding `Loc` alignment. -/
theorem mem_defEnv_of_allocate (prog : Program) (hdc : DefsConsistent prog)
    {t : Tmp} {loc : Loc} (h : allocate prog t = some loc) : (t, loc) ∈ defEnv prog := by
  have hdefs : defsOf prog t = some loc.toDef := by
    have h2 := congrFun (allocate_toDefs prog) t
    simp only [Alloc.toDefs, h, Option.map_some] at h2; exact h2.symm
  rw [defsOf_eq_defEnv_find, Option.map_eq_some_iff] at hdefs
  obtain ⟨⟨tt, loc'⟩, hfind, _⟩ := hdefs
  have htt : tt = t := by have := List.find?_some hfind; simpa using this
  subst htt
  have hmem : (tt, loc') ∈ defEnv prog := List.mem_of_find?_eq_some hfind
  have hall := defEnv_entry_eq_allocate prog hdc hmem
  rw [h] at hall
  have : loc' = loc := (Option.some.inj hall).symm
  rw [this] at hmem; exact hmem

/-- **`allocate = none` ⇒ absent from `defEnv`.** An unallocated tmp is not a `defEnv` key, so
`matCache prog t` falls to the `matInit` leaf (`matCache_absent`). -/
theorem not_mem_defEnv_of_allocate_none (prog : Program) {t : Tmp}
    (h : allocate prog t = none) : t ∉ (defEnv prog).map Prod.fst := by
  have hdefs : defsOf prog t = none := by
    have h2 := congrFun (allocate_toDefs prog) t
    simp only [Alloc.toDefs, h, Option.map_none] at h2; exact h2.symm
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
  | slot _ => simp only [matDecMeasure, tmpIdx]; omega
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

/-- **`MatDecC` — the cache-keyed decode bundle (fuel-free twin of `MatDec`).** One `decode`
clause per opcode `matExpr (matCache prog) e` emits, anchored at the running pc; composite arms
anchor their sub-decodes at the **operand cache lengths** `(matCache prog t').length`, and the
`.tmp t` arm unfolds via `allocate prog t` (`matCache_unfold`'s `Loc`). No fuel, no `MatFueled`. -/
def MatDecC (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (code : ByteArray) : UInt32 → Expr → Prop
  | p, .imm w  => decode code p = some (.Push .PUSH32, some (w, 32))
  | p, .slot n =>
      decode code p = some (.Push .PUSH32, some (UInt256.ofNat n, 32))
      ∧ decode code (p + UInt32.ofNat (emitImm (UInt256.ofNat n)).length)
          = some (.Smsf .MLOAD, .none)
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

@[simp] theorem matDecC_slot (p : UInt32) (n : Nat) :
    MatDecC prog hdc hord code p (.slot n)
      = (decode code p = some (.Push .PUSH32, some (UInt256.ofNat n, 32))
         ∧ decode code (p + UInt32.ofNat (emitImm (UInt256.ofNat n)).length)
             = some (.Smsf .MLOAD, .none)) := by
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

/-! ### `matDecC_of_seg` — the byte-segment bridge over the fold (twin of `matDec_of_seg`)

The fuel-free twin of `matDec_of_seg` (`MatDecLower.lean`): from a segment hypothesis that the
bytes `matExpr (matCache prog) e` sit in `flatBytesF prog` at `[base, base+len)`, the full
`MatDecC` bundle holds at `UInt32.ofNat base` over `lowerF prog`. Proved by **structural
recursion on `e`** (composite arms split their operand sub-segments off the parent) plus the
**def-env recursion** for the `.tmp t` arm (its bytes `matCache prog t` unfold via
`matCache_unfold` to the definiens `e'`'s bytes, and `matDecMeasure_remat_lt` justifies the
descent — NO fuel, NO `MatFueled`). The per-`lowerF` leaf decodes reuse `MatDecLower`'s
lowering-independent `extract_toList_eq`/`uInt256_wordBytesBE` through the `decode_lowerF_*`
specialisations. -/

/-- Generic prefix-of-a-segment (the `seg_prefix` twin over an arbitrary byte list). -/
theorem segF_prefix (bytes : List UInt8) (base : ℕ) (pre suf : List UInt8)
    (h : ∀ j, j < (pre ++ suf).length → bytes[base + j]? = (pre ++ suf)[j]?) :
    ∀ j, j < pre.length → bytes[base + j]? = pre[j]? := by
  intro j hj
  rw [h j (by rw [List.length_append]; omega), List.getElem?_append_left hj]

/-- Generic suffix-of-a-segment (the `seg_suffix` twin over an arbitrary byte list). -/
theorem segF_suffix (bytes : List UInt8) (base : ℕ) (pre suf : List UInt8)
    (h : ∀ j, j < (pre ++ suf).length → bytes[base + j]? = (pre ++ suf)[j]?) :
    ∀ j, j < suf.length → bytes[base + pre.length + j]? = suf[j]? := by
  intro j hj
  have := h (pre.length + j) (by rw [List.length_append]; omega)
  rw [show base + (pre.length + j) = base + pre.length + j from by ring] at this
  rw [this, List.getElem?_append_right (by omega), show pre.length + j - pre.length = j from by omega]

/-- **`.imm` leaf decode over `lowerF`** (the `imm_leaf_decode` twin). -/
theorem imm_leaf_decodeF (prog : Program) (base : ℕ) (w : Word)
    (hbound : base + 33 ≤ 2 ^ 32)
    (hseg : ∀ j, j < (emitImm w).length → (flatBytesF prog)[base + j]? = (emitImm w)[j]?) :
    decode (lowerF prog) (UInt32.ofNat base) = some (.Push .PUSH32, some (w, 32)) := by
  have hemit : (emitImm w).length = 33 := emitImm_length w
  have hbyte : (flatBytesF prog)[base]? = some Byte.push32 := by
    have := hseg 0 (by omega); simpa [emitImm] using this
  have hwin : ((flatBytesF prog).toArray.extract (base + 1) (base + 1 + 32)).toList = wordBytesBE w := by
    apply extract_toList_eq (flatBytesF prog) (base + 1) 32 (wordBytesBE w) (by simp [wordBytesBE])
    intro j hj
    have := hseg (1 + j) (by rw [hemit]; omega)
    rw [show base + (1 + j) = base + 1 + j from by ring] at this
    rw [this, show (1 + j) = j + 1 from by ring]
    simp [emitImm, List.getElem?_cons_succ]
  have himm : uInt256OfByteArray ⟨(flatBytesF prog).toArray.extract (base + 1) (base + 1 + 32)⟩ = w := by
    have hh : uInt256OfByteArray ⟨(flatBytesF prog).toArray.extract (base + 1) (base + 1 + 32)⟩
        = uInt256OfByteArray ⟨(wordBytesBE w).toArray⟩ := by
      unfold uInt256OfByteArray
      congr 2
      show ((flatBytesF prog).toArray.extract (base + 1) (base + 1 + 32)).toList.reverse = _
      rw [hwin]
    rw [hh, uInt256_wordBytesBE]
  have hp : Evm.pushArgWidth (Evm.parseInstr Byte.push32) = (32 : UInt8) := by decide
  have h32 : (32 : UInt8).toNat = 32 := by decide
  have hres := decode_lowerF_push prog base Byte.push32 32 w (by omega) hbyte hp (by decide)
    (by rw [h32]; exact himm)
  rw [hres]; rfl

/-- **Non-push opcode leaf decode over `lowerF`** (the `nonpush_leaf_decode` twin). -/
theorem nonpush_leaf_decodeF (prog : Program) (base off : ℕ) (byte : UInt8) (seg : List UInt8)
    (hbound : base + off < 2 ^ 32)
    (hoff : seg[off]? = some byte)
    (hnp : Evm.pushArgWidth (Evm.parseInstr byte) = 0)
    (hseg : ∀ j, j < seg.length → (flatBytesF prog)[base + j]? = seg[j]?) :
    decode (lowerF prog) (UInt32.ofNat (base + off)) = some (Evm.parseInstr byte, .none) := by
  have hoffl : off < seg.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hoff; exact absurd hoff (by simp)
  have hbyte : (flatBytesF prog)[base + off]? = some byte := by rw [hseg off hoffl]; exact hoff
  exact decode_lowerF_nonpush prog (base + off) byte hbound hbyte hnp

/-- **`.slot` leaf decode over `lowerF`** (the `slot_leaf_decode` twin). -/
theorem slot_leaf_decodeF (prog : Program) (base slot : ℕ)
    (hbound : base + (emitImm (UInt256.ofNat slot) ++ [Byte.mload]).length ≤ 2 ^ 32)
    (hseg : ∀ j, j < (emitImm (UInt256.ofNat slot) ++ [Byte.mload]).length →
      (flatBytesF prog)[base + j]? = (emitImm (UInt256.ofNat slot) ++ [Byte.mload])[j]?) :
    decode (lowerF prog) (UInt32.ofNat base) = some (.Push .PUSH32, some (UInt256.ofNat slot, 32))
    ∧ decode (lowerF prog) (UInt32.ofNat base
        + UInt32.ofNat (emitImm (UInt256.ofNat slot)).length) = some (.Smsf .MLOAD, .none) := by
  have hlen : (emitImm (UInt256.ofNat slot)).length = 33 := emitImm_length _
  rw [List.length_append, hlen, List.length_singleton] at hbound
  refine ⟨imm_leaf_decodeF prog base (UInt256.ofNat slot) (by omega)
      (segF_prefix (flatBytesF prog) base (emitImm (UInt256.ofNat slot)) [Byte.mload] hseg), ?_⟩
  rw [hlen, ofNat_add']
  have hmload := nonpush_leaf_decodeF prog base 33 Byte.mload
      (emitImm (UInt256.ofNat slot) ++ [Byte.mload]) (by omega)
      (by rw [List.getElem?_append_right (by rw [hlen]), hlen]; rfl)
      (by decide) hseg
  simpa using hmload

/-- **`matDecC_of_seg` (core deliverable).** The whole `MatDecC` bundle over `lowerF prog` from a
segment of the fold bytes `matExpr (matCache prog) e` at `base`. Structural on `e`; the `.tmp`
arm descends the def-env via `matCache_unfold` (`matDecMeasure_remat_lt`). -/
theorem matDecC_of_seg (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (e : Expr) (base : ℕ)
    (hbound : base + (matExpr (matCache prog) e).length ≤ 2 ^ 32)
    (hseg : ∀ j, j < (matExpr (matCache prog) e).length →
        (flatBytesF prog)[base + j]? = (matExpr (matCache prog) e)[j]?) :
    MatDecC prog hdc hord (lowerF prog) (UInt32.ofNat base) e := by
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
  | .slot n, hbound, hseg =>
      rw [matDecC_slot]
      simp only [matExpr_slot] at hseg hbound
      exact slot_leaf_decodeF prog base n hbound hseg
  | .add a b, hbound, hseg =>
      rw [matDecC_add]
      have hmat : matExpr (matCache prog) (.add a b)
          = matCache prog b ++ matCache prog a ++ [Byte.add] := by simp only [matExpr_add]
      rw [hmat] at hseg hbound
      have hsegBA := segF_prefix (flatBytesF prog) base (matCache prog b ++ matCache prog a)
        [Byte.add] hseg
      have hsegb := segF_prefix (flatBytesF prog) base (matCache prog b) (matCache prog a) hsegBA
      have hsega := segF_suffix (flatBytesF prog) base (matCache prog b) (matCache prog a) hsegBA
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
      have hsegBA := segF_prefix (flatBytesF prog) base (matCache prog b ++ matCache prog a)
        [Byte.lt] hseg
      have hsegb := segF_prefix (flatBytesF prog) base (matCache prog b) (matCache prog a) hsegBA
      have hsega := segF_suffix (flatBytesF prog) base (matCache prog b) (matCache prog a) hsegBA
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
      have hsegk := segF_prefix (flatBytesF prog) base (matCache prog k) [Byte.sload] hseg
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
          rw [matDecC_tmp_none prog hdc hord (lowerF prog) (UInt32.ofNat base) t hal]
          have hc : matCache prog t = emitImm 0 :=
            matCache_absent prog (not_mem_defEnv_of_allocate_none prog hal)
          simp only [matExpr_tmp, hc] at hseg hbound
          exact imm_leaf_decodeF prog base (0 : Word) (by rw [emitImm_length] at hbound; omega) hseg
      | some loc =>
          cases loc with
          | remat e' =>
              rw [matDecC_tmp_remat prog hdc hord (lowerF prog) (UInt32.ofNat base) t e' hal]
              have hc : matCache prog t = matExpr (matCache prog) e' :=
                matCache_remat prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              apply matDecC_of_seg prog hdc hord e' base
              · simp only [matExpr_tmp, hc] at hbound; exact hbound
              · simp only [matExpr_tmp, hc] at hseg; exact hseg
          | slot n =>
              rw [matDecC_tmp_slot prog hdc hord (lowerF prog) (UInt32.ofNat base) t n hal]
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

end Lir.V2
