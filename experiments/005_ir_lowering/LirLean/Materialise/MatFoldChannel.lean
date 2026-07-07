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

end Lir.V2
