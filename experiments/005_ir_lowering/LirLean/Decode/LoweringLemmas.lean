import LirLean.Spec.Lowering

/-!
# LirLean — lowering lemmas (extracted from `Spec/Lowering.lean`)

The proof companions of the pure lowering definitions (`LirLean/Spec/Lowering.lean`):
the `defsOf` spill-routing exhaustiveness facts (`defsOf_ne_gas` / `defsOf_ne_sload`)
and the allocation-faithfulness keystone (`toDef_locOfExpr` / `allocate_toDefs`).
Extracted so `Spec/Lowering.lean` stays a definitions-only spec-core file (Wave 3,
`docs/fleet-2026-07-02/reorg-legibility.md` §5 Step 3); every former importer of
`LirLean.Lowering` imports this module instead, so the `@[simp]` attribute and the
lemmas stay reachable exactly as before.
-/

namespace Lir

/-- `defsOf` never registers a tmp as the bare `Expr.gas`: a gas assign is routed to the
spill-load `Expr.slot (slotOf t)` (Phase B), and no other `defsOf` arm produces `.gas`. So
the recompute env's `.gas` body has been retired — every gas tmp is a memory slot. -/
theorem defsOf_ne_gas (prog : Program) (t : Tmp) : defsOf prog t ≠ some .gas := by
  -- (Cross-module extraction note: the original in-file proof `cases`-abstracted the
  -- `List.find?` scrutinee by an explicit term, which no longer matches the unfolded
  -- goal's matcher auxiliaries from another module; this proof decomposes the found
  -- pair through `Option.map_eq_some_iff` instead. Statement unchanged.)
  intro hgas
  simp only [defsOf] at hgas
  obtain ⟨pr, _hf, hpr⟩ := Option.map_eq_some_iff.mp hgas
  have hmem := List.mem_of_find?_eq_some _hf
  obtain ⟨b, _, hbmem⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, _, hsmap⟩ := List.mem_filterMap.mp hbmem
  -- `pr.2` is one of the filterMap outputs; none is `.gas`.
  cases s with
  | assign t' e' =>
      cases e' with
      | gas => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | imm w => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | tmp t'' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | add a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | lt a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | sload k => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | slot n => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
  | sstore _ _ => simp at hsmap
  | call cs =>
      obtain ⟨callee, gasFwd, rt⟩ := cs
      cases rt with
      | none => simp at hsmap
      | some t'' =>
          simp only [Option.some.injEq] at hsmap
          rw [← hsmap] at hpr; simp at hpr
  | create cs =>
      obtain ⟨value, initOffset, initSize, salt, rt⟩ := cs
      cases rt with
      | none => simp at hsmap
      | some t'' =>
          simp only [Option.some.injEq] at hsmap
          rw [← hsmap] at hpr; simp at hpr

/-- `defsOf` never registers a tmp as a bare `Expr.sload _`: an sload assign is routed to the
spill-load `Expr.slot (slotOf t)` (Phase C), and no other `defsOf` arm produces `.sload`. So
the recompute env's `.sload` body has been retired — every sload tmp is a memory slot, read
once at the def-site (cold/warm warmth charged once) and reused via `MLOAD`. -/
theorem defsOf_ne_sload (prog : Program) (t : Tmp) (k : Tmp) :
    defsOf prog t ≠ some (.sload k) := by
  -- (Same cross-module extraction note as `defsOf_ne_gas`. Statement unchanged.)
  intro hsl
  simp only [defsOf] at hsl
  obtain ⟨pr, _hf, hpr⟩ := Option.map_eq_some_iff.mp hsl
  have hmem := List.mem_of_find?_eq_some _hf
  obtain ⟨b, _, hbmem⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, _, hsmap⟩ := List.mem_filterMap.mp hbmem
  -- `pr.2` is one of the filterMap outputs; none is `.sload`.
  cases s with
  | assign t' e' =>
      cases e' with
      | gas => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | imm w => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | tmp t'' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | add a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | lt a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | sload k' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | slot n => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
  | sstore _ _ => simp at hsmap
  | call cs =>
      obtain ⟨callee, gasFwd, rt⟩ := cs
      cases rt with
      | none => simp at hsmap
      | some t'' =>
          simp only [Option.some.injEq] at hsmap
          rw [← hsmap] at hpr; simp at hpr
  | create cs =>
      obtain ⟨value, initOffset, initSize, salt, rt⟩ := cs
      cases rt with
      | none => simp at hsmap
      | some t'' =>
          simp only [Option.some.injEq] at hsmap
          rw [← hsmap] at hpr; simp at hpr

/-! ## `rematOf` — the non-`.slot` projection of `defsOf` (Phase 2A spine decouple) -/

/-- Every `rematOf` binding is a `defsOf` binding: `rematOf` only *drops* the spilled
(`.slot`) entries, it never invents one. -/
theorem defsOf_of_rematOf {prog : Program} {t : Tmp} {e : Expr}
    (h : rematOf prog t = some e) : defsOf prog t = some e := by
  rw [rematOf] at h
  split at h
  · exact absurd h (by nofun)
  · rename_i e' heq; rw [heq]; exact h
  · exact absurd h (by nofun)

/-- A non-`.slot` `defsOf` binding is a `rematOf` binding: on the rematerialised entries the
two views coincide. -/
theorem rematOf_of_defsOf {prog : Program} {t : Tmp} {e : Expr}
    (hd : defsOf prog t = some e) (hns : ∀ n, e ≠ .slot n) : rematOf prog t = some e := by
  unfold rematOf; rw [hd]
  cases e with
  | slot n => exact absurd rfl (hns n)
  | _ => rfl

/-- `rematOf` never registers a tmp as the bare `Expr.gas` (the `defsOf` twin, lifted through
`defsOf_of_rematOf`): gas tmps are spilled to `.slot` and dropped by `rematOf`. -/
theorem rematOf_ne_gas (prog : Program) (t : Tmp) : rematOf prog t ≠ some .gas :=
  fun h => defsOf_ne_gas prog t (defsOf_of_rematOf h)

/-- `rematOf` never registers a tmp as a bare `Expr.sload _` (the `defsOf` twin, lifted
through `defsOf_of_rematOf`): sload tmps are spilled to `.slot` and dropped by `rematOf`. -/
theorem rematOf_ne_sload (prog : Program) (t : Tmp) (k : Tmp) :
    rematOf prog t ≠ some (.sload k) :=
  fun h => defsOf_ne_sload prog t k (defsOf_of_rematOf h)

/-- `Loc.toDef` is a left inverse of `locOfExpr` on every expression. -/
@[simp] theorem toDef_locOfExpr (e : Expr) : (locOfExpr e).toDef = e := by
  cases e <;> rfl

/-! ## §S2 (c) — `defEnv` ↔ `defsOf` alignment (Phase 2A step S2)

`defsOf` is a global `find?` over the program-order `pairs` list; `defEnv` is that SAME
list carrying `Loc` instead of `Expr` (each `Loc` re-flattens to its `Expr` via `Loc.toDef`,
`toDef_locOfExpr`). So `defsOf` is exactly `defEnv`'s `find?`-view, mapped through `Loc.toDef`
— proven here unconditionally (definitional up to the map/find? fusion lemmas). This is the
alignment the S3 fold↔fuel bridge rests on. -/

/-- **`defsOf`'s internal `pairs` list is `defEnv prog` mapped through `Loc.toDef`.** Stated
as a function equality with `defsOf` on the left so that unfolding it exposes `defsOf`'s own
`find?`-over-`pairs`; the RHS carries the `defEnv.map`-form of the same list, so `congr`
reduces the whole thing to the per-statement `filterMap` identity (each `Loc` re-flattens to
its `Expr` by `toDef_locOfExpr`). -/
theorem defsOf_eq_find_defEnv_map (prog : Program) :
    defsOf prog
      = fun t => (((defEnv prog).map (fun p => (p.1, p.2.toDef))).find?
          (fun p => p.1 == t)).map (fun p => p.2) := by
  funext t
  simp only [defsOf]
  -- Both sides are `Option.map (·.2) (find? (·.1==t) _)`; only the scanned list differs.
  congr 1
  congr 1
  -- `defsOf`'s `pairs` = `(defEnv prog).map (·.1, ·.2.toDef)`.
  rw [defEnv, List.map_flatMap]
  simp only [List.map_filterMap]
  congr 1
  funext b
  congr 1
  funext s
  cases s with
  | assign t' e => cases e <;> rfl
  | sstore _ _ => rfl
  | call cs => obtain ⟨_, _, rt⟩ := cs; cases rt <;> rfl
  | create cs => obtain ⟨_, _, _, _, rt⟩ := cs; cases rt <;> rfl

/-- **`defsOf` is `defEnv`'s `find?`-view.** `defsOf prog t` is the first `defEnv` entry for
`t`, read back through `Loc.toDef`. Unconditional: both sides scan the identical
program-order list; the only difference is the `Expr`/`Loc` codomain, bridged by `Loc.toDef`
(`toDef_locOfExpr`). This is the alignment the S3 fold↔fuel bridge rests on. -/
theorem defsOf_eq_defEnv_find (prog : Program) (t : Tmp) :
    defsOf prog t
      = ((defEnv prog).find? (fun p => p.1 == t)).map (fun p => p.2.toDef) := by
  rw [congrFun (defsOf_eq_find_defEnv_map prog) t, List.find?_map, Option.map_map]
  rfl

/-- `allocate` is a faithful re-presentation of `defsOf`: viewing it back through
`Alloc.toDefs` recovers `defsOf` exactly. This is the Phase-A "no behaviour change"
keystone — `emit (allocate prog) prog` consumes `(allocate prog).toDefs = defsOf prog`. -/
theorem allocate_toDefs (prog : Program) : (allocate prog).toDefs = defsOf prog := by
  funext t
  simp only [Alloc.toDefs, allocate, Option.map_map]
  cases defsOf prog t with
  | none => rfl
  | some e => simp [toDef_locOfExpr]

end Lir
