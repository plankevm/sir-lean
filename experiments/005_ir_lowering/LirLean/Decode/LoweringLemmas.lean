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
  | create cs => simp at hsmap

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
  | create cs => simp at hsmap

/-- `Loc.toDef` is a left inverse of `locOfExpr` on every expression. -/
@[simp] theorem toDef_locOfExpr (e : Expr) : (locOfExpr e).toDef = e := by
  cases e <;> rfl

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
