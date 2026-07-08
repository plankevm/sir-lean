import LirLean.Spec.Lowering

/-!
# LirLean — lowering lemmas (extracted from `Spec/Lowering.lean`)

The proof companions of the pure lowering definitions (`LirLean/Spec/Lowering.lean`):
the `defsOf` spill-routing exhaustiveness facts (`defsOf_ne_gas` / `defsOf_ne_sload`),
the `rematOf` ↔ `defsOf` projection inversions (`defsOf_of_rematOf` /
`rematOf_of_defsOf`), and the `defsOf` ↔ `defEnv` first-find alignment
(`defsOf_eq_defEnv_find`). Extracted so `Spec/Lowering.lean` stays a definitions-only
spec-core file (Wave 3, `docs/fleet-2026-07-02/reorg-legibility.md` §5 Step 3); every
former importer of `LirLean.Lowering` imports this module instead.
-/

namespace Lir

/-- `defsOf` never registers a tmp as the rematerialised bare `.gas`: a gas assign is
routed to the spill slot `Loc.slot (slotOf t)`, and no other `defEnv` arm produces
`Loc.remat .gas`. So every gas tmp is a memory slot, read once at the def-site stash
and reused via `MLOAD`. -/
theorem defsOf_ne_gas (prog : Program) (t : Tmp) :
    defsOf prog t ≠ some (.remat .gas) := by
  intro hgas
  simp only [defsOf] at hgas
  obtain ⟨pr, hf, hpr⟩ := Option.map_eq_some_iff.mp hgas
  have hmem := List.mem_of_find?_eq_some hf
  rw [defEnv] at hmem
  obtain ⟨b, _, hbmem⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, _, hsmap⟩ := List.mem_filterMap.mp hbmem
  -- `pr.2` is one of the filterMap outputs; none is `Loc.remat .gas`.
  cases s with
  | assign t' e' =>
      cases e' with
      | gas => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | imm w => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                 simp [locOfExpr] at hpr
      | tmp t'' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                   simp [locOfExpr] at hpr
      | add a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                   simp [locOfExpr] at hpr
      | lt a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                  simp [locOfExpr] at hpr
      | sload k => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | slot n => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                  simp [locOfExpr] at hpr
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

/-- `defsOf` never registers a tmp as a rematerialised bare `.sload _`: an sload
assign is routed to the spill slot `Loc.slot (slotOf t)`, and no other `defEnv` arm
produces `Loc.remat (.sload _)`. So every sload tmp is a memory slot, read once at
the def-site (cold/warm warmth charged once) and reused via `MLOAD`. -/
theorem defsOf_ne_sload (prog : Program) (t : Tmp) (k : Tmp) :
    defsOf prog t ≠ some (.remat (.sload k)) := by
  intro hsl
  simp only [defsOf] at hsl
  obtain ⟨pr, hf, hpr⟩ := Option.map_eq_some_iff.mp hsl
  have hmem := List.mem_of_find?_eq_some hf
  rw [defEnv] at hmem
  obtain ⟨b, _, hbmem⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, _, hsmap⟩ := List.mem_filterMap.mp hbmem
  -- `pr.2` is one of the filterMap outputs; none is `Loc.remat (.sload _)`.
  cases s with
  | assign t' e' =>
      cases e' with
      | gas => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | imm w => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                 simp [locOfExpr] at hpr
      | tmp t'' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                   simp [locOfExpr] at hpr
      | add a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                   simp [locOfExpr] at hpr
      | lt a b => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                  simp [locOfExpr] at hpr
      | sload k' => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr; simp at hpr
      | slot n => simp only [Option.some.injEq] at hsmap; rw [← hsmap] at hpr
                  simp [locOfExpr] at hpr
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

/-! ## `rematOf` — the `.remat` projection of `defsOf` -/

/-- Every `rematOf` binding is a `defsOf` `.remat` binding: `rematOf` only *drops* the
spilled (`.slot`) entries, it never invents one. -/
theorem defsOf_of_rematOf {prog : Program} {t : Tmp} {e : Expr}
    (h : rematOf prog t = some e) : defsOf prog t = some (.remat e) := by
  rw [rematOf] at h
  split at h
  · next e' heq => rw [heq, Option.some.inj h]
  · exact absurd h (by nofun)

/-- A `.remat` `defsOf` binding is a `rematOf` binding: on the rematerialised entries
the two views coincide. -/
theorem rematOf_of_defsOf {prog : Program} {t : Tmp} {e : Expr}
    (hd : defsOf prog t = some (.remat e)) : rematOf prog t = some e := by
  rw [rematOf, hd]

/-- `rematOf` never registers a tmp as the bare `Expr.gas` (the `defsOf` twin, lifted
through `defsOf_of_rematOf`): gas tmps are spilled to `.slot` and dropped by `rematOf`. -/
theorem rematOf_ne_gas (prog : Program) (t : Tmp) : rematOf prog t ≠ some .gas :=
  fun h => defsOf_ne_gas prog t (defsOf_of_rematOf h)

/-- `rematOf` never registers a tmp as a bare `Expr.sload _` (the `defsOf` twin, lifted
through `defsOf_of_rematOf`): sload tmps are spilled to `.slot` and dropped by `rematOf`. -/
theorem rematOf_ne_sload (prog : Program) (t : Tmp) (k : Tmp) :
    rematOf prog t ≠ some (.sload k) :=
  fun h => defsOf_ne_sload prog t k (defsOf_of_rematOf h)

/-- `Loc.toDef` is a left inverse of `locOfExpr` on every expression. (Legacy: last
consumers are the generic-`defs` fuel lemmas; deleted at P9 with `Loc.toDef`.) -/
@[simp] theorem toDef_locOfExpr (e : Expr) : (locOfExpr e).toDef = e := by
  cases e <;> rfl

/-! ## `defsOf` ↔ `defEnv` alignment -/

/-- **`defsOf` is `defEnv`'s first-find view.** `defsOf prog t` is the first `defEnv`
entry for `t`. Definitional: `defsOf` is *defined* as this `find?`; the lemma names
the alignment for rewriting. -/
theorem defsOf_eq_defEnv_find (prog : Program) (t : Tmp) :
    defsOf prog t = ((defEnv prog).find? (fun p => p.1 == t)).map (·.2) := rfl

end Lir
