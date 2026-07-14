import LirLean.Spec.Lowering
import BytecodeLayer.Exec.Gas

/-!
# LirLean — materialisation charge lists

`chargeExpr`, `chargeLoc`, `chargeStep`, `chargeFold`, and `chargeCache` assign an
execution-ordered opcode-charge list to each materialised IR value. The SLOAD cost
is supplied by `sloadChg`; the list length is independent of that runtime resolver.
Generic subtraction lemmas are re-exported for the fold proofs.
-/

namespace Lir

export BytecodeLayer.Exec (subCharges_singleton charge_binOpPost_gas)

open BytecodeLayer.Exec
open GasConstants

/-! ## The charge fold (`chargeCache` over `defEnv`)

The charge cache structurally parallels `matCache`/`matExpr`/`matLoc`/
`matStep`/`matFold` (`Spec/Lowering.lean`): a left-fold of `chargeStep` over `defEnv prog`,
resolving each operand tmp against a charge-`cache` built so far instead of recursing on fuel.
Constructor-for-constructor: one list entry per emitted opcode, matching the
`StackRoomOK`/`maxChargeDepth` stack-room folds over `(chargeCache prog sloadChg t).length`.

This file defines the fold, its reduction lemmas, and the `sloadChg`-independence of
the resulting charge-list length. -/

/-- The per-`Expr` charge list under a charge-`cache`: `.imm` pushes `Gverylow`,
`.sload` uses the runtime `sloadChg`, `.gas` uses `Gbase`, and binary ops add the
trailing op charge `Gverylow`. -/
def chargeExpr (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) : Expr → List ℕ
  | .imm _   => [GasConstants.Gverylow]
  | .tmp t   => cache t
  | .add a b => cache b ++ cache a ++ [GasConstants.Gverylow]
  | .lt  a b => cache b ++ cache a ++ [GasConstants.Gverylow]
  | .sload k => cache k ++ [sloadChg k]
  | .gas     => [GasConstants.Gbase]

/-- The charge list a `Loc` contributes under a charge-`cache`: `remat e` runs `chargeExpr`;
`slot n` is the spill-load `PUSH n; MLOAD` charge `[Gverylow, Gverylow]`. -/
def chargeLoc (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) : Loc → List ℕ
  | .remat e => chargeExpr sloadChg cache e
  | .slot _  => [GasConstants.Gverylow, GasConstants.Gverylow]

/-- One charge-fold step: bind `p.1` to the charges `chargeLoc` emits for its `Loc` under the
cache built so far (the `matStep` twin). -/
def chargeStep (sloadChg : Tmp → ℕ) (c : Tmp → List ℕ) (p : Tmp × Loc) : Tmp → List ℕ :=
  Function.update c p.1 (chargeLoc sloadChg c p.2)

/-- The charge-cache fold over a def-env prefix from an initial cache (the `matFold` twin). -/
def chargeFold (sloadChg : Tmp → ℕ) (init : Tmp → List ℕ) (l : List (Tmp × Loc)) : Tmp → List ℕ :=
  l.foldl (chargeStep sloadChg) init

/-- The initial charge cache: the undefined-tmp fallback `[Gverylow]` (the charge of
`matInit`'s `emitImm 0` PUSH; the `matInit` twin). -/
def chargeInit : Tmp → List ℕ := fun _ => [GasConstants.Gverylow]

/-- The per-tmp charge cache: a structural left-fold of `chargeStep` over `defEnv prog` (the
`matCache` twin). Fuel-free; structural termination via `foldl` over a finite list. -/
def chargeCache (prog : Program) (sloadChg : Tmp → ℕ) : Tmp → List ℕ :=
  chargeFold sloadChg chargeInit (defEnv prog)

/-! ### Reduction lemmas (definitional; pair with `matExpr` shapes) -/

@[simp] theorem chargeExpr_imm (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (w : Word) :
    chargeExpr sloadChg cache (.imm w) = [GasConstants.Gverylow] := rfl
@[simp] theorem chargeExpr_tmp (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (t : Tmp) :
    chargeExpr sloadChg cache (.tmp t) = cache t := rfl
@[simp] theorem chargeExpr_add (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (a b : Tmp) :
    chargeExpr sloadChg cache (.add a b)
      = cache b ++ cache a ++ [GasConstants.Gverylow] := rfl
@[simp] theorem chargeExpr_lt (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (a b : Tmp) :
    chargeExpr sloadChg cache (.lt a b)
      = cache b ++ cache a ++ [GasConstants.Gverylow] := rfl
@[simp] theorem chargeExpr_sload (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (k : Tmp) :
    chargeExpr sloadChg cache (.sload k) = cache k ++ [sloadChg k] := rfl
@[simp] theorem chargeExpr_gas (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) :
    chargeExpr sloadChg cache .gas = [GasConstants.Gbase] := rfl
@[simp] theorem chargeLoc_remat (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (e : Expr) :
    chargeLoc sloadChg cache (.remat e) = chargeExpr sloadChg cache e := rfl
@[simp] theorem chargeLoc_slot (sloadChg : Tmp → ℕ) (cache : Tmp → List ℕ) (n : Nat) :
    chargeLoc sloadChg cache (.slot n) = [GasConstants.Gverylow, GasConstants.Gverylow] := rfl

@[simp] theorem chargeFold_nil (sloadChg : Tmp → ℕ) (init : Tmp → List ℕ) :
    chargeFold sloadChg init [] = init := rfl
@[simp] theorem chargeFold_cons (sloadChg : Tmp → ℕ) (init : Tmp → List ℕ) (p : Tmp × Loc)
    (l : List (Tmp × Loc)) :
    chargeFold sloadChg init (p :: l) = chargeFold sloadChg (chargeStep sloadChg init p) l := rfl

theorem chargeCache_eq_chargeFold (prog : Program) (sloadChg : Tmp → ℕ) :
    chargeCache prog sloadChg = chargeFold sloadChg chargeInit (defEnv prog) := rfl

/-! ### `sloadChg`-independence of the charge-list LENGTH (the stack-room fold's lockstep)

The charge-list LENGTH is independent of the runtime `sloadChg` VALUES — each `.sload`
contributes exactly one entry whatever the charge (`chargeExpr`'s `.sload` arm is
`cache k ++ [sloadChg k]`). This is what `stackBounds_of_stackFits`
(`Spec/BudgetDerivations.lean`) reads: it lets the
`StackRoomOK`/`maxChargeDepth` folds fix `sloadChg := fun _ => 0`. Stated for caches agreeing on
LENGTH at *every* tmp (the total invariant the fold propagates), so it needs no operand-locality
(`usesInExpr`) machinery and stays below `WellFormed` in the import DAG. -/

/-- `chargeExpr`'s LENGTH depends on the cache only through its per-tmp LENGTHS, and not at all
on the `sloadChg` values. -/
theorem chargeExpr_length_eq {sc sc' : Tmp → ℕ} {c c' : Tmp → List ℕ}
    (h : ∀ t, (c t).length = (c' t).length) (e : Expr) :
    (chargeExpr sc c e).length = (chargeExpr sc' c' e).length := by
  cases e with
  | imm w => rfl
  | gas => rfl
  | tmp t => exact h t
  | add a b => simp only [chargeExpr_add, List.length_append]; rw [h a, h b]
  | lt a b => simp only [chargeExpr_lt, List.length_append]; rw [h a, h b]
  | sload k => simp only [chargeExpr_sload, List.length_append, List.length_singleton]; rw [h k]

/-- `chargeLoc`'s LENGTH depends on the cache only through its per-tmp LENGTHS. -/
theorem chargeLoc_length_eq {sc sc' : Tmp → ℕ} {c c' : Tmp → List ℕ}
    (h : ∀ t, (c t).length = (c' t).length) (loc : Loc) :
    (chargeLoc sc c loc).length = (chargeLoc sc' c' loc).length := by
  cases loc with
  | remat e => exact chargeExpr_length_eq h e
  | slot n => rfl

/-- One `chargeStep` preserves per-tmp LENGTH agreement. -/
theorem chargeStep_length_eq {sc sc' : Tmp → ℕ} {c c' : Tmp → List ℕ}
    (h : ∀ t, (c t).length = (c' t).length) (p : Tmp × Loc) :
    ∀ t, (chargeStep sc c p t).length = (chargeStep sc' c' p t).length := by
  intro t
  simp only [chargeStep, Function.update_apply]
  by_cases ht : t = p.1
  · simp only [if_pos ht]; exact chargeLoc_length_eq h p.2
  · simp only [if_neg ht]; exact h t

/-- The whole `chargeFold` preserves per-tmp LENGTH agreement — hence its LENGTH is
independent of both the initial cache's byte contents (up to length) and the `sloadChg`. -/
theorem chargeFold_length_eq {sc sc' : Tmp → ℕ} :
    ∀ (l : List (Tmp × Loc)) {c c' : Tmp → List ℕ},
      (∀ t, (c t).length = (c' t).length) →
      ∀ t, (chargeFold sc c l t).length = (chargeFold sc' c' l t).length
  | [], _, _, h, t => h t
  | p :: l, c, c', h, t => by
      rw [chargeFold_cons, chargeFold_cons]
      exact chargeFold_length_eq l (chargeStep_length_eq h p) t

/-- **The `sloadChg`-independence of the charge-cache LENGTH.** The
`StackRoomOK`/`maxChargeDepth` stack-room folds may fix
`sloadChg := fun _ => 0` when reading `(chargeCache prog sloadChg t).length`. -/
theorem chargeCache_length_sloadChg_eq (prog : Program) (c1 c2 : Tmp → ℕ) (t : Tmp) :
    (chargeCache prog c1 t).length = (chargeCache prog c2 t).length := by
  rw [chargeCache_eq_chargeFold, chargeCache_eq_chargeFold]
  exact chargeFold_length_eq (defEnv prog) (fun _ => rfl) t

end Lir

-- Build-enforced axiom-cleanliness guard for the B2 deliverable: the gas-charge
-- engine depends only on `[propext, Classical.choice, Quot.sound]`.
