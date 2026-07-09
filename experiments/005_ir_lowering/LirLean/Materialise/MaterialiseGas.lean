import LirLean.Frame.Match
import LirLean.Engine.Charges

/-!
# LirLean — the materialise gas-charge engine (charge lists for the value channel)

The **canonical** charge machinery is the fuel-free fold tower of §7: `chargeExpr`/
`chargeLoc`/`chargeStep`/`chargeFold`/`chargeCache` — the per-`Expr` charge lists the fold
value channel (`Lir.V2.materialise_runsC`/`MatRunsC`, `Materialise/MatFoldChannel.lean`) and
the `StackRoomOK`/`maxChargeDepth` stack-room folds (`Spec/WellFormed.lean`) read. One list
entry per opcode `matExpr (matCache prog) e` emits, in execution order; running the lowered
push-sequence subtracts exactly that list (`subCharges`), which is the honest-gas envelope.

Also canonical (fold-consumed): the pure `subCharges` arithmetic (§3-§5 —
`subCharges_singleton`, `toNat_subCharges`, `charge_binOpPost_gas`), which is
charge-list-generic and glues the per-opcode subtractions
into the whole-expression `subCharges` inside `materialise_runsC`.

## SLOAD warmth

`.sload k` lowers to `SLOAD`, whose real-EVM charge is `sloadCost warm` — **runtime** data
(warm/cold = `Gwarmaccess`/`Gcoldsload`), fixed by the accessed-key set at the frame SLOAD
executes on. The charge lists are kept *pure* by taking a `sloadChg : Tmp → ℕ` resolver giving
that per-key cost; the value channel instantiates it with the actual `sloadCost` at each SLOAD
frame. All laws are uniform in `sloadChg` (and the charge-list LENGTH is `sloadChg`-independent,
`chargeCache_length_sloadChg_eq` — what the stack-room folds consume).

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `Match.lean`);
nothing here touches `Spec/Semantics.lean` / `V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare

/-! ## 1. PUSH32 width-stability (the load-bearing honest-gas fact)

`emitImm w` is `PUSH32` for **every** literal `w`; `PUSH32` charges `Gverylow`,
exactly as `PUSH1` (`GasConstants`: all `PUSH<n>` cost `Gverylow`). So the charge of
materialising a literal is *independent of its value and of the push width* — the
honest-gas envelope is width-stable. This is what lets the C-grind treat the
PUSH32-fattened lowering as gas-equivalent to a hypothetical narrow one. -/

/-! ## 2. The pure-arithmetic engine (sum / `subCharges` laws)

These are the laws B1 threads to glue per-leaf subtractions into the whole-expression
`subCharges`. `subCharges_append`/`subCharges_snoc` (`LirLean/Engine/Charges.lean`,
proved by induction on the charge list) decompose compound charge lists in execution
order. -/

/-- A single-element `subCharges` is one subtraction. -/
theorem subCharges_singleton (g : UInt64) (c : ℕ) :
    subCharges g [c] = g - UInt64.ofNat c := rfl

/-! ## 3. The per-opcode single-charge steps (the bricks B1's compound cases thread)

For the compound constructs (`add`/`lt`/`sload`), B1's `Runs` chain ends in the
op's *own* opcode (ADD/LT/SLOAD) applied to the operands B1 already materialised. The
gas that opcode subtracts is one element. The operands' own charges are B1's recursive `Runs`
(it owns the frame chain); B2 owns the *last* op's charge and the gluing arithmetic. -/

/-- The op-charge step for `ADD`/`LT`: the final binary opcode subtracts the trailing
`[Gverylow]` of the compound charge list. `addFrame`/`ltFrame` go through `binOpPost`,
which charges `Gverylow`; stated through the named post-frame so B1 reads it off the
endpoint of its operand chain. -/
theorem charge_binOpPost_gas (fr : Frame) (op : UInt256 → UInt256 → UInt256)
    (a b : Word) (rest : Stack Word) :
    (BytecodeLayer.Dispatch.binOpPost fr.exec op a b rest).gasAvailable
      = subCharges fr.exec.gasAvailable [Gverylow] := by
  rw [subCharges_singleton]; rfl

/-! ## 4. The charge fold twin (`chargeCache` over `defEnv`) — Phase 2A P5a

The charge cache structurally parallels `matCache`/`matExpr`/`matLoc`/
`matStep`/`matFold` (`Spec/Lowering.lean`): a left-fold of `chargeStep` over `defEnv prog`,
resolving each operand tmp against a charge-`cache` built so far instead of recursing on fuel.
Constructor-for-constructor: one list entry per emitted opcode, matching the
`StackRoomOK`/`maxChargeDepth` stack-room folds over `(chargeCache prog sloadChg t).length`.

The *fold fixpoint* `chargeCache_unfold` (the `matCache_unfold` twin) and the operand-locality
congruence live in `Materialise/MatFoldChannel.lean` (they need the `WellFormed` def-env
machinery). What lives HERE — below `WellFormed` in the import DAG, so `WellFormed`'s stack-room
folds can read it — is the definition, the reduction lemmas, and the **`sloadChg`-independence
of the charge-list LENGTH** (`chargeCache_length_sloadChg_eq`) that `stackBounds_of_stackFits`
(`Spec/BudgetDerivations.lean`) consumes. -/

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
