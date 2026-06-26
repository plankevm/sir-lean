import LirLean.Match
import LirLean.Charges

/-!
# LirLean — the materialise gas-charge engine (Layer **B2** of the `lower_conforms` grind)

`docs/lower-conforms-plan.md` Layer **B2** (`materialise_gas_charge`): the real-EVM
gas the lowered `materialiseExpr defs fuel e` push-sequence charges is exactly a
`subCharges` of a per-`Expr` **charge list** `chargeOf`. This is the honest-gas
envelope that **B1 `materialise_runs`** consumes: B1 produces the `Runs` frame chain
for `materialiseExpr`; *this* module supplies (a) the charge-list function
`chargeOf`, mirroring `materialiseExpr` opcode-for-opcode, and (b) the
pure-arithmetic engine (`subCharges`/`chargeOf` sum and append laws, the
PUSH32-width-stability fact) plus the **per-leaf gas-companion steps** that turn one
materialise opcode into one `subCharges` subtraction.

## The honest decomposition (per the B2 brief's flexibility clause)

The "running subtracts exactly `chargeOf`" statement
(`gas fr' = subCharges (gas fr) (chargeOf … e)`) needs the materialise endpoint
frame `fr'` — and that frame *only exists* as the endpoint of B1's
`materialise_runs` `Runs` chain (the intermediate frames at each operand cursor,
their stacks and accessed-key sets, are exactly what B1 threads). B2 therefore
honestly splits into:

* the **leaf** "running subtracts it" steps, which *are* standalone — `imm`/`gas`
  land on a named post-frame (`pushFrameW`/`gasFrame`) whose `gasAvailable` is a
  one-element `subCharges` directly from the `sim_*` companion (`charge_runs_imm`,
  `charge_runs_gas`);
* the **compound** case, whose gas fact is a corollary of B1's frame chain glued by
  `subCharges_append` — delivered here as the **gluing lemma** `subCharges_chargeOf_*`
  (the goal shape B1 faces, in `subCharges`/`chargeOf` terms) rather than a
  frame-level statement B2 cannot phrase without B1's `Runs`.

See the module tail (`section B1_contract`) for the precise goal shape B1 consumes.

## SLOAD warmth

`materialiseExpr`'s `.sload k` lowers to `SLOAD`, whose real-EVM charge is
`sloadCost warm` — **runtime** data (warm/cold = `Gwarmaccess`/`Gcoldsload`), fixed
by the accessed-key set at the frame SLOAD executes on (again, a B1 frame-chain
fact). `chargeOf` is kept *pure* by taking a `sloadChg : Tmp → ℕ` resolver giving
that per-key cost; B1 instantiates it with the actual `sloadCost` at each SLOAD
frame. The pure laws below are uniform in `sloadChg`.

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `Match.lean`);
nothing here touches `V2/Machine.lean` / `V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare

/-! ## 1. The per-`Expr` charge list `chargeOf`

`chargeOf defs sloadChg fuel e` is the real-EVM gas, **in execution order**, that
`materialiseExpr defs fuel e` charges — one list entry per emitted opcode. It
mirrors `materialiseExpr` constructor-for-constructor:

* `.imm _` → `emitImm _` = `PUSH32` → `[Gverylow]` (width-stable: any literal, any
  width, charges `Gverylow` — `PUSH32` costs the same as `PUSH1`, see
  `chargeOf_imm_const`);
* `.tmp t` → recurse on `defs t` (or `emitImm 0` ⇒ `[Gverylow]` for an undefined tmp,
  matching `materialiseExpr`'s conservative-`0` leaf);
* `.add`/`.lt a b` → `chargeOf (.tmp b) ++ chargeOf (.tmp a) ++ [Gverylow]`
  (operand order `b` then `a` then the op, exactly `materialiseExpr`);
* `.sload k` → `chargeOf (.tmp k) ++ [sloadChg k]` (the runtime SLOAD cost, supplied);
* `.gas` → `[Gbase]`.

The `fuel`/recursion structure is identical to `materialiseExpr` so the two stay in
lockstep (`materialiseExpr_*`/`chargeOf_*` reduction lemmas below pair up). -/
def chargeOf (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) : Nat → Expr → List ℕ
  | _,      .imm _  => [Gverylow]
  | _,      .callResult _ => [Gverylow, Gverylow]
  | 0,      _       => []
  | f + 1,  .tmp t  =>
      match defs t with
      | some e => chargeOf defs sloadChg f e
      | none   => [Gverylow]
  | f + 1,  .add a b =>
      chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a) ++ [Gverylow]
  | f + 1,  .lt a b =>
      chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a) ++ [Gverylow]
  | f + 1,  .sload k =>
      chargeOf defs sloadChg f (.tmp k) ++ [sloadChg k]
  | _ + 1,  .gas    => [Gbase]

/-! ### Reduction lemmas (definitional; pair with `materialiseExpr`'s shape) -/

@[simp] theorem chargeOf_imm (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (fuel : Nat) (w : Word) :
    chargeOf defs sloadChg fuel (.imm w) = [Gverylow] := by
  cases fuel <;> rfl

theorem chargeOf_tmp_some (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (t : Tmp) (e : Expr) (h : defs t = some e) :
    chargeOf defs sloadChg (f + 1) (.tmp t) = chargeOf defs sloadChg f e := by
  show (match defs t with | some e => chargeOf defs sloadChg f e | none => [Gverylow]) = _
  rw [h]

theorem chargeOf_tmp_none (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (t : Tmp) (h : defs t = none) :
    chargeOf defs sloadChg (f + 1) (.tmp t) = [Gverylow] := by
  show (match defs t with | some e => chargeOf defs sloadChg f e | none => [Gverylow]) = _
  rw [h]

@[simp] theorem chargeOf_add (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (a b : Tmp) :
    chargeOf defs sloadChg (f + 1) (.add a b)
      = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a) ++ [Gverylow] :=
  rfl

@[simp] theorem chargeOf_lt (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (a b : Tmp) :
    chargeOf defs sloadChg (f + 1) (.lt a b)
      = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a) ++ [Gverylow] :=
  rfl

@[simp] theorem chargeOf_sload (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (k : Tmp) :
    chargeOf defs sloadChg (f + 1) (.sload k)
      = chargeOf defs sloadChg f (.tmp k) ++ [sloadChg k] :=
  rfl

@[simp] theorem chargeOf_gas (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) :
    chargeOf defs sloadChg (f + 1) .gas = [Gbase] :=
  rfl

/-! ## 2. PUSH32 width-stability (the load-bearing honest-gas fact)

`emitImm w` is `PUSH32` for **every** literal `w`; `PUSH32` charges `Gverylow`,
exactly as `PUSH1` (`GasConstants`: all `PUSH<n>` cost `Gverylow`). So the charge of
materialising a literal is *independent of its value and of the push width* — the
honest-gas envelope is width-stable. This is what lets the C-grind treat the
PUSH32-fattened lowering as gas-equivalent to a hypothetical narrow one. -/

/-- The literal charge is the constant `[Gverylow]`, independent of the word — the
PUSH32-width-stability fact (PUSH32 costs `Gverylow`, same as PUSH1). -/
theorem chargeOf_imm_const (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (fuel : Nat) (w w' : Word) :
    chargeOf defs sloadChg fuel (.imm w) = chargeOf defs sloadChg fuel (.imm w') := by
  rw [chargeOf_imm, chargeOf_imm]

/-- An undefined tmp materialises the conservative `0` literal, charging exactly the
same `[Gverylow]` as a real literal — width-stability extends to the fallback leaf. -/
theorem chargeOf_tmp_none_eq_imm (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (t : Tmp) (w : Word) (h : defs t = none) :
    chargeOf defs sloadChg (f + 1) (.tmp t) = chargeOf defs sloadChg (f + 1) (.imm w) := by
  rw [chargeOf_tmp_none defs sloadChg f t h, chargeOf_imm]

/-! ## 3. The pure-arithmetic engine (sum / `subCharges` laws)

These are the laws B1 threads to glue per-leaf subtractions into the whole-expression
`subCharges`. `subCharges_append`/`subCharges_snoc` (`LirLean/Charges.lean`,
proved by induction on the charge list) decompose a compound `chargeOf` into its
operand sub-charges in execution order; `toNat_chargeOf` is the honest-gas envelope
(`toNat_subCharges` specialised to a `chargeOf` list). -/

/-- **The compound-charge decomposition (the B1 gluing law for `.add`/`.lt`).**
Subtracting a binary op's whole charge list off `g` is: subtract operand `b`'s
charges, then operand `a`'s, then the single op charge `Gverylow` — exactly the
order B1's `Runs` chain (mat `b`; mat `a`; ADD/LT) descends gas. Pure `subCharges`
arithmetic via `subCharges_append`/`subCharges_snoc`. -/
theorem subCharges_chargeOf_binop (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (a b : Tmp) (g : UInt64) :
    subCharges g (chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a) ++ [Gverylow])
      = subCharges (subCharges (subCharges g (chargeOf defs sloadChg f (.tmp b)))
          (chargeOf defs sloadChg f (.tmp a))) [Gverylow] := by
  rw [subCharges_append, subCharges_append]

/-- **The compound-charge decomposition for `.sload`.** Subtracting `sload k`'s
charge list is: subtract key `k`'s charges, then the single `SLOAD` charge — the
order B1's `Runs` chain (mat `k`; SLOAD) descends gas. -/
theorem subCharges_chargeOf_sload (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (k : Tmp) (g : UInt64) :
    subCharges g (chargeOf defs sloadChg f (.tmp k) ++ [sloadChg k])
      = subCharges (subCharges g (chargeOf defs sloadChg f (.tmp k))) [sloadChg k] := by
  rw [subCharges_append]

/-- **The honest-gas envelope.** When the whole `chargeOf` list fits under `g`,
materialising `e` lands the engine at `g.toNat - (chargeOf …).sum` — the exact gas
the push-sequence consumes. This is `toNat_subCharges` specialised to `chargeOf`;
B1 supplies the `Runs` that *reaches* the frame whose gas is this `subCharges`. -/
theorem toNat_chargeOf (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (fuel : Nat) (e : Expr) (g : UInt64)
    (hsum : (chargeOf defs sloadChg fuel e).sum ≤ g.toNat) :
    (subCharges g (chargeOf defs sloadChg fuel e)).toNat
      = g.toNat - (chargeOf defs sloadChg fuel e).sum :=
  toNat_subCharges g _ hsum

/-! ## 4. The leaf "running subtracts it" steps (standalone, via the `sim_*` companions)

For the two leaves whose materialise post-frame is named without B1's chain
(`imm` → `pushFrameW`, `gas` → `gasFrame`), the gas-charge lemma holds **fully and
standalone**: running the single opcode subtracts exactly the one-element
`chargeOf`. These are the base cases B1's induction discharges directly; the
compound cases reduce to them by §3's gluing laws. -/

/-- A single-element `subCharges` is one subtraction. -/
theorem subCharges_singleton (g : UInt64) (c : ℕ) :
    subCharges g [c] = g - UInt64.ofNat c := rfl

/-- **`Expr.imm` running subtracts `chargeOf`.** A frame decoding to `PUSH32 w` runs
one step to `pushFrameW fr w 32` (the `materialiseExpr defs fuel (.imm w) = emitImm w`
endpoint), whose `gasAvailable` is exactly `subCharges (gas fr) (chargeOf … (.imm w))`
= `gas fr - Gverylow`. The full B2 form for this leaf — `Runs` *and* the gas
equation — proved standalone from `sim_imm`. -/
theorem charge_runs_imm (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (fuel : Nat)
    (fr : Frame) (w : Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrameW fr w 32)
      ∧ (pushFrameW fr w 32).exec.gasAvailable
          = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg fuel (.imm w)) := by
  refine ⟨(sim_imm fr w hdec hgas hstk).1, ?_⟩
  rw [chargeOf_imm, subCharges_singleton]
  rfl

/-- **`Expr.gas` running subtracts `chargeOf`.** A frame decoding to `GAS` runs one
step to `gasFrame fr` (the `materialiseExpr defs (f+1) .gas = [GAS]` endpoint), whose
`gasAvailable` is exactly `subCharges (gas fr) (chargeOf … .gas)` = `gas fr - Gbase`.
The full B2 form for this leaf, standalone from `sim_gas`. -/
theorem charge_runs_gas (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (f : Nat)
    (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gasFrame fr)
      ∧ (gasFrame fr).exec.gasAvailable
          = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg (f + 1) .gas) := by
  refine ⟨(sim_gas fr hdec hsz hgas).1, ?_⟩
  rw [chargeOf_gas, subCharges_singleton]
  exact (sim_gas fr hdec hsz hgas).2

/-! ## 5. The per-opcode single-charge steps (the bricks B1's compound cases thread)

For the compound constructs (`add`/`lt`/`sload`), B1's `Runs` chain ends in the
op's *own* opcode (ADD/LT/SLOAD) applied to the operands B1 already materialised. The
gas that opcode subtracts is one element — these lemmas pin that single subtraction in
`subCharges`/`chargeOf` terms, so B1 closes the compound case by §3's gluing law
`subCharges_chargeOf_*` + these. The operands' own charges are B1's recursive `Runs`
(it owns the frame chain); B2 owns the *last* op's charge and the gluing arithmetic. -/

/-- The op-charge step for `ADD`/`LT`: the final binary opcode subtracts the trailing
`[Gverylow]` of the compound `chargeOf`. `addFrame`/`ltFrame` go through `binOpPost`,
which charges `Gverylow`; stated through the named post-frame so B1 reads it off the
endpoint of its operand chain. -/
theorem charge_binOpPost_gas (fr : Frame) (op : UInt256 → UInt256 → UInt256)
    (a b : Word) (rest : Stack Word) :
    (BytecodeLayer.Dispatch.binOpPost fr.exec op a b rest).gasAvailable
      = subCharges fr.exec.gasAvailable [Gverylow] := by
  rw [subCharges_singleton]; rfl

/-- The op-charge step for `SLOAD`: the final `SLOAD` opcode subtracts the trailing
`[sloadCost warm]`, with `warm` the runtime warmth at `fr` — exactly the `sloadChg k`
B1 instantiates `chargeOf` with. Stated through `sloadPost` (the `sloadFrame`
post-state). -/
theorem charge_sloadPost_gas (fr : Frame) (key : Word) (rest : Stack Word) :
    (BytecodeLayer.Dispatch.sloadPost fr.exec key rest).gasAvailable
      = subCharges fr.exec.gasAvailable
          [Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
            (fr.exec.executionEnv.address, key))] := by
  rw [subCharges_singleton]; rfl

/-! ## 6. `section B1_contract` — the goal shape B1 faces (the honest split, made precise)

The full B2 statement — *running* `materialiseExpr defs fuel e` subtracts exactly
`chargeOf … e` — is, for compound `e`, **a corollary of B1's `materialise_runs`**:
B1 produces `Runs fr fr'` with `fr'` the materialise endpoint, by an induction
mirroring `materialiseExpr`. At each node B1 already has the operand sub-`Runs`
(its IH) and the op's single step; gluing their gas via `Runs.trans` + this module's
§3 (`subCharges_chargeOf_*`) + §4/§5 (`charge_*`) yields:

```text
   (materialise endpoint fr').exec.gasAvailable
     = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg fuel e)
```

`materialise_gas_charge_contract` packages that target as a predicate on a candidate
endpoint, so B1 can state its conclusion against it without B2 having to name B1's
frame chain. This is the honest B2 deliverable: `chargeOf` + the arithmetic that
turns B1's per-step gas facts into the whole-expression `subCharges`. The leaf cases
(`charge_runs_imm`/`charge_runs_gas`) discharge this predicate **fully and
standalone** today. -/
section B1_contract

/-- The B2 conclusion as a predicate on a materialise endpoint frame `fr'` reached
from `fr` by running `materialiseExpr defs fuel e`: `fr'`'s real-EVM gas is exactly
`subCharges` of the per-`Expr` charge list. B1 discharges this on its assembled
endpoint; the leaf lemmas above discharge it standalone for `imm`/`gas`. -/
def MaterialiseGasCharge (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (fuel : Nat)
    (e : Expr) (fr fr' : Frame) : Prop :=
  fr'.exec.gasAvailable = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg fuel e)

/-- The `imm` leaf discharges the contract standalone (from `charge_runs_imm`). -/
theorem materialiseGasCharge_imm (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (fuel : Nat) (fr : Frame) (w : Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    MaterialiseGasCharge defs sloadChg fuel (.imm w) fr (pushFrameW fr w 32) :=
  (charge_runs_imm defs sloadChg fuel fr w hdec hgas hstk).2

/-- The `gas` leaf discharges the contract standalone (from `charge_runs_gas`). -/
theorem materialiseGasCharge_gas (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    MaterialiseGasCharge defs sloadChg (f + 1) .gas fr (gasFrame fr) :=
  (charge_runs_gas defs sloadChg f fr hdec hsz hgas).2

/-- **The compound gluing law (the B1 corollary engine).** Given the operand
sub-charge endpoints `frb` (after materialising `b`) and `fra` (after `a`, from
`frb`), each satisfying the contract, *and* the op-step gas fact (the final ADD/LT
subtracts `[Gverylow]` from `fra`), the binary-op endpoint satisfies the whole
contract. This is precisely the step B1's `.add`/`.lt` induction case takes: B2 owns
the `subCharges`/`chargeOf` bookkeeping, B1 owns producing `frb`/`fra`/the op step. -/
theorem materialiseGasCharge_binop
    (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (f : Nat) (a b : Tmp)
    (fr frb fra fr' : Frame)
    (hb : MaterialiseGasCharge defs sloadChg f (.tmp b) fr frb)
    (ha : MaterialiseGasCharge defs sloadChg f (.tmp a) frb fra)
    (hop : fr'.exec.gasAvailable = subCharges fra.exec.gasAvailable [Gverylow]) :
    MaterialiseGasCharge defs sloadChg (f + 1) (.add a b) fr fr'
    ∧ MaterialiseGasCharge defs sloadChg (f + 1) (.lt a b) fr fr' := by
  have key : fr'.exec.gasAvailable
      = subCharges fr.exec.gasAvailable
          (chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a) ++ [Gverylow]) := by
    rw [subCharges_chargeOf_binop, ← hb, ← ha, hop]
  exact ⟨by rw [MaterialiseGasCharge, chargeOf_add]; exact key,
         by rw [MaterialiseGasCharge, chargeOf_lt]; exact key⟩

/-- **The `sload` compound gluing law.** Given the key sub-charge endpoint `frk`
(after materialising `k`) satisfying the contract, and the `SLOAD` op-step gas fact
(subtracting `[sloadChg k]` from `frk`), the `sload` endpoint satisfies the whole
contract. B1 instantiates `sloadChg k` with the runtime `sloadCost` at `frk` (via
`charge_sloadPost_gas`). -/
theorem materialiseGasCharge_sload
    (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (f : Nat) (k : Tmp)
    (fr frk fr' : Frame)
    (hk : MaterialiseGasCharge defs sloadChg f (.tmp k) fr frk)
    (hop : fr'.exec.gasAvailable = subCharges frk.exec.gasAvailable [sloadChg k]) :
    MaterialiseGasCharge defs sloadChg (f + 1) (.sload k) fr fr' := by
  rw [MaterialiseGasCharge, chargeOf_sload, subCharges_chargeOf_sload, ← hk, hop]

/-- **The `tmp` recompute gluing law.** Materialising `.tmp t` with `defs t = some e`
*is* materialising `e` (`materialiseExpr`/`chargeOf` both recurse), so the endpoint's
contract for `.tmp t` is the contract for `e` — the recompute-on-use step, in gas
terms. -/
theorem materialiseGasCharge_tmp_some
    (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (f : Nat) (t : Tmp) (e : Expr)
    (he : defs t = some e) (fr fr' : Frame)
    (hrec : MaterialiseGasCharge defs sloadChg f e fr fr') :
    MaterialiseGasCharge defs sloadChg (f + 1) (.tmp t) fr fr' := by
  rw [MaterialiseGasCharge, chargeOf_tmp_some defs sloadChg f t e he]; exact hrec

end B1_contract

end Lir

-- Build-enforced axiom-cleanliness guard for the B2 deliverable: the gas-charge
-- engine depends only on `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.charge_runs_imm
#print axioms Lir.charge_runs_gas
#print axioms Lir.materialiseGasCharge_binop
#print axioms Lir.materialiseGasCharge_sload
#print axioms Lir.toNat_chargeOf
