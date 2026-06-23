import LirLean.V2.Machine
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.Programs
import BytecodeLayer.Observables

/-!
# LirLean v2 — observable lowering preservation, the call-free prototype (§4, §6 step 1)

This file validates the **v2 preservation theorem shape** end-to-end on a concrete
program, at low cost, before the heavier external-`call` event step. It is the
de-risking prototype of `docs/ir-design-v2.md` §6 step 1.

## The theorem shape (`ir-design-v2.md` §4)

```
IRRun prog w₀ T O → ∃ G₀, ∀ g, G₀ ≤ g → LoweredRunHasObs (lower prog) w₀ g T O
```

* **No `pc`, no gas-equality in the statement.** The only gas fact is the adequacy
  envelope `G₀ ≤ g`. The bytecode's pc/stack/gas bookkeeping lives *inside* the
  `Runs` witness `LoweredRunHasObs` unfolds to — the IR never sees it.
* **World agreement** (M3 promoted to `World`) and the **halt result** are the
  IR-facing observable.
* **The `gasRead` event is realised** by the bytecode `GAS` opcode's actual value
  (§3.4): the obs the IR consumed equals the machine gas word at the GAS site. This
  is the unified "events are witnessed by the bytecode" mechanism, applied to the
  lightweight `gasRead` event (the `call` event is the next migration step).

## Deliberate prototype cuts (documented per the brief)

* **Hand-written witness bytecode, not `lower prog`.** `lower` emits PUSH32 literals
  (33 bytes each); a `Runs` over it needs the deep offset-table/decode kernel
  reductions that make v1 `WorkedCall.lean` ~1700 lines. The prototype's purpose is
  the *theorem shape*, so the internal `Runs` witness is a hand-assembled PUSH1
  bytecode (`protoBytecode`) that computes the same values; we reuse exactly the v1
  *reasoning* machinery (`runs_*`, `runs_branch`, `messageCall_runs`, the
  `validJumpDests` reachability characterization). Wiring `lower` in is mechanical
  follow-up (it is precisely what `WorkedCall.lean` already does for its program).
* **`returned w` ↦ success+empty output.** The C3 lowering RETURNs an *empty* window
  (v1 `halt_ret`), so the IR exit word `w` is not reflected in the bytecode output
  (the §7 open question). The observable correspondence therefore checks `success`,
  empty output, and **world agreement**; both `stopped` and `returned _` map to
  success+empty. The control-flow branch is still genuinely exercised.
* **Taken arm proved; STOP arm symmetric.** For `G₀ ≤ g` the observed gas word is
  non-zero, so the gas-dependent branch takes the `RETURN` arm. The `STOP` arm is the
  same shape with `cond = 0` (and is the §4 fall-through of `runs_branch`); not
  instantiated to keep the prototype small.
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Dispatch
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.UInt64

set_option maxRecDepth 4000

/-! ## The witness bytecode (the internal `Runs` witness, PUSH1-based)

```text
pc 0  : PUSH1 5      60 05    value
pc 2  : PUSH1 7      60 07    key
pc 4  : SSTORE       55       storage[7] := 5
pc 5  : PUSH1 100    60 64    lt right operand (pushed lowest)
pc 7  : PUSH1 7      60 07    sload key
pc 9  : SLOAD        54       → 5
pc 10 : PUSH1 9      60 09
pc 12 : ADD          01       → add 9 5 = 14
pc 13 : LT           10       → lt 14 100 = 1
pc 14 : GAS          5a       → observed gas word
pc 15 : PUSH1 19     60 13    JUMPI destination (the RETURN block)
pc 17 : JUMPI        57       gas ≠ 0 ⇒ jump to 19, else fall to STOP at 18
pc 18 : STOP         00       (else arm)
pc 19 : JUMPDEST     5b       (then arm lands here)
pc 20 : PUSH1 0      60 00
pc 22 : PUSH1 0      60 00
pc 24 : RETURN       f3       return empty (offset 0, size 0)
```
-/
def protoBytecode : ByteArray :=
  ⟨#[0x60,0x05, 0x60,0x07, 0x55, 0x60,0x64, 0x60,0x07, 0x54,
     0x60,0x09, 0x01, 0x10, 0x5a, 0x60,0x13, 0x57, 0x00,
     0x5b, 0x60,0x00, 0x60,0x00, 0xf3]⟩

/-- The top-level call running `protoBytecode` in `addrA` (present, default
account; value-free, state-modifying, depth 0) — same world shape as
`BytecodeLayer.Programs.paramsSStore`. -/
def protoParams (g : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := (∅ : AccountMap).insert addrA default,
    originalAccounts := ∅, substate := default,
    caller := addrA, origin := addrA, recipient := addrA,
    codeSource := .Code protoBytecode, gas := g, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-! ## Decode facts at each pc (literal `rfl`, cheap since PUSH1) -/

private def fr0 (g : UInt64) : Frame := codeFrame (protoParams g) protoBytecode

theorem dec_0 : decode protoBytecode 0  = some (.Push .PUSH1, some (5, 1))   := by rfl
theorem dec_2 : decode protoBytecode 2  = some (.Push .PUSH1, some (7, 1))   := by rfl
theorem dec_4 : decode protoBytecode 4  = some (.Smsf .SSTORE, .none)        := by rfl
theorem dec_5 : decode protoBytecode 5  = some (.Push .PUSH1, some (100, 1)) := by rfl
theorem dec_7 : decode protoBytecode 7  = some (.Push .PUSH1, some (7, 1))   := by rfl
theorem dec_9 : decode protoBytecode 9  = some (.Smsf .SLOAD, .none)         := by rfl
theorem dec_10 : decode protoBytecode 10 = some (.Push .PUSH1, some (9, 1))   := by rfl
theorem dec_12 : decode protoBytecode 12 = some (.ArithLogic .ADD, .none)     := by rfl
theorem dec_13 : decode protoBytecode 13 = some (.ArithLogic .LT, .none)      := by rfl
theorem dec_14 : decode protoBytecode 14 = some (.Smsf .GAS, .none)           := by rfl
theorem dec_15 : decode protoBytecode 15 = some (.Push .PUSH1, some (19, 1))  := by rfl
theorem dec_17 : decode protoBytecode 17 = some (.Smsf .JUMPI, .none)         := by rfl
theorem dec_19 : decode protoBytecode 19 = some (.Smsf .JUMPDEST, .none)      := by rfl
theorem dec_20 : decode protoBytecode 20 = some (.Push .PUSH1, some (0, 1))   := by rfl
theorem dec_22 : decode protoBytecode 22 = some (.Push .PUSH1, some (0, 1))   := by rfl
theorem dec_24 : decode protoBytecode 24 = some (.System .RETURN, .none)      := by rfl

/-! ## The named post-frames (the internal `Runs` witness)

Each `f*` is the previous frame after one opcode rule's transformer, layered
exactly like `ProgramExamples.sq*`. `f0` is the entry frame; the chain runs
PUSH;PUSH;SSTORE;PUSH;PUSH;SLOAD;PUSH;ADD;LT;GAS — landing at the JUMPI site `f10`. -/

private def f1  (g : UInt64) : Frame := pushFrame (fr0 g) 5
private def f2  (g : UInt64) : Frame := pushFrame (f1 g) 7
private def f3  (g : UInt64) : Frame := sstoreFrame (f2 g) 7 5 (fr0 g).exec.stack
private def f4  (g : UInt64) : Frame := pushFrame (f3 g) 100
private def f5  (g : UInt64) : Frame := pushFrame (f4 g) 7
private def f6  (g : UInt64) : Frame := sloadFrame (f5 g) 7 (100 :: (fr0 g).exec.stack)
private def f7  (g : UInt64) : Frame := pushFrame (f6 g) 9
private def f8  (g : UInt64) : Frame := addFrame (f7 g) 9 5 (100 :: (fr0 g).exec.stack)
private def f9  (g : UInt64) : Frame := ltFrame (f8 g) 14 100 (fr0 g).exec.stack
private def f10 (g : UInt64) : Frame := gasFrame (f9 g)

/-- The self account is present in the entry world (for the SSTORE/SLOAD lens). -/
private def protoSelfAcc (g : UInt64) : Account := (fr0 g).exec.accounts.find! addrA

private theorem proto_self_present (g : UInt64) :
    (fr0 g).exec.accounts.find? (fr0 g).exec.executionEnv.address = some (protoSelfAcc g) := by rfl

/-! ### Gas along the chain, as `subCharges` (the running balance)

The charge list in execution order is `chs = [3,3,22100,3,3,100,3,3,3,2]`
(PUSH PUSH SSTORE PUSH PUSH SLOAD[warm] PUSH ADD LT GAS), summing to `22223`. -/

private def chs : List ℕ := [3, 3, 22100, 3, 3, 100, 3, 3, 3, 2]

private theorem chs_sum : chs.sum = 22223 := by decide

private theorem gas_f1  (g : UInt64) : (f1 g).exec.gasAvailable  = subCharges g [3] := by
  show (g - UInt64.ofNat Gverylow) = _; rfl
private theorem gas_f2  (g : UInt64) : (f2 g).exec.gasAvailable  = subCharges g [3,3] := by
  show ((f1 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gas_f1]; rfl
private theorem gas_f3  (g : UInt64) : (f3 g).exec.gasAvailable  = subCharges g [3,3,22100] := by
  show ((f2 g).exec.gasAvailable - UInt64.ofNat (sstoreChargeOf (f2 g).exec 7 5)) = _
  rw [show sstoreChargeOf (f2 g).exec 7 5 = 22100 from rfl, gas_f2]; rfl
private theorem gas_f4  (g : UInt64) : (f4 g).exec.gasAvailable  = subCharges g [3,3,22100,3] := by
  show ((f3 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gas_f3]; rfl
private theorem gas_f5  (g : UInt64) : (f5 g).exec.gasAvailable  = subCharges g [3,3,22100,3,3] := by
  show ((f4 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gas_f4]; rfl
private theorem gas_f6  (g : UInt64) : (f6 g).exec.gasAvailable  = subCharges g [3,3,22100,3,3,100] := by
  show ((f5 g).exec.gasAvailable - UInt64.ofNat (sloadCost
      ((f5 g).exec.substate.accessedStorageKeys.contains ((f5 g).exec.executionEnv.address, 7)))) = _
  rw [show ((f5 g).exec.substate.accessedStorageKeys.contains ((f5 g).exec.executionEnv.address, 7))
        = true from rfl, show sloadCost true = 100 from rfl, gas_f5]; rfl
private theorem gas_f7  (g : UInt64) : (f7 g).exec.gasAvailable  = subCharges g [3,3,22100,3,3,100,3] := by
  show ((f6 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gas_f6]; rfl
private theorem gas_f8  (g : UInt64) : (f8 g).exec.gasAvailable  = subCharges g [3,3,22100,3,3,100,3,3] := by
  show ((f7 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gas_f7]; rfl
private theorem gas_f9  (g : UInt64) : (f9 g).exec.gasAvailable  = subCharges g [3,3,22100,3,3,100,3,3,3] := by
  show ((f8 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gas_f8]; rfl
private theorem gas_f10 (g : UInt64) : (f10 g).exec.gasAvailable = subCharges g chs := by
  show ((f9 g).exec.gasAvailable - UInt64.ofNat Gbase) = _; rw [gas_f9]; rfl

/-! ### `toNat` of the running gas at each frame (for the per-step gas gates)

A small adequacy floor `G₀ = 30000` clears every gate (the deepest charge prefix
sums to `22221` before the GAS opcode; `30000` leaves margin). -/

private theorem toNat_subCharges_prefix (g : UInt64) (hg : 30000 ≤ g.toNat)
    (l : List ℕ) (hle : l.sum ≤ 22223) :
    (subCharges g l).toNat = g.toNat - l.sum :=
  toNat_subCharges g l (by omega)

/-! ## The straight-line prefix run to the GAS / JUMPI site

`Runs (fr0 g) (f10 g)` — the ten opcode rules glued by `Runs.trans`. Each step's
decode is a `dec_*` fact; each stack shape is `rfl`; each gas gate threads `g`
through `gas_f*` + `toNat_subCharges_prefix` then `omega`. This is the v1
`ProgramExamples.seq_runs` pattern, extended with SLOAD/ADD/LT/GAS. -/
private theorem proto_prefix_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Runs (fr0 g) (f10 g) := by
  have gv : Gverylow = 3 := rfl
  refine Runs.trans (runs_push1 (fr0 g) 5 dec_0 ?g0 (by show (0:ℕ)+1≤1024; omega))
    (Runs.trans (runs_push1 (f1 g) 7 dec_2 ?g1 (by show (1:ℕ)+1≤1024; omega))
    (Runs.trans (runs_sstore (f2 g) 7 5 (fr0 g).exec.stack dec_4 rfl (by show (2:ℕ)≤1024; omega)
        rfl ?gstip ?gcost)
    (Runs.trans (runs_push1 (f3 g) 100 dec_5 ?g3 (by show (0:ℕ)+1≤1024; omega))
    (Runs.trans (runs_push1 (f4 g) 7 dec_7 ?g4 (by show (1:ℕ)+1≤1024; omega))
    (Runs.trans (runs_sload (f5 g) 7 (100 :: (fr0 g).exec.stack) dec_9 rfl (by show (2:ℕ)≤1024; omega) ?gsload)
    (Runs.trans (runs_push1 (f6 g) 9 dec_10 ?g6 (by show (2:ℕ)+1≤1024; omega))
    (Runs.trans (runs_add (f7 g) 9 5 (100 :: (fr0 g).exec.stack) dec_12 rfl (by show (3:ℕ)≤1024; omega) ?gadd)
    (Runs.trans (runs_lt (f8 g) 14 100 (fr0 g).exec.stack dec_13 rfl (by show (2:ℕ)≤1024; omega) ?glt)
      (runs_gas (f9 g) dec_14 (by show (1:ℕ)+1≤1024; omega) ?ggas)))))))))
  case g0 => show 3 ≤ (fr0 g).exec.gasAvailable.toNat; show 3 ≤ g.toNat; omega
  case g1 => rw [gas_f1, toNat_subCharges_prefix g hg [3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case gstip =>
    show ¬ (f2 g).exec.gasAvailable.toNat ≤ Gcallstipend
    rw [gas_f2, toNat_subCharges_prefix g hg [3,3] (by decide), show Gcallstipend = 2300 from rfl]; simp only [List.sum_cons, List.sum_nil]; omega
  case gcost =>
    rw [show sstoreChargeOf (f2 g).exec 7 5 = 22100 from rfl, gas_f2,
        toNat_subCharges_prefix g hg [3,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case g3 => rw [gas_f3, toNat_subCharges_prefix g hg [3,3,22100] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case g4 => rw [gas_f4, toNat_subCharges_prefix g hg [3,3,22100,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case gsload =>
    rw [show ((f5 g).exec.substate.accessedStorageKeys.contains ((f5 g).exec.executionEnv.address, 7))
          = true from rfl, show sloadCost true = 100 from rfl, gas_f5,
        toNat_subCharges_prefix g hg [3,3,22100,3,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case g6 => rw [gas_f6, toNat_subCharges_prefix g hg [3,3,22100,3,3,100] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case gadd =>
    show Gverylow ≤ (f7 g).exec.gasAvailable.toNat
    rw [gv, gas_f7, toNat_subCharges_prefix g hg [3,3,22100,3,3,100,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case glt =>
    show Gverylow ≤ (f8 g).exec.gasAvailable.toNat
    rw [gv, gas_f8, toNat_subCharges_prefix g hg [3,3,22100,3,3,100,3,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega
  case ggas =>
    show Gbase ≤ (f9 g).exec.gasAvailable.toNat
    rw [show Gbase = 2 from rfl, gas_f9, toNat_subCharges_prefix g hg [3,3,22100,3,3,100,3,3,3] (by decide)]; simp only [List.sum_cons, List.sum_nil]; omega

/-- `UInt256.ofUInt64` is injective on zero: a non-zero `UInt64` maps to a non-zero
`UInt256`. Used to show the observed-gas word is non-zero (so the JUMPI is taken). -/
theorem ofUInt64_ne_zero (a : UInt64) (ha : a.toNat ≠ 0) : UInt256.ofUInt64 a ≠ 0 := by
  intro h
  apply ha
  have h0 := congrArg (fun w => (w.l0).toNat) h
  have h1 := congrArg (fun w => (w.l1).toNat) h
  simp only [UInt256.ofUInt64] at h0 h1
  have e0 : ((0:UInt256).l0).toNat = 0 := rfl
  have e1 : ((0:UInt256).l1).toNat = 0 := rfl
  rw [e0] at h0; rw [e1] at h1
  -- h0 : (a.toUInt32).toNat = 0 ; h1 : ((a >>> 32).toUInt32).toNat = 0
  have lt64 : a.toNat < 2^64 := a.toNat_lt
  simp only [UInt64.toUInt32_toNat, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
             show ((32:UInt64).toNat) % 64 = 32 from rfl] at h0 h1
  -- h0 : a.toNat % 2^32 = 0 ; h1 : a.toNat / 2^32 % 2^32 = 0 ; lt64 : a.toNat < 2^64
  have dm0 := Nat.div_add_mod a.toNat (2^32)
  have dm1 := Nat.div_add_mod (a.toNat / 2^32) (2^32)
  simp only [show (2:Nat)^64 = 4294967296 * 4294967296 from rfl,
             show (2:Nat)^32 = 4294967296 from rfl] at *
  omega

/-! ## The observed-gas word (§3.4: what the `gasRead` event must carry)

`protoObs g` is the word the `GAS` opcode pushes at the JUMPI site: `ofUInt64` of
the post-charge gas `g - 22223`. The IR's `gasRead` event must carry **this** value
for the IR and the bytecode to take the same branch — the "events realised by the
bytecode" clause. For `G₀ ≤ g` it is non-zero, so the gas-dependent branch is
taken. -/
def protoObs (g : UInt64) : Word := UInt256.ofUInt64 (subCharges g chs)

/-- The `GAS` opcode at `f10` pushed exactly `protoObs g`. Definitional. -/
theorem f10_top (g : UInt64) : (f10 g).exec.stack.head? = some (protoObs g) := by
  show some (UInt256.ofUInt64 (f10 g).exec.gasAvailable) = some (protoObs g)
  rw [gas_f10]; rfl

/-- For `G₀ ≤ g` the observed gas is non-zero (so the JUMPI is taken). -/
theorem protoObs_ne_zero (g : UInt64) (hg : 30000 ≤ g.toNat) : protoObs g ≠ 0 := by
  apply ofUInt64_ne_zero
  rw [toNat_subCharges g chs (by rw [chs_sum]; omega), chs_sum]; omega

/-! ## The JUMPI destination (pc 19) is a valid jump target

`pc 19` holds a `JUMPDEST` reachable from the start (walking the 13 instructions
PUSH;PUSH;SSTORE;PUSH;PUSH;SLOAD;PUSH;ADD;LT;GAS;PUSH;JUMPI;STOP). Routed through the
total `validJumpDests` via `mem_validJumpDests_of_reachable_jumpdest`, axiom-clean. -/
theorem nineteen_mem_validJumps : (19 : UInt32) ∈ validJumpDests protoBytecode 0 :=
  mem_validJumpDests_of_reachable_jumpdest protoBytecode
    (.step (byte := 0x60) (by decide) (.step (byte := 0x60) (by decide)
    (.step (byte := 0x55) (by decide) (.step (byte := 0x60) (by decide)
    (.step (byte := 0x60) (by decide) (.step (byte := 0x54) (by decide)
    (.step (byte := 0x60) (by decide) (.step (byte := 0x01) (by decide)
    (.step (byte := 0x10) (by decide) (.step (byte := 0x5a) (by decide)
    (.step (byte := 0x60) (by decide) (.step (byte := 0x57) (by decide)
    (.step (byte := 0x00) (by decide) (.refl 19))))))))))))))
    (byte := 0x5b) (by decide) (by decide)

/-! ## The branch / RETURN tail

`f11` pushes the JUMPI destination `19`; the taken arm (gas non-zero) jumps to the
`JUMPDEST` at pc 19, steps over it, pushes `0 0`, and RETURNs empty. The whole tail
composes into one `Runs (f10 g) (retFr g)` via `runs_branch` (taken side) threaded
with `Runs.trans`; `retFr` then halts by `stepFrame_return_empty`. -/

private def f11 (g : UInt64) : Frame := pushFrame (f10 g) 19
/-- After the taken JUMPI (jump to pc 19), `rest = [1]` (the residual lt result). -/
private def fJumped (g : UInt64) : Frame := jumpFrame (f11 g) Ghigh 19 (1 :: [])
private def fJd (g : UInt64) : Frame := jumpdestFrame (fJumped g)
private def fR1 (g : UInt64) : Frame := pushFrame (fJd g) 0
private def fR2 (g : UInt64) : Frame := pushFrame (fR1 g) 0
/-- The RETURN-site frame (pc 24, stack `0 :: 0 :: [1]`). -/
private def retFr (g : UInt64) : Frame := fR2 g

private theorem gas_f11 (g : UInt64) :
    (f11 g).exec.gasAvailable = subCharges g chs - UInt64.ofNat 3 := by
  show ((f10 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _
  rw [gas_f10]; rfl

/-- `f11`'s gas, in `toNat` form (`g - 22226`). -/
private theorem toNat_gas_f11 (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (f11 g).exec.gasAvailable.toNat = g.toNat - 22226 := by
  rw [gas_f11, toNat_sub_ofNat _ 3 (by
        rw [toNat_subCharges g chs (by rw [chs_sum]; omega), chs_sum]; omega) (by omega),
      toNat_subCharges g chs (by rw [chs_sum]; omega), chs_sum]; omega

/-- `get_dest 19 = some 19` at the JUMPI frame `f11`. -/
private theorem f11_get_dest (g : UInt64) : (f11 g).get_dest 19 = some 19 :=
  Frame.get_dest_of_mem _ (d := 19) (by decide)
    (by show (19 : UInt32) ∈ validJumpDests protoBytecode 0; exact nineteen_mem_validJumps)

/-- The JUMPI condition word at `f11` is `protoObs g` (the GAS value), non-zero for
`G₀ ≤ g`; the JUMPI stack is `19 :: protoObs g :: 1 :: []`. -/
private theorem f11_stk (g : UInt64) :
    (f11 g).exec.stack = (19 : UInt256) :: protoObs g :: (1 : UInt256) :: [] := by
  show (f10 g).exec.stack.push 19 = _
  show ((f9 g).exec.stack.push (UInt256.ofUInt64 (f10 g).exec.gasAvailable)).push 19 = _
  rw [gas_f10]
  show ((f9 g).exec.stack.push (protoObs g)).push 19 = _
  rfl

/-- **The branch / RETURN tail composes into one `Runs (f10 g) (retFr g)`.** The
PUSH of the destination, then the taken JUMPI (`runs_branch`, gas non-zero), the
`JUMPDEST` step, and the two `PUSH1 0`s, glued by `Runs.trans`. -/
private theorem proto_tail_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Runs (f10 g) (retFr g) := by
  -- gas margins along the tail (all ≥ the small charges, derived from f11's gas)
  have hf11 := toNat_gas_f11 g hg
  -- PUSH1 19 onto f10
  refine Runs.trans (runs_push1 (f10 g) 19 dec_15 ?gp (by show (2:ℕ)+1≤1024; omega)) ?_
  case gp => -- f10 gas ≥ 3
    rw [gas_f10, toNat_subCharges g chs (by rw [chs_sum]; omega), chs_sum]; omega
  -- JUMPI (taken arm) via runs_branch, then JUMPDEST + two pushes
  refine runs_branch (dest := 19) (cond := protoObs g) (rest := (1 : UInt256) :: [])
    dec_17 (f11_stk g) (by show (3:ℕ)≤1024; omega) ?ghi
    (Or.inl ⟨19, protoObs_ne_zero g hg, f11_get_dest g, ?taken⟩)
  case ghi => -- Ghigh = 10 ≤ f11 gas
    show Ghigh ≤ (f11 g).exec.gasAvailable.toNat
    rw [show Ghigh = 10 from rfl, hf11]; omega
  case taken =>
    -- from jumpFrame f11 Ghigh 19 [1] (pc 19, stack [1]) : JUMPDEST; PUSH 0; PUSH 0
    have hgJd : (fJumped g).exec.gasAvailable.toNat = g.toNat - 22236 := by
      show ((f11 g).exec.gasAvailable - UInt64.ofNat Ghigh).toNat = _
      rw [show Ghigh = 10 from rfl, toNat_sub_ofNat _ 10 (by rw [hf11]; omega) (by omega), hf11]; omega
    refine Runs.trans (runs_jumpdest (fJumped g) ?djd (by show (1:ℕ)≤1024; omega) ?gjd) ?_
    case djd => show decode (fJumped g).exec.executionEnv.code (fJumped g).exec.pc = _
                show decode protoBytecode 19 = _; exact dec_19
    case gjd => show Gjumpdest ≤ (fJumped g).exec.gasAvailable.toNat
                rw [show Gjumpdest = 1 from rfl, hgJd]; omega
    refine Runs.trans (runs_push1 (fJd g) 0 ?dp1 ?gp1 (by show (1:ℕ)+1≤1024; omega)) ?_
    case dp1 => show decode (fJd g).exec.executionEnv.code (fJd g).exec.pc = _
                show decode protoBytecode 20 = _; exact dec_20
    case gp1 => show 3 ≤ (fJd g).exec.gasAvailable.toNat
                show 3 ≤ ((fJumped g).exec.gasAvailable - UInt64.ofNat Gjumpdest).toNat
                rw [show Gjumpdest = 1 from rfl, toNat_sub_ofNat _ 1 (by rw [hgJd]; omega) (by omega), hgJd]; omega
    refine runs_push1 (fR1 g) 0 ?dp2 ?gp2 (by show (2:ℕ)+1≤1024; omega)
    case dp2 => show decode (fR1 g).exec.executionEnv.code (fR1 g).exec.pc = _
                show decode protoBytecode 22 = _; exact dec_22
    case gp2 => show 3 ≤ (fR1 g).exec.gasAvailable.toNat
                show 3 ≤ ((fJd g).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
                have : (fJd g).exec.gasAvailable.toNat = g.toNat - 22237 := by
                  show ((fJumped g).exec.gasAvailable - UInt64.ofNat Gjumpdest).toNat = _
                  rw [show Gjumpdest = 1 from rfl, toNat_sub_ofNat _ 1 (by rw [hgJd]; omega) (by omega), hgJd]; omega
                rw [show Gverylow = 3 from rfl, toNat_sub_ofNat _ 3 (by rw [this]; omega) (by omega), this]; omega

/-- The RETURN-site frame stack is `0 :: 0 :: [1]` — the empty-window RETURN shape. -/
private theorem retFr_stk (g : UInt64) :
    (retFr g).exec.stack = (0 : UInt256) :: (0 : UInt256) :: (1 : UInt256) :: [] := by
  show ((fR1 g).exec.stack.push 0) = _
  show (((fJd g).exec.stack.push 0).push 0) = _
  show ((((fJumped g).exec.stack).push 0).push 0) = _
  rfl

/-- The RETURN at `retFr g` halts successfully (empty output) — the `hhalt` the
bridge consumes. -/
private theorem retFr_halts (g : UInt64) :
    stepFrame (retFr g)
      = .halted (.success (returnEmptyPost (retFr g).exec ((1 : UInt256) :: []))
          ((retFr g).exec.memory.readWithPadding (0 : UInt256).toNat (0 : UInt256).toNat)) :=
  stepFrame_return_empty (retFr g) ((1 : UInt256) :: [])
    (by show decode (retFr g).exec.executionEnv.code (retFr g).exec.pc = _
        show decode protoBytecode 24 = _; exact dec_24)
    (retFr_stk g) (by rw [retFr_stk]; show (3:ℕ) ≤ 1024; omega)

/-! ## The top-level `messageCall` observable

`messageCall (protoParams g)` halts successfully, returns empty output, and leaves
`5` at storage cell `(addrA, 7)` — read off the assembled `Runs` + `retFr_halts`
through `messageCall_runs`. -/

/-- The halt the assembled run lands on. -/
private def protoHalt (g : UInt64) : FrameHalt :=
  .success (returnEmptyPost (retFr g).exec ((1 : UInt256) :: []))
    ((retFr g).exec.memory.readWithPadding (0 : UInt256).toNat (0 : UInt256).toNat)

/-- **`messageCall` of the witness bytecode** pins to the assembled run's halt. -/
theorem proto_messageCall (g : UInt64) (hg : 30000 ≤ g.toNat) :
    messageCall (protoParams g)
      = .ok (FrameResult.toCallResult (endFrame (retFr g) (protoHalt g))) :=
  messageCall_runs (protoParams g)
    (beginCall_code (protoParams g) protoBytecode rfl)
    ((proto_prefix_runs g hg).trans (proto_tail_runs g hg))
    (retFr_halts g)

/-- The completed call's storage at `(addrA, 7)` is `5` (the SSTORE'd value,
preserved by every later transformer). -/
theorem proto_storageAt (g : UInt64) (hg : 30000 ≤ g.toNat) :
    CallResult.storageAt (FrameResult.toCallResult (endFrame (retFr g) (protoHalt g))) addrA 7 = 5 := by
  show ((endFrame (retFr g) (protoHalt g)).toCallResult.accounts.find? addrA
          |>.option 0 (·.lookupStorage 7)) = 5
  have hacc : (endFrame (retFr g) (protoHalt g)).toCallResult.accounts = (f3 g).exec.accounts := by rfl
  rw [hacc]
  exact sstoreFrame_storage_self (f2 g) 7 5 (fr0 g).exec.stack (protoSelfAcc g)
    (by show (f2 g).exec.accounts.find? (f2 g).exec.executionEnv.address = _; exact proto_self_present g)
    (by decide)

/-- The completed call succeeded with empty output. -/
theorem proto_success (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (FrameResult.toCallResult (endFrame (retFr g) (protoHalt g))).success = true := by rfl

/-! ## The IR program (mirrors the witness bytecode's values)

Block 0: `t0:=5; t1:=7; sstore t1 t0; t2:=100; t3:=sload t1; t4:=9;
t5:=add t4 t3; t6:=lt t5 t2; t7:=gas` then `branch t7 L1 L2`.
Block 1 (`L1`): `ret t6`. Block 2 (`L2`): `stop`.

The arithmetic mirrors the bytecode exactly: `add t4 t3 = UInt256.add 9 5`,
`lt t5 t2 = UInt256.lt 14 100` — so the IR values are *definitionally* the lowered
opcodes'. `t7 := gas` consumes the single `gasRead` event. -/

private def tmp (n : Nat) : Tmp := ⟨n⟩
private def lbl (n : Nat) : Label := ⟨n⟩

/-- Block 0 of `protoIR`, named so the `RunStmts` chain reduces against the explicit
statement list rather than forcing the whole `Program`/`Array`. -/
def protoBlock0 : Block :=
  { stmts := [
      .assign (tmp 0) (.imm 5),
      .assign (tmp 1) (.imm 7),
      .sstore (tmp 1) (tmp 0),
      .assign (tmp 2) (.imm 100),
      .assign (tmp 3) (.sload (tmp 1)),
      .assign (tmp 4) (.imm 9),
      .assign (tmp 5) (.add (tmp 4) (tmp 3)),
      .assign (tmp 6) (.lt (tmp 5) (tmp 2)),
      .assign (tmp 7) .gas ],
    term := .branch (tmp 7) (lbl 1) (lbl 2) }

def protoBlock1 : Block := { stmts := [], term := .ret (tmp 6) }
def protoBlock2 : Block := { stmts := [], term := .stop }

def protoIR : Program :=
  { entry := lbl 0, blocks := #[protoBlock0, protoBlock1, protoBlock2] }

theorem protoIR_block0 : blockAt protoIR (lbl 0) = some protoBlock0 := rfl
theorem protoIR_block1 : blockAt protoIR (lbl 1) = some protoBlock1 := rfl

/-- The observable the IR run produces: world with `7 ↦ 5`, returning the `lt`
result `UInt256.lt 14 100`. Independent of the initial `w₀ 7` (the SSTORE overwrites
it before the SLOAD). -/
def protoObsResult (w₀ : World) : Observable :=
  { worldDelta := fun k => if k = (7 : Word) then (5 : Word) else w₀ k
    result := .returned (UInt256.lt 14 100) }

/-! ### The block-0 statement run, stepwise over named intermediate states

To keep every `whnf` bounded to a single `setLocal`/`setStorage` layer (the whole
nested-record defeq blows up otherwise), we name each intermediate state `s0 … s9`
and prove one `EvalStmt` between consecutive ones, then chain them. -/

private def s0 (w₀ : World) : IRState := { locals := fun _ => none, world := w₀ }
private def s1 (w₀ : World) : IRState := (s0 w₀).setLocal (tmp 0) 5
private def s2 (w₀ : World) : IRState := (s1 w₀).setLocal (tmp 1) 7
private def s3 (w₀ : World) : IRState := (s2 w₀).setStorage 7 5
private def s4 (w₀ : World) : IRState := (s3 w₀).setLocal (tmp 2) 100
private def s5 (w₀ : World) : IRState := (s4 w₀).setLocal (tmp 3) ((s4 w₀).world 7)
private def s6 (w₀ : World) : IRState := (s5 w₀).setLocal (tmp 4) 9
private def s7 (w₀ : World) : IRState := (s6 w₀).setLocal (tmp 5) (UInt256.add 9 5)
private def s8 (w₀ : World) : IRState := (s7 w₀).setLocal (tmp 6) (UInt256.lt 14 100)
private def s9 (w₀ : World) (obs : Word) : IRState := (s8 w₀).setLocal (tmp 7) obs

private theorem s9_locals6 (w₀ : World) (obs : Word) :
    (s9 w₀ obs).locals (tmp 6) = some (UInt256.lt 14 100) := by rfl
private theorem s9_locals7 (w₀ : World) (obs : Word) :
    (s9 w₀ obs).locals (tmp 7) = some obs := by rfl
private theorem s9_world (w₀ : World) (obs : Word) :
    (s9 w₀ obs).world = (protoObsResult w₀).worldDelta := by
  funext k; show (if k = (7:Word) then (5:Word) else w₀ k) = _; rfl

/-- **The gas-free IR run.** For any initial world `w₀` and any **non-zero**
observed gas `obs`, `protoIR` consuming the single `gasRead obs` event halts with
`protoObsResult w₀` — the gas-dependent branch takes the `ret` arm. `obs` is
supplied by the run (the event), never computed. -/
theorem proto_IRRun (w₀ : World) (obs : Word) (hobs : obs ≠ 0) :
    IRRun protoIR w₀ [Event.gasRead obs] (protoObsResult w₀) := by
  -- the nine block-0 statements, each between named states (local, cheap `whnf`)
  have e0 : EvalStmt protoIR (s0 w₀) [Event.gasRead obs] (.assign (tmp 0) (.imm 5)) (s1 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e1 : EvalStmt protoIR (s1 w₀) [Event.gasRead obs] (.assign (tmp 1) (.imm 7)) (s2 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e2 : EvalStmt protoIR (s2 w₀) [Event.gasRead obs] (.sstore (tmp 1) (tmp 0)) (s3 w₀) [Event.gasRead obs] :=
    EvalStmt.sstore (kw := 7) (vw := 5) rfl rfl
  have e3 : EvalStmt protoIR (s3 w₀) [Event.gasRead obs] (.assign (tmp 2) (.imm 100)) (s4 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e4 : EvalStmt protoIR (s4 w₀) [Event.gasRead obs] (.assign (tmp 3) (.sload (tmp 1))) (s5 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e5 : EvalStmt protoIR (s5 w₀) [Event.gasRead obs] (.assign (tmp 4) (.imm 9)) (s6 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e6 : EvalStmt protoIR (s6 w₀) [Event.gasRead obs] (.assign (tmp 5) (.add (tmp 4) (tmp 3))) (s7 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e7 : EvalStmt protoIR (s7 w₀) [Event.gasRead obs] (.assign (tmp 6) (.lt (tmp 5) (tmp 2))) (s8 w₀) [Event.gasRead obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e8 : EvalStmt protoIR (s8 w₀) [Event.gasRead obs] (.assign (tmp 7) .gas) (s9 w₀ obs) [] :=
    EvalStmt.assignGas
  have hss : RunStmts protoIR (s0 w₀) [Event.gasRead obs] protoBlock0.stmts (s9 w₀ obs) [] :=
    .cons e0 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 .nil))))))))
  -- branch on t7 = obs ≠ 0 → block 1 (ret t6); resulting O is `protoObsResult w₀`
  have hbranch :
      RunFrom protoIR (s0 w₀) [Event.gasRead obs] (lbl 0)
        { worldDelta := (s9 w₀ obs).world, result := .returned (UInt256.lt 14 100) } :=
    RunFrom.branchThen (b := protoBlock0) (cw := obs) (thenL := lbl 1) (elseL := lbl 2)
      protoIR_block0 hss rfl (s9_locals7 w₀ obs) hobs
      (RunFrom.ret (b := protoBlock1) (t := tmp 6) protoIR_block1 RunStmts.nil rfl (s9_locals6 w₀ obs))
  rw [s9_world] at hbranch
  exact hbranch

end Lir.V2
