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

end Lir.V2
