import BytecodeLayer.Drive
import BytecodeLayer.Step
import BytecodeLayer.Observables

/-!
# Capstone 1 — the call-free spine, in the shape we wanted

A handwritten program executed as a real `messageCall`, with the result stated
**only** through `CallResult.observe` (success + output). The statement is:

* **frame-free** — no `Frame`, `injectFrame`, pc, or stack;
* **fuel-free** — `seedFuel`/`drive`'s fuel never appears (it is discharged once,
  inside the proof, by `two_le_seedFuel` + `drive_halt`);
* **gas-honest by vacuity** — STOP charges nothing and the program reads no
  operands, so *no* `∃G₀` is needed and none is claimed: the equation holds for
  **every** `p` (any gas, including 0), which is exactly the honest statement for
  a gasless program. The quantitative `∃G₀` story is reserved for CALL.

The program is a single `STOP`. Out-of-range pcs decode to STOP, so the bare
empty program behaves identically; we use the explicit `0x00` byte for clarity.
The proof routes entirely through the characterization lemmas
(`stepFrame_stop`, `drive_halt`) — `messageCall`/`beginCall` are unfolded only to
expose the initial frame, never reasoned about structurally.
-/

namespace BytecodeLayer
open Evm

/-- The single-`STOP` program. -/
def stopProgram : ByteArray := ⟨#[0x00]⟩

theorem decode_stopProgram : decode stopProgram 0 = some (.System .STOP, .none) := by rfl

set_option maxHeartbeats 1000000 in
/-- **Capstone 1.** A message call into the single-`STOP` program succeeds with
empty output, for *any* call parameters whose code is `stopProgram` — no gas
floor required. Stated purely in observables. -/
theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  unfold messageCall
  unfold beginCall
  rw [hc]
  dsimp only
  rw [show seedFuel p.gas = (seedFuel p.gas - 2) + 2 by
        have := two_le_seedFuel p.gas; omega]
  rw [drive_halt _ _ _ (stepFrame_stop _ decode_stopProgram
        (le_of_eq_of_le (by rfl) (Nat.zero_le 1024)))]
  rfl

/-! ## A multi-instruction program — sequencing the run vocabulary

`PUSH1 0x05 ; STOP`. Now the run is two iterations: `drive_step` threads the
non-halting `PUSH1` (which charges `Gverylow = 3`), then `drive_halt` delivers
the `STOP`. This is where the **gas story first appears, and appears honestly**:
the equation needs `3 ≤ p.gas` — the exact intrinsic cost of the one charging
instruction — discharged once inside `stepFrame_push1`'s `if_neg`, never as an
`∃G₀` and never re-examined. Off the call path, gas is pure vacuity-propagation.
The result observables are unchanged (`success = true`, empty output): PUSH/STOP
have no observable effect, which is exactly what the projection should report. -/

/-- `PUSH1 0x05 ; STOP`. -/
def pushStopProgram : ByteArray := ⟨#[0x60, 0x05, 0x00]⟩

theorem decode_pushStop_0 :
    decode pushStopProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl

theorem decode_pushStop_2 :
    decode pushStopProgram ((0 : UInt32) + UInt8.toUInt32 2) = some (.System .STOP, .none) := by rfl

set_option maxHeartbeats 4000000 in
/-- **Capstone 1′.** A message call into `PUSH1 0x05 ; STOP` succeeds with empty
output for every `p` with `3 ≤ p.gas` — the program's exact gas cost, stated as a
plain hypothesis rather than an `∃G₀`. Observables-only, frame-free, fuel-free;
the proof composes `drive_step` (the PUSH) and `drive_halt` (the STOP). -/
theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  unfold messageCall
  unfold beginCall
  rw [hc]
  dsimp only
  rw [show seedFuel p.gas = ((seedFuel p.gas - 3) + 2) + 1 by
        have := two_le_seedFuel p.gas; unfold seedFuel at *; omega]
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 decode_pushStop_0 hg
        (by show (0 : ℕ) + 1 ≤ 1024; omega))]
  rw [drive_halt _ _ _ (stepFrame_stop _ decode_pushStop_2
        (le_of_eq_of_le (by rfl) (by omega : (1 : ℕ) ≤ 1024)))]
  rfl

/-! ## Capstone 2 — a persistent storage effect

`PUSH1 0x05 ; PUSH1 0x07 ; SSTORE ; STOP` run as a real `messageCall` into a
single account `addrA`, asserted through the **storage** observable: after the
call, `addrA`'s cell `7` holds `5`. This is the first rung with a persistent
world effect; the proof composes three `drive_step`s (the two PUSHes and the
SSTORE) and a final `drive_halt` (the STOP), then evaluates the returned
`accounts` map at `(addrA, 7)`.

The gas hypothesis is the program's **exact** cost stated plainly (not an
`∃G₀`): `3 + 3 + 22100 = 22106 ≤ p.gas`, where `22100 = Gcoldsload + Gsset` is
SSTORE's charge for a first write of a nonzero value to a cold, never-touched
slot (original = current = 0, new = 5). That floor also clears SSTORE's
`Gcallstipend` gate, since after the two PUSHes `gasAvailable ≥ 22100 > 2300`. -/

open GasConstants

/-- `gasAvailable` threading: charging `c ≤ g.toNat` gas (with `c` in range)
leaves exactly `g.toNat - c`. The one piece of UInt64 arithmetic the gas-honest
floor forces — used to carry the running balance across the two PUSHes and the
SSTORE charge, in place of a shadow gas ledger. -/
theorem toNat_sub_ofNat (g : UInt64) (c : ℕ) (hc : c ≤ g.toNat) (hlt : c < 2 ^ 64) :
    (g - UInt64.ofNat c).toNat = g.toNat - c := by
  have hofNat : (UInt64.ofNat c).toNat = c := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
  have hle : UInt64.ofNat c ≤ g := by
    rw [UInt64.le_iff_toNat_le, hofNat]; exact hc
  rw [UInt64.toNat_sub_of_le _ _ hle, hofNat]

/-- The single self-account `addrA = 0xC0FFEE`, present with a default account. -/
def addrA : AccountAddress := AccountAddress.ofNat 0xC0FFEE

/-- `PUSH1 0x05 ; PUSH1 0x07 ; SSTORE ; STOP`. -/
def sstoreProgram : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x07, 0x55, 0x00]⟩

theorem decode_sstore_0 :
    decode sstoreProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl

theorem decode_sstore_2 :
    decode sstoreProgram ((0 : UInt32) + UInt8.toUInt32 2)
      = some (.Push .PUSH1, some (7, 1)) := by rfl

theorem decode_sstore_4 :
    decode sstoreProgram (((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
      = some (.Smsf .SSTORE, .none) := by rfl

theorem decode_sstore_5 :
    decode sstoreProgram
      ((((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
      = some (.System .STOP, .none) := by rfl

/-- Message-call parameters running `sstoreProgram` in `addrA`, which is present
with a default account; no value, no calldata, state-modifying. -/
def paramsSStore (g : UInt64) : CallParams :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := #[]
    accounts := (∅ : AccountMap).insert addrA default
    originalAccounts := ∅
    substate := default
    caller := addrA
    origin := addrA
    recipient := addrA
    codeSource := .Code sstoreProgram
    gas := g
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 0
    canModifyState := true }

set_option maxHeartbeats 8000000 in
theorem messageCall_sstore_storageAt (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok ({ success := true, output := .empty }, 5) := by
  unfold messageCall
  dsimp only [paramsSStore]
  unfold beginCall
  dsimp only
  rw [show seedFuel g = ((((seedFuel g - 5) + 1) + 1) + 1) + 2 by
        have := two_le_seedFuel g; unfold seedFuel at *; omega]
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 decode_sstore_0 (by omega : 3 ≤ g.toNat)
        (by show (0 : ℕ) + 1 ≤ 1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  rw [drive_step _ _ _ (stepFrame_push1 _ 7 decode_sstore_2 (by
        show 3 ≤ (g - UInt64.ofNat GasConstants.Gverylow).toNat
        rw [show GasConstants.Gverylow = 3 from rfl,
            toNat_sub_ofNat g 3 (by omega) (by omega)]
        omega) (by
        show (1 : ℕ) + 1 ≤ 1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  simp only [show GasConstants.Gverylow = 3 from rfl]
  have hg2 : ((g - UInt64.ofNat 3) - UInt64.ofNat 3).toNat = g.toNat - 6 := by
    rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat g 3 (by omega) (by omega)]; omega) (by omega),
        toNat_sub_ofNat g 3 (by omega) (by omega)]
    omega
  rw [drive_step _ _ _ (stepFrame_sstore _ 7 5 _ decode_sstore_4 rfl ?hsz rfl ?hstip ?hcost)]
  case hsz => show (2 : ℕ) ≤ 1024; omega
  case hstip =>
    show ¬ ((g - UInt64.ofNat 3) - UInt64.ofNat 3).toNat ≤ Gcallstipend
    rw [hg2, show Gcallstipend = 2300 from rfl]; omega
  case hcost =>
    show sstoreChargeOf _ 7 5 ≤ ((g - UInt64.ofNat 3) - UInt64.ofNat 3).toNat
    rw [hg2]; show (22100 : ℕ) ≤ g.toNat - 6; omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  rw [drive_halt _ _ _ (stepFrame_stop _ decode_sstore_5 (by show (0 : ℕ) ≤ 1024; omega))]
  rfl

end BytecodeLayer
