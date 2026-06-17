import BytecodeLayer.Reasoning.Drive
import BytecodeLayer.Reasoning.Begin
import BytecodeLayer.Reasoning.Step
import BytecodeLayer.Observables
import BytecodeLayer.Programs

/-!
# Proof — program `decode` lemmas and the gas-threading bridge (`DecodeGas`)

Shared low-level proof machinery: the per-pc `decode` facts for the example
programs (`stopProgram`, `pushStopProgram`, `sstoreProgram`) and the
`toNat_sub_ofNat` UInt64 gas-threading bridge. The bridge is reused by the
straight-line program proofs (`Proof/ProgramExamples.lean`, built on
`Reasoning/Straightline.lean`) *and* by the descent / external-call proofs
(`Proof/DescentDrops.lean`, `Proof/ExternalCall.lean`) — it is not call-specific.
Despite the historical `CallFree` name, nothing here concerns the (now deleted)
call-free out-of-fuel rung.
-/

namespace BytecodeLayer.Proof
open Evm
open GasConstants

/-! ## STOP -/

theorem decode_stopProgram : decode stopProgram 0 = some (.System .STOP, .none) := by rfl

/-! ## PUSH1 ; STOP -/

theorem decode_pushStop_0 :
    decode pushStopProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl

theorem decode_pushStop_2 :
    decode pushStopProgram ((0 : UInt32) + UInt8.toUInt32 2) = some (.System .STOP, .none) := by rfl

/-! ## PUSH1 ; PUSH1 ; SSTORE ; STOP — the gas-threading bridge -/

/-- `gasAvailable` threading: charging `c ≤ g.toNat` gas (with `c` in range)
leaves exactly `g.toNat - c`. The one piece of UInt64 arithmetic the gas-honest
floor forces — used to carry the running balance across charges, in place of a
shadow gas ledger. -/
theorem toNat_sub_ofNat (g : UInt64) (c : ℕ) (hc : c ≤ g.toNat) (hlt : c < 2 ^ 64) :
    (g - UInt64.ofNat c).toNat = g.toNat - c := by
  have hofNat : (UInt64.ofNat c).toNat = c := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
  have hle : UInt64.ofNat c ≤ g := by
    rw [UInt64.le_iff_toNat_le, hofNat]; exact hc
  rw [UInt64.toNat_sub_of_le _ _ hle, hofNat]

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

end BytecodeLayer.Proof
