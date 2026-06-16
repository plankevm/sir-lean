import BytecodeLayer.Reasoning.Drive
import BytecodeLayer.Reasoning.Begin
import BytecodeLayer.Reasoning.Step
import BytecodeLayer.Observables
import BytecodeLayer.Programs
import BytecodeLayer.Proof.CallFree

/-!
# Proof — sequence decode lemmas and the gas-threading composition lemma (Sequence)

Shared machinery for the multi-write straight-line program: its per-pc `decode`
lemmas and the `subCharges` / `toNat_subCharges` gas-threading composition lemma
(prefix-sum of charges against the running `gasAvailable`, proved once by induction
on the suffix). The sequence capstone itself is now an instance of the general
straight-line rung (`Proof/StraightlineInstances.lean`); this file holds only the
pieces that instance — and the external-call proof — reuse.
-/

namespace BytecodeLayer.Proof
open Evm
open GasConstants

/-! ## Decode lemmas -/

theorem decode_seq_0 :
    decode seqProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl
theorem decode_seq_2 :
    decode seqProgram ((0 : UInt32) + UInt8.toUInt32 2)
      = some (.Push .PUSH1, some (7, 1)) := by rfl
theorem decode_seq_4 :
    decode seqProgram (((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
      = some (.Smsf .SSTORE, .none) := by rfl
theorem decode_seq_5 :
    decode seqProgram
      ((((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
      = some (.Push .PUSH1, some (11, 1)) := by rfl
theorem decode_seq_7 :
    decode seqProgram
      (((((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
        + UInt8.toUInt32 2)
      = some (.Push .PUSH1, some (9, 1)) := by rfl
theorem decode_seq_9 :
    decode seqProgram
      ((((((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
        + UInt8.toUInt32 2) + UInt8.toUInt32 2)
      = some (.Smsf .SSTORE, .none) := by rfl
theorem decode_seq_10 :
    decode seqProgram
      (((((((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
        + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
      = some (.System .STOP, .none) := by rfl

/-! ## The gas-threading composition lemma the SEQUENCE forces

With several charging instructions in series, the running `gasAvailable` is
`g - c₁ - c₂ - …` and each step's gas/stipend side-goals must compare a *prefix
sum* of charges against it. Doing this with nested `toNat_sub_ofNat` explodes
quadratically. The sequence forces this single fact, proved once by induction on
the suffix of charges and reused at every step. -/

/-- Subtract a list of charges off `g` (each as `UInt64.ofNat`), left to right. -/
def subCharges (g : UInt64) : List ℕ → UInt64
  | []      => g
  | c :: cs => subCharges (g - UInt64.ofNat c) cs

/-- **Gas threading (the composition lemma).** If the total of `cs` fits in `g`
and `g.toNat < 2^64`, subtracting the charges one by one lands at
`g.toNat - cs.sum`. Proved by induction on `cs`, reusing `toNat_sub_ofNat`. -/
theorem toNat_subCharges (g : UInt64) (cs : List ℕ)
    (hsum : cs.sum ≤ g.toNat) : (subCharges g cs).toNat = g.toNat - cs.sum := by
  induction cs generalizing g with
  | nil => simp [subCharges]
  | cons c cs ih =>
    have hc : c ≤ g.toNat := by
      have : c ≤ (c :: cs).sum := by simp [List.sum_cons]
      omega
    have h1 : (g - UInt64.ofNat c).toNat = g.toNat - c :=
      toNat_sub_ofNat g c hc (lt_of_le_of_lt hc g.toNat_lt)
    have hsum' : cs.sum ≤ (g - UInt64.ofNat c).toNat := by
      rw [h1]; have : (c :: cs).sum = c + cs.sum := by simp [List.sum_cons]
      omega
    show (subCharges (g - UInt64.ofNat c) cs).toNat = _
    rw [ih (g - UInt64.ofNat c) hsum', h1]
    have : (c :: cs).sum = c + cs.sum := by simp [List.sum_cons]
    omega

end BytecodeLayer.Proof
