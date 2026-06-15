import BytecodeLayer.Drive
import BytecodeLayer.Step
import BytecodeLayer.Observables
import BytecodeLayer.Capstone1

/-!
# Capstone 3 — a straight-line SEQUENCE of charging instructions

`PUSH1 0x05 ; PUSH1 0x07 ; SSTORE ; PUSH1 0x0B ; PUSH1 0x09 ; SSTORE ; STOP`

run as a real `messageCall` into a single account `addrA`, asserted through the
**storage** observable at *two distinct keys*: after the call, cell `7` holds `5`
and cell `9` holds `11`. This is the first rung with **several** charging
instructions in series, and the first whose proof would *repeat* the
per-instruction stepping work — which is exactly why it forces the extraction of
a reusable composition lemma.
-/

namespace BytecodeLayer
open Evm
open GasConstants

/-- `PUSH1 5 ; PUSH1 7 ; SSTORE ; PUSH1 0x0B ; PUSH1 9 ; SSTORE ; STOP`. -/
def seqProgram : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x07, 0x55, 0x60, 0x0B, 0x60, 0x09, 0x55, 0x00]⟩

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

/-- Message-call parameters running `seqProgram` in `addrA`. -/
def paramsSeq (g : UInt64) : CallParams :=
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
    codeSource := .Code seqProgram
    gas := g
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 0
    canModifyState := true }

/-! ## The gas-threading composition lemma the SEQUENCE forces

With several charging instructions in series, the running `gasAvailable` is
`g - c₁ - c₂ - …` and each step's gas/stipend side-goals must compare a *prefix
sum* of charges against it. Doing this with nested `toNat_sub_ofNat` (as the
single-SSTORE capstone could afford) explodes quadratically. The sequence forces
this single fact, proved once by induction on the suffix of charges and reused at
every step: subtracting a list of in-range charges off `g` lands at
`g.toNat - (sum of the list)`, **provided the whole sum fits in `g`**. -/

/-- Subtract a list of charges off `g` (each as `UInt64.ofNat`), left to right. -/
def subCharges (g : UInt64) : List ℕ → UInt64
  | []      => g
  | c :: cs => subCharges (g - UInt64.ofNat c) cs

/-- **Gas threading (the composition lemma).** If the total of `cs` fits in `g`
(`cs.sum ≤ g.toNat`) and `g.toNat < 2^64`, then subtracting the charges one by
one lands at `g.toNat - cs.sum`. Proved by induction on `cs`, reusing the
single-charge bridge `toNat_sub_ofNat`. -/
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

set_option maxHeartbeats 16000000 in
theorem messageCall_seq_storageAt (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok ({ success := true, output := .empty }, 5, 11) := by
  unfold messageCall
  dsimp only [paramsSeq]
  unfold beginCall
  dsimp only
  rw [show seedFuel g
        = (((((((seedFuel g - 8) + 1) + 1) + 1) + 1) + 1) + 1) + 2 by
        unfold seedFuel; omega]
  -- A reusable bridge: the running gasAvailable after charges `cs` reads as
  -- `g.toNat - cs.sum` (given the sum fits), letting every step's gas/stipend
  -- side-goal be discharged by `omega` against a fixed prefix sum.
  have gv : GasConstants.Gverylow = 3 := rfl
  -- PUSH1 5  (charge 3)
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 decode_seq_0 (by omega : 3 ≤ g.toNat)
        (by show (0 : ℕ) + 1 ≤ 1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  -- PUSH1 7  (charge 3) — gasAvailable is now g - 3
  rw [drive_step _ _ _ (stepFrame_push1 _ 7 decode_seq_2 (by
        show 3 ≤ (subCharges g [3]).toNat
        rw [toNat_subCharges g [3] (by simp; omega)]; simp; omega) (by
        show (1 : ℕ) + 1 ≤ 1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  simp only [gv]
  -- SSTORE  (charge 22100) — gasAvailable is now g - 3 - 3
  rw [drive_step _ _ _ (stepFrame_sstore _ 7 5 _ decode_seq_4 rfl ?hsz1 rfl ?hstip1 ?hcost1)]
  case hsz1 => show (2 : ℕ) ≤ 1024; omega
  case hstip1 =>
    show ¬ (subCharges g [3, 3]).toNat ≤ Gcallstipend
    rw [toNat_subCharges g [3, 3] (by simp; omega), show Gcallstipend = 2300 from rfl]
    simp; omega
  case hcost1 =>
    show sstoreChargeOf _ 7 5 ≤ (subCharges g [3, 3]).toNat
    rw [toNat_subCharges g [3, 3] (by simp; omega)]
    show (22100 : ℕ) ≤ g.toNat - (3 + (3 + 0)); omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  -- PUSH1 0x0B  (charge 3) — gasAvailable is now g - 3 - 3 - 22100
  rw [drive_step _ _ _ (stepFrame_push1 _ 11 decode_seq_5 (by
        show 3 ≤ (subCharges g [3, 3, 22100]).toNat
        rw [toNat_subCharges g [3, 3, 22100] (by simp; omega)]; simp; omega) (by
        show (0 : ℕ) + 1 ≤ 1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  simp only [gv]
  -- PUSH1 9  (charge 3)
  rw [drive_step _ _ _ (stepFrame_push1 _ 9 decode_seq_7 (by
        show 3 ≤ (subCharges g [3, 3, 22100, 3]).toNat
        rw [toNat_subCharges g [3, 3, 22100, 3] (by simp; omega)]; simp; omega) (by
        show (1 : ℕ) + 1 ≤ 1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]
  simp only [gv]
  -- SSTORE  (charge 22100) — second key, still cold; cost 22100
  rw [drive_step _ _ _ (stepFrame_sstore _ 9 11 _ decode_seq_9 rfl ?hsz2 rfl ?hstip2 ?hcost2)]
  case hsz2 => show (2 : ℕ) ≤ 1024; omega
  case hstip2 =>
    show ¬ (subCharges g [3, 3, 22100, 3, 3]).toNat ≤ Gcallstipend
    rw [toNat_subCharges g [3, 3, 22100, 3, 3] (by simp; omega),
        show Gcallstipend = 2300 from rfl]
    simp; omega
  case hcost2 =>
    show sstoreChargeOf _ 9 11 ≤ (subCharges g [3, 3, 22100, 3, 3]).toNat
    rw [toNat_subCharges g [3, 3, 22100, 3, 3] (by simp; omega)]
    show (22100 : ℕ) ≤ g.toNat - (3 + (3 + (22100 + (3 + (3 + 0))))); omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  -- STOP
  rw [drive_halt _ _ _ (stepFrame_stop _ decode_seq_10 (by show (0 : ℕ) ≤ 1024; omega))]
  rfl

end BytecodeLayer
