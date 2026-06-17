import BytecodeLayer.Reasoning.Hoare
import BytecodeLayer.Proof.Straightline
import BytecodeLayer.Semantics.UInt256
import BytecodeLayer.Semantics.Decode
import BytecodeLayer.Proof.Sequence

/-!
# Proof — worked example programs as compositions of opcode rules

These are end-to-end `messageCall` observations for concrete straight-line
programs (`stopProgram`, `pushStopProgram`, `sstoreProgram`, and an SSTORE
sequence) — the live worked examples behind the `Spec.lean` capstones. They are
demonstrations of the reasoning layer, not part of the never-out-of-fuel work.

Each program is proven by **composing the Hoare-core opcode rules**
(`runs_push1`, `runs_sstore`) with the sequencing rule `Runs.trans`, then crossing
the `messageCall` boundary with `messageCall_runs`. No execution trace is named:
the intermediate frames live inside the `Runs` derivation, and the stored values
are *derived* as the operands of `runs_sstore`, never asserted as literal frames.

The four exported observe-form theorems (`Spec.lean` delegates to these `*'`
lemmas) land here, off the composed `Runs`. The fuel obligation is the numeric
`n + 2 ≤ seedFuel`; the per-step gas side-goals thread `g` through
`toNat_sub_ofNat` / `subCharges` (`toNat_subCharges`) exactly as before, but the
`drive`/fuel plumbing is gone — it is discharged once in `messageCall_runs`.
-/

namespace BytecodeLayer.Proof
open Evm
open GasConstants
open BytecodeLayer.UInt256
open BytecodeLayer.Decode
open BytecodeLayer.Dispatch

set_option maxRecDepth 4000

/-! ## STOP — a zero-step block (halts on the first instruction) -/

set_option maxHeartbeats 1000000 in
/-- **STOP, observe-form.** `stopProgram` halts immediately: `Runs 0` (`Runs.refl`
on the initial code frame), crossed by `messageCall_runs` with `n = 0`, the halt
supplied by `stepFrame_stop`. -/
theorem messageCall_stop_observe' (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  rw [messageCall_runs p (codeFrame p stopProgram) (codeFrame p stopProgram)
        (beginCall_code p stopProgram hc)
        (Runs.refl _)
        (.success (codeFrame p stopProgram).exec .empty)
        (stepFrame_stop _ decode_stopProgram (by show (0:ℕ) ≤ 1024; omega))
        (by show (0:ℕ) + 2 ≤ seedFuel p.gas; unfold seedFuel; omega)]
  rfl

/-! ## PUSH1 5 ; STOP — a one-step block (`runs_push1` then halt) -/

set_option maxHeartbeats 1000000 in
/-- **PUSH1 ; STOP, observe-form.** One `runs_push1` (the `Runs 1` block), then the
`STOP` halt; `n = 1` at the boundary. -/
theorem messageCall_pushStop_observe' (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  have hg0 : (codeFrame p pushStopProgram).exec.gasAvailable.toNat = p.gas.toNat := rfl
  rw [messageCall_runs p (codeFrame p pushStopProgram) (pushFrame (codeFrame p pushStopProgram) 5)
        (beginCall_code p pushStopProgram hc)
        (runs_push1 (codeFrame p pushStopProgram) 5 decode_pushStop_0
          (by rw [hg0]; omega) (by show (0:ℕ) + 1 ≤ 1024; omega))
        (.success (pushFrame (codeFrame p pushStopProgram) 5).exec .empty)
        (stepFrame_stop _ decode_pushStop_2 (by show (1:ℕ) ≤ 1024; omega))
        (by show (1:ℕ) + 2 ≤ seedFuel p.gas; unfold seedFuel; omega)]
  rfl

/-! ## PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP — a three-step block (one cold write)

`runs_push1 5 ∘ runs_push1 7 ∘ runs_sstore`, glued by `Runs.trans`; `n = 3`. The
stored value `5` is the `newValue` operand of `runs_sstore`, derived through the
SSTORE effect projection, never written as a frame literal. -/

/-- The self account present in the `paramsSStore` world (`addrA`). -/
private def sstoreSelfAcc (g : UInt64) : Account :=
  (codeFrame (paramsSStore g) sstoreProgram).exec.accounts.find! addrA

private theorem sstore_self_present (g : UInt64) :
    (codeFrame (paramsSStore g) sstoreProgram).exec.accounts.find?
        (codeFrame (paramsSStore g) sstoreProgram).exec.executionEnv.address
      = some (sstoreSelfAcc g) := by rfl

set_option maxHeartbeats 4000000 in
/-- The composed `Runs 3` for `sstoreProgram`: push 5, push 7, sstore. -/
private theorem sstore_runs (g : UInt64) (hg : 22106 ≤ g.toNat) :
    Runs 3 (codeFrame (paramsSStore g) sstoreProgram)
      (sstoreFrame (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
        (codeFrame (paramsSStore g) sstoreProgram).exec.stack) := by
  have gv : GasConstants.Gverylow = 3 := rfl
  have hg0 : (codeFrame (paramsSStore g) sstoreProgram).exec.gasAvailable.toNat = g.toNat := rfl
  have hg1 : ((codeFrame (paramsSStore g) sstoreProgram).exec.gasAvailable
        - UInt64.ofNat Gverylow).toNat = g.toNat - 3 := by
    rw [gv]; show (g - UInt64.ofNat 3).toNat = g.toNat - 3
    rw [toNat_sub_ofNat g 3 (by omega) (by omega)]
  have hg2 : ((pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5).exec.gasAvailable
        - UInt64.ofNat Gverylow).toNat = g.toNat - 6 := by
    show (((codeFrame (paramsSStore g) sstoreProgram).exec.gasAvailable - UInt64.ofNat Gverylow)
        - UInt64.ofNat Gverylow).toNat = g.toNat - 6
    rw [gv, toNat_sub_ofNat _ 3 (by rw [show GasConstants.Gverylow = 3 from rfl] at hg1; omega) (by omega)]
    rw [show GasConstants.Gverylow = 3 from rfl] at hg1; omega
  refine Runs.trans (runs_push1 (codeFrame (paramsSStore g) sstoreProgram) 5 decode_sstore_0
      (by rw [hg0]; omega) (by show (0:ℕ)+1 ≤ 1024; omega))
    (Runs.trans (runs_push1 (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7 decode_sstore_2
        ?_ (by show (1:ℕ)+1 ≤ 1024; omega))
      (runs_sstore (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
        (codeFrame (paramsSStore g) sstoreProgram).exec.stack
        decode_sstore_4 rfl (by show (2:ℕ) ≤ 1024; omega) rfl ?_ ?_))
  · show 3 ≤ ((codeFrame (paramsSStore g) sstoreProgram).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
    rw [hg1]; omega
  · show ¬ ((pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5).exec.gasAvailable
        - UInt64.ofNat Gverylow).toNat ≤ Gcallstipend
    rw [hg2, show Gcallstipend = 2300 from rfl]; omega
  · rw [show sstoreChargeOf (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7).exec 7 5
          = 22100 from rfl]
    show (22100:ℕ) ≤ ((pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5).exec.gasAvailable
        - UInt64.ofNat Gverylow).toNat
    rw [hg2]; omega

set_option maxHeartbeats 4000000 in
/-- `messageCall` of `sstoreProgram` equals the success result of the composed run's
final frame, via `messageCall_runs` (`n = 3`). -/
private theorem sstore_messageCall (g : UInt64) (hg : 22106 ≤ g.toNat) :
    messageCall (paramsSStore g)
      = .ok (FrameResult.toCallResult (endFrame
          (sstoreFrame (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
            (codeFrame (paramsSStore g) sstoreProgram).exec.stack)
          (.success
            (sstoreFrame (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
              (codeFrame (paramsSStore g) sstoreProgram).exec.stack).exec .empty))) :=
  messageCall_runs (paramsSStore g) (codeFrame (paramsSStore g) sstoreProgram) _
    (beginCall_code (paramsSStore g) sstoreProgram rfl)
    (sstore_runs g hg) _
    (stepFrame_stop _ decode_sstore_5 (by show (0:ℕ) ≤ 1024; omega))
    (by show (3:ℕ) + 2 ≤ seedFuel g; unfold seedFuel; omega)

set_option maxHeartbeats 4000000 in
/-- **SSTORE, observe + storage form.** Reads the success/empty observable and the
*derived* `5` at cell `(addrA, 7)` off the composed run — the value enters as the
`runs_sstore` operand, never as a frame literal. -/
theorem messageCall_sstore_storageAt' (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok ({ success := true, output := .empty }, 5) := by
  have hcell : ((sstoreFrame (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
      (codeFrame (paramsSStore g) sstoreProgram).exec.stack).exec.accounts.find?
        addrA |>.option 0 (·.lookupStorage 7)) = 5 :=
    sstoreFrame_storage_self (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
      (codeFrame (paramsSStore g) sstoreProgram).exec.stack (sstoreSelfAcc g)
      (sstore_self_present g) (by decide)
  rw [sstore_messageCall g hg]
  show Except.ok (_, ((sstoreFrame (pushFrame (pushFrame (codeFrame (paramsSStore g) sstoreProgram) 5) 7) 7 5
      (codeFrame (paramsSStore g) sstoreProgram).exec.stack).exec.accounts.find?
        addrA |>.option 0 (·.lookupStorage 7))) = _
  rw [hcell]; rfl

/-! ## PUSH;PUSH;SSTORE;PUSH;PUSH;SSTORE;STOP — a six-step block (two cold writes)

`runs_push1 5 ∘ runs_push1 7 ∘ runs_sstore 7 5 ∘ runs_push1 11 ∘ runs_push1 9 ∘
runs_sstore 9 11`, glued by `Runs.trans`; `n = 6`. The running-gas side-goals (a
prefix sum of charges against `gasAvailable`) thread through `subCharges` /
`toNat_subCharges`. Both stored values are derived as `runs_sstore` operands. -/

/-- The composed post-frames named by the rule transformers, layered. `sq0` is the
initial frame; each `sq*` is the previous frame after one opcode rule. -/
private def sq0 (g : UInt64) : Frame := codeFrame (paramsSeq g) seqProgram
private def sq1 (g : UInt64) : Frame := pushFrame (sq0 g) 5
private def sq2 (g : UInt64) : Frame := pushFrame (sq1 g) 7
private def sq3 (g : UInt64) : Frame := sstoreFrame (sq2 g) 7 5 (sq0 g).exec.stack
private def sq4 (g : UInt64) : Frame := pushFrame (sq3 g) 11
private def sq5 (g : UInt64) : Frame := pushFrame (sq4 g) 9
private def sq6 (g : UInt64) : Frame := sstoreFrame (sq5 g) 9 11 (sq0 g).exec.stack

private theorem seq_self_present (g : UInt64) :
    (sq0 g).exec.accounts.find? (sq0 g).exec.executionEnv.address = some ((sq0 g).exec.accounts.find! addrA) := by
  rfl

set_option maxHeartbeats 16000000 in
/-- The composed `Runs 6` for `seqProgram`. -/
private theorem seq_runs (g : UInt64) (hg : 44212 ≤ g.toNat) : Runs 6 (sq0 g) (sq6 g) := by
  have gv : GasConstants.Gverylow = 3 := rfl
  -- running gas balances via `subCharges`
  have e1 : (sq1 g).exec.gasAvailable = subCharges g [3] := by
    show ((sq0 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [gv]; rfl
  have e2 : (sq2 g).exec.gasAvailable = subCharges g [3, 3] := by
    show ((sq1 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [e1, gv]; rfl
  have hcost75 : sstoreChargeOf (sq2 g).exec 7 5 = 22100 := rfl
  have e3 : (sq3 g).exec.gasAvailable = subCharges g [3, 3, 22100] := by
    show (sstorePost (sq2 g).exec 7 5 (sq0 g).exec.stack).gasAvailable = _
    rw [show (sstorePost (sq2 g).exec 7 5 (sq0 g).exec.stack).gasAvailable
          = (sq2 g).exec.gasAvailable - UInt64.ofNat (sstoreChargeOf (sq2 g).exec 7 5) from rfl]
    rw [e2, hcost75]; rfl
  have e4 : (sq4 g).exec.gasAvailable = subCharges g [3, 3, 22100, 3] := by
    show ((sq3 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [e3, gv]; rfl
  have e5 : (sq5 g).exec.gasAvailable = subCharges g [3, 3, 22100, 3, 3] := by
    show ((sq4 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [e4, gv]; rfl
  have hg0 : (sq0 g).exec.gasAvailable.toNat = g.toNat := rfl
  -- 6 = 1 + (1 + (1 + (1 + (1 + 1))))
  refine Runs.trans (runs_push1 (sq0 g) 5 decode_seq_0 (by rw [hg0]; omega) (by show (0:ℕ)+1 ≤ 1024; omega))
    (Runs.trans (runs_push1 (sq1 g) 7 decode_seq_2 ?_ (by show (1:ℕ)+1 ≤ 1024; omega))
      (Runs.trans (runs_sstore (sq2 g) 7 5 (sq0 g).exec.stack decode_seq_4 rfl
          (by show (2:ℕ) ≤ 1024; omega) rfl ?_ ?_)
        (Runs.trans (runs_push1 (sq3 g) 11 decode_seq_5 ?_ (by show (0:ℕ)+1 ≤ 1024; omega))
          (Runs.trans (runs_push1 (sq4 g) 9 decode_seq_7 ?_ (by show (1:ℕ)+1 ≤ 1024; omega))
            (runs_sstore (sq5 g) 9 11 (sq0 g).exec.stack decode_seq_9 rfl
              (by show (2:ℕ) ≤ 1024; omega) rfl ?_ ?_)))))
  · -- gas ≥ 3 after push 5
    show 3 ≤ (sq1 g).exec.gasAvailable.toNat
    rw [e1, toNat_subCharges g [3] (by simp; omega)]; simp; omega
  · -- stipend gate before first sstore
    show ¬ (sq2 g).exec.gasAvailable.toNat ≤ Gcallstipend
    rw [e2, toNat_subCharges g [3, 3] (by simp; omega), show Gcallstipend = 2300 from rfl]; simp; omega
  · -- first store cost ≤ remaining gas
    show sstoreChargeOf (sq2 g).exec 7 5 ≤ (sq2 g).exec.gasAvailable.toNat
    rw [hcost75, e2, toNat_subCharges g [3, 3] (by simp; omega)]
    show (22100:ℕ) ≤ g.toNat - (3 + (3 + 0)); omega
  · -- gas ≥ 3 after first sstore
    show 3 ≤ (sq3 g).exec.gasAvailable.toNat
    rw [e3, toNat_subCharges g [3, 3, 22100] (by simp; omega)]; simp; omega
  · -- gas ≥ 3 after push 11
    show 3 ≤ (sq4 g).exec.gasAvailable.toNat
    rw [e4, toNat_subCharges g [3, 3, 22100, 3] (by simp; omega)]; simp; omega
  · -- stipend gate before second sstore
    show ¬ (sq5 g).exec.gasAvailable.toNat ≤ Gcallstipend
    rw [e5, toNat_subCharges g [3, 3, 22100, 3, 3] (by simp; omega), show Gcallstipend = 2300 from rfl]
    simp; omega
  · -- second store cost ≤ remaining gas
    show sstoreChargeOf (sq5 g).exec 9 11 ≤ (sq5 g).exec.gasAvailable.toNat
    rw [show sstoreChargeOf (sq5 g).exec 9 11 = 22100 from rfl,
        e5, toNat_subCharges g [3, 3, 22100, 3, 3] (by simp; omega)]
    show (22100:ℕ) ≤ g.toNat - (3 + (3 + (22100 + (3 + (3 + 0))))); omega

set_option maxHeartbeats 16000000 in
private theorem seq_messageCall (g : UInt64) (hg : 44212 ≤ g.toNat) :
    messageCall (paramsSeq g)
      = .ok (FrameResult.toCallResult (endFrame (sq6 g)
          (.success (sq6 g).exec .empty))) :=
  messageCall_runs (paramsSeq g) (sq0 g) _
    (beginCall_code (paramsSeq g) seqProgram rfl)
    (seq_runs g hg) _
    (stepFrame_stop _ decode_seq_10 (by show (0:ℕ) ≤ 1024; omega))
    (by show (6:ℕ) + 2 ≤ seedFuel g; unfold seedFuel; omega)

set_option maxHeartbeats 16000000 in
/-- **Seq, observe + two storage cells.** Reads the success observable and the two
*derived* cells `(addrA, 7) ↦ 5`, `(addrA, 9) ↦ 11` off the composed run. The
second `SSTORE`'s framing leaves cell `7` intact (slot `9 ≠ 7`). -/
theorem messageCall_seq_storageAt' (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok ({ success := true, output := .empty }, 5, 11) := by
  have hself5 : (sq5 g).exec.accounts.find? (sq5 g).exec.executionEnv.address
      = some ((sq3 g).exec.accounts.find! addrA) := by rfl
  -- cell 9: the second sstore's effect (derived value 11)
  have hcell9 : ((sq6 g).exec.accounts.find? addrA |>.option 0 (·.lookupStorage 9)) = 11 :=
    sstoreFrame_storage_self (sq5 g) 9 11 (sq0 g).exec.stack
      ((sq3 g).exec.accounts.find! addrA) hself5 (by decide)
  -- cell 7: the second sstore frames it (slot 9 ≠ 7), reducing to the first sstore's effect
  have hframe7 :
      ((sq6 g).exec.accounts.find? addrA |>.option 0 (·.lookupStorage 7))
        = ((sq5 g).exec.accounts.find? addrA |>.option 0 (·.lookupStorage 7)) :=
    sstoreFrame_storage_frame (sq5 g) 9 11 (sq0 g).exec.stack
      ((sq3 g).exec.accounts.find! addrA) hself5 (by decide) addrA 7 (Or.inr (by decide))
  have hcell7' : ((sq5 g).exec.accounts.find? addrA |>.option 0 (·.lookupStorage 7)) = 5 :=
    sstoreFrame_storage_self (sq2 g) 7 5 (sq0 g).exec.stack
      ((sq0 g).exec.accounts.find! addrA) (by rfl) (by decide)
  rw [seq_messageCall g hg]
  show Except.ok (_,
      ((sq6 g).exec.accounts.find? addrA |>.option 0 (·.lookupStorage 7)),
      ((sq6 g).exec.accounts.find? addrA |>.option 0 (·.lookupStorage 9))) = _
  rw [hcell9, hframe7, hcell7']; rfl

end BytecodeLayer.Proof
