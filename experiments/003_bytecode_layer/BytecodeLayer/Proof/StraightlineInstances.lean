import BytecodeLayer.Proof.Straightline
import BytecodeLayer.Proof.CallFree
import BytecodeLayer.Proof.Sequence

/-!
# Proof — the call-free programs as non-branching-block instances

Each call-free program is a one-block instance of `messageCall_straightline`:
supply the explicit `StepsTo` chain (each link a `Step`-lemma fact wrapped by
`stepsTo_of_next`) and the final `STOP` halt; the engine discharges
`messageCall → drive`, the fuel peel, and the whole run. The exported observe-form
theorems (`Spec.lean`) land here, off the same chain — no per-instruction
`drive_step` replay.
-/

namespace BytecodeLayer.Proof
open Evm
open GasConstants

/-! ## STOP — a zero-step block (`steps = []`, halts on the first instruction) -/

/-- `stepFrame` on the `stopProgram` initial frame halts successfully with empty
output. The code/pc come from `codeFrame`/`codeEnv` (`pc = 0`, `code = stopProgram`). -/
theorem stop_halts (p : CallParams) :
    stepFrame (codeFrame p stopProgram)
      = Signal.halted (.success (codeFrame p stopProgram).exec .empty) :=
  stepFrame_stop _ decode_stopProgram (le_of_eq_of_le (by rfl) (Nat.zero_le 1024))

/-- **STOP, at the boundary.** `messageCall p = .ok r` where `r` is the success
result of the `stopProgram` initial frame — through `messageCall_straightline` with
the empty block `[codeFrame p stopProgram]`. -/
theorem messageCall_stop_ok (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    messageCall p
      = .ok (FrameResult.toCallResult
          (endFrame (codeFrame p stopProgram) (.success (codeFrame p stopProgram).exec .empty))) :=
  messageCall_straightline p (codeFrame p stopProgram) (beginCall_code p stopProgram hc)
    [] (codeFrame p stopProgram) rfl (by simp [blockFrames])
    _ (stop_halts p) (by simpa using two_le_seedFuel p.gas)

set_option maxHeartbeats 1000000 in
/-- **STOP, observe-form (re-derivation of `messageCall_stop_observe`).** Reads the
success/empty-output observable off `messageCall_stop_ok` — a one-line instance of
the straight-line engine, replacing the bespoke `drive_step`/`drive_halt` replay. -/
theorem messageCall_stop_observe' (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  rw [messageCall_stop_ok p hc]; rfl

/-! ## PUSH1 5 ; STOP — a one-step block -/

/-- The `pushStopProgram` initial frame after its single `PUSH1 5` (charge 3),
the frame the `STOP` then halts on. -/
def pushStopF1 (p : CallParams) : Frame :=
  { codeFrame p pushStopProgram with
    exec := ({ (codeFrame p pushStopProgram).exec with
                 gasAvailable := (codeFrame p pushStopProgram).exec.gasAvailable - UInt64.ofNat Gverylow
             }).replaceStackAndIncrPC ((codeFrame p pushStopProgram).exec.stack.push 5) (pcΔ := 2) }

set_option maxHeartbeats 1000000 in
theorem messageCall_pushStop_ok (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    messageCall p
      = .ok (FrameResult.toCallResult
          (endFrame (pushStopF1 p) (.success (pushStopF1 p).exec .empty))) := by
  refine messageCall_straightline p (codeFrame p pushStopProgram)
    (beginCall_code p pushStopProgram hc)
    [codeFrame p pushStopProgram] (pushStopF1 p) rfl ?_ _ ?_
      (by show (1:ℕ) + 2 ≤ seedFuel p.gas; unfold seedFuel; omega)
  · -- IsChain across `[codeFrame, pushStopF1]`: the single PUSH1 link.
    rw [show blockFrames [codeFrame p pushStopProgram] (pushStopF1 p)
          = [codeFrame p pushStopProgram, pushStopF1 p] from rfl]
    rw [List.isChain_cons_cons]
    refine ⟨stepsTo_of_next ?_, List.isChain_singleton _⟩
    exact stepFrame_push1 _ 5 decode_pushStop_0 (by simpa using hg) (by show (0:ℕ)+1 ≤ 1024; omega)
  · -- `pushStopF1` halts on STOP.
    refine stepFrame_stop _ ?_ (by show (1:ℕ) ≤ 1024; omega)
    exact decode_pushStop_2

set_option maxHeartbeats 1000000 in
/-- **PUSH1 ; STOP, observe-form (re-derivation of `messageCall_pushStop_observe`).** -/
theorem messageCall_pushStop_observe' (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  rw [messageCall_pushStop_ok p hc hg]; rfl

/-! ## PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP — a three-step block

The first instance with a persistent effect. The chain is
`codeFrame → (push 5) → (push 7) → (sstore) [STOP halts]`; each link a `Step`
lemma wrapped by `stepsTo_of_next`, the gas side-goals threaded with
`toNat_sub_ofNat` exactly as the bespoke proof did — but the fuel/`drive`
plumbing is gone. -/

/-- After `PUSH1 5`. -/
def sstoreF1 (g : UInt64) : Frame :=
  { codeFrame (paramsSStore g) sstoreProgram with
    exec := ({ (codeFrame (paramsSStore g) sstoreProgram).exec with
                 gasAvailable := (codeFrame (paramsSStore g) sstoreProgram).exec.gasAvailable
                   - UInt64.ofNat Gverylow
             }).replaceStackAndIncrPC
               ((codeFrame (paramsSStore g) sstoreProgram).exec.stack.push 5) (pcΔ := 2) }

/-- After `PUSH1 7`. -/
def sstoreF2 (g : UInt64) : Frame :=
  { sstoreF1 g with
    exec := ({ (sstoreF1 g).exec with
                 gasAvailable := (sstoreF1 g).exec.gasAvailable - UInt64.ofNat Gverylow
             }).replaceStackAndIncrPC ((sstoreF1 g).exec.stack.push 7) (pcΔ := 2) }

/-- After `SSTORE` (the frame `STOP` halts on). -/
def sstoreF3 (g : UInt64) : Frame :=
  { sstoreF2 g with
    exec := sstorePost (sstoreF2 g).exec 7 5 (codeFrame (paramsSStore g) sstoreProgram).exec.stack }

set_option maxHeartbeats 8000000 in
theorem messageCall_sstore_ok (g : UInt64) (hg : 22106 ≤ g.toNat) :
    messageCall (paramsSStore g)
      = .ok (FrameResult.toCallResult
          (endFrame (sstoreF3 g) (.success (sstoreF3 g).exec .empty))) := by
  have gv : GasConstants.Gverylow = 3 := rfl
  -- gas at the SSTORE: g - 3 - 3
  have hg2 : (sstoreF2 g).exec.gasAvailable.toNat = g.toNat - 6 := by
    show ((g - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow).toNat = g.toNat - 6
    rw [gv, toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat g 3 (by omega) (by omega)]; omega) (by omega),
        toNat_sub_ofNat g 3 (by omega) (by omega)]
    omega
  refine messageCall_straightline (paramsSStore g) (codeFrame (paramsSStore g) sstoreProgram)
    (beginCall_code (paramsSStore g) sstoreProgram rfl)
    [codeFrame (paramsSStore g) sstoreProgram, sstoreF1 g, sstoreF2 g] (sstoreF3 g)
    rfl ?_ _ ?_ (by show (3:ℕ) + 2 ≤ seedFuel g; unfold seedFuel; omega)
  · -- the three-link chain
    rw [show blockFrames [codeFrame (paramsSStore g) sstoreProgram, sstoreF1 g, sstoreF2 g] (sstoreF3 g)
          = [codeFrame (paramsSStore g) sstoreProgram, sstoreF1 g, sstoreF2 g, sstoreF3 g] from rfl]
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨stepsTo_of_next ?_, stepsTo_of_next ?_, stepsTo_of_next ?_, List.isChain_singleton _⟩
    · -- PUSH1 5
      exact stepFrame_push1 _ 5 decode_sstore_0 (by omega : 3 ≤ g.toNat)
        (by show (0:ℕ)+1 ≤ 1024; omega)
    · -- PUSH1 7, gas now g - 3
      refine stepFrame_push1 _ 7 ?_ ?_ (by show (1:ℕ)+1 ≤ 1024; omega)
      · exact decode_sstore_2
      · show 3 ≤ ((codeFrame (paramsSStore g) sstoreProgram).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
        rw [gv]
        show 3 ≤ (g - UInt64.ofNat 3).toNat
        rw [toNat_sub_ofNat g 3 (by omega) (by omega)]; omega
    · -- SSTORE, gas now g - 3 - 3
      refine stepFrame_sstore _ 7 5 _ decode_sstore_4 rfl ?_ rfl ?_ ?_
      · show (2:ℕ) ≤ 1024; omega
      · show ¬ (sstoreF2 g).exec.gasAvailable.toNat ≤ Gcallstipend
        rw [hg2, show Gcallstipend = 2300 from rfl]; omega
      · show sstoreChargeOf (sstoreF2 g).exec 7 5 ≤ (sstoreF2 g).exec.gasAvailable.toNat
        rw [hg2]; show (22100:ℕ) ≤ g.toNat - 6; omega
  · -- STOP at pc 5
    refine stepFrame_stop _ ?_ (by show (0:ℕ) ≤ 1024; omega)
    exact decode_sstore_5

set_option maxHeartbeats 8000000 in
/-- **SSTORE, observe + storage form (re-derivation of `messageCall_sstore_storageAt`).** -/
theorem messageCall_sstore_storageAt' (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok ({ success := true, output := .empty }, 5) := by
  rw [messageCall_sstore_ok g hg]; rfl

/-! ## PUSH;PUSH;SSTORE;PUSH;PUSH;SSTORE;STOP — a six-step block (two cold writes) -/

/-- The seq frames, named after the instruction that produced each. The push
charges (3) and store charges (22100) thread `g` through `subCharges`. -/
def seqF (g : UInt64) : Frame := codeFrame (paramsSeq g) seqProgram
def seqF1 (g : UInt64) : Frame :=
  { seqF g with exec := ({ (seqF g).exec with gasAvailable := (seqF g).exec.gasAvailable - UInt64.ofNat Gverylow }).replaceStackAndIncrPC ((seqF g).exec.stack.push 5) (pcΔ := 2) }
def seqF2 (g : UInt64) : Frame :=
  { seqF1 g with exec := ({ (seqF1 g).exec with gasAvailable := (seqF1 g).exec.gasAvailable - UInt64.ofNat Gverylow }).replaceStackAndIncrPC ((seqF1 g).exec.stack.push 7) (pcΔ := 2) }
def seqF3 (g : UInt64) : Frame :=
  { seqF2 g with exec := sstorePost (seqF2 g).exec 7 5 (seqF g).exec.stack }
def seqF4 (g : UInt64) : Frame :=
  { seqF3 g with exec := ({ (seqF3 g).exec with gasAvailable := (seqF3 g).exec.gasAvailable - UInt64.ofNat Gverylow }).replaceStackAndIncrPC ((seqF3 g).exec.stack.push 11) (pcΔ := 2) }
def seqF5 (g : UInt64) : Frame :=
  { seqF4 g with exec := ({ (seqF4 g).exec with gasAvailable := (seqF4 g).exec.gasAvailable - UInt64.ofNat Gverylow }).replaceStackAndIncrPC ((seqF4 g).exec.stack.push 9) (pcΔ := 2) }
def seqF6 (g : UInt64) : Frame :=
  { seqF5 g with exec := sstorePost (seqF5 g).exec 9 11 (seqF g).exec.stack }

set_option maxHeartbeats 16000000 in
theorem messageCall_seq_ok (g : UInt64) (hg : 44212 ≤ g.toNat) :
    messageCall (paramsSeq g)
      = .ok (FrameResult.toCallResult
          (endFrame (seqF6 g) (.success (seqF6 g).exec .empty))) := by
  have gv : GasConstants.Gverylow = 3 := rfl
  -- running gas balances via subCharges
  have e1 : (seqF1 g).exec.gasAvailable = subCharges g [3] := by
    show (g - UInt64.ofNat Gverylow) = _; rw [gv]; rfl
  have e2 : (seqF2 g).exec.gasAvailable = subCharges g [3, 3] := by
    show ((seqF1 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [e1, gv]; rfl
  have hcost75 : sstoreChargeOf (seqF2 g).exec 7 5 = 22100 := rfl
  have e3 : (seqF3 g).exec.gasAvailable = subCharges g [3, 3, 22100] := by
    show (sstorePost (seqF2 g).exec 7 5 (seqF g).exec.stack).gasAvailable = _
    rw [show (sstorePost (seqF2 g).exec 7 5 (seqF g).exec.stack).gasAvailable
          = (seqF2 g).exec.gasAvailable - UInt64.ofNat (sstoreChargeOf (seqF2 g).exec 7 5) from rfl]
    rw [e2, hcost75]; rfl
  have e4 : (seqF4 g).exec.gasAvailable = subCharges g [3, 3, 22100, 3] := by
    show ((seqF3 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [e3, gv]; rfl
  have e5 : (seqF5 g).exec.gasAvailable = subCharges g [3, 3, 22100, 3, 3] := by
    show ((seqF4 g).exec.gasAvailable - UInt64.ofNat Gverylow) = _; rw [e4, gv]; rfl
  refine messageCall_straightline (paramsSeq g) (codeFrame (paramsSeq g) seqProgram)
    (beginCall_code (paramsSeq g) seqProgram rfl)
    [seqF g, seqF1 g, seqF2 g, seqF3 g, seqF4 g, seqF5 g] (seqF6 g)
    rfl ?_ _ ?_ (by show (6:ℕ) + 2 ≤ seedFuel g; unfold seedFuel; omega)
  · rw [show blockFrames [seqF g, seqF1 g, seqF2 g, seqF3 g, seqF4 g, seqF5 g] (seqF6 g)
          = [seqF g, seqF1 g, seqF2 g, seqF3 g, seqF4 g, seqF5 g, seqF6 g] from rfl]
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons,
        List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨stepsTo_of_next ?_, stepsTo_of_next ?_, stepsTo_of_next ?_, stepsTo_of_next ?_,
            stepsTo_of_next ?_, stepsTo_of_next ?_, List.isChain_singleton _⟩
    · exact stepFrame_push1 _ 5 decode_seq_0 (by omega : 3 ≤ g.toNat) (by show (0:ℕ)+1 ≤ 1024; omega)
    · refine stepFrame_push1 _ 7 decode_seq_2 ?_ (by show (1:ℕ)+1 ≤ 1024; omega)
      rw [show (seqF1 g).exec.gasAvailable = _ from e1, toNat_subCharges g [3] (by simp; omega)]; simp; omega
    · refine stepFrame_sstore _ 7 5 _ decode_seq_4 rfl (by show (2:ℕ) ≤ 1024; omega) rfl ?_ ?_
      · show ¬ (seqF2 g).exec.gasAvailable.toNat ≤ Gcallstipend
        rw [e2, toNat_subCharges g [3, 3] (by simp; omega), show Gcallstipend = 2300 from rfl]; simp; omega
      · show sstoreChargeOf (seqF2 g).exec 7 5 ≤ (seqF2 g).exec.gasAvailable.toNat
        rw [hcost75, e2, toNat_subCharges g [3, 3] (by simp; omega)]
        show (22100:ℕ) ≤ g.toNat - (3 + (3 + 0)); omega
    · refine stepFrame_push1 _ 11 decode_seq_5 ?_ (by show (0:ℕ)+1 ≤ 1024; omega)
      rw [e3, toNat_subCharges g [3, 3, 22100] (by simp; omega)]; simp; omega
    · refine stepFrame_push1 _ 9 decode_seq_7 ?_ (by show (1:ℕ)+1 ≤ 1024; omega)
      rw [e4, toNat_subCharges g [3, 3, 22100, 3] (by simp; omega)]; simp; omega
    · refine stepFrame_sstore _ 9 11 _ decode_seq_9 rfl (by show (2:ℕ) ≤ 1024; omega) rfl ?_ ?_
      · show ¬ (seqF5 g).exec.gasAvailable.toNat ≤ Gcallstipend
        rw [e5, toNat_subCharges g [3, 3, 22100, 3, 3] (by simp; omega), show Gcallstipend = 2300 from rfl]
        simp; omega
      · show sstoreChargeOf (seqF5 g).exec 9 11 ≤ (seqF5 g).exec.gasAvailable.toNat
        rw [show sstoreChargeOf (seqF5 g).exec 9 11 = 22100 from rfl,
            e5, toNat_subCharges g [3, 3, 22100, 3, 3] (by simp; omega)]
        show (22100:ℕ) ≤ g.toNat - (3 + (3 + (22100 + (3 + (3 + 0))))); omega
  · refine stepFrame_stop _ decode_seq_10 (by show (0:ℕ) ≤ 1024; omega)

set_option maxHeartbeats 16000000 in
/-- **Seq, observe + two storage cells (re-derivation of `messageCall_seq_storageAt`).** -/
theorem messageCall_seq_storageAt' (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok ({ success := true, output := .empty }, 5, 11) := by
  rw [messageCall_seq_ok g hg]; rfl

/-! ## PUSH1 0 ; PUSH1 0 ; RETURN — a two-step block with a return-data observable

The first instance whose terminal instruction is `RETURN` (not `STOP`): the block
halts with `.success` carrying the empty output, landing on the general
`completedReturning` rung. Uses the new `stepFrame_return_empty` brick. -/

/-- The bytes a zero-size `RETURN` returns: `readWithPadding _ 0 0` off an empty
memory. Semantically a zero-length array, but it goes through the opaque
`ffi.ByteArray.zeroes ⟨0⟩` (an `@[extern]` memset), so we name the exact returned
value rather than claim a syntactic `ByteArray.empty`. This is the program's
return-data observable. -/
def returnOut : ByteArray := (default : ByteArray).readWithPadding (0:UInt256).toNat (0:UInt256).toNat

theorem decode_return_0 :
    decode returnProgram 0 = some (.Push .PUSH1, some (0, 1)) := by rfl
theorem decode_return_2 :
    decode returnProgram ((0 : UInt32) + UInt8.toUInt32 2) = some (.Push .PUSH1, some (0, 1)) := by rfl
theorem decode_return_4 :
    decode returnProgram (((0 : UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
      = some (.System .RETURN, .none) := by rfl

/-- After the first `PUSH1 0`. -/
def returnF1 (p : CallParams) : Frame :=
  { codeFrame p returnProgram with
    exec := ({ (codeFrame p returnProgram).exec with
                 gasAvailable := (codeFrame p returnProgram).exec.gasAvailable - UInt64.ofNat Gverylow
             }).replaceStackAndIncrPC ((codeFrame p returnProgram).exec.stack.push 0) (pcΔ := 2) }
/-- After the second `PUSH1 0` (the frame `RETURN` halts on). -/
def returnF2 (p : CallParams) : Frame :=
  { returnF1 p with
    exec := ({ (returnF1 p).exec with gasAvailable := (returnF1 p).exec.gasAvailable - UInt64.ofNat Gverylow
             }).replaceStackAndIncrPC ((returnF1 p).exec.stack.push 0) (pcΔ := 2) }

set_option maxHeartbeats 2000000 in
/-- **RETURN, at the boundary.** `messageCall p = .ok r` for `r` the success result
of the `returnProgram` block — through `messageCall_straightline`. -/
theorem messageCall_return_ok (p : CallParams)
    (hc : p.codeSource = .Code returnProgram) (hg : 6 ≤ p.gas.toNat) :
    messageCall p
      = .ok (FrameResult.toCallResult
          (endFrame (returnF2 p)
            (.success (returnEmptyPost (returnF2 p).exec (codeFrame p returnProgram).exec.stack)
                      ((returnF2 p).exec.memory.readWithPadding (0:UInt256).toNat (0:UInt256).toNat)))) := by
  have gv : GasConstants.Gverylow = 3 := rfl
  refine messageCall_straightline p (codeFrame p returnProgram) (beginCall_code p returnProgram hc)
    [codeFrame p returnProgram, returnF1 p] (returnF2 p) rfl ?_ _ ?_
      (by show (2:ℕ) + 2 ≤ seedFuel p.gas; unfold seedFuel; omega)
  · rw [show blockFrames [codeFrame p returnProgram, returnF1 p] (returnF2 p)
          = [codeFrame p returnProgram, returnF1 p, returnF2 p] from rfl]
    rw [List.isChain_cons_cons, List.isChain_cons_cons]
    refine ⟨stepsTo_of_next ?_, stepsTo_of_next ?_, List.isChain_singleton _⟩
    · exact stepFrame_push1 _ 0 decode_return_0 (by omega : 3 ≤ p.gas.toNat) (by show (0:ℕ)+1 ≤ 1024; omega)
    · refine stepFrame_push1 _ 0 decode_return_2 ?_ (by show (1:ℕ)+1 ≤ 1024; omega)
      show 3 ≤ ((codeFrame p returnProgram).exec.gasAvailable - UInt64.ofNat Gverylow).toNat
      rw [gv]; show 3 ≤ (p.gas - UInt64.ofNat 3).toNat
      rw [toNat_sub_ofNat p.gas 3 (by omega) (by omega)]; omega
  · exact stepFrame_return_empty _ _ decode_return_4 rfl (by show (2:ℕ) ≤ 1024; omega)

end BytecodeLayer.Proof
