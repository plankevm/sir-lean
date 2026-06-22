import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.ExternalCall
import BytecodeLayer.Semantics.UInt64

/-!
# Worked instantiation of the general external-CALL rule on `callerProg`/`calleeProg`

This file *exercises* `messageCall_call_runs` (`Spec.lean`) end-to-end on the real
caller/callee programs of `Programs.lean`, proving the concrete external-call
storage result — the callee's cell `(addrCallee, 7) = 5` above the gas floor —
**compositionally**, the way a user verifies their own bytecode:

* the prefix `Runs n₁ fr₀ callFr`: the seven CALL-arg pushes glued by `Runs.trans`,
  five via `runs_push1` (PUSH1) and two via the general `runs_push` (PUSH3, PUSH4),
  reusing the `ExternalCall` decode facts `dc*`;
* `hcall`: the CALL step (`stepFrame_call` through the `ExternalCall` machinery)
  producing the `.needsCall` signal and the child params/pending;
* `hchild`: the genuine child run, the reflexive callee `PUSH;PUSH;SSTORE;STOP`,
  driven to its `FrameResult` over the *empty* pending stack;
* the suffix `Runs n₂ … last` to the caller's `STOP`, with `hhalt`;
* `hfuel`: the numeric fuel bound, discharged by `omega` off `childGas_ub`/`seedFuel`.

This derivation never names the full execution trace: each piece is an
independent lemma, composed by the general rule. It both demonstrates the
intended user workflow and ensures `messageCall_call_runs` is a live, exercised
theorem; the concrete `∃G₀` spec `Examples.messageCall_call_storageAt` is now
obtained from this compositional result (no monolithic opcode chain remains).
-/

namespace BytecodeLayer.Examples
open Evm Operation GasConstants
open BytecodeLayer
open BytecodeLayer.UInt64
open BytecodeLayer.Dispatch
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.ExternalCall

set_option maxRecDepth 4000

/-! ## Gas bookkeeping -/

/-- **Upper bound on the forwarded child gas.** The 63/64 cap forwards at most
`g.toNat - 21 - 2600` to the child (`21` for the seven pushes, `2600` the call
extra cost), so `childGas g + 4 ≤ g.toNat` whenever `g ≥ 30000` — exactly the slack
the fuel side-condition of `messageCall_call_runs` needs. -/
private theorem childGas_le_caller (g : UInt64) (hg : 30000 ≤ g.toNat) :
    childGas g + 4 ≤ g.toNat := by
  unfold childGas callGasCap
  rw [show callExtraCost (AccountAddress.ofUInt256 13242862) (AccountAddress.ofUInt256 13242862) 0
        callerXfer default = 2600 from by decide]
  rw [show (g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
        - UInt64.ofNat 3 - UInt64.ofNat 3) = subCharges g [3,3,3,3,3,3,3] from by simp [subCharges]]
  rw [toNat_subCharges g [3,3,3,3,3,3,3] (by simp; omega)]
  split
  · -- the `if_pos` branch: cap is `min (allButOneSixtyFourth …) 4294967295`
    apply le_trans (Nat.add_le_add_right (min_le_left _ _) 4)
    unfold allButOneSixtyFourth
    simp only [List.sum_cons, List.sum_nil]; omega
  · -- the `if_neg` branch is vacuous: for `g ≥ 30000`, `g.toNat - 21 ≥ 2600`
    next hguard =>
      exfalso; apply hguard
      simp only [List.sum_cons, List.sum_nil]; omega

/-! ## The prefix `Runs`: the seven CALL-arg pushes -/

/-- **The prefix run.** From the caller's entry frame, the seven CALL-arg pushes
`Runs 7` to `callerCalled g` (the frame at the CALL byte with the seven args on the
stack). Five `runs_push1` and two `runs_push` (PUSH3, PUSH4), glued by `Runs.trans`;
the running gas threads through `subCharges`. The terminal frame is *defeq* to
`callerCalled g`. -/
private theorem caller_prefix_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    Runs 7 (callerFrame g) (callerCalled g) := by
  -- post-frames of each push, layered (each defeq to the previous after one push)
  have hg0 : (callerFrame g).exec.gasAvailable.toNat = g.toNat := rfl
  -- gas balances after each push
  refine Runs.trans (runs_push1 (callerFrame g) 0 dc0 (by rw [hg0]; omega) (by show (0:ℕ)+1≤1024; omega))
    (Runs.trans (runs_push1 _ 0 dc2 (by
        show 3 ≤ (subCharges g [3]).toNat; rw [toNat_subCharges g [3] (by simp;omega)]; simp; omega)
        (by show (1:ℕ)+1≤1024; omega))
      (Runs.trans (runs_push1 _ 0 dc4 (by
          show 3 ≤ (subCharges g [3,3]).toNat; rw [toNat_subCharges g [3,3] (by simp;omega)]; simp; omega)
          (by show (2:ℕ)+1≤1024; omega))
        (Runs.trans (runs_push1 _ 0 dc6 (by
            show 3 ≤ (subCharges g [3,3,3]).toNat; rw [toNat_subCharges g [3,3,3] (by simp;omega)]; simp; omega)
            (by show (3:ℕ)+1≤1024; omega))
          (Runs.trans (runs_push1 _ 0 dc8 (by
              show 3 ≤ (subCharges g [3,3,3,3]).toNat
              rw [toNat_subCharges g [3,3,3,3] (by simp;omega)]; simp; omega)
              (by show (4:ℕ)+1≤1024; omega))
            (Runs.trans (runs_push _ .PUSH3 0xCA11EE 3 (by nofun) dc10 rfl rfl (by
                show 3 ≤ (subCharges g [3,3,3,3,3]).toNat
                rw [toNat_subCharges g [3,3,3,3,3] (by simp;omega)]; simp; omega)
                (by show (5:ℕ)+1≤1024; omega))
              (runs_push _ .PUSH4 0xFFFFFFFF 4 (by nofun) dc14 rfl rfl (by
                show 3 ≤ (subCharges g [3,3,3,3,3,3]).toNat
                rw [toNat_subCharges g [3,3,3,3,3,3] (by simp;omega)]; simp; omega)
                (by show (6:ℕ)+1≤1024; omega)))))))

/-! ## The CALL step -/

/-- **The CALL step.** At `callerCalled g`, `stepFrame` emits `.needsCall` with the
child params and the suspended parent. Derived from `stepFrame_call` exactly as the
monolith does, but isolated as one lemma. -/
private theorem caller_call_step (g : UInt64) (hg : 30000 ≤ g.toNat) :
    stepFrame (callerCalled g)
      = .needsCall (callChildParams (callerCalled g) 0xCA11EE 0xFFFFFFFF)
          (callPending (callerCalled g) 0xCA11EE 0xFFFFFFFF) :=
  stepFrame_call (callerCalled g) 0xFFFFFFFF 0xCA11EE dc19 rfl (by show (7:ℕ)≤1024; omega) rfl
    (by show (0:ℕ)<1024; omega)
    (by
      show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
            (callerCalled g).exec.accounts (callerCalled g).exec.substate
            ≤ (callerCalled g).exec.gasAvailable.toNat
      rw [show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
            (callerCalled g).exec.accounts (callerCalled g).exec.substate = 2600 from by
            unfold callerCalled; dsimp only; decide]
      show 2600 ≤ (g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
        - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3).toNat
      rw [show (g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
            - UInt64.ofNat 3 - UInt64.ofNat 3) = subCharges g [3,3,3,3,3,3,3] from by simp [subCharges]]
      rw [toNat_subCharges g [3,3,3,3,3,3,3] (by simp; omega)]
      simp; omega)

/-! ## The child run over the empty pending stack -/

/-- The child `FrameResult` delivered by the run: the success `endFrame` of
`childFrame g`'s final state. Its `toCallResult` is `childResult g`. -/
private def childFrameRes (g : UInt64) : FrameResult :=
  endFrame (childFrame g) (.success (sstorePost (childAfter2Push g) 7 5 []) .empty)

private theorem childFrameRes_toCallResult (g : UInt64) :
    (childFrameRes g).toCallResult = childResult g := by
  unfold childFrameRes endFrame
  rw [show (childFrame g).kind = .call ⟨∅, callerXfer, childCkptSubstate⟩ from rfl]
  rfl

/-- **The child run, empty stack.** Over the empty pending stack, the genuine
driver runs the callee `PUSH;PUSH;SSTORE;STOP` from `childFrame g` to `.ok` of its
success `FrameResult`. This is the black-box `hchild` of `messageCall_call_runs`:
3 opcode steps + the 2-unit halt. -/
private theorem child_drive (g : UInt64) (n : ℕ)
    (hcg : 22106 ≤ childGas g) (hcg2 : childGas g < 2^64) :
    drive (n + 5) [] (.inl (childFrame g)) = .ok (childFrameRes g) := by
  have hofnat : (UInt64.ofNat (childGas g)).toNat = childGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  conv_lhs => dsimp only [childFrame]
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 dce0 (by
        show 3 ≤ (UInt64.ofNat (childGas g)).toNat; rw [hofnat]; omega) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 7 dce2 (by
        show 3 ≤ (UInt64.ofNat (childGas g) - UInt64.ofNat 3).toNat
        rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega)
        (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  have hg6 : ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat = childGas g - 6 := by
    rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega) (by omega),
        toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega
  rw [drive_step _ _ _ (stepFrame_sstore _ 7 5 _ dce4 rfl ?hsz rfl ?hstip ?hcost)]
  case hsz => show (2:ℕ) ≤ 1024; omega
  case hstip =>
    show ¬ ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat ≤ Gcallstipend
    rw [hg6, show Gcallstipend = 2300 from rfl]; omega
  case hcost => rw [sstoreChargeOf_child _ rfl rfl rfl rfl, hg6]; omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  rw [drive_halt _ _ _ (stepFrame_stop _ dce5 (by show (0:ℕ)≤1024; omega))]
  unfold childFrameRes endFrame childAfter2Push childFrame
  rfl

/-! ## The suffix `Runs`: the caller `STOP`s

After the child returns, `resumeAfterCall` hands the caller the child's account map
and advances it past the CALL. The caller's next (and last) opcode is `STOP`; the
suffix is the zero-step `Runs` to that halt site. -/

/-- The resumed caller frame (the parent after the child commits and returns). -/
private def callerResumed (g : UInt64) : Frame :=
  resumeAfterCall (childFrameRes g).toCallResult (callPending (callerCalled g) 0xCA11EE 0xFFFFFFFF)

/-- The resumed caller frame halts on `STOP`. -/
private theorem caller_resumed_halts (g : UInt64) :
    stepFrame (callerResumed g) = .halted (.success (callerResumed g).exec .empty) := by
  apply stepFrame_stop
  · show decode (callerResumed g).exec.executionEnv.code (callerResumed g).exec.pc = _
    unfold callerResumed resumeAfterCall callPending callerCalled callerEnv
    dsimp only [ExecutionState.replaceStackAndIncrPC, callerCharged]
    exact dc20
  · unfold callerResumed resumeAfterCall callPending
    dsimp only [ExecutionState.replaceStackAndIncrPC]
    show (Stack.push [] _).size ≤ 1024; show (1:ℕ) ≤ 1024; omega

/-! ## The compositional instantiation -/

/-- The child params' gas, named: the 63/64-capped `childGas g` as a `UInt64`. -/
private theorem child_params_gas (g : UInt64) :
    (callChildParams (callerCalled g) 0xCA11EE 0xFFFFFFFF).gas = UInt64.ofNat (childGas g) := by
  unfold callChildParams childGas callerCalled
  dsimp only [callerCharged]

/-- **`messageCall_call_runs`, instantiated on `callerProg`/`calleeProg`.**
For `g ≥ 30000`, the top-level call into the caller pins to the caller's `STOP`
result `endFrame (callerResumed g) …`, derived *compositionally* from the general
external-CALL rule: prefix pushes (`Runs.trans` of `runs_push1`/`runs_push`), the
CALL step, the black-box child run, the suffix `STOP`. -/
theorem messageCall_callerProg_runs (g : UInt64) (hg : 30000 ≤ g.toNat) :
    messageCall (callerParams g)
      = .ok (FrameResult.toCallResult
          (endFrame (callerResumed g) (.success (callerResumed g).exec .empty))) := by
  have hcg := childGas_lb g hg
  have hcg2 := childGas_ub g
  -- the child terminating run, lifted to fuel `seedFuel cp.gas`
  have hchild :
      drive (seedFuel (callChildParams (callerCalled g) 0xCA11EE 0xFFFFFFFF).gas) [] (.inl (childFrame g))
        = .ok (childFrameRes g) := by
    rw [child_params_gas g]
    have : seedFuel (UInt64.ofNat (childGas g)) = (seedFuel (UInt64.ofNat (childGas g)) - 5) + 5 := by
      have := two_le_seedFuel (UInt64.ofNat (childGas g)); unfold seedFuel; omega
    rw [this]; exact child_drive g _ hcg hcg2
  refine messageCall_call_runs (n₂ := 0) (callerParams g)
      (beginCall_caller g)
      (caller_prefix_runs g hg)
      (caller_call_step g hg)
      (beginCall_child g)
      hchild
      (Runs.refl (callerResumed g))
      (caller_resumed_halts g)
      ?_
  · -- fuel: seedFuel cp.gas + 7 + 1 ≤ seedFuel (callerParams g).gas
    rw [child_params_gas g]
    show seedFuel (UInt64.ofNat (childGas g)) + 7 + 1 ≤ seedFuel (callerParams g).gas
    rw [show (callerParams g).gas = g from rfl]
    have hcgub : (UInt64.ofNat (childGas g)).toNat = childGas g := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    -- seedFuel x = 2 * x.toNat + 4096; reduces to `childGas g + 4 ≤ g.toNat`.
    show 2 * (UInt64.ofNat (childGas g)).toNat + 4096 + 7 + 1 ≤ 2 * g.toNat + 4096
    rw [hcgub]
    have := childGas_le_caller g hg
    omega

/-- **The compositional external-call storage result.** Reading
`messageCall_callerProg_runs`'s pinned result through `storageAt (addrCallee, 7)`
recovers the callee's committed `5`, for `g ≥ 30000`, obtained by *instantiating
the general rule* `messageCall_call_runs` rather than a giant opcode chain. This is
the proof the concrete `∃G₀` spec `Examples.messageCall_call_storageAt` delegates
to. The `callerResumed g` final result's cell agrees with `ExternalCall.final_obs`,
since `(childFrameRes g).toCallResult = childResult g`. -/
theorem messageCall_callerProg_storageAt (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 := by
  rw [messageCall_callerProg_runs g hg]
  refine congrArg Except.ok ?_
  show CallResult.storageAt
      (endFrame (callerResumed g) (.success (callerResumed g).exec .empty)).toCallResult addrCallee 7 = 5
  -- `callerResumed g = resumeAfterCall (childResult g) (callPending …)`
  rw [show callerResumed g
        = resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295) from by
      unfold callerResumed
      rw [childFrameRes_toCallResult]]
  exact final_obs g

end BytecodeLayer.Examples
