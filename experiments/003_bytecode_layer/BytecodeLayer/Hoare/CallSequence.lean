import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Interpreter.DescentEq
import BytecodeLayer.Semantics.Interpreter.DescentDrops
import BytecodeLayer.Hoare.OutcomeBridge

/-!
# The SOUND, general external-CALL sequencing rule (`messageCall_call_runs`)

This file proves the **program-agnostic** external-call analogue of the
intra-frame `messageCall_runs`: a caller that `Runs` from its entry frame to a
CALL site, issues a CALL whose child terminates (as a *black box* — any
terminating child run), then `Runs` from the resumed frame to a halt site,
produces the expected `messageCall` result. The single side condition is the
numeric fuel bound `seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas`.

It is the real theorem that replaces any assumed-the-conclusion forwarding
hypothesis: the black-box child is reconciled against the suffix's concrete
terminating run by `messageCall`-never-out-of-fuel plus fuel monotonicity
(`drive_eq_of_both_ne_oof`).
-/

namespace BytecodeLayer.Hoare
open Evm BytecodeLayer.Interpreter BytecodeLayer.System

/-! ## Lemma 1 — fuel-agnostic agreement of terminating runs -/

/-- **Two terminating runs agree.** If `drive` at fuels `a` and `b` over the same
stack/state both avoid `OutOfFuel`, they return the same result. The larger fuel
equals the smaller by `drive_fuel_mono` either way. -/
theorem drive_eq_of_both_ne_oof {a b : ℕ} (stack : List Pending)
    (state : Frame ⊕ FrameResult)
    (ha : drive a stack state ≠ .error .OutOfFuel)
    (hb : drive b stack state ≠ .error .OutOfFuel) :
    drive a stack state = drive b stack state := by
  rcases Nat.le_total a b with hle | hle
  · exact (drive_fuel_mono hle stack state ha).symm
  · exact drive_fuel_mono hle stack state hb

/-! ## Lemma 2 — the keystone external-CALL sequencing rule -/

/-- **The general external-CALL sequencing rule.** A caller enters as code
(`EntersAsCode p fr₀`), `Runs` its prefix to a CALL site `callFr`, issues a
CALL (`stepFrame callFr = .needsCall cp pending`) whose child enters as code
(`EntersAsCode cp child`) and **terminates** (`drive (seedFuel cp.gas) [] …
= .ok childRes`, taken as a black box), then `Runs` its suffix from the resumed
frame to a halt site `last`. Given the numeric fuel bound, `messageCall p`
delivers the caller's halt result.

This is the external-call analogue of `messageCall_runs`. -/
theorem messageCall_call_runs {n₁ n₂ : ℕ}
    (p cp : CallParams) (fr₀ callFr child last : Frame)
    (childRes : FrameResult) (pending : PendingCall) (halt : FrameHalt)
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcall    : stepFrame callFr = .needsCall cp pending)
    (hcbegin  : EntersAsCode cp child)
    (hchild   : drive (seedFuel cp.gas) [] (running child) = .ok childRes)
    (hpost    : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last)
    (hhalt    : stepFrame last = .halted halt)
    (hfuel    : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  set S := seedFuel p.gas with hS
  -- Abbreviation for the resumed parent frame.
  set R := resumeAfterCall childRes.toCallResult pending with hR
  -- Reduce the goal to a `drive` equation.
  rw [messageCall_eq_drive p fr₀ hbegin]
  -- It suffices to show `drive S [] (.inl fr₀) = .ok (endFrame last halt)`.
  suffices hmain : drive S [] (.inl fr₀) = .ok (endFrame last halt) by
    rw [hmain]; rfl
  -- `m` is the fuel after the prefix and the CALL step.
  set m := S - n₁ - 1 with hm
  -- 1. Prefix: advance from `fr₀` to `callFr`.
  have hprefix : drive S [] (.inl fr₀) = drive (S - n₁) [] (.inl callFr) := by
    conv_lhs => rw [show S = n₁ + (S - n₁) by omega]
    rw [hpre.drive_advance (S - n₁)]
  -- 2. The CALL step: descend into the child, suspending the parent.
  have hcallstep : drive (S - n₁) [] (.inl callFr)
      = drive m (.call pending :: []) (.inl child) := by
    rw [show S - n₁ = m + 1 by omega]
    exact driveG_needsCall_code m [] callFr cp pending child hcall hcbegin
  -- 3a. Lift the (black-box) child run to fuel `m`.
  have hchild_m : drive m [] (.inl child) = .ok childRes := by
    rw [drive_fuel_mono (show seedFuel cp.gas ≤ m by omega) [] (.inl child)
      (by rw [hchild]; nofun)]
    exact hchild
  -- 3b. Descend equation: in-line descent equals resumed parent at some fuel `j`.
  obtain ⟨j, hj⟩ := drive_descend_eq m child childRes pending [] hchild_m
  -- Chain 1–3: `drive S [] (.inl fr₀) = drive j [] (.inl R)`.
  have hchain : drive S [] (.inl fr₀) = drive j [] (.inl R) := by
    rw [hprefix, hcallstep, hj]
  -- 4. Suffix: a concrete terminating run from `R`.
  have hsuffix : drive (n₂ + 2) [] (.inl R) = .ok (endFrame last halt) := by
    rw [hpost.drive_advance 2]
    exact drive_halt 0 last halt hhalt
  -- `drive S [] (.inl fr₀) ≠ OutOfFuel` from `messageCall_never_outOfFuel`.
  have hS_neoof : drive S [] (.inl fr₀) ≠ .error .OutOfFuel := by
    intro hcontra
    apply messageCall_never_outOfFuel p
    rw [messageCall_eq_drive p fr₀ hbegin, hcontra]
    rfl
  -- Hence `drive j [] (.inl R) ≠ OutOfFuel` (it equals `drive S [] (.inl fr₀)`).
  have hj_neoof : drive j [] (.inl R) ≠ .error .OutOfFuel := by
    rw [← hchain]; exact hS_neoof
  -- And the suffix run avoids `OutOfFuel`.
  have hsuf_neoof : drive (n₂ + 2) [] (.inl R) ≠ .error .OutOfFuel := by
    rw [hsuffix]; nofun
  -- Reconcile the two terminating runs of `R`.
  have hjeq : drive j [] (.inl R) = drive (n₂ + 2) [] (.inl R) :=
    drive_eq_of_both_ne_oof [] (.inl R) hj_neoof hsuf_neoof
  -- Combine.
  rw [hchain, hjeq, hsuffix]

/-! ## Except/Outcome decoders (reusable plumbing) -/

/-- Decode a successful `.map`: `x.map f = .ok y` exposes the underlying `.ok r`. -/
theorem ok_of_map_ok {α β : Type} {x : Except ExecutionException α} {f : α → β} {y : β}
    (h : x.map f = .ok y) : ∃ r, x = .ok r ∧ f r = y := by
  cases x with
  | error e => simp [Except.map] at h
  | ok r => exact ⟨r, rfl, by simpa [Except.map] using h⟩

/-- A completed `.ok r` with `r.success` and cell `(a,k) = v` is `completedWith`. -/
theorem completedWith_of_ok {p : CallParams} {r : CallResult}
    {a : AccountAddress} {k v : UInt256}
    (hmc : messageCall p = .ok r) (hsucc : r.success = true)
    (hstore : CallResult.storageAt r a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v := by
  refine ⟨r.output, CallResult.storageAt r, ?_, hstore⟩
  rw [ofCall_completed_of_success hmc hsucc]

/-! ## The general external-CALL rule at the named-`Outcome` level -/

/-- **The general external-CALL rule, observable-level.** The same honest,
program-agnostic sequencing hypotheses as `messageCall_call_runs`, plus the caller's
halt result being a success leaving `v` at cell `(a, k)`, yield the named
`Outcome.completedWith` predicate on `Outcome.ofCall (messageCall p)`. This is the
sound external-call rule the spec surface exposes — no assumed forwarding. -/
theorem messageCall_call_completedWith {n₁ n₂ : ℕ}
    (p cp : CallParams) (fr₀ callFr child last : Frame)
    (childRes : FrameResult) (pending : PendingCall) (halt : FrameHalt)
    (a : AccountAddress) (k v : UInt256)
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcall    : stepFrame callFr = .needsCall cp pending)
    (hcbegin  : EntersAsCode cp child)
    (hchild   : drive (seedFuel cp.gas) [] (running child) = .ok childRes)
    (hpost    : Runs n₂ (resumeAfterCall childRes.toCallResult pending) last)
    (hhalt    : stepFrame last = .halted halt)
    (hfuel    : seedFuel cp.gas + n₁ + 1 ≤ seedFuel p.gas)
    (hsucc    : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell    : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  completedWith_of_ok
    (messageCall_call_runs p cp fr₀ callFr child last childRes pending halt
      hbegin hpre hcall hcbegin hchild hpost hhalt hfuel)
    hsucc hcell

end BytecodeLayer.Hoare
