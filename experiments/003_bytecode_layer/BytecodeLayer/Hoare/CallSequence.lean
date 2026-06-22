import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Interpreter.DescentEq
import BytecodeLayer.Semantics.Interpreter.NeverOutOfFuel
import BytecodeLayer.Hoare.OutcomeBridge

/-!
# The two `messageCall`-boundary bridges, both fuel-free

This file holds **both** `messageCall`-boundary sequencing rules — the call-free
`messageCall_runs` and the external-CALL `messageCall_call_runs` — each proved
**fuel-free** (no numeric `n + … ≤ seedFuel` side condition) via
never-out-of-fuel (`messageCall_never_outOfFuel`) plus fuel agreement
(`drive_eq_of_both_ne_oof`).

`messageCall_runs` is the intra-frame bridge: a caller that `Runs` from its entry
frame to a halt site produces the expected `messageCall` result. Its run needs
exactly `n + 2` fuel, which `drive_eq_of_both_ne_oof` reconciles with
`seedFuel p.gas` (both avoid `OutOfFuel`) — no fuel ordering needed.

`messageCall_call_runs` is the **program-agnostic** external-call analogue: a
caller that `Runs` from its entry frame to a CALL site, issues a CALL whose child
terminates (as a *black box* — any terminating child run), then `Runs` from the
resumed frame to a halt site, produces the expected `messageCall` result. The
three call-facts (the CALL step, the child entering as code, and the child's
terminating run) are bundled into the derived `CallReturns` predicate, so the
rule reads as a clean five-hypothesis sequence with **no numeric fuel side
condition**.

`messageCall_call_runs` is the real theorem that replaces any
assumed-the-conclusion forwarding hypothesis: the black-box child is reconciled
against the suffix's concrete terminating run by `messageCall`-never-out-of-fuel
plus fuel monotonicity (`drive_eq_of_both_ne_oof`). Its fuel bound is discharged
internally by running the whole sequence at a deliberately large concrete fuel
and reconciling it with `seedFuel p.gas` via `drive_eq_of_both_ne_oof` — no
caller-supplied bound.
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

/-! ## The call-free boundary bridge `messageCall_runs` -/

/-- **A `Runs` block at the `messageCall` boundary, halting.** If a code call's
initial frame `fr₀` (`EntersAsCode p fr₀`) `Runs` to a frame `last` that halts
with `halt`, then `messageCall p = .ok (toCallResult (endFrame last halt))` —
**no numeric fuel side condition**.

The run needs exactly `n + 2` fuel (advance the `n` prefix steps, then halt and
deliver in `+2`); `drive_eq_of_both_ne_oof` reconciles that concrete fuel with
`seedFuel p.gas` since both avoid `OutOfFuel` (the latter by
`messageCall_never_outOfFuel`) — no fuel ordering needed.

This is the boundary; from here up, statements are observable-only. -/
theorem messageCall_runs (p : CallParams) {n : ℕ} {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (h : Runs n fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  -- The run delivers the caller's halt result (as a `FrameResult`) in exactly `n + 2` fuel.
  have hrun : drive (n + 2) [] (running fr₀) = .ok (endFrame last halt) := by
    rw [h.drive_advance 2]
    exact drive_halt 0 last halt hhalt
  -- Both the concrete run and the seeded run avoid `OutOfFuel`.
  have hrun_neoof : drive (n + 2) [] (running fr₀) ≠ .error .OutOfFuel := by
    rw [hrun]; nofun
  have hseed_neoof : drive (seedFuel p.gas) [] (running fr₀) ≠ .error .OutOfFuel := by
    intro hcontra
    apply messageCall_never_outOfFuel p
    rw [messageCall_eq_drive p fr₀ hbegin, hcontra]
    rfl
  -- Reduce the goal to a `drive` equation and reconcile the two terminating runs.
  rw [messageCall_eq_drive p fr₀ hbegin]
  rw [drive_eq_of_both_ne_oof [] (running fr₀) hseed_neoof hrun_neoof, hrun]
  rfl

/-! ## The bundled `CallReturns` predicate -/

/-- `callFr` issues a CALL whose child runs to completion, resuming at `resumeFr`.

Bundles the three call-facts of the external-CALL sequence: the CALL step
(`stepFrame callFr = .needsCall cp pending`), the child entering as code
(`EntersAsCode cp child`), and the child's black-box terminating run
(`drive (seedFuel cp.gas) [] (running child) = .ok childRes`), pinning the
resumed parent frame to `resumeAfterCall childRes.toCallResult pending`. -/
def CallReturns (callFr resumeFr : Frame) : Prop :=
  ∃ cp pending child childRes,
       stepFrame callFr = .needsCall cp pending
     ∧ EntersAsCode cp child
     ∧ drive (seedFuel cp.gas) [] (running child) = .ok childRes
     ∧ resumeFr = resumeAfterCall childRes.toCallResult pending

/-! ## Lemma 2 — the keystone external-CALL sequencing rule -/

/-- **The general external-CALL sequencing rule.** A caller enters as code
(`EntersAsCode p fr₀`), `Runs` its prefix to a CALL site `callFr`, issues a CALL
whose child enters as code and terminates, resuming at `resumeFr`
(`CallReturns callFr resumeFr`, a black-box terminating child), then `Runs` its
suffix from `resumeFr` to a halt site `last`. `messageCall p` delivers the
caller's halt result — **no numeric fuel side condition**.

The fuel bound is discharged internally: the whole sequence is run at a
deliberately large concrete fuel `f*` (chosen so every fuel split closes by
`omega` and `seedFuel p.gas ≤ f*` holds outright), then reconciled with
`seedFuel p.gas` through `drive_eq_of_both_ne_oof` and
`messageCall_never_outOfFuel`.

This is the external-call analogue of `messageCall_runs`. -/
theorem messageCall_call_runs (p : CallParams) {n₁ n₂ : ℕ}
    {fr₀ callFr resumeFr last : Frame} {halt : FrameHalt}
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcallret : CallReturns callFr resumeFr)
    (hpost    : Runs n₂ resumeFr last)
    (hhalt    : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  obtain ⟨cp, pending, child, childRes, hcall, hcbegin, hchild, hres⟩ := hcallret
  subst hres
  -- Abbreviation for the resumed parent frame.
  set R := resumeAfterCall childRes.toCallResult pending with hR
  -- A deliberately large concrete fuel: every split closes by `omega`, and
  -- `seedFuel p.gas ≤ f*` holds outright — no caller-supplied bound.
  set f := seedFuel p.gas + n₁ + 1 + seedFuel cp.gas + n₂ + 2 with hf
  -- `m` is the fuel after the prefix and the CALL step.
  set m := f - n₁ - 1 with hm
  -- 1. Prefix: advance from `fr₀` to `callFr`.
  have hprefix : drive f [] (.inl fr₀) = drive (f - n₁) [] (.inl callFr) := by
    conv_lhs => rw [show f = n₁ + (f - n₁) by omega]
    rw [hpre.drive_advance (f - n₁)]
  -- 2. The CALL step: descend into the child, suspending the parent.
  have hcallstep : drive (f - n₁) [] (.inl callFr)
      = drive m (.call pending :: []) (.inl child) := by
    rw [show f - n₁ = m + 1 by omega]
    exact driveG_needsCall_code m [] callFr cp pending child hcall hcbegin
  -- 3a. Lift the (black-box) child run to fuel `m`.
  have hchild_m : drive m [] (.inl child) = .ok childRes := by
    rw [drive_fuel_mono (show seedFuel cp.gas ≤ m by omega) [] (.inl child)
      (by rw [hchild]; nofun)]
    exact hchild
  -- 3b. Descend equation: in-line descent equals resumed parent at some fuel `j`.
  obtain ⟨j, hj⟩ := drive_descend_eq m child childRes pending [] hchild_m
  -- Chain 1–3: `drive f [] (.inl fr₀) = drive j [] (.inl R)`.
  have hchain : drive f [] (.inl fr₀) = drive j [] (.inl R) := by
    rw [hprefix, hcallstep, hj]
  -- 4. Suffix: a concrete terminating run from `R`.
  have hsuffix : drive (n₂ + 2) [] (.inl R) = .ok (endFrame last halt) := by
    rw [hpost.drive_advance 2]
    exact drive_halt 0 last halt hhalt
  -- `drive (seedFuel p.gas) [] (.inl fr₀) ≠ OutOfFuel` from `messageCall_never_outOfFuel`.
  have hseed_neoof : drive (seedFuel p.gas) [] (.inl fr₀) ≠ .error .OutOfFuel := by
    intro hcontra
    apply messageCall_never_outOfFuel p
    rw [messageCall_eq_drive p fr₀ hbegin, hcontra]
    rfl
  -- Hence `drive f [] (.inl fr₀) ≠ OutOfFuel` (`seedFuel p.gas ≤ f`, by monotonicity).
  have hf_neoof : drive f [] (.inl fr₀) ≠ .error .OutOfFuel := by
    rw [drive_fuel_mono (show seedFuel p.gas ≤ f by omega) [] (.inl fr₀) hseed_neoof]
    exact hseed_neoof
  -- Hence `drive j [] (.inl R) ≠ OutOfFuel` (it equals `drive f [] (.inl fr₀)`).
  have hj_neoof : drive j [] (.inl R) ≠ .error .OutOfFuel := by
    rw [← hchain]; exact hf_neoof
  -- And the suffix run avoids `OutOfFuel`.
  have hsuf_neoof : drive (n₂ + 2) [] (.inl R) ≠ .error .OutOfFuel := by
    rw [hsuffix]; nofun
  -- Reconcile the two terminating runs of `R`.
  have hjeq : drive j [] (.inl R) = drive (n₂ + 2) [] (.inl R) :=
    drive_eq_of_both_ne_oof [] (.inl R) hj_neoof hsuf_neoof
  -- The large-fuel run delivers the caller's halt result.
  have hf_ok : drive f [] (.inl fr₀) = .ok (endFrame last halt) := by
    rw [hchain, hjeq, hsuffix]
  -- Reduce the goal to a `drive` equation and reconcile `f` with `seedFuel p.gas`.
  rw [messageCall_eq_drive p fr₀ hbegin]
  rw [drive_eq_of_both_ne_oof [] (.inl fr₀) hseed_neoof hf_neoof, hf_ok]
  rfl

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
theorem messageCall_call_completedWith (p : CallParams) {n₁ n₂ : ℕ}
    {fr₀ callFr resumeFr last : Frame} {halt : FrameHalt}
    (a : AccountAddress) (k v : UInt256)
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs n₁ fr₀ callFr)
    (hcallret : CallReturns callFr resumeFr)
    (hpost    : Runs n₂ resumeFr last)
    (hhalt    : stepFrame last = .halted halt)
    (hsucc    : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell    : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  completedWith_of_ok
    (messageCall_call_runs p hbegin hpre hcallret hpost hhalt)
    hsucc hcell

end BytecodeLayer.Hoare
