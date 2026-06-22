import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Interpreter.DescentEq
import BytecodeLayer.Semantics.Interpreter.NeverOutOfFuel
import BytecodeLayer.Hoare.OutcomeBridge

/-!
# The two `messageCall`-boundary bridges, both fuel-free

This file holds **both** `messageCall`-boundary sequencing rules — the call-free
`messageCall_runs` and the external-CALL `messageCall_call_runs` — each proved
**fuel-free** (no numeric `n + … ≤ seedFuel` side condition) via
never-out-of-fuel (`messageCall_never_outOfFuel`) plus the index-free `Runs`
reconciliation invariant `Runs.drive_reconcile`.

`Runs.drive_reconcile` is the engine: since the index-free `Runs` carries no step
count, the bridges cannot phrase a numeric fuel bound. Instead this invariant
says that **any** non-`OutOfFuel` run from any frame on a `Runs` path yields the
same final result — proved by induction on `Runs`, splicing returning external
calls (`call` nodes) into the path via `drive_descend_eq` + `drive_fuel_mono`.

`messageCall_runs` is the intra-frame bridge: a caller that `Runs` from its entry
frame to a halt site produces the expected `messageCall` result. The halt site
delivers in `2` fuel, which `Runs.drive_reconcile` reconciles with the seeded run
(both avoid `OutOfFuel`) — no fuel ordering needed.

`messageCall_call_runs` is the **program-agnostic** external-call analogue: a
caller that `Runs` from its entry frame to a CALL site, a returning CALL (the
bundled `CallReturns` — the CALL step, the child entering as code, and the child's
black-box terminating run), then `Runs` from the resumed frame to a halt site. It
is now a corollary of `messageCall_runs`: the prefix, the `Runs.call` node, and
the suffix glue into one `Runs fr₀ last` by `Runs.trans`, with all reconciliation
delegated to `Runs.drive_reconcile`.
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

/-! ## The index-free `Runs` reconciliation invariant

The `Runs` relation carries no step-index. `Runs.drive_reconcile` is the
replacement for the old exact-fuel `drive_advance`: it states that **any**
non-`OutOfFuel` run from any frame on a `Runs` path yields the same final result.
Proved by induction on the `Runs` derivation, reusing the existing bricks —
`drive_eq_of_both_ne_oof` (the `refl` link), `drive_stepsTo` (the `step` link),
and `drive_descend_eq` + `drive_fuel_mono` (the `call` link, which splices a whole
returning child run into the path). No fuel bookkeeping, no numeric side
condition: the driver self-reconciles across the empty-stack run because every
configuration on the path terminates whenever the endpoints do. -/

/-- **The `Runs` reconciliation invariant.** If `fr` `Runs` to `last`, then any
two terminating (`≠ OutOfFuel`) runs — one from `fr` at fuel `a`, one from `last`
at fuel `b`, both over the empty pending stack — deliver the **same** result.

This is the index-free successor of the old exact-fuel `drive_advance`: it never
mentions a step count, only that the endpoints both avoid `OutOfFuel`. The three
links reuse existing lemmas without reproving them:
* `refl` — `fr = last`, so the two runs reconcile by `drive_eq_of_both_ne_oof`;
* `step` — peel one `drive` step with `drive_stepsTo`, recurse;
* `call` — splice the returning child via `drive_descend_eq` (lifting the
  black-box child run to the path's fuel with `drive_fuel_mono`), then recurse on
  the resumed frame. -/
theorem Runs.drive_reconcile {fr last : Frame} (h : Runs fr last) :
    ∀ {a b : ℕ},
      drive a [] (running fr) ≠ .error .OutOfFuel →
      drive b [] (running last) ≠ .error .OutOfFuel →
      drive a [] (running fr) = drive b [] (running last) := by
  induction h with
  | refl _ =>
    intro a b ha hb
    exact drive_eq_of_both_ne_oof [] (running _) ha hb
  | @step fr mid fr' hstep _ ih =>
    intro a b ha hb
    -- `a = 0` would be `OutOfFuel`, so peel one step `fr → mid`.
    cases a with
    | zero => simp [drive] at ha
    | succ a' =>
      rw [drive_stepsTo a' hstep] at ha ⊢
      exact ih ha hb
  | @call callFr resumeFr fr' hcall _ ih =>
    intro a b ha hb
    obtain ⟨cp, pending, child, childRes, hstep, hcbegin, hchild, hres⟩ := hcall
    subst hres
    -- `a = 0` would be `OutOfFuel`, so peel the CALL step `callFr → child`.
    cases a with
    | zero => simp [drive] at ha
    | succ a' =>
      rw [driveG_needsCall_code a' [] callFr cp pending child hstep hcbegin] at ha ⊢
      -- Lift the black-box child run to a fuel `≥` the path's fuel so the descent
      -- equation applies, then reconcile with the path's own (terminating) descent.
      set m := max a' (seedFuel cp.gas) with hm
      have hchild_m : drive m [] (running child) = .ok childRes := by
        rw [drive_fuel_mono (show seedFuel cp.gas ≤ m by omega) [] (running child)
          (by rw [hchild]; nofun)]
        exact hchild
      obtain ⟨j, hj⟩ := drive_descend_eq m child childRes pending [] hchild_m
      -- The descent at fuel `a'` equals the descent at the larger fuel `m`
      -- (the path's descent terminates, by `ha`), which `drive_descend_eq` turns
      -- into a run from the resumed frame.
      have hdesc : drive a' (.call pending :: []) (running child)
          = drive j [] (running (resumeAfterCall childRes.toCallResult pending)) := by
        rw [← hj]
        exact (drive_fuel_mono (show a' ≤ m by omega) (.call pending :: []) (running child)
          ha).symm
      rw [hdesc] at ha ⊢
      exact ih ha hb

/-! ## The call-free boundary bridge `messageCall_runs` -/

/-- **A `Runs` block at the `messageCall` boundary, halting.** If a code call's
initial frame `fr₀` (`EntersAsCode p fr₀`) `Runs` to a frame `last` that halts
with `halt`, then `messageCall p = .ok (toCallResult (endFrame last halt))` —
**no numeric fuel side condition**.

The halt site delivers its result in `2` fuel; `Runs.drive_reconcile` reconciles
that with the seeded run from `fr₀` since both avoid `OutOfFuel` (the latter by
`messageCall_never_outOfFuel`) — no step index, no fuel ordering.

This is the boundary; from here up, statements are observable-only. -/
theorem messageCall_runs (p : CallParams) {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (h : Runs fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  -- The halt site delivers the caller's halt result (as a `FrameResult`) in `2` fuel.
  have hlast : drive 2 [] (running last) = .ok (endFrame last halt) :=
    drive_halt 0 last halt hhalt
  have hlast_neoof : drive 2 [] (running last) ≠ .error .OutOfFuel := by
    rw [hlast]; nofun
  -- The seeded run from `fr₀` avoids `OutOfFuel` (never-out-of-fuel at the boundary).
  have hseed_neoof : drive (seedFuel p.gas) [] (running fr₀) ≠ .error .OutOfFuel := by
    intro hcontra
    apply messageCall_never_outOfFuel p
    rw [messageCall_eq_drive p fr₀ hbegin, hcontra]
    rfl
  -- Reduce the goal to a `drive` equation and reconcile the run from `fr₀` with
  -- the halting run from `last` along the `Runs` path — no step index, no fuel bound.
  rw [messageCall_eq_drive p fr₀ hbegin]
  rw [h.drive_reconcile hseed_neoof hlast_neoof, hlast]
  rfl

/-! ## Lemma 2 — the keystone external-CALL sequencing rule -/

/-- **The general external-CALL sequencing rule.** A caller enters as code
(`EntersAsCode p fr₀`), `Runs` its prefix to a CALL site `callFr`, issues a CALL
whose child enters as code and terminates, resuming at `resumeFr`
(`CallReturns callFr resumeFr`, a black-box terminating child), then `Runs` its
suffix from `resumeFr` to a halt site `last`. `messageCall p` delivers the
caller's halt result — **no numeric fuel side condition**.

With the index-free `Runs`, this is now a one-liner: the prefix, the returning
CALL node (`Runs.call`), and the suffix glue into a single `Runs fr₀ last` by
`Runs.trans`, and `messageCall_runs` crosses the boundary. The whole fuel
reconciliation — including splicing the black-box child run into the path — lives
inside `Runs.drive_reconcile`. -/
theorem messageCall_call_runs (p : CallParams)
    {fr₀ callFr resumeFr last : Frame} {halt : FrameHalt}
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs fr₀ callFr)
    (hcallret : CallReturns callFr resumeFr)
    (hpost    : Runs resumeFr last)
    (hhalt    : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin
    (hpre.trans (Runs.call hcallret hpost))
    hhalt

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
theorem messageCall_call_completedWith (p : CallParams)
    {fr₀ callFr resumeFr last : Frame} {halt : FrameHalt}
    (a : AccountAddress) (k v : UInt256)
    (hbegin   : EntersAsCode p fr₀)
    (hpre     : Runs fr₀ callFr)
    (hcallret : CallReturns callFr resumeFr)
    (hpost    : Runs resumeFr last)
    (hhalt    : stepFrame last = .halted halt)
    (hsucc    : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell    : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  completedWith_of_ok
    (messageCall_call_runs p hbegin hpre hcallret hpost hhalt)
    hsucc hcell

end BytecodeLayer.Hoare
