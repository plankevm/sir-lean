import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Interpreter.DescentEq
import BytecodeLayer.Semantics.Interpreter.NeverOutOfFuel
import BytecodeLayer.Hoare.OutcomeBridge

/-!
# The single `messageCall`-boundary bridge, fuel-free

This file holds the **one** `messageCall`-boundary sequencing rule,
`messageCall_runs`, proved **fuel-free** (no numeric `n + … ≤ seedFuel` side
condition) via never-out-of-fuel (`messageCall_never_outOfFuel`) plus the
index-free `Runs` reconciliation invariant `Runs.drive_reconcile`.

`Runs.drive_reconcile` is the engine: since the index-free `Runs` carries no step
count, the bridge cannot phrase a numeric fuel bound. Instead this invariant
says that **any** non-`OutOfFuel` run from any frame on a `Runs` path yields the
same final result — proved by induction on `Runs`, splicing returning external
calls (`call` nodes) into the path via `drive_descend_eq` + `drive_fuel_mono`.

`messageCall_runs` is the intra-frame bridge: a caller that `Runs` from its entry
frame to a halt site produces the expected `messageCall` result. The halt site
delivers in `2` fuel, which `Runs.drive_reconcile` reconciles with the seeded run
(both avoid `OutOfFuel`) — no fuel ordering needed.

Because `Runs` carries external CALLs as `call` nodes (`CallReturns`), this **one**
bridge already covers programs with **any number** of returning external calls,
interleaved with opcode steps in any order: the caller simply builds its
`Runs fr₀ last` with `Runs.call` / `Runs.step` / `Runs.trans` and crosses the
boundary once. The former separate `messageCall_call_runs` (a single `.call` node)
is the one-`.call` special case and is no longer needed; the general
multi-call composition guarantee is `messageCall_runs_calls` below.
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

/-! ## Multi-call composition (the general regular-language-shaped guarantee)

`messageCall_runs` already accepts a `Runs fr₀ last` that contains **any number**
of `.call` nodes interleaved with `.step`s in any order — its only premises are
`EntersAsCode p fr₀` and that `last` halts. `messageCall_runs_calls` is the same
statement, re-stated as the explicit "≥N returning external calls compose"
guarantee: it is *definitionally* `messageCall_runs`, named so callers can cite the
multi-call composition contract directly. The reconciliation across every `call`
node lives inside `Runs.drive_reconcile`; there is no per-call halt requirement and
no numeric fuel side condition. -/

/-- **Multi-call composition.** A caller that enters as code (`EntersAsCode p fr₀`)
and whose single `Runs fr₀ last` interleaves **any number of returning external
CALLs** (`.call` / `CallReturns` nodes) with opcode steps, ending at a halting
`last`, delivers the caller's halt result as `messageCall p` — with **no numeric
fuel side condition and no per-call halt requirement**. Intermediary calls (calls
that return into more code rather than halting the program) compose: each is just a
`.call` node spliced into the path by `Runs.drive_reconcile`.

This is `messageCall_runs` under a name that makes the multi-call guarantee
explicit; the caller builds `h` with `Runs.call` / `Runs.step` / `Runs.trans`. -/
theorem messageCall_runs_calls (p : CallParams) {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (h : Runs fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin h hhalt

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

/-- **The general external-CALL rule, observable-level.** A caller that enters as
code and whose single `Runs fr₀ last` carries **any number** of returning external
CALLs (`.call` nodes) to a halting `last`, plus the caller's halt result being a
success leaving `v` at cell `(a, k)`, yields the named `Outcome.completedWith`
predicate on `Outcome.ofCall (messageCall p)`. This is the sound external-call rule
the spec surface exposes — no assumed forwarding, no per-call halt requirement, no
numeric fuel side condition. The caller builds `h` with `Runs.call` /
`Runs.step` / `Runs.trans` (the single-call case is one `.call` node). -/
theorem messageCall_calls_completedWith (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (a : AccountAddress) (k v : UInt256)
    (hbegin : EntersAsCode p fr₀)
    (h      : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt)
    (hsucc  : (FrameResult.toCallResult (endFrame last halt)).success = true)
    (hcell  : CallResult.storageAt (FrameResult.toCallResult (endFrame last halt)) a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v :=
  completedWith_of_ok
    (messageCall_runs p hbegin h hhalt)
    hsucc hcell

end BytecodeLayer.Hoare
