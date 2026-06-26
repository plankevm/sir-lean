import BytecodeLayer.SharedObservable

/-!
# The flat ↔ nested observational-equivalence statement (stated, not proved)

This module states the END-GOAL equivalence at the only altitude the two engines
can be compared: the toolchain-neutral `SharedObservable` (see
`SharedObservable.lean` for *why* it must be plain data — the two packages pin
different Lean toolchains and cannot co-compile).

Because the nested `Θ` cannot be imported here (different toolchain), the nested
half of every statement is taken as an **already-computed `SharedObservable`
value** — i.e. the plain data `observe_nested (nestedSem.run w')` produced on the
exp004 side and transported across as serialized data. The flat half is computed
live via `observe_flat (flatSem.run w)`.

Everything below is a `def … : Prop` (a *statement*), or a fully-proved lemma —
**no `sorry`, no `axiom`, no `admit`**. The genuine equivalence *theorem* is left
as `def`-level goals with the input-bridge made explicit, because proving it
requires executing the nested `Θ` (impossible to import here) plus a
`CallParams ↔ NestedWorld` state bridge; the cost of that bridge is estimated in
the report.
-/

namespace BytecodeLayer
open Evm

/-! ## The general equivalence goal

For matching inputs, the flat and nested engines produce observationally-equal
results. Stated over the shared observable: the flat projection of the flat run
`agrees` (pure data + pointwise storage) with the nested projection of the nested
run. The nested projection arrives as the value `nestedObs` (transported data). -/

/-- **The general observational-equivalence goal.** Given a flat call described by
`p : CallParams` and the nested side's already-computed observable `nestedObs`
(`= observe_nested (nestedSem.run w')` for the corresponding nested world `w'`),
the flat run's observable fully agrees with it: same tag / output / gas / logs
and pointwise-equal storage.

This is the END-GOAL statement at observable altitude. Proving it for arbitrary
matching `(p, w')` needs (a) the nested `Θ` evaluated (cross-toolchain — done on
the exp004 side) and (b) a `CallParams ↔ NestedWorld` input bridge relating the
two descriptions of "the same call". -/
def equivGoal (p : CallParams) (nestedObs : SharedObservable) : Prop :=
  (observe_flat (flatSem.run p)).agrees nestedObs

/-! ## The smallest concrete instance: an empty / `STOP`-only top-level call

The cheapest program to relate is one that does nothing observable: it completes
successfully, returns no bytes, emits no logs, and leaves storage untouched. Both
engines must produce *exactly* this shared observable for such a call. We state
the expected shared observable explicitly and give the flat-side facts that hold
definitionally; the nested side must produce the same value (its
`observe_nested` of a `STOP` run), which is the concrete equivalence to discharge
once the input bridge exists. -/

/-- The shared observable a do-nothing top-level call must produce on **both**
engines: completed (`"ok"`), empty output, empty logs, gas `g`, all-zero storage.
`g` is the (engine-specific) gas remaining; the do-nothing equivalence is exactly
`dataAgrees` modulo this single ℕ (the report excludes exact gas from the
granularity, so the load-bearing claim is `tag`/`output`/`logs`/storage). -/
def emptyObs (g : Option Nat) : SharedObservable :=
  { tag := "ok", output := [], gas := g, logs := [], storageAt := fun _ _ => 0 }

/-- **Concrete goal (smallest program).** A flat call `p` that completes with no
output, no logs and no storage writes observes as `emptyObs` (its own gas), and
this must `dataAgrees`-match the nested observable of the corresponding nested
`STOP` run (which is `emptyObs` with the nested gas). The only non-definitional
content is that *both engines actually reach the completed-empty state* for a
`STOP` program — i.e. `observe_flat (messageCall p) = emptyObs _` and likewise on
the nested side. -/
def equivGoalEmpty (p : CallParams) (nestedObs : SharedObservable) : Prop :=
  (observe_flat (flatSem.run p)) = emptyObs (observe_flat (flatSem.run p)).gas ∧
  nestedObs.dataAgrees (emptyObs nestedObs.gas) ∧
  (observe_flat (flatSem.run p)).storageAgrees nestedObs

/-- A fully-proved sanity lemma (no `sorry`): `emptyObs` always `dataAgrees`
itself modulo gas, and any two `emptyObs` agree pointwise on storage. This is the
load-bearing "do-nothing observable is canonical" fact the concrete equivalence
reduces to once both engines are shown to hit `emptyObs`. -/
theorem emptyObs_storageAgrees (g g' : Option Nat) :
    (emptyObs g).storageAgrees (emptyObs g') := by
  intro _ _; rfl

/-- `emptyObs` data-agrees with itself whenever the gas matches. Proved. -/
theorem emptyObs_dataAgrees (g : Option Nat) :
    (emptyObs g).dataAgrees (emptyObs g) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end BytecodeLayer
