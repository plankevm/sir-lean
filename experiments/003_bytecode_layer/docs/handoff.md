# Experiment 003 — handoff

Read [`results.md`](results.md) first, and [`docs/review-report.md`](review-report.md)
for the detailed module-by-module navigation surface (this file does not duplicate
its signatures). Both milestones (M1 call-free spine, M2 external calls) are
**proven, green, and axiom-clean** (`[propext, Classical.choice, Quot.sound]` on
every export). The two foundation obstructions an earlier run reported were resolved
upstream in leanevm (`9cefe5b`). This file records where the ladder reached, the
resolved obstructions, the reusable patterns to carry forward, and the build.

## Recent consolidation (latest pass)

No new results in this pass — the *legibility and economy* of the existing ones.
All green, axiom-clean, pushed:

- **Monolith retired.** `messageCall_call_eq` and its scaffolding (`child_run`,
  `callerResult`, `messageCall_child_reflexive`) are deleted; the `∃G₀`
  caller-storage spec now has exactly one proof, the compositional
  `messageCall_callerProg_storageAt`.
- **The CALL rule reads as a sequence.** `messageCall_call_runs` is now five
  structural hypotheses — `fr₀ ─Runs→ callFr ─CallReturns→ resumeFr ─Runs→ last
  ─halt` — with **no numeric fuel premise** (dropped; see the pattern below).
  `CallReturns callFr resumeFr` is a derived `def` bundling the three call-facts
  (call fires / callee enters as code / child terminates). Determined binders are
  implicit, so callers pass `p` + the five hypotheses.
- **Vocabulary surfaced.** The drive state's `.inl`/`.inr` → `running`/`finished`;
  the call-entry equation `beginCall p = .inl fr` → `EntersAsCode p fr`.
- **The fuel subsystem is named for what it is.** `Measure.lean` (μ, `mu_bound`)
  → `NeverOutOfFuel.lean` (the unconditional headline); the descent Prop
  `DescentDrops` → `gasFundsDescent` ("a descent is funded out of the parent's gas,
  with ≥2 to spare, so the measure still drops").
- **The 63/64 floor is derived,** via the universal `Gas.liftFloor` lemma, not an
  asserted magic constant (`liftFloor 22106 = 22457`; the example's 30000 is now
  justified, not hand-picked).
- **Docs + a guard.** `review-report.md`/`results.md`/this file regenerated to the
  current state; `scripts/check-report-links.sh` checks that every report link
  resolves (links are relative to the doc, so package source needs `../`) and that
  `#Lnn` anchors are in range — the `lean-review-report` agent now enforces both.

## Where the ladder reached (all ✅)

The architecture is a topic tree under `BytecodeLayer/` mirroring leanevm's
`Evm/Semantics/`. Bottom-up, the rungs that the headline rests on:

```
A  Observables           ✅  CallResult.observe / .storageAt            (Observables.lean)
B  drive vocabulary      ✅  drive_step / drive_halt / driveG_* / drive_fuel_mono / seedFuel
                             / messageCall_eq_drive                      (Semantics/Interpreter/Drive.lean)
B′ descent equation      ✅  drive_append_framing / drive_descend_eq     (Semantics/Interpreter/DescentEq.lean)
   never-out-of-fuel     ✅  μ / mu_bound (mod gasFundsDescent)          (Semantics/Interpreter/Measure.lean)
                         ✅  gasFundsDescent_holds → messageCall_never_outOfFuel
                                                                          (Semantics/Interpreter/NeverOutOfFuel.lean)
   step characterization ✅  stepFrame_push1/_sstore/_stop/_sstore_oog…  (Semantics/Dispatch.lean)
   System-op facts       ✅  stepFrame_call / beginCall_* / resumeAfterCall…  (Semantics/System.lean)
   63/64 arithmetic      ✅  Gas.liftFloor / …_ge_of_liftFloor_le; childGas_lb  (Semantics/Gas.lean, ExternalCall.lean)
C  Hoare core            ✅  Runs / Runs.trans / runs_push1/_push/_sstore / messageCall_runs  (Hoare.lean)
   sequencing gas        ✅  subCharges / toNat_subCharges               (Hoare/Sequence.lean)
   M1 capstones          ✅  messageCall_stop/_pushStop/_sstore/_seq_*   (Examples/ConcreteSpecs.lean ← ProgramExamples.lean)
─────────────────────────────────────────────────────────────────────
★  CALL sequencing rule  ✅  messageCall_call_runs / _completedWith      (Hoare/CallSequence.lean, re-exported Spec.lean)
   worked instantiation  ✅  messageCall_callerProg_storageAt            (Examples/CallerProgExample.lean)
   ∃G₀ spec (G₀ = 30000) ✅  messageCall_call_storageAt (delegates to ↑) (Examples/ConcreteSpecs.lean)
   ∃G₀ counterexample    ✅  call_counterexample (g = 24000 ⇒ cell = 0)  (Examples/ConcreteSpecs.lean ← ExternalCall.lean)
   audit surface         ✅  Spec.lean re-exports the general rules      (Spec.lean — "the file to read")
   axiom purity          ✅  every export = [propext, Classical.choice, Quot.sound]
```

The headline `messageCall_call_runs` is **sound and program-agnostic**: it
reconciles a black-box terminating child against the caller's actual suffix run
using `drive_descend_eq` + the unconditional `messageCall_never_outOfFuel` + fuel
monotonicity. No hypothesis is conclusion-shaped — the old circular
`behaves_call`/`CallerForwards`/`hforward` is **gone**, and the old monolith
`messageCall_call_eq` (with `child_run`/`callerResult`/`messageCall_child_reflexive`)
is **deleted**.

Fuel is not a hypothesis of the CALL rule at all: the never-out-of-fuel subsystem
(`μ`/`mu_bound`/`gasFundsDescent`) discharges it *unconditionally*, so the rule
runs the whole sequence at a large concrete fuel and reconciles back to
`seedFuel p.gas` internally — fuel appears in no exported statement. (The call-free
`messageCall_runs` still carries a `n + 2 ≤ seedFuel p.gas` premise; it could be
dropped the same way — see "where next".)

## The two obstructions — RESOLVED (record of the fix)

Both were `forks/leanevm` foundation issues, fixed by one endorsed upstream
commit `9cefe5b` ("Remove bv_decide axiom from the execution path; expose
callArm/createArm"), conformance unchanged (2859/2859):

1. **`bv_decide` axiom** — `blt_iff_toBitVec_lt` (`Evm/UInt256.lean`) reproved by
   reducing both sides to `Nat` (`BitVec.lt_def` + `toNat_limbs`) and an
   8-limb-lexicographic `omega`, keeping `blt`/`toBitVec`/the `Decidable` instances
   and the fast runtime path unchanged. `#print axioms Evm.messageCall` is now
   standard. (Spec lemmas off the execution path still use `bv_decide` — harmless.)
2. **`private callArm`/`createArm`** (`Evm/Semantics/System.lean`) made
   non-`private`, so `stepFrame_call` can `unfold callArm`.

If a future leanevm bump regresses either, re-applying the same two changes
upstream restores axiom purity and M2 reducibility.

## Reusable patterns confirmed this run (carry forward)

- **Sound CALL sequencing without a forwarding hypothesis — and without a fuel
  premise.** Bundle the three call-facts as `CallReturns callFr resumeFr`. The proof
  pattern: reduce `messageCall` to a `drive` equation; advance the caller's prefix
  with `Runs.drive_advance`; take the CALL step with `driveG_needsCall_code`; cross
  the child boundary with `drive_descend_eq` (black-box terminating child → resumed
  parent); build the suffix run; finish with `drive_eq_of_both_ne_oof`. **To drop the
  fuel-bound hypothesis:** don't run at `seedFuel p.gas` (that forces a `≤` premise) —
  run the whole sequence at a deliberately large *concrete* fuel `f*` (every split
  closes by `omega`, no bound assumed), then reconcile `f*` with `seedFuel p.gas` via
  `drive_eq_of_both_ne_oof` + `messageCall_never_outOfFuel` (it needs no fuel
  ordering). This is what replaces the circular `hforward`; reuse it for any
  caller/callee pair, and it's the lever for dropping fuel premises elsewhere.
- **`decode <bytes> <pc> = some (op, imm)` by `rfl`, as a named lemma** (per-pc
  facts in `Examples/ProgramDecode.lean`); inline it and `simp` won't fire under
  `getD`. The pc argument must be written exactly as `incrPC` produces it.
- **Advance `drive`**: top-level with `drive_step`/`drive_halt`; a *suspended* run
  (parent on the pending stack) with `driveG_step`/`driveG_halt_callDeliver`/
  `driveG_needsCall_code`. The `conv_lhs => unfold drive` guard against rewriting
  the RHS is baked into the lemmas (`Semantics/Interpreter/Drive.lean`).
- **Gas threading for sequences**: `subCharges g cs` + `toNat_subCharges`
  (`Hoare/Sequence.lean`) read the running `gasAvailable` after charges `cs` as
  `g.toNat - cs.sum`, so each step's gas/stipend side-goal is a one-line `omega`
  against a fixed prefix sum — avoids the quadratic blow-up of nested
  `toNat_sub_ofNat`.
- **The 63/64 cap** lives in `callGasCap`/`allButOneSixtyFourth`. Bound it through
  the *universal* `Gas.liftFloor` lemma: `allButOneSixtyFourth` clears a cost `C`
  once `n ≥ liftFloor C`, via `Gas.allButOneSixtyFourth_ge_of_liftFloor_le`
  (`Semantics/Gas.lean`). `childGas_lb` routes its success bound through it
  (`liftFloor 22106 = 22457`); `omega` finishes.
- **Stack-size side goals** over a `(…push v)` of a `default.stack`: reduce `.size`
  to a literal `Nat` and `omega` (free vars block `decide`).
- **`set_option … in` must go before the `/-- … -/` docstring.**
- **No `set_option maxHeartbeats` is needed anywhere** (the old monolith required a
  huge `maxHeartbeats`; the compositional rebuild does not). The concrete *example*
  files do carry `set_option maxRecDepth 4000` (`CallerProgExample.lean`,
  `ProgramExamples.lean`, `HoareDemo.lean`) to evaluate concrete gas constants on
  fixed witness programs — this is reduction depth on the witnesses, not a soundness
  concession, and the **general** rules use neither.

## Where a next experiment could go

The bytecode reasoning layer is now demonstrated end-to-end against the real
`messageCall`, including the hard case (external calls with the `∃G₀` gas story and
a *sound, program-agnostic* CALL rule), all axiom-clean. Natural next rungs, each
demand-driven:

- **Phrase one external-call export through `Behaves`/`Outcome`.** `Hoare/Behaves.lean`
  defines the for-all-programs predicate the generalization plan wants, but no
  exported theorem is yet phrased through it (it is scaffolding ahead of use).
  Routing the headline through it would retire the frame-level altitude caveat on
  `Spec.lean`.
- **A second, structurally different callee** (e.g. one that `RETURN`s) to widen the
  M2 witness beyond the single `callerProg`/`calleeProg` pair and one CALL site. The
  general rule is parametric and consumes the child as a black box; only the
  *instantiation* is currently one example.
- **Drop the fuel premise from `messageCall_runs` too** (the call-free bridge still
  carries `n + 2 ≤ seedFuel p.gas`), by the same large-`f*` + `messageCall_never_outOfFuel`
  reconciliation now used in `messageCall_call_runs` — for consistency, cheap.
- **Gas-sufficiency "piece 2": derive the floor per callee.** A small gas-Hoare
  judgment "callee `Q` run with gas ≥ `cost(Q)` commits effect `E`" would make the
  `∃G₀` floor `liftFloor (cost Q) + overhead` for *any* callee instead of hand-derived.
  Deferred until a second callee exists (with only one, the payoff is conceptual).
- **Squash the branch history** (`exp003-fuel-layer-cleanup`) — held for the lead's
  review; the WIP/rebuild intermediate commits can collapse to the clean end state.
- **Non-zero `value` / non-empty memory windows** in CALL (the value-free,
  zero-memory restriction was deliberate to isolate the 63/64 content; lifting it
  adds the value-transfer balance arithmetic and mem-expansion charge).
- **`RETURN`/`REVERT` output**, so `CallResult.output` carries non-empty bytes.
- **Nested calls / depth**, exercising `driveG_*` and the measure with a deeper
  pending stack.
- **A source IR → bytecode lowering** with these capstones as the target-side
  obligations (the original bytecode-first goal); the export shape (observables at
  the messageCall boundary, fuel/frame-free) is exactly what a lowering soundness
  theorem should land in.

## Build

`cd experiments/003_bytecode_layer && lake build` → **green, 1127 jobs, zero
warnings** (re-run for this regeneration). `lakefile.lean` globs
`.andSubmodules \`BytecodeLayer`. No `sorry`/`admit`/`native_decide`/`bv_decide`/
`maxHeartbeats` in any proof (the sole "sorry" match is a word in a `Maps.lean`
docstring).
