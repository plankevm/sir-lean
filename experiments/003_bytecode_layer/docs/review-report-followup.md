# Review report follow-up

Report is at [docs/review-report.md](docs/review-report.md) — 244 lines, properly formatted (7 fenced Lean blocks, ~48 file:line links), so the convention works. Both substantive findings were independently confirmed.

## Executive summary (from the report)

- The circular rung is genuinely gone and replaced by a real theorem. Zero `CallerForwards`/`behaves_call`/`hforward` is present anywhere; `messageCall_call_runs` consumes the callee as a black-box terminating run and the caller via honest `Runs` traces. No hypothesis is conclusion-shaped, and the forwarding fact that was `hforward` is now derived in-proof via `drive_descend_eq` plus the now-live `messageCall_never_outOfFuel`. The two prior smells (the dead never-out-of-fuel island and the cranked `maxHeartbeats`) are both resolved.

## Two findings worth your call (both verified)

1. The compositional exercise is orphaned. `Examples/CallerProgExample.lean` is imported by nothing — it compiles only via the lakefile's `.andSubmodules` glob, so the rule is exercised-and-checked but unreachable from the Spec audit surface.

2. The monolith retirement is only half-done. I removed its `maxHeartbeats`, but the giant `messageCall_call_eq` proof still exists in `ExternalCall.lean`, and it is still what the Spec-reachable concrete fact uses:
   `ConcreteSpecs.messageCall_call_storageAt → ExternalCall.messageCall_call_storageAt → messageCall_call_eq`.
   So the caller-storage fact now has two proofs — the monolith (reachable) and the new compositional one (orphaned). The compositional path does not actually replace the monolith on the surface yet.

## Plus a doc note

`docs/results.md` and `docs/handoff.md` carry stale pre-rebuild `#print axioms`/job-count evidence (old un-namespaced names, missing the three rebuild headlines). That is Phase-4 doc-rewrite territory.

## Recommendation

Finish the retirement properly: re-point `ConcreteSpecs.messageCall_call_storageAt` to the compositional `messageCall_callerProg_storageAt` (it is actually stronger — floor `g ≥ 30000` vs the monolith's `100000`), wire `CallerProgExample` into the reachable surface, then delete `messageCall_call_eq` and any now-dead concrete drive-reduction lemmas (after checking `call_counterexample` etc. do not depend on them). That collapses the duplicate, makes the compositional proof the real one, and genuinely retires the monolith.

Would you like me to do that cleanup now? It is the natural completion of “retire the monolith,” but it deletes a chunk of `ExternalCall.lean`, so I’d rather confirm than assume.

The stale `results.md`/`handoff.md` updates would be folded into Phase 4 unless you want them fixed now.
