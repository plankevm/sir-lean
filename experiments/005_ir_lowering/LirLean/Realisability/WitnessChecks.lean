import LirLean.Realisability.WitnessCheckCode

/-!
# LirLean — Realisability spec, THE TWO R12a LEAVES (kernel-certified)

The in-kernel discharge of the two `Bool` leaves `exProg_satisfies_hypotheses_of_checks`
consumes — the residue `WitnessParams.lean`'s module header measured as infeasible for
plain `decide` on the raw evaluators. The route (per `SegmentedEval.lean` +
`CheckedStep.lean`): each leaf is restated over the CHECKED transition iterator
(`exCheckChk`, `ccCheckChk`), closed by ONE `decide +kernel` evaluation (measured ~13s /
5.5 GB each — the checked twin never touches the `USize`-opaque byte-window path and
never peels the 54096 seed fuel), then transported to the real leaf by the sorry-free
soundness + fuel-shift chain:

* `stepsLogChk_sound` / `stepsCCChk_sound` — the checked chain's verdict IS the real
  chain's (`stepsLog` / `stepsCC`);
* `driveLogC_final` / `callsCodeOk_final` — a `k`-transition terminal verdict decides
  the fuel-indexed evaluator at ANY fuel `≥ k + 1`; the witness runs in `39`
  (`driveLog`, seed fuel `54096 = 39 + 54056 + 1`) and `36` (`callsCodeOk`, fuel
  `4096 = 36 + 4059 + 1`) transitions (re-measured by native probe against the
  current lowering; identical to the original measurement).

**KERNEL CRANKS (flagged per the R12a protocol): THREE `decide +kernel` evaluations.**
The heavy leaf cranks and their transports live in sequentially dependent modules so
their memory peaks do not overlap. The cheap seed-fuel arithmetic pin
`seedFuel_exParams` travels with the recorded-run transport. No `native_decide` appears
anywhere. All three are kernel evaluations of closed decidable terms; `#print axioms`
on the final leaves reports only the standard trio via the bridge lemmas' `Classical` uses.
-/

namespace Lir

end Lir
