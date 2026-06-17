import BytecodeLayer.Reasoning.Begin
import BytecodeLayer.Reasoning.Step
import BytecodeLayer.Reasoning.Behaves
import BytecodeLayer.Observables
import BytecodeLayer.Programs
import BytecodeLayer.Proof.DecodeGas
import BytecodeLayer.Proof.Sequence

/-!
# Proof — an Outcome-from-success bridge lemma

`ofCall_completed_of_success` turns "`messageCall p` is `.ok r` with `r`
successful" into the named `Outcome.completed` predicate, so a straight-line proof
that lands a concrete `.ok r` can be read off on the audit surface.
-/

namespace BytecodeLayer.Proof
open Evm
open GasConstants

/-! ## Named-outcome bridges off a concrete `messageCall = .ok r`

Two small decoders turning "`messageCall p` is `.ok r` with `r` successful" into
the named `Outcome` predicates the rung lands on. Stated over the `CallResult`
`r` (not `endFrame`), so the per-program instances supply `r` already reduced. -/

/-- A successful `.ok r` makes `ofCall` a `completed` with `r`'s output and storage. -/
theorem ofCall_completed_of_success {p : CallParams} {r : CallResult}
    (hmc : messageCall p = .ok r) (hsucc : r.success = true) :
    Outcome.ofCall (messageCall p) = .completed r.output (CallResult.storageAt r) := by
  rw [hmc, Outcome.ofCall, Outcome.ofResult, if_pos hsucc]

end BytecodeLayer.Proof
