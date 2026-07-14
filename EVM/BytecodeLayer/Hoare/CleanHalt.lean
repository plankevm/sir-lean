import BytecodeLayer.Hoare

/-!
# Clean-halt scope predicates (`CleanHalts`, `CleanHaltsNonException`)

These predicates record that a frame's remaining run **terminates cleanly**. Two strengths are
used:

* **`CleanHalts fr`** — the run reaches *some* `.halted` outcome (the standing well-foundedness
  witness threaded through the drive recursion; its `totalGas` is the recursion measure).
* **`CleanHaltsNonException fr`** — the run reaches a `.halted` outcome that is **not** an
  `.exception` (`.success` or `.revert`). This is the honest scope boundary for the gas-agnostic
  IR: a genuine OOG/exception run cannot be modelled, so it falls outside conformance, but a
  `RETURN`/`STOP` epilogue *and* a `REVERT` (which reaches its terminal with gas to spare) are in
  scope. The non-exception strengthening is what lets the per-cursor §7 extractor
  (`CleanHaltExtract`) DERIVE each lowered opcode's gas/memory-expansion envelope, instead of
  supplying it: a continuing op's only `.halted` is `.exception`, so a cursor frame can never
  coincide with a non-exception terminal — it must step, witnessing its own gas guard.

The forward split (`cleanHalts_forward` / `cleanHaltsNonException_forward`) is the linearity of the
halting `Runs` path: `stepFrame` is a function, so `Runs.linear_to_halt` gives that every frame
reachable on the way to a halt continues to the
**same** halt. Clean-halting is therefore forward-closed along `Runs`.

No `sorry`/`axiom`/`native_decide`.
-/

namespace BytecodeLayer.Hoare

open Evm
open BytecodeLayer.Hoare

/-- **Clean-halt of a frame's remaining run.** `fr` reaches, by a run of opcode steps and
returning external calls (`Runs`), a frame `last` that **halts** (`stepFrame last = .halted
halt`). The bytecode side of the drive base case (`STOP`/`RETURN`), and the standing
well-foundedness witness threaded through the drive recursion. -/
def CleanHalts (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt

/-- A `FrameHalt` is **non-exception** iff it is not an `.exception`. -/
def HaltNonException : Evm.FrameHalt → Prop
  | .exception _ => False
  | _ => True

/-- A `.success` terminal is non-exception. -/
theorem haltNonException_success (e : Evm.ExecutionState) (o : ByteArray) :
    HaltNonException (.success e o) := trivial

/-- A `.revert` terminal is non-exception. -/
theorem haltNonException_revert (g : UInt64) (o : ByteArray) :
    HaltNonException (.revert g o) := trivial

/-- **Clean-halt to a non-exception terminal.** `fr` reaches, by a `Runs` path, a frame `last`
that halts to a **non-exception** outcome (`.success` or `.revert`, NOT `.exception`). The honest
scope boundary for the gas-agnostic IR: a genuine OOG/exception run is un-modellable and falls
outside conformance; a `RETURN`/`STOP` epilogue and a `REVERT` are in scope. Forgets to the weaker
`CleanHalts` (`cleanHaltsNonException_toCleanHalts`). -/
def CleanHaltsNonException (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt ∧ HaltNonException halt

/-- **The forward clean-halt split.** If `fr` clean-halts (at terminal `last`) and `Runs fr fj`,
then `fj` clean-halts — reaching the **same** `last`. The drive recursion threads a single
whole-run clean-halt witness from the entry frame and propagates it to each block successor through
this lemma, rather than supplying a fresh `CleanHalts` per edge. -/
theorem cleanHalts_forward {fr fj : Frame}
    (hclean : CleanHalts fr) (hreach : Runs fr fj) : CleanHalts fj := by
  obtain ⟨last, halt, hto, hhalt⟩ := hclean
  exact ⟨last, halt, Runs.linear_to_halt hhalt hto hreach, hhalt⟩

/-- **The forward non-exception clean-halt split.** The `CleanHaltsNonException` analogue of
`cleanHalts_forward`: if `fr` clean-halts non-exceptionally (at terminal `last`) and `Runs fr fj`,
then `fj` clean-halts non-exceptionally — reaching the **same** `last` (so the same non-exception
witness). The drive recursion / the statement-list induction thread a single whole-run
non-exception clean-halt witness from the entry frame and propagate it to each block successor /
each statement cursor through this lemma. -/
theorem cleanHaltsNonException_forward {fr fj : Frame}
    (hclean : CleanHaltsNonException fr) (hreach : Runs fr fj) : CleanHaltsNonException fj := by
  obtain ⟨last, halt, hto, hhalt, hne⟩ := hclean
  exact ⟨last, halt, Runs.linear_to_halt hhalt hto hreach, hhalt, hne⟩

/-- **Forget the non-exception witness.** A non-exception clean-halt is in particular a clean-halt,
so the existing `CleanHalts` consumers (the `totalGas` measure, the drive recursion) still see the
weak form. -/
theorem cleanHaltsNonException_toCleanHalts {fr : Frame}
    (h : CleanHaltsNonException fr) : CleanHalts fr := by
  obtain ⟨last, halt, hto, hhalt, _⟩ := h
  exact ⟨last, halt, hto, hhalt⟩

/-- **`.success` clean-halt ⟹ `CleanHaltsNonException`.** The success-only case (the drive
thread's `RETURN`/`STOP` epilogue) is the canonical non-exception clean-halt; kept derivable so
success-specific callers can build the witness. -/
theorem cleanHaltsNonException_of_success {fr last : Frame} {e : Evm.ExecutionState}
    {o : ByteArray} (hto : Runs fr last) (hhalt : stepFrame last = .halted (.success e o)) :
    CleanHaltsNonException fr :=
  ⟨last, .success e o, hto, hhalt, haltNonException_success e o⟩

end BytecodeLayer.Hoare

-- Build-enforced axiom-cleanliness guards.
