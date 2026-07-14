import BytecodeLayer.Equivalence
import BytecodeLayer.Programs
import BytecodeLayer.Examples.ProgramExamples
import BytecodeLayer.Examples.ProgramDecode

/-!
# The FLAT refinement half against the shared spec

The cross-engine equivalence is realized as **refinement through a shared spec**:
each engine independently proves its observable equals the canonical do-nothing
spec `emptyObs` for a do-nothing program, and cross-engine agreement is then a
meta-composition of the two refinements. This module discharges the **flat**
(`«evm»` / exp003) half for the smallest concrete program — a single `STOP` on a
funded account with enough gas.

The witness is a fully concrete `CallParams` (`stopParams`) whose
`codeSource = .Code stopProgram` over an account map carrying the recipient with
a `default` (empty-storage) account. `messageCall` of it reaches the
success-empty `CallResult` (success, empty output, no new logs, untouched
storage) via the already-proved `messageCall_runs` bridge with `Runs.refl` +
`stepFrame_stop`, so `observe_flat` reduces to `emptyObs` definitionally.

Gas is intentionally **non-load-bearing** here: the spec's `gas` field is set to
the observable's *own* gas, making that field equality `rfl`. Exact-gas equality
*across engines* is a deliberate follow-up (see the experiment report); this
theorem leaves gas as the engine's own value.
-/

namespace BytecodeLayer
open Evm
open BytecodeLayer.Examples
open BytecodeLayer.System
open BytecodeLayer.Dispatch

/-- The smallest do-nothing witness: a top-level `STOP` call on `addrA`, funded
with a `default` (empty-storage) account and `gas := 10` (STOP charges nothing,
so any gas suffices). Value-free, calldata-free, state-modifying, depth 0. -/
def stopParams : CallParams :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := #[]
    accounts := (∅ : AccountMap).insert addrA default
    originalAccounts := ∅
    substate := default
    caller := addrA
    origin := addrA
    recipient := addrA
    codeSource := .Code stopProgram
    gas := 10
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 0
    canModifyState := true }

/-- `messageCall stopParams` reaches the do-nothing success result: the entry
frame `Runs.refl`-halts on `STOP` (`stepFrame_stop`), crossed by the fuel-free
`messageCall_runs` bridge with `n = 0`. -/
theorem messageCall_stopParams :
    messageCall stopParams
      = .ok (FrameResult.toCallResult
          (endFrame (codeFrame stopParams stopProgram)
            (.success (codeFrame stopParams stopProgram).exec .empty))) := by
  exact Hoare.messageCall_runs stopParams
    (beginCall_code stopParams stopProgram rfl)
    (Hoare.Runs.refl _)
    (stepFrame_stop _ decode_stopProgram (by show (0:ℕ) ≤ 1024; omega))

/-- **The FLAT refinement.** The flat run of the do-nothing `STOP` call observes
as the canonical do-nothing spec `emptyObs` (with its own gas): `tag = "ok"`,
empty output, no logs, all-zero storage. Gas is non-load-bearing — the spec's
`gas` is the observable's own, so that field equality is `rfl`. -/
theorem flat_refines_emptyObs :
    (observe_flat (flatSem.run stopParams)).agrees
      (emptyObs (observe_flat (flatSem.run stopParams)).gas) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- tag
    show (observe_flat (flatSem.run stopParams)).tag = "ok"
    rw [show flatSem.run stopParams = messageCall stopParams from rfl, messageCall_stopParams]
    rfl
  · -- output
    show (observe_flat (flatSem.run stopParams)).output = []
    rw [show flatSem.run stopParams = messageCall stopParams from rfl, messageCall_stopParams]
    show SharedObservable.ofBytes ByteArray.empty = []
    simp [SharedObservable.ofBytes]
  · -- gas (rfl, non-load-bearing)
    rfl
  · -- logs
    show (observe_flat (flatSem.run stopParams)).logs = []
    rw [show flatSem.run stopParams = messageCall stopParams from rfl, messageCall_stopParams]
    rfl
  · -- storage, pointwise: the result's account map is the singleton `addrA ↦
    -- default`, whose storage is empty, so every cell reads `0`.
    intro addr key
    show (observe_flat (flatSem.run stopParams)).storageAt addr key = 0
    rw [show flatSem.run stopParams = messageCall stopParams from rfl, messageCall_stopParams]
    show (match ([(addrA, (default : Account))]).find? (fun p => p.1.val = addr) with
      | some p => (p.2.lookupStorage (UInt256.ofNat key)).toNat
      | none => 0) = 0
    simp only [List.find?_cons, List.find?_nil]
    by_cases h : (decide (addrA.val = addr)) = true
    · rw [h]
      show ((default : Account).lookupStorage (UInt256.ofNat key)).toNat = 0
      rw [show (default : Account).lookupStorage (UInt256.ofNat key) = 0 from rfl]; rfl
    · simp only [Bool.not_eq_true] at h; rw [h]

end BytecodeLayer
