import Evm

/-!
# `LirLean.MemAlgebra` — memory-channel crux lemmas (feasibility study)

This file de-risks the three crux lemmas needed to add a *memory value channel*
to the bytecode-lowering correctness proof (MSTORE the CALL success flag to a
per-tmp slot, MLOAD it back on use).

The EVM memory model lives in the exp003 package
(`EVMLean/Evm/Machine/MachineStateOps.lean`): `mstore` calls `writeWord` →
`writeBytes` → `ByteArray.write`; `mload` calls `lookupMemory` →
`ByteArray.readWithPadding` → `fromByteArrayBigEndian`.

## Verdict (see the agent report for detail)

* **Lemma 3 — CALL preserves caller memory: PROVED** (below). The lowered CALL
  uses zero-size input *and* return windows; that makes `writeBytes … 0` a no-op
  on memory and `MachineState.M … 0` a no-op on `activeWords`, so an `MLOAD` at
  any fixed slot is preserved across `resumeAfterCall`.

* **Lemma 1 — MSTORE/MLOAD read-back: WALL (opaque FFI).** The round-trip flows
  through `ffi.ByteArray.zeroes`, which is `@[extern] opaque` (ffi.lean:18). Its
  `size` and byte contents are unprovable without axiomatising the FFI. `zeroes`
  appears on the write path (`ByteArray.write` padding), inside the very value
  being stored (`UInt256.toByteArray = zeroes (32-b.size) ++ b`), and on the read
  path (`readWithPadding`). There are NO existing lemmas/axioms about it
  anywhere in exp003. Lemma 1 is therefore left OUT of this (green) file.

* **Lemma 2 — disjointness: WALL (same opaque FFI), strictly harder than 1.**

Both lemmas 1 and 2 become *HARD-BUT-DOABLE* only if the project adopts two FFI
axioms characterising `zeroes` (size = n, bytes = 0) — a trust-surface decision
for the owner, not something to slip in here.
-/

open Evm

namespace LirLean.MemAlgebra

/-! ## Lemma 3 — CALL with a zero-size window preserves caller memory reads -/

/-- `mload .1` (i.e. `lookupMemory`) depends on the machine state only through
its `memory` and `activeWords` fields. -/
theorem mload_congr {m m' : MachineState} (slot : UInt256)
    (hmem : m.memory = m'.memory) (haw : m.activeWords = m'.activeWords) :
    (m.mload slot).1 = (m'.mload slot).1 := by
  unfold MachineState.mload MachineState.lookupMemory
  simp [hmem, haw]

/-- `resumeAfterCall` with a zero-size **return** window leaves the caller
frame's memory bytes untouched (`writeBytes _ _ _ _ 0 = self`). -/
theorem resumeAfterCall_memory {result : CallResult} {pd : PendingCall}
    (hout : pd.outSize = 0) :
    (resumeAfterCall result pd).exec.toMachineState.memory
      = pd.frame.exec.toMachineState.memory := by
  unfold resumeAfterCall ExecutionState.replaceStackAndIncrPC
  simp only [hout]
  unfold writeBytes ByteArray.write
  simp

/-- `resumeAfterCall` with zero-size **input and return** windows leaves the
caller frame's `activeWords` untouched (`M s f 0 = s` applied twice). -/
theorem resumeAfterCall_activeWords {result : CallResult} {pd : PendingCall}
    (hin : pd.inSize = 0) (hout : pd.outSize = 0) :
    (resumeAfterCall result pd).exec.toMachineState.activeWords
      = pd.frame.exec.toMachineState.activeWords := by
  unfold resumeAfterCall ExecutionState.replaceStackAndIncrPC
  simp only [hin, hout]
  unfold MachineState.M
  simp

/-- **CALL preserves caller memory.** The lowered CALL uses zero-size input and
return windows (`in_off = in_size = out_off = out_size = 0`, see
`LirLean/Lowering.lean:144`); under those hypotheses an `MLOAD` at any fixed slot
reads the same word before and after the call's resume. The zero-size return
window is exactly what makes the memory bytes survive (`writeBytes … 0`), and the
zero-size input window keeps `activeWords` (hence the `lookupMemory` bounds
guard) unchanged. -/
theorem resumeAfterCall_mload {result : CallResult} {pd : PendingCall}
    (hin : pd.inSize = 0) (hout : pd.outSize = 0) (slot : UInt256) :
    ((resumeAfterCall result pd).exec.toMachineState.mload slot).1
      = (pd.frame.exec.toMachineState.mload slot).1 :=
  mload_congr slot
    (resumeAfterCall_memory hout)
    (resumeAfterCall_activeWords hin hout)

end LirLean.MemAlgebra
