import BytecodeLayer.Drive
import BytecodeLayer.Step
import BytecodeLayer.Observables

/-!
# Capstone 1 — the call-free spine, in the shape we wanted

A handwritten program executed as a real `messageCall`, with the result stated
**only** through `CallResult.observe` (success + output). The statement is:

* **frame-free** — no `Frame`, `injectFrame`, pc, or stack;
* **fuel-free** — `seedFuel`/`drive`'s fuel never appears (it is discharged once,
  inside the proof, by `two_le_seedFuel` + `drive_halt`);
* **gas-honest by vacuity** — STOP charges nothing and the program reads no
  operands, so *no* `∃G₀` is needed and none is claimed: the equation holds for
  **every** `p` (any gas, including 0), which is exactly the honest statement for
  a gasless program. The quantitative `∃G₀` story is reserved for CALL.

The program is a single `STOP`. Out-of-range pcs decode to STOP, so the bare
empty program behaves identically; we use the explicit `0x00` byte for clarity.
The proof routes entirely through the characterization lemmas
(`stepFrame_stop`, `drive_halt`) — `messageCall`/`beginCall` are unfolded only to
expose the initial frame, never reasoned about structurally.
-/

namespace BytecodeLayer
open Evm

/-- The single-`STOP` program. -/
def stopProgram : ByteArray := ⟨#[0x00]⟩

theorem decode_stopProgram : decode stopProgram 0 = some (.System .STOP, .none) := by rfl

set_option maxHeartbeats 1000000 in
/-- **Capstone 1.** A message call into the single-`STOP` program succeeds with
empty output, for *any* call parameters whose code is `stopProgram` — no gas
floor required. Stated purely in observables. -/
theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  unfold messageCall
  unfold beginCall
  rw [hc]
  dsimp only
  rw [show seedFuel p.gas = (seedFuel p.gas - 2) + 2 by
        have := two_le_seedFuel p.gas; omega]
  rw [drive_halt _ _ _ (stepFrame_stop _ decode_stopProgram
        (le_of_eq_of_le (by rfl) (Nat.zero_le 1024)))]
  rfl

/-! ## A multi-instruction program — sequencing the run vocabulary

`PUSH1 0x05 ; STOP`. Now the run is two iterations: `drive_step` threads the
non-halting `PUSH1` (which charges `Gverylow = 3`), then `drive_halt` delivers
the `STOP`. This is where the **gas story first appears, and appears honestly**:
the equation needs `3 ≤ p.gas` — the exact intrinsic cost of the one charging
instruction — discharged once inside `stepFrame_push1`'s `if_neg`, never as an
`∃G₀` and never re-examined. Off the call path, gas is pure vacuity-propagation.
The result observables are unchanged (`success = true`, empty output): PUSH/STOP
have no observable effect, which is exactly what the projection should report. -/

/-- `PUSH1 0x05 ; STOP`. -/
def pushStopProgram : ByteArray := ⟨#[0x60, 0x05, 0x00]⟩

theorem decode_pushStop_0 :
    decode pushStopProgram 0 = some (.Push .PUSH1, some (5, 1)) := by rfl

theorem decode_pushStop_2 :
    decode pushStopProgram ((0 : UInt32) + UInt8.toUInt32 2) = some (.System .STOP, .none) := by rfl

set_option maxHeartbeats 4000000 in
/-- **Capstone 1′.** A message call into `PUSH1 0x05 ; STOP` succeeds with empty
output for every `p` with `3 ≤ p.gas` — the program's exact gas cost, stated as a
plain hypothesis rather than an `∃G₀`. Observables-only, frame-free, fuel-free;
the proof composes `drive_step` (the PUSH) and `drive_halt` (the STOP). -/
theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty } := by
  unfold messageCall
  unfold beginCall
  rw [hc]
  dsimp only
  rw [show seedFuel p.gas = ((seedFuel p.gas - 3) + 2) + 1 by
        have := two_le_seedFuel p.gas; unfold seedFuel at *; omega]
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 decode_pushStop_0 hg
        (by show (0 : ℕ) + 1 ≤ 1024; omega))]
  rw [drive_halt _ _ _ (stepFrame_stop _ decode_pushStop_2
        (le_of_eq_of_le (by rfl) (by omega : (1 : ℕ) ≤ 1024)))]
  rfl

end BytecodeLayer
