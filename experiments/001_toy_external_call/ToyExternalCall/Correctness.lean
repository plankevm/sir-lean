import ToyExternalCall.CallSound
import ToyExternalCall.GasErasure

/-!
# The exported lowering theorem

This file composes the two halves proved elsewhere into the statements meant
for outside consumption:

* `CallSound.lowering_exact` — bytecode under `EVM.X` *equals* the metered
  IR run, on the nose, at every gas and fuel level (zero assumptions);
* `run_erasure` — a successful gasless run is refined by the metered run on
  every sufficiently large gas budget, up to the remaining-gas counter.

The results:

* `lowering_correct` — the full-strength form: if the **gasless** IR run
  succeeds, then for every sufficiently large representable gas budget the
  lowered bytecode halts via its terminal `STOP` in a final state **equal on
  the nose** to the IR's final state — memory, accounts, storage, logs,
  return data, trace length — except the three frame fields `injectFrame`
  pins (pc, machine stack, executing code) and the leftover gas counter.
* `lowering_observables` — the boundary reading: the bytecode execution's
  observables (account map — hence all storage —, substate — hence all
  logs —, and output) are exactly the IR's. No `injectFrame` in sight.

Gas appears in the statements only as the quantified budget `G`: the IR
semantics is gasless, and the theorem promises nothing about under-funded
runs (`G < G₀` may produce `OutOfGass` or, subtler, a different but
*successful* execution — a callee starved by the 63/64 forwarding cap
returns flag `0` and the caller continues; see `docs/results-v2.md`).
That is precisely the freedom a gas-optimizing lowering needs.

Fuel is threaded identically on both sides (one unit per lowered opcode) and
still appears as `s.fuel`; eliminating it needs a fuel-monotonicity theorem
about EVMYulLean's interpreter stack — known debt, see the results doc.
-/

namespace ToyExternalCall

open EvmYul

/-- The initial bytecode state for running a lowered program: the IR state's
machine state, loaded with the lowered code at `pc = 0`, an empty stack, and
a gas budget of `G`. -/
def load (program : Program) (s : Exec) (G : Nat) : EVM.State :=
  injectFrame ((s.withGas (.ofNat G)).evm) (.ofNat 0) [] (Bytecode.lower program)

/-- **The lowering theorem.** A successful gasless IR run is reproduced by
the lowered bytecode under every sufficiently large representable gas
budget, up to the frame fields and the leftover gas. -/
theorem lowering_correct (program : Program) (vj : Array UInt256) (s s' : Exec)
    (hsize : (Bytecode.lower program).size < UInt256.size)
    (h : Gasless.run program s = .ok s') :
    ∃ G₀ : Nat, ∀ G : Nat, G₀ ≤ G → G < UInt256.size →
      ∃ gFin : Word,
        EVM.X s.fuel vj (load program s G) =
          .ok (.success
            (injectFrame ((s'.withGas gFin).evm)
              (.ofNat ((Bytecode.lower program).size - 1)) []
              (Bytecode.lower program))
            ByteArray.empty) := by
  obtain ⟨G₀, hG⟩ := run_erasure program s s' h
  refine ⟨G₀, fun G hle hlt => ?_⟩
  obtain ⟨gFin, hrun⟩ := hG G hle hlt
  refine ⟨gFin, ?_⟩
  have hx := lowering_exact program vj (s.withGas (.ofNat G)) hsize
  rw [hrun] at hx
  exact hx

/-- Contract-boundary observables of an execution: the account map (hence
all storage and balances), the substate (hence all logs, accessed sets and
refund counters), and the output bytes. Deliberately excluded: leftover gas,
the machine frame (pc/stack/code), memory (nothing reads it after a halt),
and fuel. -/
structure Observables where
  accounts : AccountMap .EVM
  substate : Substate
  output : ByteArray

/-- Observables of a bytecode execution result (`none` for exceptions and
reverts). -/
def observe : Except EVM.ExecutionException (EVM.ExecutionResult EVM.State) → Option Observables
  | .ok (.success st out) => some ⟨st.accountMap, st.substate, out⟩
  | _ => none

/-- Observables of a final IR state (the IR's terminal `STOP` produces empty
output). -/
def Exec.observables (s : Exec) : Observables :=
  ⟨s.evm.accountMap, s.evm.substate, ByteArray.empty⟩

/-- **The lowering theorem, observables form.** No `injectFrame`, no frame
fields, no gas in the conclusion: sufficiently funded, the lowered bytecode
produces exactly the gasless IR's observables. -/
theorem lowering_observables (program : Program) (vj : Array UInt256) (s s' : Exec)
    (hsize : (Bytecode.lower program).size < UInt256.size)
    (h : Gasless.run program s = .ok s') :
    ∃ G₀ : Nat, ∀ G : Nat, G₀ ≤ G → G < UInt256.size →
      observe (EVM.X s.fuel vj (load program s G)) = some s'.observables := by
  obtain ⟨G₀, hG⟩ := lowering_correct program vj s s' hsize h
  refine ⟨G₀, fun G hle hlt => ?_⟩
  obtain ⟨gFin, hx⟩ := hG G hle hlt
  rw [hx]
  rfl

end ToyExternalCall
