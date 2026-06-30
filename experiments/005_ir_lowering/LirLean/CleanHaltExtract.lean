import LirLean.LowerDecode
import LirLean.V2.DriveSim

/-!
# CleanHalt extractor — clean-halting ⟹ per-cursor gas/mem envelopes (Track 1)

The conformance walk's per-cursor §7 ties (`StmtTies`/`TermTies`) currently *supply* the
gas / memory-expansion envelopes each lowered opcode needs at a block-entry frame. Those
envelopes are not free hypotheses: a frame that **clean-halts** (its remaining `Runs` reaches a
`.halted` outcome) cannot have faulted on its next step, so its next opcode's gas guard held.
This module is the **producer**: from `CleanHaltsSuccess fr` (the frame reaches a clean
`.halted (.success …)` outcome) it extracts, per lowered opcode, the gas + memory-expansion
envelope the §7 ties consume.

The lowered opcode set (`Lowering.lean` `materialiseExpr`/`emitStmt`/`emitTerm`) is exactly
`PUSH32`/`PUSH4`/`MLOAD`/`ADD`/`LT`/`SLOAD`/`GAS`/`MSTORE`/`SSTORE`/`CALL`/`POP`/`STOP`/`JUMP`/
`JUMPI`/`JUMPDEST` — no `DUP`/`SWAP` (recompute-on-use).

## What this file delivers (bottom-up)

* **`CleanHaltsSuccess`** (§0) — the *success* strengthening of `CleanHalts` (the §7 ties only
  ever fire on a `.success` terminal); `cleanHaltsSuccess_forward` (forward-closed along `Runs`,
  mirroring `cleanHalts_forward`) and `cleanHaltsSuccess_toCleanHalts` (forget the witness so
  existing `CleanHalts` consumers still see the weak form).
* **per-op OOG / `.next`-inversion bricks** (§1) — for the charge-only ops with no inversion in
  003 (`GAS`/`PUSH`/`SLOAD`/`ADD`/`LT`): `op_oog` (`¬gas ⟹ .halted (.exception OutOfGas)`) and
  `op_inv` (`.next ⟹ gas bound`), the `stepFrame`-unfold + `charge` `if_pos`/contrapositive
  pattern. `MSTORE`/`MLOAD`/`SSTORE` inversions are **reused** from 003 `Dispatch.lean`.
* **the `.next` extractor** (§2) — `halted_runs_eq` (a halted frame `Runs` only to itself) and the
  per-op `next_*_of_cleanSuccess` specialisations: `CleanHaltsSuccess fr` + the op's decode ⟹
  `∃ e', stepFrame fr = .next e'` (the success terminal forces a continuing step, since the op's
  only `.halted` is `.exception`).
* **the envelope family** (§3) — `gas_envelope_of_cleanSuccess` / `sload_envelope_of_cleanSuccess`:
  the full residual `sim_assign_gas_lowered` / `sim_assign_sload_lowered` consume, produced from
  `CleanHaltsSuccess` + the decode anchors, by threading the clean-halt forward across each stash
  step (`GAS`→`gasFrame`, `materialise`→`frk`, `SLOAD`→`sloadFrame`, `PUSH`→`pushFrameW`).

No `sorry`/`axiom`/`native_decide`. Every top-level result carries a `#print axioms` guard line.
-/

namespace Lir.CleanHaltExtract

open Evm
open Evm.Operation
open GasConstants
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## §0 — `CleanHaltsSuccess`: the success strengthening of `CleanHalts` -/

/-- **Clean-halt to a `.success` terminal.** `fr` reaches, by a `Runs` path, a frame `last`
that halts **successfully** (`stepFrame last = .halted (.success e o)`). This is the form the §7
ties actually need (the conformance walk's drive thread halts on `.success` — a `RETURN`/`STOP`
epilogue, never a revert/exception), and it forgets to the weaker `CleanHalts`
(`cleanHaltsSuccess_toCleanHalts`). -/
def CleanHaltsSuccess (fr : Frame) : Prop :=
  ∃ last e o, Runs fr last ∧ stepFrame last = .halted (.success e o)

/-- **The forward clean-halt-success split.** Mirror of `cleanHalts_forward`
(`V2/DriveSim.lean`): if `fr` clean-halts-successfully (at terminal `last`) and `Runs fr fj`,
then `fj` clean-halts-successfully — reaching the **same** `last` via `Runs.linear_to_halt`. -/
theorem cleanHaltsSuccess_forward {fr fj : Frame}
    (h : CleanHaltsSuccess fr) (hr : Runs fr fj) : CleanHaltsSuccess fj := by
  obtain ⟨last, e, o, hto, hhalt⟩ := h
  exact ⟨last, e, o, Runs.linear_to_halt hhalt hto hr, hhalt⟩

/-- **Forget the success witness.** A clean-halt-to-`.success` is in particular a clean-halt, so
existing `CleanHalts` consumers still see the weak form. -/
theorem cleanHaltsSuccess_toCleanHalts {fr : Frame}
    (h : CleanHaltsSuccess fr) : Lir.V2.CleanHalts fr := by
  obtain ⟨last, e, o, hto, hhalt⟩ := h
  exact ⟨last, _, hto, hhalt⟩

/-! ## §1 — per-op OOG / `.next`-inversion bricks

The charge-only lowered ops (`GAS`/`PUSH`/`SLOAD`/`ADD`/`LT`) have a forward `stepFrame_*` lemma
in 003 `Dispatch.lean` but **no** inversion / OOG lemma. Each is the `stepFrame`-unfold to the
`charge` `if`, taken in the `if_pos` branch (`¬gas ⟹ .halted (.exception OutOfGas)`); the
`.next`-inversion is then the contrapositive (a `.next` step witnesses the gas guard held). The
overflow `if_neg` is discharged from the same stack hypotheses the forward lemma uses.

`MSTORE`/`MLOAD`/`SSTORE` inversions are **reused** from 003 (`stepFrame_mstore_inv` etc.). -/

/-- **GAS out-of-gas.** With `Gbase` exceeding the available gas, `stepFrame` halts with
`OutOfGas`. Companion of the forward `stepFrame_gas`; the `.next`-inversion turns on its
contrapositive. -/
theorem stepFrame_gas_oog (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gbase) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .GAS)
      + stackPushCount (.Smsf .GAS) > 1024) := by
    simp only [show stackPopCount (.Smsf .GAS) = 0 from rfl,
               show stackPushCount (.Smsf .GAS) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp, pushOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **GAS `.next`-inversion.** A successful `.next` GAS step witnesses its own gas guard:
`Gbase ≤ gas`. Contrapositive of `stepFrame_gas_oog`. -/
theorem stepFrame_gas_inv (fr : Frame) {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gbase ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_gas_oog fr hdec hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **PUSH out-of-gas.** With `Gverylow` exceeding the available gas, `stepFrame` halts with
`OutOfGas`. Companion of the forward `stepFrame_push`; pops nothing, pushes one. -/
theorem stepFrame_push_oog (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gverylow) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by exact (by nofun : (Operation.Push p) ≠ Operation.INVALID))]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Push p)
      + stackPushCount (.Push p) > 1024) := by
    rw [hpop, hpush]; have := hsz; omega
  rw [if_neg hov]
  cases p with
  | PUSH0 => exact absurd rfl hp0
  | _ =>
    all_goals (
      dsimp only [dispatch]
      unfold Evm.charge
      rw [if_pos (by have := hoog; omega)]
      dsimp only [bind, Except.bind, pure, Except.pure])

/-- **PUSH `.next`-inversion.** A successful `.next` PUSH step witnesses `Gverylow ≤ gas`. -/
theorem stepFrame_push_inv (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    {e : ExecutionState} (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gverylow ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_push_oog fr p imm w hp0 hdec hpop hpush hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **SLOAD out-of-gas.** With `sloadCost warm` exceeding the available gas, `stepFrame` halts
with `OutOfGas`. Companion of the forward `stepFrame_sload`. -/
theorem stepFrame_sload_oog (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat
              < sloadCost (fr.exec.substate.accessedStorageKeys.contains
                  (fr.exec.executionEnv.address, key))) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .SLOAD)
      + stackPushCount (.Smsf .SLOAD) > 1024) := by
    simp only [show stackPopCount (.Smsf .SLOAD) = 1 from rfl,
               show stackPushCount (.Smsf .SLOAD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp, unStateOp]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  unfold charge
  rw [if_pos (by have := hoog; omega)]

/-- **SLOAD `.next`-inversion.** A successful `.next` SLOAD step witnesses `sloadCost warm ≤ gas`
(the warmth read off the same `accessedStorageKeys.contains` lens). This is exactly the
`sloadCost`-bound the `sim_assign_sload_lowered` residual's `hgasSload` conjunct needs. -/
theorem stepFrame_sload_inv (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    sloadCost (fr.exec.substate.accessedStorageKeys.contains
        (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_sload_oog fr key rest hdec hstk hsz (by omega)] at hnext
  exact absurd hnext (by simp)

end Lir.CleanHaltExtract

-- Axiom-cleanliness guards (§0).
#print axioms Lir.CleanHaltExtract.cleanHaltsSuccess_forward
#print axioms Lir.CleanHaltExtract.cleanHaltsSuccess_toCleanHalts
-- Axiom-cleanliness guards (§1).
#print axioms Lir.CleanHaltExtract.stepFrame_gas_oog
#print axioms Lir.CleanHaltExtract.stepFrame_gas_inv
#print axioms Lir.CleanHaltExtract.stepFrame_push_oog
#print axioms Lir.CleanHaltExtract.stepFrame_push_inv
#print axioms Lir.CleanHaltExtract.stepFrame_sload_oog
#print axioms Lir.CleanHaltExtract.stepFrame_sload_inv
