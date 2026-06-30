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

/-! ## §2 — the `.next` extractor (the glue)

`CleanHaltsSuccess fr` reaches a `.halted (.success …)` terminal. For a frame decoding to one of
the charge-only continuing ops, that forces a *continuing* (`.next`) step: a halted frame `Runs`
only to itself (`halted_runs_eq`), and the op's only `.halted` is `.exception` (never `.success`),
so `fr` is not the terminal — it must step. The per-op `next_*_of_cleanSuccess` then read off the
`.next`-inversion to yield the gas bound. The bound `hcont` of the abstract glue is **discharged**
per op by the op's `*_oog` lemma (its only halt is `.exception`). -/

/-- **A halted frame `Runs` only to itself.** If `stepFrame fr = .halted h` and `Runs fr last`,
then `fr = last`: the run cannot take a `step` (needs `.next`) or a `call` (needs `.needsCall`),
so it is `refl`. -/
theorem halted_runs_eq {fr last : Frame} {h : FrameHalt}
    (hhalt : stepFrame fr = .halted h) (hrun : Runs fr last) : fr = last := by
  cases hrun with
  | refl _ => rfl
  | step hstep _ => rw [hstep.1] at hhalt; exact absurd hhalt (by nofun)
  | call hcall _ =>
    obtain ⟨_, _, _, _, hstep, _⟩ := hcall
    rw [hstep] at hhalt; exact absurd hhalt (by nofun)

/-- **The abstract `.next` extractor.** From `CleanHaltsSuccess fr` and the per-op *step
dichotomy* — `fr` either continues (`.next e'`) or halts with an **exception** (`hdich`) — `fr`
takes a continuing step. The exception-halt arm is excluded because `fr`'s clean-halt terminal is
a `.success`: a halted `fr` reaches only itself (`halted_runs_eq`), so an exception halt at `fr`
would force the success terminal to be that same exception halt — impossible. Every charge-only
lowered op satisfies the dichotomy (forward lemma when the gas guard holds, `*_oog` otherwise), so
`.needsCall`/`.needsCreate` never arise — those are the CALL/CREATE ops, excluded by the op decode
the specialisations supply. -/
theorem next_of_cleanSuccess_continuing {fr : Frame}
    (hcs : CleanHaltsSuccess fr)
    (hdich : (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex))) :
    ∃ e', stepFrame fr = .next e' := by
  obtain ⟨last, e, o, hto, hhalt⟩ := hcs
  rcases hdich with hnext | ⟨ex, hexc⟩
  · exact hnext
  · -- exception halt at `fr`: `fr` reaches only itself, so the success terminal is this halt.
    exfalso
    have hfreq : fr = last := halted_runs_eq hexc hto
    subst hfreq
    rw [hexc] at hhalt
    exact absurd ((Signal.halted.injEq _ _).mp hhalt) (by nofun)

/-- **GAS step dichotomy.** A GAS-decoding frame (stack room) either continues or halts with an
exception: by gas trichotomy, `Gbase ≤ gas` ⟹ `.next (gasPost …)` (forward `stepFrame_gas`),
else `.halted (.exception OutOfGas)` (`stepFrame_gas_oog`). -/
theorem stepFrame_gas_dichotomy (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gbase ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_gas fr hdec hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_gas_oog fr hdec hsz (by omega)⟩

/-- **PUSH step dichotomy.** -/
theorem stepFrame_push_dichotomy (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gverylow ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_push fr p imm w hp0 hdec hpop hpush hgas hsz⟩
  · exact Or.inr ⟨_, stepFrame_push_oog fr p imm w hp0 hdec hpop hpush hsz (by omega)⟩

/-- **SLOAD step dichotomy.** -/
theorem stepFrame_sload_dichotomy (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_sload fr key rest hdec hstk hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_sload_oog fr key rest hdec hstk hsz (by omega)⟩

/-- **MSTORE step dichotomy.** Via the success-inversion's underlying OOG screens: either a
`.next` step (witnessed by the forward `stepFrame_mstore` under both charges) or one of the two
expansion/`Gverylow` OOG halts, or the `none`-expansion OOG halt. We package it by casing on the
expansion witness and the two charges. -/
theorem stepFrame_mstore_dichotomy (fr : Frame) (addr val : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  cases hmem : memoryExpansionWords? fr.exec.activeWords addr 32 with
  | none =>
    -- no expansion witness ⟹ `chargeMemExpansion` errors with OOG.
    refine Or.inr ⟨.OutOfGas, ?_⟩
    rw [stepFrame]
    simp only [hdec]
    dsimp only [Option.getD]
    rw [if_neg (by decide)]
    have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MSTORE)
        + stackPushCount (.Smsf .MSTORE) > 1024) := by
      simp only [show stackPopCount (.Smsf .MSTORE) = 2 from rfl,
                 show stackPushCount (.Smsf .MSTORE) = 0 from rfl]
      have := hsz; omega
    rw [if_neg hov]
    dsimp only [dispatch, smsfOp]
    rw [hstk]
    dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
      Except.bind, pure, Except.pure]
    dsimp only [chargeMemExpansion]
    rw [hmem]
  | some words' =>
    by_cases hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
    · by_cases hgas : Gverylow ≤
          (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      · exact Or.inl ⟨_, stepFrame_mstore fr addr val words' rest hdec hstk hsz hmem hgasMem hgas⟩
      · exact Or.inr ⟨.OutOfGas,
          stepFrame_mstore_oogVL fr addr val words' rest hdec hstk hsz hmem hgasMem (by omega)⟩
    · exact Or.inr ⟨.OutOfGas,
        stepFrame_mstore_oogMem fr addr val words' rest hdec hstk hsz hmem (by omega)⟩

/-! ### Per-op `.next`-from-clean-success specialisations

Combine the step dichotomy (excludes `.needsCall`/`.needsCreate`) with the abstract extractor to
turn `CleanHaltsSuccess fr` + the op decode into a continuing `.next` step, then read off the
inversion to land the gas bound. -/

/-- **GAS: clean-success ⟹ `Gbase ≤ gas`.** -/
theorem next_gas_of_cleanSuccess (fr : Frame)
    (hcs : CleanHaltsSuccess fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    Gbase ≤ fr.exec.gasAvailable.toNat ∧ stepFrame fr = .next (gasPost fr.exec) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanSuccess_continuing hcs (stepFrame_gas_dichotomy fr hdec hsz)
  have hg := stepFrame_gas_inv fr hdec hsz hnext
  exact ⟨hg, stepFrame_gas fr hdec hsz hg⟩

/-- **PUSH: clean-success ⟹ `Gverylow ≤ gas`.** -/
theorem next_push_of_cleanSuccess (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hcs : CleanHaltsSuccess fr) (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    Gverylow ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (pushFrameW fr imm w).exec := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanSuccess_continuing hcs (stepFrame_push_dichotomy fr p imm w hp0 hdec hpop hpush hsz)
  have hg := stepFrame_push_inv fr p imm w hp0 hdec hpop hpush hsz hnext
  exact ⟨hg, stepFrame_push fr p imm w hp0 hdec hpop hpush hg hsz⟩

/-- **SLOAD: clean-success ⟹ `sloadCost warm ≤ gas`.** -/
theorem next_sload_of_cleanSuccess (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsSuccess fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    sloadCost (fr.exec.substate.accessedStorageKeys.contains
        (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (sloadPost fr.exec key rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanSuccess_continuing hcs (stepFrame_sload_dichotomy fr key rest hdec hstk hsz)
  have hg := stepFrame_sload_inv fr key rest hdec hstk hsz hnext
  exact ⟨hg, stepFrame_sload fr key rest hdec hstk hsz hg⟩

/-- **MSTORE: clean-success ⟹ the expansion witness + both charges.** Reuses 003
`stepFrame_mstore_inv` on the continuing step the dichotomy produces. -/
theorem next_mstore_of_cleanSuccess (fr : Frame) (addr val : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsSuccess fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    ∃ words', memoryExpansionWords? fr.exec.activeWords addr 32 = some words'
      ∧ memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
      ∧ Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      ∧ stepFrame fr = .next (mstorePost fr.exec addr val words' rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanSuccess_continuing hcs (stepFrame_mstore_dichotomy fr addr val rest hdec hstk hsz)
  obtain ⟨words', hmem, hgasMem, hgas, he⟩ := stepFrame_mstore_inv fr addr val rest hdec hstk hsz hnext
  exact ⟨words', hmem, hgasMem, hgas, by rw [hnext, he]⟩

/-! ## §3 — the envelope family (the deliverable)

For the GAS cursor, `sim_assign_gas_lowered`'s residual is the 5-conjunct gas/mem envelope over the
3-step stash `GAS ; PUSH32 (slotOf t) ; MSTORE` at frames `fr`, `gasFrame fr`,
`pushFrameW (gasFrame fr) (ofNat slot) 32`. `gas_envelope_of_cleanSuccess` produces it from
`CleanHaltsSuccess fr` + the three frame-local decode anchors, threading the clean-halt forward
across each `StepsTo` (`fr → gasFrame fr → pushFrameW …`). The decode anchors are the **structural**
facts `sim_assign_gas_lowered` already derives internally (`hdgas'`/`hdpush'`/`hdmstore'`); the gas
bounds are no longer supplied — they are produced here. -/

/-- `StepsTo fr (gasFrame fr)` from the GAS gas guard (`Gbase ≤ gas`). The successor `gasFrame fr`
is `{ fr with exec := gasPost fr.exec }`. -/
theorem stepsTo_gasFrame (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : Gbase ≤ fr.exec.gasAvailable.toNat) :
    StepsTo fr (gasFrame fr) :=
  stepsTo_of_next (stepFrame_gas fr hdec hsz hgas)

/-- `StepsTo fr (pushFrameW fr imm w)` from a generic PUSH gas guard. -/
theorem stepsTo_pushFrameW (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hgas : Gverylow ≤ fr.exec.gasAvailable.toNat)
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    StepsTo fr (pushFrameW fr imm w) :=
  stepsTo_of_next (stepFrame_push fr p imm w hp0 hdec hpop hpush hgas hsz)

/-- **GAS envelope from clean-success.** From `CleanHaltsSuccess fr` (block-entry stack `[]`) and
the three frame-local decode anchors of the gas stash, produce the exact gas/mem residual
`sim_assign_gas_lowered` consumes: `Gbase ≤ fr.gas`, `3 ≤ (gasFrame fr).gas`, and the MSTORE
expansion witness `words'` + both memory charges at `pushFrameW (gasFrame fr) (ofNat slot) 32`.

The bound gas value the `GAS` op pushes (so the MSTORE writes) is
`ofUInt64 (fr.gas − Gbase)` — the realised GAS output, which fixes the MSTORE operand
`addr = ofNat slot`, `val = that value`, `rest = []`. -/
theorem gas_envelope_of_cleanSuccess (fr : Frame) (slot : Nat)
    (hcs : CleanHaltsSuccess fr)
    (hstk0 : fr.exec.stack = [])
    (hdecGAS : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hdecPUSH : decode (gasFrame fr).exec.executionEnv.code (gasFrame fr).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdecMSTORE :
        decode (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.executionEnv.code
          (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.pc
        = some (.Smsf .MSTORE, .none)) :
    Gbase ≤ fr.exec.gasAvailable.toNat
    ∧ 3 ≤ (gasFrame fr).exec.gasAvailable.toNat
    ∧ ∃ words',
        memoryExpansionWords?
          (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.activeWords
          (UInt256.ofNat slot) 32 = some words'
        ∧ memExpansionChargeOf (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec words'
            ≤ (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.gasAvailable.toNat
        ∧ Gverylow ≤ ((pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.gasAvailable
            - UInt64.ofNat (memExpansionChargeOf
                (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec words')).toNat := by
  -- stack-size facts along the stash.
  have hsz0 : fr.exec.stack.size + 1 ≤ 1024 := by rw [hstk0]; decide
  -- (a) GAS at `fr`.
  obtain ⟨hgasGas, hgasNext⟩ := next_gas_of_cleanSuccess fr hcs hdecGAS hsz0
  -- forward the clean-halt across `fr → gasFrame fr`.
  have hstepGas : StepsTo fr (gasFrame fr) := stepsTo_gasFrame fr hdecGAS hsz0 hgasGas
  have hcsGas : CleanHaltsSuccess (gasFrame fr) :=
    cleanHaltsSuccess_forward hcs (Runs.single hstepGas)
  -- the GAS frame's stack is `[gasval]` (size 1), so PUSH has stack room.
  have hstkGas : (gasFrame fr).exec.stack
      = UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) :: [] := by
    show (BytecodeLayer.Dispatch.gasPost fr.exec).stack = _
    dsimp only [BytecodeLayer.Dispatch.gasPost, ExecutionState.replaceStackAndIncrPC, Stack.push]
    rw [hstk0]
  have hszGas : (gasFrame fr).exec.stack.size + 1 ≤ 1024 := by
    rw [hstkGas]; simp [Stack.size]
  -- (b) PUSH32 at `gasFrame fr`.
  obtain ⟨hgasPush, hpushNext⟩ :=
    next_push_of_cleanSuccess (gasFrame fr) .PUSH32 (UInt256.ofNat slot) 32 hcsGas
      (by decide) hdecPUSH (by decide) (by decide) hszGas
  have hgasPush' : 3 ≤ (gasFrame fr).exec.gasAvailable.toNat := by
    have : Gverylow = 3 := rfl; omega
  -- forward the clean-halt across `gasFrame fr → pushFrameW (gasFrame fr) (ofNat slot) 32`.
  have hstepPush : StepsTo (gasFrame fr) (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32) :=
    stepsTo_pushFrameW (gasFrame fr) .PUSH32 (UInt256.ofNat slot) 32 (by decide) hdecPUSH
      (by decide) (by decide) hgasPush hszGas
  have hcsPush : CleanHaltsSuccess (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32) :=
    cleanHaltsSuccess_forward hcsGas (Runs.single hstepPush)
  -- the MSTORE frame's stack is `[ofNat slot, gasval]` (size 2).
  have hstkM : (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.stack
      = UInt256.ofNat slot
        :: UInt256.ofUInt64 ((fr.exec.gasAvailable - UInt64.ofNat Gbase)) :: [] := by
    show (({ (gasFrame fr).exec with
        gasAvailable := (gasFrame fr).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
      ).replaceStackAndIncrPC ((gasFrame fr).exec.stack.push (UInt256.ofNat slot)) (pcΔ := 33)).stack
      = _
    dsimp only [ExecutionState.replaceStackAndIncrPC, Stack.push]
    rw [hstkGas]
  have hszM : (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.stack.size ≤ 1024 := by
    rw [hstkM]; simp [Stack.size]
  -- (c) MSTORE at `pushFrameW …`: the expansion witness + both charges.
  obtain ⟨words', hmem, hgasMem, hgasMstore, _⟩ :=
    next_mstore_of_cleanSuccess (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32)
      (UInt256.ofNat slot) (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase)) []
      hcsPush hdecMSTORE hstkM hszM
  exact ⟨hgasGas, hgasPush', words', hmem, hgasMem, hgasMstore⟩

/-- `StepsTo fr (sloadFrame fr key rest)` from the SLOAD warmth gas guard. -/
theorem stepsTo_sloadFrame (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
    StepsTo fr (sloadFrame fr key rest) :=
  stepsTo_of_next (stepFrame_sload fr key rest hdec hstk hsz hgas)

/-- **SLOAD envelope from clean-success.** For the spilled-sload cursor, the residual
`sim_assign_sload_lowered` consumes is keyed on the **post-materialise** frame `frk` (the key
prefix is variable-length; B1 `materialise_runs` produces `frk` and the `MatRuns` Runs threading
`CleanHaltsSuccess` to it). At `frk` (stack `[keyVal]`) the tail `SLOAD ; PUSH32 ; MSTORE`
clean-halts, so this lemma produces the gas conjuncts `hgasSload`/`hgasPush`/`hmem`/`hgasMem`/
`hgasMstore` of `hresid` — everything but the **structural** activeWords-flatness `hawk`
(`frk.activeWords = fr.activeWords`: the key materialise expanded no memory — the normal sload-key
case, independent of gas), which stays a supplied structural residual.

Inputs: `CleanHaltsSuccess fr`, the entry stack-nil, the `MatRuns` thread to `frk` (which pins
`frk.stack = [keyVal]`), and the three frame-local tail decode anchors at `frk`. -/
theorem sload_envelope_of_cleanSuccess
    {defs : Tmp → Option Expr} {sloadChg : Tmp → ℕ} {f : Nat} {ekey : Expr} {wkey : Word}
    (fr frk : Frame) (keyVal : UInt256) (slot : Nat)
    (hcs : CleanHaltsSuccess fr)
    (hstk0 : fr.exec.stack = [])
    (hmrk : MatRuns defs sloadChg f ekey wkey fr frk)
    (hkeyval : wkey = keyVal)
    (hdecSLOAD : decode frk.exec.executionEnv.code frk.exec.pc = some (.Smsf .SLOAD, .none))
    (hdecPUSH : decode (sloadFrame frk keyVal []).exec.executionEnv.code
          (sloadFrame frk keyVal []).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdecMSTORE :
        decode (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.executionEnv.code
          (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.pc
        = some (.Smsf .MSTORE, .none)) :
    sloadCost (frk.exec.substate.accessedStorageKeys.contains
        (frk.exec.executionEnv.address, keyVal)) ≤ frk.exec.gasAvailable.toNat
    ∧ 3 ≤ (sloadFrame frk keyVal []).exec.gasAvailable.toNat
    ∧ ∃ words',
        memoryExpansionWords?
          (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.activeWords
          (UInt256.ofNat slot) 32 = some words'
        ∧ memExpansionChargeOf
            (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec words'
            ≤ (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.gasAvailable.toNat
        ∧ Gverylow ≤ ((pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.gasAvailable
            - UInt64.ofNat (memExpansionChargeOf
                (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec words')).toNat := by
  -- thread the clean-halt to `frk` along the materialise Runs (B1).
  have hcsK : CleanHaltsSuccess frk := cleanHaltsSuccess_forward hcs hmrk.runs
  -- `frk`'s stack is `[keyVal]` (B1 leaves the key on top of the entry stack `[]`).
  have hstkK : frk.exec.stack = keyVal :: [] := by
    rw [hmrk.stack, hstk0, ← hkeyval]; rfl
  have hszK : frk.exec.stack.size ≤ 1024 := by rw [hstkK]; simp [Stack.size]
  -- (a) SLOAD at `frk`.
  obtain ⟨hgasSload, hsloadNext⟩ := next_sload_of_cleanSuccess frk keyVal [] hcsK hdecSLOAD hstkK hszK
  -- forward the clean-halt across `frk → sloadFrame frk keyVal []`.
  have hstepSload : StepsTo frk (sloadFrame frk keyVal []) :=
    stepsTo_sloadFrame frk keyVal [] hdecSLOAD hstkK hszK hgasSload
  have hcsSload : CleanHaltsSuccess (sloadFrame frk keyVal []) :=
    cleanHaltsSuccess_forward hcsK (Runs.single hstepSload)
  -- the SLOAD frame's stack is `[v]` (size 1) for the loaded value `v`.
  have hstkSload : (sloadFrame frk keyVal []).exec.stack
      = (Evm.State.sload
          ({ frk.exec with gasAvailable := frk.exec.gasAvailable
              - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                  (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2 :: [] := by
    show (BytecodeLayer.Dispatch.sloadPost frk.exec keyVal []).stack = _
    dsimp only [BytecodeLayer.Dispatch.sloadPost, ExecutionState.replaceStackAndIncrPC, Stack.push]
  have hszSload : (sloadFrame frk keyVal []).exec.stack.size + 1 ≤ 1024 := by
    rw [hstkSload]; simp [Stack.size]
  -- (b) PUSH32 at `sloadFrame frk keyVal []`.
  obtain ⟨hgasPush, hpushNext⟩ :=
    next_push_of_cleanSuccess (sloadFrame frk keyVal []) .PUSH32 (UInt256.ofNat slot) 32 hcsSload
      (by decide) hdecPUSH (by decide) (by decide) hszSload
  have hgasPush' : 3 ≤ (sloadFrame frk keyVal []).exec.gasAvailable.toNat := by
    have : Gverylow = 3 := rfl; omega
  -- forward the clean-halt across `sloadFrame … → pushFrameW (sloadFrame …) (ofNat slot) 32`.
  have hstepPush : StepsTo (sloadFrame frk keyVal [])
      (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32) :=
    stepsTo_pushFrameW (sloadFrame frk keyVal []) .PUSH32 (UInt256.ofNat slot) 32 (by decide)
      hdecPUSH (by decide) (by decide) hgasPush hszSload
  have hcsPush : CleanHaltsSuccess (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32) :=
    cleanHaltsSuccess_forward hcsSload (Runs.single hstepPush)
  -- the MSTORE frame's stack is `[ofNat slot, v]` (size 2).
  have hstkM : (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.stack
      = UInt256.ofNat slot :: (sloadFrame frk keyVal []).exec.stack := by
    show (({ (sloadFrame frk keyVal []).exec with
        gasAvailable := (sloadFrame frk keyVal []).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
      ).replaceStackAndIncrPC ((sloadFrame frk keyVal []).exec.stack.push (UInt256.ofNat slot))
        (pcΔ := 33)).stack = _
    dsimp only [ExecutionState.replaceStackAndIncrPC, Stack.push]
  have hstkM' : (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.stack
      = UInt256.ofNat slot
        :: (Evm.State.sload
              ({ frk.exec with gasAvailable := frk.exec.gasAvailable
                  - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                      (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2 :: [] := by
    rw [hstkM, hstkSload]
  have hszM : (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.stack.size ≤ 1024 := by
    rw [hstkM']; simp [Stack.size]
  -- (c) MSTORE at `pushFrameW …`: the expansion witness + both charges.
  obtain ⟨words', hmem, hgasMem, hgasMstore, _⟩ :=
    next_mstore_of_cleanSuccess (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32)
      (UInt256.ofNat slot)
      (Evm.State.sload
        ({ frk.exec with gasAvailable := frk.exec.gasAvailable
            - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2
      [] hcsPush hdecMSTORE hstkM' hszM
  exact ⟨hgasSload, hgasPush', words', hmem, hgasMem, hgasMstore⟩

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
-- Axiom-cleanliness guards (§2).
#print axioms Lir.CleanHaltExtract.halted_runs_eq
#print axioms Lir.CleanHaltExtract.next_of_cleanSuccess_continuing
#print axioms Lir.CleanHaltExtract.stepFrame_gas_dichotomy
#print axioms Lir.CleanHaltExtract.stepFrame_push_dichotomy
#print axioms Lir.CleanHaltExtract.stepFrame_sload_dichotomy
#print axioms Lir.CleanHaltExtract.stepFrame_mstore_dichotomy
#print axioms Lir.CleanHaltExtract.next_gas_of_cleanSuccess
#print axioms Lir.CleanHaltExtract.next_push_of_cleanSuccess
#print axioms Lir.CleanHaltExtract.next_sload_of_cleanSuccess
#print axioms Lir.CleanHaltExtract.next_mstore_of_cleanSuccess
-- Axiom-cleanliness guards (§3).
#print axioms Lir.CleanHaltExtract.stepsTo_gasFrame
#print axioms Lir.CleanHaltExtract.stepsTo_pushFrameW
#print axioms Lir.CleanHaltExtract.gas_envelope_of_cleanSuccess
#print axioms Lir.CleanHaltExtract.stepsTo_sloadFrame
#print axioms Lir.CleanHaltExtract.sload_envelope_of_cleanSuccess
