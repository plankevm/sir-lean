import LirLean.Materialise.MatDecLower
import LirLean.Engine.CleanHalt

/-!
# CleanHalt extractor — clean-halting ⟹ per-cursor gas/mem envelopes (Track 1)

The conformance walk's per-cursor §7 ties (the former `StmtTies`/`TermTies`, since reshaped
into the run-DERIVED `StmtTies'`/`TermTies'` in `V2/RealisabilitySpec.lean`) *supply* the
gas / memory-expansion envelopes each lowered opcode needs at a block-entry frame. Those
envelopes are not free hypotheses: a frame that **clean-halts** (its remaining `Runs` reaches a
`.halted` outcome) cannot have faulted on its next step, so its next opcode's gas guard held.
This module is the **producer**: from `CleanHaltsNonException fr` (the frame reaches a clean
`.halted` outcome that is **not** an `.exception` — `.success` or `.revert`) it extracts, per
lowered opcode, the gas + memory-expansion envelope the §7 ties consume.

The lowered opcode set (`Lowering.lean` `materialiseExpr`/`emitStmt`/`emitTerm`) is exactly
`PUSH32`/`PUSH4`/`MLOAD`/`ADD`/`LT`/`SLOAD`/`GAS`/`MSTORE`/`SSTORE`/`CALL`/`POP`/`STOP`/`JUMP`/
`JUMPI`/`JUMPDEST` — no `DUP`/`SWAP` (recompute-on-use).

## What this file delivers (bottom-up)

* **`CleanHaltsNonException`** (§0) — the *non-exception* strengthening of `CleanHalts` (the §7
  ties only ever fire on a run that reaches its terminal cleanly — `.success` or `.revert`, never
  a genuine OOG/exception); `cleanHaltsNonException_forward` (forward-closed along `Runs`,
  mirroring `cleanHalts_forward`) and `cleanHaltsNonException_toCleanHalts` (forget the witness so
  existing `CleanHalts` consumers still see the weak form). `cleanHaltsNonException_of_success`
  keeps the success-only case derivable.
* **per-op OOG / `.next`-inversion bricks** (§1) — for the charge-only ops with no inversion in
  003 (`GAS`/`PUSH`/`SLOAD`/`ADD`/`LT`): `op_oog` (`¬gas ⟹ .halted (.exception OutOfGas)`) and
  `op_inv` (`.next ⟹ gas bound`), the `stepFrame`-unfold + `charge` `if_pos`/contrapositive
  pattern. `MSTORE`/`MLOAD`/`SSTORE` inversions are **reused** from 003 `Dispatch.lean`.
* **the `.next` extractor** (§2) — `halted_runs_eq` (a halted frame `Runs` only to itself) and the
  per-op `next_*_of_cleanHalt` specialisations: `CleanHaltsNonException fr` + the op's decode ⟹
  `∃ e', stepFrame fr = .next e'` (the non-exception terminal forces a continuing step, since the
  op's only `.halted` is `.exception`).
* **the envelope family** (§3) — `gas_envelope_of_cleanHalt` / `sload_envelope_of_cleanHalt`:
  the full residual `sim_assign_gas_lowered` / `sim_assign_sload_lowered` consume, produced from
  `CleanHaltsNonException` + the decode anchors, by threading the clean-halt forward across each
  stash step (`GAS`→`gasFrame`, `materialise`→`frk`, `SLOAD`→`sloadFrame`, `PUSH`→`pushFrameW`).

No `sorry`/`axiom`/`native_decide`. Every top-level result carries a `#print axioms` guard line.
-/

namespace Lir.CleanHaltExtract

open Evm
open Evm.Operation
open GasConstants
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## §0 — `CleanHaltsNonException` (defined in `V2/DriveSim.lean`)

`CleanHalts` allows the run to reach **any** `.halted` outcome, including `.exception` (a genuine
OOG/exception run, which the gas-agnostic IR cannot model). The §7 ties only ever fire on a run
that reaches its terminal **cleanly** — a `.success` (`RETURN`/`STOP` epilogue) *or* a `.revert`
(a revert reaches its terminal with gas to spare). Both share the one property the extractor's
core argument needs: the terminal is **not** `.exception`. A continuing op's only `.halted` is
`.exception`, so a cursor frame can never coincide with a non-exception terminal — it must step.

`CleanHaltsNonException` (and its forward split `cleanHaltsNonException_forward`, the weakening
`cleanHaltsNonException_toCleanHalts`, and the success special case
`cleanHaltsNonException_of_success`) live in `LirLean/Engine/CleanHalt.lean` — upstream of both this
extractor and the drive walk. Open `Lir.V2` brings them into scope here. -/

open Lir.V2 (CleanHaltsNonException cleanHaltsNonException_forward HaltNonException)

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

/-! ### ADD / LT / MLOAD OOG / inversion bricks (the FoldLemma additions)

The aggregate gas-FOLD residuals (`materialise_runs_of_cleanHalt`) descend the materialise run
through `ADD`/`LT` (binary-op tails) and the `MLOAD` readback of a `.slot`-spilled tmp. Those ops
have a forward `stepFrame_add`/`stepFrame_lt`/`stepFrame_mload` in 003 but no inversion/OOG lemma,
so we build them here, copying the GAS/PUSH/SLOAD pattern above: the `binOp` charges `Gverylow`
*before* popping (no `hstk` needed for OOG); `MLOAD` mirrors the MSTORE `memExpansion + Gverylow`
double-charge (`stepFrame_mstore_oogMem`/`_oogVL` shape). -/

/-- **ADD out-of-gas.** With `Gverylow` exceeding the available gas, `stepFrame` halts with
`OutOfGas` at the `binOp` charge (which fires before the pop). Companion of `stepFrame_add`. -/
theorem stepFrame_add_oog (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (_hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gverylow) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by nofun)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.ArithLogic .ADD)
      + stackPushCount (.ArithLogic .ADD) > 1024) := by
    simp only [show stackPopCount (.ArithLogic .ADD) = 2 from rfl,
               show stackPushCount (.ArithLogic .ADD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, binOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **ADD `.next`-inversion.** A successful `.next` ADD step witnesses `Gverylow ≤ gas`. -/
theorem stepFrame_add_inv (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gverylow ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_add_oog fr a b rest hdec hstk hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **LT out-of-gas.** Mirror of `stepFrame_add_oog` for `LT`. -/
theorem stepFrame_lt_oog (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (_hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gverylow) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by nofun)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.ArithLogic .LT)
      + stackPushCount (.ArithLogic .LT) > 1024) := by
    simp only [show stackPopCount (.ArithLogic .LT) = 2 from rfl,
               show stackPushCount (.ArithLogic .LT) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, binOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **LT `.next`-inversion.** A successful `.next` LT step witnesses `Gverylow ≤ gas`. -/
theorem stepFrame_lt_inv (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gverylow ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_lt_oog fr a b rest hdec hstk hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **MLOAD no-expansion-witness OOG.** When `memoryExpansionWords?` is `none`, `MLOAD` halts at
`chargeMemExpansion` with `OutOfGas`. Mirror of `stepFrame_mstore` `none` arm (the readback
analogue). -/
theorem stepFrame_mload_oogNone (fr : Frame) (addr : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = none) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MLOAD)
      + stackPushCount (.Smsf .MLOAD) > 1024) := by
    simp only [show stackPopCount (.Smsf .MLOAD) = 1 from rfl,
               show stackPushCount (.Smsf .MLOAD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]

/-- **MLOAD memory-expansion out-of-gas.** With the expansion witness `words'` resolved but the
expansion charge exceeding the remaining gas, `MLOAD` halts with `OutOfGas` at the first `charge`.
Mirror of `stepFrame_mstore_oogMem`. -/
theorem stepFrame_mload_oogMem (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hoog : fr.exec.gasAvailable.toNat < memExpansionChargeOf fr.exec words') :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MLOAD)
      + stackPushCount (.Smsf .MLOAD) > 1024) := by
    simp only [show stackPopCount (.Smsf .MLOAD) = 1 from rfl,
               show stackPushCount (.Smsf .MLOAD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  unfold charge
  rw [if_pos (by have := hoog; dsimp only [memExpansionChargeOf] at this ⊢; omega)]

/-- **MLOAD `Gverylow` out-of-gas.** With the expansion charge cleared but `Gverylow` exceeding the
post-expansion gas, `MLOAD` halts with `OutOfGas` at the second `charge`. Mirror of
`stepFrame_mstore_oogVL`. -/
theorem stepFrame_mload_oogVL (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat)
    (hoog : (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
              < Gverylow) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .MLOAD)
      + stackPushCount (.Smsf .MLOAD) > 1024) := by
    simp only [show stackPopCount (.Smsf .MLOAD) = 1 from rfl,
               show stackPushCount (.Smsf .MLOAD) = 1 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  rw [hstk]
  dsimp only [Stack.pop, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  unfold charge
  rw [if_neg (by have := hgasMem; dsimp only [memExpansionChargeOf] at this ⊢; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_pos (by have := hoog; dsimp only [memExpansionChargeOf] at this ⊢; omega)]

/-- **MLOAD success-inversion.** A `.next` MLOAD step witnesses its memory-expansion bookkeeping:
an expansion witness `words'`, both charges fit, and `e = mloadPost …`. Mirror of
`stepFrame_mstore_inv`. -/
theorem stepFrame_mload_inv (fr : Frame) (addr : UInt256) (rest : Stack UInt256)
    {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    ∃ words', memoryExpansionWords? fr.exec.activeWords addr 32 = some words'
      ∧ memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
      ∧ Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      ∧ e = mloadPost fr.exec addr words' rest := by
  cases hmem : memoryExpansionWords? fr.exec.activeWords addr 32 with
  | none =>
    exfalso
    rw [stepFrame_mload_oogNone fr addr rest hdec hstk hsz hmem] at hnext
    exact absurd hnext (by simp)
  | some words' =>
    have hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat := by
      by_contra h
      rw [stepFrame_mload_oogMem fr addr words' rest hdec hstk hsz hmem (by omega)] at hnext
      exact absurd hnext (by simp)
    have hgas : Gverylow ≤
        (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat := by
      by_contra h
      rw [stepFrame_mload_oogVL fr addr words' rest hdec hstk hsz hmem hgasMem (by omega)] at hnext
      exact absurd hnext (by simp)
    refine ⟨words', rfl, hgasMem, hgas, ?_⟩
    rw [stepFrame_mload fr addr words' rest hdec hstk hsz hmem hgasMem hgas] at hnext
    exact (Signal.next.injEq _ _).mp hnext.symm

/-! ## §2 — the `.next` extractor (the glue)

`CleanHaltsNonException fr` reaches a `.halted halt` terminal with `halt ≠ .exception`. For a frame
decoding to one of the charge-only continuing ops, that forces a *continuing* (`.next`) step: a
halted frame `Runs` only to itself (`halted_runs_eq`), and the op's only `.halted` is `.exception`
(never `.success`/`.revert`), so `fr` is not the terminal — it must step. The per-op
`next_*_of_cleanHalt` then read off the `.next`-inversion to yield the gas bound. The bound `hcont`
of the abstract glue is **discharged** per op by the op's `*_oog` lemma (its only halt is
`.exception`). -/

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

/-- **The abstract `.next` extractor.** From `CleanHaltsNonException fr` and the per-op *step
dichotomy* — `fr` either continues (`.next e'`) or halts with an **exception** (`hdich`) — `fr`
takes a continuing step. The exception-halt arm is excluded because `fr`'s clean-halt terminal is
**non-exception**: a halted `fr` reaches only itself (`halted_runs_eq`), so an exception halt at
`fr` would force the non-exception terminal `halt` to be that same exception halt — contradicting
`halt.IsNonException`. Every charge-only lowered op satisfies the dichotomy (forward lemma when the
gas guard holds, `*_oog` otherwise), so `.needsCall`/`.needsCreate` never arise — those are the
CALL/CREATE ops, excluded by the op decode the specialisations supply. -/
theorem next_of_cleanHalt_continuing {fr : Frame}
    (hcs : CleanHaltsNonException fr)
    (hdich : (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex))) :
    ∃ e', stepFrame fr = .next e' := by
  obtain ⟨last, halt, hto, hhalt, hne⟩ := hcs
  rcases hdich with hnext | ⟨ex, hexc⟩
  · exact hnext
  · -- exception halt at `fr`: `fr` reaches only itself, so the terminal `halt` is this exception.
    exfalso
    have hfreq : fr = last := halted_runs_eq hexc hto
    subst hfreq
    rw [hexc] at hhalt
    have : halt = .exception ex := ((Signal.halted.injEq _ _).mp hhalt).symm
    rw [this] at hne
    exact hne

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

/-! ### Per-op `.next`-from-clean-halt specialisations

Combine the step dichotomy (excludes `.needsCall`/`.needsCreate`) with the abstract extractor to
turn `CleanHaltsNonException fr` + the op decode into a continuing `.next` step, then read off the
inversion to land the gas bound. -/

/-- **GAS: clean-halt ⟹ `Gbase ≤ gas`.** -/
theorem next_gas_of_cleanHalt (fr : Frame)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    Gbase ≤ fr.exec.gasAvailable.toNat ∧ stepFrame fr = .next (gasPost fr.exec) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_gas_dichotomy fr hdec hsz)
  have hg := stepFrame_gas_inv fr hdec hsz hnext
  exact ⟨hg, stepFrame_gas fr hdec hsz hg⟩

/-- **PUSH: clean-halt ⟹ `Gverylow ≤ gas`.** -/
theorem next_push_of_cleanHalt (fr : Frame) (p : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hcs : CleanHaltsNonException fr) (hp0 : p ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push p, some (imm, w)))
    (hpop : stackPopCount (.Push p) = 0) (hpush : stackPushCount (.Push p) = 1)
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    Gverylow ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (pushFrameW fr imm w).exec := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_push_dichotomy fr p imm w hp0 hdec hpop hpush hsz)
  have hg := stepFrame_push_inv fr p imm w hp0 hdec hpop hpush hsz hnext
  exact ⟨hg, stepFrame_push fr p imm w hp0 hdec hpop hpush hg hsz⟩

/-- **SLOAD: clean-halt ⟹ `sloadCost warm ≤ gas`.** -/
theorem next_sload_of_cleanHalt (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    sloadCost (fr.exec.substate.accessedStorageKeys.contains
        (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (sloadPost fr.exec key rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_sload_dichotomy fr key rest hdec hstk hsz)
  have hg := stepFrame_sload_inv fr key rest hdec hstk hsz hnext
  exact ⟨hg, stepFrame_sload fr key rest hdec hstk hsz hg⟩

/-- **MSTORE: clean-halt ⟹ the expansion witness + both charges.** Reuses 003
`stepFrame_mstore_inv` on the continuing step the dichotomy produces. -/
theorem next_mstore_of_cleanHalt (fr : Frame) (addr val : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    ∃ words', memoryExpansionWords? fr.exec.activeWords addr 32 = some words'
      ∧ memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
      ∧ Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      ∧ stepFrame fr = .next (mstorePost fr.exec addr val words' rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_mstore_dichotomy fr addr val rest hdec hstk hsz)
  obtain ⟨words', hmem, hgasMem, hgas, he⟩ := stepFrame_mstore_inv fr addr val rest hdec hstk hsz hnext
  exact ⟨words', hmem, hgasMem, hgas, by rw [hnext, he]⟩

/-! ### ADD / LT / MLOAD step dichotomies + `next_*_of_cleanHalt` (FoldLemma)

The aggregate gas FOLD descends through ADD/LT (binary-op tails) and the MLOAD readback. Each is a
continuing op, so `CleanHaltsNonException` forces a `.next` step (the dichotomy excludes
`.needsCall`/`.needsCreate`), and the inversion reads off the gas bound. -/

/-- **ADD step dichotomy.** -/
theorem stepFrame_add_dichotomy (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gverylow ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_add fr a b rest hdec hstk hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_add_oog fr a b rest hdec hstk hsz (by omega)⟩

/-- **LT step dichotomy.** -/
theorem stepFrame_lt_dichotomy (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gverylow ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_lt fr a b rest hdec hstk hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_lt_oog fr a b rest hdec hstk hsz (by omega)⟩

/-- **MLOAD step dichotomy.** Casing on the expansion witness and the two charges (mirror of
`stepFrame_mstore_dichotomy`). -/
theorem stepFrame_mload_dichotomy (fr : Frame) (addr : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  cases hmem : memoryExpansionWords? fr.exec.activeWords addr 32 with
  | none => exact Or.inr ⟨.OutOfGas, stepFrame_mload_oogNone fr addr rest hdec hstk hsz hmem⟩
  | some words' =>
    by_cases hgasMem : memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
    · by_cases hgas : Gverylow ≤
          (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      · exact Or.inl ⟨_, stepFrame_mload fr addr words' rest hdec hstk hsz hmem hgasMem hgas⟩
      · exact Or.inr ⟨.OutOfGas,
          stepFrame_mload_oogVL fr addr words' rest hdec hstk hsz hmem hgasMem (by omega)⟩
    · exact Or.inr ⟨.OutOfGas, stepFrame_mload_oogMem fr addr words' rest hdec hstk hsz hmem (by omega)⟩

/-- **ADD: clean-halt ⟹ `Gverylow ≤ gas`** (and the continuing `.next` step). -/
theorem next_add_of_cleanHalt (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    Gverylow ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (binOpPost fr.exec UInt256.add a b rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_add_dichotomy fr a b rest hdec hstk hsz)
  have hg := stepFrame_add_inv fr a b rest hdec hstk hsz hnext
  exact ⟨hg, stepFrame_add fr a b rest hdec hstk hsz hg⟩

/-- **LT: clean-halt ⟹ `Gverylow ≤ gas`** (and the continuing `.next` step). -/
theorem next_lt_of_cleanHalt (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    Gverylow ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (binOpPost fr.exec UInt256.lt a b rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_lt_dichotomy fr a b rest hdec hstk hsz)
  have hg := stepFrame_lt_inv fr a b rest hdec hstk hsz hnext
  exact ⟨hg, stepFrame_lt fr a b rest hdec hstk hsz hg⟩

/-- **MLOAD: clean-halt ⟹ the expansion witness + both charges** (and the `.next` step). Reuses
`stepFrame_mload_inv` on the continuing step the dichotomy produces. -/
theorem next_mload_of_cleanHalt (fr : Frame) (addr : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    ∃ words', memoryExpansionWords? fr.exec.activeWords addr 32 = some words'
      ∧ memExpansionChargeOf fr.exec words' ≤ fr.exec.gasAvailable.toNat
      ∧ Gverylow ≤ (fr.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf fr.exec words')).toNat
      ∧ stepFrame fr = .next (mloadPost fr.exec addr words' rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_mload_dichotomy fr addr rest hdec hstk hsz)
  obtain ⟨words', hmem, hgasMem, hgas, he⟩ := stepFrame_mload_inv fr addr rest hdec hstk hsz hnext
  exact ⟨words', hmem, hgasMem, hgas, by rw [hnext, he]⟩

/-! ## §3 — the envelope family (the deliverable)

For the GAS cursor, `sim_assign_gas_lowered`'s residual is the 5-conjunct gas/mem envelope over the
3-step stash `GAS ; PUSH32 (slotOf t) ; MSTORE` at frames `fr`, `gasFrame fr`,
`pushFrameW (gasFrame fr) (ofNat slot) 32`. `gas_envelope_of_cleanHalt` produces it from
`CleanHaltsNonException fr` + the three frame-local decode anchors, threading the clean-halt forward
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

/-- **GAS envelope from clean-halt.** From `CleanHaltsNonException fr` (block-entry stack `[]`) and
the three frame-local decode anchors of the gas stash, produce the exact gas/mem residual
`sim_assign_gas_lowered` consumes: `Gbase ≤ fr.gas`, `3 ≤ (gasFrame fr).gas`, and the MSTORE
expansion witness `words'` + both memory charges at `pushFrameW (gasFrame fr) (ofNat slot) 32`.

The bound gas value the `GAS` op pushes (so the MSTORE writes) is
`ofUInt64 (fr.gas − Gbase)` — the realised GAS output, which fixes the MSTORE operand
`addr = ofNat slot`, `val = that value`, `rest = []`. -/
theorem gas_envelope_of_cleanHalt (fr : Frame) (slot : Nat)
    (hcs : CleanHaltsNonException fr)
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
  obtain ⟨hgasGas, hgasNext⟩ := next_gas_of_cleanHalt fr hcs hdecGAS hsz0
  -- forward the clean-halt across `fr → gasFrame fr`.
  have hstepGas : StepsTo fr (gasFrame fr) := stepsTo_gasFrame fr hdecGAS hsz0 hgasGas
  have hcsGas : CleanHaltsNonException (gasFrame fr) :=
    cleanHaltsNonException_forward hcs (Runs.single hstepGas)
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
    next_push_of_cleanHalt (gasFrame fr) .PUSH32 (UInt256.ofNat slot) 32 hcsGas
      (by decide) hdecPUSH (by decide) (by decide) hszGas
  have hgasPush' : 3 ≤ (gasFrame fr).exec.gasAvailable.toNat := by
    have : Gverylow = 3 := rfl; omega
  -- forward the clean-halt across `gasFrame fr → pushFrameW (gasFrame fr) (ofNat slot) 32`.
  have hstepPush : StepsTo (gasFrame fr) (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32) :=
    stepsTo_pushFrameW (gasFrame fr) .PUSH32 (UInt256.ofNat slot) 32 (by decide) hdecPUSH
      (by decide) (by decide) hgasPush hszGas
  have hcsPush : CleanHaltsNonException (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32) :=
    cleanHaltsNonException_forward hcsGas (Runs.single hstepPush)
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
    next_mstore_of_cleanHalt (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32)
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

/-- **SLOAD envelope from clean-halt.** For the spilled-sload cursor, the residual
`sim_assign_sload_lowered` consumes is keyed on the **post-materialise** frame `frk` (the key
prefix is variable-length; B1 `materialise_runs` produces `frk` and the `MatRuns` Runs threading
`CleanHaltsNonException` to it). At `frk` (stack `[keyVal]`) the tail `SLOAD ; PUSH32 ; MSTORE`
clean-halts, so this lemma produces the gas conjuncts `hgasSload`/`hgasPush`/`hmem`/`hgasMem`/
`hgasMstore` of `hresid` — everything but the **structural** activeWords-flatness `hawk`
(`frk.activeWords = fr.activeWords`: the key materialise expanded no memory — the normal sload-key
case, independent of gas), which stays a supplied structural residual.

Inputs: `CleanHaltsNonException fr`, the entry stack-nil, the `MatRuns` thread to `frk` (which pins
`frk.stack = [keyVal]`), and the three frame-local tail decode anchors at `frk`. -/
theorem sload_envelope_of_cleanHalt
    {defs : Tmp → Option Expr} {sloadChg : Tmp → ℕ} {f : Nat} {ekey : Expr} {wkey : Word}
    (fr frk : Frame) (keyVal : UInt256) (slot : Nat)
    (hcs : CleanHaltsNonException fr)
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
  have hcsK : CleanHaltsNonException frk := cleanHaltsNonException_forward hcs hmrk.runs
  -- `frk`'s stack is `[keyVal]` (B1 leaves the key on top of the entry stack `[]`).
  have hstkK : frk.exec.stack = keyVal :: [] := by
    rw [hmrk.stack, hstk0, ← hkeyval]; rfl
  have hszK : frk.exec.stack.size ≤ 1024 := by rw [hstkK]; simp [Stack.size]
  -- (a) SLOAD at `frk`.
  obtain ⟨hgasSload, hsloadNext⟩ := next_sload_of_cleanHalt frk keyVal [] hcsK hdecSLOAD hstkK hszK
  -- forward the clean-halt across `frk → sloadFrame frk keyVal []`.
  have hstepSload : StepsTo frk (sloadFrame frk keyVal []) :=
    stepsTo_sloadFrame frk keyVal [] hdecSLOAD hstkK hszK hgasSload
  have hcsSload : CleanHaltsNonException (sloadFrame frk keyVal []) :=
    cleanHaltsNonException_forward hcsK (Runs.single hstepSload)
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
    next_push_of_cleanHalt (sloadFrame frk keyVal []) .PUSH32 (UInt256.ofNat slot) 32 hcsSload
      (by decide) hdecPUSH (by decide) (by decide) hszSload
  have hgasPush' : 3 ≤ (sloadFrame frk keyVal []).exec.gasAvailable.toNat := by
    have : Gverylow = 3 := rfl; omega
  -- forward the clean-halt across `sloadFrame … → pushFrameW (sloadFrame …) (ofNat slot) 32`.
  have hstepPush : StepsTo (sloadFrame frk keyVal [])
      (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32) :=
    stepsTo_pushFrameW (sloadFrame frk keyVal []) .PUSH32 (UInt256.ofNat slot) 32 (by decide)
      hdecPUSH (by decide) (by decide) hgasPush hszSload
  have hcsPush : CleanHaltsNonException (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32) :=
    cleanHaltsNonException_forward hcsSload (Runs.single hstepPush)
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
    next_mstore_of_cleanHalt (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32)
      (UInt256.ofNat slot)
      (Evm.State.sload
        ({ frk.exec with gasAvailable := frk.exec.gasAvailable
            - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2
      [] hcsPush hdecMSTORE hstkM' hszM
  exact ⟨hgasSload, hgasPush', words', hmem, hgasMem, hgasMstore⟩

/-! ## §4 — JUMP / JUMPDEST clean-halt envelopes (the terminator landing)

The lowered `jump`/`branch` terminators step `PUSH4 destOff ; JUMP` (and JUMPI for `branch`).
The pre-`JUMPDEST` landing frame `fj` (the JUMP successor frame, sitting *on* the landing
`JUMPDEST` byte) needs its `Gjumpdest` envelope discharged: the threaded clean-halt at `fj`
forces the `JUMPDEST` step to continue, so `Gjumpdest ≤ fj.gas`. The JUMP gas envelope
`Gmid ≤ frp.gas` (at the post-PUSH4 frame `frp`) is what lets the `JUMP` step run at all.

These mirror the §1/§2 charge-only bricks. JUMP charges `Gmid` *before* popping (no `hstk` for
OOG, only `hsz`); the success arm carries the valid-destination witness `hdest`. JUMPDEST is a
pop-0/push-0 no-op charging `Gjumpdest`. -/

/-- **JUMP out-of-gas.** With `Gmid` exceeding the available gas, `stepFrame` halts with
`OutOfGas` at the `charge` (which fires before the pop). Companion of the forward
`stepFrame_jump`; needs only `hsz` (the charge precedes the destination pop). -/
theorem stepFrame_jump_oog (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMP, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gmid) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMP)
      + stackPushCount (.Smsf .JUMP) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMP) = 1 from rfl,
               show stackPushCount (.Smsf .JUMP) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **JUMP `.next`-inversion.** A successful `.next` JUMP step witnesses `Gmid ≤ gas`.
Contrapositive of `stepFrame_jump_oog`. -/
theorem stepFrame_jump_inv (fr : Frame) {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMP, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gmid ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_jump_oog fr hdec hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **JUMPDEST out-of-gas.** With `Gjumpdest` exceeding the available gas, `stepFrame` halts with
`OutOfGas`. Companion of the forward `stepFrame_jumpdest`; pop-0/push-0 no-op. -/
theorem stepFrame_jumpdest_oog (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gjumpdest) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMPDEST)
      + stackPushCount (.Smsf .JUMPDEST) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMPDEST) = 0 from rfl,
               show stackPushCount (.Smsf .JUMPDEST) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **JUMPDEST `.next`-inversion.** A successful `.next` JUMPDEST step witnesses `Gjumpdest ≤ gas`. -/
theorem stepFrame_jumpdest_inv (fr : Frame) {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gjumpdest ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_jumpdest_oog fr hdec hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **JUMP step dichotomy.** A JUMP-decoding frame (with the destination operand `dest :: rest`
and valid-destination witness `hdest`) either continues to `jumpPost … new_pc rest` or halts with
an exception (OOG when `gas < Gmid`). -/
theorem stepFrame_jump_dichotomy (fr : Frame) (dest : UInt256) (new_pc : UInt32)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMP, .none))
    (hstk : fr.exec.stack = dest :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hdest : fr.get_dest dest = some new_pc) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gmid ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_jump fr dest new_pc rest hdec hstk hsz hgas hdest⟩
  · exact Or.inr ⟨_, stepFrame_jump_oog fr hdec hsz (by omega)⟩

/-- **JUMPDEST step dichotomy.** A JUMPDEST-decoding frame either continues to `jumpdestPost …`
or halts with an exception (OOG when `gas < Gjumpdest`). -/
theorem stepFrame_jumpdest_dichotomy (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gjumpdest ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_jumpdest fr hdec hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_jumpdest_oog fr hdec hsz (by omega)⟩

/-- **JUMP: clean-halt ⟹ `Gmid ≤ gas`** (and the continuing `.next` step to `jumpPost`). The
valid-destination witness `hdest` is needed for the success arm of the dichotomy. -/
theorem next_jump_of_cleanHalt (fr : Frame) (dest : UInt256) (new_pc : UInt32)
    (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMP, .none))
    (hstk : fr.exec.stack = dest :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hdest : fr.get_dest dest = some new_pc) :
    Gmid ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (jumpPost fr.exec Gmid new_pc rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_jump_dichotomy fr dest new_pc rest hdec hstk hsz hdest)
  have hg := stepFrame_jump_inv fr hdec hsz hnext
  exact ⟨hg, stepFrame_jump fr dest new_pc rest hdec hstk hsz hg hdest⟩

/-- **JUMPDEST: clean-halt ⟹ `Gjumpdest ≤ gas`** (and the continuing `.next` step to
`jumpdestPost`). The bound the terminator landing's pre-`JUMPDEST` frame needs. -/
theorem next_jumpdest_of_cleanHalt (fr : Frame)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hsz : fr.exec.stack.size ≤ 1024) :
    Gjumpdest ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (jumpdestPost fr.exec) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_jumpdest_dichotomy fr hdec hsz)
  have hg := stepFrame_jumpdest_inv fr hdec hsz hnext
  exact ⟨hg, stepFrame_jumpdest fr hdec hsz hg⟩

/-! ## §5 — `JUMPI` clean-halt gas envelopes (`branch` terminator landing bricks)

The lowered `branch` terminator is `materialise cond ; PUSH4 thenOff ; JUMPI ; PUSH4 elseOff ;
JUMP`. The `JUMPI` arm needs its `Ghigh` envelope discharged from the threaded clean-halt — at
the post-PUSH4 frame `frp` (with `thenWord :: cw :: rest` on the stack). `JUMPI` charges `Ghigh`
*before* popping its two operands (`stackPopCount (.Smsf .JUMPI) = 2`), so a single OOG companion
covers **both** the taken (`cw ≠ 0`) and fall-through (`cw = 0`) arms: only `hsz` is needed for
OOG, the runtime `cw` selects the success-arm continuation. -/

/-- **JUMPI out-of-gas.** With `Ghigh` exceeding the available gas, `stepFrame` halts with
`OutOfGas` at the `charge` (which fires before the two-operand pop). Companion of the forward
`stepFrame_jumpi_taken`/`stepFrame_jumpi_fallthrough`; needs only `hsz` (the charge precedes the
pop, so it is condition-independent). -/
theorem stepFrame_jumpi_oog (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Ghigh) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .JUMPI)
      + stackPushCount (.Smsf .JUMPI) > 1024) := by
    simp only [show stackPopCount (.Smsf .JUMPI) = 2 from rfl,
               show stackPushCount (.Smsf .JUMPI) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **JUMPI `.next`-inversion.** A successful `.next` JUMPI step witnesses `Ghigh ≤ gas`.
Contrapositive of `stepFrame_jumpi_oog`; condition-independent. -/
theorem stepFrame_jumpi_inv (fr : Frame) {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Ghigh ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_jumpi_oog fr hdec hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **JUMPI taken step dichotomy.** A JUMPI-decoding frame (operands `dest :: cond :: rest`, a
non-zero condition `hcond`, valid-destination witness `hdest`) either continues to
`jumpPost … new_pc rest` or halts with an exception (OOG when `gas < Ghigh`). -/
theorem stepFrame_jumpi_taken_dichotomy (fr : Frame) (dest cond : UInt256) (new_pc : UInt32)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: cond :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hcond : cond ≠ 0)
    (hdest : fr.get_dest dest = some new_pc) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Ghigh ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_jumpi_taken fr dest cond new_pc rest hdec hstk hsz hgas hcond hdest⟩
  · exact Or.inr ⟨_, stepFrame_jumpi_oog fr hdec hsz (by omega)⟩

/-- **JUMPI fall-through step dichotomy.** A JUMPI-decoding frame (operands `dest :: 0 :: rest`,
zero condition) either continues to `jumpiFallthroughPost … rest` or halts with an exception
(OOG when `gas < Ghigh`). No destination requirement (the jump is not taken). -/
theorem stepFrame_jumpi_fallthrough_dichotomy (fr : Frame) (dest : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: (0 : UInt256) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Ghigh ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, stepFrame_jumpi_fallthrough fr dest rest hdec hstk hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_jumpi_oog fr hdec hsz (by omega)⟩

/-- **JUMPI taken: clean-halt ⟹ `Ghigh ≤ gas`** (and the continuing `.next` step to `jumpPost`).
The non-zero condition `hcond` and valid-destination `hdest` select the taken success arm. -/
theorem next_jumpi_taken_of_cleanHalt (fr : Frame) (dest cond : UInt256) (new_pc : UInt32)
    (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: cond :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hcond : cond ≠ 0)
    (hdest : fr.get_dest dest = some new_pc) :
    Ghigh ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (jumpPost fr.exec Ghigh new_pc rest) := by
  obtain ⟨e', hnext⟩ := next_of_cleanHalt_continuing hcs
    (stepFrame_jumpi_taken_dichotomy fr dest cond new_pc rest hdec hstk hsz hcond hdest)
  have hg := stepFrame_jumpi_inv fr hdec hsz hnext
  exact ⟨hg, stepFrame_jumpi_taken fr dest cond new_pc rest hdec hstk hsz hg hcond hdest⟩

/-- **JUMPI fall-through: clean-halt ⟹ `Ghigh ≤ gas`** (and the continuing `.next` step to
`jumpiFallthroughPost`). The zero condition selects the fall-through success arm. -/
theorem next_jumpi_fallthrough_of_cleanHalt (fr : Frame) (dest : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: (0 : UInt256) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    Ghigh ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (jumpiFallthroughPost fr.exec rest) := by
  obtain ⟨e', hnext⟩ := next_of_cleanHalt_continuing hcs
    (stepFrame_jumpi_fallthrough_dichotomy fr dest rest hdec hstk hsz)
  have hg := stepFrame_jumpi_inv fr hdec hsz hnext
  exact ⟨hg, stepFrame_jumpi_fallthrough fr dest rest hdec hstk hsz hg⟩

end Lir.CleanHaltExtract

-- Axiom-cleanliness guards (§0 — predicate lives in `LirLean/Engine/CleanHalt.lean`).
-- Axiom-cleanliness guards (§1).
-- Axiom-cleanliness guards (§2).
-- Axiom-cleanliness guards (§1.5/§2 — FoldLemma ADD/LT/MLOAD bricks).
-- Axiom-cleanliness guards (§3).
-- Axiom-cleanliness guards (§4 — JUMP/JUMPDEST terminator-landing bricks).
-- Axiom-cleanliness guards (§5 — JUMPI terminator-landing bricks).
