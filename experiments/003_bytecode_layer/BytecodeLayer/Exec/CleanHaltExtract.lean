import BytecodeLayer.Hoare.CleanHalt

/-!
# Clean-halt gas and memory envelopes

A frame whose remaining `Runs` reaches a non-exception halt cannot fault on its
next step. This module turns that fact into opcode-specific gas and memory-expansion
bounds.

The supported opcode set is
`PUSH32`/`PUSH4`/`MLOAD`/`ADD`/`LT`/`SLOAD`/`GAS`/`MSTORE`/`SSTORE`/`CALL`/`POP`/`STOP`/`JUMP`/
`JUMPI`/`JUMPDEST` — no `DUP`/`SWAP` (recompute-on-use).

## Main layers

* **`CleanHaltsNonException`** (§0) identifies runs ending in `.success` or `.revert`.
* **per-op OOG / `.next`-inversion bricks** (§1) — for the charge-only ops with no inversion in
  `GAS`/`PUSH`/`SLOAD`/`ADD`/`LT`: `op_oog` (`¬gas ⟹ .halted (.exception OutOfGas)`) and
  `op_inv` (`.next ⟹ gas bound`), the `stepFrame`-unfold + `charge` `if_pos`/contrapositive
  pattern.
* **the `.next` extractor** (§2) — `halted_runs_eq` (a halted frame `Runs` only to itself) and the
  per-op `next_*_of_cleanHalt` specialisations: `CleanHaltsNonException fr` + the op's decode ⟹
  `∃ e', stepFrame fr = .next e'` (the non-exception terminal forces a continuing step, since the
  op's only `.halted` is `.exception`).
* **the envelope family** (§3) threads clean halting across decoded GAS, SLOAD,
  PUSH, and MSTORE steps and returns their combined charge bounds.
-/

namespace BytecodeLayer.Exec.CleanHaltExtract

open Evm
open Evm.Operation
open GasConstants
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## §0 — `CleanHaltsNonException`

`CleanHalts` permits any halted outcome. `CleanHaltsNonException` restricts the
terminal outcome to `.success` or `.revert`. A continuing opcode whose only halted
case is `.exception` must therefore take a `.next` step.
-/

open BytecodeLayer.Hoare (CleanHaltsNonException cleanHaltsNonException_forward HaltNonException)

/-! ## §1 — per-op OOG / `.next`-inversion bricks

The charge-only ops (`GAS`/`PUSH`/`SLOAD`/`ADD`/`LT`) need inversion and OOG lemmas.
Each is the `stepFrame`-unfold to the
`charge` `if`, taken in the `if_pos` branch (`¬gas ⟹ .halted (.exception OutOfGas)`); the
`.next`-inversion is then the contrapositive (a `.next` step witnesses the gas guard held). The
overflow `if_neg` is discharged from the same stack hypotheses the forward lemma uses.

`MSTORE`/`MLOAD`/`SSTORE` use their existing inversion lemmas. -/

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

/-- A successful `.next` SLOAD step witnesses `sloadCost warm ≤ gas`. -/
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

/-! ### ADD / LT / MLOAD OOG and inversion bricks

These lemmas copy the GAS/PUSH/SLOAD pattern: the `binOp` charges `Gverylow`
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
then `fr = last`: the run cannot take a `step` (needs `.next`), a `call` (needs `.needsCall`), or a
`create` (needs `.needsCreate`), so it is `refl`. -/
theorem halted_runs_eq {fr last : Frame} {h : FrameHalt}
    (hhalt : stepFrame fr = .halted h) (hrun : Runs fr last) : fr = last := by
  cases hrun with
  | refl _ => rfl
  | step hstep _ => rw [hstep.1] at hhalt; exact absurd hhalt (by nofun)
  | call hcall _ =>
    obtain ⟨_, _, _, _, hstep, _⟩ := hcall
    rw [hstep] at hhalt; exact absurd hhalt (by nofun)
  | create hc _ =>
    obtain ⟨_, _, _, hstep, _⟩ := hc
    rw [hstep] at hhalt; exact absurd hhalt (by nofun)

/-- **The abstract `.next` extractor.** From `CleanHaltsNonException fr` and the per-op *step
dichotomy* — `fr` either continues (`.next e'`) or halts with an **exception** (`hdich`) — `fr`
takes a continuing step. The exception-halt arm is excluded because `fr`'s clean-halt terminal is
**non-exception**: a halted `fr` reaches only itself (`halted_runs_eq`), so an exception halt at
`fr` would force the non-exception terminal `halt` to be that same exception halt — contradicting
`halt.IsNonException`. Every charge-only op satisfies the dichotomy (forward lemma when the
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

/-- **MSTORE: clean-halt ⟹ the expansion witness + both charges.** Uses
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

/-! ### ADD / LT / MLOAD step dichotomies

Each is a continuing op, so `CleanHaltsNonException` forces a `.next` step (the dichotomy excludes
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

/-- **MLOAD: clean-halt ⟹ the expansion witness + both charges** (and the `.next` step). Uses
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

/-! ## §3 — combined envelopes

`gas_envelope_of_cleanHalt` covers the three-step sequence
`GAS ; PUSH32 slot ; MSTORE`, threading clean halting across each `StepsTo` edge.
-/

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

/-- **GAS envelope from clean-halt.** From `CleanHaltsNonException fr` (entry stack `[]`) and
the three frame-local decode anchors, produce `Gbase ≤ fr.gas`,
`3 ≤ (gasFrame fr).gas`, and the MSTORE
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

/-! ## §4 — JUMP / JUMPDEST clean-halt envelopes (the terminator landing)

The pre-`JUMPDEST` landing frame `fj` (the JUMP successor frame, sitting on the landing
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

The `JUMPI` arm needs its `Ghigh` envelope discharged from the threaded clean-halt at
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

/-! ## §6 — POP and CALL-charge clean-halt bricks

POP and CALL cursors need two more instances of the same extraction pattern:

* **POP** (the `resultTmp = none` Route-B tail): `stepFrame_pop_oog`/`stepFrame_pop_dichotomy`/
  `next_pop_of_cleanHalt`, the exact `runs_pop` mirror of the GAS brick (POP charges `Gbase`
  *before* popping, so the OOG arm needs no stack shape);
* **the CALL charge** (`call_extraCost_le_of_cleanHalt`): the value-free zero-window CALL's
  only dispatch fault is the `charge (gasCap + extraCost)` gate; when `extraCost` exceeds the
  available gas that charge throws (`stepFrame_call_oog`), so a clean-halting CALL cursor
  witnesses `callExtraCost ≤ gas` — exactly `stepFrame_call`'s remaining gas premise. (The
  `depth < 1024` guard is NOT derivable from clean-halt — the deep fallback is a plain `.next`.
  The recorder therefore represents both CALL outcomes positionally.) -/

/-- **POP out-of-gas.** With `Gbase` exceeding the available gas, `stepFrame` halts with
`OutOfGas`. POP charges before popping, so no
stack shape is needed. -/
theorem stepFrame_pop_oog (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .POP, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hoog : fr.exec.gasAvailable.toNat < Gbase) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.Smsf .POP)
      + stackPushCount (.Smsf .POP) > 1024) := by
    simp only [show stackPopCount (.Smsf .POP) = 1 from rfl,
               show stackPushCount (.Smsf .POP) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, smsfOp]
  unfold charge
  rw [if_pos (by have := hoog; omega)]
  dsimp only [bind, Except.bind, pure, Except.pure]

/-- **POP `.next`-inversion.** A successful `.next` POP step witnesses `Gbase ≤ gas`. -/
theorem stepFrame_pop_inv (fr : Frame) {e : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .POP, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hnext : stepFrame fr = .next e) :
    Gbase ≤ fr.exec.gasAvailable.toNat := by
  by_contra h
  rw [stepFrame_pop_oog fr hdec hsz (by omega)] at hnext
  exact absurd hnext (by simp)

/-- **POP step dichotomy.** -/
theorem stepFrame_pop_dichotomy (fr : Frame) (v : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .POP, .none))
    (hstk : fr.exec.stack = v :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    (∃ e', stepFrame fr = .next e') ∨ (∃ ex, stepFrame fr = .halted (.exception ex)) := by
  by_cases hgas : Gbase ≤ fr.exec.gasAvailable.toNat
  · exact Or.inl ⟨_, BytecodeLayer.Dispatch.stepFrame_pop fr v rest hdec hstk hsz hgas⟩
  · exact Or.inr ⟨_, stepFrame_pop_oog fr hdec hsz (by omega)⟩

/-- **POP: clean-halt ⟹ `Gbase ≤ gas`** (and the continuing `.next` step to `popPost`). The
`runs_pop` feeder for the fire-and-forget (`resultTmp = none`) call tail. -/
theorem next_pop_of_cleanHalt (fr : Frame) (v : UInt256) (rest : Stack UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .POP, .none))
    (hstk : fr.exec.stack = v :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    Gbase ≤ fr.exec.gasAvailable.toNat
      ∧ stepFrame fr = .next (BytecodeLayer.Dispatch.popPost fr.exec rest) := by
  obtain ⟨e', hnext⟩ :=
    next_of_cleanHalt_continuing hcs (stepFrame_pop_dichotomy fr v rest hdec hstk hsz)
  have hg := stepFrame_pop_inv fr hdec hsz hnext
  exact ⟨hg, BytecodeLayer.Dispatch.stepFrame_pop fr v rest hdec hstk hsz hg⟩

/-- **CALL out-of-gas** (value-free zero-window shape). With `callExtraCost` exceeding the
available gas, the `charge (gasCap + extraCost)` gate throws and `stepFrame` halts with
`OutOfGas`. Mirrors `BytecodeLayer.System.stepFrame_call`'s dispatch walk into the failing
charge (the mem-expansion charge is `0` for the all-zero windows; the static-mode screen is
skipped at `value = 0`; `gasCap + extraCost ≥ extraCost > gas` regardless of `callGasCap`'s
branch). -/
theorem stepFrame_call_oog (fr : Frame) (gasv toAddr : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .CALL, .none))
    (hstk : fr.exec.stack = gasv :: toAddr :: 0 :: 0 :: 0 :: 0 :: 0 :: [])
    (hoog : fr.exec.gasAvailable.toNat
      < callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
          fr.exec.accounts fr.exec.substate) :
    stepFrame fr = .halted (.exception .OutOfGas) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.System .CALL)
      + stackPushCount (.System .CALL) > 1024) := by
    simp only [show stackPopCount (.System .CALL) = 7 from rfl,
               show stackPushCount (.System .CALL) = 1 from rfl, hstk, Stack.size]
    simp only [List.length]
    omega
  rw [if_neg hov]
  dsimp only [dispatch, systemOp]
  rw [hstk]
  dsimp only [Stack.pop7, liftM, monadLift, MonadLift.monadLift, Option.option,
    bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp)]
  unfold callArm
  dsimp only [memoryExpansionWords?, bind, Except.bind, pure, Except.pure]
  simp only [show (((0:UInt256))==0) = true from rfl, if_true, Option.bind_some]
  rw [show (Cₘ fr.exec.activeWords - Cₘ fr.exec.activeWords) = 0 from by omega]
  unfold charge
  rw [if_neg (by simp)]
  dsimp only
  rw [show fr.exec.gasAvailable - UInt64.ofNat 0 = fr.exec.gasAvailable from by
        simp]
  rw [if_pos (by have := hoog; omega)]

/-- **CALL: clean-halt ⟹ `callExtraCost ≤ gas`** (the CALL charge extraction). A CALL cursor
that clean-halts non-exceptionally cannot be sitting on the failing `charge` gate: were
`extraCost > gas`, `stepFrame` would halt `OutOfGas` here (`stepFrame_call_oog`), and a halted
frame `Runs` only to itself (`halted_runs_eq`) — forcing the non-exception terminal to BE that
exception halt. This is `stepFrame_call`'s residual gas premise, DERIVED. -/
theorem call_extraCost_le_of_cleanHalt (fr : Frame) (gasv toAddr : UInt256)
    (hcs : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .CALL, .none))
    (hstk : fr.exec.stack = gasv :: toAddr :: 0 :: 0 :: 0 :: 0 :: 0 :: []) :
    callExtraCost (AccountAddress.ofUInt256 toAddr) (AccountAddress.ofUInt256 toAddr) 0
      fr.exec.accounts fr.exec.substate ≤ fr.exec.gasAvailable.toNat := by
  by_contra hlt
  obtain ⟨last, halt, hto, hhalt, hne⟩ := hcs
  have hoog := stepFrame_call_oog fr gasv toAddr hdec hstk (by omega)
  have heq : fr = last := halted_runs_eq hoog hto
  subst heq
  rw [hoog] at hhalt
  have hhx : halt = .exception .OutOfGas := ((Signal.halted.injEq _ _).mp hhalt).symm
  rw [hhx] at hne
  exact hne

end BytecodeLayer.Exec.CleanHaltExtract
