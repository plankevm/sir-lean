import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Semantics.Interpreter.Measure
import BytecodeLayer.Semantics.Interpreter.NeverOutOfFuel

/-!
# `Runs`-level gas monotonicity (`docs/ir-design-v2.md` §3.4 "holds across calls")

The v2 IR design (`experiments/005_ir_lowering/docs/ir-design-v2.md` §3.4) gives the
gas oracle exactly **one** law: the `gasRead` values, in program order, are monotone
non-increasing (`gasAvailable.toNat` only goes down). `LirLean/V2/Mono.lean` discharged
that law for a *concrete* two-read program by exact `subCharges` arithmetic. The
**general** lowering (an arbitrary `Runs`, with `.call` nodes between reads) needs the
law as a structural fact about the engine, **including through external calls** — the
63/64 net-debit argument: a returning call nets a debit on the caller, so the caller's
gas after the call is no larger than before.

This file proves that fact, bottom-up, reusing the never-OutOfFuel gas machinery
verbatim (nothing new about gas costs is introduced here):

1. **`StepsTo` never increases gas** (`StepsTo.gas_le`). A single non-halting opcode
   step strictly decreases gas for non-`System` opcodes (`stepFrame_next_lt`) and for
   `System` `.next` fallbacks (`systemOp_next_gas`); either way the post-frame's gas is
   `≤` the pre-frame's.

2. **`drive` never increases total gas** (`drive_gasRemaining_le_totalGas`). For any
   terminating `drive f stack state = .ok r`, the result's `gasRemaining` is `≤` the
   state's `totalGas` (active gas + every suspended parent's saved gas). Proved by
   induction on `f`, one branch per `drive` transition, each discharged by an already
   proven per-transition gas-`≤` fact: `stepFrame_next_lt`/`systemOp_next_gas` (step),
   `endFrame_gasRemaining_le` (halt), `gasFundsDescent_conj4/5a/4'/5b` (descents),
   `resumeAfterCall_gas_le`/`resumeAfterCreate_gas_le_savedGas` (deliveries). This is the
   `mu_bound` skeleton with the `+2` slack dropped to a plain `≤`.

   Specialised to a top-level child run (`stack = []`, `state = .inl child`) it gives the
   **net-debit fact**: a child call returns no more gas than it was funded
   (`childRes.gasRemaining ≤ child.gas`), which is the 63/64-refund-doesn't-raise-gas
   content of §3.4.

3. **`Runs` never increases gas** (`Runs.gasAvailable_le`). By induction on the `Runs`
   derivation: `refl` (equal), `step` (rung 1, transitively), and `call` (rung 2 + the
   net-debit, threading a `.call`/`CallReturns` node). This is the lemma the v2 general
   preservation theorem consumes: across any flat `Runs fr last`,
   `last.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat` — **no hypothesis** on the
   call returning (`CallReturns` already bundles a returning child), no per-opcode cost
   assumed.

The §3.4 monotone-oracle law is then `Runs.gasAvailable_le` read at the two `GAS` reads:
any two `gasRead` values realised on a `Runs` path are monotone because the machine's
`gasAvailable.toNat` between them does not increase, including across `.call` nodes.
-/

namespace BytecodeLayer.Hoare
open Evm
open GasConstants
open BytecodeLayer.Dispatch
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Gas

/-! ## 1. A single opcode step never increases gas -/

/-- **One opcode step never increases gas.** `StepsTo fr fr'` (`stepFrame fr = .next
fr'.exec`, `fr'` is `fr` with `exec` advanced) has `fr'.exec.gasAvailable.toNat ≤
fr.exec.gasAvailable.toNat`. Both the non-`System` opcodes (`stepFrame_next_lt`, a
*strict* drop) and the `System` `.next` fallbacks (`systemOp_next_gas` via
`stepFrame_next_systemOp`, also a strict drop) land at `≤`. -/
theorem StepsTo.gas_le {fr fr' : Frame} (h : StepsTo fr fr') :
    fr'.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat := by
  obtain ⟨hstep, hfr'⟩ := h
  -- `fr'.exec` is the `.next` payload.
  have hnext : stepFrame fr = .next fr'.exec := hstep
  by_cases hsys : ∃ s, (decode fr.exec.executionEnv.code fr.exec.pc
      |>.getD (Operation.STOP, .none)).1 = .System s
  · obtain ⟨s, hs⟩ := hsys
    have := systemOp_next_gas (stepFrame_next_systemOp hs hnext)
    omega
  · have hne : ∀ s, (decode fr.exec.executionEnv.code fr.exec.pc
        |>.getD (.STOP, .none)).1 ≠ .System s := by
      intro s hc; exact hsys ⟨s, hc⟩
    exact le_of_lt (stepFrame_next_lt hne hnext)

/-! ## 2. `drive` never increases total gas

The gas-conservation invariant: a terminating `drive` returns no more gas than the total
gas held by the machine at entry. This is `mu_bound` with the `+2` measure slack relaxed
to a plain `≤`; every per-transition bound is an existing lemma. -/

/-- **`drive` gas conservation.** Any terminating run `drive f stack state = .ok r`
returns gas `r.gasRemaining ≤ totalGas stack state` — the engine never manufactures gas,
across opcode steps, halts, CALL/CREATE descents *and* their deliveries. The branch
structure mirrors `mu_bound`; each step reuses the already proven per-transition
gas-`≤` fact. -/
theorem drive_gasRemaining_le_totalGas :
    ∀ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) (r : FrameResult),
      drive f stack state = .ok r → FrameResult.gasRemaining r ≤ totalGas stack state := by
  intro f
  induction f with
  | zero => intro stack state r h; simp [drive] at h
  | succ n ih =>
    intro stack state r h
    unfold drive at h
    cases state with
    | inr result =>
      dsimp only at h
      cases hstk : stack with
      | nil =>
        rw [hstk] at h; dsimp only at h
        simp only [Except.ok.injEq] at h; subst h
        simp only [totalGas, activeGas, List.map_nil, List.sum_nil]; omega
      | cons pending rest =>
        rw [hstk] at h; dsimp only at h
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h; dsimp only at h
          have hrec := ih rest (.inl parent) r h
          -- delivery: parent gas ≤ savedGas pending + result.gasRemaining
          have hcons : activeGas (.inl parent)
              ≤ Pending.savedGas pending + FrameResult.gasRemaining result := by
            cases pending with
            | call pd =>
              simp only [Pending.resume] at hres
              simp only [Except.ok.injEq] at hres; subst hres
              have hb := resumeAfterCall_gas_le result.toCallResult pd
              rw [toCallResult_gasRemaining] at hb
              simp only [activeGas, Pending.savedGas]; omega
            | create pd =>
              simp only [Pending.resume] at hres
              have hb := resumeAfterCreate_gas_le_savedGas (result := result.toCreateResult)
                (pd := pd) hres
              rw [toCreateResult_gasRemaining] at hb
              simp only [activeGas, Pending.savedGas]; omega
          rw [totalGas_cons]
          simp only [totalGas, activeGas] at hrec hcons ⊢
          omega
        | error e =>
          rw [hres] at h; dsimp only at h
          have hrec := ih rest (.inr (endFrame pending.frame (.exception e))) r h
          -- exceptional resume: the delivered result carries gas 0
          have hz : FrameResult.gasRemaining (endFrame pending.frame (.exception e)) = 0 := by
            unfold endFrame; cases pending.frame.kind <;>
              simp [FrameResult.gasRemaining, endCall, endCreate, UInt64.toNat_ofNat]
          rw [totalGas_cons]
          simp only [totalGas, activeGas, hz] at hrec
          omega
    | inl current =>
      dsimp only at h
      cases hstep : stepFrame current with
      | next exec' =>
        rw [hstep] at h; dsimp only at h
        have hrec := ih stack (.inl { current with exec := exec' }) r h
        -- the step never increases gas
        have hle : exec'.gasAvailable.toNat ≤ current.exec.gasAvailable.toNat :=
          StepsTo.gas_le (stepsTo_of_next hstep)
        simp only [totalGas, activeGas] at hrec ⊢
        omega
      | halted halt =>
        rw [hstep] at h; dsimp only at h
        have hrec := ih stack (.inr (endFrame current halt)) r h
        have hle := endFrame_gasRemaining_le hstep
        simp only [totalGas, activeGas] at hrec ⊢
        omega
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h; dsimp only at h
          have hrec := ih (.call pending :: stack) (.inl child) r h
          have hdrop := gasFundsDescent_conj4 current params pending child stack hstep hbc
          rw [totalGas_cons] at hrec
          simp only [totalGas, activeGas, Pending.savedGas] at hrec ⊢
          simp only [activeGas, Pending.savedGas] at hdrop
          omega
        | inr result =>
          rw [hbc] at h; dsimp only at h
          have hrec := ih (.call pending :: stack) (.inr (.call result)) r h
          have hdrop := gasFundsDescent_conj5a current params pending result stack hstep hbc
          rw [totalGas_cons] at hrec
          simp only [totalGas, activeGas, FrameResult.gasRemaining, Pending.savedGas] at hrec ⊢
          simp only [FrameResult.gasRemaining, activeGas, Pending.savedGas] at hdrop
          omega
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h
        -- `beginCreate` is total: the descent into `beginCreate params` is unconditional.
        have hrec := ih (.create pending :: stack) (.inl (beginCreate params)) r h
        have hdrop := gasFundsDescent_conj4' current params pending (beginCreate params) stack hstep rfl
        rw [totalGas_cons] at hrec
        simp only [totalGas, activeGas, Pending.savedGas] at hrec ⊢
        simp only [activeGas, Pending.savedGas] at hdrop
        omega

/-- **The net-debit fact (top-level child run).** A child `drive` run that terminates
returns no more gas than the gas it was funded with: `r.gasRemaining ≤ fr.exec.gas`.
This is the 63/64 / refund content of §3.4 read off `drive_gasRemaining_le_totalGas` at
the empty pending stack — a returning call cannot raise the caller's available gas. -/
theorem drive_gasRemaining_le_of_running {fr : Frame} {f : ℕ} {r : FrameResult}
    (h : drive f [] (.inl fr) = .ok r) :
    FrameResult.gasRemaining r ≤ fr.exec.gasAvailable.toNat := by
  have := drive_gasRemaining_le_totalGas f [] (.inl fr) r h
  simpa only [totalGas, activeGas, List.map_nil, List.sum_nil, Nat.add_zero] using this

/-! ## 3. A `CallReturns` node nets a debit on the caller

The 63/64 net-debit argument, assembled from the descent inequality and the delivery
bound. The CALL is funded out of the parent's gas *before* the parent is suspended, so
the child's funded gas plus the parent's saved gas is `≤` the caller's pre-CALL gas
(`gasFundsDescent_conj4`); the child returns no more than it was funded
(`drive_gasRemaining_le_of_running`); and the resumed parent's gas is `≤` saved-parent +
child-returned (`resumeAfterCall_gas_le`). Chaining the three gives the resumed frame's
gas `≤` the caller's. -/

/-- **A returning external CALL nets a debit on the caller.** If `CallReturns callFr
resumeFr` (one CALL at `callFr` whose child runs to completion, resuming at `resumeFr`),
then `resumeFr.exec.gasAvailable.toNat ≤ callFr.exec.gasAvailable.toNat`. The 63/64 refund
only means the caller wasn't charged for the child's *unused* gas; it never raises the
caller's gas. **No hypothesis** beyond `CallReturns` itself (which already bundles the
child returning). -/
theorem CallReturns.gas_le {callFr resumeFr : Frame} (h : CallReturns callFr resumeFr) :
    resumeFr.exec.gasAvailable.toNat ≤ callFr.exec.gasAvailable.toNat := by
  obtain ⟨cp, pending, child, childRes, hstep, hcbegin, hchild, hres⟩ := h
  subst hres
  -- (a) descent: child funded gas + saved-parent gas + 2 ≤ caller gas.
  have hdesc := gasFundsDescent_conj4 callFr cp pending child [] hstep hcbegin
  simp only [activeGas, Pending.savedGas] at hdesc
  -- (b) child returns no more than it was funded.
  have hchildGas : FrameResult.gasRemaining childRes ≤ child.exec.gasAvailable.toNat :=
    drive_gasRemaining_le_of_running hchild
  -- (c) the child was funded `params.gas`.
  have hchildFunded : child.exec.gasAvailable.toNat = cp.gas.toNat := by
    rw [beginCall_inl_gas hcbegin]
  -- (d) resumed parent gas ≤ saved-parent gas + child-returned gas.
  have hresume := resumeAfterCall_gas_le childRes.toCallResult pending
  rw [toCallResult_gasRemaining] at hresume
  -- chain (a)–(d).
  omega

/-! ## 4. `Runs` never increases gas — the §3.4 "holds across calls" lemma -/

/-- **`Runs` gas monotonicity (`docs/ir-design-v2.md` §3.4).** Across any flat
`Runs fr last` — opcode steps and returning external CALLs (`.call`/`CallReturns` nodes)
in any order — the machine's remaining gas does not increase:
`last.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat`.

By induction on the `Runs` derivation: `refl` (equal endpoints), `step` (one opcode never
raises gas, by `StepsTo.gas_le`, then transitively), and `call` (the 63/64 net-debit,
`CallReturns.gas_le`, then transitively). This is the structural fact that makes §3.4's
"the monotone gas-read law holds across calls" a **real proof**: any two `gasRead` values
realised on a `Runs` path are non-increasing because the `gasAvailable.toNat` between them
is, including through every `.call` node. **No hypothesis** on the calls returning beyond
what `Runs.call`/`CallReturns` already carry, and **no per-opcode cost** is assumed. -/
theorem Runs.gasAvailable_le {fr last : Frame} (h : Runs fr last) :
    last.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat := by
  induction h with
  | refl _ => exact Nat.le_refl _
  | step hstep _ ih => exact le_trans ih (StepsTo.gas_le hstep)
  | call hcall _ ih => exact le_trans ih (CallReturns.gas_le hcall)

-- Build-enforced axiom-cleanliness guards: the headline and its two load-bearing
-- supporting lemmas depend only on `[propext, Classical.choice, Quot.sound]`.
#print axioms Runs.gasAvailable_le
#print axioms drive_gasRemaining_le_totalGas
#print axioms CallReturns.gas_le

end BytecodeLayer.Hoare
