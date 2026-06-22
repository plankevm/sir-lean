import Evm
import BytecodeLayer.Semantics.Gas
import BytecodeLayer.Semantics.System
import BytecodeLayer.Semantics.Interpreter.Drive

/-!
# The `drive` step measure (`Measure`)

Why `drive` always terminates within its fuel, as a **measure argument** —
out-of-gas is itself a halt, so the gas bounds the number of `drive` recursions
and there is no separate termination hypothesis. `totalGas` sums the gas held by
the active component (running frame or finished result) and every suspended
parent on the pending stack; the measure `μ` is
`2 * totalGas + 2 * stack.length + (1 or 2)`. It strictly decreases on every
`drive` recursion and starts below `seedFuel`.

This file is the **framework**. It defines `μ` and proves the general bound
`mu_bound` over arbitrary pending stacks — discharging obligations 1, 2, 6
(`resumeAfterCall_gas_le`), 7 (resume fault) inline — parametric over the one fact
the induction cannot supply generically: `gasFundsDescent`. That fact says each
CALL/CREATE descent and `System`-`.next` fallback strictly drops `μ`, because a
descent is funded out of the parent's gas with ≥2 to spare. It is *declared* here
(and `messageCall_never_outOfFuel_of_gasFundsDescent` is the boundary theorem
modulo it) and *discharged* in `Semantics/Interpreter/NeverOutOfFuel.lean`, which
then concludes the unconditional headline `messageCall_never_outOfFuel`.

The CREATE descent (4') relies on the kind-aware `Pending.savedGas` below, which
withholds the forwarded `allButOneSixtyFourth` from the measure (the child already
counts it) so an open CREATE descent isn't double-counted. Relevant leanevm defs:
`callArm`/`createArm` (`Evm/Semantics/System.lean`), `beginCall`
(`Evm/Semantics/Call.lean`), `beginCreate` (`Evm/Semantics/Create.lean`), and the
gas helpers `callGasCap`/`callExtraCost`/`allButOneSixtyFourth`
(`Evm/Semantics/Gas.lean`).
-/

namespace BytecodeLayer.Interpreter
open Evm
open GasConstants
open BytecodeLayer.Gas
open BytecodeLayer.System

/-! ## The measure -/

/-- The gas a suspended parent frame holds, as it contributes to the measure.

For a suspended CALL parent this is its full saved `gasAvailable` (the parent was
debited the forwarded gas *before* it was saved, so its saved gas is genuinely
"its own"). For a suspended CREATE parent, however, `createArm` saves the parent
with its *full* undebited gas while forwarding `allButOneSixtyFourth` of it to the
child; that forwarded part is already counted in the child's `activeGas`, so we
subtract it here to avoid double-counting during an open CREATE descent.
`resumeAfterCreate` later reconciles by returning the lent part to the parent. -/
def Pending.savedGas : Pending → ℕ
  | .call pd   => pd.frame.exec.gasAvailable.toNat
  | .create pd => pd.frame.exec.gasAvailable.toNat
                    - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat

/-- Gas held by the active component of a `drive` state. -/
def activeGas : (Frame ⊕ FrameResult) → ℕ
  | .inl fr => fr.exec.gasAvailable.toNat
  | .inr r  => FrameResult.gasRemaining r

/-- Total gas in the machine: the active component plus every suspended parent. -/
def totalGas (stack : List Pending) (state : Frame ⊕ FrameResult) : ℕ :=
  activeGas state + (stack.map Pending.savedGas).sum

/-- The `.inl`/`.inr` tag-bit: `2` for a running frame, `1` for a result. The
gap makes a `.halted` delivery (`.inl → .inr`, same gas/stack) drop μ. -/
def tagBit : (Frame ⊕ FrameResult) → ℕ
  | .inl _ => 2
  | .inr _ => 1

@[simp] theorem tagBit_inl (fr : Frame) : tagBit (.inl fr) = 2 := rfl
@[simp] theorem tagBit_inr (r : FrameResult) : tagBit (.inr r) = 1 := rfl

/-- The measure. -/
def μ (stack : List Pending) (state : Frame ⊕ FrameResult) : ℕ :=
  2 * totalGas stack state + 2 * stack.length + tagBit state

@[simp] theorem totalGas_cons (p : Pending) (stack : List Pending)
    (state : Frame ⊕ FrameResult) :
    totalGas (p :: stack) state
      = activeGas state + Pending.savedGas p + (stack.map Pending.savedGas).sum := by
  simp only [totalGas, List.map_cons, List.sum_cons]; omega

theorem μ_pos (stack : List Pending) (state : Frame ⊕ FrameResult) : 1 ≤ μ stack state := by
  unfold μ tagBit; split <;> omega


/-! ## General measure bound (induction skeleton)

The full `mu_bound` over arbitrary pending stacks. Obligations 1 (non-`System`
`.next`), 2 (`.halted`), 6 (`resume = .ok`), and 7 (`resume = .error`) are
discharged inline below. The CALL/CREATE *descent* obligations (3 — `System`
`.next` fallbacks; 4/5 — `.needsCall`/`.needsCreate` into a child) are taken as
hypotheses `gasFundsDescent` here; closing them (the 63/64 / stipend / `extraCost`
arithmetic, mined from M2) removes the hypothesis and yields the unconditional
general theorem. -/

/-- Each CALL/CREATE descent and each `System` `.next` fallback strictly drops
the measure by enough: `μ` of the recursive `drive` target is `< μ` of the
current state. This is the single remaining (gas-arithmetic) obligation. -/
def gasFundsDescent : Prop :=
  -- (3) System `.next` fallback: totalGas drops ≥ 1
  (∀ (fr : Frame) (exec' : ExecutionState) (stack : List Pending),
      stepFrame fr = .next exec' →
      (∃ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s) →
      totalGas stack (.inl { fr with exec := exec' }) < totalGas stack (.inl fr))
  ∧ -- (4) needsCall descent into a child
  (∀ (fr : Frame) (params : CallParams) (pending : PendingCall) (child : Frame) (_stack : List Pending),
      stepFrame fr = .needsCall params pending → beginCall params = .inl child →
      activeGas (.inl child) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (5a) needsCall precompile (immediate result)
  (∀ (fr : Frame) (params : CallParams) (pending : PendingCall) (result : CallResult) (_stack : List Pending),
      stepFrame fr = .needsCall params pending → beginCall params = .inr result →
      FrameResult.gasRemaining (.call result) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (4') needsCreate descent into a child
  (∀ (fr : Frame) (params : CreateParams) (pending : PendingCreate) (child : Frame) (_stack : List Pending),
      stepFrame fr = .needsCreate params pending → beginCreate params = .ok child →
      activeGas (.inl child) + Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (5b) needsCreate failure (zeroed result)
  (∀ (fr : Frame) (params : CreateParams) (pending : PendingCreate) (_stack : List Pending),
      stepFrame fr = .needsCreate params pending →
      Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr))

/-- **The general measure bound.** `μ stack state ≤ f → drive f stack state ≠
OutOfFuel`. By induction on `f`, with the per-transition decrease for every
`drive` branch; descent/fallback decreases come from `gasFundsDescent`. -/
theorem mu_bound (hd : gasFundsDescent) :
    ∀ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult),
      μ stack state ≤ f → drive f stack state ≠ .error .OutOfFuel := by
  obtain ⟨hd3, hd4, hd5, hd4', hd5'⟩ := hd
  intro f
  induction f with
  | zero =>
    intro stack state hf
    have := μ_pos stack state; omega
  | succ n ih =>
    intro stack state hf
    conv_lhs => unfold drive
    dsimp only
    cases state with
    | inr result =>
      dsimp only
      cases hstk : stack with
      | nil => simp
      | cons pending rest =>
        dsimp only
        cases hres : pending.resume result with
        | ok parent =>
          dsimp only
          -- delivery: stack shrinks, totalGas conserved (resume doesn't create gas)
          apply ih
          have hcons : activeGas (.inl parent) + (rest.map Pending.savedGas).sum
              ≤ FrameResult.gasRemaining result + Pending.savedGas pending
                + (rest.map Pending.savedGas).sum := by
            have : activeGas (.inl parent)
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
                have hb := resumeAfterCreate_gas_le_savedGas (result := result.toCreateResult) (pd := pd) hres
                rw [toCreateResult_gasRemaining] at hb
                simp only [activeGas, Pending.savedGas]; omega
            omega
          subst hstk
          simp only [activeGas] at hcons
          simp only [μ, tagBit, totalGas, activeGas, List.length_cons] at hf ⊢
          simp only [List.map_cons, List.sum_cons] at hf
          omega
        | error e =>
          dsimp only
          -- resume faulted: parent halts exceptionally, stack shrinks
          apply ih
          subst hstk
          -- endFrame (.exception) gas is 0
          have hz : activeGas (.inr (endFrame pending.frame (.exception e))) = 0 := by
            simp only [activeGas]
            unfold endFrame; cases pending.frame.kind <;>
              simp [FrameResult.gasRemaining, endCall, endCreate, UInt64.toNat_ofNat]
          simp only [μ, tagBit, totalGas, List.length_cons, List.map_cons, List.sum_cons, hz] at hf ⊢
          omega
    | inl current =>
      dsimp only
      cases hstep : stepFrame current with
      | next exec' =>
        dsimp only
        by_cases hsys : ∃ s, (decode current.exec.executionEnv.code current.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s
        · -- (3) System fallback
          apply ih
          have hdrop := hd3 current exec' stack hstep hsys
          simp only [μ, tagBit] at hf ⊢
          omega
        · -- (1) non-System next: gas strictly drops
          apply ih
          push Not at hsys
          have hlt : exec'.gasAvailable.toNat < current.exec.gasAvailable.toNat :=
            stepFrame_next_lt hsys hstep
          simp only [μ, tagBit, totalGas, activeGas] at hf ⊢
          omega
      | halted halt =>
        dsimp only
        -- (2) halt: state becomes .inr, gas ≤ current's
        apply ih
        have hle := endFrame_gasRemaining_le hstep
        simp only [μ, tagBit, totalGas, activeGas] at hf ⊢
        omega
      | needsCall params pending =>
        dsimp only
        cases hbc : beginCall params with
        | inl child =>
          dsimp only
          apply ih
          have hdrop := hd4 current params pending child stack hstep hbc
          simp only [μ, tagBit, totalGas, activeGas, Pending.savedGas, List.length_cons, List.map_cons, List.sum_cons] at hf ⊢
          simp only [activeGas, Pending.savedGas] at hdrop
          omega
        | inr result =>
          dsimp only
          apply ih
          have hdrop := hd5 current params pending result stack hstep hbc
          simp only [μ, tagBit, totalGas, activeGas, Pending.savedGas, List.length_cons, List.map_cons, List.sum_cons] at hf ⊢
          simp only [activeGas, Pending.savedGas] at hdrop
          omega
      | needsCreate params pending =>
        dsimp only
        cases hbcr : beginCreate params with
        | ok child =>
          dsimp only
          apply ih
          have hdrop := hd4' current params pending child stack hstep hbcr
          simp only [μ, tagBit, totalGas, activeGas, Pending.savedGas, List.length_cons, List.map_cons, List.sum_cons] at hf ⊢
          simp only [activeGas, Pending.savedGas] at hdrop
          omega
        | error e =>
          dsimp only
          apply ih
          have hdrop := hd5' current params pending stack hstep
          simp only [μ, tagBit, totalGas, activeGas, FrameResult.gasRemaining, UInt64.toNat_ofNat, Pending.savedGas, List.length_cons, List.map_cons, List.sum_cons] at hf ⊢
          simp only [activeGas, Pending.savedGas] at hdrop
          omega

/-- **General `messageCall` never out-of-fuel**, modulo `gasFundsDescent`. The
measure starts at `μ [] (.inl frame) = 2 * p.gas.toNat + 2 ≤ seedFuel p.gas`. -/
theorem messageCall_never_outOfFuel_of_gasFundsDescent (hd : gasFundsDescent) (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel := by
  unfold messageCall
  cases h : beginCall p with
  | inr result => simp
  | inl frame =>
    simp only []
    intro hc
    have hg : frame.exec.gasAvailable = p.gas := beginCall_inl_gas h
    have hμ : μ [] (.inl frame) ≤ seedFuel p.gas := by
      simp only [μ, tagBit, totalGas, activeGas, List.map_nil, List.sum_nil, List.length_nil]
      unfold seedFuel; rw [hg]; omega
    have hb : drive (seedFuel p.gas) [] (.inl frame) ≠ .error .OutOfFuel :=
      mu_bound hd (seedFuel p.gas) [] (.inl frame) hμ
    cases hd' : drive (seedFuel p.gas) [] (.inl frame) with
    | error e => rw [hd'] at hc; simp [Functor.map, Except.map] at hc; rw [hc] at hd'; exact hb hd'
    | ok r => rw [hd'] at hc; simp [Functor.map, Except.map] at hc

end BytecodeLayer.Interpreter
