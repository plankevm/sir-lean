import BytecodeLayer.Semantics.Interpreter.Measure
import BytecodeLayer.Semantics.Gas
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.Semantics.Precompiles
import BytecodeLayer.Semantics.Dispatch

/-!
# `drive` never runs out of fuel — unconditional (`NeverOutOfFuel`)

The headline:

  `messageCall_never_outOfFuel (p : CallParams) : messageCall p ≠ .error .OutOfFuel`

for every program and gas, with no termination hypothesis and no `Frame`/fuel in
the statement — out-of-gas is itself a halt, so the gas bounds the step count.

The measure framework lives in `Semantics/Interpreter/Measure.lean`, which proves
the general bound `mu_bound` modulo the one fact it cannot supply generically:
`gasFundsDescent`. This file **discharges** `gasFundsDescent` (the CALL/CREATE
*descent* and `System`-`.next`-*fallback* gas inequalities, obligations 3/4/5a/4'/5b),
assembles them into `gasFundsDescent_holds`, and feeds it to
`messageCall_never_outOfFuel_of_gasFundsDescent` to land the unconditional theorem.

## The arithmetic, generously

The descent semantics (`callArm`/`createArm`, `Evm/Semantics/System.lean`) charge
the parent `gasCap + extraCost` *before* suspending and forward the child
`childGas = gasCap (+ Gcallstipend when value ≠ 0)`. The forwarded gas is exactly
conserved against the parent's saved gas, and the call's *own* cost (`extraCost`,
≥ `Gcoldaccountaccess`/`Gwarmaccess` ≥ 100, or ≥ `Gcallvalue` = 9000 with value)
strictly dominates the tiny `+2` measure slack and the `Gcallstipend` (2300)
added to the child. No tight arithmetic is needed — only "the call's own cost is
a positive constant bigger than 2 (resp. 2302)."
-/

namespace BytecodeLayer.Interpreter
open Evm
open Evm.Operation
open GasConstants
open BytecodeLayer.Precompiles
open BytecodeLayer.UInt64
open BytecodeLayer.Gas
open BytecodeLayer.Dispatch
open BytecodeLayer.System

/-! ## The five `gasFundsDescent` conjuncts

Conjuncts (3), (4), (5a), (4'), (5b) are exactly the per-transition decreases
that `mu_bound` needs, and each follows from the `systemOp`/`stepFrame`
inversions plus the gas arithmetic above. They are stated here in the precise
`Prop` shapes of `gasFundsDescent` and assembled into `gasFundsDescent_holds`, which
discharges the last hypothesis of the general theorem. -/

/-- **Conjunct (3).** A `System`-op `.next` fallback strictly drops `totalGas`. -/
theorem gasFundsDescent_conj3
    (fr : Frame) (exec' : ExecutionState) (stack : List Pending)
    (hstep : stepFrame fr = .next exec')
    (hsys : ∃ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s) :
    totalGas stack (.inl { fr with exec := exec' }) < totalGas stack (.inl fr) := by
  obtain ⟨s, hs⟩ := hsys
  have hsop := stepFrame_next_systemOp hs hstep
  have hlt := systemOp_next_gas hsop
  simp only [totalGas, activeGas]
  omega

/-- **Conjunct (4).** A `.needsCall` descent into a code child: child gas +
saved parent gas + 2 ≤ pre-step gas. -/
theorem gasFundsDescent_conj4
    (fr : Frame) (params : CallParams) (pending : PendingCall) (child : Frame) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCall params pending) (hbc : beginCall params = .inl child) :
    activeGas (.inl child) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCall_systemOp hstep
  have hgas := systemOp_needsCall_gas hsop
  have hchild : child.exec.gasAvailable = params.gas := beginCall_inl_gas hbc
  simp only [activeGas, Pending.savedGas]
  rw [hchild]
  exact hgas

/-- **Conjunct (5a).** A `.needsCall` precompile (immediate result): result gas +
saved parent gas + 2 ≤ pre-step gas. -/
theorem gasFundsDescent_conj5a
    (fr : Frame) (params : CallParams) (pending : PendingCall) (result : CallResult) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCall params pending) (hbc : beginCall params = .inr result) :
    FrameResult.gasRemaining (.call result) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCall_systemOp hstep
  have hgas := systemOp_needsCall_gas hsop
  have hres : result.gasRemaining.toNat ≤ params.gas.toNat := beginCall_inr_gas hbc
  simp only [FrameResult.gasRemaining, activeGas, Pending.savedGas]
  omega

/-! ## Conjunct (4') — `needsCreate` descent

For a CREATE/CREATE2 descent `stepFrame fr = .needsCreate params pending` with
`beginCreate params = child` (total), the kind-aware `Pending.savedGas` makes the
descent conserve the measure (plus the `createCost ≥ 2` slack):

* the suspended parent's frame keeps the full charged gas `g`, so
  `Pending.savedGas (.create pending) = g − allButOneSixtyFourth g`;
* the child is forwarded `allButOneSixtyFourth g`, so
  `activeGas (.inl child) = allButOneSixtyFourth g`.

Hence the LHS is
`allButOneSixtyFourth g + (g − allButOneSixtyFourth g) + 2 = g + 2`, and
`g + 2 ≤ activeGas (.inl fr)` is exactly `systemOp_needsCreate_savedGas` (the
`createCost`/`create2Cost` charged in `systemOp` before `createArm` covers the
`+2`). The forwarded `allButOneSixtyFourth g` is no longer double-counted: the
measure subtracts it from the parent precisely because the child holds it, and
`resumeAfterCreate` returns it on delivery (`mu_bound`'s create-resume case via
`resumeAfterCreate_gas_le_savedGas`). -/

/-- **Conjunct (4').** A `.needsCreate` descent into a code child: child gas +
saved parent gas + 2 ≤ pre-step gas. The child holds `allButOneSixtyFourth g`,
the (kind-aware) saved parent holds `g − allButOneSixtyFourth g`, and the
`createCost` charged before `createArm` covers the `+2`. -/
theorem gasFundsDescent_conj4'
    (fr : Frame) (params : CreateParams) (pending : PendingCreate) (child : Frame) (_stack : List Pending)
    (hstep : stepFrame fr = .needsCreate params pending) (hbcr : beginCreate params = child) :
    activeGas (.inl child) + Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr) := by
  obtain ⟨s, hsop⟩ := stepFrame_needsCreate_systemOp hstep
  have hsaved := systemOp_needsCreate_savedGas hsop
  have hchild := systemOp_needsCreate_childGas hsop
  have hcg : child.exec.gasAvailable = params.gas := by rw [← hbcr]; exact beginCreate_gas
  -- `params.gas = .ofNat (allButOneSixtyFourth pd.gas)`, and the round-trip is exact.
  have habf_le : allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat
      ≤ pending.frame.exec.gasAvailable.toNat := by unfold allButOneSixtyFourth; omega
  have hlt : allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt habf_le pending.frame.exec.gasAvailable.toNat_lt
  have hchildNat : child.exec.gasAvailable.toNat
      = allButOneSixtyFourth pending.frame.exec.gasAvailable.toNat := by
    rw [hcg, hchild, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hlt
  simp only [activeGas, Pending.savedGas]
  rw [hchildNat]
  omega

/-- **`gasFundsDescent` discharged.** All five per-transition decrease obligations
hold; the create descent (4') is sound under the kind-aware `Pending.savedGas`. -/
theorem gasFundsDescent_holds : gasFundsDescent :=
  ⟨gasFundsDescent_conj3, gasFundsDescent_conj4, gasFundsDescent_conj5a,
    gasFundsDescent_conj4'⟩

/-- **General `messageCall` never out-of-fuel — unconditional.** No
`gasFundsDescent`, no `Frame`/fuel hypothesis: for every `CallParams`, the message
call never returns `OutOfFuel`. -/
theorem messageCall_never_outOfFuel (p : CallParams) :
    messageCall p ≠ .error .OutOfFuel :=
  messageCall_never_outOfFuel_of_gasFundsDescent gasFundsDescent_holds p

end BytecodeLayer.Interpreter

