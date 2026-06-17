import Evm
import BytecodeLayer.Reasoning.StepGas
import BytecodeLayer.Reasoning.Fuel

/-!
# `drive` never runs out of fuel (unconditional)

The target: `drive (seedFuel gas) [] (.inl fr) ≠ .error .OutOfFuel`, with no
termination hypothesis — out-of-gas is itself a halt, so the number of `drive`
recursions is bounded by the gas.

The proof is a measure argument. `totalGas` sums the gas held by the active
component (running frame or finished result) and every suspended parent on the
pending stack. The measure `μ` is `2 * totalGas + 2 * stack.length + (1 or 2)`;
it strictly decreases on every `drive` recursion, and starts below `seedFuel`.

## Status

* **Fully proven, unconditional in the gas:**
  - `mu_bound` — the **general** measure-induction skeleton over arbitrary
    pending stacks, discharging obligations 1, 2, 6 (`resumeAfterCall_gas_le`),
    7 (resume fault) inline.
  - `messageCall_never_outOfFuel_of_descentDrops` — the general boundary theorem
    **modulo** `DescentDrops`.
* **Discharged:** `DescentDrops` — the CALL/CREATE *descent / `System`-`.next`-
  fallback* gas arithmetic (obligations 3, 4, 5a, 4', 5b) — is fully proven in
  `Proof/DescentDrops.lean` (`descentDrops_holds`). The CREATE descent (4')
  relies on the kind-aware `Pending.savedGas` below, which withholds the
  forwarded `allButOneSixtyFourth` from the measure (since the child already
  counts it) and so does not double-count during an open CREATE descent. This
  yields the **unconditional** general theorem
  `BytecodeLayer.Proof.messageCall_never_outOfFuel`. The relevant leanevm defs
  are `callArm`/`createArm` (`Evm/Semantics/System.lean`), `beginCall`
  (`Evm/Semantics/Call.lean`), `beginCreate` (`Evm/Semantics/Create.lean`), and
  the gas helpers `callGasCap`/`callExtraCost`/`allButOneSixtyFourth`
  (`Evm/Semantics/Gas.lean`).
-/

namespace BytecodeLayer
open Evm
open GasConstants

/-! ## Gas accessors -/

/-- The gas a finished frame result still carries. -/
def FrameResult.gasRemaining : FrameResult → ℕ
  | .call r   => r.gasRemaining.toNat
  | .create r => r.gasRemaining.toNat

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

/-! ## Obligation 2 — halting: `endFrame` never carries more gas than the frame

A halting step's result keeps at most the frame's available gas. `endCall` /
`endCreate` set `gasRemaining` to either `0`, a `revert`-carried gas, or the
halt's `exec.gasAvailable` (possibly minus a deposit). We bound the gas carried
by every `FrameHalt` reachable from `stepFrame` by the frame's pre-step gas. -/

theorem ite_le {c : Prop} [Decidable c] {a b m : ℕ} (ha : a ≤ m) (hb : b ≤ m) :
    (if c then a else b) ≤ m := by split <;> assumption

/-- The gas a `FrameHalt` carries. -/
def FrameHalt.gasOf : FrameHalt → ℕ
  | .success exec _    => exec.gasAvailable.toNat
  | .revert g _        => g.toNat
  | .exception _       => 0

theorem charge_gasOf_le {cost : ℕ} {exec exec' : ExecutionState}
    (h : charge cost exec = .ok exec') :
    exec'.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_le h

theorem chargeMem_gasOf_le {exec exec' : ExecutionState} {off size : UInt256}
    (h : chargeMemExpansion exec off size = .ok exec') :
    exec'.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le h

/-- `returnOrRevertOp` halts with gas ≤ the input frame gas. -/
theorem returnOrRevertOp_gasOf_le {op : Operation.SystemOp} {exec : ExecutionState} {halt : FrameHalt}
    (h : returnOrRevertOp op exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  rw [returnOrRevertOp] at h
  cases hp : exec.stack.pop2 with
  | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨s, off, size⟩ := v; rw [hp] at h
    simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hm : chargeMemExpansion exec off size with
    | error e => rw [hm] at h; simp at h
    | ok ec =>
      rw [hm] at h
      have hle : ec.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasOf_le hm
      simp only [pure, Except.pure] at h
      split at h <;>
        · simp only [Except.ok.injEq, Signal.halted.injEq] at h
          subst h
          simp only [FrameHalt.gasOf, gasNat_replaceStackAndIncrPC]
          exact hle

/-- `selfdestructOp` halts with gas ≤ the input frame gas. -/
theorem selfdestructOp_gasOf_le {exec : ExecutionState} {halt : FrameHalt}
    (h : selfdestructOp exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  rw [selfdestructOp] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp [bind, Except.bind] at h
  | ok _ =>
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hp : exec.stack.pop with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, rw'⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hc : charge (selfdestructCost _ _) exec with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h
        have hle : ec.gasAvailable.toNat ≤ exec.gasAvailable.toNat := charge_gasOf_le hc
        simp only [] at h
        -- the result is `.halted (.success (exec'.replaceStackAndIncrPC stack) .empty)`
        -- where exec' is ec with only account/substate fields changed (gas preserved).
        split at h <;>
          · simp only [Except.ok.injEq, Signal.halted.injEq] at h
            subst h
            simp only [FrameHalt.gasOf, gasNat_replaceStackAndIncrPC]
            exact hle

/-- `haltOp` halts with gas ≤ the input frame gas. -/
theorem haltOp_gasOf_le {op : Operation.SystemOp} {exec : ExecutionState} {halt : FrameHalt}
    (h : haltOp op exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  unfold haltOp at h
  cases op with
  | STOP =>
    simp only [Except.ok.injEq, Signal.halted.injEq] at h
    subst h; simp only [FrameHalt.gasOf]; omega
  | RETURN => exact returnOrRevertOp_gasOf_le h
  | REVERT => exact returnOrRevertOp_gasOf_le h
  | SELFDESTRUCT => exact selfdestructOp_gasOf_le h
  | INVALID => simp [throw, throwThe, MonadExceptOf.throw] at h
  | _ => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A `Step` `s` *never halts* if no `.ok (.halted _)` is among its outputs. The
non-`System` dispatcher arms (and the helper combinators that build them) enjoy
this: their `.ok` outputs are all `continueWith` (`.next`) values; `.error`s and
`throw`s are not `.ok`. -/
def neverHalts (s : Step) : Prop := ∀ hl, s ≠ .ok (.halted hl)

theorem neverHalts_continueWith (e : ExecutionState) : neverHalts (continueWith e) := by
  intro hl he; simp [continueWith] at he

theorem neverHalts_error (e : ExecutionException) : neverHalts (.error e : Step) := by
  intro hl he; simp at he

theorem neverHalts_throw (e : ExecutionException) :
    neverHalts (throw e : Step) := by
  intro hl he; simp [throw, throwThe, MonadExceptOf.throw] at he

/-- An `.error`-shaped `Step` is not `.ok (.halted _)`. Closes the throw branches
after `throw`/`bind` are unfolded to `.error`. -/
theorem error_ne_okHalted (e : ExecutionException) (hl : FrameHalt) :
    ¬ ((.error e : Step) = .ok (.halted hl)) := by simp

theorem neverHalts_bind_except {α : Type} (m : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, m = .ok a → neverHalts (k a)) : neverHalts (m >>= k) := by
  intro hl he
  cases hm : m with
  | error e => rw [hm] at he; simp [bind, Except.bind] at he
  | ok a => rw [hm] at he; simp only [bind, Except.bind] at he; exact hk a hm hl he

theorem neverHalts_optionBind {α : Type} (o : Option α) (k : α → Step)
    (hk : ∀ a, o = some a → neverHalts (k a)) :
    neverHalts ((o : Except ExecutionException α) >>= k) := by
  intro hl he
  cases ho : o with
  | none => rw [ho] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
  | some a =>
    rw [ho] at he; simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    exact hk a ho hl he

/-- A `charge`-then-`k` step never halts if `k` never does. -/
theorem neverHalts_chargeBind {cost : ℕ} {exec : ExecutionState} {k : ExecutionState → Step}
    (hk : ∀ ec, charge cost exec = .ok ec → neverHalts (k ec)) :
    neverHalts (charge cost exec >>= k) :=
  neverHalts_bind_except _ _ hk

/-- A `chargeMemExpansion`-then-`k` step never halts if `k` never does. -/
theorem neverHalts_memChargeBind {exec : ExecutionState} {off size : UInt256}
    {k : ExecutionState → Step} (hk : ∀ ec, neverHalts (k ec)) :
    neverHalts (chargeMemExpansion exec off size >>= k) := by
  apply neverHalts_bind_except; intro a _; exact hk a

theorem unOp_neverHalts {f : UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (unOp f exec cost) := by
  rw [unOp]; apply neverHalts_chargeBind; intro ec _
  apply neverHalts_optionBind; rintro ⟨s, a⟩ _; exact neverHalts_continueWith _

theorem binOp_neverHalts {f : UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (binOp f exec cost) := by
  rw [binOp]; apply neverHalts_chargeBind; intro ec _
  apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _; exact neverHalts_continueWith _

theorem ternOp_neverHalts {f : UInt256 → UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (ternOp f exec cost) := by
  rw [ternOp]; apply neverHalts_chargeBind; intro ec _
  apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _; exact neverHalts_continueWith _

theorem pushOp_neverHalts {v : ExecutionState → UInt256} {exec : ExecutionState} {cost : ℕ} :
    neverHalts (pushOp v exec cost) := by
  rw [pushOp]; apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _

theorem unStateOp_neverHalts {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec : ExecutionState} :
    neverHalts (unStateOp f cost exec) := by
  rw [unStateOp]; apply neverHalts_optionBind; rintro ⟨s, a⟩ _
  apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _

theorem dup_neverHalts {n : ℕ} {exec : ExecutionState} : neverHalts (dup n exec) := by
  rw [dup]; apply neverHalts_chargeBind; intro ec _
  unfold neverHalts; intro hl he
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v => rw [hg] at he; simp [continueWith] at he

theorem swap_neverHalts {n : ℕ} {exec : ExecutionState} : neverHalts (swap n exec) := by
  rw [swap]; apply neverHalts_chargeBind; intro ec _
  unfold neverHalts; intro hl he
  by_cases hg : List.length (ec.stack.take (n + 1)) = (n + 1)
  · rw [if_pos hg] at he; simp [continueWith] at he
  · rw [if_neg hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he

theorem logArm_neverHalts {exec : ExecutionState} {stack : Stack UInt256}
    {offset size : UInt256} {topics : Array UInt256} :
    neverHalts (logArm exec stack offset size topics) := by
  rw [logArm]; apply neverHalts_bind_except; intro _ _
  apply neverHalts_memChargeBind; intro ec
  apply neverHalts_chargeBind; intro ec2 _; exact neverHalts_continueWith _

theorem smsfOp_neverHalts {op : Operation.SmsfOp} {fr : Frame} {exec : ExecutionState} :
    neverHalts (smsfOp op fr exec) := by
  unfold smsfOp
  cases op with
  | POP =>
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, a⟩ _; exact neverHalts_continueWith _
  | MLOAD =>
    apply neverHalts_optionBind; rintro ⟨s, a⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | MSTORE =>
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | MSTORE8 =>
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | SLOAD => exact unStateOp_neverHalts
  | SSTORE =>
    apply neverHalts_bind_except; intro _ _
    by_cases hg : exec.gasAvailable.toNat ≤ Gcallstipend
    · simp only [hg, if_true]; exact neverHalts_throw _
    · simp only [hg, if_false]
      apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
      apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _
  | TLOAD => exact unStateOp_neverHalts
  | TSTORE =>
    apply neverHalts_bind_except; intro _ _
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _; exact neverHalts_continueWith _
  | MSIZE => exact pushOp_neverHalts
  | GAS => exact pushOp_neverHalts
  | JUMP =>
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, d⟩ _ hl he
    dsimp only at he
    split at he <;> simp [continueWith] at he
  | JUMPI =>
    apply neverHalts_chargeBind; intro ec _
    apply neverHalts_optionBind; rintro ⟨s, d, c⟩ _ hl he
    dsimp only at he
    split at he
    · split at he <;> simp [continueWith] at he
    · simp [continueWith] at he
  | PC => exact pushOp_neverHalts
  | JUMPDEST =>
    apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _
  | MCOPY =>
    apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _

/-- The non-`System` dispatcher arms never halt. -/
theorem dispatch_neverHalts {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec : ExecutionState} (hne : ∀ s, op ≠ .System s) :
    neverHalts (dispatch op arg fr exec) := by
  unfold dispatch
  cases op with
  | System s => exact absurd rfl (hne s)
  | KECCAK256 =>
    apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
    apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
    exact neverHalts_continueWith _
  | Smsf s => exact smsfOp_neverHalts
  | Log l => cases l <;>
      (apply neverHalts_optionBind; rintro _ _; exact logArm_neverHalts)
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_neverHalts
    | _ =>
      apply neverHalts_chargeBind; intro ec _ hl he
      cases arg <;> simp [continueWith, throw, throwThe, MonadExceptOf.throw] at he
  | Dup d => exact dup_neverHalts
  | Swap s => exact swap_neverHalts
  | ArithLogic a => cases a <;>
      first
        | exact binOp_neverHalts | exact unOp_neverHalts | exact ternOp_neverHalts
        | (apply neverHalts_optionBind; rintro ⟨s, a, b⟩ _
           apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _)
  | Env e =>
    cases e <;>
      first
        | exact pushOp_neverHalts | exact unStateOp_neverHalts
        | (apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _
           apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
           exact neverHalts_continueWith _)
        | (apply neverHalts_optionBind; rintro ⟨s, a, b, c, d⟩ _
           apply neverHalts_memChargeBind; intro ec; apply neverHalts_chargeBind; intro ec2 _
           exact neverHalts_continueWith _)
        | (apply neverHalts_optionBind; rintro ⟨s, a, b, c⟩ _ hl he
           revert he; dsimp only; split
           · intro he; simp [bind, Except.bind] at he
           · exact (neverHalts_memChargeBind (k := _)
               (fun ec => neverHalts_chargeBind (fun ec2 _ => neverHalts_continueWith _)) hl))
  | Block b =>
    cases b <;>
      first
        | exact pushOp_neverHalts | exact unStateOp_neverHalts
        | (apply neverHalts_optionBind; rintro ⟨s, i⟩ _
           apply neverHalts_chargeBind; intro ec _; exact neverHalts_continueWith _)

/-- `callArm` never halts: its outputs are `.needsCall` or `.next`. -/
theorem callArm_neverHalts {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} :
    neverHalts (callArm fr exec stack gas caller recipient codeAddress value apparentValue
      inOffset inSize outOffset outSize permission) := by
  rw [callArm]
  -- `let some words' := … | throw .OutOfGas` then two charges then an `if`.
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none =>
    intro hl he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some words' =>
    simp only [bind, Except.bind]
    apply neverHalts_chargeBind; intro ec1 _
    apply neverHalts_chargeBind; intro ec2 _
    unfold neverHalts; intro hl he
    split at he <;> simp at he

/-- `createArm` never halts: its outputs are `.needsCreate` or `.next`. -/
theorem createArm_neverHalts {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} :
    neverHalts (createArm fr exec stack value initOffset initSize salt) := by
  rw [createArm]
  -- `resumeAfterCreate r p >>= fun f => pure (.next f.exec)` is the only `.ok`
  -- output in every branch; the continuation yields `.next`, never `.halted`.
  have hk : ∀ (r : CreateResult) (p : PendingCreate),
      neverHalts (resumeAfterCreate r p >>= fun f => (pure (.next f.exec) : Step)) := by
    intro r p
    apply neverHalts_bind_except; intro f _ hl he
    simp [pure, Except.pure] at he
  simp only [bind, Except.bind, pure, Except.pure]
  intro hl he
  split at he
  · exact hk _ _ hl he
  · split at he
    · simp at he
    · exact hk _ _ hl he

/-- `systemOp` halts with gas ≤ the input frame gas. Halt ops go through
`haltOp_gasOf_le`; the CALL/CREATE family never halts. -/
theorem systemOp_gasOf_le {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {halt : FrameHalt} (h : systemOp op fr exec = .ok (.halted halt)) :
    FrameHalt.gasOf halt ≤ exec.gasAvailable.toNat := by
  unfold systemOp at h
  cases op with
  | STOP => exact haltOp_gasOf_le h
  | RETURN => exact haltOp_gasOf_le h
  | REVERT => exact haltOp_gasOf_le h
  | SELFDESTRUCT => exact haltOp_gasOf_le h
  | INVALID => exact haltOp_gasOf_le h
  | CALL =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, v, io, is, oo, os⟩ _
    unfold neverHalts; intro hl he
    revert he; simp only [bind, Except.bind, pure, Except.pure]
    split <;> intro he
    · simp at he
    · exact callArm_neverHalts hl he
  | CALLCODE =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, v, io, is, oo, os⟩ _
    exact callArm_neverHalts
  | DELEGATECALL =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, io, is, oo, os⟩ _
    exact callArm_neverHalts
  | STATICCALL =>
    refine absurd h ?_
    apply neverHalts_optionBind; rintro ⟨s, g, t, io, is, oo, os⟩ _
    exact callArm_neverHalts
  | CREATE =>
    refine absurd h ?_
    apply neverHalts_bind_except; intro _ _
    apply neverHalts_optionBind; rintro ⟨s, v, io, is⟩ _
    unfold neverHalts; intro hl he
    revert he; simp only [bind, Except.bind, pure, Except.pure]
    split <;> intro he
    · simp at he
    · revert he
      exact (neverHalts_memChargeBind (k := _)
        (fun ec => neverHalts_chargeBind (fun ec2 _ => createArm_neverHalts)) hl)
  | CREATE2 =>
    refine absurd h ?_
    apply neverHalts_bind_except; intro _ _
    apply neverHalts_optionBind; rintro ⟨s, v, io, is, salt⟩ _
    unfold neverHalts; intro hl he
    revert he; simp only [bind, Except.bind, pure, Except.pure]
    split <;> intro he
    · simp at he
    · revert he
      exact (neverHalts_memChargeBind (k := _)
        (fun ec => neverHalts_chargeBind (fun ec2 _ => createArm_neverHalts)) hl)

/-- A `.halted` from `stepFrame` carries gas ≤ the frame's pre-step gas. The
halt comes from INVALID/overflow (gas 0), a dispatch `.error` (gas 0), or a
dispatch `.ok (.halted)`. The last forces a `System` halt op (non-System arms
`neverHalt`), bounded by `haltOp_gasOf_le`. -/
theorem stepFrame_halted_gasOf_le {fr : Frame} {halt : FrameHalt}
    (h : stepFrame fr = .halted halt) :
    FrameHalt.gasOf halt ≤ fr.exec.gasAvailable.toNat := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · simp only [Signal.halted.injEq] at h; subst h; simp only [FrameHalt.gasOf]; omega
  · split at h
    · simp only [Signal.halted.injEq] at h; subst h; simp only [FrameHalt.gasOf]; omega
    · cases hdisp : dispatch op arg fr fr.exec with
      | error e =>
        rw [hdisp] at h; simp only [Signal.halted.injEq] at h
        subst h; simp only [FrameHalt.gasOf]; omega
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e => exact absurd h (by simp)
        | needsCall p pc => exact absurd h (by simp)
        | needsCreate p pc => exact absurd h (by simp)
        | halted hl =>
          simp only [Signal.halted.injEq] at h; subst h
          by_cases hsys : ∃ s, op = .System s
          · obtain ⟨s, rfl⟩ := hsys
            rw [dispatch] at hdisp
            exact systemOp_gasOf_le hdisp
          · exact absurd hdisp (dispatch_neverHalts (fun s hc => hsys ⟨s, hc⟩) hl)

/-- **Obligation 2.** `endFrame` of a `stepFrame`-halt keeps gas ≤ the frame gas. -/
theorem endFrame_gasRemaining_le {fr : Frame} {halt : FrameHalt}
    (h : stepFrame fr = .halted halt) :
    FrameResult.gasRemaining (endFrame fr halt) ≤ fr.exec.gasAvailable.toNat := by
  have hb := stepFrame_halted_gasOf_le h
  unfold endFrame
  cases fr.kind with
  | call cp =>
    simp only [FrameResult.gasRemaining]
    cases halt with
    | success exec output =>
      simp only [endCall, FrameHalt.gasOf] at hb ⊢; exact hb
    | revert g output => simp only [endCall, FrameHalt.gasOf] at hb ⊢; exact hb
    | exception e => simp only [endCall, UInt64.toNat_ofNat]; omega
  | create addr cp =>
    simp only [FrameResult.gasRemaining]
    cases halt with
    | success exec output =>
      simp only [endCreate, FrameHalt.gasOf] at hb ⊢
      rw [UInt64.toNat_ofNat']
      refine le_trans (Nat.mod_le _ _) (le_trans ?_ hb)
      exact ite_le (Nat.zero_le _) (Nat.sub_le _ _)
    | revert g output => simp only [endCreate, FrameHalt.gasOf] at hb ⊢; exact hb
    | exception e => simp only [endCreate, UInt64.toNat_ofNat]; omega

/-! ## Obligation 6 — delivery: `resume` does not create gas

`resumeAfterCall` restores the parent's gas to `parentSaved + childRemaining`
(memory writes preserve gas, the stack/pc rewrap preserves gas; UInt64 wrap can
only *lower* the `.toNat`). `resumeAfterCreate` keeps even less (it deducts the
`allButOneSixtyFourth` floor). Either way, the delivered parent's gas `.toNat` is
`≤ savedParent + childRemaining`. -/

theorem writeBytes_gasAvailable (src : ByteArray) (sa : ℕ) (self : MachineState)
    (da len : ℕ) : (writeBytes src sa self da len).gasAvailable = self.gasAvailable := rfl

/-- `toCallResult` preserves `gasRemaining` (matches `FrameResult.gasRemaining`). -/
theorem toCallResult_gasRemaining (r : FrameResult) :
    r.toCallResult.gasRemaining.toNat = FrameResult.gasRemaining r := by
  cases r <;> rfl

/-- `toCreateResult` preserves `gasRemaining` (matches `FrameResult.gasRemaining`). -/
theorem toCreateResult_gasRemaining (r : FrameResult) :
    r.toCreateResult.gasRemaining.toNat = FrameResult.gasRemaining r := by
  cases r <;> rfl

/-- `resumeAfterCall` gives the parent gas `.toNat ≤ savedParent + childRemaining`. -/
theorem resumeAfterCall_gas_le (result : CallResult) (pd : PendingCall) :
    (resumeAfterCall result pd).exec.gasAvailable.toNat
      ≤ pd.frame.exec.gasAvailable.toNat + result.gasRemaining.toNat := by
  unfold resumeAfterCall
  simp only [gasNat_replaceStackAndIncrPC]
  -- exec'.gasAvailable = machineWithOutput.gasAvailable + result.gasRemaining,
  -- machineWithOutput = writeBytes … pd.frame.exec.toMachineState …
  show (_ + result.gasRemaining).toNat ≤ _
  rw [UInt64.toNat_add]
  refine le_trans (Nat.mod_le _ _) ?_
  -- writeBytes preserves gas, so the first summand is pd.frame.exec.gasAvailable.toNat
  exact Nat.le_refl _

/-- `resumeAfterCreate` (when it returns a frame) gives parent gas
`.toNat ≤ savedParent + childRemaining`. -/
theorem resumeAfterCreate_gas_le {result : CreateResult} {pd : PendingCreate} {parent : Frame}
    (h : resumeAfterCreate result pd = .ok parent) :
    parent.exec.gasAvailable.toNat
      ≤ pd.frame.exec.gasAvailable.toNat + result.gasRemaining.toNat := by
  unfold resumeAfterCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [gasNat_replaceStackAndIncrPC]
    rw [UInt64.toNat_ofNat']
    refine le_trans (Nat.mod_le _ _) ?_
    -- gas.toNat - allButOneSixtyFourth gas.toNat + gasRemaining.toNat ≤ gas.toNat + gasRemaining.toNat
    have : pd.frame.exec.gasAvailable.toNat - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat
        ≤ pd.frame.exec.gasAvailable.toNat := Nat.sub_le _ _
    omega

/-- The **tight** `resumeAfterCreate` bound, matching the kind-aware
`Pending.savedGas`: the resumed parent's gas is `≤ (saved − allButOneSixtyFourth
saved) + childRemaining`. The forwarded `allButOneSixtyFourth` returns to the
parent on delivery, which is exactly what `savedGas (.create _)` already withheld
from the measure. -/
theorem resumeAfterCreate_gas_le_savedGas {result : CreateResult} {pd : PendingCreate} {parent : Frame}
    (h : resumeAfterCreate result pd = .ok parent) :
    parent.exec.gasAvailable.toNat
      ≤ (pd.frame.exec.gasAvailable.toNat
          - allButOneSixtyFourth pd.frame.exec.gasAvailable.toNat)
        + result.gasRemaining.toNat := by
  unfold resumeAfterCreate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [gasNat_replaceStackAndIncrPC]
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_le _ _

/-! ## Halt-op shape helper -/

/-- `haltOp` never produces `.next`: its `.ok` outputs are all `.halted`. -/
theorem haltOp_not_next {op : Operation.SystemOp} {exec exec' : ExecutionState}
    (hh : op = .STOP ∨ op = .RETURN ∨ op = .REVERT ∨ op = .SELFDESTRUCT ∨ op = .INVALID) :
    haltOp op exec ≠ .ok (.next exec') := by
  intro he
  unfold haltOp at he
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · simp at he
  · rw [returnOrRevertOp] at he
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at he
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at he; simp at he
      | ok ec =>
        rw [hm] at he; simp only [pure, Except.pure] at he
        split at he <;> simp at he
  · rw [returnOrRevertOp] at he
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    | some v =>
      obtain ⟨s, off, size⟩ := v; rw [hp] at he
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
      cases hm : chargeMemExpansion exec off size with
      | error e => rw [hm] at he; simp at he
      | ok ec =>
        rw [hm] at he; simp only [pure, Except.pure] at he
        split at he <;> simp at he
  · rw [selfdestructOp] at he
    cases hr : requireStateMod exec with
    | error e => rw [hr] at he; simp [bind, Except.bind] at he
    | ok _ =>
      rw [hr] at he; simp only [bind, Except.bind, pure, Except.pure] at he
      cases hp : exec.stack.pop with
      | none => rw [hp] at he; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at he
      | some v =>
        obtain ⟨s, rw'⟩ := v; rw [hp] at he
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at he
        cases hc : charge (selfdestructCost _ _) exec with
        | error e => rw [hc] at he; simp at he
        | ok ec =>
          rw [hc] at he; simp only [] at he
          split at he <;> simp at he
  · simp [throw, throwThe, MonadExceptOf.throw] at he

/-- The gas of the frame `beginCall` produces for a code call is `params.gas`. -/
theorem beginCall_inl_gas {p : CallParams} {fr : Frame} (h : beginCall p = .inl fr) :
    fr.exec.gasAvailable = p.gas := by
  unfold beginCall at h
  cases hcs : p.codeSource with
  | Precompiled pc => rw [hcs] at h; simp at h
  | Code code => rw [hcs] at h; simp only [Sum.inl.injEq] at h; subst h; rfl

/-! ## General measure bound (induction skeleton)

The full `mu_bound` over arbitrary pending stacks. Obligations 1 (non-`System`
`.next`), 2 (`.halted`), 6 (`resume = .ok`), and 7 (`resume = .error`) are
discharged inline below. The CALL/CREATE *descent* obligations (3 — `System`
`.next` fallbacks; 4/5 — `.needsCall`/`.needsCreate` into a child) are taken as
hypotheses `DescentDrops` here; closing them (the 63/64 / stipend / `extraCost`
arithmetic, mined from M2) removes the hypothesis and yields the unconditional
general theorem. -/

/-- Each CALL/CREATE descent and each `System` `.next` fallback strictly drops
the measure by enough: `μ` of the recursive `drive` target is `< μ` of the
current state. This is the single remaining (gas-arithmetic) obligation. -/
def DescentDrops : Prop :=
  -- (3) System `.next` fallback: totalGas drops ≥ 1
  (∀ (fr : Frame) (exec' : ExecutionState) (stack : List Pending),
      stepFrame fr = .next exec' →
      (∃ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s) →
      totalGas stack (.inl { fr with exec := exec' }) < totalGas stack (.inl fr))
  ∧ -- (4) needsCall descent into a child
  (∀ (fr : Frame) (params : CallParams) (pending : PendingCall) (child : Frame) (stack : List Pending),
      stepFrame fr = .needsCall params pending → beginCall params = .inl child →
      activeGas (.inl child) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (5a) needsCall precompile (immediate result)
  (∀ (fr : Frame) (params : CallParams) (pending : PendingCall) (result : CallResult) (stack : List Pending),
      stepFrame fr = .needsCall params pending → beginCall params = .inr result →
      FrameResult.gasRemaining (.call result) + Pending.savedGas (.call pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (4') needsCreate descent into a child
  (∀ (fr : Frame) (params : CreateParams) (pending : PendingCreate) (child : Frame) (stack : List Pending),
      stepFrame fr = .needsCreate params pending → beginCreate params = .ok child →
      activeGas (.inl child) + Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr))
  ∧ -- (5b) needsCreate failure (zeroed result)
  (∀ (fr : Frame) (params : CreateParams) (pending : PendingCreate) (stack : List Pending),
      stepFrame fr = .needsCreate params pending →
      Pending.savedGas (.create pending) + 2 ≤ activeGas (.inl fr))

/-- **The general measure bound.** `μ stack state ≤ f → drive f stack state ≠
OutOfFuel`. By induction on `f`, with the per-transition decrease for every
`drive` branch; descent/fallback decreases come from `DescentDrops`. -/
theorem mu_bound (hd : DescentDrops) :
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

/-- **General `messageCall` never out-of-fuel**, modulo `DescentDrops`. The
measure starts at `μ [] (.inl frame) = 2 * p.gas.toNat + 2 ≤ seedFuel p.gas`. -/
theorem messageCall_never_outOfFuel_of_descentDrops (hd : DescentDrops) (p : CallParams) :
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

end BytecodeLayer
