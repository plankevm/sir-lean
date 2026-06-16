import Evm
import BytecodeLayer.Reasoning.StepGasBasics

/-!
# Every non-halting opcode strictly decreases available gas

`stepFrame fr = .next exec' → exec'.gasAvailable.toNat < fr.exec.gasAvailable.toNat`
for every decoded opcode that is **not** a `System` op (the `CALL`/`CREATE`
family). The proof is a bind-chokepoint argument: every `.next` such an opcode
emits is the output of a final `charge cost` with `cost ≥ 1` (intermediate
`chargeMemExpansion` steps never raise gas, and the post-charge continuations
only reshuffle stack/pc/state). See `dispatch_next_lt` / `stepFrame_next_lt`.

The `System` family is excluded on purpose: its `.next` *fallback* paths
(insufficient funds, depth limit, nonce overflow) set gas via
`resumeAfterCall` / `resumeAfterCreate`, not a final `charge`.
-/

namespace BytecodeLayer
open Evm
open Evm.Operation
open GasConstants

/-- Reducing a successful lifted-`Option` (`pop`) bind: keeps the inner `>>=`. -/
theorem lift_some_bind {α : Type} (v : α) (k : α → Step) :
    (((some v : Option α) : Except ExecutionException α) >>= k) = k v := rfl

theorem lift_none_bind {α : Type} (k : α → Step) :
    (((none : Option α) : Except ExecutionException α) >>= k) = .error .StackUnderflow := rfl

/-- A `Step` value `s` is *gas-bounded by* `g` when every `.next exec'` it carries
satisfies `exec'.gasAvailable.toNat ≤ g`. This is the property the dispatcher's
post-charge continuations enjoy (they only reshuffle the stack/pc/state, never
raise gas above the charged level). -/
def gasBoundedBy (g : ℕ) (s : Step) : Prop :=
  ∀ exec', s = .ok (.next exec') → exec'.gasAvailable.toNat ≤ g

theorem gasBoundedBy_continueWith {g : ℕ} {exec : ExecutionState}
    (h : exec.gasAvailable.toNat ≤ g) : gasBoundedBy g (continueWith exec) := by
  intro e he
  simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he
  subst he; exact h

/-- A lifted-`Option` bind (a `pop`) is gas-bounded by `g` if every successful
continuation is. The `none` case lifts to `.error`, which is not a `.next`. -/
theorem gasBoundedBy_optionBind {g : ℕ} {α : Type} (o : Option α) (k : α → Step)
    (hk : ∀ a, o = some a → gasBoundedBy g (k a)) :
    gasBoundedBy g ((o : Except ExecutionException α) >>= k) := by
  intro e he
  cases ho : o with
  | none =>
    rw [ho] at he
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at he
    exact absurd he (by simp)
  | some a =>
    rw [ho] at he
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option, bind, Except.bind] at he
    exact hk a ho e he

/-- `chargeMemExpansion` never raises gas. -/
theorem chargeMem_gasAvailable_le {exec ec : ExecutionState} {off size : UInt256}
    (h : chargeMemExpansion exec off size = .ok ec) :
    ec.gasAvailable.toNat ≤ exec.gasAvailable.toNat := by
  unfold chargeMemExpansion at h
  split at h
  · simp at h
  · exact charge_le h

/-- The bind chokepoint. If `charge cost exec` succeeds, `cost ≥ 1`, and the
continuation `k` is gas-bounded by the charged exec's gas whenever it fires, then
`charge cost exec >>= k` produces a `.next` with strictly less gas than `exec`. -/
theorem chargeBind_lt {cost : ℕ} {exec exec' : ExecutionState} {k : ExecutionState → Step}
    (hc : 1 ≤ cost)
    (hk : ∀ ec, charge cost exec = .ok ec → gasBoundedBy ec.gasAvailable.toNat (k ec))
    (h : (charge cost exec >>= k) = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  cases hch : charge cost exec with
  | error e => rw [hch] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hch] at h
    simp only [bind, Except.bind] at h
    have hlt : ec.gasAvailable.toNat < exec.gasAvailable.toNat := charge_lt hc hch
    have hle : exec'.gasAvailable.toNat ≤ ec.gasAvailable.toNat := hk ec hch exec' h
    omega

/-! ## Per-helper `.next` strict-decrease lemmas (PrimOps) -/

theorem unOp_lt {f : UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (hc : 1 ≤ cost) (h : unOp f exec cost = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [unOp] at h
  apply chargeBind_lt hc (k := _) (h := h)
  intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, a⟩ _
  exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

theorem binOp_lt' {f : UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (hc : 1 ≤ cost) (h : binOp f exec cost = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [binOp] at h
  apply chargeBind_lt hc (k := _) (h := h)
  intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, a, b⟩ _
  exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

theorem ternOp_lt {f : UInt256 → UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (hc : 1 ≤ cost) (h : ternOp f exec cost = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [ternOp] at h
  apply chargeBind_lt hc (k := _) (h := h)
  intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, a, b, c⟩ _
  exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

theorem pushOp_lt {v : ExecutionState → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (hc : 1 ≤ cost) (h : pushOp v exec cost = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [pushOp] at h
  apply chargeBind_lt hc (k := _) (h := h)
  intro ec _
  exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

/-- `unStateOp` pops first, then charges `cost exec a`; strict decrease needs a
`≥ 1` lower bound on that cost for every popped operand. -/
theorem unStateOp_lt {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec exec' : ExecutionState}
    (hc : ∀ e a, 1 ≤ cost e a) (h : unStateOp f cost exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [unStateOp] at h
  -- shape: exec.stack.pop >>= fun (s,a) => charge (cost exec a) exec >>= fun ec => continueWith ...
  cases hp : exec.stack.pop with
  | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨s, a⟩ := v
    rw [hp] at h
    simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    apply chargeBind_lt (hc exec a) (k := _) (h := h)
    intro ec _
    exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

theorem dup_lt {n : ℕ} {exec exec' : ExecutionState}
    (h : dup n exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [dup] at h
  apply chargeBind_lt (by decide : 1 ≤ Gverylow) (k := _) (h := h)
  intro ec _ e he
  -- continuation: match ec.stack[n-1]? with some v => continueWith ... | none => throw
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v =>
    rw [hg] at he
    simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he
    subst he; exact le_of_eq (gasNat_replaceStackAndIncrPC ..)

theorem swap_lt {n : ℕ} {exec exec' : ExecutionState}
    (h : swap n exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [swap] at h
  apply chargeBind_lt (by decide : 1 ≤ Gverylow) (k := _) (h := h)
  intro ec _ e he
  by_cases hl : (ec.stack.take (n + 1)).length = (n + 1)
  · simp only [hl, if_true] at he
    simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he
    subst he; exact le_of_eq (gasNat_replaceStackAndIncrPC ..)
  · simp only [hl, if_false] at he
    simp [throw, throwThe, MonadExceptOf.throw] at he

/-- `chargeMemExpansion` (only decreases gas) followed by a `charge (cost ec)` with
`cost ec ≥ 1` and a gas-preserving continuation: strict decrease. The second
charge's cost may depend on the memory-expansion result. -/
theorem memChargeBind_lt {cost : ExecutionState → ℕ} {exec exec' : ExecutionState}
    {off size : UInt256} {k : ExecutionState → Step}
    (hc : ∀ ec, 1 ≤ cost ec)
    (hk : ∀ ec ec2, chargeMemExpansion exec off size = .ok ec → charge (cost ec) ec = .ok ec2 →
          gasBoundedBy ec2.gasAvailable.toNat (k ec2))
    (h : (chargeMemExpansion exec off size >>= fun ec => charge (cost ec) ec >>= k) = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  cases hm : chargeMemExpansion exec off size with
  | error e => rw [hm] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hm] at h; simp only [bind, Except.bind] at h
    have hmle : ec.gasAvailable.toNat ≤ exec.gasAvailable.toNat := chargeMem_gasAvailable_le hm
    have := chargeBind_lt (hc ec) (k := k) (exec := ec) (exec' := exec')
      (fun ec2 hch => hk ec ec2 hm hch) (by simpa [bind, Except.bind] using h)
    omega

theorem sstoreCost_pos (o c n : UInt256) (w : Bool) : 1 ≤ sstoreCost o c n w := by
  have hstore : 1 ≤
      (if c = n || o ≠ c then Gwarmaccess
       else if c ≠ n && o = c && o = 0 then Gsset else Gsreset) := by
    unfold Gwarmaccess Gsset Gsreset
    split <;> [skip; split] <;> omega
  unfold sstoreCost
  exact le_trans hstore (Nat.le_add_left _ _)

theorem logCost_pos (tc : ℕ) (size : UInt256) : 1 ≤ logCost tc size := by
  unfold logCost Glog; omega

theorem expCost_pos (e : UInt256) : 1 ≤ expCost e := by
  unfold expCost Gexp; split <;> omega

theorem keccakCost_pos (s : UInt256) : 1 ≤ keccakCost s := by
  unfold keccakCost Gkeccak256; omega

theorem accessCost_pos (a : AccountAddress) (sub : Substate) : 1 ≤ accessCost a sub := by
  unfold accessCost Gwarmaccess Gcoldaccountaccess; split <;> omega

theorem sloadCost_pos (w : Bool) : 1 ≤ sloadCost w := by
  unfold sloadCost Gwarmaccess Gcoldsload; split <;> omega

/-- `logArm`: requireStateMod, then chargeMemExpansion (≤), then `charge (logCost ..)`
(≥ 375), then a gas-preserving `logOp`+continueWith. -/
theorem logArm_lt {exec exec' : ExecutionState} {stack : Stack UInt256}
    {offset size : UInt256} {topics : Array UInt256}
    (h : logArm exec stack offset size topics = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  rw [logArm] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp [bind, Except.bind] at h
  | ok _ =>
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    apply memChargeBind_lt (fun _ => logCost_pos _ _) (k := _) (h := h)
    intro ec ec2 _ _
    exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

/-! ## smsf arms -/

theorem smsfOp_next_lt {op : SmsfOp} {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp op fr exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  unfold smsfOp at h
  cases op with
  | POP =>
    simp only at h
    apply chargeBind_lt (by decide : 1 ≤ Gbase) (k := _) (h := h)
    intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, a⟩ _
    exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | MLOAD =>
    simp only at h
    cases hp : exec.stack.pop with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, a⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      apply memChargeBind_lt (fun _ => (by decide : 1 ≤ Gverylow)) (k := _) (h := h)
      intro ec ec2 _ _
      exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | MSTORE =>
    simp only at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, a, b⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      apply memChargeBind_lt (fun _ => (by decide : 1 ≤ Gverylow)) (k := _) (h := h)
      intro ec ec2 _ _
      exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | MSTORE8 =>
    simp only at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, a, b⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      apply memChargeBind_lt (fun _ => (by decide : 1 ≤ Gverylow)) (k := _) (h := h)
      intro ec ec2 _ _
      exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | SLOAD => exact unStateOp_lt (fun e a => by unfold sloadCost; split <;> decide) h
  | SSTORE =>
    simp only at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · cases hp : exec.stack.pop2 with
        | none =>
          rw [hp] at h
          simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
          exact absurd h (by simp)
        | some v =>
          obtain ⟨s, a, b⟩ := v; rw [hp] at h
          simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
          apply chargeBind_lt (sstoreCost_pos _ _ _ _) (k := _) (h := h)
          intro ec _
          exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | TLOAD => exact unStateOp_lt (fun e a => by unfold tloadCost Gwarmaccess; decide) h
  | TSTORE =>
    simp only at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp [bind, Except.bind] at h
    | ok _ =>
      rw [hr] at h; simp only [bind, Except.bind] at h
      apply chargeBind_lt (by unfold tstoreCost Gwarmaccess; decide : 1 ≤ tstoreCost) (k := _) (h := h)
      intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, a, b⟩ _
      exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | MSIZE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
  | GAS => exact pushOp_lt (by decide : 1 ≤ Gbase) h
  | JUMP =>
    simp only at h
    apply chargeBind_lt (by decide : 1 ≤ Gmid) (k := _) (h := h)
    intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, d⟩ _ e he
    split at he <;>
      first
        | (simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he; subst he; rfl)
        | simp at he
  | JUMPI =>
    simp only at h
    apply chargeBind_lt (by decide : 1 ≤ Ghigh) (k := _) (h := h)
    intro ec _; apply gasBoundedBy_optionBind; rintro ⟨s, d, c⟩ _ e he
    split at he
    · split at he <;>
        first
          | (simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he; subst he; rfl)
          | simp at he
    · simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he
      subst he; rfl
  | PC => exact pushOp_lt (by decide : 1 ≤ Gbase) h
  | JUMPDEST =>
    simp only at h
    apply chargeBind_lt (by decide : 1 ≤ Gjumpdest) (k := _) (h := h)
    intro ec _ e he
    simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he
    subst he; rfl
  | MCOPY =>
    simp only at h
    cases hp : exec.stack.pop3 with
    | none => rw [hp] at h; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, a, b, c⟩ := v; rw [hp] at h
      simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at h
      apply memChargeBind_lt (cost := fun _ => Gverylow + copyCost c) (k := _) (h := h)
      · intro _; show 1 ≤ Gverylow + copyCost _; unfold Gverylow; omega
      · intro ec ec2 _ _
        exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))

/-! ## Top-level dispatcher lemma (non-`System` ops)

Every non-`System` opcode reaches `.next` only through a `charge cost` with
`cost ≥ 1`, so it strictly decreases gas. `System` (CALL/CREATE families) is
treated separately: its `.next` fallback paths set gas through
`resumeAfterCall`/`resumeAfterCreate`, not a final `charge`. -/

/-- Inline arm of shape `pop* >>= charge c >>= continueWith (…replaceStackAndIncrPC…)`. -/
macro "pop_charge_lt" hyp:ident pop:term " with " pat:rcasesPat " using " bound:term : tactic =>
  `(tactic|
    (cases hp : $pop with
     | none => rw [hp, lift_none_bind] at $hyp:ident; exact absurd $hyp (by simp)
     | some v =>
       obtain $pat := v; rw [hp, lift_some_bind] at $hyp:ident
       refine chargeBind_lt $bound (k := _) (h := $hyp) ?_
       intro ec _
       exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))))

/-- Inline arm of shape `pop* >>= chargeMem >>= charge c >>= continueWith (…replaceStackAndIncrPC…)`. -/
macro "pop_memcharge_lt" hyp:ident pop:term " with " pat:rcasesPat " using " bound:term : tactic =>
  `(tactic|
    (cases hp : $pop with
     | none => rw [hp, lift_none_bind] at $hyp:ident; exact absurd $hyp (by simp)
     | some v =>
       obtain $pat := v; rw [hp, lift_some_bind] at $hyp:ident
       refine memChargeBind_lt (fun _ => $bound) (k := _) (h := $hyp) ?_
       intro ec ec2 _ _
       exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))))

/-- A `LOG` arm: `pop* >>= logArm …`, and `logArm` is already proven. -/
macro "pop_log" hyp:ident pop:term " with " pat:rcasesPat : tactic =>
  `(tactic|
    (cases hp : $pop with
     | none => rw [hp, lift_none_bind] at $hyp:ident; exact absurd $hyp (by simp)
     | some v =>
       obtain $pat := v; rw [hp, lift_some_bind] at $hyp:ident
       exact logArm_lt $hyp))

set_option maxHeartbeats 1000000 in
/-- **Strict gas-decrease at the `dispatch` level for all non-`System` opcodes.**
If a non-`System` opcode produces `.next exec'`, then `exec'` has strictly less
available gas than the input `exec`. Proved by a per-opcode-class case split
(10 top-level constructors; the arithmetic/env/block/push/dup/swap/keccak/log
classes each reduce to one of the proven helper/inline chokepoints). -/
theorem dispatch_next_lt {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec exec' : ExecutionState}
    (hne : ∀ s, op ≠ .System s)
    (h : dispatch op arg fr exec = .ok (.next exec')) :
    exec'.gasAvailable.toNat < exec.gasAvailable.toNat := by
  unfold dispatch at h
  cases op with
  | System s => exact absurd rfl (hne s)
  | KECCAK256 =>
    simp only at h
    pop_memcharge_lt h exec.stack.pop2 with ⟨s, a, b⟩ using (keccakCost_pos _)
  | Smsf s => exact smsfOp_next_lt h
  | Log l =>
    cases l with
    | LOG0 => simp only at h; pop_log h exec.stack.pop2 with ⟨s, a, b⟩
    | LOG1 => simp only at h; pop_log h exec.stack.pop3 with ⟨s, a, b, t1⟩
    | LOG2 => simp only at h; pop_log h exec.stack.pop4 with ⟨s, a, b, t1, t2⟩
    | LOG3 => simp only at h; pop_log h exec.stack.pop5 with ⟨s, a, b, t1, t2, t3⟩
    | LOG4 => simp only at h; pop_log h exec.stack.pop6 with ⟨s, a, b, t1, t2, t3, t4⟩
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | _ =>
      simp only at h
      refine chargeBind_lt (by decide : 1 ≤ Gverylow) (k := _) (h := h) ?_
      intro ec _ e he
      cases harg : arg with
      | none => rw [harg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
      | some w =>
        obtain ⟨av, aw⟩ := w; rw [harg] at he
        simp only [continueWith, Except.ok.injEq, Signal.next.injEq] at he
        subst he; exact le_of_eq (gasNat_replaceStackAndIncrPC ..)
  | Dup d => exact dup_lt h
  | Swap s => exact swap_lt h
  | ArithLogic a =>
    cases a with
    | ADD => exact binOp_lt' (by decide) h
    | MUL => exact binOp_lt' (by decide) h
    | SUB => exact binOp_lt' (by decide) h
    | DIV => exact binOp_lt' (by decide) h
    | SDIV => exact binOp_lt' (by decide) h
    | MOD => exact binOp_lt' (by decide) h
    | SMOD => exact binOp_lt' (by decide) h
    | ADDMOD => exact ternOp_lt (by decide) h
    | MULMOD => exact ternOp_lt (by decide) h
    | EXP =>
      simp only at h
      pop_charge_lt h exec.stack.pop2 with ⟨s, a, b⟩ using (expCost_pos _)
    | SIGNEXTEND => exact binOp_lt' (by decide) h
    | LT => exact binOp_lt' (by decide) h
    | GT => exact binOp_lt' (by decide) h
    | SLT => exact binOp_lt' (by decide) h
    | SGT => exact binOp_lt' (by decide) h
    | EQ => exact binOp_lt' (by decide) h
    | ISZERO => exact unOp_lt (by decide) h
    | AND => exact binOp_lt' (by decide) h
    | OR => exact binOp_lt' (by decide) h
    | XOR => exact binOp_lt' (by decide) h
    | NOT => exact unOp_lt (by decide) h
    | BYTE => exact binOp_lt' (by decide) h
    | SHL => exact binOp_lt' (by decide) h
    | SHR => exact binOp_lt' (by decide) h
    | SAR => exact binOp_lt' (by decide) h
  | Env e =>
    cases e with
    | ADDRESS => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | BALANCE => exact unStateOp_lt (fun _ a => accessCost_pos _ _) h
    | ORIGIN => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | CALLER => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | CALLVALUE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | CALLDATALOAD => exact unStateOp_lt (fun _ _ => by unfold Gverylow; omega) h
    | CALLDATASIZE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | CODESIZE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | GASPRICE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | EXTCODESIZE => exact unStateOp_lt (fun _ a => accessCost_pos _ _) h
    | EXTCODEHASH => exact unStateOp_lt (fun _ a => accessCost_pos _ _) h
    | RETURNDATASIZE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | CALLDATACOPY =>
      simp only at h
      pop_memcharge_lt h exec.stack.pop3 with ⟨s, a, b, c⟩ using (by unfold Gverylow; omega)
    | CODECOPY =>
      simp only at h
      pop_memcharge_lt h exec.stack.pop3 with ⟨s, a, b, c⟩ using (by unfold Gverylow; omega)
    | EXTCODECOPY =>
      simp only at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp, lift_none_bind] at h; exact absurd h (by simp)
      | some v =>
        obtain ⟨s, a, b, c, d⟩ := v; rw [hp, lift_some_bind] at h; dsimp only at h
        apply memChargeBind_lt (cost := fun ec => accessCost (AccountAddress.ofUInt256 a) ec.substate + copyCost d) (k := _) (h := h)
        · intro ec; show 1 ≤ accessCost (AccountAddress.ofUInt256 a) ec.substate + copyCost d
          have := accessCost_pos (AccountAddress.ofUInt256 a) ec.substate; omega
        · intro ec ec2 _ _
          exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
    | RETURNDATACOPY =>
      simp only at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp, lift_none_bind] at h; exact absurd h (by simp)
      | some v =>
        obtain ⟨s, a, b, c⟩ := v; rw [hp, lift_some_bind] at h
        split at h
        · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
        · apply memChargeBind_lt (cost := fun _ => Gverylow + copyCost c) (k := _) (h := h)
          · intro _; show 1 ≤ Gverylow + copyCost _; unfold Gverylow; omega
          · intro ec ec2 _ _
            exact gasBoundedBy_continueWith (le_of_eq (gasNat_replaceStackAndIncrPC ..))
  | Block b =>
    cases b with
    | BLOCKHASH => exact unStateOp_lt (fun _ _ => by unfold Gblockhash; omega) h
    | COINBASE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | TIMESTAMP => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | NUMBER => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | PREVRANDAO => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | GASLIMIT => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | CHAINID => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | SELFBALANCE => exact pushOp_lt (by decide : 1 ≤ Glow) h
    | BASEFEE => exact pushOp_lt (by decide : 1 ≤ Gbase) h
    | BLOBHASH =>
      simp only at h
      pop_charge_lt h exec.stack.pop with ⟨s, i⟩ using (by unfold HASH_OPCODE_GAS; omega)
    | BLOBBASEFEE => exact pushOp_lt (by decide : 1 ≤ Gbase) h

/-! ## Top-level `stepFrame` strict gas-decrease (non-`System` opcodes)

`stepFrame` decodes the opcode, screens `INVALID`/stack-overflow (which `.halted`),
then forwards to `dispatch`; the result is `.next` only when `dispatch` returns
`.ok (.next …)`. So for any decoded opcode that is not a `System` op, a `.next`
step strictly decreases gas. -/
theorem stepFrame_next_lt {fr : Frame} {exec' : ExecutionState}
    (hne : ∀ s, (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none)).1 ≠ .System s)
    (h : stepFrame fr = .next exec') :
    exec'.gasAvailable.toNat < fr.exec.gasAvailable.toNat := by
  rw [stepFrame] at h
  -- name the decoded (op, arg) pair as a unit so it appears atomically.
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h hne
  obtain ⟨op, arg⟩ := dp
  simp only at h hne
  split at h
  · exact absurd h (by simp)  -- INVALID ⇒ .halted
  · split at h
    · exact absurd h (by simp) -- stack overflow ⇒ .halted
    · -- dispatch branch
      cases hdisp : dispatch op arg fr fr.exec with
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e =>
          simp only [Signal.next.injEq] at h; subst h
          exact dispatch_next_lt hne hdisp
        | halted hl => simp only at h; exact absurd h (by simp)
        | needsCall p pc => simp only at h; exact absurd h (by simp)
        | needsCreate p pc => simp only at h; exact absurd h (by simp)
      | error e => rw [hdisp] at h; exact absurd h (by simp)

end BytecodeLayer
