import BytecodeLayer.Reasoning.StepGas

/-!
# Proof — dispatch/`stepFrame` signal-shape bridges (`DispatchSignalShape`)

The `onlyNext` machinery (mirroring `neverHalts`) and the
`stepFrame`→`systemOp` bridges. This cluster is independent of the descent gas
tower — it depends only on the leanevm dispatcher and `StepGas` foundations.

Extracted from `Proof/DescentDrops.lean`; the three public `stepFrame_*_systemOp`
bridges feed the `descentDrops_conj*` proofs there (which import this file).
-/

namespace BytecodeLayer.Proof
open Evm
open Evm.Operation
open GasConstants

/-! ## `stepFrame` inversion: bridging the `Signal` to `systemOp`

`stepFrame fr` decodes `(op, arg)`, screens `INVALID`/overflow (both `.halted`),
then maps `dispatch op arg fr fr.exec`. A `.needsCall`/`.needsCreate`/(System)
`.next` signal therefore comes from `dispatch op arg fr fr.exec = .ok (that
signal)` with `op = .System s`, and `dispatch (.System s) … = systemOp s …`.

The non-`System` dispatcher arms only ever emit `.next` (`continueWith`) on
success, so they cannot emit `.needsCall`/`.needsCreate`. We capture that with
`onlyNext`, mirroring `neverHalts`. -/

/-- A `Step` whose every `.ok` output is a `.next`. -/
def onlyNext (s : Step) : Prop := ∀ sig, s = .ok sig → ∃ e, sig = .next e

theorem onlyNext_continueWith (e : ExecutionState) : onlyNext (continueWith e) := by
  intro sig he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨e, he.symm⟩
theorem onlyNext_error (e : ExecutionException) : onlyNext (.error e : Step) := by
  intro sig he; simp at he
theorem onlyNext_throw (e : ExecutionException) : onlyNext (throw e : Step) := by
  intro sig he; simp [throw, throwThe, MonadExceptOf.throw] at he
theorem onlyNext_bind_except {α : Type} (m : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, m = .ok a → onlyNext (k a)) : onlyNext (m >>= k) := by
  intro sig he
  cases hm : m with
  | error e => rw [hm] at he; simp [bind, Except.bind] at he
  | ok a => rw [hm] at he; simp only [bind, Except.bind] at he; exact hk a hm sig he
theorem onlyNext_optionBind {α : Type} (o : Option α) (k : α → Step)
    (hk : ∀ a, o = some a → onlyNext (k a)) :
    onlyNext ((o : Except ExecutionException α) >>= k) := by
  intro sig he
  cases ho : o with
  | none => rw [ho] at he; simp [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
  | some a =>
    rw [ho] at he; simp only [bind, Except.bind, MonadLift.monadLift, liftM, monadLift, Option.option] at he
    exact hk a ho sig he
theorem onlyNext_chargeBind {cost : ℕ} {exec : ExecutionState} {k : ExecutionState → Step}
    (hk : ∀ ec, charge cost exec = .ok ec → onlyNext (k ec)) :
    onlyNext (charge cost exec >>= k) :=
  onlyNext_bind_except _ _ hk
theorem onlyNext_memChargeBind {exec : ExecutionState} {off size : UInt256}
    {k : ExecutionState → Step} (hk : ∀ ec, onlyNext (k ec)) :
    onlyNext (chargeMemExpansion exec off size >>= k) := by
  apply onlyNext_bind_except; intro a _; exact hk a

theorem unOp_onlyNext {f : UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (unOp f exec cost) := by
  rw [unOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a⟩ _; exact onlyNext_continueWith _
theorem binOp_onlyNext {f : UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (binOp f exec cost) := by
  rw [binOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _; exact onlyNext_continueWith _
theorem ternOp_onlyNext {f : UInt256 → UInt256 → UInt256 → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (ternOp f exec cost) := by
  rw [ternOp]; apply onlyNext_chargeBind; intro ec _
  apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _; exact onlyNext_continueWith _
theorem pushOp_onlyNext {v : ExecutionState → UInt256} {exec : ExecutionState} {cost : ℕ} :
    onlyNext (pushOp v exec cost) := by
  rw [pushOp]; apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
theorem unStateOp_onlyNext {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec : ExecutionState} :
    onlyNext (unStateOp f cost exec) := by
  rw [unStateOp]; apply onlyNext_optionBind; rintro ⟨s, a⟩ _
  apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
theorem dup_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (dup n exec) := by
  rw [dup]; apply onlyNext_chargeBind; intro ec _
  intro sig he
  cases hg : ec.stack[n-1]? with
  | none => rw [hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
  | some v => rw [hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
theorem swap_onlyNext {n : ℕ} {exec : ExecutionState} : onlyNext (swap n exec) := by
  rw [swap]; apply onlyNext_chargeBind; intro ec _
  intro sig he
  by_cases hg : List.length (ec.stack.take (n + 1)) = (n + 1)
  · rw [if_pos hg] at he; simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
  · rw [if_neg hg] at he; simp [throw, throwThe, MonadExceptOf.throw] at he
theorem logArm_onlyNext {exec : ExecutionState} {stack : Stack UInt256}
    {offset size : UInt256} {topics : Array UInt256} :
    onlyNext (logArm exec stack offset size topics) := by
  rw [logArm]; apply onlyNext_bind_except; intro _ _
  apply onlyNext_memChargeBind; intro ec
  apply onlyNext_chargeBind; intro ec2 _; exact onlyNext_continueWith _
theorem smsfOp_onlyNext {op : Operation.SmsfOp} {fr : Frame} {exec : ExecutionState} :
    onlyNext (smsfOp op fr exec) := by
  unfold smsfOp
  cases op with
  | POP =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, a⟩ _; exact onlyNext_continueWith _
  | MLOAD =>
    apply onlyNext_optionBind; rintro ⟨s, a⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | MSTORE =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | MSTORE8 =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | SLOAD => exact unStateOp_onlyNext
  | SSTORE =>
    apply onlyNext_bind_except; intro _ _
    by_cases hg : exec.gasAvailable.toNat ≤ Gcallstipend
    · simp only [hg, if_true]; exact onlyNext_throw _
    · simp only [hg, if_false]
      apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
      apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
  | TLOAD => exact unStateOp_onlyNext
  | TSTORE =>
    apply onlyNext_bind_except; intro _ _
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _; exact onlyNext_continueWith _
  | MSIZE => exact pushOp_onlyNext
  | GAS => exact pushOp_onlyNext
  | JUMP =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, d⟩ _ sig he
    dsimp only at he
    split at he
    · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
    · simp at he
  | JUMPI =>
    apply onlyNext_chargeBind; intro ec _
    apply onlyNext_optionBind; rintro ⟨s, d, c⟩ _ sig he
    dsimp only at he
    split at he
    · split at he
      · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
      · simp at he
    · simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩
  | PC => exact pushOp_onlyNext
  | JUMPDEST =>
    apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _
  | MCOPY =>
    apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _

/-- The non-`System` dispatcher arms only emit `.next`. -/
theorem dispatch_onlyNext {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec : ExecutionState} (hne : ∀ s, op ≠ .System s) :
    onlyNext (dispatch op arg fr exec) := by
  unfold dispatch
  cases op with
  | System s => exact absurd rfl (hne s)
  | KECCAK256 =>
    apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
    apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
    exact onlyNext_continueWith _
  | Smsf s => exact smsfOp_onlyNext
  | Log l => cases l <;>
      (apply onlyNext_optionBind; rintro _ _; exact logArm_onlyNext)
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_onlyNext
    | _ =>
      apply onlyNext_chargeBind; intro ec _ sig he
      cases arg <;>
        first
          | (simp only [continueWith, Except.ok.injEq] at he; exact ⟨_, he.symm⟩)
          | simp [throw, throwThe, MonadExceptOf.throw] at he
  | Dup d => exact dup_onlyNext
  | Swap s => exact swap_onlyNext
  | ArithLogic a => cases a <;>
      first
        | exact binOp_onlyNext | exact unOp_onlyNext | exact ternOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, a, b⟩ _
           apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _)
  | Env e =>
    cases e <;>
      first
        | exact pushOp_onlyNext | exact unStateOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _
           apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
           exact onlyNext_continueWith _)
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c, d⟩ _
           apply onlyNext_memChargeBind; intro ec; apply onlyNext_chargeBind; intro ec2 _
           exact onlyNext_continueWith _)
        | (apply onlyNext_optionBind; rintro ⟨s, a, b, c⟩ _ sig he
           revert he; dsimp only; split
           · intro he; simp [bind, Except.bind] at he
           · exact (onlyNext_memChargeBind (k := _)
               (fun ec => onlyNext_chargeBind (fun ec2 _ => onlyNext_continueWith _)) sig))
  | Block b =>
    cases b <;>
      first
        | exact pushOp_onlyNext | exact unStateOp_onlyNext
        | (apply onlyNext_optionBind; rintro ⟨s, i⟩ _
           apply onlyNext_chargeBind; intro ec _; exact onlyNext_continueWith _)

/-- Bridge: a non-`.next` `Signal` from a successful `dispatch` forces `op` to be
a `System` op. -/
theorem dispatch_ok_System_of_not_next {op : Operation} {arg : Option (UInt256 × UInt8)}
    {fr : Frame} {exec : ExecutionState} {sig : Signal}
    (hdisp : dispatch op arg fr exec = .ok sig) (hnn : ∀ e, sig ≠ .next e) :
    ∃ s, op = .System s := by
  by_cases hsys : ∃ s, op = .System s
  · exact hsys
  · push Not at hsys
    obtain ⟨e, he⟩ := dispatch_onlyNext hsys sig hdisp
    exact absurd he (hnn e)

/-- The shared `stepFrame`→`dispatch` skeleton. A non-`.halted` `Signal` from
`stepFrame fr` is exactly that `Signal` from `dispatch op arg fr fr.exec` on the
decoded `(op, arg)` — the INVALID/overflow screens and the error arm all produce
`.halted`, so they are excluded. The three public bridges are thin wrappers. -/
private theorem stepFrame_dispatch {fr : Frame} {sig : Signal}
    (h : stepFrame fr = sig) (hnh : ∀ hl, sig ≠ .halted hl) :
    dispatch (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
        (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).2
        fr fr.exec = .ok sig := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp at h ⊢
  obtain ⟨op, arg⟩ := dp
  simp only at h ⊢
  split at h
  · exact absurd h.symm (hnh _)
  · split at h
    · exact absurd h.symm (hnh _)
    · cases hdisp : dispatch op arg fr fr.exec with
      | error e => rw [hdisp] at h; exact absurd h.symm (hnh _)
      | ok signal =>
        rw [hdisp] at h
        have h' : signal = sig := h
        rw [h']

/-- A `.needsCall` from `stepFrame` is a `.needsCall` from `systemOp s fr fr.exec`. -/
theorem stepFrame_needsCall_systemOp {fr : Frame} {p : CallParams} {pd : PendingCall}
    (h : stepFrame fr = .needsCall p pd) :
    ∃ s, systemOp s fr fr.exec = .ok (.needsCall p pd) := by
  have hdisp := stepFrame_dispatch h (by simp)
  obtain ⟨s, hs⟩ := dispatch_ok_System_of_not_next hdisp (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact ⟨s, hdisp⟩

/-- A `.needsCreate` from `stepFrame` is a `.needsCreate` from `systemOp s fr fr.exec`. -/
theorem stepFrame_needsCreate_systemOp {fr : Frame} {cp : CreateParams} {pd : PendingCreate}
    (h : stepFrame fr = .needsCreate cp pd) :
    ∃ s, systemOp s fr fr.exec = .ok (.needsCreate cp pd) := by
  have hdisp := stepFrame_dispatch h (by simp)
  obtain ⟨s, hs⟩ := dispatch_ok_System_of_not_next hdisp (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact ⟨s, hdisp⟩

/-- A `System`-op `.next` from `stepFrame`: when the decoded op is a `System` op
and `stepFrame` is `.next exec'`, that `.next` comes from `systemOp s fr fr.exec`. -/
theorem stepFrame_next_systemOp {fr : Frame} {exec' : ExecutionState} {s : Operation.SystemOp}
    (hs : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 = .System s)
    (h : stepFrame fr = .next exec') :
    systemOp s fr fr.exec = .ok (.next exec') := by
  have hdisp := stepFrame_dispatch h (by simp)
  rw [hs] at hdisp; rw [dispatch] at hdisp; exact hdisp

end BytecodeLayer.Proof
