import BytecodeLayer.Exec.Invariants
import BytecodeLayer.Hoare.DriveMono
import BytecodeLayer.Hoare.CleanHalt

/-!
# Self-account presence along execution

One ordinary step preserves the current execution address's account. Returning CALL
and CREATE edges preserve it under explicit local assumptions, and the resulting
facts extend across an arbitrary `Runs` derivation.
-/

namespace BytecodeLayer.Exec.Invariants

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps

/-! ### Forward closure along `Runs`

`Runs` has ordinary-step, returning-CALL, and returning-CREATE edges. The local
preservation predicates below isolate the assumptions required for each edge before
`selfPresent_runs` composes them over the relation.
-/

/-- One non-halting opcode step keeps the self account present. -/
def StepPreservesSelf : Prop :=
  ∀ ⦃fr fr' : Frame⦄, StepsTo fr fr' → SelfPresent fr → SelfPresent fr'

/-- Every non-halting opcode step keeps the self account present. -/
theorem stepPreservesSelf : StepPreservesSelf := by
  intro fr fr' hstep hself
  exact Evm.stepFrame_next_self hstep.1 hself

/-- **Local per-call self-presence preservation.** One returning external CALL (`CallReturns`)
keeps the *caller's* self account present. Satisfiable, not vacuous: the resume keeps the self
address (`resumeAfterCall_address`) and the returned `result.accounts` retains the caller (the
checkpoint on revert/exception is the caller's own pre-call map; on success the shared world keeps
the caller present — the caller is not the callee). The structural address half is banked; the
`result.accounts`-presence half is the returning-world fact supplied per CALL edge. -/
def CallPreservesSelf : Prop :=
  ∀ ⦃callFr resumeFr : Frame⦄, CallReturns callFr resumeFr → SelfPresent callFr → SelfPresent resumeFr

/-- A returning CALL preserves the caller's self account when ordinary steps,
precompiles, CALL entry, successful halts, and the suspended caller frame preserve
the tracked account and address. -/
theorem callPreservesSelf_success
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → ∀ a, AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → ∀ a, AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → ∀ a, AccPresent a fr.exec.accounts →
        AccPresent a e.accounts)
    (hcall_self : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd →
        pd.frame.exec.executionEnv.address = fr.exec.executionEnv.address)
    {callFr resumeFr : Frame} (hcr : CallReturns callFr resumeFr)
    (hself : SelfPresent callFr) :
    SelfPresent resumeFr := by
  obtain ⟨cp, pending, child, childRes, hstep, _hcode, hchild, hresume⟩ := hcr
  -- The tracked address: the caller's self (= the resumed self, `resumeAfterCall_address`).
  set a : Evm.AccountAddress := pending.frame.exec.executionEnv.address with ha
  -- The caller's self is present in `callFr.exec.accounts` (`hself`), and `callFr`'s self equals `a`.
  have haddr : callFr.exec.executionEnv.address = a := by
    rw [ha]; exact (hcall_self callFr cp pending hstep).symm
  have hcaller : AccPresent a callFr.exec.accounts := by
    obtain ⟨acc, hf⟩ := hself
    exact ⟨acc, by rw [← haddr]; exact hf⟩
  -- Hence present in `cp.accounts` (CALL-site framing), and so the child run starts present at `a`.
  have hcp : AccPresent a cp.accounts := hcall_acc callFr cp pending hstep a hcaller
  -- Build `DrivePresent a [] (running child)` from `cp.accounts` presence.
  -- (The child enters as code: `hchild`'s run is on `child`, so `beginCall cp = .inl child`.)
  have hbc : Evm.beginCall cp = .inl child := _hcode
  have hchildPres : DrivePresent a [] (Sum.inl child) := by
    refine ⟨beginCall_inl_accounts_present a cp hbc hcp, ?_, trivial⟩
    obtain ⟨created, sub, hkind⟩ := beginCall_inl_checkpoint cp hbc
    unfold CheckpointPresent; rw [hkind]; exact hcp
  -- Presence at `a` is monotone across the child drive run.
  have hmono' := drive_accounts_find_mono a
    (fun fr exec' h => hmono fr exec' h a)
    (fun c imm h => hprec c imm h a)
    (fun fr c pd h => hcall_acc fr c pd h a)
    hcall_kind
    (fun fr e o h => hhalt fr e o h a)
    (seedFuel cp.gas) [] (Sum.inl child) childRes hchild hchildPres
  -- Close `SelfPresent resumeFr` via the landed resume-self bridge.
  rw [hresume]
  exact resumeAfterCall_self_of_accounts childRes.toCallResult pending hmono'

/-- Assemble the local account-preservation hypotheses into `CallPreservesSelf`. -/
theorem callPreservesSelf
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → ∀ a, AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → ∀ a, AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → ∀ a, AccPresent a fr.exec.accounts →
        AccPresent a e.accounts)
    (hcall_self : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd →
        pd.frame.exec.executionEnv.address = fr.exec.executionEnv.address) :
    CallPreservesSelf := by
  intro callFr resumeFr hcr hself
  exact callPreservesSelf_success hmono hprec hcall_acc hcall_kind hhalt hcall_self hcr hself

/-- Discharge the structural CALL hypotheses, leaving only preservation by immediate
precompile results. -/
theorem callPreservesSelf_modGuards
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    CallPreservesSelf :=
  callPreservesSelf
    (fun fr exec' h a hp => Evm.stepFrame_next_accMono h a hp)
    hprec
    (fun fr cp pd h a hp => (Evm.stepFrame_needsCall_inv h).1 ▸ hp)
    (fun fr cp pd h => (Evm.stepFrame_needsCall_inv h).2.1)
    (fun fr e o h a hp => Evm.stepFrame_halted_success_accMono h a hp)
    (fun fr cp pd h => congrArg ExecutionEnv.address (Evm.stepFrame_needsCall_inv h).2.2)

/-! ### The CREATE resume edge -/

/-- **Local per-create self-presence preservation.** One returning CREATE (`CreateReturns`) keeps the
*creator's* self account present. The create twin of `CallPreservesSelf`. -/
def CreatePreservesSelf : Prop :=
  ∀ ⦃createFr resumeFr : Frame⦄, CreateReturns createFr resumeFr → SelfPresent createFr →
    SelfPresent resumeFr

/-- A returning CREATE preserves the creator's self account under the same local
account-preservation hypotheses used for CALL. -/
theorem createPreservesSelf
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → ∀ a, AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → ∀ a, AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → ∀ a, AccPresent a fr.exec.accounts →
        AccPresent a e.accounts) :
    CreatePreservesSelf := by
  intro createFr resumeFr hcr hself
  obtain ⟨cp, pending, childRes, hstep, hchild, hresume⟩ := hcr
  -- the tracked address: the creator's self (= the resumed self, `resumeAfterCreate_execEnv`).
  set a : Evm.AccountAddress := createFr.exec.executionEnv.address with ha
  -- the creator's self is present in `createFr.exec.accounts` (`hself`, definitionally at `a`).
  have hcaller : AccPresent a createFr.exec.accounts := hself
  -- CREATE-site framing transports presence to `cp.accounts`.
  obtain ⟨hcr_acc, hcr_kind, _hcr_pdacc, hcr_env⟩ := Evm.stepFrame_needsCreate_inv hstep
  have hcp : AccPresent a cp.accounts := hcr_acc a hcaller
  -- the init child drive starts present at `a` (`beginCreate` total).
  have hchildPres : DrivePresent a [] (Sum.inl (Evm.beginCreate cp)) := by
    refine ⟨beginCreate_ok_accounts_present a cp rfl hcp, ?_, trivial⟩
    obtain ⟨addr, created, sub, hkind⟩ := beginCreate_ok_checkpoint cp rfl
    unfold CheckpointPresent; rw [hkind]; exact hcp
  -- Presence at `a` is monotone across the child drive run.
  have hmono' := drive_accounts_find_mono a
    (fun fr exec' h => hmono fr exec' h a)
    (fun c imm h => hprec c imm h a)
    (fun fr c pd h => hcall_acc fr c pd h a)
    hcall_kind
    (fun fr e o h => hhalt fr e o h a)
    (seedFuel cp.gas) [] (Sum.inl (Evm.beginCreate cp)) childRes hchild hchildPres
  -- the resume keeps presence (`.ok` rewrites `accounts := result.accounts`) and the self address.
  have hpres : AccPresent a resumeFr.exec.accounts :=
    resumeAfterCreate_exec_accounts_present a childRes pending resumeFr hresume hmono'
  -- close `SelfPresent resumeFr`: its self is the creator's `a` (`resumeAfterCreate_execEnv`).
  have haddr : resumeFr.exec.executionEnv.address = a := by
    rw [resumeAfterCreate_execEnv childRes pending resumeFr hresume, hcr_env]
  show ∃ acc, resumeFr.exec.accounts.find? resumeFr.exec.executionEnv.address = some acc
  rw [haddr]; exact hpres

/-- **`CreatePreservesSelf` with the four universally-true closers discharged engine-level** (create
twin of `callPreservesSelf_modGuards`): the whole chain reduces to the ONE surviving seam `hprec`
(a precompile CALL inside the init run preserves presence — the exact same fact CALL supplies). -/
theorem createPreservesSelf_modGuards
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    CreatePreservesSelf :=
  createPreservesSelf
    (fun fr exec' h a hp => Evm.stepFrame_next_accMono h a hp)
    hprec
    (fun fr cp pd h a hp => (Evm.stepFrame_needsCall_inv h).1 ▸ hp)
    (fun fr cp pd h => (Evm.stepFrame_needsCall_inv h).2.1)
    (fun fr e o h a hp => Evm.stepFrame_halted_success_accMono h a hp)

/-- **`SelfPresent` is forward-closed along a whole `Runs` segment.** From `SelfPresent fr` and
`Runs fr fr'`, `SelfPresent fr'` — given the three local one-edge preservation facts
(`StepPreservesSelf` for opcode steps, `CallPreservesSelf` for returning external CALLs, and
`CreatePreservesSelf` for returning CREATEs, *including the `Runs.call`/`Runs.create` resume nodes*).
Proved by induction on the `Runs` derivation (the template is `Runs.gasAvailable_le`): `refl` carries
`h` unchanged; `step`/`call`/`create` apply the corresponding local edge then recurse. This is the
threading the SSTORE-presence discharge needs across the drive walk: a later SSTORE cursor inherits the
entry frame's self-presence through every block step and returning descent. All three edge hypotheses
are satisfiable (not vacuous) — see `StepPreservesSelf`/`CallPreservesSelf`/`CreatePreservesSelf` — so
this introduces no unsatisfiable assumption. -/
theorem selfPresent_runs (hstep : StepPreservesSelf) (hcall : CallPreservesSelf)
    (hcreate : CreatePreservesSelf)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' := by
  induction hruns with
  | refl _ => exact h
  | step hs _ ih => exact ih (hstep hs h)
  | call hc _ ih => exact ih (hcall hc h)
  | create hc _ ih => exact ih (hcreate hc h)

/-- Thread self presence across `Runs`, discharging every edge except immediate
precompile-result preservation. -/
theorem selfPresent_runs_of_call
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' :=
  selfPresent_runs stepPreservesSelf (callPreservesSelf_modGuards hprec)
    (createPreservesSelf_modGuards hprec) h hruns

/-- Immediate precompile calls preserve every account already present in the caller world. -/
def PrecompilesPreservePresence : Prop :=
  ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
    Evm.beginCall cp = .inr imm →
    ∀ a, BytecodeLayer.Hoare.AccPresent a cp.accounts →
      BytecodeLayer.Hoare.AccPresent a imm.accounts

theorem callPreservesSelf_of_precompiles :
    PrecompilesPreservePresence → CallPreservesSelf :=
  fun h => callPreservesSelf_modGuards h

abbrev CallsCode : Evm.Frame → Prop := BytecodeLayer.Interpreter.CallsCode

abbrev CleanHaltsNonException : Evm.Frame → Prop :=
  BytecodeLayer.Hoare.CleanHaltsNonException

def ReachableFrom (params : Evm.CallParams) (fr' : Evm.Frame) : Prop :=
  ∃ fr₀, Evm.beginCall params = .inl fr₀ ∧ BytecodeLayer.Hoare.Runs fr₀ fr'

structure PrecompileAssumptions (params : Evm.CallParams) : Prop where
  noErase : PrecompilesPreservePresence
  callsCode : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CallsCode fr'
  createResolves : ∀ fr', ReachableFrom params fr' → BytecodeLayer.Interpreter.CreateResolves fr'

end BytecodeLayer.Exec.Invariants
