import BytecodeLayer.Hoare.Descent

/-!
# Account presence is monotone across a whole `drive` run

The drive-run presence invariant
(`CheckpointPresent` / `StackPresent` / `DrivePresent`), the `endFrame` presence closers
(`endFrame_call_accPresent` / `endFrame_create_accPresent` / `endFrame_accPresent`), and
the strong-fuel drive induction `drive_accounts_find_mono`.

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace BytecodeLayer.Hoare

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps

/-! ### Brick D — account-presence monotone across a whole `drive` run

`drive_accounts_find_mono`: if `a` is present in the running accounts (and in every checkpoint that a
rollback could restore) at the *start* of a `drive` run, it stays present in the run's result. This is
the account-level analogue of `drive_fuel_succ` — a strong-fuel induction following `drive`'s own
recursion — and is the engine-level fact the `.success` shape of `CallPreservesSelf` reduces to.

The presence invariant `DrivePresent a` threads three facts simultaneously, because two `drive` exits
*roll back* the running map to a checkpoint:

* the running `exec.accounts` (`.inl`) / result accounts (`.inr`),
* the **kind checkpoint** of the running `.inl` frame (what `endCall .revert/.exception` restores),
* the kind checkpoint of **every** pending ancestor on the stack (each will become a running frame
  on delivery, and may itself roll back).

The only remaining erase-risk arm is `beginCall`'s precompile `.inr` (closed per-arm by the supplied
`hprec`); `beginCreate` is total (no begin-fault arm — it always descends into a child), so the CREATE
step is proven in place via `stepFrame_needsCreate_inv` with no supplied seam — each supplied closer
(`hmono`/`hprec`/…) genuinely satisfiable, never vacuous (documented at `callPreservesSelf`). -/

/-- Presence at `a` in a frame's kind checkpoint accounts (what `endCall .revert/.exception` and
`endCreate` failure restore). -/
def CheckpointPresent (a : Evm.AccountAddress) (fr : Evm.Frame) : Prop :=
  match fr.kind with
  | .call cp => AccPresent a cp.accounts
  | .create _ cp => AccPresent a cp.accounts

/-- Presence at `a` in every pending ancestor's kind checkpoint. -/
def StackPresent (a : Evm.AccountAddress) : List Evm.Pending → Prop
  | [] => True
  | p :: rest => CheckpointPresent a p.frame ∧ StackPresent a rest

/-- The drive-run presence invariant: `a` present in the running map and in the running frame's
checkpoint (`.inl`) / in the result map (`.inr`), and in every pending ancestor's checkpoint. -/
def DrivePresent (a : Evm.AccountAddress) (stack : List Evm.Pending) :
    Evm.Frame ⊕ Evm.FrameResult → Prop
  | .inl current => AccPresent a current.exec.accounts ∧ CheckpointPresent a current
      ∧ StackPresent a stack
  | .inr result => AccPresent a result.toCallResult.accounts ∧ StackPresent a stack

/-- `endFrame` (a `.call`-kind halt) preserves presence at `a` given running-map presence (the
`.success` swap is killed by `accMono_emptySwap`) and checkpoint presence (the `.revert/.exception`
rollback). The `.create`-kind case is excluded by the no-CREATE seam at the producing step. -/
theorem endFrame_call_accPresent (a : Evm.AccountAddress) (cp : Evm.Checkpoint)
    (halt : Evm.FrameHalt)
    (hcp : AccPresent a cp.accounts)
    (hsucc : ∀ e o, halt = .success e o → AccPresent a e.accounts) :
    AccPresent a (Evm.endCall cp halt).accounts := by
  cases halt with
  | success e o =>
    -- `endCall .success` accounts = `if e.accounts == ∅ then cp.accounts else e.accounts`.
    have he : AccPresent a e.accounts := hsucc e o rfl
    show AccPresent a (if e.accounts == (∅ : Evm.AccountMap) then cp.accounts else e.accounts)
    exact accMono_emptySwap a e.accounts cp.accounts he
  | revert g o => exact (by rw [endCall_revert_accounts]; exact hcp)
  | exception ex => exact (by rw [endCall_exception_accounts]; exact hcp)

/-- `endCreate` preserves presence at `a` given checkpoint presence and running-map presence (on the
deployment-success branch the result map is `exec.accounts.insert address …` — an `insert`, presence
preserving via Brick A; on every failure branch it is the checkpoint map). The `.create`-kind twin of
`endFrame_call_accPresent`. -/
theorem endFrame_create_accPresent (a : Evm.AccountAddress) (addr : Evm.AccountAddress)
    (cp : Evm.Checkpoint) (halt : Evm.FrameHalt)
    (hcp : AccPresent a cp.accounts)
    (hsucc : ∀ e o, halt = .success e o → AccPresent a e.accounts) :
    AccPresent a (Evm.endCreate addr cp halt).accounts := by
  cases halt with
  | success e o =>
    have he : AccPresent a e.accounts := hsucc e o rfl
    show AccPresent a (Evm.endCreate addr cp (.success e o)).accounts
    -- `(endCreate … .success).accounts = if deploymentFailed then cp.accounts else
    --  e.accounts.insert address { (e.accounts.findD address default) with code := o }`.
    -- Case on the (opaque) `deploymentFailed` condition: rollback (cp) or `insert` (Brick A).
    unfold Evm.endCreate
    dsimp only
    -- The `accounts` field is `if deploymentFailed then cp.accounts else e.accounts.insert addr …`.
    -- Case on the (opaque) `deploymentFailed` condition: rollback (cp) vs. `insert` (Brick A).
    split_ifs with hdf
    · exact hcp
    · exact accounts_find?_insert_mono _ _ _ _ he
  | revert g o => exact (by show AccPresent a (Evm.endCreate addr cp (.revert g o)).accounts; exact hcp)
  | exception ex =>
    exact (by show AccPresent a (Evm.endCreate addr cp (.exception ex)).accounts; exact hcp)

/-- `endFrame` preserves presence at `a` for **either** frame kind, given checkpoint presence and (on
a `.success` halt) running-map presence. Combines `endFrame_call_accPresent` /
`endFrame_create_accPresent`; this is the unconditional halt closer for the drive induction (no kind
exclusion needed — both `endCall` and `endCreate` are presence-preserving). -/
theorem endFrame_accPresent (a : Evm.AccountAddress) (current : Evm.Frame) (halt : Evm.FrameHalt)
    (hck : CheckpointPresent a current)
    (hsucc : ∀ e o, halt = .success e o → AccPresent a e.accounts) :
    AccPresent a (Evm.endFrame current halt).toCallResult.accounts := by
  unfold Evm.endFrame
  unfold CheckpointPresent at hck
  cases hk : current.kind with
  | call cp =>
    simp only [hk]
    rw [hk] at hck
    show AccPresent a (Evm.endCall cp halt).accounts
    exact endFrame_call_accPresent a cp halt hck hsucc
  | create addr cp =>
    simp only [hk]
    rw [hk] at hck
    show AccPresent a (Evm.endCreate addr cp halt).toCallResult.accounts
    -- `(endCreate …).toCallResult.accounts = (endCreate …).accounts` (projection is accounts-verbatim).
    exact endFrame_create_accPresent a addr cp halt hck hsucc

/-- **Brick D — account-presence is monotone across a whole `drive` run.** Strong induction on
`fuel` following `drive`'s recursion (template: `drive_fuel_succ`). `DrivePresent a` at the start
yields `AccPresent a` in the result accounts at the end, given:

* `hmono` — the per-`.next`-step account-presence mono at `a` (Brick C; supplied & satisfiable:
  proven outright as `stepFrame_next_accMono`, the presence half of the dispatch walk, whose
  SSTORE/TSTORE arms close via `accounts_find?_insert_mono`);
* `hprec` — `beginCall`'s precompile `.inr` arm preserves presence at `a` (satisfiable: precompiles
  only insert; vacuous for call-free IR);
* `hcall_acc`/`hcall_kind` — the CALL-site boundary facts: the issued `params.accounts` retains
  presence at `a` from the issuing frame's running map, and the suspended `pending.frame` keeps the
  issuing frame's checkpoint (`callArm` sets `params.accounts := (post-charge) exec.accounts` —
  `charge` is accounts-verbatim — and `pending.frame := { current with exec := … }`, same `kind`).
  Satisfiable & local (the `callArm` framing); supplied to keep the drive induction self-contained
  rather than re-diving the `stepFrame → dispatch → systemOp → callArm` chain;
* `hhalt` — the halting-opcode account-verbatim fact (STOP/RETURN/REVERT don't touch accounts).

The CREATE arm needs **no** seam: `drive`'s CREATE-begin-fault arm now returns the caller checkpoint
(`pending.frame.exec.accounts`, the issuing frame's running map — the faithful soft-failure behaviour,
*not* the prior emptied map), so it preserves presence directly; and the CREATE descent threads
presence into the child the same way the CALL descent does. Both sub-arms are proven in place via the
universally-true CREATE-site inversion `stepFrame_needsCreate_inv` (the create twin of
`stepFrame_needsCall_inv`) — so no frame-kind exclusion / no-CREATE side-condition is needed. All
supplied seams are `∀`-quantified (constant across the recursion); both `endCall` **and** `endCreate`
are presence-preserving (success = `insert`, failure = checkpoint), so no kind exclusion is needed at
the halt/resume arms either. -/
theorem drive_accounts_find_mono (a : Evm.AccountAddress)
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → AccPresent a fr.exec.accounts →
        AccPresent a e.accounts) :
    ∀ (f : ℕ) (stack : List Evm.Pending) (state : Evm.Frame ⊕ Evm.FrameResult)
      (res : Evm.FrameResult),
      Evm.drive f stack state = .ok res → DrivePresent a stack state →
      AccPresent a res.toCallResult.accounts := by
  intro f
  induction f with
  | zero => intro stack state res h _; simp [Evm.drive] at h
  | succ n ih =>
    intro stack state res hdrive hpres
    unfold Evm.drive at hdrive
    cases state with
    | inr result =>
      cases stack with
      | nil =>
        -- terminal delivery: `res = result`, presence carried by `hpres`.
        simp only at hdrive
        obtain ⟨hr, _⟩ := hpres
        rw [(Except.ok.injEq _ _).mp hdrive] at hr; exact hr
      | cons pending rest =>
        dsimp only at hdrive
        obtain ⟨hresult, hstk⟩ := hpres
        obtain ⟨hpend, hrest⟩ := hstk
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at hdrive; dsimp only at hdrive
          refine ih rest (.inl parent) res hdrive ⟨?_, ?_, hrest⟩
          · -- parent.exec.accounts presence: for `.call`, `= result.accounts` (resumeAfterCall);
            -- for `.create`, `= result.accounts` (resumeAfterCreate), both present by `hresult`.
            cases pending with
            | call pd =>
              simp only [Evm.Pending.resume, Except.ok.injEq] at hres
              rw [← hres]
              show AccPresent a (Evm.resumeAfterCall result.toCallResult pd).exec.accounts
              rw [resumeAfterCall_accounts]; exact hresult
            | create pd =>
              -- `Pending.resume (.create pd) = resumeAfterCreate result.toCreateResult pd`; on `.ok`
              -- the resumed exec.accounts = result.accounts (present), so transports `hresult`.
              simp only [Evm.Pending.resume] at hres
              exact resumeAfterCreate_exec_accounts_present a result pd parent hres hresult
          · -- parent checkpoint presence: both resumes rebuild `pd.frame` with the same `kind`.
            cases pending with
            | call pd =>
              simp only [Evm.Pending.resume, Except.ok.injEq] at hres
              rw [← hres]
              show CheckpointPresent a (Evm.resumeAfterCall result.toCallResult pd)
              have hkeq : (Evm.resumeAfterCall result.toCallResult pd).kind = pd.frame.kind := rfl
              unfold CheckpointPresent; rw [hkeq]; exact hpend
            | create pd =>
              simp only [Evm.Pending.resume] at hres
              have hkeq : parent.kind = pd.frame.kind :=
                resumeAfterCreate_kind result pd parent hres
              show CheckpointPresent a parent
              unfold CheckpointPresent; rw [hkeq]; exact hpend
        | error e =>
          rw [hres] at hdrive; dsimp only at hdrive
          -- resume faulted: parent halts exceptionally; deliver `endFrame pending.frame (.exception e)`.
          refine ih rest (.inr (Evm.endFrame pending.frame (.exception e))) res hdrive ⟨?_, hrest⟩
          -- `endFrame .exception` rolls back to the checkpoint (present `hpend`); no `.success` arg.
          refine endFrame_accPresent a pending.frame (.exception e) hpend ?_
          intro e' o' hcon; exact absurd hcon (by nofun)
    | inl current =>
      dsimp only at hdrive
      obtain ⟨hrun, hck, hstk⟩ := hpres
      cases hstep : Evm.stepFrame current with
      | next exec =>
        rw [hstep] at hdrive; dsimp only at hdrive
        refine ih stack (.inl { current with exec := exec }) res hdrive ⟨?_, ?_, hstk⟩
        · show AccPresent a exec.accounts; exact hmono current exec hstep hrun
        · -- `.next` updates only `exec`; `kind` (hence checkpoint) unchanged.
          show CheckpointPresent a { current with exec := exec }
          unfold CheckpointPresent; exact hck
      | halted halt =>
        rw [hstep] at hdrive; dsimp only at hdrive
        refine ih stack (.inr (Evm.endFrame current halt)) res hdrive ⟨?_, hstk⟩
        -- `endFrame current halt`: presence-preserving for either kind (`endFrame_accPresent`);
        -- on `.success`, the running map at halt is `hrun`.
        refine endFrame_accPresent a current halt hck ?_
        intro e o he; exact hhalt current e o (by rw [hstep, he]) hrun
      | needsCall params pending =>
        rw [hstep] at hdrive; dsimp only at hdrive
        have hcpacc : AccPresent a params.accounts := hcall_acc current params pending hstep hrun
        have hpf : pending.frame.kind = current.kind := hcall_kind current params pending hstep
        cases hbc : Evm.beginCall params with
        | inl child =>
          rw [hbc] at hdrive; dsimp only at hdrive
          refine ih (.call pending :: stack) (.inl child) res hdrive ⟨?_, ?_, ?_, hstk⟩
          · exact beginCall_inl_accounts_present a params hbc hcpacc
          · obtain ⟨created, sub, hkind⟩ := beginCall_inl_checkpoint params hbc
            unfold CheckpointPresent; rw [hkind]; exact hcpacc
          · show CheckpointPresent a pending.frame
            unfold CheckpointPresent; rw [hpf]
            unfold CheckpointPresent at hck; exact hck
        | inr immediate =>
          rw [hbc] at hdrive; dsimp only at hdrive
          refine ih (.call pending :: stack) (.inr (.call immediate)) res hdrive ⟨?_, ?_, hstk⟩
          · show AccPresent a immediate.accounts; exact hprec params immediate hbc hcpacc
          · show CheckpointPresent a pending.frame
            unfold CheckpointPresent; rw [hpf]
            unfold CheckpointPresent at hck; exact hck
      | needsCreate params pending =>
        rw [hstep] at hdrive; dsimp only at hdrive
        -- CREATE-site inversion (the create twin of `hcall_acc`/`hcall_kind`): `params.accounts`
        -- keeps presence from the issuing running map, the suspended `pending.frame` keeps the
        -- issuing `kind`, and its running map is exactly `current.exec.accounts`.
        -- (`hcr_pdacc`, the suspended-caller running map, fed only the removed CREATE-begin
        -- fault arm; `beginCreate` is now total so that arm is gone.)
        obtain ⟨hcr_acc, hcr_kind, _⟩ := Evm.stepFrame_needsCreate_inv hstep
        have hcpacc : AccPresent a params.accounts := hcr_acc a hrun
        -- `beginCreate` is total: the descent into `beginCreate params` is unconditional.
        refine ih (.create pending :: stack) (.inl (Evm.beginCreate params)) res hdrive ⟨?_, ?_, ?_, hstk⟩
        · -- child running map: `accountsWithNew` (verbatim or ≤2 inserts over `params.accounts`).
          exact beginCreate_ok_accounts_present a params rfl hcpacc
        · -- child checkpoint: the `.create _ ⟨_, params.accounts, _⟩` node carries `params.accounts`.
          obtain ⟨addr, created, sub, hkind⟩ := beginCreate_ok_checkpoint params rfl
          unfold CheckpointPresent; rw [hkind]; exact hcpacc
        · -- pending ancestor checkpoint: same `kind` as `current`, present by `hck`.
          show CheckpointPresent a pending.frame
          unfold CheckpointPresent; rw [hcr_kind]
          unfold CheckpointPresent at hck; exact hck

end BytecodeLayer.Hoare

-- CALLMONO Brick D: account-presence monotone across a whole `drive` run — the `.success` shape
-- of `CallPreservesSelf` discharged (the CREATE no-erase seam eliminated; only `hprec` supplied).
