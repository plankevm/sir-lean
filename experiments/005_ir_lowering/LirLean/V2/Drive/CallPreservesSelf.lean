import LirLean.V2.Drive.SelfPresent
import LirLean.Engine.DriveMono

/-!
# LirLean v2 — `SelfPresent` forward-closed along `Runs` (`Drive/CallPreservesSelf`)

The seam-carrying layer of the former `V2/TieDischarge.lean` (decl names and namespaces
unchanged): the two local one-edge preservation predicates (`StepPreservesSelf` — a proven
theorem, `stepPreservesSelf`, via `Engine/StepWalk.lean`'s `stepFrame_next_self`; and
`CallPreservesSelf` — supplied & satisfiable), the `.success`-shape discharge
`callPreservesSelf_success` over `Engine/DriveMono.lean`'s Brick D
(`drive_accounts_find_mono`), the assembled `callPreservesSelf`, and
`callPreservesSelf_modGuards` — which reduces the whole chain to the ONE surviving supplied
hypothesis `hprec` (`beginCall`'s precompile `.inr` arm preserves presence; the seam quoted
verbatim by `V2/RealisabilitySpec.lean`). `selfPresent_runs`/`selfPresent_runs_of_call`
thread `SelfPresent` across an arbitrary `Runs` derivation.

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps
open Lir

/-! ### `SelfPresent`-forward along a whole `Runs` segment (incl. the `Runs.call` resume)

`SelfPresent` transports across one materialise sub-run (account map + self address preserved). The drive walk
glues those sub-runs (and returning external CALLs) into a single `Runs fr fr'` segment between
block boundaries, so the SSTORE-presence discharge needs `SelfPresent` **forward-closed along the
whole `Runs`** — including the `Runs.call` resume node, where the resumed *caller* frame's account
map is the child's returned `result.accounts` (the shared world state threaded back through
`resumeAfterCall`), not the caller's pre-call map.

The `Runs` relation (`BytecodeLayer/Hoare.lean`) has three constructors — `refl` / `step`
(`StepsTo`, one non-halting opcode) / `call` (`CallReturns`, one returning external CALL). The
forward closure is an induction on the derivation (the template is `Runs.gasAvailable_le`): `refl`
is `rfl`, and each `step`/`call` rung is a *local* one-edge preservation. We name those two edges as
predicates so the drive walk discharges them with the facts it already has (the materialise bricks
for `step`, the returning-call world-threading for `call`):

* `StepPreservesSelf` — a single non-halting opcode step preserves the self account's presence.
  **DISCHARGED (no longer supplied): `stepPreservesSelf` is a proven theorem** — every `.next` opcode
  (of *any* program, not just the lowering) leaves `accounts` either untouched (`binOp`/`pushOp`/… via
  `replaceStackAndIncrPC`, and the CALL/CREATE `.next` fallbacks via `resumeAfterCall`/`resumeAfterCreate`
  whose `result.accounts = exec.accounts`) or inserts *at* the self account (`SSTORE`/`TSTORE` via
  `State.sstore`/`State.tstore`); none ever erases it, and the execution environment (hence the self
  address) is preserved throughout. The engine-level brick is `Evm.stepFrame_next_self`, the
  `a := self` corollary of the strengthened accMono dispatch walk (`stepFrame_next_accMono` for the
  presence half, `stepFrame_next_execEnvAddr` for the address transport); `selfPresent_runs`'s first
  hypothesis is satisfied by `stepPreservesSelf` outright.
* `CallPreservesSelf` — a returning external CALL preserves the *caller's* self account presence.
  **Satisfiable, not vacuous**: the resume preserves the self *address* (`resumeAfterCall` rebuilds
  the caller frame, touching only stack/pc/gas/accounts/substate — `resumeAfterCall_address`), and
  the returned `result.accounts` retains the caller's account (its checkpoint on revert/exception is
  the caller's own pre-call map; on success the shared world keeps the caller present — the caller is
  not the callee). The structural address half is banked below; the `result.accounts`-presence half
  is the returning-world fact the drive walk supplies per CALL edge.

The general lemma `selfPresent_runs` threads both across an arbitrary `Runs`; the address-transport
helpers `resumeAfterCall_address`/`resumeAfterCall_accounts` are the `rfl` facts the `call` edge
reduces to. -/

/-- **Local per-step self-presence preservation.** One non-halting opcode step (`StepsTo`) keeps
the self account present. Satisfiable for the lowered program — every `.next` opcode either leaves
`accounts` untouched or inserts at the self account, never erasing it — and supplied per edge by the
materialise-frame preservation (each `.next` post-frame leaves `accounts`/self address untouched). -/
def StepPreservesSelf : Prop :=
  ∀ ⦃fr fr' : Frame⦄, StepsTo fr fr' → SelfPresent fr → SelfPresent fr'

/-- **`StepPreservesSelf` DISCHARGED — fully general, no lower-prog hypothesis.** Every non-halting
opcode step keeps the self account present. A `StepsTo fr fr'` is `stepFrame fr = .next fr'.exec`
(with `fr' = { fr with exec := fr'.exec }`), and `stepFrame_next_self` proves a `.next` step keeps
`SelfAt`; `SelfPresent fr` is `SelfAt fr.exec` and `SelfPresent fr'` is `SelfAt fr'.exec` by
definition. So this holds for **every** frame — in particular for every reachable frame of a
`lower prog` run — and is no longer a supplied edge: `selfPresent_runs`'s first hypothesis is now a
theorem, not an assumption. -/
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

/-- **The `.success` shape of `CallPreservesSelf`, discharged via Brick D.** A returning external
CALL keeps the *caller's* self present, given the same `hmono`/`hprec`/`hcall_acc`/`hcall_kind`/`hhalt`
closers as `drive_accounts_find_mono` plus the CALL-site self-address framing `hcall_self`. The CREATE
arm needs no seam — `drive_accounts_find_mono` now proves it in place (`beginCreate` is total, an
unconditional child descent threaded via `stepFrame_needsCreate_inv`).

The child run `drive (seedFuel cp.gas) [] (running child) = .ok childRes` *starts* present at the
caller's self address `a` (`beginCall` threads `cp.accounts` presence into the child's running map and
checkpoint, `cp.accounts` present from the caller's running map via `hcall_acc`); `drive_accounts_find_mono`
carries that presence to `childRes`'s accounts; `resumeAfterCall_self_of_accounts` then closes
`SelfPresent resumeFr` (the resumed self is the caller's, `resumeAfterCall_address`). Non-vacuous: the
`DrivePresent` premise is genuinely established from `SelfPresent callFr`, not assumed. -/
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
  -- Apply Brick D: presence at `a` is monotone across the child drive run (start `([], inl child)`).
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

/-- **`CallPreservesSelf`, discharged modulo the precompile no-erase seam.** Every shape of a
returning external CALL keeps the caller's self present: `.success` via `callPreservesSelf_success`
(Brick D), `.revert`/`.exception` structurally (folded in — `callPreservesSelf_success` covers the
whole `CallReturns` once the child run terminates, since `childRes` already carries whichever shape).

The seam hypotheses are each genuinely satisfiable (never vacuous) and remain **supplied**:
* `hmono`/`hcall_acc`/`hcall_kind`/`hhalt`/`hcall_self` are *universally-true* framing facts (every
  `.next` step is accounts-monotone at any `a`; `callArm` sets `params.accounts`/`pending.frame` from
  the issuing exec; halting opcodes don't touch accounts) — true for **all** frames, so trivially
  satisfiable (`hmono` is the unproven Brick C, but holds for every frame);
* `hprec` is the precompile-preservation fact (precompiles only insert) — satisfiable, vacuous for
  call-free IR.

The no-CREATE seam is **gone**: `drive`'s CREATE-begin-fault arm now returns the caller checkpoint
(`pending.frame.exec.accounts`, the faithful soft-failure map — not the prior emptied map), so
`drive_accounts_find_mono` proves the whole CREATE step (fault + descent) presence-preserving in place
via `stepFrame_needsCreate_inv`.

`CallPreservesSelf` is *not* unconditionally true (the precompile `.inr` `∅`-arm really can erase, and
`CallReturns` does not by itself rule it out across the child run). The strict improvement over the
prior fully-supplied `CallPreservesSelf`: its `.success` monotonicity is now *discharged* engine-level
(Brick D), and the CREATE no-erase guard is *eliminated* (the faithful fault arm preserves presence). -/
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

/-- **`CallPreservesSelf`, with the five universally-true CALL-seam facts DISCHARGED engine-level.**
The arbitrary-`a` account-monotonicity bricks (this cycle) prove engine-level, for *every* frame:

* `hmono` — `Evm.stepFrame_next_accMono` (Brick C, the `.next` account-presence mono);
* `hcall_acc` / `hcall_kind` / `hcall_self` — `Evm.stepFrame_needsCall_inv` (the CALL-site framing:
  child params' accounts = issuing accounts, suspended frame keeps `kind` and execution-env address);
* `hhalt` — `Evm.stepFrame_halted_success_accMono` (STOP/RETURN/SELFDESTRUCT keep accounts present —
  no erase).

So `callPreservesSelf`'s six supplied hypotheses collapse to **one**: the genuinely-conditional
`hprec` (precompile `.inr` output map — opaque for a live precompile, vacuous for the call-free /
non-precompile-targeting lowered IR). The former no-CREATE seam `hncr` is **eliminated**: `beginCreate`
is total (no begin-fault arm — it always descends into a child), so `drive_accounts_find_mono`
discharges the whole CREATE step engine-level via `stepFrame_needsCreate_inv`. `hprec` remains
**supplied**, genuinely satisfiable and non-vacuous; this
is *not* a hypothesis-free `CallPreservesSelf` (the precompile `.inr` `∅`-arm really can erase). -/
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

/-- **`SelfPresent` is forward-closed along a whole `Runs` segment.** From `SelfPresent fr` and
`Runs fr fr'`, `SelfPresent fr'` — given the two local one-edge preservation facts
(`StepPreservesSelf` for opcode steps, `CallPreservesSelf` for returning external CALLs, *including
the `Runs.call` resume node*). Proved by induction on the `Runs` derivation (the template is
`Runs.gasAvailable_le`): `refl` carries `h` unchanged; `step`/`call` apply the corresponding local
edge then recurse. This is the threading the SSTORE-presence discharge needs across the drive walk:
a later SSTORE cursor inherits the entry frame's self-presence through every block step and returning
call. Both edge hypotheses are satisfiable (not vacuous) — see `StepPreservesSelf`/`CallPreservesSelf`
— so this introduces no unsatisfiable assumption. -/
theorem selfPresent_runs (hstep : StepPreservesSelf) (hcall : CallPreservesSelf)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' := by
  induction hruns with
  | refl _ => exact h
  | step hs _ ih => exact ih (hstep hs h)
  | call hc _ ih => exact ih (hcall hc h)

/-- **`selfPresent_runs` with the step edge already discharged.** Since `stepPreservesSelf` is a
proven theorem (not a supplied edge), the only remaining hypothesis is the CALL edge
`CallPreservesSelf` (the call-tie seam — genuinely-open in its `.success` shape, supplied & satisfiable;
its revert/exception shapes are structurally discharged by `resumeAfterCall_self_of_accounts`). This is
the form the drive walk consumes: thread self-presence across a whole `Runs` with only the returning
external CALL fact to supply. -/
theorem selfPresent_runs_of_call (hcall : CallPreservesSelf)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' :=
  selfPresent_runs stepPreservesSelf hcall h hruns

end Lir.V2

-- StepPreservesSelf is DISCHARGED (a theorem, not a supplied edge): the engine-level brick
-- `stepFrame_next_self` (the `a := self` corollary of the dispatch walk), plus the call-resume
-- structural halves, are all axiom-clean.
-- CALLMONO: account-presence monotone across a whole `drive` run (Brick D) — the `.success` shape
-- of `CallPreservesSelf` discharged (the CREATE no-erase seam now eliminated; only `hprec` supplied).
