import LirLean.Engine.AccountMap
import BytecodeLayer.Hoare.CallSequence

/-!
# `LirLean.Engine.StepWalk` — the ONE dispatch walk: env-equality + account-presence mono

The engine-level per-opcode `.next` induction (CALLMONO Brick C) and its frame-level wrappers,
extracted verbatim from the former `V2/TieDischarge.lean` monolith (names and namespaces unchanged; zero IR / zero
recorder / zero `SelfPresent`):

* the accounts/env framing prims (`charge_accounts_env`, `chargeMemExpansion_accounts_env`,
  `replaceStackAndIncrPC_accounts`, `continueWith_next`, `sstore_accMono`/`tstore_accMono`);
* the `resumeAfterCall`/`endCall` structural `rfl` facts (`resumeAfterCall_address`/`_accounts`,
  `endCall_revert_accounts`/`endCall_exception_accounts`);
* the strengthened accMono dispatch walk (every `.next` arm concludes
  `exec'.executionEnv = exec.executionEnv ∧ ∀ a, AccPresent a … → AccPresent a …`), capped by
  `stepFrame_next_accMono` / `stepFrame_next_execEnvAddr` / the `a := self` corollary
  `stepFrame_next_self` (stated on `SelfAt`, the raw-execution-state presence predicate);
* the halt-success presence family (`stepFrame_halted_success_accMono` and its `haltOp` arms).

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Lir.V2

open Evm
open GasConstants

/-! ### `StepPreservesSelf` is DISCHARGED — every `.next` opcode keeps the self account present

The materialise post-frames leave the self account present (`accounts`/self address untouched, `rfl`). The
`Runs`-level `StepPreservesSelf` edge ranges over the **engine** `stepFrame`, so it needs the
account-presence preservation proved for *every* `.next`-producing opcode `Evm.stepFrame` can take —
not just the ones the lowering emits. We prove that fully generally here, so `StepPreservesSelf`
becomes a theorem (no longer a supplied hypothesis), discharged outright for the lowered program (and
every program). The template is `Runs.gasAvailable_le`'s `StepsTo.gas_le` brick: split System vs
non-`System`, case the dispatch/`systemOp` arm.

The two facts a `.next` step preserves:
* `exec'.executionEnv.address = exec.executionEnv.address` — **every** opcode (`replaceStackAndIncrPC`/
  `charge`/the CALL/CREATE resumes all leave `executionEnv` untouched), and
* presence at that address — `accounts` is either left verbatim (all arithmetic/env/memory/jump/SLOAD
  ops, and the CALL/CREATE `.next` fallbacks via `resumeAfterCall`/`resumeAfterCreate` whose
  `result.accounts = exec.accounts`) or has an account **inserted at the self address** (SSTORE/TSTORE
  via `State.sstore`/`State.tstore`, whose `none` branch is the map verbatim and whose `some` branch is
  `setAccount self … = insert self …`). No opcode inside `drive` ever erases the self entry. -/

/-- `charge` leaves the account map and execution environment untouched (only `gasAvailable`
moves): if `charge c e = .ok e'` then `e'.accounts = e.accounts` and `e'.executionEnv =
e.executionEnv`. -/
theorem charge_accounts_env {c : ℕ} {e e' : ExecutionState} (h : charge c e = .ok e') :
    e'.accounts = e.accounts ∧ e'.executionEnv = e.executionEnv := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- `charge` preserves the program counter. -/
theorem charge_pc {c : ℕ} {e e' : ExecutionState} (h : charge c e = .ok e') :
    e'.pc = e.pc := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    subst h
    rfl

/-- `chargeMemExpansion` likewise leaves `accounts`/`executionEnv` untouched. -/
theorem chargeMemExpansion_accounts_env {e e' : ExecutionState} {off sz : UInt256}
    (h : chargeMemExpansion e off sz = .ok e') :
    e'.accounts = e.accounts ∧ e'.executionEnv = e.executionEnv := by
  unfold chargeMemExpansion at h
  split at h
  · exact absurd h (by simp)
  · exact charge_accounts_env h

/-- `chargeMemExpansion` preserves the program counter. -/
theorem chargeMemExpansion_pc {e e' : ExecutionState} {off sz : UInt256}
    (h : chargeMemExpansion e off sz = .ok e') :
    e'.pc = e.pc := by
  unfold chargeMemExpansion at h
  split at h
  · exact absurd h (by simp)
  · exact charge_pc h

/-- `charge` leaves the memory byte-map untouched (only `gasAvailable` moves). -/
theorem charge_memory {c : ℕ} {e e' : ExecutionState} (h : charge c e = .ok e') :
    e'.toMachineState.memory = e.toMachineState.memory := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h; subst h; rfl

/-- `chargeMemExpansion` charges gas but never writes memory bytes. -/
theorem chargeMemExpansion_memory {e e' : ExecutionState} {off sz : UInt256}
    (h : chargeMemExpansion e off sz = .ok e') :
    e'.toMachineState.memory = e.toMachineState.memory := by
  unfold chargeMemExpansion at h
  split at h
  · exact absurd h (by simp)
  · exact charge_memory h

/-- `charge` leaves `activeWords` untouched (only `gasAvailable` moves). -/
theorem charge_activeWords {c : ℕ} {e e' : ExecutionState} (h : charge c e = .ok e') :
    e'.toMachineState.activeWords = e.toMachineState.activeWords := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h; subst h; rfl

/-- `chargeMemExpansion` charges gas but never mutates `activeWords` (it only *reads* it to
compute the cost). -/
theorem chargeMemExpansion_activeWords {e e' : ExecutionState} {off sz : UInt256}
    (h : chargeMemExpansion e off sz = .ok e') :
    e'.toMachineState.activeWords = e.toMachineState.activeWords := by
  unfold chargeMemExpansion at h
  split at h
  · exact absurd h (by simp)
  · exact charge_activeWords h

/-- **The presence side-condition `SelfPresent` reads, stated on raw execution states.** -/
def SelfAt (exec : ExecutionState) : Prop :=
  ∃ acc : Account, exec.accounts.find? exec.executionEnv.address = some acc

/-! ### The `resumeAfterCall`/`endCall` structural transport facts

The `rfl` halves of the `Runs.call` resume's presence transport (the `SelfPresent`-stating
consumers live in `V2/Drive`): the resumed frame keeps the suspended caller's `executionEnv`
and takes the child's returned `result.accounts`; `endCall` rolls back to the checkpoint map
on `.revert`/`.exception`. -/

/-- The resumed frame's self address is the *caller's* self address: `resumeAfterCall` rebuilds
`pd.frame` (the suspended caller) touching only stack/pc/gas/accounts/substate, leaving
`executionEnv` (hence `.address`) untouched. The structural half of the `Runs.call` resume's
self-presence transport. -/
theorem resumeAfterCall_address (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.executionEnv.address
      = pd.frame.exec.executionEnv.address := rfl

/-- The resumed frame's account map is the child's returned `result.accounts` (the shared world
state threaded back). The structural half of the `Runs.call` resume's self-presence transport:
self-presence at the resumed frame is exactly `result.accounts.find? (caller self) = some _`. -/
theorem resumeAfterCall_accounts (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.accounts = result.accounts := rfl

/-- **On `.revert`/`.exception`, `endCall` returns the caller's pre-call account map verbatim.**
`endCall checkpoint (.revert …)` and `endCall checkpoint (.exception …)` both set `accounts :=
checkpoint.accounts` (the caller's pre-call world is rolled back). The structural half of
`CallPreservesSelf` for the two failing `CallResult` shapes: if the caller self was present in the
pre-call `checkpoint.accounts` (the very map `SelfPresent` held against at `callFr`), it is present in
the returned result. The remaining `.success` shape is the genuinely-open residual
`drive_accounts_find_mono` (account-presence monotone across the child `drive` run; out of scope here
— a whole-child-run induction of P5-spine magnitude). -/
theorem endCall_revert_accounts (checkpoint : Evm.Checkpoint) (g : UInt64) (o : ByteArray) :
    (Evm.endCall checkpoint (.revert g o)).accounts = checkpoint.accounts := by
  rfl

theorem endCall_exception_accounts (checkpoint : Evm.Checkpoint) (e : Evm.ExecutionException) :
    (Evm.endCall checkpoint (.exception e)).accounts = checkpoint.accounts := rfl

end Lir.V2

/-! ### The engine-level `.next` combinator inversion

`continueWith` is the shared exit of every simple dispatch arm; its `.next` carries the argument
verbatim. The per-arm preservation facts themselves live in the strengthened accMono dispatch walk
below (env-equality + presence-mono in ONE induction); `SelfAt` preservation is its `a := self`
corollary `stepFrame_next_self`. -/

namespace Evm

open GasConstants

/-- A `.next` produced by `continueWith` carries its argument verbatim: `continueWith e = .ok (.next
e')` forces `e' = e`. -/
theorem continueWith_next {e e' : ExecutionState} (h : continueWith e = .ok (.next e')) : e' = e := by
  unfold continueWith at h
  simp only [Except.ok.injEq, Signal.next.injEq] at h
  exact h.symm

/-- If `Frame.get_dest` resolves a branch target, the resolved pc is one of the frame's recorded
valid jump destinations. -/
theorem Frame.get_dest_some_mem {fr : Frame} {dest : UInt256} {newpc : UInt32}
    (h : fr.get_dest dest = some newpc) : newpc ∈ fr.validJumps := by
  unfold Frame.get_dest at h
  cases hto : dest.toUInt32? with
  | none =>
      rw [hto] at h
      simp at h
  | some d =>
      rw [hto] at h
      simp only [bind, Option.bind] at h
      have hsome : (fr.validJumps.find? (fun x => x == d)).isSome := by
        simp [h]
      convert Array.get_find?_mem (xs := fr.validJumps) (p := fun x => x == d) hsome using 1
      simp [h]

end Evm

/-! ### CALLMONO Brick C — the ONE dispatch walk: env-equality + account-presence mono (engine level)

The single per-opcode `.next` induction, carrying BOTH facts every `.next` arm satisfies:

* `exec'.executionEnv = exec.executionEnv` — **every** `.next` opcode leaves the execution
  environment untouched (`replaceStackAndIncrPC`/`charge`/`chargeMemExpansion` and the CALL/CREATE
  fallback resumes all preserve it). This half is *unconditional* (not under a presence
  hypothesis) — it supports the standalone `stepFrame_next_execEnvAddr`.
* `∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts` — presence at an arbitrary
  tracked `a` is monotone. Every arm collapses to one of two closers:
  * `accMono_of_accounts_eq a (h : exec'.accounts = exec.accounts)` — the verbatim-accounts arms
    (all but SSTORE/TSTORE), where `charge`/`chargeMemExpansion`/`replaceStackAndIncrPC` preserve
    accounts;
  * `accounts_find?_insert_mono` (Brick A) — the insert-at-self arms (SSTORE/TSTORE), where the
    write is an `insert` at the self key and presence at any `a` survives.

CALL/CREATE `.next` (the funds/depth fallback) resume with `result.accounts = exec.accounts` (the
captured caller map) and the suspended caller's `executionEnv`, so both halves transport verbatim.
The self-address instance (`a := self`, transported along the env half) is `stepFrame_next_self`
below — the former standalone `SelfAt` walk is subsumed by this one induction. -/

namespace Evm
open GasConstants

/-- `replaceStackAndIncrPC` preserves the account map (it touches only `stack`/`pc`). -/
theorem replaceStackAndIncrPC_accounts {e : ExecutionState} (s : Stack UInt256) (pcΔ : UInt8) :
    (ExecutionState.replaceStackAndIncrPC e s pcΔ).accounts = e.accounts := rfl

/-- `replaceStackAndIncrPC` advances the program counter by its explicit byte delta. -/
theorem replaceStackAndIncrPC_pc {e : ExecutionState} (s : Stack UInt256) (pcΔ : UInt8) :
    (ExecutionState.replaceStackAndIncrPC e s pcΔ).pc = e.pc + pcΔ.toUInt32 := rfl

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- Presence at `a` survives `replaceStackAndIncrPC` of a state whose accounts equal a present base.
The base accounts equality `hacc` is given up to defeq (`e.accounts` is read through
`replaceStackAndIncrPC`). -/
theorem accMono_replaceOfBase {base e : ExecutionState} (s : Stack UInt256) (pcΔ : UInt8)
    {a : AccountAddress} (hacc : e.accounts = base.accounts)
    (h : AccPresent a base.accounts) :
    AccPresent a (ExecutionState.replaceStackAndIncrPC e s pcΔ).accounts := by
  refine accMono_of_accounts_eq a ?_ h
  rw [replaceStackAndIncrPC_accounts, hacc]

/-- **`State.sstore` keeps presence at an arbitrary `a`.** The `none` branch is verbatim; the `some`
branch inserts at the self key, and presence at any `a` survives the insert (Brick A). -/
theorem sstore_accMono (st : State) (key val : UInt256) (a : AccountAddress)
    (h : Lir.V2.AccPresent a st.accounts) :
    Lir.V2.AccPresent a (st.sstore key val).accounts := by
  unfold State.sstore
  simp only [State.lookupAccount, Option.option]
  cases hr : st.accounts.find? st.executionEnv.address with
  | none => simpa only [hr] using h
  | some acc =>
    simp only [hr]
    exact Lir.V2.accounts_find?_insert_mono _ _ _ _ h

/-- **`State.tstore` keeps presence at an arbitrary `a`.** Same shape as `sstore_accMono`. -/
theorem tstore_accMono (st : State) (key val : UInt256) (a : AccountAddress)
    (h : Lir.V2.AccPresent a st.accounts) :
    Lir.V2.AccPresent a (st.tstore key val).accounts := by
  unfold State.tstore
  simp only [State.lookupAccount, Option.option]
  cases hr : st.accounts.find? st.executionEnv.address with
  | none => simpa only [hr] using h
  | some acc =>
    simp only [hr]
    exact Lir.V2.accounts_find?_insert_mono _ _ _ _ h

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- The accounts-verbatim post-`charge`/`replaceStackAndIncrPC` shape: env-equality + presence
monotone at every `a`, captured once for the simple dispatch arms. -/
theorem dispatch_simple_arm_next_accMono {exec echarged e exec' : ExecutionState}
    {s : Stack UInt256} {pcΔ : UInt8} {cost : ℕ}
    (hc : charge cost exec = .ok echarged)
    (hbase_acc : e.accounts = echarged.accounts)
    (hbase_env : e.executionEnv = echarged.executionEnv)
    (heq : exec' = ExecutionState.replaceStackAndIncrPC e s pcΔ) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  subst heq
  obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
  refine ⟨?_, fun a h => ?_⟩
  · show e.executionEnv = exec.executionEnv
    rw [hbase_env, hcenv]
  · refine accMono_of_accounts_eq a ?_ h
    rw [replaceStackAndIncrPC_accounts, hbase_acc, hcacc]

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- A `pushOp` `.next` preserves the execution environment and presence at every `a`. -/
theorem pushOp_next_accMono {v : ExecutionState → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : pushOp v exec cost = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold pushOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h
    exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)

/-- A `pushOp` `.next` advances the program counter by one byte. -/
theorem pushOp_next_pc {v : ExecutionState → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : pushOp v exec cost = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold pushOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h
    rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
    rw [Lir.V2.charge_pc hc]
    rfl

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- A `unStateOp` `.next` whose world-op `f` leaves `accounts`/`executionEnv` fixed preserves the
execution environment and presence at every `a`. -/
theorem unStateOp_next_accMono {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec exec' : ExecutionState}
    (hf : ∀ (st : Evm.State) (x : UInt256), (f st x).1.accounts = st.accounts
        ∧ (f st x).1.executionEnv = st.executionEnv)
    (h : unStateOp f cost exec = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold unStateOp at h
  simp only [bind, Except.bind] at h
  cases hpop : exec.stack.pop with
  | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨st1, x⟩ := v; rw [hpop] at h
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hc : charge (cost exec x) exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h
      simp only [] at h
      rw [continueWith_next h]
      obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
      obtain ⟨hfacc, hfenv⟩ := hf ec.toState x
      refine ⟨?_, fun a hp => ?_⟩
      · show (f ec.toState x).1.executionEnv = exec.executionEnv
        rw [hfenv, hcenv]
      · refine accMono_of_accounts_eq a ?_ hp
        show (f ec.toState x).1.accounts = exec.accounts
        rw [hfacc, hcacc]

/-- `unStateOp` `.next` advances the program counter by one byte. -/
theorem unStateOp_next_pc {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec exec' : ExecutionState}
    (h : unStateOp f cost exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold unStateOp at h
  simp only [bind, Except.bind] at h
  cases hpop : exec.stack.pop with
  | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨st1, x⟩ := v; rw [hpop] at h
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hc : charge (cost exec x) exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h
      simp only [] at h
      rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
      rw [Lir.V2.charge_pc hc]
      rfl

/-- The `POP` stack-management arm advances by one byte on `.next`. -/
theorem smsf_pop_next_pc {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp .POP fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold smsfOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge Gbase exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h
    simp only [] at h
    cases hpop : ec.stack.pop with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, _⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
      rw [Lir.V2.charge_pc hc]
      rfl

/-- The `MLOAD` arm advances by one byte on `.next`. -/
theorem smsf_mload_next_pc {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp .MLOAD fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold smsfOp at h
  simp only [bind, Except.bind] at h
  cases hpop : exec.stack.pop with
  | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨stk, addr⟩ := v; rw [hpop] at h
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hm : chargeMemExpansion exec addr 32 with
    | error e => rw [hm] at h; simp at h
    | ok em =>
      rw [hm] at h; simp only [] at h
      cases hc : charge Gverylow em with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
        rw [Lir.V2.charge_pc hc, Lir.V2.chargeMemExpansion_pc hm]
        rfl

/-- The `MSTORE` arm advances by one byte on `.next`. -/
theorem smsf_mstore_next_pc {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp .MSTORE fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold smsfOp at h
  simp only [bind, Except.bind] at h
  cases hpop : exec.stack.pop2 with
  | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨stk, addr, val⟩ := v; rw [hpop] at h
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hm : chargeMemExpansion exec addr 32 with
    | error e => rw [hm] at h; simp at h
    | ok em =>
      rw [hm] at h; simp only [] at h
      cases hc : charge Gverylow em with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
        rw [Lir.V2.charge_pc hc, Lir.V2.chargeMemExpansion_pc hm]
        rfl

/-- The `SLOAD` arm advances by one byte on `.next`. -/
theorem smsf_sload_next_pc {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp .SLOAD fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold smsfOp at h
  exact unStateOp_next_pc h

/-- The `SSTORE` arm advances by one byte on `.next`. -/
theorem smsf_sstore_next_pc {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp .SSTORE fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold smsfOp at h
  simp only [bind, Except.bind] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h
    simp only [] at h
    split at h
    · simp at h
    · cases hpop : exec.stack.pop2 with
      | none =>
        rw [hpop] at h
        simp [MonadLift.monadLift, liftM, monadLift, Option.option, pure, Except.pure] at h
      | some v =>
        obtain ⟨stk, key, newValue⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge _ exec with
        | error e => rw [hc] at h; simp [pure, Except.pure] at h
        | ok ec =>
          rw [hc] at h
          simp only [] at h
          rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
          rw [Lir.V2.charge_pc hc]
          rfl

/-- The `GAS` arm advances by one byte on `.next`. -/
theorem smsf_gas_next_pc {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp .GAS fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold smsfOp at h
  exact pushOp_next_pc h

open Lir.V2 (AccPresent) in
/-- A `charge`-then-`SSTORE`-write `.next` preserves the execution environment and presence at
every `a` (`State.sstore` writes only `accounts`/`substate`: the `none` branch is verbatim, the
`some` branch is `setAccount`/`addAccessedStorageKey`/substate updates — `executionEnv` fixed). -/
theorem charge_sstore_next_accMono {cost : ℕ} {exec exec' : ExecutionState} {key newVal : UInt256}
    {st : Stack UInt256}
    (h : (charge cost exec).bind (fun ec => continueWith
        (ExecutionState.replaceStackAndIncrPC { ec with toState := ec.toState.sstore key newVal } st))
      = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hc] at h; simp only [bind, Except.bind] at h
    rw [continueWith_next h]
    obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
    have henvs : (ec.toState.sstore key newVal).executionEnv = ec.toState.executionEnv := by
      unfold State.sstore
      simp only [State.lookupAccount, Option.option]
      cases hr : ec.toState.accounts.find? ec.toState.executionEnv.address with
      | none => rfl
      | some acc => rfl
    refine ⟨?_, fun a hp => ?_⟩
    · show (ec.toState.sstore key newVal).executionEnv = exec.executionEnv
      rw [henvs]
      exact hcenv
    · rw [replaceStackAndIncrPC_accounts]
      show AccPresent a (ec.toState.sstore key newVal).accounts
      refine sstore_accMono ec.toState key newVal a ?_
      show AccPresent a ec.accounts
      exact Lir.V2.accMono_of_accounts_eq a hcacc hp

open Lir.V2 (AccPresent) in
/-- The `TSTORE` twin of `charge_sstore_next_accMono`. -/
theorem charge_tstore_next_accMono {cost : ℕ} {exec exec' : ExecutionState} {key val : UInt256}
    {st : Stack UInt256}
    (h : (charge cost exec).bind (fun ec => continueWith
        (ExecutionState.replaceStackAndIncrPC { ec with toState := ec.toState.tstore key val } st))
      = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hc] at h; simp only [bind, Except.bind] at h
    rw [continueWith_next h]
    obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
    have henvs : (ec.toState.tstore key val).executionEnv = ec.toState.executionEnv := by
      unfold State.tstore
      simp only [State.lookupAccount, Option.option]
      cases hr : ec.toState.accounts.find? ec.toState.executionEnv.address with
      | none => rfl
      | some acc => rfl
    refine ⟨?_, fun a hp => ?_⟩
    · show (ec.toState.tstore key val).executionEnv = exec.executionEnv
      rw [henvs]
      exact hcenv
    · rw [replaceStackAndIncrPC_accounts]
      show AccPresent a (ec.toState.tstore key val).accounts
      refine tstore_accMono ec.toState key val a ?_
      show AccPresent a ec.accounts
      exact Lir.V2.accMono_of_accounts_eq a hcacc hp

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- `unOp` `.next` preserves the execution environment and presence at every `a`. -/
theorem unOp_next_accMono {f : UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : unOp f exec cost = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold unOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hpop : ec.stack.pop with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, x⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- `binOp` `.next` preserves the execution environment and presence at every `a`. -/
theorem binOp_next_accMono {f : UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : binOp f exec cost = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold binOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hpop : ec.stack.pop2 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, x, y⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)

/-- `binOp` `.next` advances the program counter by one byte. -/
theorem binOp_next_pc {f : UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : binOp f exec cost = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  unfold binOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hpop : ec.stack.pop2 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, x, y⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      rw [continueWith_next h, ExecutionState.replaceStackAndIncrPC]
      rw [Lir.V2.charge_pc hc]
      rfl

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- `ternOp` `.next` preserves the execution environment and presence at every `a`. -/
theorem ternOp_next_accMono {f : UInt256 → UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState}
    {cost : ℕ} (h : ternOp f exec cost = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold ternOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hpop : ec.stack.pop3 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, x, y, z⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- `dup` `.next` preserves the execution environment and presence at every `a`. -/
theorem dup_next_accMono {n : ℕ} {exec exec' : ExecutionState}
    (h : dup n exec = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold dup at h
  simp only [bind, Except.bind] at h
  cases hc : charge Gverylow exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hd : ec.stack[n-1]? with
    | none => rw [hd] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | some x =>
      rw [hd] at h; simp only [] at h
      exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- `swap` `.next` preserves the execution environment and presence at every `a`. -/
theorem swap_next_accMono {n : ℕ} {exec exec' : ExecutionState}
    (h : swap n exec = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold swap at h
  simp only [bind, Except.bind] at h
  cases hc : charge Gverylow exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    split at h
    · exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)
    · simp [throw, throwThe, MonadExceptOf.throw] at h

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- `logArm` `.next` preserves the execution environment and presence at every `a` (`logOp` touches
only `substate`/`activeWords`). -/
theorem logArm_next_accMono {exec exec' : ExecutionState} {stk : Stack UInt256} {offset size : UInt256}
    {topics : Array UInt256}
    (h : logArm exec stk offset size topics = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold logArm at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h; simp only [] at h
    cases hm : chargeMemExpansion exec offset size with
    | error e => rw [hm] at h; simp at h
    | ok em =>
      rw [hm] at h; simp only [] at h
      cases hc : charge (logCost topics.size size) em with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        rw [continueWith_next h]
        obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
        obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
        refine ⟨?_, fun a hp => ?_⟩
        · show (ec.logOp offset size topics).executionEnv = exec.executionEnv
          show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
        · refine accMono_of_accounts_eq a ?_ hp
          show (ec.logOp offset size topics).accounts = exec.accounts
          show ec.accounts = exec.accounts; rw [hcacc, hmacc]

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **`callArm` `.next` (fallback) preserves the execution environment and presence at every `a`.**
The funds/depth fallback resumes via `resumeAfterCall failed pending`, whose `.exec.accounts =
failed.accounts = exec.accounts` (the captured caller map; `charge` preserves accounts) and whose
`.exec.executionEnv` is the suspended caller's (`pending.frame.exec = e2`, whose env equals
`exec`'s since `charge` preserves it). -/
theorem callArm_next_accMono
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {exec' : ExecutionState}
    (h : callArm fr exec stack gas caller recipient codeAddress value apparentValue
          inOffset inSize outOffset outSize permission = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  rw [callArm] at h
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none => rw [hw] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp at h
    | ok e1 =>
      rw [he1] at h
      simp only [] at h
      obtain ⟨he1acc, he1env⟩ := Lir.V2.charge_accounts_env he1
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      set childGas := if value = 0 then gasCap else gasCap + Gcallstipend with hcg
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp at h
      | ok e2 =>
        rw [he2] at h
        simp only [] at h
        obtain ⟨he2acc, he2env⟩ := Lir.V2.charge_accounts_env he2
        split at h
        · -- needsCall branch: contradiction
          simp only [Except.ok.injEq] at h
          exact absurd h (by simp)
        · -- next (fallback) branch
          simp only [Except.ok.injEq, Signal.next.injEq] at h
          subst h
          -- `exec' = (resumeAfterCall failed pending).exec`; accounts = failed.accounts = e1.accounts,
          -- env = pending.frame.exec.executionEnv = e2.executionEnv = exec.executionEnv.
          refine ⟨?_, fun a hp => ?_⟩
          · show e2.executionEnv = exec.executionEnv
            rw [he2env, he1env]
          · show AccPresent a (resumeAfterCall _ _).exec.accounts
            rw [Lir.V2.resumeAfterCall_accounts]
            exact accMono_of_accounts_eq a he1acc hp

/-- `callArm` `.next` is the funds/depth fallback and resumes after the CALL byte. -/
theorem callArm_next_pc
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {exec' : ExecutionState}
    (h : callArm fr exec stack gas caller recipient codeAddress value apparentValue
          inOffset inSize outOffset outSize permission = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  rw [callArm] at h
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none => rw [hw] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp at h
    | ok e1 =>
      rw [he1] at h
      simp only [] at h
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp at h
      | ok e2 =>
        rw [he2] at h
        simp only [] at h
        split at h
        · simp only [Except.ok.injEq] at h
          exact absurd h (by simp)
        · simp only [Except.ok.injEq, Signal.next.injEq] at h
          subst h
          unfold resumeAfterCall
          rw [replaceStackAndIncrPC_pc, Lir.V2.charge_pc he2,
            Lir.V2.charge_pc he1]
          rfl

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **`createArm` `.next` (fallback) preserves the execution environment and presence at every
`a`.** Both fallback arms resume via `resumeAfterCreate failed pending`, whose `.exec.accounts =
failed.accounts = exec.accounts` and whose `.exec.executionEnv` is the suspended caller's
(`pending.frame.exec = exec`, env untouched by the resume). -/
theorem createArm_next_accMono
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      f.exec.executionEnv = exec.executionEnv
        ∧ ∀ a, AccPresent a exec.accounts → AccPresent a f.exec.accounts := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp)
    · simp only [Except.ok.injEq] at hf
      rw [← hf]
      refine ⟨rfl, fun a hp => ?_⟩
      -- resumed `.exec.accounts = result.accounts = exec.accounts`.
      show AccPresent a (ExecutionState.replaceStackAndIncrPC _ _ _).accounts
      rw [replaceStackAndIncrPC_accounts]
      exact hp
  split at h
  · -- nonce-overflow fallback
    revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · -- successful guard: `.needsCreate`, contradiction with `.next`
      simp only [Except.ok.injEq] at h; exact absurd h (by simp)
    · -- funds/depth/size fallback
      revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-- `createArm` `.next` is a fallback arm and resumes after the CREATE/CREATE2 byte. -/
theorem createArm_next_pc
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      f.exec.pc = exec.pc + 1 := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp)
    · simp only [Except.ok.injEq] at hf
      rw [← hf, replaceStackAndIncrPC_pc]
      change exec.pc + 1 = exec.pc + 1
      rfl
  split at h
  · revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · simp only [Except.ok.injEq] at h
      exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-- `createArm` `.next` (the soft-fail fallback) resumes with the residual operand stack plus the
pushed `0` (the `resumeAfterCreate failed` `pushedValue`, which is `0` because `failed.success =
false`). The residual `stack` is the operand-block residual the `systemOp` `pop4` handed in. -/
theorem createArm_next_stack
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec'.stack = stack.push 0 := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      f.exec.stack = stack.push 0 := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp)
    · simp only [Except.ok.injEq] at hf
      rw [← hf]
      -- `pushedValue = 0` because `failed.success = false`; `replaceStackAndIncrPC` sets the stack.
      rfl
  split at h
  · revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · simp only [Except.ok.injEq] at h
      exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-- `createArm` `.next` (the soft-fail fallback) keeps the suspended frame's memory bytes: the
resume rebuilds `exec` touching only accounts/substate/gas/activeWords/returnData, and
`replaceStackAndIncrPC` touches only stack/pc. -/
theorem createArm_next_memory
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec'.toMachineState.memory = exec.toMachineState.memory := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      f.exec.toMachineState.memory = exec.toMachineState.memory := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp)
    · simp only [Except.ok.injEq] at hf
      rw [← hf]
      rfl
  split at h
  · revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · simp only [Except.ok.injEq] at h
      exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-- `createArm` `.next` (the soft-fail fallback) keeps the accounts map: the resume installs
`failed.accounts = exec.accounts` (the pre-op map, NO nonce bump), and `replaceStackAndIncrPC` never
touches accounts. So the resumed self-storage lens reads `exec`'s. -/
theorem createArm_next_accounts
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec'.accounts = exec.accounts := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      f.exec.accounts = exec.accounts := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp)
    · simp only [Except.ok.injEq] at hf
      rw [← hf]
      rfl
  split at h
  · revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · simp only [Except.ok.injEq] at h
      exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-- `MachineState.M s f l` dominates its base `s` (`l = 0` is `s`; else `max s _`). -/
theorem M_ge_left (s f l : UInt64) : s.toNat ≤ (MachineState.M s f l).toNat := by
  unfold MachineState.M
  split
  · exact le_refl _
  · rw [show (s ⊔ ((f + l + 31) / 32))
          = (if s ≤ (f + l + 31) / 32 then (f + l + 31) / 32 else s) from rfl]
    split
    · rename_i h; rwa [UInt64.le_iff_toNat_le] at h
    · exact le_refl _

/-- `createArm` `.next` (the soft-fail fallback) dominates the suspended frame's `activeWords`: the
resume sets `activeWords := M exec.activeWords pd.initOffset pd.initSize`, which is `≥ exec.activeWords`
(`M_ge_left`). -/
theorem createArm_next_activeWords_ge
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec')) :
    exec.toMachineState.activeWords.toNat ≤ exec'.toMachineState.activeWords.toNat := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      exec.toMachineState.activeWords.toNat ≤ f.exec.toMachineState.activeWords.toNat := by
    intro f hf
    unfold resumeAfterCreate at hf
    simp only [bind, Except.bind, pure, Except.pure] at hf
    split at hf
    · exact absurd hf (by simp)
    · simp only [Except.ok.injEq] at hf
      rw [← hf]
      show exec.toMachineState.activeWords.toNat
        ≤ (MachineState.M exec.toMachineState.activeWords initOffset.toUInt64 initSize.toUInt64).toNat
      exact M_ge_left _ _ _
  split at h
  · revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · simp only [Except.ok.injEq] at h
      exact absurd h (by simp)
    · revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **A `.next` System op preserves the execution environment and presence at every `a`.** Halt ops
never `.next`; CALL family reduces to `callArm`; CREATE/CREATE2 reduce to `createArm` on the charged
state (charges accounts/env-verbatim). -/
theorem systemOp_next_accMono {op : Operation.SystemOp} {fr : Frame} {exec exec' : ExecutionState}
    (h : systemOp op fr exec = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h)
      (BytecodeLayer.System.haltOp_not_next' (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
      BytecodeLayer.System.systemOp_callArm_reduce (by tauto) h
    exact callArm_next_accMono hc
  | CREATE =>
    unfold systemOp at h
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hpop : exec.stack.pop3 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              obtain ⟨henv, hmono⟩ := createArm_next_accMono h
              refine ⟨?_, fun a hp => ?_⟩
              · rw [henv, hcenv, hmenv]
              · exact hmono a (accMono_of_accounts_eq a (by rw [hcacc, hmacc]) hp)
  | CREATE2 =>
    unfold systemOp at h
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hpop : exec.stack.pop4 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              obtain ⟨henv, hmono⟩ := createArm_next_accMono h
              refine ⟨?_, fun a hp => ?_⟩
              · rw [henv, hcenv, hmenv]
              · exact hmono a (accMono_of_accounts_eq a (by rw [hcacc, hmacc]) hp)

/-- A `.next` CREATE-family `systemOp` is a fallback arm and advances past the opcode byte. -/
theorem systemOp_next_create_pc {op : Operation.SystemOp} {fr : Frame}
    {exec exec' : ExecutionState}
    (hop : op = .CREATE ∨ op = .CREATE2)
    (h : systemOp op fr exec = .ok (.next exec')) :
    exec'.pc = exec.pc + 1 := by
  rcases hop with rfl | rfl
  · unfold systemOp at h
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h
      simp only [] at h
      cases hp : exec.stack.pop3 with
      | none =>
        rw [hp] at h
        simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v
        rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e =>
            rw [hm] at h
            simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h
            simp only [pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h
              simp only [] at h
              have hpc' := createArm_next_pc h
              rw [hpc', Lir.V2.charge_pc hc, Lir.V2.chargeMemExpansion_pc hm]
  · unfold systemOp at h
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h
      simp only [] at h
      cases hp : exec.stack.pop4 with
      | none =>
        rw [hp] at h
        simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v
        rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e =>
            rw [hm] at h
            simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h
            simp only [pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h
              simp only [] at h
              have hpc' := createArm_next_pc h
              rw [hpc', Lir.V2.charge_pc hc, Lir.V2.chargeMemExpansion_pc hm]

/-- **A `.next` CREATE2 `systemOp` resumes with the operand residual plus the pushed `0`.** The
`pop4` residual `s` of the original stack is the createArm residual (charging never touches the
stack), and the soft-fail push is `0`. -/
theorem systemOp_next_create2_stack {fr : Frame} {exec exec' : ExecutionState}
    (h : systemOp .CREATE2 fr exec = .ok (.next exec')) :
    ∃ residual value initOffset initSize salt,
      exec.stack.pop4 = some (residual, value, initOffset, initSize, salt)
      ∧ exec'.stack = residual.push 0 := by
  unfold systemOp at h
  simp only [bind, Except.bind] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h
    simp only [] at h
    cases hpop : exec.stack.pop4 with
    | none =>
      rw [hpop] at h
      simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, val, io, is, salt⟩ := v
      rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      split at h
      · simp at h
      · cases hm : chargeMemExpansion exec io is with
        | error e => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h
          simp only [pure, Except.pure] at h
          cases hc : charge (create2Cost is) em with
          | error e => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h
            simp only [] at h
            exact ⟨s, val, io, is, salt, rfl, createArm_next_stack h⟩

/-- **A `.next` CREATE2 `systemOp` keeps the memory bytes.** Charging preserves the byte-map, and the
soft-fail resume never writes memory. -/
theorem systemOp_next_create2_memory {fr : Frame} {exec exec' : ExecutionState}
    (h : systemOp .CREATE2 fr exec = .ok (.next exec')) :
    exec'.toMachineState.memory = exec.toMachineState.memory := by
  unfold systemOp at h
  simp only [bind, Except.bind] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h
    simp only [] at h
    cases hpop : exec.stack.pop4 with
    | none =>
      rw [hpop] at h
      simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, val, io, is, salt⟩ := v
      rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      split at h
      · simp at h
      · cases hm : chargeMemExpansion exec io is with
        | error e => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h
          simp only [pure, Except.pure] at h
          cases hc : charge (create2Cost is) em with
          | error e => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h
            simp only [] at h
            rw [createArm_next_memory h, Lir.V2.charge_memory hc,
              Lir.V2.chargeMemExpansion_memory hm]

/-- **A `.next` CREATE2 `systemOp` keeps the accounts map.** Charging preserves accounts, and the
soft-fail resume installs the pre-op (un-bumped) map. -/
theorem systemOp_next_create2_accounts {fr : Frame} {exec exec' : ExecutionState}
    (h : systemOp .CREATE2 fr exec = .ok (.next exec')) :
    exec'.accounts = exec.accounts := by
  unfold systemOp at h
  simp only [bind, Except.bind] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h
    simp only [] at h
    cases hpop : exec.stack.pop4 with
    | none =>
      rw [hpop] at h
      simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, val, io, is, salt⟩ := v
      rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      split at h
      · simp at h
      · cases hm : chargeMemExpansion exec io is with
        | error e => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h
          simp only [pure, Except.pure] at h
          cases hc : charge (create2Cost is) em with
          | error e => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h
            simp only [] at h
            rw [createArm_next_accounts h, (Lir.V2.charge_accounts_env hc).1,
              (Lir.V2.chargeMemExpansion_accounts_env hm).1]

/-- **A `.next` CREATE2 `systemOp` dominates the frame's `activeWords`.** Charging never mutates
`activeWords`, and the soft-fail resume grows it to `M`. -/
theorem systemOp_next_create2_activeWords_ge {fr : Frame} {exec exec' : ExecutionState}
    (h : systemOp .CREATE2 fr exec = .ok (.next exec')) :
    exec.toMachineState.activeWords.toNat ≤ exec'.toMachineState.activeWords.toNat := by
  unfold systemOp at h
  simp only [bind, Except.bind] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h
    simp only [] at h
    cases hpop : exec.stack.pop4 with
    | none =>
      rw [hpop] at h
      simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨s, val, io, is, salt⟩ := v
      rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      split at h
      · simp at h
      · cases hm : chargeMemExpansion exec io is with
        | error e => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h
          simp only [pure, Except.pure] at h
          cases hc : charge (create2Cost is) em with
          | error e => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h
            simp only [] at h
            have hge := createArm_next_activeWords_ge h
            rwa [Lir.V2.charge_activeWords hc, Lir.V2.chargeMemExpansion_activeWords hm] at hge

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **A `.next` `smsfOp` preserves the execution environment and presence at every `a`.**
Memory/stack/flow arms are accounts/env-verbatim; SLOAD/TLOAD are `unStateOp` read-only on
accounts/env; SSTORE/TSTORE write at the self key (insert-mono), env untouched. -/
theorem smsfOp_next_accMono {op : Operation.SmsfOp} {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp op fr exec = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold smsfOp at h
  cases op with
  | POP =>
    simp only [bind, Except.bind] at h
    cases hc : charge Gbase exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      cases hpop : ec.stack.pop with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨st, x⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)
  | MLOAD =>
    simp only [bind, Except.bind] at h
    cases hpop : exec.stack.pop with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, addr⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec addr 32 with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge Gverylow em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
          exact ⟨show ec.executionEnv = exec.executionEnv by rw [hcenv, hmenv],
            fun a hp => accMono_replaceOfBase _ _
              (show ec.accounts = exec.accounts by rw [hcacc, hmacc]) hp⟩
  | MSTORE =>
    simp only [bind, Except.bind] at h
    cases hpop : exec.stack.pop2 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, addr, val⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec addr 32 with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge Gverylow em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
          exact ⟨show ec.executionEnv = exec.executionEnv by rw [hcenv, hmenv],
            fun a hp => accMono_replaceOfBase _ _
              (show ec.accounts = exec.accounts by rw [hcacc, hmacc]) hp⟩
  | MSTORE8 =>
    simp only [bind, Except.bind] at h
    cases hpop : exec.stack.pop2 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, addr, val⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec addr 1 with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge Gverylow em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
          exact ⟨show ec.executionEnv = exec.executionEnv by rw [hcenv, hmenv],
            fun a hp => accMono_replaceOfBase _ _
              (show ec.accounts = exec.accounts by rw [hcacc, hmacc]) hp⟩
  | SLOAD =>
    refine unStateOp_next_accMono ?_ h
    intro st x; exact ⟨rfl, rfl⟩
  | SSTORE =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      split at h
      · simp at h
      · cases hpop : exec.stack.pop2 with
        | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        | some v =>
          obtain ⟨st, key, newVal⟩ := v; rw [hpop] at h
          simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
          exact charge_sstore_next_accMono h
  | TLOAD =>
    refine unStateOp_next_accMono ?_ h
    intro st x; exact ⟨rfl, rfl⟩
  | TSTORE =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hc : charge tstoreCost exec with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        cases hpop : ec.stack.pop2 with
        | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        | some v =>
          obtain ⟨st, key, val⟩ := v; rw [hpop] at h
          simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
          rw [continueWith_next h]
          obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
          have henvs : (ec.toState.tstore key val).executionEnv = ec.toState.executionEnv := by
            unfold State.tstore
            simp only [State.lookupAccount, Option.option]
            cases hf : ec.toState.accounts.find? ec.toState.executionEnv.address with
            | none => rfl
            | some acc => rfl
          refine ⟨?_, fun a hp => ?_⟩
          · show (ec.toState.tstore key val).executionEnv = exec.executionEnv
            rw [henvs]
            exact hcenv
          · rw [replaceStackAndIncrPC_accounts]
            show AccPresent a (ec.toState.tstore key val).accounts
            refine tstore_accMono ec.toState key val a ?_
            exact accMono_of_accounts_eq a hcacc hp
  | MSIZE => exact pushOp_next_accMono h
  | GAS => exact pushOp_next_accMono h
  | PC => exact pushOp_next_accMono h
  | JUMP =>
    simp only [bind, Except.bind] at h
    cases hc : charge Gmid exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      cases hpop : ec.stack.pop with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨st, dest⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
        cases hd : fr.get_dest dest with
        | none => rw [hd] at h; simp at h
        | some newpc =>
          rw [hd] at h; simp only [] at h
          rw [continueWith_next h]
          exact ⟨hcenv, fun a hp => accMono_of_accounts_eq a hcacc hp⟩
  | JUMPI =>
    simp only [bind, Except.bind] at h
    cases hc : charge Ghigh exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      cases hpop : ec.stack.pop2 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨st, dest, cond⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
        split at h
        · cases hd : fr.get_dest dest with
          | none => rw [hd] at h; simp at h
          | some newpc =>
            rw [hd] at h; simp only [] at h
            rw [continueWith_next h]
            exact ⟨hcenv, fun a hp => accMono_of_accounts_eq a hcacc hp⟩
        · rw [continueWith_next h]
          exact ⟨hcenv, fun a hp => accMono_of_accounts_eq a hcacc hp⟩
  | JUMPDEST =>
    simp only [bind, Except.bind] at h
    cases hc : charge Gjumpdest exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      rw [continueWith_next h]
      obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
      exact ⟨hcenv, fun a hp => accMono_of_accounts_eq a hcacc hp⟩
  | MCOPY =>
    simp only [bind, Except.bind] at h
    cases hpop : exec.stack.pop3 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, dest, src, sz⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec (max dest src) sz with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge (Gverylow + copyCost sz) em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
          exact ⟨show ec.executionEnv = exec.executionEnv by rw [hcenv, hmenv],
            fun a hp => accMono_replaceOfBase _ _
              (show ec.accounts = exec.accounts by rw [hcacc, hmacc]) hp⟩

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **`dispatch` `.next` preserves the execution environment and presence at every `a` (engine
level).** The one dispatch walk: every `.next`-producing opcode keeps `executionEnv` fixed and
account-presence monotone at every tracked address. -/
theorem dispatch_next_accMono {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec exec' : ExecutionState}
    (h : dispatch op arg fr exec = .ok (.next exec')) :
    exec'.executionEnv = exec.executionEnv
      ∧ ∀ a, AccPresent a exec.accounts → AccPresent a exec'.accounts := by
  unfold dispatch at h
  cases op with
  | System s => exact systemOp_next_accMono h
  | Smsf s => exact smsfOp_next_accMono h
  | KECCAK256 =>
    simp only [bind, Except.bind] at h
    cases hpop : exec.stack.pop2 with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, off, sz⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off sz with
      | error er => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge (keccakCost sz) em with
        | error er => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
          exact ⟨show ec.executionEnv = exec.executionEnv by rw [hcenv, hmenv],
            fun a hp => accMono_replaceOfBase _ _
              (show ec.accounts = exec.accounts by rw [hcacc, hmacc]) hp⟩
  | ArithLogic ar =>
    cases ar with
    | ADD | SUB | SIGNEXTEND | LT | GT | SLT | SGT | EQ | AND | OR | XOR | BYTE | SHL | SHR | SAR
    | MUL | DIV | SDIV | MOD | SMOD => exact binOp_next_accMono h
    | ADDMOD | MULMOD => exact ternOp_next_accMono h
    | ISZERO | NOT => exact unOp_next_accMono h
    | EXP =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop2 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, b, e⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge (expCost e) exec with
        | error er => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)
  | Env e =>
    cases e with
    | ADDRESS | ORIGIN | CALLER | CALLVALUE | CALLDATASIZE | CODESIZE | GASPRICE | RETURNDATASIZE =>
      exact pushOp_next_accMono h
    | BALANCE => exact unStateOp_next_accMono (fun _ _ => ⟨rfl, rfl⟩) h
    | CALLDATALOAD => exact unStateOp_next_accMono (fun _ _ => ⟨rfl, rfl⟩) h
    | EXTCODESIZE => exact unStateOp_next_accMono (fun _ _ => ⟨rfl, rfl⟩) h
    | EXTCODEHASH =>
      refine unStateOp_next_accMono ?_ h
      intro st x
      show (State.extCodeHash st x).1.accounts = st.accounts
        ∧ (State.extCodeHash st x).1.executionEnv = st.executionEnv
      unfold State.extCodeHash
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    | CALLDATACOPY =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop3 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, x, y, z⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hm : chargeMemExpansion exec x z with
        | error er => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h; simp only [pure, Except.pure] at h
          cases hc : charge (Gverylow + copyCost z) em with
          | error er => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h; simp only [] at h
            rw [continueWith_next h]
            obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
            obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
            refine ⟨?_, fun a hp => ?_⟩
            · show (ec.calldatacopy x y z).executionEnv = exec.executionEnv
              show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
            · refine accMono_of_accounts_eq a ?_ hp
              show (ec.calldatacopy x y z).accounts = exec.accounts
              show ec.accounts = exec.accounts; rw [hcacc, hmacc]
    | CODECOPY =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop3 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, x, y, z⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hm : chargeMemExpansion exec x z with
        | error er => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h; simp only [pure, Except.pure] at h
          cases hc : charge (Gverylow + copyCost z) em with
          | error er => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h; simp only [] at h
            rw [continueWith_next h]
            obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
            obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
            refine ⟨?_, fun a hp => ?_⟩
            · show (ec.codeCopy x y z).executionEnv = exec.executionEnv
              show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
            · refine accMono_of_accounts_eq a ?_ hp
              show (ec.codeCopy x y z).accounts = exec.accounts
              show ec.accounts = exec.accounts; rw [hcacc, hmacc]
    | EXTCODECOPY =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop4 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, addr, x, y, z⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hm : chargeMemExpansion exec x z with
        | error er => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h; simp only [pure, Except.pure] at h
          cases hc : charge (accessCost (AccountAddress.ofUInt256 addr) em.substate + copyCost z) em with
          | error er => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h; simp only [] at h
            rw [continueWith_next h]
            obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
            obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
            refine ⟨?_, fun a hp => ?_⟩
            · show (ec.extCodeCopy' addr x y z).executionEnv = exec.executionEnv
              show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
            · refine accMono_of_accounts_eq a ?_ hp
              show (ec.extCodeCopy' addr x y z).accounts = exec.accounts
              show ec.accounts = exec.accounts; rw [hcacc, hmacc]
    | RETURNDATACOPY =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop3 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, x, y, z⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec x z with
          | error er => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (Gverylow + copyCost z) em with
            | error er => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              rw [continueWith_next h]
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              exact ⟨show ec.executionEnv = exec.executionEnv by rw [hcenv, hmenv],
                fun a hp => accMono_replaceOfBase _ _
                  (show ec.accounts = exec.accounts by rw [hcacc, hmacc]) hp⟩
  | Block b =>
    cases b with
    | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO | GASLIMIT | CHAINID | SELFBALANCE | BASEFEE
    | BLOBBASEFEE => exact pushOp_next_accMono h
    | BLOCKHASH => exact unStateOp_next_accMono (fun _ _ => ⟨rfl, rfl⟩) h
    | BLOBHASH =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, i⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge HASH_OPCODE_GAS exec with
        | error er => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_next_accMono h
    | _ =>
      simp only [bind, Except.bind] at h
      cases hc : charge Gverylow exec with
      | error er => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        cases harg : arg with
        | none => rw [harg] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
        | some w =>
          obtain ⟨av, aw⟩ := w; rw [harg] at h
          simp only [] at h
          exact dispatch_simple_arm_next_accMono hc rfl rfl (continueWith_next h)
  | Dup d => exact dup_next_accMono h
  | Swap s => exact swap_next_accMono h
  | Log l =>
    cases l with
    | LOG0 =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop2 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_accMono h
    | LOG1 =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop3 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_accMono h
    | LOG2 =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop4 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1, t2⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_accMono h
    | LOG3 =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop5 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1, t2, t3⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_accMono h
    | LOG4 =>
      simp only [bind, Except.bind] at h
      cases hpop : exec.stack.pop6 with
      | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1, t2, t3, t4⟩ := v; rw [hpop] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_accMono h

/-- **A `.next` `stepFrame` preserves the execution environment.** `stepFrame` decodes, screens
`INVALID`/stack-overflow (both `.halted`, never `.next`), then forwards to `dispatch`; a `.next`
is exactly a `dispatch … = .ok (.next exec')`, whose env half is the walk's first conjunct. The
full-`executionEnv` equality is strictly stronger than the address projection the SelfAt
transport needs. -/
theorem stepFrame_next_execEnvAddr {fr : Frame} {exec' : ExecutionState}
    (h : stepFrame fr = .next exec') : exec'.executionEnv = fr.exec.executionEnv := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp
    at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases hdisp : dispatch op arg fr fr.exec with
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e =>
          simp only [Signal.next.injEq] at h; subst h
          exact (dispatch_next_accMono hdisp).1
        | halted hl => simp only at h; exact absurd h (by simp)
        | needsCall p pc => simp only at h; exact absurd h (by simp)
        | needsCreate p pc => simp only at h; exact absurd h (by simp)
      | error e => rw [hdisp] at h; exact absurd h (by simp)

open Lir.V2 (AccPresent) in
/-- **A `.next` `stepFrame` preserves presence at an arbitrary `a` (Brick C / `hmono`).** The
presence half of the dispatch walk; the deliverable consumed at `callPreservesSelf`'s
`hmono` slot. -/
theorem stepFrame_next_accMono {fr : Frame} {exec' : ExecutionState}
    (h : stepFrame fr = .next exec') (a : AccountAddress) (hp : AccPresent a fr.exec.accounts) :
    AccPresent a exec'.accounts := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp
    at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases hdisp : dispatch op arg fr fr.exec with
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e =>
          simp only [Signal.next.injEq] at h; subst h
          exact (dispatch_next_accMono hdisp).2 a hp
        | halted hl => simp only at h; exact absurd h (by simp)
        | needsCall p pc => simp only at h; exact absurd h (by simp)
        | needsCreate p pc => simp only at h; exact absurd h (by simp)
      | error e => rw [hdisp] at h; exact absurd h (by simp)

open Lir.V2 (SelfAt) in
/-- **A `.next` `stepFrame` preserves self-presence (the engine-level `StepPreservesSelf` brick).**
The `a := self` corollary of the dispatch walk: presence at the (fixed) caller self address
transports by `stepFrame_next_accMono`, and the self address itself is preserved by
`stepFrame_next_execEnvAddr`. -/
theorem stepFrame_next_self {fr : Frame} {exec' : ExecutionState}
    (h : stepFrame fr = .next exec') (hself : SelfAt fr.exec) : SelfAt exec' := by
  obtain ⟨acc, ha⟩ := hself
  obtain ⟨acc', ha'⟩ := stepFrame_next_accMono h fr.exec.executionEnv.address ⟨acc, ha⟩
  exact ⟨acc', by rw [stepFrame_next_execEnvAddr h]; exact ha'⟩

/-- A decoded `JUMPDEST` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_jumpdest_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.JUMPDEST, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .JUMPDEST) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch, smsfOp] at hstep
    simp only [bind, Except.bind] at hstep
    cases hc : charge Gjumpdest fr.exec with
    | error e =>
        rw [hc] at hstep
        simp at hstep
    | ok ec =>
        rw [hc] at hstep
        simp only [] at hstep
        unfold continueWith at hstep
        simp only [Signal.next.injEq] at hstep
        rw [← hstep, ExecutionState.incrPC]
        have hcp := Lir.V2.charge_pc hc
        rw [hpc] at hcp
        rw [hcp, nextInstrPosNat]
        simp [pushArgWidth]

/-- A decoded `POP` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_pop_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.POP, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .POP) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hs : smsfOp .POP fr fr.exec with
    | error e => rw [hs] at hstep; simp at hstep
    | ok signal =>
      rw [hs] at hstep
      cases signal with
      | next e =>
        simp only [Signal.next.injEq] at hstep
        subst hstep
        have hpc' := smsf_pop_next_pc hs
        rw [hpc] at hpc'
        rw [hpc', nextInstrPosNat]
        simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `MLOAD` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_mload_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.MLOAD, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .MLOAD) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hs : smsfOp .MLOAD fr fr.exec with
    | error e => rw [hs] at hstep; simp at hstep
    | ok signal =>
      rw [hs] at hstep
      cases signal with
      | next e =>
        simp only [Signal.next.injEq] at hstep
        subst hstep
        have hpc' := smsf_mload_next_pc hs
        rw [hpc] at hpc'
        rw [hpc', nextInstrPosNat]
        simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `MSTORE` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_mstore_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.MSTORE, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .MSTORE) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hs : smsfOp .MSTORE fr fr.exec with
    | error e => rw [hs] at hstep; simp at hstep
    | ok signal =>
      rw [hs] at hstep
      cases signal with
      | next e =>
        simp only [Signal.next.injEq] at hstep
        subst hstep
        have hpc' := smsf_mstore_next_pc hs
        rw [hpc] at hpc'
        rw [hpc', nextInstrPosNat]
        simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `SLOAD` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_sload_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.SLOAD, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .SLOAD) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hs : smsfOp .SLOAD fr fr.exec with
    | error e => rw [hs] at hstep; simp at hstep
    | ok signal =>
      rw [hs] at hstep
      cases signal with
      | next e =>
        simp only [Signal.next.injEq] at hstep
        subst hstep
        have hpc' := smsf_sload_next_pc hs
        rw [hpc] at hpc'
        rw [hpc', nextInstrPosNat]
        simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `SSTORE` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_sstore_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.SSTORE, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .SSTORE) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hs : smsfOp .SSTORE fr fr.exec with
    | error e => rw [hs] at hstep; simp at hstep
    | ok signal =>
      rw [hs] at hstep
      cases signal with
      | next e =>
        simp only [Signal.next.injEq] at hstep
        subst hstep
        have hpc' := smsf_sstore_next_pc hs
        rw [hpc] at hpc'
        rw [hpc', nextInstrPosNat]
        simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `GAS` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_gas_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.GAS, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .GAS) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hs : smsfOp .GAS fr fr.exec with
    | error e => rw [hs] at hstep; simp at hstep
    | ok signal =>
      rw [hs] at hstep
      cases signal with
      | next e =>
        simp only [Signal.next.injEq] at hstep
        subst hstep
        have hpc' := smsf_gas_next_pc hs
        rw [hpc] at hpc'
        rw [hpc', nextInstrPosNat]
        simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `JUMP` `.next` step lands in the frame's valid jump table. -/
theorem stepFrame_next_jump_pc {fr : Frame} {exec' : ExecutionState}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.JUMP, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc ∈ fr.validJumps := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch, smsfOp] at hstep
    simp only [bind, Except.bind] at hstep
    cases hc : charge Gmid fr.exec with
    | error e => rw [hc] at hstep; simp at hstep
    | ok ec =>
      rw [hc] at hstep; simp only [] at hstep
      cases hpop : ec.stack.pop with
      | none => rw [hpop] at hstep; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at hstep
      | some v =>
        obtain ⟨stk, dest⟩ := v; rw [hpop] at hstep
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at hstep
        cases hd : fr.get_dest dest with
        | none => rw [hd] at hstep; simp at hstep
        | some newpc =>
          rw [hd] at hstep; simp only [] at hstep
          unfold continueWith at hstep
          simp only [Signal.next.injEq] at hstep
          rw [← hstep]
          exact Frame.get_dest_some_mem hd

/-- A decoded `JUMPI` `.next` step either falls through or lands in the valid jump table. -/
theorem stepFrame_next_jumpi_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.JUMPI, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .JUMPI) ∨ exec'.pc ∈ fr.validJumps := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch, smsfOp] at hstep
    simp only [bind, Except.bind] at hstep
    cases hc : charge Ghigh fr.exec with
    | error e => rw [hc] at hstep; simp at hstep
    | ok ec =>
      rw [hc] at hstep; simp only [] at hstep
      cases hpop : ec.stack.pop2 with
      | none => rw [hpop] at hstep; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at hstep
      | some v =>
        obtain ⟨stk, dest, cond⟩ := v; rw [hpop] at hstep
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at hstep
        cases hcond : (cond != 0) with
        | false =>
          rw [hcond] at hstep
          simp only [Bool.false_eq_true, ↓reduceIte] at hstep
          unfold continueWith at hstep
          simp only [Signal.next.injEq] at hstep
          subst hstep
          left
          have hcp := Lir.V2.charge_pc hc
          rw [hpc] at hcp
          rw [hcp, nextInstrPosNat]
          simp [pushArgWidth]
        | true =>
          rw [hcond] at hstep
          simp only [↓reduceIte] at hstep
          cases hd : fr.get_dest dest with
          | none => rw [hd] at hstep; simp at hstep
          | some newpc =>
            rw [hd] at hstep; simp only [] at hstep
            unfold continueWith at hstep
            simp only [Signal.next.injEq] at hstep
            subst hstep
            right
            exact Frame.get_dest_some_mem hd

/-- A decoded `ADD` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_add_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ADD, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .ADD) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hb : binOp UInt256.add fr.exec with
    | error e => rw [hb] at hstep; simp at hstep
    | ok signal =>
        rw [hb] at hstep
        cases signal with
        | next e =>
            simp only [Signal.next.injEq] at hstep
            subst hstep
            have hpc' := binOp_next_pc hb
            rw [hpc] at hpc'
            rw [hpc', nextInstrPosNat]
            simp [pushArgWidth]
        | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

/-- A decoded `LT` `.next` step advances to the next sequential instruction. -/
theorem stepFrame_next_lt_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.LT, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .LT) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hb : binOp UInt256.lt fr.exec with
    | error e => rw [hb] at hstep; simp at hstep
    | ok signal =>
        rw [hb] at hstep
        cases signal with
        | next e =>
            simp only [Signal.next.injEq] at hstep
            subst hstep
            have hpc' := binOp_next_pc hb
            rw [hpc] at hpc'
            rw [hpc', nextInstrPosNat]
            simp [pushArgWidth]
        | halted hl | needsCall p pc | needsCreate p pc => simp at hstep

theorem decode_push_width {code : ByteArray} {pc : UInt32} {p : Operation.PushOp}
    {imm : UInt256} {w : UInt8}
    (hdec : decode code pc = some (.Push p, some (imm, w))) :
    w = pushArgWidth (.Push p) := by
  unfold decode at hdec
  simp only [bind, Option.bind] at hdec
  cases hget : code.get? pc.toNat with
  | none =>
      rw [hget] at hdec
      simp at hdec
  | some byte =>
      rw [hget] at hdec
      simp only at hdec
      split at hdec
      · simp only [Option.some.injEq, Prod.mk.injEq] at hdec
        have hw := hdec.2.2.symm
        rw [hdec.1] at hw
        exact hw
      · simp at hdec

/-- A decoded `PUSH4` `.next` step advances by its opcode byte plus four immediate bytes. -/
theorem stepFrame_next_push4_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    {imm : UInt256}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH4, some (imm, 4)))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b (.Push .PUSH4)) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · dsimp only [dispatch] at hstep
    simp only [bind, Except.bind] at hstep
    cases hc : charge Gverylow fr.exec with
    | error e =>
        rw [hc] at hstep
        simp at hstep
    | ok ec =>
        rw [hc] at hstep
        simp only at hstep
        unfold continueWith at hstep
        simp only [Signal.next.injEq] at hstep
        rw [← hstep, ExecutionState.replaceStackAndIncrPC]
        have hcp := Lir.V2.charge_pc hc
        rw [hpc] at hcp
        rw [hcp, nextInstrPosNat]
        simpa [pushArgWidth, show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide,
          show UInt8.toNat (4 : UInt8) = 4 from rfl, show b + 1 + 4 = b + 5 by omega]
          using (UInt32.ofNat_add b 5)

/-- A decoded `PUSH32` `.next` step advances by its opcode byte plus 32 immediate bytes. -/
theorem stepFrame_next_push32_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    {imm : UInt256}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (imm, 32)))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b (.Push .PUSH32)) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [reduceCtorEq, ↓reduceIte] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · dsimp only [dispatch] at hstep
    simp only [bind, Except.bind] at hstep
    cases hc : charge Gverylow fr.exec with
    | error e =>
        rw [hc] at hstep
        simp at hstep
    | ok ec =>
        rw [hc] at hstep
        simp only at hstep
        unfold continueWith at hstep
        simp only [Signal.next.injEq] at hstep
        rw [← hstep, ExecutionState.replaceStackAndIncrPC]
        have hcp := Lir.V2.charge_pc hc
        rw [hpc] at hcp
        rw [hcp, nextInstrPosNat]
        simpa [pushArgWidth, show ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 from by decide,
          show UInt8.toNat (32 : UInt8) = 32 from rfl, show b + 1 + 32 = b + 33 by omega]
          using (UInt32.ofNat_add b 33)

/-- A decoded `CALL` `.next` step is the fallback arm and advances past the CALL byte. -/
theorem stepFrame_next_call_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.CALL, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .CALL) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hsys : systemOp .CALL fr fr.exec with
    | error e =>
      rw [hsys] at hstep
      split at hstep <;> simp at hstep
    | ok signal =>
      rw [hsys] at hstep
      cases signal with
      | next e =>
        split at hstep
        · simp at hstep
        · simp only [Signal.next.injEq] at hstep
          subst hstep
          obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
            BytecodeLayer.System.systemOp_callArm_reduce (by tauto) hsys
          have hpc' := callArm_next_pc hc
          rw [hpc] at hpc'
          rw [hpc', nextInstrPosNat]
          simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc =>
        split at hstep <;> simp at hstep

/-- A decoded `CREATE` `.next` step is a fallback arm and advances past the CREATE byte. -/
theorem stepFrame_next_create_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.CREATE, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .CREATE) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hsys : systemOp .CREATE fr fr.exec with
    | error e =>
      rw [hsys] at hstep
      split at hstep <;> simp at hstep
    | ok signal =>
      rw [hsys] at hstep
      cases signal with
      | next e =>
        split at hstep
        · simp at hstep
        · simp only [Signal.next.injEq] at hstep
          subst hstep
          have hpc' := systemOp_next_create_pc (op := .CREATE) (by tauto) hsys
          rw [hpc] at hpc'
          rw [hpc', nextInstrPosNat]
          simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc =>
        split at hstep <;> simp at hstep

/-- A decoded `CREATE2` `.next` step is a fallback arm and advances past the CREATE2 byte. -/
theorem stepFrame_next_create2_pc {fr : Frame} {exec' : ExecutionState} {b : Nat}
    (hpc : fr.exec.pc = UInt32.ofNat b)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.CREATE2, .none))
    (hstep : stepFrame fr = .next exec') :
    exec'.pc = UInt32.ofNat (nextInstrPosNat b .CREATE2) := by
  rw [stepFrame] at hstep
  rw [hdec] at hstep
  simp only [Option.getD_some] at hstep
  simp only [stackPopCount, stackPushCount] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · rw [dispatch] at hstep
    cases hsys : systemOp .CREATE2 fr fr.exec with
    | error e =>
      rw [hsys] at hstep
      split at hstep <;> simp at hstep
    | ok signal =>
      rw [hsys] at hstep
      cases signal with
      | next e =>
        split at hstep
        · simp at hstep
        · simp only [Signal.next.injEq] at hstep
          subst hstep
          have hpc' := systemOp_next_create_pc (op := .CREATE2) (by tauto) hsys
          rw [hpc] at hpc'
          rw [hpc', nextInstrPosNat]
          simp [pushArgWidth]
      | halted hl | needsCall p pc | needsCreate p pc =>
        split at hstep <;> simp at hstep

/-! ### Halt-success account-presence (`hhalt`)

A `.halted (.success e o)` from `stepFrame` comes only from `haltOp` (INVALID/overflow screens halt
only with `.exception`; the non-`System` dispatcher arms never halt). The three success-producing
`haltOp` arms keep presence at `a`: STOP (accounts verbatim), RETURN (verbatim through
`chargeMemExpansion`/`replaceStackAndIncrPC`), SELFDESTRUCT (`accountMap'` is verbatim or ≤2 inserts at
the recipient/self — no erase). -/

open Lir.V2 (AccPresent accMono_of_accounts_eq accounts_find?_insert_mono) in
/-- **`selfdestructOp` `.halted .success` preserves presence at `a`.** `accountMap'` is a nested
match whose branches are `exec.accounts` (verbatim) or ≤2 `insert`s (at `r` and `self`); presence at
any `a` survives every branch (`accounts_find?_insert_mono`). No erase. -/
theorem selfdestructOp_success_accMono {exec e : ExecutionState} {o : ByteArray}
    {a : AccountAddress}
    (h : selfdestructOp exec = .ok (.halted (.success e o)))
    (hp : AccPresent a exec.accounts) : AccPresent a e.accounts := by
  unfold selfdestructOp at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hr : requireStateMod exec with
  | error er => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h; simp only [] at h
    cases hpop : exec.stack.pop with
    | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stack, recipientWord⟩ := v; rw [hpop] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      revert h
      generalize hcost : selfdestructCost _ _ = cost
      intro h
      cases hc : charge cost exec with
      | error er => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h
        simp only [Except.ok.injEq, Signal.halted.injEq, FrameHalt.success.injEq] at h
        obtain ⟨he, _⟩ := h
        obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
        -- presence transports through the charge first.
        have hpc : AccPresent a ec.accounts := accMono_of_accounts_eq a hcacc hp
        -- `e = exec'.replaceStackAndIncrPC stack`; reduce `.accounts` to `accountMap'`.
        rw [← he, replaceStackAndIncrPC_accounts]
        -- `exec'.accounts = accountMap'`; case the createdAccounts guard, then the nested matches.
        -- Every leaf is either `ec.accounts` (verbatim) or ≤2 `insert`s; presence at `a` survives.
        dsimp only [Evm.State.lookupAccount]
        split
        all_goals
          cases hself : ec.accounts.find? exec.executionEnv.address with
          | none => simp only [hself, dbgTrace]; exact hpc
          | some selfAccount =>
            simp only [hself]
            cases hrec : ec.accounts.find? (AccountAddress.ofUInt256 recipientWord) with
            | none =>
              simp only [hrec]
              split
              · exact hpc
              · exact accounts_find?_insert_mono _ _ _ _ (accounts_find?_insert_mono _ _ _ _ hpc)
            | some recipientAccount =>
              simp only [hrec]
              split
              · exact accounts_find?_insert_mono _ _ _ _ (accounts_find?_insert_mono _ _ _ _ hpc)
              · first
                | exact accounts_find?_insert_mono _ _ _ _ (accounts_find?_insert_mono _ _ _ _ hpc)
                | exact hpc

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **`returnOrRevertOp` `.halted .success` preserves presence at `a`.** Accounts pass through
`chargeMemExpansion` (verbatim) and `replaceStackAndIncrPC` (verbatim). -/
theorem returnOrRevertOp_success_accMono {op : Operation.SystemOp} {exec e : ExecutionState}
    {o : ByteArray} {a : AccountAddress}
    (h : returnOrRevertOp op exec = .ok (.halted (.success e o)))
    (hp : AccPresent a exec.accounts) : AccPresent a e.accounts := by
  unfold returnOrRevertOp at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hpop : exec.stack.pop2 with
  | none => rw [hpop] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨stack, offset, size⟩ := v; rw [hpop] at h
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hm : chargeMemExpansion exec offset size with
    | error er => rw [hm] at h; simp at h
    | ok em =>
      rw [hm] at h; simp only [] at h
      obtain ⟨hmacc, _⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
      split at h
      · -- REVERT: `.halted (.revert …)`, not `.success`
        simp only [Except.ok.injEq] at h; exact absurd h (by simp)
      · -- RETURN: `.halted (.success exec' output)`; `exec'.accounts = em.accounts = exec.accounts`.
        simp only [Except.ok.injEq, Signal.halted.injEq, FrameHalt.success.injEq] at h
        obtain ⟨he, _⟩ := h
        rw [← he, replaceStackAndIncrPC_accounts]
        show AccPresent a em.accounts
        exact accMono_of_accounts_eq a hmacc hp

open Lir.V2 (AccPresent accMono_of_accounts_eq) in
/-- **`haltOp` `.halted .success` preserves presence at `a`.** STOP keeps accounts verbatim; RETURN
via `returnOrRevertOp_success_accMono`; SELFDESTRUCT via `selfdestructOp_success_accMono`. REVERT/
INVALID never produce `.success`. -/
theorem haltOp_success_accMono {op : Operation.SystemOp} {exec e : ExecutionState} {o : ByteArray}
    {a : AccountAddress}
    (h : haltOp op exec = .ok (.halted (.success e o)))
    (hp : AccPresent a exec.accounts) : AccPresent a e.accounts := by
  unfold haltOp at h
  cases op with
  | STOP =>
    simp only [Except.ok.injEq, Signal.halted.injEq, FrameHalt.success.injEq] at h
    obtain ⟨he, _⟩ := h; rw [← he]; exact hp
  | RETURN => exact returnOrRevertOp_success_accMono h hp
  | REVERT =>
    -- REVERT yields `.halted (.revert …)`, never `.success`.
    exact returnOrRevertOp_success_accMono h hp
  | SELFDESTRUCT => exact selfdestructOp_success_accMono h hp
  | INVALID => simp [throw, throwThe, MonadExceptOf.throw] at h
  | CALL | CALLCODE | DELEGATECALL | STATICCALL | CREATE | CREATE2 =>
    simp [throw, throwThe, MonadExceptOf.throw] at h

open Lir.V2 (AccPresent) in
/-- **`systemOp` `.halted .success` preserves presence at `a`.** Only `haltOp` produces a `.success`
halt (CALL/CREATE never halt). -/
theorem systemOp_success_accMono {op : Operation.SystemOp} {fr : Frame} {exec e : ExecutionState}
    {o : ByteArray} {a : AccountAddress}
    (h : systemOp op fr exec = .ok (.halted (.success e o)))
    (hp : AccPresent a exec.accounts) : AccPresent a e.accounts := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    unfold systemOp at h
    exact haltOp_success_accMono h hp
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
      BytecodeLayer.System.systemOp_callArm_reduce (by tauto) h
    exact absurd hc (BytecodeLayer.System.callArm_neverHalts _)
  | CREATE =>
    obtain ⟨_, _, _, _, _, _, _, hcr⟩ :=
      BytecodeLayer.System.systemOp_createArm_reduce (by tauto) h
    exact absurd hcr (BytecodeLayer.System.createArm_neverHalts _)
  | CREATE2 =>
    obtain ⟨_, _, _, _, _, _, _, hcr⟩ :=
      BytecodeLayer.System.systemOp_createArm_reduce (by tauto) h
    exact absurd hcr (BytecodeLayer.System.createArm_neverHalts _)

open Lir.V2 (AccPresent) in
/-- **`stepFrame` `.halted .success` preserves presence at `a` (`hhalt`).** Decode + screen
(INVALID/overflow halt only with `.exception`), then the `.success` halt comes from `dispatch`, which
for a `System` op is `systemOp` (non-`System` arms never halt). -/
theorem stepFrame_halted_success_accMono {fr : Frame} {e : ExecutionState} {o : ByteArray}
    (h : stepFrame fr = .halted (.success e o)) (a : AccountAddress)
    (hp : AccPresent a fr.exec.accounts) : AccPresent a e.accounts := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp
    at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · -- INVALID screen: `.halted (.exception .InvalidInstruction)`, not `.success`
    exact absurd h (by simp)
  · split at h
    · -- overflow screen: `.halted (.exception .StackOverflow)`, not `.success`
      exact absurd h (by simp)
    · cases hdisp : dispatch op arg fr fr.exec with
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next ex => simp only at h; exact absurd h (by simp)
        | halted hl =>
          simp only [Signal.halted.injEq] at h; subst h
          -- the `.halted .success` from `dispatch` is a `System` op's `systemOp` signal
          cases op with
          | System s =>
            rw [dispatch] at hdisp
            exact systemOp_success_accMono hdisp hp
          | _ =>
            exact absurd hdisp
              (BytecodeLayer.System.dispatch_neverHalts (by
                intro s hc; exact absurd hc (by simp)) _)
        | needsCall p pc => simp only at h; exact absurd h (by simp)
        | needsCreate p pc => simp only at h; exact absurd h (by simp)
      | error er => rw [hdisp] at h; exact absurd h (by simp)


end Evm

-- HMONO: the engine-level CALL-seam facts PROVEN at an arbitrary tracked address `a`
-- (Brick C `stepFrame_next_accMono` + halt-success presence); `stepFrame_next_self` is the
-- `a := self` corollary of the walk.
