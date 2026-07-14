import BytecodeLayer.Exec.Call
import BytecodeLayer.Exec.Create
import LirLean.Decode.LoweringLemmas
import LirLean.Decode.Layout
import BytecodeLayer.Exec.Invariants
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence

/-!
# LirLean — frame-local simulation and boundary lemmas

This module collects **atomic, frame-local simulation lemmas**. Each shows that an
EVM `Runs` segment implements one lowered construct, discharging straight to the
corresponding opcode rule. It also contains the CALL/CREATE oracle reflexivity
lemmas and the top-level `messageCall` boundary discharge.

The lemmas are deliberately stated using only the frame facts they consume: local
decode, stack shape, gas bounds, and observable storage. This keeps them reusable
by the current `Corr`-based simulation without carrying a second IR state or a
parallel invariant.
-/

namespace Lir.Frame
open BytecodeLayer.Exec
open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Maps
open BytecodeLayer.Dispatch
open BytecodeLayer.System

/-- The self account's storage at `key`, read through exp003's observable lens
(the same `find?/lookupStorage` used by `sstoreFrame_storage_self` /
`sloadFrame_storage_self`). -/
def selfStorage (fr : Frame) (key : Word) : Word :=
  fr.exec.accounts.find? fr.exec.executionEnv.address |>.option 0 (·.lookupStorage key)

/-- The storage of account `addr` at `key` in frame `fr`, through the same lens.
Used to state the `SSTORE` effect/frame clauses keyed on a fixed self address (the
exact form exp003's `sstoreFrame_storage_*` lemmas produce), sidestepping the
post-frame's own-address defeq. -/
def storageAt (fr : Frame) (addr : AccountAddress) (key : Word) : Word :=
  fr.exec.accounts.find? addr |>.option 0 (·.lookupStorage key)

/-! ## Atomic per-construct simulation lemmas

Each lemma takes the EVM frame's **local** facts (decode at `fr.exec.pc`, stack
shape, gas bound) — the hypotheses the `runs_*` rule wants — and packages the
resulting `Runs` with its concrete post-frame observation. The frame's real EVM gas
bound remains explicit; the gas-free IR does not account opcode cost. -/

/-- **`Expr.imm` simulation.** A frame decoding to `PUSH32 w` runs one step to
`pushFrameW fr w 32`, leaving `w` on top. -/
theorem sim_imm (fr : Frame) (w : Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrameW fr w 32)
      ∧ (pushFrameW fr w 32).exec.stack = fr.exec.stack.push w := by
  refine ⟨runs_push fr .PUSH32 w 32 (by nofun) hdec rfl rfl hgas hstk, ?_⟩
  rfl

/-- **`Expr.gas` simulation.** A frame decoding to `GAS` runs one step to
`gasFrame fr`, dropping the frame's real EVM gas by `GasConstants.Gbase` (the
*bytecode* spec's honest gas — the IR no longer accounts cost). -/
theorem sim_gas (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gasFrame fr)
      ∧ (gasFrame fr).exec.gasAvailable = fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase := by
  exact ⟨runs_gas fr hdec hsz hgas, rfl⟩

/-- **`Expr.add` simulation.** A frame decoding to `ADD` with `a :: b :: rest`
runs one step to `addFrame fr a b rest`, leaving `UInt256.add a b` on top. -/
theorem sim_add (fr : Frame) (a b : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (addFrame fr a b rest)
      ∧ (addFrame fr a b rest).exec.stack = rest.push (UInt256.add a b) := by
  exact ⟨runs_add fr a b rest hdec hstk hsz hgas, rfl⟩

/-- **`Expr.lt` simulation.** A frame decoding to `LT` with `a :: b :: rest` runs
one step to `ltFrame fr a b rest`, leaving `UInt256.lt a b` on top. -/
theorem sim_lt (fr : Frame) (a b : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (ltFrame fr a b rest)
      ∧ (ltFrame fr a b rest).exec.stack = rest.push (UInt256.lt a b) := by
  exact ⟨runs_lt fr a b rest hdec hstk hsz hgas, rfl⟩

/-- **`Expr.sload` simulation.** A frame decoding to `SLOAD` with `key :: rest`
runs one step to `sloadFrame fr key rest`, leaving the self account's stored value
at `key` on top. -/
theorem sim_sload (fr : Frame) (key : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (sloadFrame fr key rest)
      ∧ (sloadFrame fr key rest).exec.stack.head? = some (selfStorage fr key) := by
  exact ⟨runs_sload fr key rest hdec hstk hsz hgas, sloadFrame_storage_self fr key rest⟩

/-- **SSTORE effect, value-agnostic.** Reading the self account's storage at
`key` after `sstoreFrame` returns `newValue` — for *every* `newValue`, including
`0` (a slot clear, which `Account.updateStorage` implements as an `RBMap.erase`;
the read-back then hits `Evm.Storage.findD_erase_self`). -/
theorem sstoreFrame_storage_self' (fr : Frame) (key newValue : Word) (rest : Stack Word)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? fr.exec.executionEnv.address
      |>.option 0 (·.lookupStorage key)) = newValue := by
  rw [sstoreFrame_accounts fr key newValue rest acc hself, accounts_find?_insert_self]
  show (acc.updateStorage key newValue).lookupStorage key = newValue
  unfold Account.updateStorage Account.lookupStorage
  by_cases h0 : newValue = 0
  · subst h0
    rw [if_pos (by decide)]
    exact Evm.Storage.findD_erase_self acc.storage key
  · rw [if_neg (by
      show ¬ ((newValue == (default : UInt256)) = true)
      rw [show (default : UInt256) = 0 from rfl]
      intro hc; exact h0 ((UInt256.beq_iff_eq newValue 0).mp hc))]
    exact storage_findD_insert_self _ _ _ _

/-- **SSTORE framing, value-agnostic.** Any cell other than `(self, key)` is
unchanged after `sstoreFrame`, for *every* `newValue` including `0` (the erase
branch, read back through `Evm.Storage.findD_erase_of_ne`). -/
theorem sstoreFrame_storage_frame' (fr : Frame) (key newValue : Word) (rest : Stack Word)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (a' : AccountAddress) (k' : UInt256)
    (hframe : a' ≠ fr.exec.executionEnv.address ∨ k' ≠ key) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? a' |>.option 0 (·.lookupStorage k'))
      = (fr.exec.accounts.find? a' |>.option 0 (·.lookupStorage k')) := by
  rw [sstoreFrame_accounts fr key newValue rest acc hself]
  rcases hframe with ha | hk
  · rw [accounts_find?_insert_of_ne _ _ ha]
  · by_cases ha : a' = fr.exec.executionEnv.address
    · subst ha
      rw [accounts_find?_insert_self, hself]
      show (acc.updateStorage key newValue).lookupStorage k' = acc.lookupStorage k'
      unfold Account.updateStorage Account.lookupStorage
      by_cases h0 : newValue = 0
      · subst h0
        rw [if_pos (by decide)]
        exact Evm.Storage.findD_erase_of_ne acc.storage hk
      · rw [if_neg (by
          show ¬ ((newValue == (default : UInt256)) = true)
          rw [show (default : UInt256) = 0 from rfl]
          intro hc; exact h0 ((UInt256.beq_iff_eq newValue 0).mp hc))]
        exact storage_findD_insert_of_ne _ _ _ hk
    · rw [accounts_find?_insert_of_ne _ _ ha]

/-- **`Stmt.sstore` simulation.** A frame decoding to `SSTORE` with
`key :: value :: rest` runs one step to `sstoreFrame fr key value rest`; reading
back `(self, key)` returns `value` (for *every* `value`, zero writes included),
re-establishing `M3` at the written cell, and any other cell is unchanged (the
frame clause). -/
theorem sim_sstore (fr : Frame) (key value : Word) (rest : Stack Word) (acc : Account)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: value :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key value ≤ fr.exec.gasAvailable.toNat)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc) :
    Runs fr (sstoreFrame fr key value rest)
      ∧ storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address key = value
      ∧ ∀ k', k' ≠ key →
          storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address k'
            = storageAt fr fr.exec.executionEnv.address k' := by
  refine ⟨runs_sstore fr key value rest hdec hstk hsz hmod hstip hcost, ?_, ?_⟩
  · exact sstoreFrame_storage_self' fr key value rest acc hself
  · intro k' hk'
    exact sstoreFrame_storage_frame' fr key value rest acc hself
      fr.exec.executionEnv.address k' (Or.inr hk')

/-! ### `popFrame` accessor reductions

`popPost`/`popFrame` (exp003 `Hoare.lean`) `replaceStackAndIncrPC`s after a `Gbase`
charge — replacing the stack with `rest`, advancing pc by one, leaving
`executionEnv` (hence code / address) untouched. These reductions mirror the
`sstoreFrame_*` / `sloadFrame_*` families so the worked-example run can read off the
post-frame's code/pc/stack/gas/addr by `simp`. -/

@[simp] theorem popFrame_code (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem popFrame_validJumps (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).validJumps = fr.validJumps := rfl

@[simp] theorem popFrame_addr (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem popFrame_pc (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem popFrame_stack (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.stack = rest := rfl

@[simp] theorem popFrame_gas (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.gasAvailable
      = fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase := rfl

/-! ## MSTORE / MLOAD simulation (the memory value channel)

The memory bricks Track C's value channel (`docs/calls-value-channel-plan.md`)
threads. `sim_mload` exposes the pushed word (the head of the resulting stack);
`sim_mstore` exposes that the post-frame's memory is `fr`'s memory (on the
doubly-charged state) with `val` written at `addr` (`mstore addr val`) — the read-back
a later MLOAD lemma consumes. Both take the memory-expansion witness `hmem` (pinning
`words'`) and the two honest *bytecode*-gas bounds (memory expansion + `Gverylow`),
exactly the hypotheses `runs_mstore`/`runs_mload` want. Mirrors `sim_sstore`/`sim_sload`. -/

/-- **`Expr.mload` simulation.** A frame decoding to `MLOAD` with `addr :: rest` runs
one step to `mloadFrame fr addr words' rest`, leaving the word read from memory at
`addr` on top — exposed through `mloadFrame_value`. -/
theorem sim_mload (fr : Frame) (addr : Word) (words' : UInt64) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words'
                ≤ fr.exec.gasAvailable.toNat)
    (hgas : GasConstants.Gverylow
              ≤ (fr.exec.gasAvailable
                  - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words')).toNat) :
    Runs fr (mloadFrame fr addr words' rest)
      ∧ (mloadFrame fr addr words' rest).exec.stack.head?
          = some ((BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mload addr).1 := by
  exact ⟨runs_mload fr addr words' rest hdec hstk hsz hmem hgasMem hgas,
    mloadFrame_value fr addr words' rest⟩

/-- **`Stmt.mstore` simulation.** A frame decoding to `MSTORE` with
`addr :: val :: rest` runs one step to `mstoreFrame fr addr val words' rest`; the
post-frame's memory is `fr`'s (doubly-charged) machine state with `val` written at
`addr` (`mstore addr val`) — the read-back a later `sim_mload` consumes. -/
theorem sim_mstore (fr : Frame) (addr val : Word) (words' : UInt64) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words'
                ≤ fr.exec.gasAvailable.toNat)
    (hgas : GasConstants.Gverylow
              ≤ (fr.exec.gasAvailable
                  - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words')).toNat) :
    Runs fr (mstoreFrame fr addr val words' rest)
      ∧ (mstoreFrame fr addr val words' rest).exec.toMachineState
          = (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mstore addr val := by
  exact ⟨runs_mstore fr addr val words' rest hdec hstk hsz hmem hgasMem hgas,
    mstoreFrame_memory fr addr val words' rest⟩

/-! ## Terminator halt steps (consumed by the bridge `hhalt`)

`STOP`/`RETURN` are **not** `runs_*` rules — the bridge `messageCall_runs` takes the
halt directly via its `hhalt` argument. These lemmas expose exactly that halt step
for the two IR terminators, ready to feed the bridge. -/

/-- **`Term.stop` halt.** A frame decoding to `STOP` halts with the current state
and empty output — the `hhalt` the bridge consumes for `IRHalt.stopped`. -/
theorem halt_stop (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .STOP, .none))
    (hstk : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success fr.exec .empty) :=
  stepFrame_stop fr hdec hstk

/-! ### The RETURN-word halt (the full-observable `ret` shape)

The full-observable `ret` lowering (`emitTerm .ret`) is `materialise t ++ PUSH32 0 ++
MSTORE ++ PUSH32 32 ++ PUSH32 0 ++ RETURN`: it stashes the returned word `vw` to
`mem[0]` then `RETURN(0, 32)` returns that 32-byte window (`vw`'s big-endian bytes).
The halt brick therefore returns a **non-empty** 32-byte output — the return-data
observable `observe` reads back as `returned vw`. -/

/-- The execution state RETURN(0, 32) leaves before halting **when offset `0` / size `32`
is already covered by `activeWords`** (the post-`MSTORE(0, …)` shape): the memory charge is
`Cₘ activeWords - Cₘ activeWords = 0` (a no-op on gas), the `activeWords` bump `M _ 0 32`,
and the popped stack. The size-32 analogue of `returnEmptyPost`; its `.accounts` are
`exec.accounts` by `rfl`. -/
def returnWordPost (exec : ExecutionState) (rest : Stack Word) : ExecutionState :=
  let charged : ExecutionState := { exec with gasAvailable := exec.gasAvailable - UInt64.ofNat 0 }
  ExecutionState.replaceStackAndIncrPC
    { charged with
        toMachineState :=
          { charged.toMachineState with
              activeWords := MachineState.M charged.activeWords (0 : Word).toUInt64 (32 : Word).toUInt64 } }
    rest

/-- **`Term.ret` halt (word return window).** A frame decoding to `RETURN` with
`0 :: 32 :: rest` on the stack and offset `0`/size `32` **already covered** by
`activeWords` (`hmem`: `memoryExpansionWords? activeWords 0 32 = some activeWords`, so the
memory charge is `0` — the post-`MSTORE(0,…)` shape) halts successfully, returning the
32-byte window `memory.readWithPadding 0 32`. This is the `hhalt` the bridge consumes for
`IRHalt.returned vw`; the returned bytes are `vw`'s (`readWithPadding_written_grow`). The
size-32 analogue of `stepFrame_return_empty`. -/
theorem stepFrame_return_word (fr : Frame) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .RETURN, .none))
    (hstk : fr.exec.stack = (0 : Word) :: (32 : Word) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords (0 : Word) (32 : Word)
              = some fr.exec.activeWords) :
    stepFrame fr = .halted (.success (returnWordPost fr.exec rest)
      (fr.exec.memory.readWithPadding (0 : Word).toNat (32 : Word).toNat)) := by
  unfold stepFrame
  simp only [hdec]
  dsimp only [Option.getD]
  rw [if_neg (by decide)]
  have hov : ¬ (fr.exec.stack.size - stackPopCount (.System .RETURN)
      + stackPushCount (.System .RETURN) > 1024) := by
    simp only [show stackPopCount (.System .RETURN) = 2 from rfl,
               show stackPushCount (.System .RETURN) = 0 from rfl]
    have := hsz; omega
  rw [if_neg hov]
  dsimp only [dispatch, systemOp, haltOp, returnOrRevertOp]
  rw [hstk]
  dsimp only [Stack.pop2, liftM, monadLift, MonadLift.monadLift, Option.option, bind,
    Except.bind, pure, Except.pure]
  dsimp only [chargeMemExpansion]
  rw [hmem]
  dsimp only []
  rw [Nat.sub_self]
  unfold charge
  rw [if_neg (by simp)]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg (by decide)]
  dsimp only [returnWordPost]

/-! ### `activeWords` evaluation helpers for the RETURN-window coverage `hmem`

At the RETURN frame the lowering has just executed `MSTORE(0, vw)`, so `activeWords`
is `M A 0 32` (the `mstore` bump). `RETURN(0, 32)`'s coverage witness therefore needs
`memoryExpansionWords? (M A 0 32) 0 32 = some (M A 0 32)` — the size-32 memory access at
offset 0 is a no-op because the window is already active (`M`-idempotence). -/

/-- `M · 0 32` is idempotent (both fold `x ↦ max x 1`). -/
theorem M_zero32_idem (a : UInt64) :
    MachineState.M (MachineState.M a 0 32) 0 32 = MachineState.M a 0 32 := by
  have h : ∀ b : UInt64, MachineState.M b 0 32 = max b 1 := fun b => rfl
  rw [h a, h (max a 1)]
  simp only [UInt64.max_def]
  by_cases hc : a ≤ 1 <;> simp [hc]

/-- **`memoryExpansionWords?` at an already-active `[0, 32)` window is a no-op.** For
`activeWords = M a 0 32` (the post-`MSTORE(0,…)` shape), the size-32 access at offset 0
expands to the same `activeWords` (`M`-idempotence) — the zero-charge coverage witness
`stepFrame_return_word` consumes. -/
theorem memExpWords_zero32_covered (a : UInt64) :
    memoryExpansionWords? (MachineState.M a 0 32) (0 : Word) (32 : Word)
      = some (MachineState.M a 0 32) := by
  unfold memoryExpansionWords?
  rw [if_neg (by decide)]
  dsimp only [bind, Option.bind]
  rw [show ((0 : Word).toUInt64? = some 0) from by decide,
      show ((32 : Word).toUInt64? = some 32) from by decide]
  dsimp only []
  rw [if_neg (by decide)]
  rw [M_zero32_idem]

/-! ## `Stmt.call` simulation (the `Runs.call` node)

A `Stmt.call` lowers to seven CALL-arg pushes then `CALL`. Under lowering it is a
`Runs.call` node carrying a `CallReturns` witness (the CALL step, the child
entering as code, the black-box child run, the resumed parent). The engine threads
exactly that node by `Runs.trans` — see the worked compositional derivation in
`BytecodeLayer.Examples.CallerProgExample`. We expose the constructor wrapper. -/

/-- **`Stmt.call` simulation.** Given a returning external CALL at `callFr`
(`CallReturns callFr resumeFr`) and the `Runs` continuation from the resumed frame,
the whole call is one `Runs callFr fr'` — a `Runs.call` node glued by the rest. The
`CallReturns` witness is built exactly as in
`BytecodeLayer.Examples.CallerProgExample.caller_callReturns`. -/
theorem sim_call {callFr resumeFr fr' : Frame}
    (hcall : CallReturns callFr resumeFr) (rest : Runs resumeFr fr') :
    Runs callFr fr' :=
  Runs.call hcall rest

/-! ## Call-oracle reflexivity headline (`docs/ir-design.md` §5)

The deliverable that demonstrates the call-agnostic design: **instantiate the
oracle to `evmCallOracle` → the IR's call-effect is *reflexively equal* to the
lowered bytecode's ext-call effect.** The
IR side reads the oracle's projections (`postStorage` / `restoredGas` /
`successWord`); the EVM side is the resumed frame `resumeAfterCall result pd`'s
observables. Because `evmCallOracle`'s fields are *defined* as those very
projections (`Frame/Call.lean`), the three coincidences are `rfl`-clean.

The `CallReturns callFr resumeFr` witness pins `resumeFr = resumeAfterCall
childRes.toCallResult pending`, so the headline reads off the actual resumed frame. -/

/-- **The external-call reflexivity headline.** Given a returning external CALL
(`CallReturns callFr resumeFr`, so `resumeFr = resumeAfterCall result pd` for the
projected child result / pending call), at `evmCallOracle` the IR's call effect
coincides — *by construction* — with the lowered resume's observables:

* **post-storage** of any account `addr` at `key` equals the resumed frame's
  observable storage (`storageAt resumeFr`);
* **restored gas** equals the resumed frame's `gasAvailable` (`gasAfterReturn`);
* **success word** equals the word the CALL pushed onto the stack — the head of
  `resumeFr`'s stack, which is exp003's `x` (0 on failure/insufficient-funds/
  depth-limit, else 1).

Instantiate the oracle to the EVM one and the IR's external-call effect is
reflexively the lowered bytecode's. -/
theorem call_reflects_lowered {callFr resumeFr : Frame}
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (∀ addr key, evmCallOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCallOracle.restoredGas result pd = resumeFr.exec.gasAvailable
      ∧ evmCallOracle.successWord result pd = callSuccessFlag result pd := by
  obtain ⟨cp, pending, child, childRes, _hstep, _henters, _hdrive, hresume⟩ := hcall
  subst hresume
  exact ⟨childRes.toCallResult, pending, rfl, fun _ _ => rfl, rfl, rfl⟩

/-! ## `Stmt.create` simulation (the `Runs.create` node)

A `Stmt.create` lowers to the CREATE-arg pushes then `CREATE`/`CREATE2`. Under
lowering it is a `Runs.create` node carrying a `CreateReturns` witness (the CREATE
step, the total `beginCreate` child's black-box run, the *successfully-resumed*
parent through the 63/64 retention guard). The engine threads exactly that node by
`Runs.trans`, the twin of `sim_call`. -/

/-- **`Stmt.create` simulation.** Given a returning CREATE at `createFr`
(`CreateReturns createFr resumeFr`, so the init child ran and `resumeAfterCreate`
resolved `.ok resumeFr` past the 63/64 guard) and the `Runs` continuation from the
resumed frame, the whole create is one `Runs createFr fr'` — a `Runs.create` node
glued by the rest. The CREATE twin of `sim_call`. -/
theorem sim_create {createFr resumeFr fr' : Frame}
    (hc : CreateReturns createFr resumeFr) (rest : Runs resumeFr fr') :
    Runs createFr fr' :=
  Runs.create hc rest

/-! ## Create-oracle reflexivity headline (CREATE twin of `call_reflects_lowered`)

The CREATE analogue of the call-reflexivity deliverable: **instantiate the oracle to
`evmCreateOracle` → the IR's create-effect is *equal* to the lowered bytecode's
CREATE effect.** Unlike CALL, this is **not** fully `rfl`-clean on the storage side.
`evmCallOracle.postStorage` projects `resumeAfterCall` directly, so its coincidence
with `storageAt resumeFr` is `rfl`. `evmCreateOracle.postStorage`, by contrast, reads
`result.accounts` **directly** (kept total because `resumeAfterCreate` is
`Except`-typed and may throw on the 63/64 guard, `Create.lean`), while the resumed
frame's storage is `resumeFr.exec.accounts`. The `CreateReturns` witness pins
`resumeAfterCreate result pd = .ok resumeFr`; `resumeAfterCreate` writes `accounts :=
result.accounts` (exp003 `Create.lean:204`), untouched by the `replaceStackAndIncrPC`
wrapper, so the two coincide — but through a short unfold of the guarded resume, not a
`rfl`. The address-word side stays `rfl` (`evmCreateOracle.addressWord :=
createAddrOrZero`). -/

/-- **The CREATE reflexivity headline.** Given a returning, successfully-resumed CREATE
(`CreateReturns createFr resumeFr`, so `resumeAfterCreate result pd = .ok resumeFr` for
the projected child result / pending create), at `evmCreateOracle` the IR's create
effect coincides with the lowered resume's observables:

* **post-storage** of any account `addr` at `key` equals the resumed frame's
  observable storage (`storageAt resumeFr`) — via the `accounts := result.accounts`
  write of `resumeAfterCreate`, unfolded through the 63/64 guard;
* **address word** equals the deployed-address-or-`0` the CREATE pushes
  (`createAddrOrZero`, `rfl`).

The CREATE twin of `call_reflects_lowered`; the storage side is the create-specific
proof cost (R3) that CALL got for free. -/
theorem create_reflects_lowered {createFr resumeFr : Frame}
    (hc : CreateReturns createFr resumeFr) :
    ∃ result pd, resumeAfterCreate result pd = .ok resumeFr
      ∧ (∀ addr key, evmCreateOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCreateOracle.addressWord result pd = createAddrOrZero result pd := by
  obtain ⟨cp, pending, childRes, _hstep, _hdrive, hresume⟩ := hc
  refine ⟨childRes.toCreateResult, pending, hresume, ?_, rfl⟩
  -- Storage side (R3): `evmCreateOracle.postStorage` reads `result.accounts` directly,
  -- while `storageAt resumeFr` reads `resumeFr.exec.accounts`. `resumeAfterCreate` writes
  -- `accounts := result.accounts` (exp003 `Create.lean:204`), unchanged by
  -- `replaceStackAndIncrPC` — so unfold the guarded resume to identify the two.
  have hacc : resumeFr.exec.accounts = childRes.toCreateResult.accounts := by
    unfold resumeAfterCreate at hresume
    simp only [bind, Except.bind, pure, Except.pure] at hresume
    split at hresume
    · exact absurd hresume (by simp)
    · simp only [Except.ok.injEq] at hresume
      rw [← hresume]
      dsimp only [ExecutionState.replaceStackAndIncrPC]
  intro addr key
  simp only [evmCreateOracle, storageAt, hacc]

/-! ## Top-level preservation discharge (`lower_preserves`, the bridge half)

`lower_preserves` (`docs/ir-design.md` §6.3) closes the simulation under the IR run
and crosses the single boundary bridge `messageCall_runs`. The program-global
*assembly* of the `Runs fr₀ last` is separate; the **discharge** —
turning an assembled `Runs` + the terminator halt into the observable
`messageCall` result — is fully provable now and proved here. It is the exact half
that consumes A's `messageCall_runs`, specialised to the two IR terminators.

`lower_preserves_discharge` is the construct-agnostic bridge; `lower_preserves_stop`
/ `lower_preserves_ret` are the two terminator instances, supplying the halt from
`halt_stop` / `stepFrame_return_word`. The single-call worked program assembles its `Runs` and
applies the matching one. -/

/-- **The boundary discharge.** A top-level call entering the lowered code as code
(`EntersAsCode`) whose assembled `Runs fr₀ last` reaches a halting `last`
(`stepFrame last = .halted halt`) delivers the caller's halt result as
`messageCall`. This is `messageCall_runs` applied at the IR/lowering boundary; it
crosses regardless of how many `Runs.call` (external CALL) nodes the assembled run
contains (multi-call composition is `messageCall_runs_calls`). -/
theorem lower_preserves_discharge (prog : Program) (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (_hcode : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin hruns hhalt

/-- **`Term.stop` preservation.** When the assembled `Runs` lands on a `STOP` frame
`last`, the discharge pins `messageCall` to `last`'s success
`endFrame`. The halt is `halt_stop`. -/
theorem lower_preserves_stop (prog : Program) (p : CallParams) {fr₀ last : Frame}
    (hbegin : EntersAsCode p fr₀)
    (hcode  : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hdec   : decode last.exec.executionEnv.code last.exec.pc = some (.System .STOP, .none))
    (hstk   : last.exec.stack.size ≤ 1024) :
    messageCall p = .ok (FrameResult.toCallResult
      (endFrame last (.success last.exec .empty))) :=
  lower_preserves_discharge prog p hbegin hcode hruns (halt_stop last hdec hstk)

/-- **`Term.ret` preservation** (word return window). When the assembled `Runs`
lands on a `RETURN` frame `last` with `0 :: 32 :: rest` and the `[0, 32)` window already
active (`hmem`, the post-`MSTORE(0,…)` shape), the discharge pins
`messageCall` to `last`'s success `endFrame`, returning the 32-byte window. The halt is
`stepFrame_return_word`. -/
theorem lower_preserves_ret (prog : Program) (p : CallParams) {fr₀ last : Frame}
    (rest : Stack Word)
    (hbegin : EntersAsCode p fr₀)
    (hcode  : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hdec   : decode last.exec.executionEnv.code last.exec.pc = some (.System .RETURN, .none))
    (hstk   : last.exec.stack = (0 : Word) :: (32 : Word) :: rest)
    (hsz    : last.exec.stack.size ≤ 1024)
    (hmem   : memoryExpansionWords? last.exec.activeWords (0 : Word) (32 : Word)
                = some last.exec.activeWords) :
    messageCall p = .ok (FrameResult.toCallResult
      (endFrame last (.success (returnWordPost last.exec rest)
        (last.exec.memory.readWithPadding (0 : Word).toNat (32 : Word).toNat)))) :=
  lower_preserves_discharge prog p hbegin hcode hruns (stepFrame_return_word last rest hdec hstk hsz hmem)

end Lir.Frame

-- Build-enforced axiom-cleanliness guard for the memory value-channel simulation
-- bricks: both MSTORE/MLOAD arms depend only on `[propext, Classical.choice, Quot.sound]`.
