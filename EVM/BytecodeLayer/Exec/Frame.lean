import BytecodeLayer.Exec.Call
import BytecodeLayer.Exec.Create
import BytecodeLayer.Exec.CallRealises
import BytecodeLayer.Exec.Invariants
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence

namespace BytecodeLayer.Exec

open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Maps
open BytecodeLayer.Dispatch
open BytecodeLayer.System

def selfStorage (fr : Frame) (key : Word) : Word :=
  fr.exec.accounts.find? fr.exec.executionEnv.address |>.option 0 (·.lookupStorage key)

/-! ## Atomic per-construct simulation lemmas

Each lemma takes the EVM frame's **local** facts (decode at `fr.exec.pc`, stack
shape, gas bound) — the hypotheses the `runs_*` rule wants — and packages the
resulting `Runs` with its concrete post-frame observation. The frame's real EVM gas
bound remains explicit. -/

/-- **`PUSH32` simulation.** A frame decoding to `PUSH32 w` runs one step to
`pushFrameW fr w 32`, leaving `w` on top. -/
theorem sim_imm (fr : Frame) (w : Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrameW fr w 32)
      ∧ (pushFrameW fr w 32).exec.stack = fr.exec.stack.push w := by
  refine ⟨runs_push fr .PUSH32 w 32 (by nofun) hdec rfl rfl hgas hstk, ?_⟩
  rfl

/-- **`GAS` simulation.** A frame decoding to `GAS` runs one step to
`gasFrame fr`, dropping the frame's real EVM gas by `GasConstants.Gbase`. -/
theorem sim_gas (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gasFrame fr)
      ∧ (gasFrame fr).exec.gasAvailable = fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase := by
  exact ⟨runs_gas fr hdec hsz hgas, rfl⟩

/-- **`ADD` simulation.** A frame decoding to `ADD` with `a :: b :: rest`
runs one step to `addFrame fr a b rest`, leaving `UInt256.add a b` on top. -/
theorem sim_add (fr : Frame) (a b : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (addFrame fr a b rest)
      ∧ (addFrame fr a b rest).exec.stack = rest.push (UInt256.add a b) := by
  exact ⟨runs_add fr a b rest hdec hstk hsz hgas, rfl⟩

/-- **`LT` simulation.** A frame decoding to `LT` with `a :: b :: rest` runs
one step to `ltFrame fr a b rest`, leaving `UInt256.lt a b` on top. -/
theorem sim_lt (fr : Frame) (a b : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (ltFrame fr a b rest)
      ∧ (ltFrame fr a b rest).exec.stack = rest.push (UInt256.lt a b) := by
  exact ⟨runs_lt fr a b rest hdec hstk hsz hgas, rfl⟩

/-- **`SLOAD` simulation.** A frame decoding to `SLOAD` with `key :: rest`
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

/-- **`SSTORE` simulation.** A frame decoding to `SSTORE` with
`key :: value :: rest` runs one step to `sstoreFrame fr key value rest`; reading
back `(self, key)` returns `value` (for *every* `value`, zero writes included),
and any other cell is unchanged. -/
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

`popPost`/`popFrame` `replaceStackAndIncrPC`s after a `Gbase` charge — replacing the
stack with `rest`, advancing pc by one, and leaving `executionEnv` (hence code and
address) untouched. These reductions expose the post-frame's code, pc, stack, gas,
and address to `simp`. -/

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

`sim_mload` exposes the pushed word (the head of the resulting stack);
`sim_mstore` exposes that the post-frame's memory is `fr`'s memory (on the
doubly-charged state) with `val` written at `addr` (`mstore addr val`) — the read-back
a later MLOAD lemma consumes. Both take the memory-expansion witness `hmem` (pinning
`words'`) and the two honest *bytecode*-gas bounds (memory expansion + `Gverylow`),
exactly the hypotheses `runs_mstore`/`runs_mload` want. Mirrors `sim_sstore`/`sim_sload`. -/

/-- **`MLOAD` simulation.** A frame decoding to `MLOAD` with `addr :: rest` runs
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

/-- **`MSTORE` simulation.** A frame decoding to `MSTORE` with
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

`STOP`/`RETURN` are **not** `runs_*` rules. These lemmas expose their halt steps
directly. -/

/-- **`STOP` halt.** A frame decoding to `STOP` halts with the current state and
empty output. -/
theorem halt_stop (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .STOP, .none))
    (hstk : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success fr.exec .empty) :=
  stepFrame_stop fr hdec hstk

/-! ### The RETURN-word halt (the full-observable `ret` shape)

The halt brick returns the **non-empty** 32-byte window selected by
`RETURN(0, 32)`. -/

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

/-- **`RETURN` halt (word return window).** A frame decoding to `RETURN` with
`0 :: 32 :: rest` on the stack and offset `0`/size `32` **already covered** by
`activeWords` (`hmem`: `memoryExpansionWords? activeWords 0 32 = some activeWords`, so the
memory charge is `0` — the post-`MSTORE(0,…)` shape) halts successfully, returning the
32-byte window `memory.readWithPadding 0 32`. The size-32 analogue of
`stepFrame_return_empty`. -/
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

After `MSTORE(0, vw)`, `activeWords` is `M A 0 32` (the `mstore` bump).
`RETURN(0, 32)`'s coverage witness therefore needs
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

/-! ## CALL simulation (the `Runs.call` node)

A returning external call is a `Runs.call` node carrying a `CallReturns` witness:
the CALL step, the child entering as code, the child run, and the resumed parent.
This section exposes the constructor wrapper. -/

/-- **CALL simulation.** Given a returning external CALL at `callFr`
(`CallReturns callFr resumeFr`) and the `Runs` continuation from the resumed frame,
the whole call is one `Runs callFr fr'` — a `Runs.call` node glued by the rest. -/
theorem sim_call {callFr resumeFr fr' : Frame}
    (hcall : CallReturns callFr resumeFr) (rest : Runs resumeFr fr') :
    Runs callFr fr' :=
  Runs.call hcall rest

/-! ## CREATE simulation (the `Runs.create` node)

A returning contract creation is a `Runs.create` node carrying a `CreateReturns`
witness: the CREATE step, the child run, and the successfully resumed parent after
the 63/64 retention guard. -/

/-- **CREATE simulation.** Given a returning CREATE at `createFr`
(`CreateReturns createFr resumeFr`, so the init child ran and `resumeAfterCreate`
resolved `.ok resumeFr` past the 63/64 guard) and the `Runs` continuation from the
resumed frame, the whole create is one `Runs createFr fr'` — a `Runs.create` node
glued by the rest. The CREATE twin of `sim_call`. -/
theorem sim_create {createFr resumeFr fr' : Frame}
    (hc : CreateReturns createFr resumeFr) (rest : Runs resumeFr fr') :
    Runs createFr fr' :=
  Runs.create hc rest


end BytecodeLayer.Exec
