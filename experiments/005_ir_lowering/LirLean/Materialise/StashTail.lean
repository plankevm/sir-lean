import LirLean.Materialise.MaterialiseRuns
import LirLean.Materialise.MatFoldChannel
import BytecodeLayer.Exec.Stash

open Lir.Frame
open BytecodeLayer.Exec

/-!
# LirLean — SLOAD stash-tail adapter

The generic stash-tail simulations live in the bytecode execution layer. This module retains
the IR-specific cached-SLOAD adapter, which composes expression materialisation with `SLOAD` and
the generic tail.
-/

namespace Lir

export BytecodeLayer.Exec
  (memChargedState_memory memChargedState_activeWords mstoreFrame_memBytes_eq
   mstoreFrame_activeWords_eq pushFrameW_accounts pushFrameW_canMod pushFrameW_activeWords'
   pushFrameW_gas pushFrameW_stack' stash_tail_runs stash_tail_runs_covered stash_tail_gas)

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## The SLOAD-prefix variant (the cached-SLOAD def-site stash)

The spilled-SLOAD stash is `matCache k ++ [SLOAD] ++ PUSH32 slot ++ MSTORE`: materialise the
key `k` (the fold value-channel `Lir.materialise_runsC` prefix — a non-gas/non-sload `Expr`),
`SLOAD` the cell at `k`, then the core tail stashes the loaded value at `slot`. This composes
three existing GREEN pieces — `materialise_runsC` (`Materialise/MatFoldChannel.lean`),
`sim_sload` (the frame-local SLOAD brick), and `stash_tail_runs` — with no new spine decode
primitive.

The materialise-key endpoint `frk` and its `MatRunsC` bundle are taken as *inputs* (the caller
runs `materialise_runsC` and supplies them, exactly as `sim_assign_sload_lowered` does over
`lower prog`). The one genuine extra side-condition the variable-length prefix introduces is the
**activeWords-flatness residual** `hawk : frk.activeWords = fr.activeWords`: the memory-channel
ties anchor the value-channel MSTORE against the *pre-materialise* frame `fr`, and `mstore`'s
`activeWords` output is a function of the input `activeWords` (`mstore_activeWords_congr`), so the
two coincide exactly when materialising the key did not expand memory (the normal sload-key case;
`MatRunsC` guarantees `memBytes` equality unconditionally but only `activeWords`-nondecreasing).
The loaded value is tied to `w` through `selfStorage fr keyVal = w` (the `Corr`/`StorageAgree`
storage lens at the materialised key, threaded by `MatRunsC.storage`). -/

/-- **The spilled-SLOAD def-site stash `matCache k ; SLOAD ; PUSH32 slot ; MSTORE`
(forward lemma, P-walk).** From the statement boundary `fr` (`stack = []`), given the
materialise-key endpoint `frk` (the `MatRunsC` bundle for `.tmp k`, leaving the key value `keyVal`
on top of `[]`), the `SLOAD`/`PUSH32 slot`/`MSTORE` decode anchors relative to `frk`, the
activeWords-flatness residual `hawk`, the loaded-value tie `selfStorage fr keyVal = w`, and the
honest runtime SLOAD/PUSH/MSTORE gas + memory-expansion-witness side-conditions, running the four
opcode groups reaches `endFr` storing `w` at `slot`, with the **honest** memory channel
(`memory`/`activeWords` `= (fr.mstore slot w)`), the frame pins, and the stack back to `[]`. -/
theorem stash_tail_sload {prog : Program} {sloadChg : Tmp → ℕ}
    (fr frk : Frame) (k : Tmp) (keyVal w : Word) (slot : Nat) (words' : UInt64)
    (hstk : fr.exec.stack = [])
    (hmrk : Lir.MatRunsC prog sloadChg (.tmp k) keyVal fr frk)
    -- the activeWords-flatness residual: materialising the key did not expand memory.
    (hawk : frk.exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords)
    -- the loaded value is the `Corr`/`StorageAgree` reading of the world at the key (threaded
    -- back to `fr` by `MatRunsC.storage`):
    (hwval : selfStorage fr keyVal = w)
    -- decode anchors relative to `frk` (the SLOAD, then the stash tail PUSH/MSTORE):
    (hdsload : decode frk.exec.executionEnv.code frk.exec.pc = some (.Smsf .SLOAD, .none))
    (hdpush : decode frk.exec.executionEnv.code (frk.exec.pc + UInt32.ofNat 1)
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdmstore : decode frk.exec.executionEnv.code (frk.exec.pc + UInt32.ofNat 1 + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none))
    -- honest runtime gas / memory-expansion-witness side-conditions:
    (hgasSload : Evm.sloadCost (frk.exec.substate.accessedStorageKeys.contains
        (frk.exec.executionEnv.address, keyVal)) ≤ frk.exec.gasAvailable.toNat)
    (hgasPush : 3 ≤ (sloadFrame frk keyVal []).exec.gasAvailable.toNat)
    (hmem : memoryExpansionWords?
      (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.activeWords
      (UInt256.ofNat slot) 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf
      (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec words'
        ≤ (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.gasAvailable.toNat)
    (hgasMstore : GasConstants.Gverylow
      ≤ ((pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.gasAvailable
          - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf
              (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec words')).toNat) :
    StashRuns fr
      (mstoreFrame (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32)
        (UInt256.ofNat slot) w words' [])
      slot w ((matCache prog k).length + 35) [] := by
  -- key value on top of the boundary stack after materialising `k`.
  have hkstk : frk.exec.stack = keyVal :: [] := by rw [hmrk.stack, hstk]; rfl
  have hksz : frk.exec.stack.size ≤ 1024 := by rw [hkstk]; simp
  -- == step: SLOAD at `frk`, popping `keyVal`, pushing `selfStorage frk keyVal` ==
  obtain ⟨hsloadrun, _⟩ := sim_sload frk keyVal [] hdsload hkstk hksz hgasSload
  set frs := sloadFrame frk keyVal [] with hfrs
  -- frs facts: stack = [loaded], pc = frk.pc + 1, env / storage = frk's.
  have hsloaded : selfStorage frk keyVal = w := by
    rw [← hwval]; exact hmrk.storage keyVal
  have hsstk : frs.exec.stack = w :: [] := by
    rw [hfrs, sloadFrame_stack, hsloaded]; rfl
  have hscode : frs.exec.executionEnv.code = frk.exec.executionEnv.code := by
    rw [hfrs]; exact sloadFrame_code ..
  have hspc : frs.exec.pc = frk.exec.pc + UInt32.ofNat 1 := by
    rw [hfrs, sloadFrame_pc, show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
  -- the tail decode anchors relative to `frs.pc` (= frk.pc + 1).
  have hdpush' : decode frs.exec.executionEnv.code frs.exec.pc
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)) := by
    rw [hscode, hspc]; exact hdpush
  have hdmstore' : decode frs.exec.executionEnv.code (frs.exec.pc + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none) := by rw [hscode, hspc]; exact hdmstore
  have hssz : frs.exec.stack.size + 1 ≤ 1024 := by rw [hsstk]; simp
  -- == steps: the core tail from `frs`, stashing `w` ==
  let endFr := mstoreFrame (pushFrameW frs (UInt256.ofNat slot) 32)
    (UInt256.ofNat slot) w words' []
  obtain ⟨hrun, hmemBytes, hmemActive, hpc, hcode, hvalid, haddr, hcanmod, haccounts,
      hstorage, hstkEnd⟩ :=
    stash_tail_runs frs slot w [] words' hsstk hdpush' hdmstore' hssz hgasPush
      hmem hgasMem hgasMstore
  change StashRuns fr endFr slot w ((matCache prog k).length + 35) []
  refine ⟨(hmrk.runs.trans hsloadrun).trans hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hstkEnd⟩
  · -- memory bytes: tail writes `w` at `slot` over `frs`'s memory = `frk`'s = `fr`'s (memBytes).
    rw [hmemBytes]
    apply BytecodeLayer.Hoare.MemAlgebra.mstore_memory_congr
    show frs.exec.toMachineState.memory = fr.exec.toMachineState.memory
    rw [hfrs, sloadFrame_memory]; exact hmrk.memBytes
  · -- activeWords: tail's `activeWords` is a function of `frs`'s = `frk`'s = `fr`'s (hawk).
    rw [hmemActive]
    apply BytecodeLayer.Hoare.MemAlgebra.mstore_activeWords_congr
    show frs.exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords
    rw [hfrs, sloadFrame_activeWords, hawk]
  · -- pc: (frk.pc + 1) + 34 = fr.pc + ((matCache k).length + 35);
    -- frk.pc = fr.pc + (matCache k).length (`MatRunsC.pc` through `matExpr_tmp`).
    have hmrkpc : frk.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog k).length := by
      have := hmrk.pc; simpa only [matExpr_tmp] using this
    rw [hpc, hspc, hmrkpc, UInt32.ofNat_add,
        show (UInt32.ofNat 35) = UInt32.ofNat 1 + UInt32.ofNat 34 from by decide]
    ac_rfl
  · rw [hcode, hscode]; exact hmrk.code
  · rw [hvalid]; rw [hfrs, sloadFrame_validJumps]; exact hmrk.validJumps
  · rw [haddr]; rw [hfrs]; rw [sloadFrame_addr]; exact hmrk.addr
  · rw [hcanmod]; rw [hfrs]
    show (sloadFrame frk keyVal []).exec.executionEnv.canModifyState = _
    rw [show (sloadFrame frk keyVal []).exec.executionEnv.canModifyState
          = frk.exec.executionEnv.canModifyState from rfl]
    exact hmrk.canMod
  · -- accounts: SLOAD/PUSH/MSTORE never touch `accounts`; `frk`'s = `fr`'s (`MatRunsC`).
    rw [haccounts, hfrs]
    show (sloadFrame frk keyVal []).exec.accounts = _
    rw [show (sloadFrame frk keyVal []).exec.accounts = frk.exec.accounts from rfl]
    exact hmrk.accounts
  · intro kk; rw [hstorage kk]; rw [hfrs, sloadFrame_selfStorage]; exact hmrk.storage kk
end Lir

-- Build-enforced axiom-cleanliness guard for the P1 stash-tail forward lemmas: the core tail,
-- its covered specialization, the GAS-prefix variant, and the SLOAD-prefix variant (fold-keyed:
-- `MatRunsC`/`matCache`, no fuel) depend only on `[propext, Classical.choice, Quot.sound]`.
