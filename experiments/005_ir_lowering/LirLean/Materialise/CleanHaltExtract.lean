import BytecodeLayer.Exec.CleanHaltExtract
import LirLean.Materialise.MatFoldChannel

open BytecodeLayer.Exec

namespace Lir.CleanHaltExtract

open Evm
open Evm.Operation
open GasConstants
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open BytecodeLayer.Exec.CleanHaltExtract

export BytecodeLayer.Exec.CleanHaltExtract
  (stepFrame_gas_oog stepFrame_gas_inv stepFrame_push_oog stepFrame_push_inv
   stepFrame_sload_oog stepFrame_sload_inv stepFrame_add_oog stepFrame_add_inv
   stepFrame_lt_oog stepFrame_lt_inv stepFrame_mload_oogNone stepFrame_mload_oogMem
   stepFrame_mload_oogVL stepFrame_mload_inv halted_runs_eq next_of_cleanHalt_continuing
   stepFrame_gas_dichotomy stepFrame_push_dichotomy stepFrame_sload_dichotomy
   stepFrame_mstore_dichotomy next_gas_of_cleanHalt next_push_of_cleanHalt
   next_sload_of_cleanHalt next_mstore_of_cleanHalt stepFrame_add_dichotomy
   stepFrame_lt_dichotomy stepFrame_mload_dichotomy next_add_of_cleanHalt
   next_lt_of_cleanHalt next_mload_of_cleanHalt stepsTo_gasFrame stepsTo_pushFrameW
   gas_envelope_of_cleanHalt stepsTo_sloadFrame stepFrame_jump_oog stepFrame_jump_inv
   stepFrame_jumpdest_oog stepFrame_jumpdest_inv stepFrame_jump_dichotomy
   stepFrame_jumpdest_dichotomy next_jump_of_cleanHalt next_jumpdest_of_cleanHalt
   stepFrame_jumpi_oog stepFrame_jumpi_inv stepFrame_jumpi_taken_dichotomy
   stepFrame_jumpi_fallthrough_dichotomy next_jumpi_taken_of_cleanHalt
   next_jumpi_fallthrough_of_cleanHalt stepFrame_pop_oog stepFrame_pop_inv
   stepFrame_pop_dichotomy next_pop_of_cleanHalt stepFrame_call_oog
   call_extraCost_le_of_cleanHalt)

/-- The generic SLOAD clean-halt envelope specialised to an IR materialisation run. -/
theorem sload_envelope_of_cleanHalt
    {prog : Program} {sloadChg : Tmp → ℕ} {ekey : Expr} {wkey : Word}
    (fr frk : Frame) (keyVal : UInt256) (slot : Nat)
    (hcs : CleanHaltsNonException fr)
    (hstk0 : fr.exec.stack = [])
    (hmrk : Lir.MatRunsC prog sloadChg ekey wkey fr frk)
    (hkeyval : wkey = keyVal)
    (hdecSLOAD : decode frk.exec.executionEnv.code frk.exec.pc = some (.Smsf .SLOAD, .none))
    (hdecPUSH : decode (sloadFrame frk keyVal []).exec.executionEnv.code
          (sloadFrame frk keyVal []).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdecMSTORE :
        decode (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.executionEnv.code
          (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.pc
        = some (.Smsf .MSTORE, .none)) :
    sloadCost (frk.exec.substate.accessedStorageKeys.contains
        (frk.exec.executionEnv.address, keyVal)) ≤ frk.exec.gasAvailable.toNat
    ∧ 3 ≤ (sloadFrame frk keyVal []).exec.gasAvailable.toNat
    ∧ ∃ words',
        memoryExpansionWords?
          (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.activeWords
          (UInt256.ofNat slot) 32 = some words'
        ∧ memExpansionChargeOf
            (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec words'
            ≤ (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.gasAvailable.toNat
        ∧ Gverylow ≤ ((pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.gasAvailable
            - UInt64.ofNat (memExpansionChargeOf
                (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec words')).toNat := by
  have hcsK : CleanHaltsNonException frk := cleanHaltsNonException_forward hcs hmrk.runs
  have hstkK : frk.exec.stack = keyVal :: [] := by
    rw [hmrk.stack, hstk0, ← hkeyval]; rfl
  have hszK : frk.exec.stack.size ≤ 1024 := by rw [hstkK]; simp [Stack.size]
  obtain ⟨hgasSload, hsloadNext⟩ :=
    next_sload_of_cleanHalt frk keyVal [] hcsK hdecSLOAD hstkK hszK
  have hstepSload : StepsTo frk (sloadFrame frk keyVal []) :=
    stepsTo_sloadFrame frk keyVal [] hdecSLOAD hstkK hszK hgasSload
  have hcsSload : CleanHaltsNonException (sloadFrame frk keyVal []) :=
    cleanHaltsNonException_forward hcsK (Runs.single hstepSload)
  have hstkSload : (sloadFrame frk keyVal []).exec.stack
      = (Evm.State.sload
          ({ frk.exec with gasAvailable := frk.exec.gasAvailable
              - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                  (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2 :: [] := by
    show (BytecodeLayer.Dispatch.sloadPost frk.exec keyVal []).stack = _
    dsimp only [BytecodeLayer.Dispatch.sloadPost, ExecutionState.replaceStackAndIncrPC, Stack.push]
  have hszSload : (sloadFrame frk keyVal []).exec.stack.size + 1 ≤ 1024 := by
    rw [hstkSload]; simp [Stack.size]
  obtain ⟨hgasPush, hpushNext⟩ :=
    next_push_of_cleanHalt (sloadFrame frk keyVal []) .PUSH32 (UInt256.ofNat slot) 32 hcsSload
      (by decide) hdecPUSH (by decide) (by decide) hszSload
  have hgasPush' : 3 ≤ (sloadFrame frk keyVal []).exec.gasAvailable.toNat := by
    have : Gverylow = 3 := rfl; omega
  have hstepPush : StepsTo (sloadFrame frk keyVal [])
      (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32) :=
    stepsTo_pushFrameW (sloadFrame frk keyVal []) .PUSH32 (UInt256.ofNat slot) 32 (by decide)
      hdecPUSH (by decide) (by decide) hgasPush hszSload
  have hcsPush : CleanHaltsNonException
      (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32) :=
    cleanHaltsNonException_forward hcsSload (Runs.single hstepPush)
  have hstkM : (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.stack
      = UInt256.ofNat slot :: (sloadFrame frk keyVal []).exec.stack := by
    show (({ (sloadFrame frk keyVal []).exec with
        gasAvailable := (sloadFrame frk keyVal []).exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
      ).replaceStackAndIncrPC ((sloadFrame frk keyVal []).exec.stack.push (UInt256.ofNat slot))
        (pcΔ := 33)).stack = _
    dsimp only [ExecutionState.replaceStackAndIncrPC, Stack.push]
  have hstkM' : (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.stack
      = UInt256.ofNat slot
        :: (Evm.State.sload
              ({ frk.exec with gasAvailable := frk.exec.gasAvailable
                  - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                      (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2 :: [] := by
    rw [hstkM, hstkSload]
  have hszM : (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32).exec.stack.size ≤ 1024 := by
    rw [hstkM']; simp [Stack.size]
  obtain ⟨words', hmem, hgasMem, hgasMstore, _⟩ :=
    next_mstore_of_cleanHalt (pushFrameW (sloadFrame frk keyVal []) (UInt256.ofNat slot) 32)
      (UInt256.ofNat slot)
      (Evm.State.sload
        ({ frk.exec with gasAvailable := frk.exec.gasAvailable
            - UInt64.ofNat (sloadCost (frk.exec.substate.accessedStorageKeys.contains
                (frk.exec.executionEnv.address, keyVal))) }.toState) keyVal).2
      [] hcsPush hdecMSTORE hstkM' hszM
  exact ⟨hgasSload, hgasPush', words', hmem, hgasMem, hgasMstore⟩

end Lir.CleanHaltExtract
