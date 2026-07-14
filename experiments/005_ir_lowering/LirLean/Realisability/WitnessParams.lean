import LirLean.Realisability.Witness
import BytecodeLayer.Exec.WitnessChecks

/-!
# LirLean — concrete realisability witness parameters

This module defines `exParams`, `exCheck`, and the IR-specific reduction
`exProg_satisfies_hypotheses_of_checks`. The generic executable checks and their
soundness results are re-exported for that reduction.
-/

namespace Lir

export BytecodeLayer.Exec.Recorder
  (RunLog.clean_of_cleanb beginCall_inr_noErase callsCodeOk_head callsCodeOk_step
   callsCodeOk_call callsCodeOk_create callsCode_of_callsCodeOk entryCallsCodeOk
   callsCode_of_entryCheck callsCodeOk_head_create createResolves_of_callsCodeOk
   createResolves_of_entryCheck)

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter



/-! ## §4 — the concrete witness params -/

/-- The witness self (recipient) address. Arbitrary non-precompile address. -/
def exSelf : AccountAddress := Fin.ofNat _ 0x1234

/-- The witness callee address (`exProg`'s CALL target, `t4 := 0x100`): an ordinary
code account slot — NOT a precompile (`1..10`). -/
def exCallee : AccountAddress := Fin.ofNat _ 0x100

/-- The witness caller address (not present in the account map; `value = 0` makes the
transfer prologue a no-op on it). -/
def exCaller : AccountAddress := Fin.ofNat _ 0xC0FFEE

/-- The recipient's account: `default` (empty storage/code — the executed code is
pinned by `codeSource`, and `exProg`'s SLOAD/SSTORE run against this storage). -/
def exAcc : Account := default

/-- The witness account map: the recipient and the (empty-code) callee. -/
def exAccounts : AccountMap :=
  (Batteries.RBMap.empty.insert exSelf exAcc).insert exCallee default

/-- **The R12a witness `CallParams`.** Gas `25000`: enough to clear `exProg`'s block 0
(cold SLOAD `2100` + cold zero→nonzero SSTORE `22100` + cold CALL `2600` net of the
callee's returned forward + the emitted PUSH/MSTORE spill traffic — measured floor
`24850`), small enough that the first block-1 `t6 := gas` read is already below the
`1000` loop threshold: the loop exits after ONE iteration with `179` gas left, a clean
`.stop` (probed landscape: `24800 ↦ OOG`, `24850 ↦ rem 29`, `25000 ↦ rem 179`,
`25800 ↦ 2 iterations`). Keeps the two kernel cranks minimal. -/
def exParams : CallParams :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := #[]
    accounts := exAccounts
    originalAccounts := exAccounts
    substate := default
    caller := exCaller
    origin := exCaller
    recipient := exSelf
    codeSource := .Code (Lir.lower exProg)
    gas := 25000
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 1
    canModifyState := true }

/-- The single-evaluation run check: the recording interpreter completes on
`lower exProg` from `exParams` at the seeded fuel AND the recorded run halted cleanly
(the `cleanb` twin). One `Bool`, so ONE evaluation certifies both the `hrun` and the
`hclean` conjuncts. **R12a leaf 1 of 2** — TRUE by native evaluation (module header);
its in-kernel discharge is the measured-infeasible crank. -/
def exCheck : Bool :=
  match runWithLog exParams (seedFuel exParams.gas) with
  | some log => log.cleanb
  | none => false

/-- The recipient account is present (the flagship's `hself` at the witness). -/
theorem exParams_self_present : exParams.accounts.find? exParams.recipient = some exAcc := by
  rfl

/-- The witness gas floor (the flagship's `hgas` at the witness). -/
theorem exParams_gas_floor : GasConstants.Gjumpdest ≤ exParams.gas.toNat := by
  decide

/-! ## §5 — the R12a reduction (sorry-free; the two `Bool` leaves are the whole residue)

`entryCallsCodeOk exParams 4096 = true` is **R12a leaf 2 of 2** (fuel `4096` covers the
~hundred-step top-level chain with slack). -/

/-- **The R12a reduction.** From the two decidable leaves — the recorded run exists
and is clean (`exCheck`), and the seam trace check passes (`entryCallsCodeOk`)
— the FULL `exProg_satisfies_hypotheses` conjunction follows: the definitional pins
are `rfl`, presence/gas-floor are the closed lemmas above, `hrun`/`hclean` fall out of
the `exCheck` match, and the seam structure combines the engine-level
`beginCall_inr_noErase` theorem with the checker soundness lemmas
`callsCode_of_entryCheck` + `createResolves_of_entryCheck` (one shared `Bool`
evaluation covers both reachable-frame seam faces; `exProg` is create-free, so the
create face is exercised vacuously — no reachable `.needsCreate`).
R12a (`RealisabilitySpec.lean`) = this theorem + the two leaves. -/
theorem exProg_satisfies_hypotheses_of_checks
    (hchk : exCheck = true)
    (hcc : entryCallsCodeOk exParams 4096 = true) :
    ∃ (params : CallParams) (log : RunLog) (acc : Account),
      params.codeSource = .Code (Lir.lower exProg)
      ∧ params.canModifyState = true
      ∧ params.accounts.find? params.recipient = some acc
      ∧ GasConstants.Gjumpdest ≤ params.gas.toNat
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ log.clean
      ∧ PrecompileAssumptions exProg params := by
  unfold exCheck at hchk
  revert hchk
  cases hrun : runWithLog exParams (seedFuel exParams.gas) with
  | none => exact fun hchk => Bool.noConfusion hchk
  | some log =>
    intro hcleanb
    exact ⟨exParams, log, exAcc, rfl, rfl, exParams_self_present, exParams_gas_floor,
      hrun, RunLog.clean_of_cleanb hcleanb,
      { noErase := beginCall_inr_noErase
        callsCode := callsCode_of_entryCheck hcc
        createResolves := createResolves_of_entryCheck hcc }⟩

end Lir
