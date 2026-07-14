import LirLean.Realisability.Witness
import BytecodeLayer.Exec.WitnessChecks

/-!
# LirLean — Realisability spec, WITNESS PARAMS (R12a's concrete run)

The concrete `CallParams` witness for `exProg_satisfies_hypotheses` (R12a,
`RealisabilitySpec.lean`) and the sorry-free machinery its conjuncts need. This module
is SORRY-FREE; it reduces R12a to exactly TWO decidable `Bool` leaves
(`exProg_satisfies_hypotheses_of_checks`). Contents:

* `RunLog.cleanb` — the executable `Bool` twin of the log-side clean-scope predicate
  (`RunLog.clean` is a `Prop` match; a `cleanb = true` evaluation discharges it);
* `beginCall_inr_noErase` — the **engine fact** behind the `hseams.noErase` seam,
  DISCHARGED for the current exp003 engine: every one of the 10 precompile stubs
  returns, in its account-map component, either its input map (= `cp.accounts` after
  at most two balance-credit `insert`s — presence-monotone) or `∅` (in which case
  `beginCall`'s packaging falls back to the caller's original map). R12a deliberately
  doubles as the machine-check of this fact against the seam bundle
  (`Spec/Seams.lean`, `PrecompileAssumptions.noErase`);
* `callsCodeOk` — a fuel-indexed **trace checker** for the `hseams.callsCode` AND
  `hseams.createResolves` seams: it replays the deterministic top-level chain
  (`stepFrame` steps, returning CALLs, returning CREATEs), checks every issued
  `.needsCall`'s code source, and checks every issued `.needsCreate` with a
  terminating init child resumes successfully. Soundness (`callsCode_of_entryCheck`,
  `createResolves_of_entryCheck`) turns ONE `Bool` evaluation into BOTH
  reachable-frame universals — the chain is linear because
  `stepFrame`/`beginCall`/`drive`/the resumes are functions;
* `exParams` — the literal witness params: recipient `0x1234` (a `default` account —
  the executed code is pinned by `codeSource := .Code (lower exProg)`), callee `0x100`
  (an ordinary empty-code account, NOT a precompile address `1..10`), `value := 0`,
  gas `25000` — tuned so the recorded run halts cleanly after ONE block-1 loop
  iteration (measured landscape, native probe: block 0's cold SLOAD + cold nonzero
  SSTORE + cold CALL + spill traffic clear at ≥ 24850; at 25000 the first `t6 := gas`
  read is already below the `1000` threshold, so the loop exits at once with 179 gas
  left — a clean `.stop`, 2 recorded gas reads, 1 sload, 1 call);
* `exProg_satisfies_hypotheses_of_checks` — **the R12a reduction**: from the two `Bool`
  leaves `exCheck = true` (the recorded run exists and is clean) and
  `entryCallsCodeOk exParams 4096 = true` (the `CallsCode` trace check), the FULL R12a
  conjunction follows by real (sorry-free) assembly.

## Where the two leaves ARE discharged (`WitnessChecks.lean`, kernel-certified)

Both leaves are decidable and TRUE; plain `decide +kernel` on the raw evaluators is
measured-infeasible (`native_decide` is banned repo-wide). Two DISTINCT walls, found in
order:

1. **Fuel-peel memory blow-up** (the original measured ladder): the v4.30 kernel's
   lazy whnf explodes evaluating `driveLog` at the 54096 seed fuel. Gas-prefix ladder,
   kernel wall-clock: 100 ↦ 1s, 3000 ↦ 2s, 10000 ↦ 2s, 23000 ↦ 5s, 24400 ↦ 5s,
   24700 (dies AT the CALL charge) ↦ 5s; 24770+ ↦ OOM-killed (>30 GB — 60 GB, 10–15
   min, 96 GB machine). Fixed by `SegmentedEval.lean`: the run is a linear chain of
   ONE-fuel transitions (`nextLog`/`stepsLog`; the witness run is 39 transitions
   total), composed back to the fuel-indexed evaluator by the shift/final lemmas —
   no fuel peel, no laziness pile-up.

2. **The `USize` opacity wall** (found once the fuel peel was gone): every padded
   byte-window primitive routes through `ffi.ByteArray.zeroes (u : USize)`, and
   `USize` normalization is stuck on the OPAQUE `System.Platform.getNumBits` —
   platform-dependent BY DESIGN, so NO kernel evaluation can cross it (first forced
   at transition 20, the CALL descent's calldata window; located with a kernel-whnf
   stuck-head chaser). Fixed by `CheckedStep.lean`: a checked twin evaluator with
   `ℕ`-computed padding twins for exactly the poisoned arms (MLOAD/MSTORE/CALL
   calldata) under decidable `< 2 ^ 32` bound checks (both platforms agree there —
   `System.Platform.numBits_eq`), delegation everywhere else, and full soundness
   back to the real chain.

`WitnessChecks.lean` runs THREE flagged `decide +kernel` cranks — the two heavy leaf
evaluations over the checked twin (~13s / 5.5 GB each) plus the cheap `seedFuel`
arithmetic pin — and transports the verdicts to `exCheck = true` (`exCheck_true`) and
`entryCallsCodeOk exParams 4096 = true` (`entryCallsCodeOk_exParams`);
`exProg_satisfies_hypotheses` (R12a) is CLOSED from them, axiom-clean
(`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `ofReduceBool`).
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
