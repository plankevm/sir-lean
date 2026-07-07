import LirLean.V2.Realisability.Machinery
import LirLean.V2.Drive.DriveSim

/-!
# LirLean v2 — the coupled run-producer `runFrom_of_driveCorrLog` (R11's terminal, WIP-only)

**EVERY `sorry` IN THIS FILE IS TRACKED DEBT.** This module is the tracked SKELETON for the
one obligation that gates the whole experiment: the coupled run-producer
`runFrom_of_driveCorrLog`, documented verbatim at
`LirLean/V2/Realisability/RealisabilitySpec.lean:224-248` as "THE BLOCKER (Route-A, NOT a
citable leaf)". It is the packaged existential the flagship `lower_conforms` (R11) and its
`lower_conforms_exact`/`lower_conforms_gasfree` siblings `obtain`, and — with the CREATE
channel wired (`docs/create/STATUS.md`) — it closes CALL and CREATE simultaneously.

## Why this is NOT assembly over citable leaves (the two documented reasons)

* **(a) unconditional `SimStmtStep` is unsatisfiable under the reshape.** The only in-tree
  run-producer `lower_conforms_cyclic'` (`V2/Drive/DriveSim.lean`) consumes an ALL-FRAMES
  `SimStmtStep` (`Sim/SimStmts.lean:66`) — a per-statement simulation with NO coupling
  antecedent. The reshaped `StmtTies'` (`Surface.lean:640`) can only conclude its arms UNDER
  the load-bearing `RecorderCoupled` antecedent (target-architecture §3); the coupling-free
  path is exactly the vacuity the reshape exists to kill (header lessons 1–3, `RealisabilitySpec`).
  So the producer cannot factor through `SimStmtStep`/`DriveStep`/`runFrom_of_driveCorr`; it must
  run its OWN walk carrying `DriveCorrLog` (which BUNDLES `RecorderCoupled`) and fire the Layer-C
  sim bricks ONLY at the coupled walk-frames — the `simStmt_coupled_*` family below.
* **(b) R6 `runs_atReachableBoundary` cannot supply `hrb` alone.** Its B2 side condition
  `(flatBytes prog).length ≤ 2 ^ 32` (`Machinery.lean:1509`) has no producer from `hwl` — no
  `WellFormedLowered` field asserts it directly, only per-cursor bounds. Threaded here as an
  explicit honest seam `hsize` (`boundaryWalk_of_wl` below); wiring it into the flagship's
  hypothesis surface is a tracked DECISION (see `docs/create/producer-plan.md`).

## Shape of the construction (see `docs/create/producer-plan.md` for the full plan)

The producer is a strong-`totalGas` induction (`runFrom_of_driveCorrLog_rec`) carrying the
coupled boundary invariant `DriveCorrLog` (Corr + clean-halt + coupling + presence + self/addr/
kind pins) TOGETHER with a `StreamsAligned` fact pinning the IR streams `(T, C, D)` to the
realised image of the un-consumed recorder suffixes. At each boundary a per-block step
`driveLogStep_of_block` either bottoms out (halt → the packaged `RunFromCoupled` = terminal
world+result equation + IR `RunFrom`) or advances to a strictly-smaller successor. Its statement
engine is the COUPLED block walk `simStmts_coupled_block`, which folds the per-statement coupled
steps `simStmt_coupled_*` — each firing the matching `StmtTies'` arm (coupling available) and
advancing the coupling suffix via exactly one R7 edge (`recorderCoupled_step_gas` / `_sload` /
`_step_other` / `recorderCoupled_call_extract`), consuming exactly the matching realised stream
head. This is the piece that does NOT exist as `SimStmtStep`.

Every declaration's docstring states the tractability and the exact bricks it fires. Registered
in the NON-DEFAULT `WIP` lean_lib; the default `LirLean` cone stays sorry-free and never imports
this module.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch

/-! ## §0 — the coupled-walk vocabulary (all REAL; no sorry)

The three helper predicates the producer's induction threads. `StreamsAligned` is the
positional bridge that turns the whole realised streams (`realisedGas`/`realisedCall`/
`realisedCreate`) at entry into the per-block head-consumption the IR `RunFrom` performs:
at every coupled boundary the IR streams `(T, C, D)` are exactly the realised image of the
un-consumed recorder suffixes `(gS, cS, log.creates)`. The sload suffix `sS` has no IR
stream (SLOAD consumes nothing on the IR side), so it is not aligned. The create channel is
pinned to the WHOLE `log.creates` (the coupling's `restart` field pins it whole; the walk
consumes no create until Step 8's `createSuffix` twin lands — `Surface.lean:526-531`). -/

/-- The IR streams `(T, C, D)` at a coupled boundary are the realised image of the recorder
suffixes: the gas trace IS the gas suffix, the call stream IS the `evmV2CallEntry` image of
the call suffix, and the create stream IS the (whole) realised create stream. REAL def. -/
def StreamsAligned (self : AccountAddress) (log : RunLog)
    (gS : List Word) (cS : List CallRecord)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  T = gS ∧ C = callStreamOf cS self ∧ D = createStreamOf log.creates self

/-- The producer's per-boundary OUTPUT: some IR observable `O` whose world AND result equal
the `observe` of the bytecode frame's halting terminal (reachable from `fr`), together with
the IR `RunFrom` from `(st, T, C, D)` at `L` to `O`. This is the packaged shape the flagship's
blocker `obtain` consumes (its `hworld`+`hrunfrom` conjuncts, at the entry boundary). REAL def. -/
def RunFromCoupled (prog : Program) (self : AccountAddress)
    (st : IRState) (fr : Frame) (L : Label)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  ∃ O : Observable,
    (∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world
        ∧ (observe self (endFrame last haltSig)).result = O.result)
    ∧ RunFrom prog st T C D L O

/-- The COUPLED per-block obligation (the `DriveLogStep` analogue of `DriveSim`'s `DriveStep`,
but carrying the coupling + alignment). From a coupled boundary either the block HALTS
(`RunFromCoupled`) or it takes an EDGE to a strictly-smaller-`totalGas` successor whose
`DriveCorrLog` + `StreamsAligned` are re-established, with the bytecode forward run `Runs fr fr'`
and the IR one-block continuation. REAL def. -/
def DriveLogStep (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream)
    (gS : List Word) (sS : List Nat) (cS : List CallRecord) : Prop :=
  RunFromCoupled prog self st fr L T C D
  ∨
  (∃ (st' : IRState) (T' : Trace) (C' : CallStream) (D' : CreateStream)
      (succ : Label) (fr' : Frame) (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord),
      Runs fr fr'
    ∧ DriveCorrLog prog sloadChg log self st' fr' succ gS' sS' cS'
    ∧ StreamsAligned self log gS' cS' T' C' D'
    ∧ totalGas [] (.inl fr') < totalGas [] (.inl fr)
    ∧ (∀ O, RunFrom prog st' T' C' D' succ O → RunFrom prog st T C D L O))

/-- The result of ONE coupled statement step at cursor `(L, pc)`: the IR `EvalStmt` of `s`
(consuming the aligned stream heads), the matching bytecode `Runs fr fr'` re-establishing
`Corr` at `pc+1` with empty stack, and the advanced coupling `RecorderCoupled` + `StreamsAligned`
at the tail. REAL def. -/
def CoupledAdvance (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (L : Label) (pc : Nat) (st : IRState) (fr : Frame)
    (T : Trace) (C : CallStream) (D : CreateStream) (s : Stmt) : Prop :=
  ∃ (st' : IRState) (fr' : Frame) (T' : Trace) (C' : CallStream) (D' : CreateStream)
    (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord),
    EvalStmt prog st T C D s st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 st' fr' L (pc + 1)
    ∧ fr'.exec.stack = []
    ∧ RecorderCoupled log fr' gS' sS' cS'
    ∧ StreamsAligned self log gS' cS' T' C' D'

/-! ## §1 — entry seeds (leaf-most; assembly over green lemmas)

The entry `DriveCorrLog` and the entry `StreamsAligned` — the base of the induction. Both are
assembly of already-green lemmas; the only content is discharging `entry_corr`'s `StorageAgree`
against the definitional `entryState` and pinning the `codeFrame`'s address/kind. -/

/-- **P1a — entry stream alignment.** At the entry frame the realised streams
(`realisedGas log` / `realisedCall log self` / `realisedCreate log self`) are the alignment of
the WHOLE recorder streams (`log.gas` / `log.calls` / `log.creates`), which are exactly the
entry coupling suffixes (`recorderCoupled_entry`). Near-`rfl` (`realisedGas`/`realisedCall`/
`realisedCreate`/`callStreamOf`/`createStreamOf` unfold). TRACTABILITY: now. -/
theorem streamsAligned_entry (self : AccountAddress) (log : RunLog) :
    StreamsAligned self log log.gas log.calls
      (realisedGas log) (realisedCall log self) (realisedCreate log self) :=
  -- `realisedGas log ≡ log.gas`, `realisedCall log self ≡ callStreamOf log.calls self`,
  -- `realisedCreate log self ≡ createStreamOf log.creates self` all by definition.
  ⟨rfl, rfl, rfl⟩

/-- **P1b — the entry coupled boundary.** From the flagship hypotheses, assemble the entry
`DriveCorrLog` at `prog.entry` on the whole recorder suffixes, at the entry block's
POST-`JUMPDEST` landing frame `fr₀'` (with the bytecode `Runs fr₀ fr₀'` witness). Fires:
`corr_at_jumpdest_landing` (`Corr`, with `StorageAgree` reconciled from the definitional
`entryState` against the `codeFrame`'s `codeAccounts` storage lens — balance credit/debit leave
storage untouched), `cleanHalts_of_runWithLog` (clean-halt scope, then
`cleanHaltsNonException_forward` to the landing), `ClosedCFG.entry_present` (presence),
`selfPresent_codeFrame` (self-presence, transported across the `JUMPDEST` step whose
`jumpdestPost` leaves `accounts`/`executionEnv` untouched), the `codeFrame` address/kind pins
(preserved by the `JUMPDEST` step, which only moves `exec.pc`/`gas`), and `recorderCoupled_entry`
+ `recorderCoupled_stepsTo_other` (coupling, carried across the non-gas/non-sload `JUMPDEST`
step).

STATEMENT CORRECTION (reported to the lead): the skeleton originally pinned the `DriveCorrLog`
frame to the beginCall frame `fr₀` (`= codeFrame params (lower prog)`, pc `= offsetTable
entry.idx = 0`). That is UNPROVABLE: `Corr`'s `pc_eq` at cursor `(prog.entry, 0)` demands
`pc = pcOf prog prog.entry 0 = offsetTable entry.idx + 1` (`pcOf_zero`, the `+1` skipping the
leading `JUMPDEST`), which `codeFrame.pc = 0` does not meet — every `DriveCorrLog` boundary frame
is a POST-`JUMPDEST` landing (cf. the edge disjunct of `driveLogStep_of_block`, which lands at
`jumpdestFrame fj`). The corrected conclusion returns that landing `fr₀'` together with `Runs fr₀
fr₀'` (exactly the "transport across the internal `Runs`" the plan note anticipates), which R11
bridges to the beginCall frame via `Runs.trans`. Also threads the create-resolves seam `hcreate`
(present already on R11) that `cleanHalts_of_runWithLog` needs. TRACTABILITY: now. -/
theorem driveCorrLog_entry {prog : Program} {sloadChg : Tmp → ℕ} {params : CallParams}
    {log : RunLog} {acc : Account} {fr₀ : Frame}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params)
    (hbegin : beginCall params = .inl fr₀)
    (hcreate : ∀ fr', ReachableFrom params fr' → CreateResolves fr')
    (hne : ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt → HaltNonException halt) :
    ∃ fr₀' : Frame, Runs fr₀ fr₀'
      ∧ DriveCorrLog prog sloadChg log params.recipient (entryState params) fr₀' prog.entry
          log.gas log.sloads log.calls := by
  -- the beginCall frame is the entry `codeFrame`.
  have hfr : fr₀ = codeFrame params (lower prog) :=
    (Sum.inl.injEq _ _).mp (hbegin.symm.trans (beginCall_code params (lower prog) hcode))
  subst hfr
  -- entry block, present and offset-0.
  obtain ⟨bentry, hbentry⟩ := hwl.closed.entry_present
  have hbtl : prog.blocks.toList[prog.entry.idx]? = some bentry := toList_of_blockAt hbentry
  have hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32 :=
    hwl.closed.entry_bound
  have hoff0 : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx = 0 := by
    unfold offsetTable; rw [hwl.entry0]; simp
  -- the entry `codeFrame` field reductions.
  have hpc : (codeFrame params (lower prog)).exec.pc
      = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx) := by
    rw [codeFrame_pc, hoff0]; rfl
  have hcodeF : (codeFrame params (lower prog)).exec.executionEnv.code = lower prog :=
    codeFrame_code params (lower prog)
  have hvalid : (codeFrame params (lower prog)).validJumps
      = validJumpDests (codeFrame params (lower prog)).exec.executionEnv.code 0 := by
    rw [codeFrame_validJumps, codeFrame_code]
  have hstk : (codeFrame params (lower prog)).exec.stack = [] := codeFrame_stack params (lower prog)
  have hmodF : (codeFrame params (lower prog)).exec.executionEnv.canModifyState = true := by
    rw [codeFrame_canMod]; exact hmod
  have hgasF : GasConstants.Gjumpdest ≤ (codeFrame params (lower prog)).exec.gasAvailable.toNat := by
    rw [codeFrame_gas]; exact hgas
  have hsz : (codeFrame params (lower prog)).exec.stack.size ≤ 1024 := by
    rw [hstk]; show (0 : ℕ) ≤ 1024; omega
  have hdec : decode (codeFrame params (lower prog)).exec.executionEnv.code
      (codeFrame params (lower prog)).exec.pc = some (.Smsf .JUMPDEST, .none) := by
    rw [hcodeF, hpc]; exact decode_at_block_offset_jumpdest prog prog.entry bentry hbtl hbound
  -- the entry STORAGE tie: reconcile `entryState`'s params-storage lens with `codeFrame`'s
  -- `codeAccounts` lens (balance credit/debit leave the recipient's storage untouched).
  have hstore : StorageAgree (entryState params) (codeFrame params (lower prog)) := by
    intro k
    have hrhs : (entryState params).world k = acc.lookupStorage k := by
      show (params.accounts.find? params.recipient).option 0 (fun a => a.lookupStorage k)
          = acc.lookupStorage k
      rw [hself]; rfl
    show ((codeAccounts params).find? params.recipient).option 0 (fun a => a.lookupStorage k)
        = (entryState params).world k
    rw [hrhs]
    unfold codeAccounts
    rw [hself]
    have hm1rec : (params.accounts.insert params.recipient
          { acc with balance := acc.balance + params.value }).find? params.recipient
        = some { acc with balance := acc.balance + params.value } :=
      BytecodeLayer.Maps.accounts_find?_insert_self _ _ _
    cases hcal : (params.accounts.insert params.recipient
        { acc with balance := acc.balance + params.value }).find? params.caller with
    | none => simp only [hcal]; rw [hm1rec]; rfl
    | some cacc =>
      simp only [hcal]
      by_cases hcr : params.caller = params.recipient
      · have hcacc : cacc = { acc with balance := acc.balance + params.value } := by
          rw [hcr, hm1rec] at hcal; exact (Option.some.injEq _ _).mp hcal.symm
        subst hcacc
        rw [hcr, BytecodeLayer.Maps.accounts_find?_insert_self]; rfl
      · rw [BytecodeLayer.Maps.accounts_find?_insert_of_ne _ _ (fun h => hcr h.symm), hm1rec]; rfl
  -- `Corr` at the post-`JUMPDEST` landing `jumpdestFrame (codeFrame …)` at `(prog.entry, 0)`.
  obtain ⟨hjdrun, hjdcorr⟩ :=
    corr_at_jumpdest_landing (prog := prog) (sloadChg := sloadChg) (obs := 0)
      (st := entryState params) hbtl hpc hcodeF hvalid hstk hmodF hstore
      (by unfold entryState; exact defsSound_entry prog _)
      (by intro t ht; simp [entryState] at ht)
      (by intro t slot v _ hloc; simp [entryState] at hloc) hdec hgasF
  refine ⟨jumpdestFrame (codeFrame params (lower prog)), hjdrun, ?_⟩
  -- the entry clean-halt scope (via modellability), forwarded to the landing.
  have hcc : ∀ fr', Runs (codeFrame params (lower prog)) fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨_, hbegin, hr⟩
  have hcr : ∀ fr', Runs (codeFrame params (lower prog)) fr' → CreateResolves fr' :=
    fun fr' hr => hcreate fr' ⟨_, hbegin, hr⟩
  have hclean₀ : CleanHaltsNonException (codeFrame params (lower prog)) :=
    cleanHalts_of_runWithLog (prog := prog) hrun hbegin hcr hcc hne
  -- entry coupling, carried across the `JUMPDEST` step.
  have hcp₀ : RecorderCoupled log (codeFrame params (lower prog)) log.gas log.sloads log.calls :=
    recorderCoupled_entry hrun hbegin
  have hstepsTo : StepsTo (codeFrame params (lower prog))
      (jumpdestFrame (codeFrame params (lower prog))) :=
    stepsTo_of_next (stepFrame_jumpdest (codeFrame params (lower prog)) hdec hsz hgasF)
  have hnotgas : isGasOp (codeFrame params (lower prog)) = false := by
    unfold isGasOp; rw [hdec]; rfl
  have hnotsload : isSloadOp (codeFrame params (lower prog)) = false := by
    unfold isSloadOp; rw [hdec]; rfl
  -- self-presence at the entry frame, transported across the `JUMPDEST` step.
  have hsp₀ : SelfPresent (codeFrame params (lower prog)) :=
    selfPresent_codeFrame params (lower prog) hself
  exact
    { corr := hjdcorr
      cleanHalts := cleanHaltsNonException_forward hclean₀ hjdrun
      present := ⟨bentry, hbentry⟩
      selfPresent := by obtain ⟨a, ha⟩ := hsp₀; exact ⟨a, ha⟩
      addrPin := rfl
      kindPin := ⟨⟨params.createdAccounts, params.accounts, params.substate⟩, rfl⟩
      coupled := recorderCoupled_stepsTo_other hcp₀ hnotgas hnotsload hstepsTo }

/-! ## §2 — the per-statement COUPLED steps (the crux; reason (a))

One lemma per statement shape. Each takes the cursor statement, the `Corr` at `(L, pc)`, the
coupling `RecorderCoupled log fr …`, the clean-halt scope, the `StreamsAligned` fact, and the
matching `StmtTies'` arm output (produced by R10a `stmtTies'_of_runWithLog`), and produces the
`CoupledAdvance`. The IR `EvalStmt` is built from the aligned stream head; the bytecode `Runs`
from the Layer-C sim brick fired AT THE COUPLED FRAME; the coupling advance from the matching R7
edge. None of these factor through the unconditional `SimStmtStep`.

`sloadChg` is fixed to a chosen value once inside the walk (the sim bricks are `∀ sloadChg`;
the producer picks the canonical one). We leave it a parameter here. -/

/-- **Read-implies-bound.** If an expression `E` evaluates to `some _` and it reads `t`
(`usesInExpr t E ≠ 0`), then `t` is bound (`st.locals t ≠ none`). The value channel of
`evalExpr` short-circuits to `none` on any unbound operand. REAL; no sorry. -/
private theorem evalExpr_reads_bound {st : IRState} {t : Tmp} :
    ∀ {E : Expr} {W : Word}, evalExpr st 0 E = some W → usesInExpr t E ≠ 0 →
      st.locals t ≠ none := by
  intro E W heval hu hnone
  cases E with
  | imm _  => simp [usesInExpr] at hu
  | gas    => simp [usesInExpr] at hu
  | slot _ => simp [usesInExpr] at hu
  | tmp t' =>
      simp only [usesInExpr] at hu
      by_cases ht' : t' = t
      · subst ht'; simp only [evalExpr] at heval; rw [hnone] at heval
        simp at heval
      · simp [ht'] at hu
  | sload k =>
      simp only [evalExpr] at heval
      simp only [usesInExpr] at hu
      have hk_bound : st.locals k ≠ none := by intro h; rw [h] at heval; simp at heval
      by_cases hk : k = t
      · subst hk; exact hk_bound hnone
      · simp [hk] at hu
  | add a b =>
      simp only [evalExpr] at heval
      simp only [usesInExpr] at hu
      have ha : st.locals a ≠ none := by intro h; rw [h] at heval; simp at heval
      have hb : st.locals b ≠ none := by
        intro h; rw [h] at heval; cases hla : st.locals a <;> simp [hla] at heval
      by_cases hat : a = t
      · subst hat; exact ha hnone
      · by_cases hbt : b = t
        · subst hbt; exact hb hnone
        · simp [hat, hbt] at hu
  | lt a b =>
      simp only [evalExpr] at heval
      simp only [usesInExpr] at hu
      have ha : st.locals a ≠ none := by intro h; rw [h] at heval; simp at heval
      have hb : st.locals b ≠ none := by
        intro h; rw [h] at heval; cases hla : st.locals a <;> simp [hla] at heval
      by_cases hat : a = t
      · subst hat; exact ha hnone
      · by_cases hbt : b = t
        · subst hbt; exact hb hnone
        · simp [hat, hbt] at hu

/-- **DefsSound self-repair across a recomputable pure rebind.** For a RECOMPUTABLE target
`t` (`¬ NonRecomputable`) the strong `DefsSound` is preserved by `t := e` with no live-scope
side conditions: `DefsSound` at `st` already forces `t`'s current binding (if any) to equal
the recompute `w`, so either the rebind is a no-op (loop re-entry) or `t` was unbound (so no
reader of `t` could have been soundly bound). This is exactly why the plain-assign arm needs
neither the self-read (`usesInExpr t e = 0`) nor the define-before-use scoping clauses that
`StepScopedS` deliberately dropped (header lesson 8). REAL; no sorry. -/
private theorem defsSound_setLocal_recomputable {prog : Program} {st : IRState}
    {t : Tmp} {e : Expr} {w : Word}
    (hnr : ¬ NonRecomputable prog t)
    (hdef : rematOf prog t = some e)
    (hv : evalExpr st 0 e = some w)
    (hsound : DefsSound prog st) :
    DefsSound prog (st.setLocal t w) := by
  -- `DefsSound` pins `t`'s current binding: it is either absent or already `w`.
  have hst_cases : st.locals t = none ∨ st.locals t = some w := by
    cases hlt : st.locals t with
    | none => exact Or.inl rfl
    | some v =>
        have hev : some v = evalExpr st 0 e := hsound t e v hdef hnr hlt
        rw [hv] at hev
        right; exact hev
  rcases hst_cases with hstn | hstw
  · -- `t` unbound: no bound reader of `t`, so recompute is unchanged for every sound tmp.
    intro t₀ e₀ w₀ hdef₀ hnr₀ hlocal₀
    by_cases heqt : t₀ = t
    · subst t₀
      have he₀ : e₀ = e := Option.some.inj (hdef₀.symm.trans hdef)
      subst e₀
      have hw₀ : w₀ = w := by
        have h1 : (st.setLocal t w).locals t = some w := by simp [IRState.setLocal]
        rw [h1] at hlocal₀; exact (Option.some.inj hlocal₀).symm
      subst w₀
      have hu : usesInExpr t e = 0 := by
        by_contra hu; exact (evalExpr_reads_bound hv hu) hstn
      rw [evalExpr_setLocal_of_unused hu, hv]
    · have hl' : st.locals t₀ = some w₀ := by
        simp only [IRState.setLocal, if_neg heqt] at hlocal₀; exact hlocal₀
      have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hl'
      have hu : usesInExpr t e₀ = 0 := by
        by_contra hu; exact (evalExpr_reads_bound hprev.symm hu) hstn
      rw [evalExpr_setLocal_of_unused hu]; exact hprev
  · -- `t` already bound to `w`: the rebind is a no-op, so `DefsSound` carries over verbatim.
    have heq : st.setLocal t w = st := by
      have hfun : (fun t' => if t' = t then some w else st.locals t') = st.locals := by
        funext t'; by_cases h : t' = t
        · subst h; rw [if_pos rfl]; exact hstw.symm
        · rw [if_neg h]
      show { st with locals := fun t' => if t' = t then some w else st.locals t' } = st
      rw [hfun]
    rw [heq]; exact hsound

/-- **P2-assignPure — the plain-assign coupled step** (neither `.gas` nor `.sload`). Fires
`StmtTies'` arm (1) (not-spilled + `StepScopedS` + post-state scoping + `MemRealises`), builds
the `EvalStmt.assignPure` (consuming no stream head — all suffixes/streams unchanged), the
reflexive bytecode `Runs` (a rematerialised assign emits no bytes, `emitStmt_assign_remat`),
and re-establishes `Corr` at `(L, pc+1)`. The coupling and alignment ride across UNCHANGED
(the frame does not move). The one non-trivial `Corr` clause — strong `DefsSound` at the
post-state — is discharged by `defsSound_setLocal_recomputable`: the arm's `wellScoped`
conclusion at `t` plus the not-spilled clause give `¬ NonRecomputable t`, which makes the
rebind DefsSound-self-repairing (no live-scope clause required). The simplest arm.
TRACTABILITY: now. -/
theorem simStmt_coupled_assignPure {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {t : Tmp} {e : Expr} {w : Word} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t e))
    (hne : e ≠ .gas) (hns : ∀ k, e ≠ .sload k)
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS T C D)
    (hv : evalExpr st 0 e = some w)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.assign t e) := by
  -- Fire `StmtTies'` arm (1) at this cursor with the coupling + clean-halt in hand.
  obtain ⟨hslot, hstepS, hscoped', hmem'⟩ :=
    hties.1 pc t e w st fr gS sS cS hcur hne hns hcorr hcp hch hv
  -- The registered def and the recomputability of the (non-spilled) target.
  have hdef : rematOf prog t = some e := hstepS.1 hne hns
  have hnr : ¬ NonRecomputable prog t := by
    have hd := (hscoped' t (by simp [IRState.setLocal])).1
    rcases hd with h | ⟨n, hn⟩
    · exact h
    · exact absurd hn (hslot n)
  -- The IR cursor advances by a zero-length emit, so the byte offset is unchanged.
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  have hpc : pcOf prog L (pc + 1) = pcOf prog L pc := by
    rw [pcOf_succ prog L b pc (.assign t e) hbt hcur,
        emitStmt_assign_remat (defsOf prog) (recomputeFuel prog) t e hslot]
    simp
  -- The post-state's strong `DefsSound` (self-repair; no live-scope clause).
  have hsound' : DefsSound prog (st.setLocal t w) :=
    defsSound_setLocal_recomputable hnr hdef hv hcorr.defsSound
  -- Package: `st' = st.setLocal t w`, `fr' = fr`, streams/suffixes UNCHANGED.
  refine ⟨st.setLocal t w, fr, T, C, D, gS, sS, cS,
    EvalStmt.assignPure (prog := prog) (T := T) (C := C) (D := D) hne hv,
    Runs.refl fr, ?_, hcorr.stack_nil, hcp, hal⟩
  exact
    { pc_eq := by rw [hpc]; exact hcorr.pc_eq
      code_eq := hcorr.code_eq
      validJumps_eq := hcorr.validJumps_eq
      stack_nil := hcorr.stack_nil
      can_modify := hcorr.can_modify
      storage := hcorr.storage
      defsSound := hsound'
      wellScoped := hscoped'
      memAgree := hmem' }

/-- **P2-gas — the spilled-`.gas` coupled step (THE R1 CONJUNCT at work).** Fires `StmtTies'`
arm (3) whose gas-suffix head equation IS `gas_suffix_head_realised` (R1), the in-tree
`sim_assign_gas_lowered` brick, and `recorderCoupled_step_gas` (R7b) to consume the gas head.
The alignment `T = gS` forces the IR `EvalStmt.assignGas` to consume exactly the head R7b pins.
Depends on R1 (green — `gas_suffix_head_realised`) + the gas sim brick. TRACTABILITY: hard. -/
theorem simStmt_coupled_gas {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {t : Tmp} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t .gas))
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS T C D)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.assign t .gas) := by
  sorry

/-- **P2-sload — the spilled-`.sload` coupled step.** Fires `StmtTies'` arm (2) (the read value
is the storage lens `st.world kv` at the antecedent-pinned key binding), the in-tree
`sim_assign_sload` brick, and `recorderCoupled_sload` (R7c) to advance the sload suffix. No IR
stream head consumed (SLOAD reads the IR world, not a stream — `EvalStmt.assignPure` on
`.sload k`). Twin of P2-gas on the sload channel. TRACTABILITY: hard. -/
theorem simStmt_coupled_sload {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {t k : Tmp} {kv : Word} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t (.sload k)))
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS T C D)
    (hkey : st.locals k = some kv)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.assign t (.sload k)) := by
  sorry

/-! ### S1 — the coupling fold over a `materialise` run (`recorderCoupled_matRuns`)

The missing Runs-level fold (Block-#1 plan §S1): running `materialiseExpr defs fuel e` for a
non-`gas`/non-`sload` `e` emits ONLY `PUSH32`/`MLOAD`/`ADD`/`LT` frames (a bare `.gas`/`.sload`
is never materialised — Phase B/C), each of which is a non-recording top-level `.next` step
(`isGasOp = false`, `isSloadOp = false` from the `MatDec` decode). So the recorder coupling
`RecorderCoupled log fr gS sS cS` rides UNCHANGED across the whole run. Proved as a JOINT
recursion mirroring `Lir.materialise_runs` field-for-field (so the endpoint frame carries BOTH
the `MatRuns` bundle the SSTORE `Corr`-work consumes AND the coupling), inserting one
`recorderCoupled_step_other` (R7d) per emitted opcode frame. REAL; no sorry. -/

open GasConstants in
/-- **S1 — `recorderCoupled_matRuns`.** The joint `materialise_runs` + coupling fold. Same
premises + conclusion as `Lir.materialise_runs`, plus: it CARRIES the recorder coupling
`RecorderCoupled log fr gS sS cS` across the whole run to the endpoint. Every materialise frame
decodes to `PUSH32`/`MLOAD`/`ADD`/`LT` (never `GAS`/`SLOAD`), so each step is non-recording
(`recorderCoupled_step_other`, R7d). Mirror of the green `materialise_runs` recursion. -/
theorem recorderCoupled_matRuns {prog : Program} (sloadChg : Tmp → ℕ)
    (fuel : Nat) (st : IRState) (obs : Word) (log : RunLog)
    (gS : List Word) (sS : List Nat) (cS : List CallRecord) :
    ∀ (e : Expr) (w : Word) (fr : Frame),
      MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg fuel fr.exec.pc e →
      DefsSound prog st →
      (∀ t, st.locals t ≠ none →
        (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
        ∧ defsOf prog t ≠ none) →
      StorageAgree st fr →
      e ≠ .gas →
      (∀ k, e ≠ .sload k) →
      MemRealises prog st fr →
      evalExpr st obs e = some w →
      (chargeOf (defsOf prog) sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat →
      fr.exec.stack.size + (chargeOf (defsOf prog) sloadChg fuel e).length ≤ 1024 →
      RecorderCoupled log fr gS sS cS →
      ∃ fr', MatRuns (defsOf prog) sloadChg fuel e w fr fr'
        ∧ RecorderCoupled log fr' gS sS cS := by
  set defs := defsOf prog with hdefs
  induction fuel with
  | zero =>
      intro e w fr hdec hsound hscoped hstore hne hnsl hmemreal heval hgas hstk hcp
      cases e with
      | imm v =>
          have hwv : w = v := (Option.some.inj heval).symm
          have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
              = some (.Push .PUSH32, some (v, 32)) := by rw [matDec_imm] at hdec; exact hdec
          have hg3 : 3 ≤ fr.exec.gasAvailable.toNat := by
            rw [chargeOf_imm] at hgas; simpa [show Gverylow = 3 from rfl] using hgas
          have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
            rw [chargeOf_imm] at hstk; simpa using hstk
          refine ⟨pushFrameW fr v 32, ?_, ?_⟩
          · rw [hwv]; exact matRuns_imm defs sloadChg 0 fr v hdec hgas hszfr
          · exact recorderCoupled_step_other hcp
              (by unfold isGasOp; rw [hdec']; rfl) (by unfold isSloadOp; rw [hdec']; rfl)
              (stepFrame_push fr .PUSH32 v 32 (by decide) hdec' (by decide) (by decide) hg3 hszfr)
      | slot slot => exact absurd heval (by simp [evalExpr])
      | _ => exact absurd hdec (by simp [MatDec])
  | succ f ih =>
      intro e w fr hdec hsound hscoped hstore hne hnsl hmemreal heval hgas hstk hcp
      cases e with
      | imm v =>
          have hwv : w = v := (Option.some.inj heval).symm
          have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
              = some (.Push .PUSH32, some (v, 32)) := by rw [matDec_imm] at hdec; exact hdec
          have hg3 : 3 ≤ fr.exec.gasAvailable.toNat := by
            rw [chargeOf_imm] at hgas; simpa [show Gverylow = 3 from rfl] using hgas
          have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
            rw [chargeOf_imm] at hstk; simpa using hstk
          refine ⟨pushFrameW fr v 32, ?_, ?_⟩
          · rw [hwv]; exact matRuns_imm defs sloadChg (f + 1) fr v hdec hgas hszfr
          · exact recorderCoupled_step_other hcp
              (by unfold isGasOp; rw [hdec']; rfl) (by unfold isSloadOp; rw [hdec']; rfl)
              (stepFrame_push fr .PUSH32 v 32 (by decide) hdec' (by decide) (by decide) hg3 hszfr)
      | slot slot => exact absurd heval (by simp [evalExpr])
      | gas => exact absurd rfl hne
      | sload k => exact absurd rfl (hnsl k)
      | tmp t =>
          have hloc : st.locals t = some w := heval
          cases ht : defs t with
          | none =>
              exact absurd (by rw [← hdefs, ht] : defsOf prog t = none)
                (hscoped t (by rw [hloc]; simp)).2
          | some e' =>
              rcases Classical.em (∃ slot, e' = .slot slot) with ⟨slot, he'⟩ | hncr
              · -- == the memory value-channel readback arm (PUSH32 slot ; MLOAD) ==
                  have hdeft : defsOf prog t = some (.slot slot) := by rw [← hdefs, ht, he']
                  have hmd : MatDec fr.exec.executionEnv.code defs sloadChg (f + 1) fr.exec.pc
                      (.tmp t) := hdec
                  rw [matDec_tmp_some fr.exec.executionEnv.code defs sloadChg f fr.exec.pc t e' ht,
                      he', matDec_slot] at hmd
                  obtain ⟨hdpush, hdmload⟩ := hmd
                  obtain ⟨hcm, ham, hreal, hval⟩ := hmemreal t slot w hdeft hloc
                  have hmexp : materialiseExpr defs (f + 1) (.tmp t)
                      = emitImm (UInt256.ofNat slot) ++ [Byte.mload] := by
                    rw [materialiseExpr_tmp_some defs f t e' ht, he', materialiseExpr_slot]
                  have hchg : chargeOf defs sloadChg (f + 1) (.tmp t) = [Gverylow, Gverylow] := by
                    rw [chargeOf_tmp_some defs sloadChg f t e' ht, he']; cases f <;> rfl
                  have hsum2 : (chargeOf defs sloadChg (f + 1) (.tmp t)).sum = Gverylow + Gverylow := by
                    rw [hchg]; simp [List.sum_cons]
                  have hgv3 : (Gverylow : ℕ) = 3 := rfl
                  have hgasPush : 3 ≤ fr.exec.gasAvailable.toNat := by
                    rw [hsum2, hgv3] at hgas; omega
                  have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
                    rw [hchg] at hstk
                    simp only [List.length_cons, List.length_nil] at hstk; omega
                  -- == step 1: PUSH32 slot ==
                  obtain ⟨hpushrun, hpushstk⟩ :=
                    sim_imm fr (UInt256.ofNat slot) hdpush hgasPush hszfr
                  set frp := pushFrameW fr (UInt256.ofNat slot) 32 with hfrp
                  have hfrpcode : frp.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
                  have hfrpmem : frp.exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl
                  have hfrpaw : frp.exec.toMachineState.activeWords
                      = fr.exec.toMachineState.activeWords := rfl
                  have hfrppc : frp.exec.pc = fr.exec.pc + UInt32.ofNat 33 := by
                    rw [hfrp, pushFrameW_pc, push32_pcΔ]
                  have hfrpstk : frp.exec.stack = (UInt256.ofNat slot) :: fr.exec.stack := by
                    rw [hpushstk]; rfl
                  have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; simp; omega
                  -- coupling across the PUSH32 step (non-recording).
                  have hcpp : RecorderCoupled log frp gS sS cS := by
                    rw [hfrp]
                    exact recorderCoupled_step_other hcp
                      (by unfold isGasOp; rw [hdpush]; rfl) (by unfold isSloadOp; rw [hdpush]; rfl)
                      (stepFrame_push fr .PUSH32 (UInt256.ofNat slot) 32 (by decide) hdpush
                        (by decide) (by decide) hgasPush hszfr)
                  -- == step 2: MLOAD at `slot` (covered ⇒ zero memory expansion) ==
                  have hreal' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by
                    rw [show (UInt256.ofNat slot).toNat = slot from by
                      rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
                    exact hreal
                  have hMeq : MachineState.M frp.exec.toMachineState.activeWords
                      (UInt256.ofNat slot).toUInt64 32 = frp.exec.toMachineState.activeWords := by
                    rw [hfrpaw]; exact M_32_eq_self_of_covered _ _ ham hreal'
                  have hnoexp : memoryExpansionWords? frp.exec.activeWords (UInt256.ofNat slot) 32
                      = some frp.exec.activeWords := by
                    show memoryExpansionWords? frp.exec.toMachineState.activeWords _ _ = _
                    rw [hfrpaw]
                    exact memoryExpansionWords?_ofNat_32_of_covered _ ham hreal
                  have hzcost : BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
                      frp.exec.activeWords = 0 := by
                    show Evm.Cₘ frp.exec.activeWords - Evm.Cₘ frp.exec.activeWords = 0
                    omega
                  have hmloaddec : decode frp.exec.executionEnv.code frp.exec.pc
                      = some (.Smsf .MLOAD, .none) := by
                    rw [hfrpcode, hfrppc]
                    have : (emitImm (UInt256.ofNat slot)).length = 33 := emitImm_length _
                    rw [show fr.exec.pc + UInt32.ofNat 33
                          = fr.exec.pc + UInt32.ofNat (emitImm (UInt256.ofNat slot)).length from by
                          rw [this]]
                    exact hdmload
                  have hgMem : BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
                      frp.exec.activeWords ≤ frp.exec.gasAvailable.toNat := by rw [hzcost]; omega
                  have hfrpgasN : frp.exec.gasAvailable.toNat
                      = fr.exec.gasAvailable.toNat - Gverylow := by
                    show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
                    rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow (by rw [hgv3]; omega)
                      (by rw [hgv3]; omega)]
                  have hgMl : GasConstants.Gverylow
                      ≤ (frp.exec.gasAvailable
                          - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
                              frp.exec.activeWords)).toNat := by
                    rw [hzcost,
                        BytecodeLayer.UInt64.toNat_sub_ofNat frp.exec.gasAvailable 0
                          (Nat.zero_le _) (by norm_num),
                        Nat.sub_zero, hfrpgasN, hgv3]
                    rw [hsum2, hgv3] at hgas; omega
                  obtain ⟨hmloadrun, hmloadhd⟩ :=
                    sim_mload frp (UInt256.ofNat slot) frp.exec.activeWords fr.exec.stack
                      hmloaddec hfrpstk hfrpsz hnoexp hgMem hgMl
                  set frm := mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords fr.exec.stack
                    with hfrm
                  -- coupling across the MLOAD step (non-recording).
                  have hcpm : RecorderCoupled log frm gS sS cS := by
                    rw [hfrm]
                    exact recorderCoupled_step_other hcpp
                      (by unfold isGasOp; rw [hmloaddec]; rfl)
                      (by unfold isSloadOp; rw [hmloaddec]; rfl)
                      (stepFrame_mload frp (UInt256.ofNat slot) frp.exec.activeWords fr.exec.stack
                        hmloaddec hfrpstk hfrpsz hnoexp hgMem hgMl)
                  have hmval : ((BytecodeLayer.Dispatch.memChargedState frp.exec
                      frp.exec.activeWords).toMachineState.mload (UInt256.ofNat slot)).1 = w := by
                    rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot)
                          (show (BytecodeLayer.Dispatch.memChargedState frp.exec
                              frp.exec.activeWords).toMachineState.memory
                            = fr.exec.toMachineState.memory from by rw [← hfrpmem]; rfl)
                          (show (BytecodeLayer.Dispatch.memChargedState frp.exec
                              frp.exec.activeWords).toMachineState.activeWords
                            = fr.exec.toMachineState.activeWords from by rw [← hfrpaw]; rfl)]
                    exact hval
                  have hfrmstk : frm.exec.stack = fr.exec.stack.push w := by
                    show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.stack = _
                    rw [← hmval]; rfl
                  have hfrmmem : frm.exec.toMachineState.memory = fr.exec.toMachineState.memory := by
                    show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.toMachineState.memory = _
                    rw [show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                          fr.exec.stack).exec.toMachineState.memory
                        = frp.exec.toMachineState.memory from rfl, hfrpmem]
                  have hfrmaw : frm.exec.toMachineState.activeWords
                      = fr.exec.toMachineState.activeWords := by
                    show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.toMachineState.activeWords = _
                    rw [show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                          fr.exec.stack).exec.toMachineState.activeWords
                        = MachineState.M frp.exec.toMachineState.activeWords
                            (UInt256.ofNat slot).toUInt64 32 from rfl, hMeq, hfrpaw]
                  have hexp0 : frp.exec.gasAvailable
                      - UInt64.ofNat (memExpansionChargeOf frp.exec frp.exec.activeWords)
                      = frp.exec.gasAvailable := by
                    apply UInt64.toNat_inj.mp
                    rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ _
                      (by rw [hzcost]; omega) (by rw [hzcost]; norm_num), hzcost, Nat.sub_zero]
                  have hfrmgas : frm.exec.gasAvailable
                      = (fr.exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow := by
                    show ((BytecodeLayer.Dispatch.memChargedState frp.exec
                      frp.exec.activeWords).gasAvailable) = _
                    show ((frp.exec.gasAvailable - UInt64.ofNat (memExpansionChargeOf frp.exec
                      frp.exec.activeWords)) - UInt64.ofNat Gverylow) = _
                    rw [hexp0, hfrp]; rfl
                  refine ⟨frm, ?_, hcpm⟩
                  refine
                    { runs := hpushrun.trans hmloadrun
                      stack := hfrmstk
                      code := ?_
                      validJumps := ?_
                      addr := ?_
                      canMod := ?_
                      accounts := ?_
                      storage := ?_
                      pc := ?_
                      gasCharge := ?_
                      gasToNat := ?_
                      memBytes := hfrmmem
                      memActive := by rw [hfrmaw] }
                  · show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.executionEnv.code = _
                    rw [show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                          fr.exec.stack).exec.executionEnv.code = frp.exec.executionEnv.code from rfl,
                        hfrpcode]
                  · show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).validJumps = _
                    rfl
                  · show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.executionEnv.address = _
                    rfl
                  · show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.executionEnv.canModifyState = _
                    rfl
                  · show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.accounts = _
                    rfl
                  · intro k
                    show selfStorage (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack) k = _
                    rfl
                  · show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                      fr.exec.stack).exec.pc = _
                    rw [show (mloadFrame frp (UInt256.ofNat slot) frp.exec.activeWords
                          fr.exec.stack).exec.pc = frp.exec.pc + 1 from rfl, hfrppc, hmexp]
                    rw [List.length_append, emitImm_length,
                        show ([Byte.mload] : List UInt8).length = 1 from rfl,
                        show (33 : ℕ) + 1 = 34 from rfl,
                        show (UInt32.ofNat 34) = UInt32.ofNat 33 + 1 from by decide]
                    ac_rfl
                  · show MaterialiseGasCharge defs sloadChg (f + 1) (.tmp t) fr frm
                    rw [MaterialiseGasCharge, hchg]
                    show frm.exec.gasAvailable = subCharges fr.exec.gasAvailable [Gverylow, Gverylow]
                    rw [hfrmgas]
                    show (fr.exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow
                      = subCharges fr.exec.gasAvailable [Gverylow, Gverylow]
                    rfl
                  · rw [hsum2, hfrmgas]
                    have hgge : Gverylow + Gverylow ≤ fr.exec.gasAvailable.toNat := by
                      rw [hsum2, hgv3] at hgas; rw [hgv3]; omega
                    have h2 : (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat
                        = fr.exec.gasAvailable.toNat - Gverylow :=
                      BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow
                        (by rw [hgv3]; omega) (by rw [hgv3]; omega)
                    rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow
                          (by rw [h2, hgv3]; omega) (by rw [hgv3]; omega), h2]
                    omega
              · -- == the pure recompute path (B3 `DefsSound`) — `e'` is NOT a call result ==
                  have htmd : MatDec fr.exec.executionEnv.code defs sloadChg f fr.exec.pc e' := by
                    rw [matDec_tmp_some fr.exec.executionEnv.code defs sloadChg f fr.exec.pc t e' ht]
                      at hdec
                    exact hdec
                  have hgas' : (chargeOf defs sloadChg f e').sum ≤ fr.exec.gasAvailable.toNat := by
                    rw [chargeOf_tmp_some defs sloadChg f t e' ht] at hgas; exact hgas
                  have hstk' : fr.exec.stack.size + (chargeOf defs sloadChg f e').length ≤ 1024 := by
                    rw [chargeOf_tmp_some defs sloadChg f t e' ht] at hstk; exact hstk
                  have hnr : ¬ NonRecomputable prog t := by
                    rcases (hscoped t (by rw [hloc]; simp)).1 with hnr | ⟨slot, hcrdef⟩
                    · exact hnr
                    · exfalso
                      apply hncr
                      have : some e' = some (Expr.slot slot) := by
                        rw [← ht, hdefs]; exact hcrdef
                      exact ⟨slot, Option.some.inj this⟩
                  have he'ng : e' ≠ .gas := by
                    rintro rfl
                    exact defsOf_ne_gas prog t (by rw [← hdefs]; exact ht)
                  have he'nsl : ∀ k, e' ≠ .sload k := by
                    intro k
                    rintro rfl
                    exact defsOf_ne_sload prog t k (by rw [← hdefs]; exact ht)
                  have hdfs : some w = evalExpr st 0 e' :=
                    hsound t e' w (rematOf_of_defsOf (by rw [← hdefs, ht]) (fun n h => hncr ⟨n, h⟩))
                      hnr hloc
                  have heval' : evalExpr st obs e' = some w := by
                    rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
                  obtain ⟨fr', hmr, hcp'⟩ := ih e' w fr htmd hsound hscoped hstore he'ng he'nsl
                    hmemreal heval' hgas' hstk' hcp
                  refine ⟨fr', ?_, hcp'⟩
                  have hmexp : materialiseExpr defs (f + 1) (.tmp t) = materialiseExpr defs f e' :=
                    materialiseExpr_tmp_some defs f t e' ht
                  have hchg : chargeOf defs sloadChg (f + 1) (.tmp t) = chargeOf defs sloadChg f e' :=
                    chargeOf_tmp_some defs sloadChg f t e' ht
                  exact
                    { runs := hmr.runs
                      stack := hmr.stack
                      code := hmr.code
                      validJumps := hmr.validJumps
                      addr := hmr.addr
                      canMod := hmr.canMod
                      accounts := hmr.accounts
                      storage := hmr.storage
                      pc := by rw [hmexp]; exact hmr.pc
                      gasCharge := by
                        rw [MaterialiseGasCharge, hchg]; exact hmr.gasCharge
                      gasToNat := by rw [hchg]; exact hmr.gasToNat
                      memBytes := hmr.memBytes
                      memActive := hmr.memActive }
      | add a b =>
          obtain ⟨va, hla, vb, hlb, hwadd⟩ :
              ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
                ∧ w = UInt256.add va vb := by
            simp only [evalExpr] at heval
            cases hla : st.locals a with
            | none => simp [hla] at heval
            | some va =>
                cases hlb : st.locals b with
                | none => simp [hla, hlb] at heval
                | some vb =>
                    refine ⟨va, rfl, vb, rfl, ?_⟩
                    simp [hla, hlb] at heval; exact heval.symm
          subst hwadd
          obtain ⟨hdb, hda, hop⟩ := hdec
          have hcadd : chargeOf defs sloadChg (f + 1) (.add a b)
              = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a)
                ++ [Gverylow] := chargeOf_add defs sloadChg f a b
          have hevb : evalExpr st obs (.tmp b) = some vb := hlb
          have heva : evalExpr st obs (.tmp a) = some va := hla
          have hgasb : (chargeOf defs sloadChg f (.tmp b)).sum ≤ fr.exec.gasAvailable.toNat := by
            rw [hcadd] at hgas
            simp only [List.sum_append] at hgas; omega
          have hstkb : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp b)).length ≤ 1024 := by
            rw [hcadd] at hstk
            simp only [List.length_append] at hstk; omega
          obtain ⟨frb, hmrb, hcpb⟩ := ih (.tmp b) vb fr hdb hsound hscoped hstore (by nofun) (by nofun)
            hmemreal hevb hgasb hstkb hcp
          have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
          have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length :=
            hmrb.pc
          have hda' : MatDec frb.exec.executionEnv.code defs sloadChg f frb.exec.pc (.tmp a) := by
            rw [hbcode, hbpc]; exact hda
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.add a b)).sum
              = (chargeOf defs sloadChg f (.tmp b)).sum
                + (chargeOf defs sloadChg f (.tmp a)).sum + Gverylow := by
            rw [hcadd]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.add a b)).length
              = (chargeOf defs sloadChg f (.tmp b)).length
                + (chargeOf defs sloadChg f (.tmp a)).length + 1 := by
            rw [hcadd]; simp only [List.length_append, List.length_singleton]
          have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
            rw [hmrb.stack]; simp [Stack.push]
          have hpb1 : 1 ≤ (chargeOf defs sloadChg f (.tmp b)).length :=
            chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp b) hdb
          have hgasa : (chargeOf defs sloadChg f (.tmp a)).sum ≤ frb.exec.gasAvailable.toNat := by
            rw [hmrb.gasToNat]; rw [hsum_split] at hgas; omega
          have hstka : frb.exec.stack.size + (chargeOf defs sloadChg f (.tmp a)).length ≤ 1024 := by
            rw [hlen_split] at hstk; rw [hfrbsz]; omega
          obtain ⟨fra, hmra, hcpa⟩ := ih (.tmp a) va frb hda' hsound hscoped
            (hstore.transport hmrb.storage) (by nofun) (by nofun)
            (hmemreal.transport hmrb.memBytes hmrb.memActive)
            heva hgasa hstka hcpb
          have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
            rw [hmra.code, hbcode]
          have hapc : fra.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
                  + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length := by
            rw [hmra.pc, hbpc]
          have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
            rw [hmra.stack, hmrb.stack]; rfl
          have hadec : decode fra.exec.executionEnv.code fra.exec.pc
              = some (.ArithLogic .ADD, .none) := by
            rw [hacode, hapc]; exact hop
          have haszle : fra.exec.stack.size ≤ 1024 := by
            have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by
              rw [hastk]; simp
            have hpa1 : 1 ≤ (chargeOf defs sloadChg f (.tmp a)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f frb.exec.pc (.tmp a) hda'
            rw [hlen_split] at hstk; rw [hfrasz]; omega
          have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
            rw [hsum_split] at hgas; rw [hmra.gasToNat, hmrb.gasToNat]; omega
          obtain ⟨hadrun, hadstk⟩ := sim_add fra va vb fr.exec.stack hadec hastk haszle hagas
          -- coupling across the ADD step (non-recording).
          have hcp' : RecorderCoupled log (addFrame fra va vb fr.exec.stack) gS sS cS :=
            recorderCoupled_step_other hcpa
              (by unfold isGasOp; rw [hadec]; rfl) (by unfold isSloadOp; rw [hadec]; rfl)
              (stepFrame_add fra va vb fr.exec.stack hadec hastk haszle hagas)
          refine ⟨addFrame fra va vb fr.exec.stack, ?_, hcp'⟩
          refine
            { runs := (hmrb.runs.trans hmra.runs).trans hadrun
              stack := ?_
              code := ?_
              validJumps := ?_
              addr := ?_
              canMod := ?_
              accounts := ?_
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_
              memBytes := by
                rw [addFrame_memory]; exact hmra.memBytes.trans hmrb.memBytes
              memActive := le_trans hmrb.memActive
                (le_trans hmra.memActive (by rw [addFrame_activeWords])) }
          · rw [hadstk]
          · rw [addFrame_code, hacode]
          · rw [addFrame_validJumps, hmra.validJumps, hmrb.validJumps]
          · rw [addFrame_addr, hmra.addr, hmrb.addr]
          · show (addFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState = _
            rw [show (addFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState
                  = fra.exec.executionEnv.canModifyState from rfl, hmra.canMod, hmrb.canMod]
          · show (addFrame fra va vb fr.exec.stack).exec.accounts = _
            rw [show (addFrame fra va vb fr.exec.stack).exec.accounts
                  = fra.exec.accounts from rfl, hmra.accounts, hmrb.accounts]
          · intro k; rw [addFrame_selfStorage, hmra.storage, hmrb.storage]
          · rw [addFrame_pc, hapc, materialiseExpr_add]
            simp only [List.length_append, List.length_singleton]
            rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1) = 1 from rfl]
            ac_rfl
          · exact (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
              (addFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
              (charge_binOpPost_gas fra UInt256.add va vb fr.exec.stack)).1
          · have hsum : (chargeOf defs sloadChg (f + 1) (.add a b)).sum
                ≤ fr.exec.gasAvailable.toNat := hgas
            have hc :
                (addFrame fra va vb fr.exec.stack).exec.gasAvailable
                  = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg (f + 1) (.add a b)) :=
              (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
                (addFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
                (charge_binOpPost_gas fra UInt256.add va vb fr.exec.stack)).1
            rw [hc]; exact toNat_chargeOf defs sloadChg (f + 1) (.add a b) _ hsum
      | lt a b =>
          obtain ⟨va, hla, vb, hlb, hwlt⟩ :
              ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
                ∧ w = UInt256.lt va vb := by
            simp only [evalExpr] at heval
            cases hla : st.locals a with
            | none => simp [hla] at heval
            | some va =>
                cases hlb : st.locals b with
                | none => simp [hla, hlb] at heval
                | some vb =>
                    refine ⟨va, rfl, vb, rfl, ?_⟩
                    simp [hla, hlb] at heval; exact heval.symm
          subst hwlt
          obtain ⟨hdb, hda, hop⟩ := hdec
          have hclt : chargeOf defs sloadChg (f + 1) (.lt a b)
              = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a)
                ++ [Gverylow] := chargeOf_lt defs sloadChg f a b
          have hevb : evalExpr st obs (.tmp b) = some vb := hlb
          have heva : evalExpr st obs (.tmp a) = some va := hla
          have hgasb : (chargeOf defs sloadChg f (.tmp b)).sum ≤ fr.exec.gasAvailable.toNat := by
            rw [hclt] at hgas
            simp only [List.sum_append] at hgas; omega
          have hstkb : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp b)).length ≤ 1024 := by
            rw [hclt] at hstk
            simp only [List.length_append] at hstk; omega
          obtain ⟨frb, hmrb, hcpb⟩ := ih (.tmp b) vb fr hdb hsound hscoped hstore (by nofun) (by nofun)
            hmemreal hevb hgasb hstkb hcp
          have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
          have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length :=
            hmrb.pc
          have hda' : MatDec frb.exec.executionEnv.code defs sloadChg f frb.exec.pc (.tmp a) := by
            rw [hbcode, hbpc]; exact hda
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.lt a b)).sum
              = (chargeOf defs sloadChg f (.tmp b)).sum
                + (chargeOf defs sloadChg f (.tmp a)).sum + Gverylow := by
            rw [hclt]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.lt a b)).length
              = (chargeOf defs sloadChg f (.tmp b)).length
                + (chargeOf defs sloadChg f (.tmp a)).length + 1 := by
            rw [hclt]; simp only [List.length_append, List.length_singleton]
          have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
            rw [hmrb.stack]; simp [Stack.push]
          have hpb1 : 1 ≤ (chargeOf defs sloadChg f (.tmp b)).length :=
            chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp b) hdb
          have hgasa : (chargeOf defs sloadChg f (.tmp a)).sum ≤ frb.exec.gasAvailable.toNat := by
            rw [hmrb.gasToNat]; rw [hsum_split] at hgas; omega
          have hstka : frb.exec.stack.size + (chargeOf defs sloadChg f (.tmp a)).length ≤ 1024 := by
            rw [hlen_split] at hstk; rw [hfrbsz]; omega
          obtain ⟨fra, hmra, hcpa⟩ := ih (.tmp a) va frb hda' hsound hscoped
            (hstore.transport hmrb.storage) (by nofun) (by nofun)
            (hmemreal.transport hmrb.memBytes hmrb.memActive)
            heva hgasa hstka hcpb
          have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
            rw [hmra.code, hbcode]
          have hapc : fra.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
                  + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length := by
            rw [hmra.pc, hbpc]
          have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
            rw [hmra.stack, hmrb.stack]; rfl
          have hadec : decode fra.exec.executionEnv.code fra.exec.pc
              = some (.ArithLogic .LT, .none) := by
            rw [hacode, hapc]; exact hop
          have haszle : fra.exec.stack.size ≤ 1024 := by
            have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by
              rw [hastk]; simp
            have hpa1 : 1 ≤ (chargeOf defs sloadChg f (.tmp a)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f frb.exec.pc (.tmp a) hda'
            rw [hlen_split] at hstk; rw [hfrasz]; omega
          have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
            rw [hsum_split] at hgas; rw [hmra.gasToNat, hmrb.gasToNat]; omega
          obtain ⟨hadrun, hadstk⟩ := sim_lt fra va vb fr.exec.stack hadec hastk haszle hagas
          -- coupling across the LT step (non-recording).
          have hcp' : RecorderCoupled log (ltFrame fra va vb fr.exec.stack) gS sS cS :=
            recorderCoupled_step_other hcpa
              (by unfold isGasOp; rw [hadec]; rfl) (by unfold isSloadOp; rw [hadec]; rfl)
              (stepFrame_lt fra va vb fr.exec.stack hadec hastk haszle hagas)
          refine ⟨ltFrame fra va vb fr.exec.stack, ?_, hcp'⟩
          refine
            { runs := (hmrb.runs.trans hmra.runs).trans hadrun
              stack := ?_
              code := ?_
              validJumps := ?_
              addr := ?_
              canMod := ?_
              accounts := ?_
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_
              memBytes := by
                rw [ltFrame_memory]; exact hmra.memBytes.trans hmrb.memBytes
              memActive := le_trans hmrb.memActive
                (le_trans hmra.memActive (by rw [ltFrame_activeWords])) }
          · rw [hadstk]
          · rw [ltFrame_code, hacode]
          · rw [ltFrame_validJumps, hmra.validJumps, hmrb.validJumps]
          · rw [ltFrame_addr, hmra.addr, hmrb.addr]
          · show (ltFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState = _
            rw [show (ltFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState
                  = fra.exec.executionEnv.canModifyState from rfl, hmra.canMod, hmrb.canMod]
          · show (ltFrame fra va vb fr.exec.stack).exec.accounts = _
            rw [show (ltFrame fra va vb fr.exec.stack).exec.accounts
                  = fra.exec.accounts from rfl, hmra.accounts, hmrb.accounts]
          · intro k; rw [ltFrame_selfStorage, hmra.storage, hmrb.storage]
          · rw [ltFrame_pc, hapc, materialiseExpr_lt]
            simp only [List.length_append, List.length_singleton]
            rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1) = 1 from rfl]
            ac_rfl
          · exact (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
              (ltFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
              (charge_binOpPost_gas fra UInt256.lt va vb fr.exec.stack)).2
          · have hsum : (chargeOf defs sloadChg (f + 1) (.lt a b)).sum
                ≤ fr.exec.gasAvailable.toNat := hgas
            have hc :
                (ltFrame fra va vb fr.exec.stack).exec.gasAvailable
                  = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg (f + 1) (.lt a b)) :=
              (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
                (ltFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
                (charge_binOpPost_gas fra UInt256.lt va vb fr.exec.stack)).2
            rw [hc]; exact toNat_chargeOf defs sloadChg (f + 1) (.lt a b) _ hsum

/-- **S3 — `sim_sstore_stmt'`, the WIP re-plumb of `sim_sstore_stmt`.** Same conclusion as the
in-tree `sim_sstore_stmt` (`Sim/SimStmt.lean`), but (i) DROPS the unsatisfiable `∀`-quantified
`hsstore : SstoreRealises fr kw vw acc` — its three runtime facts are derived POINT-WISE at the
internal SSTORE frame `frk` from the threaded `SelfPresent fr` + clean-halt via
`sstoreRealises_at_frame` (R4); and (ii) THREADS the recorder coupling
`RecorderCoupled log fr gS sS cS` across the two `materialise` runs (S1 `recorderCoupled_matRuns`,
value then key) and the SSTORE frame itself (S2, one `recorderCoupled_step_other`, R7d — SSTORE is
neither GAS nor SLOAD), returning it at the post-frame. The `Corr` re-establishment body is verbatim
`sim_sstore_stmt`. REAL; no sorry. -/
theorem sim_sstore_stmt' {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {log : RunLog}
    {st : IRState} {key value : Tmp} {kw vw : Word}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Lir.Corr prog sloadChg obs st fr L pc)
    (hk : st.locals key = some kw) (hv : st.locals value = some vw)
    (hsc : Lir.StepScoped prog st (.sstore key value))
    (hdv : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
            fr.exec.pc (.tmp value))
    (hdk : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
            (fr.exec.pc + UInt32.ofNat
              (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length) (.tmp key))
    (hdop : decode fr.exec.executionEnv.code
            (fr.exec.pc
              + UInt32.ofNat (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
              + UInt32.ofNat (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length)
            = some (.Smsf .SSTORE, .none))
    (hcs : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hstk : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
              + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length
              + 1 ≤ 1024) :
    ∃ fr', Runs fr fr'
      ∧ Lir.Corr prog sloadChg obs (st.setStorage kw vw) fr' L (pc + 1)
      ∧ fr'.exec.stack = []
      ∧ RecorderCoupled log fr' gS sS cS := by
  classical
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  set lv := (materialiseExpr defs fuel (.tmp value)).length with hlv
  set lk := (materialiseExpr defs fuel (.tmp key)).length with hlk
  have hstacknil := hcorr.stack_nil
  -- == B1 call 1: materialise `value` from `fr`, leaving `[vw]`, carrying the coupling ==
  have hevv : V2.evalExpr st obs (.tmp value) = some vw := hv
  have hszfr : fr.exec.stack.size = 0 := by rw [hstacknil]; rfl
  have hstkv : fr.exec.stack.size + (chargeOf defs sloadChg fuel (.tmp value)).length ≤ 1024 := by
    rw [hszfr]; omega
  have hgasv : (chargeOf defs sloadChg fuel (.tmp value)).sum ≤ fr.exec.gasAvailable.toNat :=
    materialise_charge_le_of_cleanHalt sloadChg fuel st obs (.tmp value) vw fr
      hdv hcorr.defsSound hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
      hevv hcs hstkv
  obtain ⟨frv, hmrv, hcpv⟩ := recorderCoupled_matRuns sloadChg fuel st obs log gS sS cS
    (.tmp value) vw fr
    hdv hcorr.defsSound hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
    hevv hgasv hstkv hcp
  have hvcode : frv.exec.executionEnv.code = fr.exec.executionEnv.code := hmrv.code
  have hvaddr : frv.exec.executionEnv.address = fr.exec.executionEnv.address := hmrv.addr
  have hvpc : frv.exec.pc = fr.exec.pc + UInt32.ofNat lv := hmrv.pc
  have hvstk : frv.exec.stack = vw :: fr.exec.stack := by rw [hmrv.stack]; rfl
  -- == B1 call 2: materialise `key` from `frv`, leaving `[kw, vw]`, carrying the coupling ==
  have hevk : V2.evalExpr st obs (.tmp key) = some kw := hk
  have hcsv : CleanHaltsNonException frv := cleanHaltsNonException_forward hcs hmrv.runs
  have hdk' : MatDec frv.exec.executionEnv.code defs sloadChg fuel frv.exec.pc (.tmp key) := by
    rw [hvcode, hvpc]; exact hdk
  have hfrvsz : frv.exec.stack.size = fr.exec.stack.size + 1 := by rw [hvstk]; simp
  have hstkk : frv.exec.stack.size + (chargeOf defs sloadChg fuel (.tmp key)).length ≤ 1024 := by
    rw [hfrvsz, hszfr]; omega
  have hgask : (chargeOf defs sloadChg fuel (.tmp key)).sum ≤ frv.exec.gasAvailable.toNat :=
    materialise_charge_le_of_cleanHalt sloadChg fuel st obs (.tmp key) kw frv
      hdk' hcorr.defsSound hcorr.wellScoped
      (hcorr.storage.transport hmrv.storage) (by nofun) (by nofun)
      (hcorr.memAgree.transport hmrv.memBytes hmrv.memActive) hevk hcsv hstkk
  obtain ⟨frk, hmrk, hcpk⟩ := recorderCoupled_matRuns sloadChg fuel st obs log gS sS cS
    (.tmp key) kw frv
    hdk' hcorr.defsSound hcorr.wellScoped
    (hcorr.storage.transport hmrv.storage) (by nofun) (by nofun)
    (hcorr.memAgree.transport hmrv.memBytes hmrv.memActive) hevk hgask hstkk hcpv
  have hkcode : frk.exec.executionEnv.code = fr.exec.executionEnv.code := by
    rw [hmrk.code, hvcode]
  have hkvalid : frk.validJumps = fr.validJumps := by
    rw [hmrk.validJumps, hmrv.validJumps]
  have hkaddr : frk.exec.executionEnv.address = fr.exec.executionEnv.address := by
    rw [hmrk.addr, hvaddr]
  have hkpc : frk.exec.pc = fr.exec.pc + UInt32.ofNat lv + UInt32.ofNat lk := by
    rw [hmrk.pc, hvpc]
  have hkstk : frk.exec.stack = kw :: vw :: [] := by
    rw [hmrk.stack, hvstk, hstacknil]; rfl
  have hkdec : decode frk.exec.executionEnv.code frk.exec.pc = some (.Smsf .SSTORE, .none) := by
    rw [hkcode, hkpc]; exact hdop
  have hksz : frk.exec.stack.size ≤ 1024 := by rw [hkstk]; simp
  have hkmod : frk.exec.executionEnv.canModifyState = true := by
    rw [hmrk.canMod, hmrv.canMod]; exact hcorr.can_modify
  -- == the point-wise SSTORE realisation at `frk` (R4), from the transported `SelfPresent` ==
  have hspv : SelfPresent frv := by
    obtain ⟨a, ha⟩ := hsp; exact ⟨a, by rw [hmrv.accounts, hmrv.addr]; exact ha⟩
  have hspk : SelfPresent frk := by
    obtain ⟨a, ha⟩ := hspv; exact ⟨a, by rw [hmrk.accounts, hmrk.addr]; exact ha⟩
  have hcsk : CleanHaltsNonException frk := cleanHaltsNonException_forward hcsv hmrk.runs
  obtain ⟨hstip, hcost, acc, hself⟩ :=
    sstoreRealises_at_frame hspk hcsk hkstk hkdec hkmod
  obtain ⟨hsrun, hswrite, hsframe⟩ :=
    sim_sstore frk kw vw [] acc hkdec hkstk hksz hkmod hstip hcost hself
  -- == coupling across the SSTORE frame (S2 — SSTORE is neither GAS nor SLOAD, non-recording) ==
  have hcpf : RecorderCoupled log (sstoreFrame frk kw vw []) gS sS cS :=
    recorderCoupled_step_other hcpk
      (by unfold isGasOp; rw [hkdec]; rfl) (by unfold isSloadOp; rw [hkdec]; rfl)
      (stepFrame_sstore frk kw vw [] hkdec hkstk hksz hkmod hstip hcost)
  refine ⟨sstoreFrame frk kw vw [], (hmrv.runs.trans hmrk.runs).trans hsrun, ?_, ?_, hcpf⟩
  · -- re-establish `Corr` at `(L, pc+1)` for `st.setStorage kw vw` (verbatim `sim_sstore_stmt`).
    have hfraddr : (sstoreFrame frk kw vw []).exec.executionEnv.address
        = frk.exec.executionEnv.address := sstoreFrame_addr frk kw vw []
    have hemit : (emitStmt defs fuel (.sstore key value)).length = lv + lk + 1 := by
      rw [emitStmt_sstore]; simp only [List.length_append, List.length_singleton, hlv, hlk]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (lv + lk + 1) := by
      rw [pcOf_succ prog L b pc (.sstore key value) hb hs, hemit]
    refine
      { pc_eq := ?_
        code_eq := ?_
        validJumps_eq := ?_
        stack_nil := by rw [sstoreFrame_stack]
        can_modify := by rw [sstoreFrame_canMod, hkmod]
        storage := ?_
        defsSound := ?_
        wellScoped := ?_
        memAgree := ?_ }
    · rw [sstoreFrame_pc, hkpc, hcorr.pc_eq, hpcN,
          show ((1 : UInt8).toUInt32) = UInt32.ofNat 1 from rfl,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add]
      ac_rfl
    · rw [sstoreFrame_code, hkcode]; exact hcorr.code_eq
    · rw [sstoreFrame_validJumps, sstoreFrame_code, hkvalid, hkcode]; exact hcorr.validJumps_eq
    · intro keyw
      rw [selfStorage_eq_storageAt, hfraddr]
      show storageAt (sstoreFrame frk kw vw []) frk.exec.executionEnv.address keyw
        = (st.setStorage kw vw).world keyw
      by_cases hk0 : keyw = kw
      · subst hk0
        rw [hswrite]
        show vw = (if keyw = keyw then vw else st.world keyw)
        simp
      · rw [hsframe keyw hk0]
        show storageAt frk frk.exec.executionEnv.address keyw
          = (st.setStorage kw vw).world keyw
        rw [show storageAt frk frk.exec.executionEnv.address keyw = selfStorage frk keyw from rfl,
            hmrk.storage keyw, hmrv.storage keyw, hcorr.storage keyw]
        show st.world keyw = (if keyw = kw then vw else st.world keyw)
        simp [hk0]
    · exact defsSound_preserved_sstore hsc hcorr.defsSound
    · intro tw htw
      exact hcorr.wellScoped tw (by simpa [V2.IRState.setStorage] using htw)
    · intro tw slot v hdef hloc
      have hloc' : st.locals tw = some v := by simpa [V2.IRState.setStorage] using hloc
      have hmembytes : (sstoreFrame frk kw vw []).exec.toMachineState.memory
          = fr.exec.toMachineState.memory := by
        rw [sstoreFrame_memory, hmrk.memBytes, hmrv.memBytes]
      have hmemact : fr.exec.toMachineState.activeWords.toNat
          ≤ (sstoreFrame frk kw vw []).exec.toMachineState.activeWords.toNat := by
        rw [sstoreFrame_activeWords]; exact le_trans hmrv.memActive hmrk.memActive
      exact (hcorr.memAgree.transport hmembytes hmemact) tw slot v hdef hloc'
  · rw [sstoreFrame_stack]

/-- **P2-sstore — the SSTORE coupled step.** Fires `StmtTies'` arm (4) (`StepScopedS` +
stack-room), the in-tree `sim_sstore_stmt` brick fed the point-wise `sstoreRealises_at_frame`
(R4 — the honest replacement of the unsatisfiable `∃ acc, SstoreRealises` conjunct, discharged
at the concrete frame from clean-halt + the threaded `SelfPresent`), and `recorderCoupled_step_other`
(R7d). No stream head consumed (`EvalStmt.sstore`). Needs `SelfPresent fr` (from the walk
invariant) fed to R4. TRACTABILITY: hard. -/
theorem simStmt_coupled_sstore {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {key value : Tmp} {kw vw : Word} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (hal : StreamsAligned self log gS cS T C D)
    (hk : st.locals key = some kw) (hvv : st.locals value = some vw)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.sstore key value) := by
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  -- ties arm (4): `StepScopedS` + the stack-room fold (fired with coupling + clean-halt).
  obtain ⟨hstepS, hstkbound⟩ :=
    hties.2.2.2.1 pc key value kw vw st fr gS sS cS hcur hcorr hcp hch hk hvv
  -- `StepScopedS` ⟹ the per-state `StepScoped` the sstore B3 preservation consumes (the static
  -- form quantifies over ALL registered defs, so it dominates the state-gated one).
  have hsc : Lir.StepScoped prog st (.sstore key value) := by
    intro t₀ e₀ hdef _ _ keyk; exact hstepS t₀ e₀ hdef keyk
  -- well-formedness: the two operand fuel-sufficiency facts + the statement pc bound (`hwl.wf`).
  obtain ⟨hwfv, hwfk⟩ := hwl.wf.matFueled_sstore L b pc key value hbt hcur
  have hbound := hwl.wf.bound_sstore L b pc key value hbt hcur
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  set lv := (materialiseExpr defs fuel (.tmp value)).length with hlv
  set lk := (materialiseExpr defs fuel (.tmp key)).length with hlk
  have hemit : emitStmt defs fuel (.sstore key value)
      = materialiseExpr defs fuel (.tmp value) ++ materialiseExpr defs fuel (.tmp key)
        ++ [Byte.sstore] := emitStmt_sstore ..
  have hlen : (emitStmt defs fuel (.sstore key value)).length = lv + lk + 1 := by
    rw [hemit]; simp only [List.length_append, List.length_singleton]; omega
  -- decode bundle at the static cursors (`matDec_of_lower` / `sstore_op_decode`), as in the
  -- in-tree `sim_sstore_stmt_lowered` decode-discharge (Layer A over `lower prog`).
  have hdv : MatDec fr.exec.executionEnv.code defs sloadChg fuel fr.exec.pc (.tmp value) := by
    rw [hcorr.code_eq, hcorr.pc_eq]
    have := matDec_of_lower prog sloadChg L b pc (.sstore key value) 0 (.tmp value)
      hbt hcur (by simpa using sstore_sub_value defs fuel key value)
      (by rw [← hdefs, ← hfuel, hlen]; omega) hwfv (by rw [← hdefs, ← hfuel, Nat.add_zero]; omega)
    simpa using this
  have hdk : MatDec fr.exec.executionEnv.code defs sloadChg fuel
      (fr.exec.pc + UInt32.ofNat lv) (.tmp key) := by
    rw [hcorr.code_eq, hcorr.pc_eq, ofNat_add']
    exact matDec_of_lower prog sloadChg L b pc (.sstore key value) lv (.tmp key)
      hbt hcur (sstore_sub_key defs fuel key value) (by rw [← hdefs, ← hfuel, hlen]; omega) hwfk
      (by rw [← hdefs, ← hfuel]; omega)
  have hdop : decode fr.exec.executionEnv.code
      (fr.exec.pc + UInt32.ofNat lv + UInt32.ofNat lk) = some (.Smsf .SSTORE, .none) := by
    rw [hcorr.code_eq, hcorr.pc_eq, ofNat_add', ofNat_add',
        show pcOf prog L pc + lv + lk = pcOf prog L pc + (lv + lk) from by omega]
    exact sstore_op_decode prog L b pc key value hbt hcur (by omega)
  -- fire S3 (`sim_sstore_stmt'`): the two-frame materialise fold + the point-wise R4 realisation
  -- + the coupling transported to the post-frame.
  obtain ⟨fr', hruns, hcorr', hstacknil', hcpf⟩ :=
    sim_sstore_stmt' hbt hcur hcorr hk hvv hsc hdv hdk hdop hch hsp hcp hstkbound
  -- S4 — assemble the `CoupledAdvance`: `EvalStmt.sstore` consumes NO stream head (T/C/D and
  -- gS/sS/cS ride unchanged), so the alignment `hal` carries over verbatim.
  exact ⟨st.setStorage kw vw, fr', T, C, D, gS, sS, cS,
    EvalStmt.sstore hk hvv, hruns, hcorr', hstacknil', hcpf, hal⟩

/-- **P2-call — the external-CALL coupled step (the R3/Piece-B-gated arm).** Fires `StmtTies'`
arm (5) / `CallRealisesS` (R3 `callRealises_of_recorded`, whose Piece A is green via
`recorderCoupled_call_extract`), the in-tree `sim_call_stmt` brick, and `recorderCoupled_call`
(R7e) to advance past the recorded CALL record; the `callSuffix` head `rec` positionally IS this
call's recorded result, so `EvalStmt.call` consumes exactly the aligned `callStreamOf` head
(`callStreamOf_cons`). BLOCKER: R3's Piece B (the `materialise`-driven CALL argument-push run —
`Runs fr callFr` + `stepFrame callFr = .needsCall …`) has NO in-tree producer
(`callRealises_of_recorded` is `sorry`, `Machinery.lean:405`); and the `resumeAfterCall` frame-pin
sub-facts may need a bytecode-layer computation in the DEFAULT target (STOP-and-report, per the
track rules). TRACTABILITY: hard (Piece-B-gated). -/
theorem simStmt_coupled_call {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {cs : CallSpec} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {rec : CallRecord} {cS' : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS (rec :: cS'))
    (hch : CleanHaltsNonException fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hcallee : ∃ cw, st.locals cs.callee = some cw)
    (hgasfwd : ∃ gw, st.locals cs.gasFwd = some gw)
    (hal : StreamsAligned self log gS (rec :: cS') T C D)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.call cs) := by
  sorry

/-! ## §3 — the COUPLED block walk and the per-block step -/

/-- The COUPLED block-run output at the terminator cursor `(L, b.stmts.length)`: the IR
`RunStmts` of the whole block (from the aligned streams), the bytecode `Runs fr fr'`, the
re-established `Corr` + empty stack + clean-halt at `fr'`, the advanced coupling + alignment,
and the self/address/kind pins transported to `fr'` (for the `TermTies'` antecedents). REAL def. -/
def CoupledBlockRun (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (L : Label) (b : Block) (st : IRState) (fr : Frame)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  ∃ (st' : IRState) (fr' : Frame) (T' : Trace) (C' : CallStream) (D' : CreateStream)
    (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord),
    RunStmts prog st T C D b.stmts st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 st' fr' L b.stmts.length
    ∧ fr'.exec.stack = []
    ∧ CleanHaltsNonException fr'
    ∧ RecorderCoupled log fr' gS' sS' cS'
    ∧ StreamsAligned self log gS' cS' T' C' D'
    ∧ SelfPresent fr'
    ∧ fr'.exec.executionEnv.address = self
    ∧ (∃ cp, fr'.kind = .call cp)

/-- **P3a — the COUPLED block walk** (the analogue of `sim_stmts_block`, but coupled; reason
(a) in one lemma). By induction over the block statement suffix, fold the `simStmt_coupled_*`
family: at each cursor dispatch on the statement shape, fire the matching arm (feeding it the
current coupling + alignment + `StmtTies'`), then recurse on the tail at the advanced coupling.
The self/addr/kind pins ride along via `selfPresent_runs` / `runs_kind` / the address transport.
Consumes: `stmtTies'_of_runWithLog` (R10a) for the arm facts; `RunDefinableG` (`hwl.defs`) for
operand definability at each cursor. TRACTABILITY: hard (assembles §2). -/
theorem simStmts_coupled_block {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcorr : Lir.Corr prog sloadChg 0 st fr L 0)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hkind : ∃ cp, fr.kind = .call cp)
    (hal : StreamsAligned self log gS cS T C D)
    (hstmts : StmtTies' prog sloadChg log self L b)
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    CoupledBlockRun prog sloadChg log self L b st fr T C D := by
  sorry

/-- **P3b — the COUPLED per-block step.** From the coupled boundary `DriveCorrLog` + alignment
at a present block, produce the `DriveLogStep`: run the block walk (P3a), then dispatch on
`b.term` (via `TermTies'`, produced by R10b `termTies'_of_walk`):
* `stop`/`ret` → the HALT disjunct: package `RunFromCoupled` from the terminator world-channel
  brick (`sim_term_halt_stop`/`_ret`) AND the RESULT channel (`observe`-result = `.stopped` /
  `.returned w`, via the live `observe` inverse the `ret` lowering — the coupled analogue of
  `drive_step_block_stop`/`_ret`, extended to the result channel `conforms_of_worldeq` needs);
* `jump`/`branch` → the EDGE disjunct: the successor `jumpdestFrame fj` re-establishing
  `DriveCorrLog` at `succ` (coupling transported UNCHANGED across the terminator edge — no
  gas/sload/call recorded on a JUMPDEST/JUMP/JUMPI, `recorderCoupled_stepsTo_other`),
  `StreamsAligned` unchanged, the strict `totalGas_succ_lt` descent, and the IR continuation
  (`RunFrom.jump`/`.branch*`) — the coupled analogue of `drive_step_block_jump`/`_branch`.
TRACTABILITY: hard (assembles P3a + the terminator bricks + `DriveCorrLog` re-establishment). -/
theorem driveLogStep_of_block {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {st : IRState} {fr : Frame} {L : Label}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hclosed : ClosedCFG prog)
    (hdrive : DriveCorrLog prog sloadChg log self st fr L gS sS cS)
    (hal : StreamsAligned self log gS cS T C D)
    (hstmts : StmtTies' prog sloadChg log self L
      (Classical.choose (DriveCorrLog.present hdrive)))
    (hterm : TermTies' prog sloadChg log self L
      (Classical.choose (DriveCorrLog.present hdrive)))
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    DriveLogStep prog sloadChg log self st fr L T C D gS sS cS := by
  sorry

/-! ## §4 — the drive recursion and the packaged producer -/

/-- **P4 — the coupled drive recursion (F2 analogue).** From the coupled per-boundary step
`DriveLogStep` available at every reachable `DriveCorrLog` boundary (with its alignment), the
packaged `RunFromCoupled` holds. Strong induction on the bytecode `totalGas` measure
(`totalGas_succ_lt`, `driveCorr_measure`), so it holds for CYCLIC CFGs. The halt disjunct is the
base case; the edge disjunct recurses at the strictly-smaller successor and prepends via the IR
continuation + `Runs.trans` (lifting the successor's bytecode halt terminal back to `fr`).
Structural mirror of `runFrom_of_driveCorr`. TRACTABILITY: hard (structural). -/
theorem runFrom_of_driveCorrLog_rec {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress}
    (hstep : ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream)
        (D : CreateStream) (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      DriveCorrLog prog sloadChg log self st fr L gS sS cS →
      StreamsAligned self log gS cS T C D →
      DriveLogStep prog sloadChg log self st fr L T C D gS sS cS) :
    ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      DriveCorrLog prog sloadChg log self st fr L gS sS cS →
      StreamsAligned self log gS cS T C D →
      RunFromCoupled prog self st fr L T C D := by
  sorry

/-- **P5 — the R6 boundary walk (`hrb`), reason (b).** Every `Runs fr₀`-reachable frame sits at
a reachable instruction boundary — `runs_atReachableBoundary`, needing `hne : 0 < prog.blocks.size`
(from `hwl.closed.entry_present` / `hwl.entry0`) AND the size seam `hsize`. The `hsize`
`(flatBytes prog).length ≤ 2 ^ 32` has NO producer from `hwl` — threaded as an explicit honest
seam. NOTE: R6 itself carries three pure-engine geometry `sorry` bricks in DEFAULT-target files
(`atReachableBoundaryVJ_step`/`_call` residues + the CREATE edge `atReachableBoundaryVJ_create`)
which are OUTSIDE this track's edit surface. TRACTABILITY: blocked-on-decision (the `hsize` seam
must be wired into the flagship; the engine bricks land elsewhere). -/
theorem boundaryWalk_of_wl {prog : Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hwl : WellLowered prog)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr' := by
  sorry

/-- **P6 — create-resolves for all reachable frames (`hcr`).** The blocker existential's first
conjunct. Threaded from a `ReachableFrom`-scoped create-resolves seam (the honest R4 residual —
`CreateResolves` is NOT structural, `V2/Modellable.lean:413`); trivial once the seam is a
hypothesis. WIRING the seam into the flagship's `PrecompileAssumptions` (or a companion) is a
tracked DECISION. TRACTABILITY: blocked-on-decision (needs the seam wired). -/
theorem createResolves_reachable {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hseam : ∀ fr', ReachableFrom params fr' → CreateResolves fr') :
    ∀ fr', Runs fr₀ fr' → CreateResolves fr' :=
  -- Every `Runs fr₀`-reachable frame is `ReachableFrom params` (`⟨fr₀, hbegin, hr⟩`), so the
  -- seam applies directly — the same `ReachableFrom` witness `driveCorrLog_entry` uses.
  fun fr' hr => hseam fr' ⟨fr₀, hbegin, hr⟩

/-- **R11 — `runFrom_of_driveCorrLog`, THE COUPLED RUN-PRODUCER.** The packaged existential the
flagship `lower_conforms` (`RealisabilitySpec.lean:240-247`) and its siblings `obtain`. Assembles:
the entry coupled boundary (P1a/P1b), the coupled drive recursion (P4) discharged per-boundary by
`driveLogStep_of_block` (P3b) fed the reshaped ties from R10a/R10b, and the create-resolves
conjunct (P6). Two honest seams beyond the flagship's current surface — the size bound `hsize`
(reason (b), P5) and the create-resolves residual `hcreate` (P6) — are threaded explicitly;
wiring them into the flagship is the tracked decision recorded in `docs/create/producer-plan.md`.

The output matches the blocker `obtain` verbatim: the create-resolves conjunct, the terminal
world+result equation, and the IR `RunFrom` at the pinned oracles (`realisedGas log` /
`realisedCall log recipient` / `realisedCreate log recipient`, from `entryState params`).
TRACTABILITY: hard (top-level assembly; genuinely closes once P1–P6 land). -/
theorem runFrom_of_driveCorrLog {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account} {fr₀ : Frame}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params)
    (hbegin : beginCall params = .inl fr₀)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (hcreate : ∀ fr', ReachableFrom params fr' → CreateResolves fr') :
    ∃ O : Observable,
      (∀ fr', Runs fr₀ fr' → CreateResolves fr')
      ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
          ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
          ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
      ∧ RunFrom prog (entryState params) (realisedGas log)
          (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O := by
  sorry

end Lir.V2
