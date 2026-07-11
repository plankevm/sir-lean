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
  `(flatBytes prog).length ≤ 2 ^ 32` (`Machinery.lean:1509`) is not a field of the internal
  `WellLowered` adapter — `WellFormedLowered` only carries per-cursor bounds. The public
  flagship now exposes the scalar `codeFits` budget; this producer still threads the derived
  size fact as an explicit `hsize` parameter at the boundary-walk helper.

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

The four helper predicates the producer's induction threads. `StreamsAligned` is the
positional bridge that turns the whole realised streams (`realisedGas`/`realisedCall`/
`realisedCreate`) at entry into the per-block head-consumption the IR `RunFrom` performs:
at every coupled boundary the IR streams `(T, C, D)` are exactly the realised image of the
un-consumed recorder suffixes `(gS, cS, dS)`. The sload suffix `sS` has no IR stream
(SLOAD consumes nothing on the IR side), so it is not aligned. -/

/-- The IR streams `(T, C, D)` at a coupled boundary are the realised image of the recorder
suffixes: the gas trace IS the gas suffix, the call stream IS the `evmV2CallEntry` image of
the call suffix, and the create stream IS the `evmV2CreateEntry` image of the create
suffix. REAL def. -/
def StreamsAligned (self : AccountAddress) (log : RunLog)
    (gS : List Word) (cS : List CallRecord) (dS : List CreateRecord)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  T = gS ∧ C = callStreamOf cS self ∧ D = createStreamOf dS self

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
    (gS : List Word) (sS : List Nat) (cS : List CallRecord) (dS : List CreateRecord) : Prop :=
  RunFromCoupled prog self st fr L T C D
  ∨
  (∃ (st' : IRState) (T' : Trace) (C' : CallStream) (D' : CreateStream)
      (succ : Label) (fr' : Frame) (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord)
      (dS' : List CreateRecord),
      Runs fr fr'
    ∧ DriveCorrLog prog sloadChg log self st' fr' succ gS' sS' cS' dS'
    ∧ StreamsAligned self log gS' cS' dS' T' C' D'
    ∧ totalGas [] (.inl fr') < totalGas [] (.inl fr)
    ∧ (∀ O, RunFrom prog st' T' C' D' succ O → RunFrom prog st T C D L O))

/-- The result of ONE coupled statement step at cursor `(L, pc)`: the IR `EvalStmt` of `s`
(consuming the aligned stream heads), the matching bytecode `Runs fr fr'` re-establishing
`Corr` at `pc+1` with empty stack, and the advanced coupling `RecorderCoupled` + `StreamsAligned`
at the tail. REAL def. -/
def CoupledAdvance (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (I : Tmp → Prop) (L : Label) (pc : Nat) (st : IRState) (fr : Frame)
    (T : Trace) (C : CallStream) (D : CreateStream) (s : Stmt) : Prop :=
  ∃ (st' : IRState) (fr' : Frame) (T' : Trace) (C' : CallStream) (D' : CreateStream)
    (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord) (dS' : List CreateRecord),
    EvalStmt prog st T C D s st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 (invalStep prog I s) st' fr' L (pc + 1)
    ∧ fr'.exec.stack = []
    ∧ RecorderCoupled log fr' gS' sS' cS' dS'
    ∧ StreamsAligned self log gS' cS' dS' T' C' D'

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
    StreamsAligned self log log.gas log.calls log.creates
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
bridges to the beginCall frame via `Runs.trans`. The reachable create-resolves seam in
`PrecompileAssumptions` supplies the modellability side-condition that
`cleanHalts_of_runWithLog` needs. TRACTABILITY: now. -/
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
    (hne : ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt → HaltNonException halt) :
    ∃ fr₀' : Frame, Runs fr₀ fr₀'
      ∧ DriveCorrLog prog sloadChg log params.recipient (entryState params) fr₀' prog.entry
          log.gas log.sloads log.calls log.creates := by
  -- the beginCall frame is the entry `codeFrame`.
  have hfr : fr₀ = codeFrame params (lower prog) :=
    (Sum.inl.injEq _ _).mp (hbegin.symm.trans (beginCall_code params (lower prog) hcode))
  subst hfr
  -- entry block, present and offset-0.
  obtain ⟨bentry, hbentry⟩ := hwl.closed.entry_present
  have hbtl : prog.blocks.toList[prog.entry.idx]? = some bentry := toList_of_blockAt hbentry
  have hbound : offsetTable (matCache prog) (defsOf prog) prog.blocks prog.entry.idx < 2 ^ 32 :=
    hwl.closed.entry_bound
  have hoff0 : offsetTable (matCache prog) (defsOf prog) prog.blocks prog.entry.idx = 0 := by
    unfold offsetTable; rw [hwl.entry0]; simp
  -- the entry `codeFrame` field reductions.
  have hpc : (codeFrame params (lower prog)).exec.pc
      = UInt32.ofNat (offsetTable (matCache prog) (defsOf prog) prog.blocks prog.entry.idx) := by
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
    fun fr' hr => hseams.createResolves fr' ⟨_, hbegin, hr⟩
  have hclean₀ : CleanHaltsNonException (codeFrame params (lower prog)) :=
    cleanHalts_of_runWithLog (prog := prog) hrun hbegin hcr hcc hne
  -- entry coupling, carried across the `JUMPDEST` step.
  have hcp₀ :
      RecorderCoupled log (codeFrame params (lower prog)) log.gas log.sloads log.calls log.creates :=
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
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t e))
    (hne : e ≠ .gas) (hns : ∀ k, e ≠ .sload k)
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hv : evalExpr st 0 e = some w)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.assign t e) := by
  -- Fire `StmtTies'` arm (1) at this cursor with the coupling + clean-halt in hand.
  obtain ⟨hslot, hstepS, hscoped', hmem'⟩ :=
    hties.1 pc t e w st fr gS sS cS dS
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False))
      hcur hne hns hcorr hcp hch hv
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
        emitStmt_assign_remat (matCache prog) (defsOf prog) t e hslot]
    simp
  have hstep : EvalStmt prog st T C D (.assign t e) (st.setLocal t w) T C D :=
    EvalStmt.assignPure hne hv
  have hsound' : DefsSoundS prog
      (invalStep prog ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.assign t e))
      (st.setLocal t w) :=
    defsSoundS_preserved_step hwl.defsCons hb hcur hstep hcorr.defsSound
  -- Package: `st' = st.setLocal t w`, `fr' = fr`, streams/suffixes UNCHANGED.
  refine ⟨st.setLocal t w, fr, T, C, D, gS, sS, cS, dS,
    hstep,
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
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t .gas))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.assign t .gas) := by
  classical
  let I := (b.stmts.take pc).foldl (invalStep prog) (fun _ => False)
  obtain ⟨hslotdef, hstepS, hslots, hghead, hscoped', hslot63, hslotplat, hpcbound⟩ :=
    hties.2.2.1 pc t st fr gS sS cS dS I hcur hcorr hcp hch
  cases hg : gS with
  | nil => simp [hg] at hghead
  | cons g gS' =>
    have hgeq : g = UInt256.ofUInt64
        (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase) := by
      simpa [hg] using hghead
    subst g
    have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
    obtain ⟨hdgas, hdpush, hdmstore⟩ :=
      decode_gasstash hbt hcur hslotdef hpcbound hcorr
    obtain ⟨hgasGas, hgasPush, words', hmem, hgasMem, hgasMstore⟩ :=
      CleanHaltExtract.gas_envelope_of_cleanHalt fr (slotOf t) hch hcorr.stack_nil
        hdgas hdpush hdmstore
    let endFr := mstoreFrame
      (pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32)
      (UInt256.ofNat (slotOf t))
      (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)) words' []
    have hstash := stash_tail_gas fr (slotOf t) words' hcorr.stack_nil
      hdgas (by simpa [gasFrame_pc] using hdpush)
      (by simpa [gasFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore)
      hgasGas hgasPush hmem hgasMem hgasMstore
    have hszGas : fr.exec.stack.size + 1 ≤ 1024 := by rw [hcorr.stack_nil]; simp
    have hgasStep := stepFrame_gas fr hdgas hszGas hgasGas
    have hisGas : isGasOp fr = true := by unfold isGasOp; rw [hdgas]; rfl
    have hcpGas : RecorderCoupled log (gasFrame fr) gS' sS cS dS := by
      simpa [gasFrame] using (recorderCoupled_step_gas (by simpa [hg] using hcp) hisGas hgasStep).1
    let frp := pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32
    have hpushStep : stepFrame (gasFrame fr) = .next frp.exec :=
      stepFrame_push (gasFrame fr) .PUSH32 (UInt256.ofNat (slotOf t)) 32 (by decide)
        hdpush (by decide) (by decide) hgasPush (by rw [gasFrame_stack, hcorr.stack_nil]; simp)
    have hcpPush : RecorderCoupled log frp gS' sS cS dS := by
      apply recorderCoupled_step_other hcpGas
      · unfold isGasOp; rw [hdpush]; rfl
      · unfold isSloadOp; rw [hdpush]; rfl
      · simpa [frp] using hpushStep
    let hgasVal : Word := UInt256.ofUInt64
      (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)
    have hmstoreStep : stepFrame frp = .next
        (mstoreFrame frp (UInt256.ofNat (slotOf t)) hgasVal words' []).exec := by
      apply stepFrame_mstore frp (UInt256.ofNat (slotOf t)) hgasVal words' []
      · simpa [frp, gasFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
      · simp only [frp, pushFrameW_stack', gasFrame_stack, hcorr.stack_nil]
        rfl
      · simp [frp, gasFrame_stack, hcorr.stack_nil]
      · exact hmem
      · exact hgasMem
      · exact hgasMstore
    have hcpEnd : RecorderCoupled log endFr gS' sS cS dS := by
      have hcpm := recorderCoupled_step_other hcpPush
        (by
          unfold isGasOp
          have hd : decode frp.exec.executionEnv.code frp.exec.pc =
              some (.Smsf .MSTORE, .none) := by
            simpa [frp, gasFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
          rw [hd]; rfl)
        (by
          unfold isSloadOp
          have hd : decode frp.exec.executionEnv.code frp.exec.pc =
              some (.Smsf .MSTORE, .none) := by
            simpa [frp, gasFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
          rw [hd]; rfl)
        hmstoreStep
      simpa [endFr, frp, hgasVal] using hcpm
    have hEval : EvalStmt prog st
        (hgasVal :: gS') C D (.assign t .gas) (st.setLocal t hgasVal) gS' C D :=
      EvalStmt.assignGas
    have hsound' := defsSoundS_preserved_step hwl.defsCons hb hcur hEval hcorr.defsSound
    have hstash' : StashRuns fr endFr (slotOf t) hgasVal
        (emitStmt (matCache prog) (defsOf prog) (.assign t .gas)).length [] := by
      simpa [endFr, hgasVal, emitStmt_assign_slot, hslotdef, emitImm_length] using hstash
    obtain ⟨hrun, hcorr', hstack⟩ := sim_assign_gas hbt hcur hslotdef hcorr
      hstepS hslots hscoped' hsound' ⟨hslot63, hslotplat, hstash'⟩
    rcases hal with ⟨rfl, hC, hD⟩
    rw [hg]
    exact ⟨st.setLocal t hgasVal, endFr, gS', C, D, gS', sS, cS, dS,
      hEval, hrun, hcorr', hstack, hcpEnd, ⟨rfl, hC, hD⟩⟩

-- S1 (`recorderCoupled_matRunsC`, the coupling fold over a `materialise` run) is RELOCATED
-- to `Machinery.lean` (pure relocation): the R3 arg-push producer `call_args_run_of_coupled`
-- there consumes it, and `Machinery` cannot import this module.

theorem simStmt_coupled_sload {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {t k : Tmp} {kv : Word} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t (.sload k)))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hkey : st.locals k = some kv)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.assign t (.sload k)) := by
  classical
  let I := (b.stmts.take pc).foldl (invalStep prog) (fun _ => False)
  obtain ⟨hslotdef, hstepS, hslots, hwval, hscoped', hslot63, hslotplat,
      hstkKey, hflat⟩ :=
    hties.2.1 pc t k kv st fr gS sS cS dS I hcur hcorr hcp hch hkey
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  have hfree : RematClosureFree prog I (.tmp k) :=
    hwl.scopedUses L b pc (.assign t (.sload k)) hb hcur k (by simp [readsStmt, usesInExpr])
  have hemit : emitStmt (matCache prog) (defsOf prog) (.assign t (.sload k))
      = matCache prog k ++ [Byte.sload]
          ++ emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore] := by
    rw [emitStmt_assign_slot (matCache prog) (defsOf prog) t (.sload k) hslotdef]
    rfl
  have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.assign t (.sload k))).length =
      (matCache prog k).length + 35 := by
    rw [hemit]
    simp only [List.length_append, List.length_singleton, emitImm_length]
  have hseg : ∀ j, j < (matCache prog k).length + 35 →
      (flatBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.assign t (.sload k)))[j]? := by
    intro j hj
    exact flatBytes_at_pcOf_offset prog L b pc (.assign t (.sload k)) j hbt hcur
      (by rw [hemitlen]; omega)
  have hsegk : ∀ j, j < (matExpr (matCache prog) (.tmp k)).length →
      (flatBytes prog)[pcOf prog L pc + j]? = (matExpr (matCache prog) (.tmp k))[j]? := by
    intro j hj
    simp only [matExpr_tmp] at hj ⊢
    rw [hseg j (by omega), hemit]
    rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_singleton]; omega),
        List.getElem?_append_left
          (by simp only [List.length_append, List.length_singleton]; omega),
        List.getElem?_append_left hj]
  have hbound := hwl.wf.bound_sload L b pc t k hbt hcur
  have hdk : MatDecC prog hwl.defsCons hwl.defEnvOrdered fr.exec.executionEnv.code fr.exec.pc
      (.tmp k) := by
    rw [hcorr.code_eq, hcorr.pc_eq]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp k) (pcOf prog L pc)
      (by simp only [matExpr_tmp]; omega) hsegk
  have hstkC : fr.exec.stack.size +
      (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp k)).length ≤ 1024 := by
    simpa only [chargeExpr_tmp] using hstkKey
  have hgasKey := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st 0 I (.tmp k) kv fr hdk hcorr.defsSound hfree hcorr.wellScoped
    hcorr.storage (by nofun) (by nofun) hcorr.memAgree hkey hch hstkC
  obtain ⟨frk, hmrk, hcpk⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st 0 log gS sS cS dS I (.tmp k) kv fr hdk hcorr.defsSound hfree
    hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree hkey hgasKey hstkC hcp
  obtain ⟨hdsload, hdpush, hdmstore⟩ :=
    decode_sloadstash hbt hcur hslotdef hbound hcorr hmrk
  have hkw : st.world kv = st.world kv := rfl
  have hawk := hflat frk hmrk
  obtain ⟨hgasSload, hgasPush, words', hmem, hgasMem, hgasMstore⟩ :=
    CleanHaltExtract.sload_envelope_of_cleanHalt fr frk kv (slotOf t)
      hch hcorr.stack_nil hmrk rfl hdsload hdpush hdmstore
  have hkstk : frk.exec.stack = kv :: [] := by rw [hmrk.stack, hcorr.stack_nil]; rfl
  have hksz : frk.exec.stack.size ≤ 1024 := by rw [hkstk]; simp
  have hsloadStep := stepFrame_sload frk kv [] hdsload hkstk hksz hgasSload
  have hisSload : isSloadOp frk = true := by unfold isSloadOp; rw [hdsload]; rfl
  obtain ⟨n, sS', hsSeq⟩ := sloadSuffix_nonempty hcpk hisSload hsloadStep
  subst hsSeq
  have hcpSload : RecorderCoupled log (sloadFrame frk kv []) gS sS' cS dS := by
    simpa [sloadFrame] using (recorderCoupled_sload hcpk hisSload hsloadStep).1
  let frp := pushFrameW (sloadFrame frk kv []) (UInt256.ofNat (slotOf t)) 32
  have hpushStep : stepFrame (sloadFrame frk kv []) = .next frp.exec :=
    stepFrame_push (sloadFrame frk kv []) .PUSH32 (UInt256.ofNat (slotOf t)) 32 (by decide)
      hdpush (by decide) (by decide) hgasPush
      (by simp [sloadFrame_stack])
  have hcpPush : RecorderCoupled log frp gS sS' cS dS := by
    apply recorderCoupled_step_other hcpSload
    · unfold isGasOp; rw [hdpush]; rfl
    · unfold isSloadOp; rw [hdpush]; rfl
    · simpa [frp] using hpushStep
  let w := st.world kv
  let endFr := mstoreFrame frp (UInt256.ofNat (slotOf t)) w words' []
  have hmstoreStep : stepFrame frp = .next endFr.exec := by
    apply stepFrame_mstore frp (UInt256.ofNat (slotOf t)) w words' []
    · simpa [frp, sloadFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
    · simp only [frp, pushFrameW_stack', sloadFrame_stack, hmrk.storage,
        hcorr.stack_nil, w, Stack.push]
      rw [hcorr.storage kv]
    · simp [frp, sloadFrame_stack, hcorr.stack_nil]
    · exact hmem
    · exact hgasMem
    · exact hgasMstore
  have hcpEnd : RecorderCoupled log endFr gS sS' cS dS := by
    have hcpm := recorderCoupled_step_other hcpPush
      (by
        unfold isGasOp
        have hd : decode frp.exec.executionEnv.code frp.exec.pc =
            some (.Smsf .MSTORE, .none) := by
          simpa [frp, sloadFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
        rw [hd]; rfl)
      (by
        unfold isSloadOp
        have hd : decode frp.exec.executionEnv.code frp.exec.pc =
            some (.Smsf .MSTORE, .none) := by
          simpa [frp, sloadFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
        rw [hd]; rfl)
      hmstoreStep
    simpa [endFr] using hcpm
  have hwself : selfStorage fr kv = w := by simp [w, hcorr.storage kv]
  have hstash := stash_tail_sload fr frk k kv w (slotOf t) words' hcorr.stack_nil hmrk
    hawk hwself hdsload
    (by simpa [sloadFrame_pc] using hdpush)
    (by simpa [sloadFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore)
    hgasSload hgasPush hmem hgasMem hgasMstore
  have hstash' : StashRuns fr endFr (slotOf t) w
      (emitStmt (matCache prog) (defsOf prog) (.assign t (.sload k))).length [] := by
    rw [hemitlen]
    simpa [endFr, frp, w] using hstash
  have hEval : EvalStmt prog st T C D (.assign t (.sload k)) (st.setLocal t w) T C D := by
    exact EvalStmt.assignPure (by simp) (by simpa [w] using hwval)
  have hsound' := defsSoundS_preserved_step hwl.defsCons hb hcur hEval hcorr.defsSound
  obtain ⟨hrun, hcorr', hstack⟩ := sim_assign_sload hbt hcur hslotdef hcorr hstepS
    hslots (by simpa [w] using hwval) (by simpa [w] using hscoped') hsound' ⟨hslot63, hslotplat, hstash'⟩
  exact ⟨st.setLocal t w, endFr, T, C, D, gS, sS', cS, dS,
    hEval, hrun, hcorr', hstack, hcpEnd, hal⟩
/-- **S3 — `sim_sstore_stmt'`, the WIP re-plumb of `sim_sstore_stmt`.** Same conclusion as the
in-tree `sim_sstore_stmt` (`Sim/SimStmt.lean`), but (i) DROPS the unsatisfiable `∀`-quantified
`hsstore : SstoreRealises fr kw vw acc` — its three runtime facts are derived POINT-WISE at the
internal SSTORE frame `frk` from the threaded `SelfPresent fr` + clean-halt via
`sstoreRealises_at_frame` (R4); and (ii) THREADS the recorder coupling
`RecorderCoupled log fr gS sS cS` across the two `materialise` runs (S1 `recorderCoupled_matRunsC`,
value then key) and the SSTORE frame itself (S2, one `recorderCoupled_step_other`, R7d — SSTORE is
neither GAS nor SLOAD), returning it at the post-frame. The `Corr` re-establishment body is verbatim
`sim_sstore_stmt`. REAL; no sorry. -/
theorem sim_sstore_stmt' {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {log : RunLog}
    {st : IRState} {key value : Tmp} {kw vw : Word}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    {I : Tmp → Prop}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Lir.Corr prog sloadChg obs I st fr L pc)
    (hk : st.locals key = some kw) (hv : st.locals value = some vw)
    (hsc : Lir.StepScoped prog st (.sstore key value))
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (hfreeValue : RematClosureFree prog I (.tmp value))
    (hfreeKey : RematClosureFree prog I (.tmp key))
    (hdv : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc (.tmp value))
    (hdk : MatDecC prog hdc hord fr.exec.executionEnv.code
            (fr.exec.pc + UInt32.ofNat (matCache prog value).length) (.tmp key))
    (hdop : decode fr.exec.executionEnv.code
            (fr.exec.pc
              + UInt32.ofNat (matCache prog value).length
              + UInt32.ofNat (matCache prog key).length)
            = some (.Smsf .SSTORE, .none))
    (hcs : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstk : (chargeCache prog sloadChg value).length
              + (chargeCache prog sloadChg key).length + 1 ≤ 1024) :
    ∃ fr', Runs fr fr'
      ∧ Lir.Corr prog sloadChg obs I (st.setStorage kw vw) fr' L (pc + 1)
      ∧ fr'.exec.stack = []
      ∧ RecorderCoupled log fr' gS sS cS dS := by
  classical
  set lv := (matCache prog value).length with hlv
  set lk := (matCache prog key).length with hlk
  have hstacknil := hcorr.stack_nil
  -- == B1 call 1: materialise `value` from `fr`, leaving `[vw]`, carrying the coupling.
  -- The value-channel gas bound is DERIVED from the clean-halt witness. ==
  have hevv : V2.evalExpr st obs (.tmp value) = some vw := hv
  have hszfr : fr.exec.stack.size = 0 := by rw [hstacknil]; rfl
  have hstkv : fr.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp value)).length ≤ 1024 := by
    simp only [chargeExpr_tmp]; omega
  have hgasv : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp value)).sum
      ≤ fr.exec.gasAvailable.toNat :=
    materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp value) vw fr
      hdv hcorr.defsSound hfreeValue hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
      hevv hcs hstkv
  obtain ⟨frv, hmrv, hcpv⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs log gS sS cS dS
    I (.tmp value) vw fr
    hdv hcorr.defsSound hfreeValue hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
    hevv hgasv hstkv hcp
  have hvcode : frv.exec.executionEnv.code = fr.exec.executionEnv.code := hmrv.code
  have hvaddr : frv.exec.executionEnv.address = fr.exec.executionEnv.address := hmrv.addr
  have hvpc : frv.exec.pc = fr.exec.pc + UInt32.ofNat lv := hmrv.pc
  have hvstk : frv.exec.stack = vw :: fr.exec.stack := by rw [hmrv.stack]; rfl
  -- == B1 call 2: materialise `key` from `frv`, leaving `[kw, vw]`, carrying the coupling ==
  have hevk : V2.evalExpr st obs (.tmp key) = some kw := hk
  have hcsv : CleanHaltsNonException frv := cleanHaltsNonException_forward hcs hmrv.runs
  have hdk' : MatDecC prog hdc hord frv.exec.executionEnv.code frv.exec.pc (.tmp key) := by
    rw [hvcode, hvpc]; exact hdk
  have hfrvsz : frv.exec.stack.size = fr.exec.stack.size + 1 := by rw [hvstk]; simp
  have hstkk : frv.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp key)).length ≤ 1024 := by
    rw [hfrvsz, hszfr]; simp only [chargeExpr_tmp]; omega
  have hgask : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp key)).sum
      ≤ frv.exec.gasAvailable.toNat :=
    materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp key) kw frv
      hdk' hcorr.defsSound hfreeKey hcorr.wellScoped
      (hcorr.storage.transport hmrv.storage) (by nofun) (by nofun)
      (hcorr.memAgree.transport hmrv.memBytes hmrv.memActive) hevk hcsv hstkk
  obtain ⟨frk, hmrk, hcpk⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs log gS sS cS dS
    I (.tmp key) kw frv
    hdk' hcorr.defsSound hfreeKey hcorr.wellScoped
    (hcorr.storage.transport hmrv.storage) (by nofun) (by nofun)
    (hcorr.memAgree.transport hmrv.memBytes hmrv.memActive) hevk hgask hstkk hcpv
  have hkcode : frk.exec.executionEnv.code = fr.exec.executionEnv.code := by
    rw [hmrk.code, hvcode]
  have hkvalid : frk.validJumps = fr.validJumps := by
    rw [hmrk.validJumps, hmrv.validJumps]
  have hkaddr : frk.exec.executionEnv.address = fr.exec.executionEnv.address := by
    rw [hmrk.addr, hvaddr]
  have hkpc : frk.exec.pc = fr.exec.pc + UInt32.ofNat lv + UInt32.ofNat lk := by
    have h : frk.exec.pc = frv.exec.pc + UInt32.ofNat lk := hmrk.pc
    rw [h, hvpc]
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
  have hcpf : RecorderCoupled log (sstoreFrame frk kw vw []) gS sS cS dS :=
    recorderCoupled_step_other hcpk
      (by unfold isGasOp; rw [hkdec]; rfl) (by unfold isSloadOp; rw [hkdec]; rfl)
      (stepFrame_sstore frk kw vw [] hkdec hkstk hksz hkmod hstip hcost)
  refine ⟨sstoreFrame frk kw vw [], (hmrv.runs.trans hmrk.runs).trans hsrun, ?_, ?_, hcpf⟩
  · -- re-establish `Corr` at `(L, pc+1)` for `st.setStorage kw vw` (verbatim `sim_sstore_stmt`).
    have hfraddr : (sstoreFrame frk kw vw []).exec.executionEnv.address
        = frk.exec.executionEnv.address := sstoreFrame_addr frk kw vw []
    have hemit : (emitStmt (matCache prog) (defsOf prog) (.sstore key value)).length
        = lv + lk + 1 := by
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
    · have hstepS : EvalStmt prog st ([] : Trace) ([] : CallStream) ([] : CreateStream)
          (.sstore key value) (st.setStorage kw vw) [] [] [] := EvalStmt.sstore hk hv
      exact defsSoundS_preserved_step hdc (blockAt_of_toList prog L b hb) hs
        hstepS hcorr.defsSound
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
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hk : st.locals key = some kw) (hvv : st.locals value = some vw)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.sstore key value) := by
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  -- ties arm (4): `StepScopedS` + the stack-room fold (fired with coupling + clean-halt).
  obtain ⟨hstepS, hstkbound⟩ :=
    hties.2.2.2.1 pc key value kw vw st fr gS sS cS dS
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False))
      hcur hcorr hcp hch hk hvv
  -- `StepScopedS` ⟹ the per-state `StepScoped` the sstore B3 preservation consumes (the static
  -- form quantifies over ALL registered defs, so it dominates the state-gated one).
  have hsc : Lir.StepScoped prog st (.sstore key value) := by
    intro t₀ e₀ hdef _ _ keyk; exact hstepS t₀ e₀ hdef keyk
  -- well-formedness: the statement pc bound (`hwl.wf`; the fold emission needs no
  -- fuel-sufficiency facts — structural termination).
  have hbound := hwl.wf.bound_sstore L b pc key value hbt hcur
  have hemit : emitStmt (matCache prog) (defsOf prog) (.sstore key value)
      = matCache prog value ++ matCache prog key ++ [Byte.sstore] := emitStmt_sstore ..
  have hlen : (emitStmt (matCache prog) (defsOf prog) (.sstore key value)).length
      = (matCache prog value).length + (matCache prog key).length + 1 := by
    rw [hemit]; simp only [List.length_append, List.length_singleton]
  -- decode bundle at the static cursors (`matDecC_of_lower` / `sstore_op_decode`), as in the
  -- in-tree `sim_sstore_stmt_lowered` decode-discharge (Layer A over `lower prog`).
  have hdv : MatDecC prog hwl.defsCons hwl.defEnvOrdered fr.exec.executionEnv.code
      fr.exec.pc (.tmp value) := by
    rw [hcorr.code_eq, hcorr.pc_eq]
    have := matDecC_of_lower prog hwl.defsCons hwl.defEnvOrdered L b pc (.sstore key value)
      0 (.tmp value) hbt hcur
      (by simpa using sstore_sub_value (matCache prog) (defsOf prog) key value)
      (by simp only [matExpr_tmp, Nat.zero_add]; rw [hlen]; omega)
      (by simp only [matExpr_tmp]; omega)
    simpa using this
  have hdk : MatDecC prog hwl.defsCons hwl.defEnvOrdered fr.exec.executionEnv.code
      (fr.exec.pc + UInt32.ofNat (matCache prog value).length) (.tmp key) := by
    rw [hcorr.code_eq, hcorr.pc_eq, ofNat_add']
    exact matDecC_of_lower prog hwl.defsCons hwl.defEnvOrdered L b pc (.sstore key value)
      (matCache prog value).length (.tmp key) hbt hcur
      (by simpa using sstore_sub_key (matCache prog) (defsOf prog) key value)
      (by simp only [matExpr_tmp]; rw [hlen]; omega)
      (by simp only [matExpr_tmp]; omega)
  have hdop : decode fr.exec.executionEnv.code
      (fr.exec.pc + UInt32.ofNat (matCache prog value).length
        + UInt32.ofNat (matCache prog key).length) = some (.Smsf .SSTORE, .none) := by
    rw [hcorr.code_eq, hcorr.pc_eq, ofNat_add', ofNat_add',
        show pcOf prog L pc + (matCache prog value).length + (matCache prog key).length
          = pcOf prog L pc + ((matCache prog value).length + (matCache prog key).length)
          from by omega]
    exact sstore_op_decode prog L b pc key value hbt hcur (by omega)
  have hfreeValue := hwl.scopedUses L b pc (.sstore key value) hb hcur value
    (by simp [readsStmt])
  have hfreeKey := hwl.scopedUses L b pc (.sstore key value) hb hcur key
    (by simp [readsStmt])
  -- fire S3 (`sim_sstore_stmt'`): the two-frame materialise fold + the point-wise R4 realisation
  -- + the coupling transported to the post-frame.
  obtain ⟨fr', hruns, hcorr', hstacknil', hcpf⟩ :=
    sim_sstore_stmt' hbt hcur hcorr hk hvv hsc hwl.defsCons hwl.defEnvOrdered
      hfreeValue hfreeKey hdv hdk hdop
      hch hsp hcp hstkbound
  -- S4 — assemble the `CoupledAdvance`: `EvalStmt.sstore` consumes NO stream head (T/C/D and
  -- gS/sS/cS ride unchanged), so the alignment `hal` carries over verbatim.
  exact ⟨st.setStorage kw vw, fr', T, C, D, gS, sS, cS, dS,
    EvalStmt.sstore hk hvv, hruns, hcorr', hstacknil', hcpf, hal⟩

/-! ### The CALL arm's support bricks (all REAL, no sorry)

* `stmt_offset_bound_of_codeFits` — the generic per-statement byte-offset bound under the
  flagship scalar `codeFits` (stated for ANY statement; Machinery's `call_stmt_offset_bound`
  is `private` and CALL-only, so this local copy is the reusable form).
* `call_post_wellScoped'` — the call arm's post-state scoping fold: world replacement
  preserves the fold; a bound result tmp's slot registration comes from `DefsConsistent`'s
  call clause.
* `sim_call_stmt'` — the SCOPED, fixed-endpoint re-plumb of `sim_call_stmt` that the coupled
  walk needs (it must CONSTRUCT the Route-B tail itself to transport the recorder coupling
  frame-by-frame). -/

private theorem stmt_offset_bound_of_codeFits {prog : Program} {L : Label} {b : Block}
    {pc : Nat} {s : Stmt}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some s)
    {k : Nat}
    (hk : k < (emitStmt (matCache prog) (defsOf prog) s).length) :
    pcOf prog L pc + k < 2 ^ 32 := by
  have hbyte0 : (emitStmt (matCache prog) (defsOf prog) s)[k]?
      = some ((emitStmt (matCache prog) (defsOf prog) s)[k]) :=
    List.getElem?_eq_getElem hk
  have hflat : (flatBytes prog)[pcOf prog L pc + k]?
      = some ((emitStmt (matCache prog) (defsOf prog) s)[k]) := by
    rw [flatBytes_at_pcOf_offset prog L b pc s k (Lir.toList_of_blockAt hb) hcur hk]
    exact hbyte0
  rw [List.getElem?_eq_some_iff] at hflat
  exact lt_of_lt_of_le hflat.1 (Nat.le_of_lt hcodeFits)

/-- The call arm's post-state scoping fold: world replacement preserves the fold; a bound
result tmp's slot registration comes from `DefsConsistent`'s call clause. REAL; no sorry. -/
private theorem call_post_wellScoped' {prog : Program} {L : Label} {b : Block} {pc : Nat}
    {cs : CallSpec} {st : IRState} {world' : World} {success : Word}
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hdefsCons : DefsConsistent prog)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none) :
    ∀ t, (match cs.resultTmp with
            | some t' => { st with world := world' }.setLocal t' success
            | none => { st with world := world' }).locals t ≠ none →
          (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
          ∧ defsOf prog t ≠ none := by
  intro t hlocal
  cases hres : cs.resultTmp with
  | none =>
      have hlocal' : st.locals t ≠ none := by
        simpa [hres] using hlocal
      exact hscoped t hlocal'
  | some u =>
      by_cases ht : t = u
      · subst u
        have hslot : defsOf prog t = some (.slot (slotOf t)) :=
          (hdefsCons L b pc hb).2.1 cs t hcur hres
        exact ⟨Or.inr ⟨slotOf t, hslot⟩, by simp [hslot]⟩
      · have hlocal' : st.locals t ≠ none := by
          simpa [IRState.setLocal, hres, ht] using hlocal
        exact hscoped t hlocal'

/-- **`sim_call_stmt'`, the SCOPED, fixed-endpoint re-plumb of `sim_call_stmt`.** Two changes
against the in-tree original (`Sim/SimStmt.lean:596`): (i) the strong `DefsSound`/`StepScoped`
inputs are REPLACED by a directly-supplied scoped post-state soundness `hsound' : DefsSoundS
prog I' st'` (the coupled walk produces it via `defsSoundS_preserved_step` at `invalStep I
(.call cs)`), so the conclusion `Corr` is scoped at `I'`; and (ii) the Route-B tail is taken at
a FIXED endpoint `endFr` (a `StashRuns` bundle for `resultTmp = some t`, the pinned `popFrame`
for `none`) instead of the original's opaque existential — the coupled caller CONSTRUCTS the
tail run itself (it must, to transport the recorder coupling frame-by-frame across it). The
`Corr` re-establishment body is verbatim `sim_call_stmt`. REAL; no sorry. -/
theorem sim_call_stmt' {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : IRState} {cs : CallSpec}
    {L : Label} {b : Block} {pc : Nat} {argsLen : Nat}
    {fr callFr resumeFr endFr : Frame} {result : Evm.CallResult} {pd : Evm.PendingCall}
    {self : AccountAddress} {I' : Tmp → Prop}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.call cs))
    (hfrpc : fr.exec.pc = UInt32.ofNat (pcOf prog L pc))
    (hargslen : argsLen
      = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ matCache prog cs.callee
          ++ matCache prog cs.gasFwd).length)
    (hargs : Runs fr callFr)
    (hcallpc : callFr.exec.pc = fr.exec.pc + UInt32.ofNat argsLen)
    (hcallmem : callFr.exec.toMachineState.memory = fr.exec.toMachineState.memory)
    (hcallactive : fr.exec.toMachineState.activeWords.toNat
      ≤ callFr.exec.toMachineState.activeWords.toNat)
    (hcall : CallReturns callFr resumeFr)
    (hresume : resumeFr = Evm.resumeAfterCall result pd)
    (hst' : st' = (match cs.resultTmp with
        | some t => { st with world := fun key => evmCallOracle.postStorage result pd self key }.setLocal
                      t (callSuccessFlag result pd)
        | none   => { st with world := fun key => evmCallOracle.postStorage result pd self key }))
    (hresaddr : resumeFr.exec.executionEnv.address = self)
    (hrescode : resumeFr.exec.executionEnv.code = lower prog)
    (hrescanmod : resumeFr.exec.executionEnv.canModifyState = true)
    (hrespc : resumeFr.exec.pc = callFr.exec.pc + 1)
    (hresstack : resumeFr.exec.stack = callSuccessFlag result pd :: [])
    (hresmem : resumeFr.exec.toMachineState.memory = callFr.exec.toMachineState.memory)
    (hresactive : callFr.exec.toMachineState.activeWords.toNat
      ≤ resumeFr.exec.toMachineState.activeWords.toNat)
    (hresvalidjumps : resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0)
    (hsound' : DefsSoundS prog I' st')
    (hmem : Lir.MemRealises prog st fr)
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    (hscoped' : ∀ t, st'.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (htailSome : ∀ t, cs.resultTmp = some t →
      (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
      ∧ Lir.StashRuns resumeFr endFr (slotOf t) (callSuccessFlag result pd) 34 [])
    (htailNone : cs.resultTmp = none →
      Runs resumeFr endFr ∧ endFr = popFrame resumeFr []) :
    Runs fr endFr ∧ Lir.Corr prog sloadChg obs I' st' endFr L (pc + 1)
      ∧ endFr.exec.stack = [] := by
  classical
  -- == the Runs to `resumeFr`: arg pushes then the returning CALL node ==
  have hruns0 : Runs fr resumeFr := hargs.trans (sim_call hcall (Runs.refl resumeFr))
  -- `M3` re-established at `resumeFr`: `selfStorage resumeFr key = postStorage…`.
  have hM3 : ∀ key,
      selfStorage resumeFr key = evmCallOracle.postStorage result pd self key := by
    intro key
    rw [selfStorage_eq_storageAt, hresaddr, hresume]; rfl
  -- `emitStmt .call` length = argsLen + 1 + tailLen.
  have hemitcall : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ matCache prog cs.callee ++ matCache prog cs.gasFwd)
        ++ [Byte.call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none   => [Byte.pop]) := rfl
  -- pre-call MemRealises transports `fr → callFr → resumeFr`.
  have hmemRes : Lir.MemRealises prog st resumeFr :=
    ((hmem.transport hcallmem hcallactive).transport hresmem hresactive)
  -- == case on the result tmp: the fixed-endpoint Route-B tail ==
  cases hr : cs.resultTmp with
  | none =>
    -- POP tail: `endFr = popFrame resumeFr []`, stack `[]`, memory untouched.
    obtain ⟨hpoprun, hendeq⟩ := htailNone hr
    subst hendeq
    refine ⟨hruns0.trans hpoprun, ?_, by rw [popFrame_stack]⟩
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.call cs)).length
        = argsLen + 1 + 1 := by
      rw [hemitcall, hr]
      set argsBlock := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hab
      rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton,
        ← hargslen]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (argsLen + 1 + 1) := by
      rw [pcOf_succ prog L b pc (.call cs) hb hs, hemitlen]
    refine
      { pc_eq := ?_
        code_eq := ?_
        validJumps_eq := ?_
        stack_nil := by rw [popFrame_stack]
        can_modify := ?_
        storage := ?_
        defsSound := hsound'
        wellScoped := hscoped'
        memAgree := ?_ }
    · -- M1
      rw [popFrame_pc, hrespc, hcallpc, hfrpc, hpcN,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add,
          show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
      ac_rfl
    · rw [popFrame_code, hrescode]
    · rw [popFrame_validJumps, popFrame_code, hresvalidjumps]
    · rw [popFrame_canMod, hrescanmod]
    · -- M3: world is the resumed self-lens; POP doesn't touch storage.
      intro key
      have hst'none : st' = { st with world := fun key => evmCallOracle.postStorage result pd self key } := by
        rw [hst', hr]
      rw [hst'none]
      show selfStorage (popFrame resumeFr []) key = _
      rw [show selfStorage (popFrame resumeFr []) key = selfStorage resumeFr key from rfl]
      exact hM3 key
    · -- memAgree: `st'.locals = st.locals`, POP preserves memory bytes + activeWords.
      have hloceq : st' = { st with world := fun key => evmCallOracle.postStorage result pd self key } := by
        rw [hst', hr]
      intro tw slot v hdef hloc
      rw [hloceq] at hloc
      exact (hmemRes.transport (by rw [popFrame_memory]) (by rw [popFrame_activeWords]))
        tw slot v hdef hloc
  | some t =>
    -- PUSH slot; MSTORE tail at the FIXED endpoint `endFr` (the caller's coupled stash run).
    obtain ⟨hslot63, hslotplat, hstash⟩ := htailSome t hr
    obtain ⟨hendrun, hendmembytes, hendmemactive, hendpc, hendcode,
      hendvalid, hendaddr, hendcanmod, _, hendstorage, hendstk⟩ := hstash
    set flag := callSuccessFlag result pd with hflag
    set slot := slotOf t with hslotdef
    refine ⟨hruns0.trans hendrun, ?_, hendstk⟩
    have hslotlt256 : slot < 2 ^ 256 := by
      have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    have hslotEq : (UInt256.ofNat slot).toNat = slot := by
      rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslotlt256]
    have hslot63' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by rw [hslotEq]; exact hslot63
    have hslotplat' : (UInt256.ofNat slot).toNat < 2 ^ System.Platform.numBits := by
      rw [hslotEq]; exact hslotplat
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.call cs)).length
        = argsLen + 1 + 34 := by
      rw [hemitcall, hr]
      set argsBlock := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hab
      rw [List.length_append, List.length_append, List.length_singleton, ← hargslen,
        List.length_append, List.length_singleton, emitImm_length]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (argsLen + 1 + 34) := by
      rw [pcOf_succ prog L b pc (.call cs) hb hs, hemitlen]
    refine
      { pc_eq := ?_
        code_eq := ?_
        validJumps_eq := ?_
        stack_nil := hendstk
        can_modify := ?_
        storage := ?_
        defsSound := hsound'
        wellScoped := hscoped'
        memAgree := ?_ }
    · -- M1
      rw [hendpc, hrespc, hcallpc, hfrpc, hpcN,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add,
          show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
      ac_rfl
    · rw [hendcode, hrescode]
    · rw [hendvalid, hendcode]; exact hresvalidjumps
    · rw [hendcanmod, hrescanmod]
    · -- M3: world is the resumed self-lens; the MSTORE tail preserves the self-lens.
      intro key
      rw [hst', hr]
      show selfStorage endFr key = _
      rw [hendstorage key]; exact hM3 key
    · -- memAgree: New slot binds flag; other call-result slots preserved.
      intro tw slot' v hdef hloc
      by_cases htw : tw = t
      · -- the just-bound call-result tmp `t`: `slot' = slotOf t = slot`, `v = flag`.
        subst htw
        have hvflag : v = flag := by
          have : st'.locals tw = some flag := by rw [hst', hr]; simp [V2.IRState.setLocal]
          rw [this] at hloc; exact (Option.some.inj hloc).symm
        have hslot'eq : slot' = slot := by
          rw [show slot = slotOf tw from rfl]
          exact hslots tw slot' hdef
        subst hslot'eq; subst hvflag
        refine ⟨?_, ?_, hslot63, ?_⟩
        · rw [hendmembytes]
          have := LirLean.MemAlgebra.mstore_memory_size resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag (by rw [hslotEq]; exact hslotplat)
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · rw [hendmemactive]
          have := LirLean.MemAlgebra.mstore_activeWords_covers resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63'
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot) hendmembytes hendmemactive]
          exact LirLean.MemAlgebra.mstore_reads_back resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63' hslotplat'
      · -- another bound tmp `tw ≠ t`: unchanged value; its slot survives the disjoint MSTORE.
        have hloc0 : st.locals tw = some v := by
          rw [hst', hr] at hloc
          simpa [V2.IRState.setLocal, htw] using hloc
        obtain ⟨hcm, ham, hreal, hval⟩ := hmemRes tw slot' v hdef hloc0
        have hslot'lt256 : slot' < 2 ^ 256 := by
          have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega
        have hslot'Eq : (UInt256.ofNat slot').toNat = slot' := by
          rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslot'lt256]
        have hslot'def : slot' = slotOf tw := hslots tw slot' hdef
        have htwne : t.id ≠ tw.id := fun h => htw (by cases t; cases tw; cases h; rfl)
        have hdisN : slot + 32 ≤ slot' ∨ slot' + 32 ≤ slot := by
          rw [hslotdef, hslot'def]
          exact LirLean.MemAlgebra.slot_windows_disjoint t.id tw.id htwne
        have hdisN' : (UInt256.ofNat slot').toNat + 32 ≤ (UInt256.ofNat slot).toNat
            ∨ (UInt256.ofNat slot).toNat + 32 ≤ (UInt256.ofNat slot').toNat := by
          rw [hslotEq, hslot'Eq]; exact hdisN.symm
        obtain ⟨hmem', hact', hval'⟩ :=
          LirLean.MemAlgebra.mstore_preserves_slot_grow resumeFr.exec.toMachineState
            (UInt256.ofNat slot) (UInt256.ofNat slot') flag hslot63' hslotplat' hcm ham hdisN'
        refine ⟨?_, ?_, hreal, ?_⟩
        · rw [hendmembytes]; exact hmem'
        · rw [hendmemactive]; exact hact'
        · rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot') hendmembytes hendmemactive]
          exact hval'.trans hval

/-- **P2-call — the external-CALL coupled step.** BLOCKER RESOLVED: R3's Piece B is closed on
main (`call_head_realises_coupled`, Machinery — the SAME Piece-A/B chain as
`callRealises_of_recorded`, kept coupling-alive: `call_args_run_of_coupled` →
`call_dispatch_of_coupled` → the CallsCode seam → `recorderCoupled_call_extract`, stopping
BEFORE the tail). This arm fires that bundle to get the arg-push run + the returning CALL + the
coupling advanced past the recorded record (tail suffix `cS'`); then it CONSTRUCTS the Route-B
tail itself — the coupling must be transported frame-by-frame across it, so the tail steps are
built here from the byte-layout decode anchors (`imm_leaf_decodeF`/`nonpush_leaf_decodeF` under
the `codeFits` bound) + the clean-halt envelopes (`next_push_of_cleanHalt`/
`next_mstore_of_cleanHalt`/`next_pop_of_cleanHalt`), each step advanced by R7d
`recorderCoupled_step_other` — and re-establishes `Corr` at the tail endpoint via the scoped
fixed-endpoint `sim_call_stmt'` (carrier `defsSoundS_preserved_step` at `invalStep I (.call cs)`
from the start). The `callSuffix` head `rec` positionally IS this call's recorded result, so
`EvalStmt.call` consumes exactly the aligned `callStreamOf` head; gas/sload/create suffixes ride
unchanged. -/
theorem simStmt_coupled_call {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {cs : CallSpec} {st : IRState} {fr : Frame} {cw gw : Word}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {rec : CallRecord} {cS' : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    -- ROUND-4 SIGNATURE ADDITIONS (the R3 Piece-B discovered set; see the reshaped
    -- `StmtTies'` arm (5) and `callRealises_of_recorded`): the flagship scalar
    -- `codeFits`, the reachable-frames CallsCode seam, the concrete operand bindings
    -- (fed by `RunDefinableG.stmts` at the walk), and the two static-fold gaps
    -- (call-operand stack room, result-slot addressability).
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS (rec :: cS') dS)
    (hch : CleanHaltsNonException fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hcc : ∀ fr', Runs fr fr' → CallsCode fr')
    (hcallee : st.locals cs.callee = some cw)
    (hgasfwd : st.locals cs.gasFwd = some gw)
    (hstkCallee : 5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024)
    (hstkGasFwd : 6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024)
    (hslotaddr : ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits)
    (hal : StreamsAligned self log gS (rec :: cS') dS T C D)
    (_hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.call cs) := by
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  -- operand closure-freeness at the cursor's fold set (`ScopedUses`).
  have hfreeCallee : RematClosureFree prog
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp cs.callee) :=
    hwl.scopedUses L b pc (.call cs) hb hcur cs.callee (by simp [readsStmt])
  have hfreeGasFwd : RematClosureFree prog
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp cs.gasFwd) :=
    hwl.scopedUses L b pc (.call cs) hb hcur cs.gasFwd (by simp [readsStmt])
  -- == the coupled CALL-head bundle (Piece A/B, coupling kept at the resume frame) ==
  obtain ⟨callFr, hargs, hcallpc, hcallmem, hcallact, hcallret, hcpres,
      hresaddr0, hrescode, hrescanmod, hrespc, hresstack, hresmem, hresactive, hresvalid⟩ :=
    call_head_realises_coupled hwl hcodeFits hb hcur hcorr hcp hch hcc hcallee hgasfwd
      hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
  have hresaddr : (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.address
      = self := by rw [hresaddr0, haddr]
  -- == the IR step: consume the aligned call-stream head (the realised image of `rec`) ==
  have hCcons : C = evmV2CallEntry rec.result rec.pending self :: callStreamOf cS' self := by
    rw [hal.2.1]; rfl
  have hentry : evmV2CallEntry rec.result rec.pending self
      = ((fun key => evmCallOracle.postStorage rec.result rec.pending self key),
          callSuccessFlag rec.result rec.pending) := rfl
  have hEval : EvalStmt prog st T C D (.call cs)
      (match cs.resultTmp with
        | some t' => { st with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key }.setLocal
                        t' (callSuccessFlag rec.result rec.pending)
        | none   => { st with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key })
      T (callStreamOf cS' self) D := by
    rw [hCcons, hentry]
    exact EvalStmt.call hcallee hgasfwd
  -- the scoped post-state carrier, from the start (R0b at `invalStep I (.call cs)`).
  have hsound' := defsSoundS_preserved_step hwl.defsCons hb hcur hEval hcorr.defsSound
  -- the post-state scoping fold.
  have hscoped' := call_post_wellScoped'
    (world' := fun key => evmCallOracle.postStorage rec.result rec.pending self key)
    (success := callSuccessFlag rec.result rec.pending)
    hb hcur hwl.defsCons hcorr.wellScoped
  -- clean halt at the resume frame (forwarded across the arg run + the CALL node).
  have hchres : CleanHaltsNonException (Evm.resumeAfterCall rec.result rec.pending) :=
    cleanHaltsNonException_forward hch (hargs.trans (sim_call hcallret (Runs.refl _)))
  -- == the byte layout at the cursor (`codeFits`-bounded decode anchors for the tail) ==
  set argsB := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hargsB
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = argsB ++ [Byte.call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none => [Byte.pop]) := rfl
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length →
      (flatBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.call cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.call cs) j hbt hcur hj
  -- the resume frame sits one byte past the CALL byte: `pcOf + (|argsB| + 1)`.
  have hpcR : (Evm.resumeAfterCall rec.result rec.pending).exec.pc
      = UInt32.ofNat (pcOf prog L pc + (argsB.length + 1)) := by
    have harith : pcOf prog L pc + (argsB.length + 1)
        = pcOf prog L pc + argsB.length + 1 := by omega
    rw [harith, hrespc, hcallpc, hcorr.pc_eq,
        show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add', ofNat_add']
  have hszR : (Evm.resumeAfterCall rec.result rec.pending).exec.stack.size + 1 ≤ 1024 := by
    rw [hresstack]; simp
  have hszR' : (Evm.resumeAfterCall rec.result rec.pending).exec.stack.size ≤ 1024 := by
    rw [hresstack]; simp
  -- == case on the result tmp: build the COUPLED Route-B tail, then re-establish `Corr` ==
  cases hr : cs.resultTmp with
  | some t =>
    -- byte layout: `argsB ++ [CALL] ++ (PUSH32 (slotOf t) ++ [MSTORE])`.
    have hemit' : emitStmt (matCache prog) (defsOf prog) (.call cs)
        = (argsB ++ [Byte.call]) ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) := by
      rw [hemit0, hr]
    have hseg' : ∀ j, j < ((argsB ++ [Byte.call])
          ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])).length →
        (flatBytes prog)[pcOf prog L pc + j]?
          = ((argsB ++ [Byte.call])
              ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]))[j]? := by
      intro j hj
      rw [← hemit']
      exact hseg j (by rw [hemit']; exact hj)
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.call cs)).length
        = argsB.length + 1 + 34 := by
      rw [hemit']
      simp only [List.length_append, List.length_singleton, emitImm_length]
    have hlast : pcOf prog L pc + (argsB.length + 34) < 2 ^ 32 :=
      stmt_offset_bound_of_codeFits hcodeFits hb hcur (by rw [hemitlen]; omega)
    have hsegTail : ∀ j, j < (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]).length →
        (flatBytes prog)[pcOf prog L pc + (argsB.length + 1) + j]?
          = (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])[j]? := by
      intro j hj
      have h := segF_suffix (flatBytes prog) (pcOf prog L pc) (argsB ++ [Byte.call])
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) hseg' j hj
      rwa [show pcOf prog L pc + (argsB ++ [Byte.call]).length
            = pcOf prog L pc + (argsB.length + 1) from by
          simp only [List.length_append, List.length_singleton]] at h
    -- the two tail decode anchors at the resume frame.
    have hdpushR : decode (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code
        (Evm.resumeAfterCall rec.result rec.pending).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) := by
      rw [hrescode, hpcR]
      exact imm_leaf_decodeF prog (pcOf prog L pc + (argsB.length + 1))
        (UInt256.ofNat (slotOf t)) (by omega)
        (segF_prefix (flatBytes prog) (pcOf prog L pc + (argsB.length + 1))
          (emitImm (UInt256.ofNat (slotOf t))) [Byte.mstore] hsegTail)
    have hdmstoreR : decode (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code
        ((Evm.resumeAfterCall rec.result rec.pending).exec.pc + UInt32.ofNat 33)
        = some (.Smsf .MSTORE, .none) := by
      rw [hrescode, hpcR, ofNat_add']
      have h := nonpush_leaf_decodeF prog (pcOf prog L pc + (argsB.length + 1)) 33
        Byte.mstore (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])
        (by omega)
        (by rw [List.getElem?_append_right (by rw [emitImm_length]), emitImm_length]; rfl)
        (by decide) hsegTail
      simpa using h
    -- == step 1 (COUPLED): PUSH32 (slotOf t) ==
    obtain ⟨hgasPushVL, hpushStep⟩ := Lir.CleanHaltExtract.next_push_of_cleanHalt
      (Evm.resumeAfterCall rec.result rec.pending) .PUSH32 (UInt256.ofNat (slotOf t)) 32
      hchres (by decide) hdpushR (by decide) (by decide) hszR
    have hgasPush3 : 3 ≤ (Evm.resumeAfterCall rec.result rec.pending).exec.gasAvailable.toNat := by
      have hvl : GasConstants.Gverylow = 3 := rfl
      omega
    have hcpPush : RecorderCoupled log
        (pushFrameW (Evm.resumeAfterCall rec.result rec.pending) (UInt256.ofNat (slotOf t)) 32)
        gS sS cS' dS := by
      apply recorderCoupled_step_other hcpres
      · unfold isGasOp; rw [hdpushR]; rfl
      · unfold isSloadOp; rw [hdpushR]; rfl
      · exact hpushStep
    have hchPush : CleanHaltsNonException
        (pushFrameW (Evm.resumeAfterCall rec.result rec.pending) (UInt256.ofNat (slotOf t)) 32) :=
      cleanHaltsNonException_forward hchres
        (runs_push (Evm.resumeAfterCall rec.result rec.pending) .PUSH32
          (UInt256.ofNat (slotOf t)) 32 (by nofun) hdpushR rfl rfl hgasPush3 hszR)
    -- == step 2 (COUPLED): MSTORE, writing the success flag at the result slot ==
    have hfrpstk : (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
          (UInt256.ofNat (slotOf t)) 32).exec.stack
        = UInt256.ofNat (slotOf t) :: callSuccessFlag rec.result rec.pending :: [] := by
      rw [pushFrameW_stack', hresstack]; rfl
    have hfrpsz : (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
          (UInt256.ofNat (slotOf t)) 32).exec.stack.size ≤ 1024 := by
      rw [hfrpstk]; simp
    have hdmstoreF : decode (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
          (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
        (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
          (UInt256.ofNat (slotOf t)) 32).exec.pc
        = some (.Smsf .MSTORE, .none) := by
      rw [show (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
            (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
          = (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code from rfl,
          pushFrameW_pc, push32_pcΔ]
      exact hdmstoreR
    obtain ⟨words', hmemW, hgasMemW, hgasVLW, hmstoreStep⟩ :=
      Lir.CleanHaltExtract.next_mstore_of_cleanHalt
        (pushFrameW (Evm.resumeAfterCall rec.result rec.pending) (UInt256.ofNat (slotOf t)) 32)
        (UInt256.ofNat (slotOf t)) (callSuccessFlag rec.result rec.pending) []
        hchPush hdmstoreF hfrpstk hfrpsz
    have hcpEnd : RecorderCoupled log
        (mstoreFrame (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
            (UInt256.ofNat (slotOf t)) 32)
          (UInt256.ofNat (slotOf t)) (callSuccessFlag rec.result rec.pending) words' [])
        gS sS cS' dS := by
      apply recorderCoupled_step_other hcpPush
      · unfold isGasOp; rw [hdmstoreF]; rfl
      · unfold isSloadOp; rw [hdmstoreF]; rfl
      · exact hmstoreStep
    -- the packaged tail bundle (`StashRuns`) at exactly the coupled endpoint.
    have hstash : Lir.StashRuns (Evm.resumeAfterCall rec.result rec.pending)
        (mstoreFrame (pushFrameW (Evm.resumeAfterCall rec.result rec.pending)
            (UInt256.ofNat (slotOf t)) 32)
          (UInt256.ofNat (slotOf t)) (callSuccessFlag rec.result rec.pending) words' [])
        (slotOf t) (callSuccessFlag rec.result rec.pending) 34 [] :=
      stash_tail_runs (Evm.resumeAfterCall rec.result rec.pending) (slotOf t)
        (callSuccessFlag rec.result rec.pending) [] words'
        hresstack hdpushR hdmstoreR hszR hgasPush3 hmemW hgasMemW hgasVLW
    -- == `Corr` re-established at the coupled endpoint (S3-call) ==
    obtain ⟨hruns, hcorr', hstk'⟩ := sim_call_stmt'
      (result := rec.result) (pd := rec.pending) (self := self)
      hbt hcur hcorr.pc_eq (by rw [hargsB]) hargs hcallpc hcallmem hcallact hcallret rfl rfl
      hresaddr hrescode hrescanmod hrespc hresstack hresmem hresactive hresvalid
      hsound' hcorr.memAgree (slots_slot_of_defsOf prog) hscoped'
      (fun t' ht' => by
        have heq : t = t' := by
          rw [hr] at ht'
          exact Option.some.inj ht'
        subst heq
        exact ⟨(hslotaddr t hr).1, (hslotaddr t hr).2, hstash⟩)
      (fun hn => by rw [hr] at hn; cases hn)
    rcases hal with ⟨hT, _, hD⟩
    exact ⟨_, _, T, callStreamOf cS' self, D, gS, sS, cS', dS,
      hEval, hruns, hcorr', hstk', hcpEnd, ⟨hT, rfl, hD⟩⟩
  | none =>
    -- byte layout: `argsB ++ [CALL] ++ [POP]`.
    have hemit' : emitStmt (matCache prog) (defsOf prog) (.call cs)
        = (argsB ++ [Byte.call]) ++ [Byte.pop] := by
      rw [hemit0, hr]
    have hseg' : ∀ j, j < ((argsB ++ [Byte.call]) ++ [Byte.pop]).length →
        (flatBytes prog)[pcOf prog L pc + j]?
          = ((argsB ++ [Byte.call]) ++ [Byte.pop])[j]? := by
      intro j hj
      rw [← hemit']
      exact hseg j (by rw [hemit']; exact hj)
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.call cs)).length
        = argsB.length + 1 + 1 := by
      rw [hemit']
      simp only [List.length_append, List.length_singleton]
    -- the POP decode anchor at the resume frame.
    have hpopbyte : ((argsB ++ [Byte.call]) ++ [Byte.pop])[argsB.length + 1]?
        = some Byte.pop := by
      rw [List.getElem?_append_right (by
            simp only [List.length_append, List.length_singleton]; omega)]
      simp
    have hdpopR : decode (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code
        (Evm.resumeAfterCall rec.result rec.pending).exec.pc
        = some (.Smsf .POP, .none) := by
      rw [hrescode, hpcR]
      have h := nonpush_leaf_decodeF prog (pcOf prog L pc) (argsB.length + 1) Byte.pop
        ((argsB ++ [Byte.call]) ++ [Byte.pop])
        (stmt_offset_bound_of_codeFits hcodeFits hb hcur (by rw [hemitlen]; omega))
        hpopbyte (by decide) hseg'
      simpa using h
    -- == the one COUPLED POP step ==
    obtain ⟨hgasPop, hpopStep⟩ := Lir.CleanHaltExtract.next_pop_of_cleanHalt
      (Evm.resumeAfterCall rec.result rec.pending)
      (callSuccessFlag rec.result rec.pending) [] hchres hdpopR hresstack hszR'
    have hpoprun : Runs (Evm.resumeAfterCall rec.result rec.pending)
        (popFrame (Evm.resumeAfterCall rec.result rec.pending) []) :=
      runs_pop (Evm.resumeAfterCall rec.result rec.pending)
        (callSuccessFlag rec.result rec.pending) [] hdpopR hresstack hszR' hgasPop
    have hcpEnd : RecorderCoupled log
        (popFrame (Evm.resumeAfterCall rec.result rec.pending) []) gS sS cS' dS := by
      apply recorderCoupled_step_other hcpres
      · unfold isGasOp; rw [hdpopR]; rfl
      · unfold isSloadOp; rw [hdpopR]; rfl
      · exact hpopStep
    -- == `Corr` re-established at the coupled endpoint (S3-call) ==
    obtain ⟨hruns, hcorr', hstk'⟩ := sim_call_stmt'
      (result := rec.result) (pd := rec.pending) (self := self)
      hbt hcur hcorr.pc_eq (by rw [hargsB]) hargs hcallpc hcallmem hcallact hcallret rfl rfl
      hresaddr hrescode hrescanmod hrespc hresstack hresmem hresactive hresvalid
      hsound' hcorr.memAgree (slots_slot_of_defsOf prog) hscoped'
      (fun t' ht' => by rw [hr] at ht'; cases ht')
      (fun _ => ⟨hpoprun, rfl⟩)
    rcases hal with ⟨hT, _, hD⟩
    exact ⟨_, _, T, callStreamOf cS' self, D, gS, sS, cS', dS,
      hEval, hruns, hcorr', hstk', hcpEnd, ⟨hT, rfl, hD⟩⟩

/-- **P2-create — the external-CREATE coupled step** (STATEMENT ONLY — tracked `sorry`).
The CREATE twin of `simStmt_coupled_call`. Statement mirrors the CALL arm field-for-field:
the four operand bindings (value/off/size/salt), the `CreateResolves` reachable-frames seam (the
create analogue of the `CallsCode` seam), the four operand stack-room folds, and the result-slot
addressability; the coupling's `createSuffix` head `rec` is consumed (`EvalStmt.create` on the
aligned `createStreamOf` head), gas/sload/call suffixes ride unchanged.

STATUS: STATEMENT WIRED for the downstream block walk; PROOF DEFERRED (this producer round declares
only the shape). It consumes `create_head_realises_coupled` (Machinery, currently a tracked stub
itself, blocked on the default-layer CREATE dispatch producer + resume pins) + a `sim_create_stmt'`
S3 carrier (the CREATE twin of `sim_call_stmt'`) that must be built for the coupled Route-B tail
re-establishment. NEXT AGENT: once those land, this proof is a line-for-line transcription of
`simStmt_coupled_call`. -/
theorem simStmt_coupled_create {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {cs : CreateSpec} {st : IRState} {fr : Frame}
    {valueW initOffW initSizeW saltW : Word}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord} {rec : CreateRecord} {dS' : List CreateRecord}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS (rec :: dS'))
    (hch : CleanHaltsNonException fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hcr : ∀ fr', Runs fr fr' → CreateResolves fr')
    (hvalue : st.locals cs.value = some valueW)
    (hoff : st.locals cs.initOffset = some initOffW)
    (hsize : st.locals cs.initSize = some initSizeW)
    (hsalt : st.locals cs.salt = some saltW)
    (hstkSalt : 0 + (chargeCache prog sloadChg cs.salt).length ≤ 1024)
    (hstkSize : 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024)
    (hstkOff : 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024)
    (hstkValue : 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024)
    (hslotaddr : ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits)
    (hal : StreamsAligned self log gS cS (rec :: dS') T C D)
    (_hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.create cs) := by
  -- DIAGNOSTIC (tracked debt): STATEMENT ONLY. Line-for-line transcription of
  -- `simStmt_coupled_call` once `create_head_realises_coupled` + `sim_create_stmt'` land.
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
    (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord) (dS' : List CreateRecord),
    RunStmts prog st T C D b.stmts st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 (fun _ => False) st' fr' L b.stmts.length
    ∧ fr'.exec.stack = []
    ∧ CleanHaltsNonException fr'
    ∧ RecorderCoupled log fr' gS' sS' cS' dS'
    ∧ StreamsAligned self log gS' cS' dS' T' C' D'
    ∧ SelfPresent fr'
    ∧ fr'.exec.executionEnv.address = self
    ∧ (∃ cp, fr'.kind = .call cp)

/-- **Address preserved along a whole `Runs`.** The self address is `rfl`-preserved by every
edge of a `Runs` path: an opcode `.step` only advances `exec` off the same `executionEnv`
(`stepFrame_next_execEnvAddr`); a returning `.call` rebuilds the caller frame whose `executionEnv`
is the CALL-site frame's (`stepFrame_needsCall_inv` + `resumeAfterCall_address`); a returning
`.create` likewise (`stepFrame_needsCreate_inv` + `resumeAfterCreate_execEnv`). The address twin of
`runs_kind`; the brick the block walk uses to transport `DriveCorrLog.addrPin` across each coupled
statement step's `Runs fr fr'` (including the CALL/CREATE resume edges). REAL; no sorry. -/
theorem runs_address_preserved {fr fr' : Frame} (h : Runs fr fr') :
    fr'.exec.executionEnv.address = fr.exec.executionEnv.address := by
  induction h with
  | refl _ => rfl
  | step hs _ ih =>
      rw [ih]
      have := stepFrame_next_execEnvAddr hs.1
      rw [hs.2]; rw [this]
  | call hc _ ih =>
      obtain ⟨cp, pending, child, childRes, hstep, _, _, hresume⟩ := hc
      rw [ih, hresume, resumeAfterCall_address]
      exact congrArg (·.address) (Evm.stepFrame_needsCall_inv hstep).2.2
  | create hc _ ih =>
      obtain ⟨cp, pending, childRes, hstep, _, hresume⟩ := hc
      rw [ih, resumeAfterCreate_execEnv childRes pending _ hresume]
      exact congrArg (·.address) (Evm.stepFrame_needsCreate_inv hstep).2.2.2

/-- **Append a single `EvalStmt` at the tail of a prefix `RunStmts`.** The `RunStmts` inductive
`cons`es at the front; the block walk grows its prefix run one statement at a time at the tail, so
it needs the snoc form. Structural induction on the prefix run. REAL; no sorry. -/
theorem runStmts_snoc {prog : Program} {st st' st'' : IRState} {T T' T'' : Trace}
    {C C' C'' : CallStream} {D D' D'' : CreateStream} {ss : List Stmt} {s : Stmt}
    (hpre : RunStmts prog st T C D ss st' T' C' D')
    (hstep : EvalStmt prog st' T' C' D' s st'' T'' C'' D'') :
    RunStmts prog st T C D (ss ++ [s]) st'' T'' C'' D'' := by
  induction hpre with
  | nil => exact RunStmts.cons hstep RunStmts.nil
  | cons hh _ ih => exact RunStmts.cons hh (ih hstep)

/-- **P3a — the COUPLED block walk** (the analogue of `sim_stmts_block`, but coupled; reason
(a) in one lemma). By induction over the block statement suffix, fold the `simStmt_coupled_*`
family: at each cursor dispatch on the statement shape, fire the matching arm (feeding it the
current coupling + alignment + `StmtTies'`), then recurse on the tail at the advanced coupling.
The self/addr/kind pins ride along via `selfPresent_runs_of_call` / `runs_kind` /
`runs_address_preserved`. Consumes: `stmtTies'_of_runWithLog` (R10a) for the arm facts;
`RunDefinableG` (`hwl.defs`) for operand definability at each cursor; `hwl.stack`/`hwl.slotAddr`
for the call/create static stack-room + slot-addressability folds; `hwl.revalidates` to coerce the
terminal accumulated invalidation fold back to `DefsSound` (`RevalidatesPerBlock`).
TRACTABILITY: hard (assembles §2). -/
theorem simStmts_coupled_block {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    -- RESHAPE (approved): the flagship scalar `codeFits` + the reachable-frames CallsCode /
    -- CreateResolves seams, threaded so the `.call` / `.create` arms of the walk are
    -- dischargeable. Both are supplied at `boundaryWalk_of_wl` (from `hcodeFits` / `hseams`),
    -- transported across each statement step by `Runs.trans`.
    (hcodeFits : codeFits prog)
    (hcc : ∀ fr', Runs fr fr' → CallsCode fr')
    (hcr : ∀ fr', Runs fr fr' → CreateResolves fr')
    (hb : blockAt prog L = some b)
    (hcorr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L 0)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hkind : ∃ cp, fr.kind = .call cp)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hstmts : StmtTies' prog sloadChg log self L b)
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    CoupledBlockRun prog sloadChg log self L b st fr T C D := by
  -- PARTIAL / BLOCKED (precise obstruction reported). The pure-statement walk
  -- (assign/gas/sload/sstore) fully discharges: the drop-induction with a prefix-`RunStmts`
  -- accumulator (`runStmts_snoc`), operand bindings from `hwl.defs` (`StmtDefinableG`), the
  -- static stack-room/slot-addr folds from `hwl.stack`/`hwl.slotAddr`, the pin transport
  -- (`cleanHaltsNonException_forward` / `selfPresent_runs_of_call` / `runs_address_preserved` /
  -- `runs_kind`), the seam transport by `Runs.trans`, and the terminal fold→`DefsSound` coercion
  -- via `hwl.revalidates` (`RevalidatesPerBlock`) — ALL verified green.
  --
  -- The `.call` / `.create` arms are BLOCKED on a missing Machinery-level lemma: firing
  -- `simStmt_coupled_call` / `_create` requires the coupling's call/create SUFFIX to be already
  -- split (`RecorderCoupled log frc gS sS (rec :: cS') dS`), but the block walk holds only a
  -- GENERAL suffix `cSc`, and its non-emptiness at a `.call` cursor is NOT derivable from the
  -- pieces available here (via `StreamsAligned`, firing the IR `EvalStmt.call` itself needs a
  -- non-empty `Cc = callStreamOf cSc self`). This is the exact analogue of the gas/sload arms,
  -- which take a GENERAL suffix and split it INTERNALLY via `gasSuffix_nonempty` /
  -- `sloadSuffix_nonempty` (Machinery) at the reached GAS/SLOAD op. The call/create twins
  -- `callSuffix_nonempty` / `createSuffix_nonempty` (keyed on the reached CALL/CREATE-byte frame
  -- firing `.needsCall` / `.needsCreate`) do NOT exist, and `simStmt_coupled_call` /
  -- `call_head_realises_coupled` / `call_dispatch_of_coupled` are keyed on `rec :: cS'` upfront.
  -- Resolving this needs either those Machinery lemmas or a reshape of the CALL/CREATE arms to
  -- take a general suffix and split internally — both in the Machinery layer (concurrent owner).
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
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    -- RESHAPE (approved): `codeFits` + the reachable-frames CallsCode / CreateResolves seams,
    -- passed straight into the block walk (P3a). Supplied at `boundaryWalk_of_wl`.
    (hcodeFits : codeFits prog)
    (hcc : ∀ fr', Runs fr fr' → CallsCode fr')
    (hcr : ∀ fr', Runs fr fr' → CreateResolves fr')
    (hclosed : ClosedCFG prog)
    (hdrive : DriveCorrLog prog sloadChg log self st fr L gS sS cS dS)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hstmts : StmtTies' prog sloadChg log self L
      (Classical.choose (DriveCorrLog.present hdrive)))
    (hterm : TermTies' prog sloadChg log self L
      (Classical.choose (DriveCorrLog.present hdrive)))
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    DriveLogStep prog sloadChg log self st fr L T C D gS sS cS dS := by
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
    -- RESHAPE (approved): `hstep` (= `driveLogStep_of_block`) now takes the `codeFits` scalar and
    -- the per-frame reachable-frames CallsCode / CreateResolves seams; the recursion threads them
    -- to the strictly-smaller successor by `Runs.trans` across the edge `Runs fr fr'`.
    (hcodeFits : codeFits prog)
    (hstep : ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream)
        (D : CreateStream) (gS : List Word) (sS : List Nat) (cS : List CallRecord)
        (dS : List CreateRecord),
      (∀ fr', Runs fr fr' → CallsCode fr') →
      (∀ fr', Runs fr fr' → CreateResolves fr') →
      DriveCorrLog prog sloadChg log self st fr L gS sS cS dS →
      StreamsAligned self log gS cS dS T C D →
      DriveLogStep prog sloadChg log self st fr L T C D gS sS cS dS) :
    ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord) (dS : List CreateRecord),
      (∀ fr', Runs fr fr' → CallsCode fr') →
      (∀ fr', Runs fr fr' → CreateResolves fr') →
      DriveCorrLog prog sloadChg log self st fr L gS sS cS dS →
      StreamsAligned self log gS cS dS T C D →
      RunFromCoupled prog self st fr L T C D := by
  -- strong induction on the bytecode `totalGas` measure of the boundary frame, generalising over
  -- all the boundary data so the IH applies at the strictly-smaller successor.
  intro st fr L T C D gS sS cS dS hcc hcr hdrive hal
  induction hmeasure : totalGas [] (.inl fr) using Nat.strong_induction_on
    generalizing st fr L T C D gS sS cS dS with
  | _ n ih =>
    subst hmeasure
    rcases hstep st fr L T C D gS sS cS dS hcc hcr hdrive hal with
      hrun | ⟨st', T', C', D', succ, fr', gS', sS', cS', dS', hruns, hdrive', hal', hlt, hcont⟩
    · -- halt disjunct: the block bottoms out; `RunFromCoupled` is delivered directly.
      exact hrun
    · -- edge disjunct: recurse at the strictly-smaller successor, then prepend the block.
      -- the seams transport across the edge `Runs fr fr'`: anything reachable from `fr'` is
      -- reachable from `fr`, so `hcc`/`hcr` at `fr` re-supply the successor's seams.
      have hcc' : ∀ fr'', Runs fr' fr'' → CallsCode fr'' := fun fr'' hr => hcc fr'' (hruns.trans hr)
      have hcr' : ∀ fr'', Runs fr' fr'' → CreateResolves fr'' := fun fr'' hr => hcr fr'' (hruns.trans hr)
      obtain ⟨O, ⟨last, haltSig, hlast, hhalt, hworld, hresult⟩, hir⟩ :=
        ih (totalGas [] (.inl fr')) hlt st' fr' succ T' C' D' gS' sS' cS' dS' hcc' hcr' hdrive' hal' rfl
      -- the successor's bytecode halt terminal lifts back to `fr` across the edge `Runs fr fr'`.
      exact ⟨O, ⟨last, haltSig, hruns.trans hlast, hhalt, hworld, hresult⟩, hcont O hir⟩

/-- **P5 — the R6 boundary walk (`hrb`), reason (b).** Every `Runs fr₀`-reachable frame sits at
a reachable instruction boundary. This helper derives the nonempty-program precondition from
`hwl.closed.entry_present` / `hwl.entry0`; the byte-size seam remains explicit because
`WellLowered` is only an internal adapter and does not carry whole-program byte length. -/
theorem boundaryWalk_of_wl {prog : Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hwl : WellLowered prog)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr' := by
  have hne : 0 < prog.blocks.size := by
    obtain ⟨bentry, hbentry⟩ := hwl.closed.entry_present
    unfold blockAt at hbentry
    rw [hwl.entry0] at hbentry
    by_contra hz
    have hs : prog.blocks.size = 0 := Nat.eq_zero_of_not_pos hz
    rw [Array.getElem?_eq_none (by rw [hs])] at hbentry
    cases hbentry
  exact runs_atReachableBoundary hbegin hcode hne hsize

/-- **P6 — create-resolves for all reachable frames (`hcr`).** The blocker existential's first
conjunct. Threaded from the reachable-frame create-resolves field in `PrecompileAssumptions`
(the honest R4 residual — `CreateResolves` is NOT structural, `V2/Modellable.lean:413`).
TRACTABILITY: direct seam adapter. -/
theorem createResolves_reachable {prog : Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hseams : PrecompileAssumptions prog params) :
    ∀ fr', Runs fr₀ fr' → CreateResolves fr' :=
  -- Every `Runs fr₀`-reachable frame is `ReachableFrom params` (`⟨fr₀, hbegin, hr⟩`), so the
  -- seam applies directly.
  fun fr' hr => hseams.createResolves fr' ⟨fr₀, hbegin, hr⟩

/-- **R11 — `runFrom_of_driveCorrLog`, THE COUPLED RUN-PRODUCER.** The packaged existential the
flagship `lower_conforms` (`RealisabilitySpec.lean:240-247`) and its siblings `obtain`. Assembles:
the entry coupled boundary (P1a/P1b), the coupled drive recursion (P4) discharged per-boundary by
`driveLogStep_of_block` (P3b) fed the reshaped ties from R10a/R10b, and the create-resolves
conjunct (P6). The whole-code size bound remains an internal producer input and is derived from
the public `codeFits` premise at flagship call sites; create-resolves comes from the seam bundle.

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
    -- RESHAPE (approved): the strict `codeFits` scalar (the `simStmt_coupled_call/create` arms
    -- consume the strict `< 2^32`, not the `≤` face carried by `hsize`). Supplied at the flagship
    -- call site (it holds `hcodeFits : codeFits prog` in scope).
    (hcodeFits : codeFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params)
    (hbegin : beginCall params = .inl fr₀)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∃ O : Observable,
      (∀ fr', Runs fr₀ fr' → CreateResolves fr')
      ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
          ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
          ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
      ∧ RunFrom prog (entryState params) (realisedGas log)
          (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O := by
  sorry

end Lir.V2
