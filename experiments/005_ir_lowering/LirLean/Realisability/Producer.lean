import LirLean.Realisability.Machinery
import LirLean.Drive.DriveSim

open Lir.Frame
open BytecodeLayer.Exec

/-!
# LirLean — the coupled run-producer `runFrom_of_driveCorrLog`

This module proves the coupled run-producer
`runFrom_of_driveCorrLog`. It is the packaged existential the flagship `lower_conforms` (R11) and its
`lower_conforms_exact`/`lower_conforms_gasfree` siblings `obtain`, and — with the CREATE
channel wired (`docs/create/STATUS.md`) — it closes CALL and CREATE simultaneously.

## Why this is NOT assembly over citable leaves (the two documented reasons)

* **(a) unconditional `SimStmtStep` is unsatisfiable under the reshape.** The only in-tree
  run-producer `lower_conforms_cyclic'` (`Drive/DriveSim.lean`) consumes an ALL-FRAMES
  `SimStmtStep` (`Sim/SimStmts.lean:66`) — a per-statement simulation with NO coupling
  antecedent. The reshaped `StmtTies'` (`Surface.lean:640`) can only conclude its arms UNDER
  the load-bearing `RecorderCoupled` antecedent (target-architecture §3); the coupling-free
  path is exactly the vacuity the reshape exists to kill (header lessons 1–3, `RealisabilitySpec`).
  So the producer cannot factor through `SimStmtStep`/`DriveStep`/`runFrom_of_driveCorr`; it must
  run its OWN walk carrying `DriveCorrLog` (which BUNDLES `RecorderCoupled`) and fire the Layer-C
  sim bricks ONLY at the coupled walk-frames — the `simStmt_coupled_*` family below.
* **(b) R6 `runs_atReachableBoundary` cannot supply `hrb` alone.** Its B2 side condition
  `(lowerBytes prog).length ≤ 2 ^ 32` (`Machinery.lean:1509`) is not a field of the internal
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
in the NON-DEFAULT `WIP` lean_lib so the default `LirLean` cone does not pay to rebuild it.
-/

namespace Lir

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
un-consumed recorder suffixes `(gS, cS, dS)`. SLOAD consumes no recorder stream. -/

/-- The IR streams `(T, C, D)` at a coupled boundary are the realised image of the recorder
suffixes: the gas trace IS the gas suffix, the call stream IS the `evmCallEntry` image of
the call suffix, and the create stream IS the `evmCreateEntry` image of the create
suffix. REAL def. -/
def StreamsAligned (self : AccountAddress) (log : RunLog)
    (gS : List Word) (cS : List CallRecord) (dS : List CreateRecord)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  T = gS ∧ C = callStreamOf cS self ∧ D = createStreamOf dS self

/-- The producer's per-boundary OUTPUT: some IR observable `O` whose world AND result equal
the `observe` of the bytecode frame's halting terminal (reachable from `fr`), together with
the IR `RunFrom` from `(st, T, C, D)` at `L` to `O`. This is the packaged shape the flagship's
`obtain` consumes (its `hworld`+`hrunfrom` conjuncts, at the entry boundary). -/
def RunFromCoupled (prog : Program) (self : AccountAddress)
    (st : IRState) (fr : Frame) (L : Label)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  ∃ O : Observable,
    (∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world
        ∧ (observe self (endFrame last haltSig)).result = O.result)
    ∧ RunFrom prog st T C D L O
    ∧ RunFromAll prog st T C D L O

/-- The COUPLED per-block obligation (the `DriveLogStep` analogue of `DriveSim`'s `DriveStep`,
but carrying the coupling + alignment). From a coupled boundary either the block HALTS
(`RunFromCoupled`) or it takes an EDGE to a strictly-smaller-`totalGas` successor whose
`DriveCorrLog` + `StreamsAligned` are re-established, with the bytecode forward run `Runs fr fr'`
and the IR one-block continuation. REAL def. -/
def DriveLogStep (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream)
    (gS : List Word) (cS : List CallRecord) (dS : List CreateRecord) : Prop :=
  RunFromCoupled prog self st fr L T C D
  ∨
  (∃ (st' : IRState) (T' : Trace) (C' : CallStream) (D' : CreateStream)
      (succ : Label) (fr' : Frame) (gS' : List Word) (cS' : List CallRecord)
      (dS' : List CreateRecord),
      Runs fr fr'
    ∧ DriveCorrLog prog sloadChg log self st' fr' succ gS' cS' dS'
    ∧ StreamsAligned self log gS' cS' dS' T' C' D'
    ∧ totalGas [] (.inl fr') < totalGas [] (.inl fr)
    ∧ (∀ O, RunFrom prog st' T' C' D' succ O → RunFrom prog st T C D L O)
    ∧ (∀ O, RunFromAll prog st' T' C' D' succ O → RunFromAll prog st T C D L O))

/-- The result of ONE coupled statement step at cursor `(L, pc)`: the IR `EvalStmt` of `s`
(consuming the aligned stream heads), the matching bytecode `Runs fr fr'` re-establishing
`Corr` at `pc+1` with empty stack, and the advanced coupling `RecorderCoupled` + `StreamsAligned`
at the tail. REAL def. -/
def CoupledAdvance (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (I : Tmp → Prop) (L : Label) (pc : Nat) (st : IRState) (fr : Frame)
    (T : Trace) (C : CallStream) (D : CreateStream) (s : Stmt) : Prop :=
  ∃ (st' : IRState) (fr' : Frame) (T' : Trace) (C' : CallStream) (D' : CreateStream)
    (gS' : List Word) (cS' : List CallRecord) (dS' : List CreateRecord),
    EvalStmt prog st T C D s st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 (invalStep prog I s) st' fr' L (pc + 1)
    ∧ fr'.exec.stack = []
    ∧ RecorderCoupled log fr' gS' cS' dS'
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
          log.gas log.calls log.creates := by
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
      RecorderCoupled log (codeFrame params (lower prog)) log.gas log.calls log.creates :=
    recorderCoupled_entry hrun hbegin
  have hstepsTo : StepsTo (codeFrame params (lower prog))
      (jumpdestFrame (codeFrame params (lower prog))) :=
    stepsTo_of_next (stepFrame_jumpdest (codeFrame params (lower prog)) hdec hsz hgasF)
  have hnotgas : isGasOp (codeFrame params (lower prog)) = false := by
    unfold isGasOp; rw [hdec]; rfl
  have hnotcreate2 : isCreate2Op (codeFrame params (lower prog)) = false := by
    unfold isCreate2Op; rw [hdec]; rfl
  have hnotcall : isCallOp (codeFrame params (lower prog)) = false := by
    unfold isCallOp; rw [hdec]; rfl
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
      coupled := recorderCoupled_stepsTo_other hcp₀ hnotgas hnotcreate2 hnotcall hstepsTo }

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
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t e))
    (hne : e ≠ .gas) (hns : ∀ k, e ≠ .sload k)
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hv : evalExpr st 0 e = some w)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.assign t e) := by
  -- Fire `StmtTies'` arm (1) at this cursor with the coupling + clean-halt in hand.
  obtain ⟨hslot, hstepS, hscoped', hmem'⟩ :=
    hties.1 pc t e w st fr gS cS dS
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
  refine ⟨st.setLocal t w, fr, T, C, D, gS, cS, dS,
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
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t .gas))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) L pc st fr T C D (.assign t .gas) := by
  classical
  let I := (b.stmts.take pc).foldl (invalStep prog) (fun _ => False)
  obtain ⟨hslotdef, hstepS, hslots, hghead, hscoped', hslot63, hslotplat, hpcbound⟩ :=
    hties.2.2.1 pc t st fr gS cS dS I hcur hcorr hcp hch
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
    have hcpGas : RecorderCoupled log (gasFrame fr) gS' cS dS := by
      simpa [gasFrame] using (recorderCoupled_step_gas (by simpa [hg] using hcp) hisGas hgasStep).1
    let frp := pushFrameW (gasFrame fr) (UInt256.ofNat (slotOf t)) 32
    have hpushStep : stepFrame (gasFrame fr) = .next frp.exec :=
      stepFrame_push (gasFrame fr) .PUSH32 (UInt256.ofNat (slotOf t)) 32 (by decide)
        hdpush (by decide) (by decide) hgasPush (by rw [gasFrame_stack, hcorr.stack_nil]; simp)
    have hcpPush : RecorderCoupled log frp gS' cS dS := by
      apply recorderCoupled_step_other hcpGas
      · unfold isGasOp; rw [hdpush]; rfl
      · unfold isCreate2Op; rw [hdpush]; rfl
      · unfold isCallOp; rw [hdpush]; rfl
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
    have hcpEnd : RecorderCoupled log endFr gS' cS dS := by
      have hcpm := recorderCoupled_step_other hcpPush
        (by
          unfold isGasOp
          have hd : decode frp.exec.executionEnv.code frp.exec.pc =
              some (.Smsf .MSTORE, .none) := by
            simpa [frp, gasFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
          rw [hd]; rfl)
        (by
          unfold isCreate2Op
          have hd : decode frp.exec.executionEnv.code frp.exec.pc =
              some (.Smsf .MSTORE, .none) := by
            simpa [frp, gasFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
          rw [hd]; rfl)
        (by
          unfold isCallOp
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
    exact ⟨st.setLocal t hgasVal, endFr, gS', C, D, gS', cS, dS,
      hEval, hrun, hcorr', hstack, hcpEnd, ⟨rfl, hC, hD⟩⟩

-- S1 (`recorderCoupled_matRunsC`, the coupling fold over a `materialise` run) is RELOCATED
-- to `Machinery.lean` (pure relocation): the R3 arg-push producer `call_args_run_of_coupled`
-- there consumes it, and `Machinery` cannot import this module.

theorem simStmt_coupled_sload {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {t k : Tmp} {kv : Word} {st : IRState} {fr : Frame}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t (.sload k)))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS cS dS)
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
    hties.2.1 pc t k kv st fr gS cS dS I hcur hcorr hcp hch hkey
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
      (lowerBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.assign t (.sload k)))[j]? := by
    intro j hj
    exact lowerBytes_at_pcOf_offset prog L b pc (.assign t (.sload k)) j hbt hcur
      (by rw [hemitlen]; omega)
  have hsegk : ∀ j, j < (matExpr (matCache prog) (.tmp k)).length →
      (lowerBytes prog)[pcOf prog L pc + j]? = (matExpr (matCache prog) (.tmp k))[j]? := by
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
    sloadChg st 0 log gS cS dS I (.tmp k) kv fr hdk hcorr.defsSound hfree
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
  have hcpSload : RecorderCoupled log (sloadFrame frk kv []) gS cS dS := by
    exact recorderCoupled_step_other hcpk
      (by unfold isGasOp; rw [hdsload]; rfl)
      (by unfold isCreate2Op; rw [hdsload]; rfl)
      (by unfold isCallOp; rw [hdsload]; rfl)
      hsloadStep
  let frp := pushFrameW (sloadFrame frk kv []) (UInt256.ofNat (slotOf t)) 32
  have hpushStep : stepFrame (sloadFrame frk kv []) = .next frp.exec :=
    stepFrame_push (sloadFrame frk kv []) .PUSH32 (UInt256.ofNat (slotOf t)) 32 (by decide)
      hdpush (by decide) (by decide) hgasPush
      (by simp [sloadFrame_stack])
  have hcpPush : RecorderCoupled log frp gS cS dS := by
    apply recorderCoupled_step_other hcpSload
    · unfold isGasOp; rw [hdpush]; rfl
    · unfold isCreate2Op; rw [hdpush]; rfl
    · unfold isCallOp; rw [hdpush]; rfl
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
  have hcpEnd : RecorderCoupled log endFr gS cS dS := by
    have hcpm := recorderCoupled_step_other hcpPush
      (by
        unfold isGasOp
        have hd : decode frp.exec.executionEnv.code frp.exec.pc =
            some (.Smsf .MSTORE, .none) := by
          simpa [frp, sloadFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
        rw [hd]; rfl)
      (by
        unfold isCreate2Op
        have hd : decode frp.exec.executionEnv.code frp.exec.pc =
            some (.Smsf .MSTORE, .none) := by
          simpa [frp, sloadFrame_pc, pushFrameW_pc, push32_pcΔ] using hdmstore
        rw [hd]; rfl)
      (by
        unfold isCallOp
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
  exact ⟨st.setLocal t w, endFr, T, C, D, gS, cS, dS,
    hEval, hrun, hcorr', hstack, hcpEnd, hal⟩
/-- **S3 — `sim_sstore_stmt'`, the WIP re-plumb of `sim_sstore_stmt`.** Same conclusion as the
in-tree `sim_sstore_stmt` (`Sim/SimStmt.lean`), but (i) DROPS the unsatisfiable `∀`-quantified
`hsstore : SstoreRealises fr kw vw acc` — its three runtime facts are derived POINT-WISE at the
internal SSTORE frame `frk` from the threaded `SelfPresent fr` + clean-halt via
`sstoreRealises_at_frame` (R4); and (ii) THREADS the recorder coupling
`RecorderCoupled log fr gS cS` across the two `materialise` runs (S1 `recorderCoupled_matRunsC`,
value then key) and the SSTORE frame itself (S2, one `recorderCoupled_step_other`, R7d — SSTORE is
neither GAS nor SLOAD), returning it at the post-frame. The `Corr` re-establishment body is verbatim
`sim_sstore_stmt`. REAL; no sorry. -/
theorem sim_sstore_stmt' {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {log : RunLog}
    {st : IRState} {key value : Tmp} {kw vw : Word}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
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
    (hcp : RecorderCoupled log fr gS cS dS)
    (hstk : (chargeCache prog sloadChg value).length
              + (chargeCache prog sloadChg key).length + 1 ≤ 1024) :
    ∃ fr', Runs fr fr'
      ∧ Lir.Corr prog sloadChg obs I (st.setStorage kw vw) fr' L (pc + 1)
      ∧ fr'.exec.stack = []
      ∧ RecorderCoupled log fr' gS cS dS := by
  classical
  set lv := (matCache prog value).length with hlv
  set lk := (matCache prog key).length with hlk
  have hstacknil := hcorr.stack_nil
  -- == B1 call 1: materialise `value` from `fr`, leaving `[vw]`, carrying the coupling.
  -- The value-channel gas bound is DERIVED from the clean-halt witness. ==
  have hevv : Lir.evalExpr st obs (.tmp value) = some vw := hv
  have hszfr : fr.exec.stack.size = 0 := by rw [hstacknil]; rfl
  have hstkv : fr.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp value)).length ≤ 1024 := by
    simp only [chargeExpr_tmp]; omega
  have hgasv : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp value)).sum
      ≤ fr.exec.gasAvailable.toNat :=
    materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs I (.tmp value) vw fr
      hdv hcorr.defsSound hfreeValue hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
      hevv hcs hstkv
  obtain ⟨frv, hmrv, hcpv⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs log gS cS dS
    I (.tmp value) vw fr
    hdv hcorr.defsSound hfreeValue hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
    hevv hgasv hstkv hcp
  have hvcode : frv.exec.executionEnv.code = fr.exec.executionEnv.code := hmrv.code
  have hvaddr : frv.exec.executionEnv.address = fr.exec.executionEnv.address := hmrv.addr
  have hvpc : frv.exec.pc = fr.exec.pc + UInt32.ofNat lv := hmrv.pc
  have hvstk : frv.exec.stack = vw :: fr.exec.stack := by rw [hmrv.stack]; rfl
  -- == B1 call 2: materialise `key` from `frv`, leaving `[kw, vw]`, carrying the coupling ==
  have hevk : Lir.evalExpr st obs (.tmp key) = some kw := hk
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
  obtain ⟨frk, hmrk, hcpk⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs log gS cS dS
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
  have hcpf : RecorderCoupled log (sstoreFrame frk kw vw []) gS cS dS :=
    recorderCoupled_step_other hcpk
      (by unfold isGasOp; rw [hkdec]; rfl)
      (by unfold isCreate2Op; rw [hkdec]; rfl)
      (by unfold isCallOp; rw [hkdec]; rfl)
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
      exact hcorr.wellScoped tw (by simpa [Lir.IRState.setStorage] using htw)
    · intro tw slot v hdef hloc
      have hloc' : st.locals tw = some v := by simpa [Lir.IRState.setStorage] using hloc
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
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS cS dS)
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
    hties.2.2.2.1 pc key value kw vw st fr gS cS dS
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
  -- gS/cS ride unchanged), so the alignment `hal` carries over verbatim.
  exact ⟨st.setStorage kw vw, fr', T, C, D, gS, cS, dS,
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
  have hflat : (lowerBytes prog)[pcOf prog L pc + k]?
      = some ((emitStmt (matCache prog) (defsOf prog) s)[k]) := by
    rw [lowerBytes_at_pcOf_offset prog L b pc s k (Lir.toList_of_blockAt hb) hcur hk]
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

/-- World replacement preserves the create arm's static well-scoping; a bound result tmp uses
the slot registration supplied by `DefsConsistent`. -/
private theorem create_post_wellScoped' {prog : Program} {L : Label} {b : Block} {pc : Nat}
    {cs : CreateSpec} {st : IRState} {world' : World} {addrW : Word}
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hdefsCons : DefsConsistent prog)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none) :
    ∀ t, (match cs.resultTmp with
            | some t' => { st with world := world' }.setLocal t' addrW
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
          (hdefsCons L b pc hb).2.2 cs t hcur hres
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
    (hcall : Runs callFr resumeFr)
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
    (hM3 : ∀ key, selfStorage resumeFr key = evmCallOracle.postStorage result pd self key)
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
  have hruns0 : Runs fr resumeFr := hargs.trans hcall
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
      rw [BytecodeLayer.Hoare.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslotlt256]
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
          have : st'.locals tw = some flag := by rw [hst', hr]; simp [Lir.IRState.setLocal]
          rw [this] at hloc; exact (Option.some.inj hloc).symm
        have hslot'eq : slot' = slot := by
          rw [show slot = slotOf tw from rfl]
          exact hslots tw slot' hdef
        subst hslot'eq; subst hvflag
        refine ⟨?_, ?_, hslot63, ?_⟩
        · rw [hendmembytes]
          have := BytecodeLayer.Hoare.MemAlgebra.mstore_memory_size resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag (by rw [hslotEq]; exact hslotplat)
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · rw [hendmemactive]
          have := BytecodeLayer.Hoare.MemAlgebra.mstore_activeWords_covers resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63'
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · rw [BytecodeLayer.Hoare.MemAlgebra.mload_congr (UInt256.ofNat slot) hendmembytes hendmemactive]
          exact BytecodeLayer.Hoare.MemAlgebra.mstore_reads_back resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63' hslotplat'
      · -- another bound tmp `tw ≠ t`: unchanged value; its slot survives the disjoint MSTORE.
        have hloc0 : st.locals tw = some v := by
          rw [hst', hr] at hloc
          simpa [Lir.IRState.setLocal, htw] using hloc
        obtain ⟨hcm, ham, hreal, hval⟩ := hmemRes tw slot' v hdef hloc0
        have hslot'lt256 : slot' < 2 ^ 256 := by
          have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega
        have hslot'Eq : (UInt256.ofNat slot').toNat = slot' := by
          rw [BytecodeLayer.Hoare.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslot'lt256]
        have hslot'def : slot' = slotOf tw := hslots tw slot' hdef
        have htwne : t.id ≠ tw.id := fun h => htw (by cases t; cases tw; cases h; rfl)
        have hdisN : slot + 32 ≤ slot' ∨ slot' + 32 ≤ slot := by
          rw [hslotdef, hslot'def]
          exact BytecodeLayer.Hoare.MemAlgebra.slot_windows_disjoint t.id tw.id htwne
        have hdisN' : (UInt256.ofNat slot').toNat + 32 ≤ (UInt256.ofNat slot).toNat
            ∨ (UInt256.ofNat slot).toNat + 32 ≤ (UInt256.ofNat slot').toNat := by
          rw [hslotEq, hslot'Eq]; exact hdisN.symm
        obtain ⟨hmem', hact', hval'⟩ :=
          BytecodeLayer.Hoare.MemAlgebra.mstore_preserves_slot_grow resumeFr.exec.toMachineState
            (UInt256.ofNat slot) (UInt256.ofNat slot') flag hslot63' hslotplat' hcm ham hdisN'
        refine ⟨?_, ?_, hreal, ?_⟩
        · rw [hendmembytes]; exact hmem'
        · rw [hendmemactive]; exact hact'
        · rw [BytecodeLayer.Hoare.MemAlgebra.mload_congr (UInt256.ofNat slot') hendmembytes hendmemactive]
          exact hval'.trans hval

/-- The CREATE counterpart of `sim_call_stmt'`: re-establishes scoped correspondence at a
fixed Route-B tail endpoint from the arm-uniform CREATE resume bundle. -/
theorem sim_create_stmt' {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : IRState} {cs : CreateSpec}
    {L : Label} {b : Block} {pc : Nat} {argsLen : Nat}
    {fr createFr resumeFr endFr : Frame} {result : Evm.CreateResult} {pd : Evm.PendingCreate}
    {self : AccountAddress} {I' : Tmp → Prop}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.create cs))
    (hfrpc : fr.exec.pc = UInt32.ofNat (pcOf prog L pc))
    (hargslen : argsLen
      = (matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value).length)
    (hargs : Runs fr createFr)
    (hcreatepc : createFr.exec.pc = fr.exec.pc + UInt32.ofNat argsLen)
    (hcreatemem : createFr.exec.toMachineState.memory = fr.exec.toMachineState.memory)
    (hcreateactive : fr.exec.toMachineState.activeWords.toNat
      ≤ createFr.exec.toMachineState.activeWords.toNat)
    (hrunsCR : Runs createFr resumeFr)
    (hst' : st' = (match cs.resultTmp with
        | some t => { st with world := fun key => evmCreateOracle.postStorage result pd self key }.setLocal
                      t (createAddrOrZero result pd)
        | none   => { st with world := fun key => evmCreateOracle.postStorage result pd self key }))
    (hresaddr : resumeFr.exec.executionEnv.address = self)
    (hrescode : resumeFr.exec.executionEnv.code = lower prog)
    (hrescanmod : resumeFr.exec.executionEnv.canModifyState = true)
    (hrespc : resumeFr.exec.pc = createFr.exec.pc + 1)
    (hresstack : resumeFr.exec.stack = createAddrOrZero result pd :: [])
    (hresmem : resumeFr.exec.toMachineState.memory = createFr.exec.toMachineState.memory)
    (hresactive : createFr.exec.toMachineState.activeWords.toNat
      ≤ resumeFr.exec.toMachineState.activeWords.toNat)
    (hresvalidjumps : resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0)
    (hresstorage : ∀ key,
      selfStorage resumeFr key = evmCreateOracle.postStorage result pd self key)
    (hsound' : DefsSoundS prog I' st')
    (hmem : Lir.MemRealises prog st fr)
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    (hscoped' : ∀ t, st'.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (htailSome : ∀ t, cs.resultTmp = some t →
      (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
      ∧ Lir.StashRuns resumeFr endFr (slotOf t) (createAddrOrZero result pd) 34 [])
    (htailNone : cs.resultTmp = none →
      Runs resumeFr endFr ∧ endFr = popFrame resumeFr []) :
    Runs fr endFr ∧ Lir.Corr prog sloadChg obs I' st' endFr L (pc + 1)
      ∧ endFr.exec.stack = [] := by
  classical
  -- == the Runs to `resumeFr`: arg pushes then the returning CREATE node ==
  have hruns0 : Runs fr resumeFr := hargs.trans hrunsCR
  have hM3 : ∀ key,
      selfStorage resumeFr key = evmCreateOracle.postStorage result pd self key := hresstorage
  -- `emitStmt .create` length = argsLen + 1 + tailLen.
  have hemitcreate : emitStmt (matCache prog) (defsOf prog) (.create cs)
      = (matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value)
        ++ [Byte.create2]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none   => [Byte.pop]) := rfl
  -- pre-create MemRealises transports `fr → createFr → resumeFr`.
  have hmemRes : Lir.MemRealises prog st resumeFr :=
    ((hmem.transport hcreatemem hcreateactive).transport hresmem hresactive)
  -- == case on the result tmp: the fixed-endpoint Route-B tail ==
  cases hr : cs.resultTmp with
  | none =>
    -- POP tail: `endFr = popFrame resumeFr []`, stack `[]`, memory untouched.
    obtain ⟨hpoprun, hendeq⟩ := htailNone hr
    subst hendeq
    refine ⟨hruns0.trans hpoprun, ?_, by rw [popFrame_stack]⟩
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.create cs)).length
        = argsLen + 1 + 1 := by
      rw [hemitcreate, hr]
      set argsBlock := matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value with hab
      rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton,
        ← hargslen]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (argsLen + 1 + 1) := by
      rw [pcOf_succ prog L b pc (.create cs) hb hs, hemitlen]
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
      rw [popFrame_pc, hrespc, hcreatepc, hfrpc, hpcN,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add,
          show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
      ac_rfl
    · rw [popFrame_code, hrescode]
    · rw [popFrame_validJumps, popFrame_code, hresvalidjumps]
    · rw [popFrame_canMod, hrescanmod]
    · -- M3: world is the resumed self-lens; POP doesn't touch storage.
      intro key
      have hst'none : st' = { st with world := fun key => evmCreateOracle.postStorage result pd self key } := by
        rw [hst', hr]
      rw [hst'none]
      show selfStorage (popFrame resumeFr []) key = _
      rw [show selfStorage (popFrame resumeFr []) key = selfStorage resumeFr key from rfl]
      exact hM3 key
    · -- memAgree: `st'.locals = st.locals`, POP preserves memory bytes + activeWords.
      have hloceq : st' = { st with world := fun key => evmCreateOracle.postStorage result pd self key } := by
        rw [hst', hr]
      intro tw slot v hdef hloc
      rw [hloceq] at hloc
      exact (hmemRes.transport (by rw [popFrame_memory]) (by rw [popFrame_activeWords]))
        tw slot v hdef hloc
  | some t =>
    -- PUSH slot; MSTORE tail at the fixed coupled endpoint `endFr`.
    obtain ⟨hslot63, hslotplat, hstash⟩ := htailSome t hr
    obtain ⟨hendrun, hendmembytes, hendmemactive, hendpc, hendcode,
      hendvalid, hendaddr, hendcanmod, _, hendstorage, hendstk⟩ := hstash
    set flag := createAddrOrZero result pd with hflag
    set slot := slotOf t with hslotdef
    refine ⟨hruns0.trans hendrun, ?_, hendstk⟩
    have hslotlt256 : slot < 2 ^ 256 := by
      have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    have hslotEq : (UInt256.ofNat slot).toNat = slot := by
      rw [BytecodeLayer.Hoare.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslotlt256]
    have hslot63' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by rw [hslotEq]; exact hslot63
    have hslotplat' : (UInt256.ofNat slot).toNat < 2 ^ System.Platform.numBits := by
      rw [hslotEq]; exact hslotplat
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.create cs)).length
        = argsLen + 1 + 34 := by
      rw [hemitcreate, hr]
      set argsBlock := matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value with hab
      rw [List.length_append, List.length_append, List.length_singleton, ← hargslen,
        List.length_append, List.length_singleton, emitImm_length]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (argsLen + 1 + 34) := by
      rw [pcOf_succ prog L b pc (.create cs) hb hs, hemitlen]
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
      rw [hendpc, hrespc, hcreatepc, hfrpc, hpcN,
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
    · -- memAgree: New slot binds flag; other create-result slots preserved.
      intro tw slot' v hdef hloc
      by_cases htw : tw = t
      · -- the just-bound create-result tmp `t`: `slot' = slotOf t = slot`, `v = flag`.
        subst htw
        have hvflag : v = flag := by
          have : st'.locals tw = some flag := by rw [hst', hr]; simp [Lir.IRState.setLocal]
          rw [this] at hloc; exact (Option.some.inj hloc).symm
        have hslot'eq : slot' = slot := by
          rw [show slot = slotOf tw from rfl]
          exact hslots tw slot' hdef
        subst hslot'eq; subst hvflag
        refine ⟨?_, ?_, hslot63, ?_⟩
        · rw [hendmembytes]
          have := BytecodeLayer.Hoare.MemAlgebra.mstore_memory_size resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag (by rw [hslotEq]; exact hslotplat)
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · rw [hendmemactive]
          have := BytecodeLayer.Hoare.MemAlgebra.mstore_activeWords_covers resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63'
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · rw [BytecodeLayer.Hoare.MemAlgebra.mload_congr (UInt256.ofNat slot) hendmembytes hendmemactive]
          exact BytecodeLayer.Hoare.MemAlgebra.mstore_reads_back resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63' hslotplat'
      · -- another bound tmp `tw ≠ t`: unchanged value; its slot survives the disjoint MSTORE.
        have hloc0 : st.locals tw = some v := by
          rw [hst', hr] at hloc
          simpa [Lir.IRState.setLocal, htw] using hloc
        obtain ⟨hcm, ham, hreal, hval⟩ := hmemRes tw slot' v hdef hloc0
        have hslot'lt256 : slot' < 2 ^ 256 := by
          have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega
        have hslot'Eq : (UInt256.ofNat slot').toNat = slot' := by
          rw [BytecodeLayer.Hoare.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslot'lt256]
        have hslot'def : slot' = slotOf tw := hslots tw slot' hdef
        have htwne : t.id ≠ tw.id := fun h => htw (by cases t; cases tw; cases h; rfl)
        have hdisN : slot + 32 ≤ slot' ∨ slot' + 32 ≤ slot := by
          rw [hslotdef, hslot'def]
          exact BytecodeLayer.Hoare.MemAlgebra.slot_windows_disjoint t.id tw.id htwne
        have hdisN' : (UInt256.ofNat slot').toNat + 32 ≤ (UInt256.ofNat slot).toNat
            ∨ (UInt256.ofNat slot).toNat + 32 ≤ (UInt256.ofNat slot').toNat := by
          rw [hslotEq, hslot'Eq]; exact hdisN.symm
        obtain ⟨hmem', hact', hval'⟩ :=
          BytecodeLayer.Hoare.MemAlgebra.mstore_preserves_slot_grow resumeFr.exec.toMachineState
            (UInt256.ofNat slot) (UInt256.ofNat slot') flag hslot63' hslotplat' hcm ham hdisN'
        refine ⟨?_, ?_, hreal, ?_⟩
        · rw [hendmembytes]; exact hmem'
        · rw [hendmemactive]; exact hact'
        · rw [BytecodeLayer.Hoare.MemAlgebra.mload_congr (UInt256.ofNat slot') hendmembytes hendmemactive]
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
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
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
    (hcp : RecorderCoupled log fr gS (rec :: cS') dS)
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
  obtain ⟨resumeFr, callFr, hargs, hcallpc, hcallmem, hcallact, hcallret, hcpres,
      hresaddr0, hrescode, hrescanmod, hrespc, hresstack, hresmem, hresactive,
      hresvalid, hressto⟩ :=
    call_head_realises_coupled hwl hcodeFits hb hcur hcorr hcp hch hcc hcallee hgasfwd
      hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
  have hresaddr : (resumeFr).exec.executionEnv.address
      = self := by rw [hresaddr0, haddr]
  have hM3 : ∀ key, selfStorage resumeFr key =
      evmCallOracle.postStorage rec.result rec.pending self key := by
    intro key
    rw [← haddr]
    exact hressto key
  -- == the IR step: consume the aligned call-stream head (the realised image of `rec`) ==
  have hCcons : C = evmCallEntry rec.result rec.pending self :: callStreamOf cS' self := by
    rw [hal.2.1]; rfl
  have hentry : evmCallEntry rec.result rec.pending self
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
  have hchres : CleanHaltsNonException resumeFr :=
    cleanHaltsNonException_forward hch (hargs.trans hcallret)
  -- == the byte layout at the cursor (`codeFits`-bounded decode anchors for the tail) ==
  set argsB := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hargsB
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = argsB ++ [Byte.call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none => [Byte.pop]) := rfl
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length →
      (lowerBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.call cs))[j]? :=
    fun j hj => lowerBytes_at_pcOf_offset prog L b pc (.call cs) j hbt hcur hj
  -- the resume frame sits one byte past the CALL byte: `pcOf + (|argsB| + 1)`.
  have hpcR : (resumeFr).exec.pc
      = UInt32.ofNat (pcOf prog L pc + (argsB.length + 1)) := by
    have harith : pcOf prog L pc + (argsB.length + 1)
        = pcOf prog L pc + argsB.length + 1 := by omega
    rw [harith, hrespc, hcallpc, hcorr.pc_eq,
        show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add', ofNat_add']
  have hszR : (resumeFr).exec.stack.size + 1 ≤ 1024 := by
    rw [hresstack]; simp
  have hszR' : (resumeFr).exec.stack.size ≤ 1024 := by
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
        (lowerBytes prog)[pcOf prog L pc + j]?
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
        (lowerBytes prog)[pcOf prog L pc + (argsB.length + 1) + j]?
          = (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])[j]? := by
      intro j hj
      have h := segF_suffix (lowerBytes prog) (pcOf prog L pc) (argsB ++ [Byte.call])
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) hseg' j hj
      rwa [show pcOf prog L pc + (argsB ++ [Byte.call]).length
            = pcOf prog L pc + (argsB.length + 1) from by
          simp only [List.length_append, List.length_singleton]] at h
    -- the two tail decode anchors at the resume frame.
    have hdpushR : decode (resumeFr).exec.executionEnv.code
        (resumeFr).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) := by
      rw [hrescode, hpcR]
      exact imm_leaf_decodeF prog (pcOf prog L pc + (argsB.length + 1))
        (UInt256.ofNat (slotOf t)) (by omega)
        (segF_prefix (lowerBytes prog) (pcOf prog L pc + (argsB.length + 1))
          (emitImm (UInt256.ofNat (slotOf t))) [Byte.mstore] hsegTail)
    have hdmstoreR : decode (resumeFr).exec.executionEnv.code
        ((resumeFr).exec.pc + UInt32.ofNat 33)
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
      (resumeFr) .PUSH32 (UInt256.ofNat (slotOf t)) 32
      hchres (by decide) hdpushR (by decide) (by decide) hszR
    have hgasPush3 : 3 ≤ (resumeFr).exec.gasAvailable.toNat := by
      have hvl : GasConstants.Gverylow = 3 := rfl
      omega
    have hcpPush : RecorderCoupled log
        (pushFrameW (resumeFr) (UInt256.ofNat (slotOf t)) 32)
        gS cS' dS := by
      apply recorderCoupled_step_other hcpres
      · unfold isGasOp; rw [hdpushR]; rfl
      · unfold isCreate2Op; rw [hdpushR]; rfl
      · unfold isCallOp; rw [hdpushR]; rfl
      · exact hpushStep
    have hchPush : CleanHaltsNonException
        (pushFrameW (resumeFr) (UInt256.ofNat (slotOf t)) 32) :=
      cleanHaltsNonException_forward hchres
        (runs_push (resumeFr) .PUSH32
          (UInt256.ofNat (slotOf t)) 32 (by nofun) hdpushR rfl rfl hgasPush3 hszR)
    -- == step 2 (COUPLED): MSTORE, writing the success flag at the result slot ==
    have hfrpstk : (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.stack
        = UInt256.ofNat (slotOf t) :: callSuccessFlag rec.result rec.pending :: [] := by
      rw [pushFrameW_stack', hresstack]; rfl
    have hfrpsz : (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.stack.size ≤ 1024 := by
      rw [hfrpstk]; simp
    have hdmstoreF : decode (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
        (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.pc
        = some (.Smsf .MSTORE, .none) := by
      rw [show (pushFrameW (resumeFr)
            (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
          = (resumeFr).exec.executionEnv.code from rfl,
          pushFrameW_pc, push32_pcΔ]
      exact hdmstoreR
    obtain ⟨words', hmemW, hgasMemW, hgasVLW, hmstoreStep⟩ :=
      Lir.CleanHaltExtract.next_mstore_of_cleanHalt
        (pushFrameW (resumeFr) (UInt256.ofNat (slotOf t)) 32)
        (UInt256.ofNat (slotOf t)) (callSuccessFlag rec.result rec.pending) []
        hchPush hdmstoreF hfrpstk hfrpsz
    have hcpEnd : RecorderCoupled log
        (mstoreFrame (pushFrameW (resumeFr)
            (UInt256.ofNat (slotOf t)) 32)
          (UInt256.ofNat (slotOf t)) (callSuccessFlag rec.result rec.pending) words' [])
        gS cS' dS := by
      apply recorderCoupled_step_other hcpPush
      · unfold isGasOp; rw [hdmstoreF]; rfl
      · unfold isCreate2Op; rw [hdmstoreF]; rfl
      · unfold isCallOp; rw [hdmstoreF]; rfl
      · exact hmstoreStep
    -- the packaged tail bundle (`StashRuns`) at exactly the coupled endpoint.
    have hstash : Lir.StashRuns (resumeFr)
        (mstoreFrame (pushFrameW (resumeFr)
            (UInt256.ofNat (slotOf t)) 32)
          (UInt256.ofNat (slotOf t)) (callSuccessFlag rec.result rec.pending) words' [])
        (slotOf t) (callSuccessFlag rec.result rec.pending) 34 [] :=
      stash_tail_runs (resumeFr) (slotOf t)
        (callSuccessFlag rec.result rec.pending) [] words'
        hresstack hdpushR hdmstoreR hszR hgasPush3 hmemW hgasMemW hgasVLW
    -- == `Corr` re-established at the coupled endpoint (S3-call) ==
    obtain ⟨hruns, hcorr', hstk'⟩ := sim_call_stmt'
      (result := rec.result) (pd := rec.pending) (self := self)
      hbt hcur hcorr.pc_eq (by rw [hargsB]) hargs hcallpc hcallmem hcallact hcallret rfl
      hresaddr hrescode hrescanmod hrespc hresstack hresmem hresactive hresvalid hM3
      hsound' hcorr.memAgree (slots_slot_of_defsOf prog) hscoped'
      (fun t' ht' => by
        have heq : t = t' := by
          rw [hr] at ht'
          exact Option.some.inj ht'
        subst heq
        exact ⟨(hslotaddr t hr).1, (hslotaddr t hr).2, hstash⟩)
      (fun hn => by rw [hr] at hn; cases hn)
    rcases hal with ⟨hT, _, hD⟩
    exact ⟨_, _, T, callStreamOf cS' self, D, gS, cS', dS,
      hEval, hruns, hcorr', hstk', hcpEnd, ⟨hT, rfl, hD⟩⟩
  | none =>
    -- byte layout: `argsB ++ [CALL] ++ [POP]`.
    have hemit' : emitStmt (matCache prog) (defsOf prog) (.call cs)
        = (argsB ++ [Byte.call]) ++ [Byte.pop] := by
      rw [hemit0, hr]
    have hseg' : ∀ j, j < ((argsB ++ [Byte.call]) ++ [Byte.pop]).length →
        (lowerBytes prog)[pcOf prog L pc + j]?
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
    have hdpopR : decode (resumeFr).exec.executionEnv.code
        (resumeFr).exec.pc
        = some (.Smsf .POP, .none) := by
      rw [hrescode, hpcR]
      have h := nonpush_leaf_decodeF prog (pcOf prog L pc) (argsB.length + 1) Byte.pop
        ((argsB ++ [Byte.call]) ++ [Byte.pop])
        (stmt_offset_bound_of_codeFits hcodeFits hb hcur (by rw [hemitlen]; omega))
        hpopbyte (by decide) hseg'
      simpa using h
    -- == the one COUPLED POP step ==
    obtain ⟨hgasPop, hpopStep⟩ := Lir.CleanHaltExtract.next_pop_of_cleanHalt
      (resumeFr)
      (callSuccessFlag rec.result rec.pending) [] hchres hdpopR hresstack hszR'
    have hpoprun : Runs (resumeFr)
        (popFrame (resumeFr) []) :=
      runs_pop (resumeFr)
        (callSuccessFlag rec.result rec.pending) [] hdpopR hresstack hszR' hgasPop
    have hcpEnd : RecorderCoupled log
        (popFrame (resumeFr) []) gS cS' dS := by
      apply recorderCoupled_step_other hcpres
      · unfold isGasOp; rw [hdpopR]; rfl
      · unfold isCreate2Op; rw [hdpopR]; rfl
      · unfold isCallOp; rw [hdpopR]; rfl
      · exact hpopStep
    -- == `Corr` re-established at the coupled endpoint (S3-call) ==
    obtain ⟨hruns, hcorr', hstk'⟩ := sim_call_stmt'
      (result := rec.result) (pd := rec.pending) (self := self)
      hbt hcur hcorr.pc_eq (by rw [hargsB]) hargs hcallpc hcallmem hcallact hcallret rfl
      hresaddr hrescode hrescanmod hrespc hresstack hresmem hresactive hresvalid hM3
      hsound' hcorr.memAgree (slots_slot_of_defsOf prog) hscoped'
      (fun t' ht' => by rw [hr] at ht'; cases ht')
      (fun _ => ⟨hpoprun, rfl⟩)
    rcases hal with ⟨hT, _, hD⟩
    exact ⟨_, _, T, callStreamOf cS' self, D, gS, cS', dS,
      hEval, hruns, hcorr', hstk', hcpEnd, ⟨hT, rfl, hD⟩⟩

/-- **P2-create — the external-CREATE coupled step.** The CREATE twin of
`simStmt_coupled_call`, mirroring the CALL arm field-for-field:
the four operand bindings (value/off/size/salt), the `CreateResolves` reachable-frames seam (the
create analogue of the `CallsCode` seam), the four operand stack-room folds, and the result-slot
addressability; the coupling's `createSuffix` head `rec` is consumed (`EvalStmt.create` on the
aligned `createStreamOf` head), gas/sload/call suffixes ride unchanged.

It consumes the arm-uniform `create_head_realises_coupled`, constructs the coupled Route-B tail,
and uses `sim_create_stmt'` to re-establish correspondence at its fixed endpoint. -/
theorem simStmt_coupled_create {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat}
    {cs : CreateSpec} {st : IRState} {fr : Frame}
    {valueW initOffW initSizeW saltW : Word}
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
    {cS : List CallRecord} {rec : CreateRecord} {dS' : List CreateRecord}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hcorr : Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) st fr L pc)
    (hcp : RecorderCoupled log fr gS cS (rec :: dS'))
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
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  have hfreeValue : RematClosureFree prog
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp cs.value) :=
    hwl.scopedUses L b pc (.create cs) hb hcur cs.value (by simp [readsStmt])
  have hfreeOff : RematClosureFree prog
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp cs.initOffset) :=
    hwl.scopedUses L b pc (.create cs) hb hcur cs.initOffset (by simp [readsStmt])
  have hfreeSize : RematClosureFree prog
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp cs.initSize) :=
    hwl.scopedUses L b pc (.create cs) hb hcur cs.initSize (by simp [readsStmt])
  have hfreeSalt : RematClosureFree prog
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp cs.salt) :=
    hwl.scopedUses L b pc (.create cs) hb hcur cs.salt (by simp [readsStmt])
  obtain ⟨resumeFr, createFr, hargs, hcreatepc, hcreatemem, hcreateact, hrunsCR, hcpres,
      hresaddr0, hrescode, hrescanmod, hrespc, hresstack, hresmem, hresactive, hresvalid,
      hressto⟩ :=
    create_head_realises_coupled hwl hcodeFits hb hcur hcorr hcp hch hcr
      hvalue hoff hsize hsalt hfreeValue hfreeOff hfreeSize hfreeSalt
      hstkSalt hstkSize hstkOff hstkValue
  have hresaddr : resumeFr.exec.executionEnv.address = self := by rw [hresaddr0, haddr]
  have hressto' : ∀ k, selfStorage resumeFr k =
      evmCreateOracle.postStorage rec.result rec.pending self k := by
    intro k
    rw [← haddr]
    exact hressto k
  have hDcons : D = evmCreateEntry rec.result rec.pending self
      :: createStreamOf dS' self := by
    rw [hal.2.2]; rfl
  have hentry : evmCreateEntry rec.result rec.pending self
      = ((fun key => evmCreateOracle.postStorage rec.result rec.pending self key),
          createAddrOrZero rec.result rec.pending) := rfl
  have hEval : EvalStmt prog st T C D (.create cs)
      (match cs.resultTmp with
        | some t' => { st with world := fun key =>
                        evmCreateOracle.postStorage rec.result rec.pending self key }.setLocal
                        t' (createAddrOrZero rec.result rec.pending)
        | none => { st with world := fun key =>
                        evmCreateOracle.postStorage rec.result rec.pending self key })
      T C (createStreamOf dS' self) := by
    rw [hDcons, hentry]
    exact EvalStmt.create hvalue hoff hsize hsalt
  have hsound' := defsSoundS_preserved_step hwl.defsCons hb hcur hEval hcorr.defsSound
  have hscoped' := create_post_wellScoped'
    (world' := fun key => evmCreateOracle.postStorage rec.result rec.pending self key)
    (addrW := createAddrOrZero rec.result rec.pending)
    hb hcur hwl.defsCons hcorr.wellScoped
  have hchres : CleanHaltsNonException resumeFr :=
    cleanHaltsNonException_forward hch (hargs.trans hrunsCR)
  set argsB := matCache prog cs.salt ++ matCache prog cs.initSize
      ++ matCache prog cs.initOffset ++ matCache prog cs.value with hargsB
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.create cs)
      = argsB ++ [Byte.create2]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none => [Byte.pop]) := rfl
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.create cs)).length →
      (lowerBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.create cs))[j]? :=
    fun j hj => lowerBytes_at_pcOf_offset prog L b pc (.create cs) j hbt hcur hj
  have hpcR : resumeFr.exec.pc
      = UInt32.ofNat (pcOf prog L pc + (argsB.length + 1)) := by
    have harith : pcOf prog L pc + (argsB.length + 1)
        = pcOf prog L pc + argsB.length + 1 := by omega
    rw [harith, hrespc, hcreatepc, hcorr.pc_eq,
        show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add', ofNat_add']
  have hszR : resumeFr.exec.stack.size + 1 ≤ 1024 := by
    rw [hresstack]; simp
  have hszR' : resumeFr.exec.stack.size ≤ 1024 := by
    rw [hresstack]; simp
  -- == case on the result tmp: build the COUPLED Route-B tail, then re-establish `Corr` ==
  cases hr : cs.resultTmp with
  | some t =>
    -- byte layout: `argsB ++ [CREATE] ++ (PUSH32 (slotOf t) ++ [MSTORE])`.
    have hemit' : emitStmt (matCache prog) (defsOf prog) (.create cs)
        = (argsB ++ [Byte.create2]) ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) := by
      rw [hemit0, hr]
    have hseg' : ∀ j, j < ((argsB ++ [Byte.create2])
          ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])).length →
        (lowerBytes prog)[pcOf prog L pc + j]?
          = ((argsB ++ [Byte.create2])
              ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]))[j]? := by
      intro j hj
      rw [← hemit']
      exact hseg j (by rw [hemit']; exact hj)
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.create cs)).length
        = argsB.length + 1 + 34 := by
      rw [hemit']
      simp only [List.length_append, List.length_singleton, emitImm_length]
    have hlast : pcOf prog L pc + (argsB.length + 34) < 2 ^ 32 :=
      stmt_offset_bound_of_codeFits hcodeFits hb hcur (by rw [hemitlen]; omega)
    have hsegTail : ∀ j, j < (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]).length →
        (lowerBytes prog)[pcOf prog L pc + (argsB.length + 1) + j]?
          = (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])[j]? := by
      intro j hj
      have h := segF_suffix (lowerBytes prog) (pcOf prog L pc) (argsB ++ [Byte.create2])
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) hseg' j hj
      rwa [show pcOf prog L pc + (argsB ++ [Byte.create2]).length
            = pcOf prog L pc + (argsB.length + 1) from by
          simp only [List.length_append, List.length_singleton]] at h
    -- the two tail decode anchors at the resume frame.
    have hdpushR : decode (resumeFr).exec.executionEnv.code
        (resumeFr).exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) := by
      rw [hrescode, hpcR]
      exact imm_leaf_decodeF prog (pcOf prog L pc + (argsB.length + 1))
        (UInt256.ofNat (slotOf t)) (by omega)
        (segF_prefix (lowerBytes prog) (pcOf prog L pc + (argsB.length + 1))
          (emitImm (UInt256.ofNat (slotOf t))) [Byte.mstore] hsegTail)
    have hdmstoreR : decode (resumeFr).exec.executionEnv.code
        ((resumeFr).exec.pc + UInt32.ofNat 33)
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
      (resumeFr) .PUSH32 (UInt256.ofNat (slotOf t)) 32
      hchres (by decide) hdpushR (by decide) (by decide) hszR
    have hgasPush3 : 3 ≤ (resumeFr).exec.gasAvailable.toNat := by
      have hvl : GasConstants.Gverylow = 3 := rfl
      omega
    have hcpPush : RecorderCoupled log
        (pushFrameW (resumeFr) (UInt256.ofNat (slotOf t)) 32)
        gS cS dS' := by
      apply recorderCoupled_step_other hcpres
      · unfold isGasOp; rw [hdpushR]; rfl
      · unfold isCreate2Op; rw [hdpushR]; rfl
      · unfold isCallOp; rw [hdpushR]; rfl
      · exact hpushStep
    have hchPush : CleanHaltsNonException
        (pushFrameW (resumeFr) (UInt256.ofNat (slotOf t)) 32) :=
      cleanHaltsNonException_forward hchres
        (runs_push (resumeFr) .PUSH32
          (UInt256.ofNat (slotOf t)) 32 (by nofun) hdpushR rfl rfl hgasPush3 hszR)
    -- == step 2 (COUPLED): MSTORE, writing the created address at the result slot ==
    have hfrpstk : (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.stack
        = UInt256.ofNat (slotOf t) :: createAddrOrZero rec.result rec.pending :: [] := by
      rw [pushFrameW_stack', hresstack]; rfl
    have hfrpsz : (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.stack.size ≤ 1024 := by
      rw [hfrpstk]; simp
    have hdmstoreF : decode (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
        (pushFrameW (resumeFr)
          (UInt256.ofNat (slotOf t)) 32).exec.pc
        = some (.Smsf .MSTORE, .none) := by
      rw [show (pushFrameW (resumeFr)
            (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
          = (resumeFr).exec.executionEnv.code from rfl,
          pushFrameW_pc, push32_pcΔ]
      exact hdmstoreR
    obtain ⟨words', hmemW, hgasMemW, hgasVLW, hmstoreStep⟩ :=
      Lir.CleanHaltExtract.next_mstore_of_cleanHalt
        (pushFrameW (resumeFr) (UInt256.ofNat (slotOf t)) 32)
        (UInt256.ofNat (slotOf t)) (createAddrOrZero rec.result rec.pending) []
        hchPush hdmstoreF hfrpstk hfrpsz
    have hcpEnd : RecorderCoupled log
        (mstoreFrame (pushFrameW (resumeFr)
            (UInt256.ofNat (slotOf t)) 32)
          (UInt256.ofNat (slotOf t)) (createAddrOrZero rec.result rec.pending) words' [])
        gS cS dS' := by
      apply recorderCoupled_step_other hcpPush
      · unfold isGasOp; rw [hdmstoreF]; rfl
      · unfold isCreate2Op; rw [hdmstoreF]; rfl
      · unfold isCallOp; rw [hdmstoreF]; rfl
      · exact hmstoreStep
    -- the packaged tail bundle (`StashRuns`) at exactly the coupled endpoint.
    have hstash : Lir.StashRuns (resumeFr)
        (mstoreFrame (pushFrameW (resumeFr)
            (UInt256.ofNat (slotOf t)) 32)
          (UInt256.ofNat (slotOf t)) (createAddrOrZero rec.result rec.pending) words' [])
        (slotOf t) (createAddrOrZero rec.result rec.pending) 34 [] :=
      stash_tail_runs (resumeFr) (slotOf t)
        (createAddrOrZero rec.result rec.pending) [] words'
        hresstack hdpushR hdmstoreR hszR hgasPush3 hmemW hgasMemW hgasVLW
    -- == `Corr` re-established at the coupled endpoint (S3-create) ==
    obtain ⟨hruns, hcorr', hstk'⟩ := sim_create_stmt'
      (result := rec.result) (pd := rec.pending) (self := self)
      hbt hcur hcorr.pc_eq (by rw [hargsB]) hargs hcreatepc hcreatemem hcreateact hrunsCR rfl
      hresaddr hrescode hrescanmod hrespc hresstack hresmem hresactive hresvalid hressto'
      hsound' hcorr.memAgree (slots_slot_of_defsOf prog) hscoped'
      (fun t' ht' => by
        have heq : t = t' := by
          rw [hr] at ht'
          exact Option.some.inj ht'
        subst heq
        exact ⟨(hslotaddr t hr).1, (hslotaddr t hr).2, hstash⟩)
      (fun hn => by rw [hr] at hn; cases hn)
    rcases hal with ⟨hT, hC, _⟩
    exact ⟨_, _, T, C, createStreamOf dS' self, gS, cS, dS',
      hEval, hruns, hcorr', hstk', hcpEnd, ⟨hT, hC, rfl⟩⟩
  | none =>
    -- byte layout: `argsB ++ [CREATE] ++ [POP]`.
    have hemit' : emitStmt (matCache prog) (defsOf prog) (.create cs)
        = (argsB ++ [Byte.create2]) ++ [Byte.pop] := by
      rw [hemit0, hr]
    have hseg' : ∀ j, j < ((argsB ++ [Byte.create2]) ++ [Byte.pop]).length →
        (lowerBytes prog)[pcOf prog L pc + j]?
          = ((argsB ++ [Byte.create2]) ++ [Byte.pop])[j]? := by
      intro j hj
      rw [← hemit']
      exact hseg j (by rw [hemit']; exact hj)
    have hemitlen : (emitStmt (matCache prog) (defsOf prog) (.create cs)).length
        = argsB.length + 1 + 1 := by
      rw [hemit']
      simp only [List.length_append, List.length_singleton]
    -- the POP decode anchor at the resume frame.
    have hpopbyte : ((argsB ++ [Byte.create2]) ++ [Byte.pop])[argsB.length + 1]?
        = some Byte.pop := by
      rw [List.getElem?_append_right (by
            simp only [List.length_append, List.length_singleton]; omega)]
      simp
    have hdpopR : decode (resumeFr).exec.executionEnv.code
        (resumeFr).exec.pc
        = some (.Smsf .POP, .none) := by
      rw [hrescode, hpcR]
      have h := nonpush_leaf_decodeF prog (pcOf prog L pc) (argsB.length + 1) Byte.pop
        ((argsB ++ [Byte.create2]) ++ [Byte.pop])
        (stmt_offset_bound_of_codeFits hcodeFits hb hcur (by rw [hemitlen]; omega))
        hpopbyte (by decide) hseg'
      simpa using h
    -- == the one COUPLED POP step ==
    obtain ⟨hgasPop, hpopStep⟩ := Lir.CleanHaltExtract.next_pop_of_cleanHalt
      (resumeFr)
      (createAddrOrZero rec.result rec.pending) [] hchres hdpopR hresstack hszR'
    have hpoprun : Runs (resumeFr)
        (popFrame (resumeFr) []) :=
      runs_pop (resumeFr)
        (createAddrOrZero rec.result rec.pending) [] hdpopR hresstack hszR' hgasPop
    have hcpEnd : RecorderCoupled log
        (popFrame (resumeFr) []) gS cS dS' := by
      apply recorderCoupled_step_other hcpres
      · unfold isGasOp; rw [hdpopR]; rfl
      · unfold isCreate2Op; rw [hdpopR]; rfl
      · unfold isCallOp; rw [hdpopR]; rfl
      · exact hpopStep
    -- == `Corr` re-established at the coupled endpoint (S3-create) ==
    obtain ⟨hruns, hcorr', hstk'⟩ := sim_create_stmt'
      (result := rec.result) (pd := rec.pending) (self := self)
      hbt hcur hcorr.pc_eq (by rw [hargsB]) hargs hcreatepc hcreatemem hcreateact hrunsCR rfl
      hresaddr hrescode hrescanmod hrespc hresstack hresmem hresactive hresvalid hressto'
      hsound' hcorr.memAgree (slots_slot_of_defsOf prog) hscoped'
      (fun t' ht' => by rw [hr] at ht'; cases ht')
      (fun _ => ⟨hpoprun, rfl⟩)
    rcases hal with ⟨hT, hC, _⟩
    exact ⟨_, _, T, C, createStreamOf dS' self, gS, cS, dS',
      hEval, hruns, hcorr', hstk', hcpEnd, ⟨hT, hC, rfl⟩⟩


/-! ## §3 — the COUPLED block walk and the per-block step -/

/-- The COUPLED block-run output at the terminator cursor `(L, b.stmts.length)`: the IR
`RunStmts` of the whole block (from the aligned streams), the bytecode `Runs fr fr'`, the
re-established `Corr` + empty stack + clean-halt at `fr'`, the advanced coupling + alignment,
and the self/address/kind pins transported to `fr'` (for the `TermTies'` antecedents). REAL def. -/
def CoupledBlockRun (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog) (self : AccountAddress)
    (L : Label) (b : Block) (st : IRState) (fr : Frame)
    (T : Trace) (C : CallStream) (D : CreateStream) : Prop :=
  ∃ (st' : IRState) (fr' : Frame) (T' : Trace) (C' : CallStream) (D' : CreateStream)
    (gS' : List Word) (cS' : List CallRecord) (dS' : List CreateRecord),
    RunStmts prog st T C D b.stmts st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 (fun _ => False) st' fr' L b.stmts.length
    ∧ fr'.exec.stack = []
    ∧ CleanHaltsNonException fr'
    ∧ RecorderCoupled log fr' gS' cS' dS'
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
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
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
    (hcp : RecorderCoupled log fr gS cS dS)
    (hch : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hkind : ∃ cp, fr.kind = .call cp)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hstmts : StmtTies' prog sloadChg log self L b)
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    CoupledBlockRun prog sloadChg log self L b st fr T C D := by
  classical
  let WalkAt := fun (pc : Nat) (stc : IRState) (frc : Frame)
      (Tc : Trace) (Cc : CallStream) (Dc : CreateStream)
      (gSc : List Word) (cSc : List CallRecord) (dSc : List CreateRecord) =>
    RunStmts prog st T C D (b.stmts.take pc) stc Tc Cc Dc →
    Runs fr frc →
    Lir.Corr prog sloadChg 0
      ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) stc frc L pc →
    frc.exec.stack = [] → RecorderCoupled log frc gSc cSc dSc →
    CleanHaltsNonException frc → SelfPresent frc →
    frc.exec.executionEnv.address = self → (∃ cp, frc.kind = .call cp) →
    StreamsAligned self log gSc cSc dSc Tc Cc Dc →
    (∀ fr', Runs frc fr' → CallsCode fr') →
    (∀ fr', Runs frc fr' → CreateResolves fr') →
    CoupledBlockRun prog sloadChg log self L b st fr T C D
  have walk : ∀ n pc stc frc Tc Cc Dc gSc cSc dSc,
      b.stmts.length - pc = n → pc ≤ b.stmts.length →
      WalkAt pc stc frc Tc Cc Dc gSc cSc dSc := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro pc stc frc Tc Cc Dc gSc cSc dSc hmeasure hpcle
      intro hpre hrunpre hcorr hstack hcpC hclean hself haddrC hkindC halC hccC hcrC
      by_cases hend : pc = b.stmts.length
      · subst pc
        have hIfalse :
            (b.stmts.foldl (invalStep prog) (fun _ => False)) = (fun _ => False) := by
          funext t
          apply propext
          exact ⟨fun ht => absurd ht (hwl.revalidates L b hb t), fun ht => ht.elim⟩
        have hcorrEnd : Lir.Corr prog sloadChg 0 (fun _ => False) stc frc L b.stmts.length := by
          simpa [hIfalse] using hcorr
        exact ⟨stc, frc, Tc, Cc, Dc, gSc, cSc, dSc,
          by simpa using hpre, hrunpre, hcorrEnd, hstack, hclean, hcpC, halC,
          hself, haddrC, hkindC⟩
      · have hpclt : pc < b.stmts.length := lt_of_le_of_ne hpcle hend
        let s := b.stmts[pc]
        have hcur : b.stmts[pc]? = some s := List.getElem?_eq_getElem hpclt
        have hdef : StmtDefinableG stc s :=
          hwl.defs.stmts st stc T Tc C Cc D Dc L b pc s hb hcur hpre
        have hadv : CoupledAdvance prog sloadChg log self
            ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False))
            L pc stc frc Tc Cc Dc s := by
          cases hs : s with
          | assign t e =>
            simp only [hs, StmtDefinableG] at hdef
            by_cases heg : e = .gas
            · subst e
              exact simStmt_coupled_gas hwl hb (by simpa [hs] using hcur)
                hcorr hcpC hclean halC hstmts
            · by_cases hes : ∃ k, e = .sload k
              · obtain ⟨k, rfl⟩ := hes
                obtain hbad | ⟨w, hw⟩ := hdef
                · exact absurd hbad heg
                · cases hkey : stc.locals k with
                  | none => simp [evalExpr, hkey] at hw
                  | some kv =>
                  exact simStmt_coupled_sload hwl hb (by simpa [hs] using hcur)
                    hcorr hcpC hclean halC hkey hstmts
              · obtain hbad | ⟨w, hw⟩ := hdef
                · exact absurd hbad heg
                · exact simStmt_coupled_assignPure hwl hb (by simpa [hs] using hcur)
                    heg (fun k he => hes ⟨k, he⟩) hcorr hcpC hclean halC hw hstmts
          | sstore key value =>
            simp only [hs, StmtDefinableG] at hdef
            obtain ⟨⟨kw, hk⟩, ⟨vw, hv⟩⟩ := hdef
            exact simStmt_coupled_sstore hwl hb (by simpa [hs] using hcur)
              hcorr hcpC hclean hself halC hk hv hstmts
          | call cs =>
            simp only [hs, StmtDefinableG] at hdef
            obtain ⟨⟨cw, hcallee⟩, ⟨gw, hgasfwd⟩⟩ := hdef
            have hfreeCallee := hwl.scopedUses L b pc (.call cs) hb
              (by simpa [hs] using hcur) cs.callee (by simp [readsStmt])
            have hfreeGasFwd := hwl.scopedUses L b pc (.call cs) hb
              (by simpa [hs] using hcur) cs.gasFwd (by simp [readsStmt])
            have hstkCallee := hwl.stack.callCallee sloadChg L b pc cs hb
              (by simpa [hs] using hcur)
            have hstkGasFwd := hwl.stack.callGasFwd sloadChg L b pc cs hb
              (by simpa [hs] using hcur)
            obtain ⟨rec, cS', hcS⟩ := callSuffix_nonempty_at_stmt hwl hcodeFits hb
              (by simpa [hs] using hcur) hcorr hcpC hclean hcallee hgasfwd
              hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
            subst cSc
            exact simStmt_coupled_call hwl hcodeFits hb (by simpa [hs] using hcur)
              hcorr hcpC hclean haddrC hccC hcallee hgasfwd hstkCallee hstkGasFwd
              (fun t ht => hwl.slotAddr L b pc t hb
                (Or.inr (Or.inr (Or.inl ⟨cs, by simpa [hs] using hcur, ht⟩))))
              halC hstmts
          | create cs =>
            simp only [hs, StmtDefinableG] at hdef
            obtain ⟨⟨valueW, hvalue⟩, ⟨initOffW, hoff⟩, ⟨initSizeW, hsize⟩,
              ⟨saltW, hsalt⟩⟩ := hdef
            have hfreeValue := hwl.scopedUses L b pc (.create cs) hb
              (by simpa [hs] using hcur) cs.value (by simp [readsStmt])
            have hfreeOff := hwl.scopedUses L b pc (.create cs) hb
              (by simpa [hs] using hcur) cs.initOffset (by simp [readsStmt])
            have hfreeSize := hwl.scopedUses L b pc (.create cs) hb
              (by simpa [hs] using hcur) cs.initSize (by simp [readsStmt])
            have hfreeSalt := hwl.scopedUses L b pc (.create cs) hb
              (by simpa [hs] using hcur) cs.salt (by simp [readsStmt])
            obtain ⟨hstkSalt, hstkSize, hstkOff, hstkValue⟩ :=
              hwl.stack.createOperands sloadChg L b pc cs hb (by simpa [hs] using hcur)
            have hstkSalt' : 0 + (chargeCache prog sloadChg cs.salt).length ≤ 1024 := by
              simpa using hstkSalt
            obtain ⟨rec, dS', hdS⟩ := createSuffix_nonempty_at_stmt hwl hcodeFits hb
              (by simpa [hs] using hcur) hcorr hcpC hclean hvalue hoff hsize hsalt
              hfreeValue hfreeOff hfreeSize hfreeSalt hstkSalt' hstkSize hstkOff hstkValue
            subst dSc
            exact simStmt_coupled_create hwl hcodeFits hb (by simpa [hs] using hcur)
              hcorr hcpC hclean haddrC hcrC hvalue hoff hsize hsalt hstkSalt' hstkSize
              hstkOff hstkValue
              (fun t ht => hwl.slotAddr L b pc t hb
                (Or.inr (Or.inr (Or.inr ⟨cs, by simpa [hs] using hcur, ht⟩))))
              halC hstmts
        obtain ⟨st', fr', T', C', D', gS', cS', dS', hEval, hrun, hcorr',
          hstack', hcp', hal'⟩ := hadv
        have htake : b.stmts.take (pc + 1) = b.stmts.take pc ++ [s] := by
          rw [List.take_succ, hcur]
          rfl
        have hpre' : RunStmts prog st T C D (b.stmts.take (pc + 1)) st' T' C' D' := by
          rw [htake]
          exact runStmts_snoc hpre hEval
        have hfold :
            (b.stmts.take (pc + 1)).foldl (invalStep prog) (fun _ => False) =
              invalStep prog ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) s := by
          rw [htake, List.foldl_append]
          rfl
        have hcorr'' : Lir.Corr prog sloadChg 0
            ((b.stmts.take (pc + 1)).foldl (invalStep prog) (fun _ => False))
            st' fr' L (pc + 1) := by
          rw [hfold]
          exact hcorr'
        have hclean' := cleanHaltsNonException_forward hclean hrun
        have hself' := selfPresent_runs_of_call hprec hself hrun
        have haddr' : fr'.exec.executionEnv.address = self := by
          rw [runs_address_preserved hrun, haddrC]
        have hkind' : ∃ cp, fr'.kind = .call cp := by
          obtain ⟨cp, hcpkind⟩ := hkindC
          exact ⟨cp, (runs_kind hrun).trans hcpkind⟩
        have hnextlt : b.stmts.length - (pc + 1) < n := by omega
        exact ih (b.stmts.length - (pc + 1)) hnextlt (pc + 1)
          st' fr' T' C' D' gS' cS' dS' rfl (by omega)
          hpre' (hrunpre.trans hrun) hcorr'' hstack' hcp' hclean' hself' haddr' hkind' hal'
          (fun f hf => hccC f (hrun.trans hf))
          (fun f hf => hcrC f (hrun.trans hf))
  exact walk b.stmts.length 0 st fr T C D gS cS dS (by omega) (by omega)
    (by simpa using (RunStmts.nil : RunStmts prog st T C D [] st T C D))
    (Runs.refl fr) (by simpa using hcorr) hcorr.stack_nil hcp hch hsp haddr hkind hal hcc hcr

/-- Recorder coupling follows the lowered `ret` epilogue to its terminal frame.  The epilogue
contains only materialisation, pushes, and an `MSTORE`; none of those instructions records an
oracle event. -/
private theorem recorderCoupled_term_ret {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {st : IRState} {t : Tmp} {w : Word} {L : Label} {b : Block} {fr : Frame}
    {gS : List Word} {cS : List CallRecord} {dS : List CreateRecord}
    (hcorr : Corr prog sloadChg 0 (fun _ => False) st fr L b.stmts.length)
    (hw : st.locals t = some w)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (hdv : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc (.tmp t))
    (hgas : (chargeCache prog sloadChg t).sum ≤ fr.exec.gasAvailable.toNat)
    (hstk : (chargeCache prog sloadChg t).length ≤ 1024)
    (hret : ∀ frv : Frame, Runs fr frv →
        frv.exec.executionEnv.code = fr.exec.executionEnv.code →
        frv.exec.executionEnv.address = fr.exec.executionEnv.address →
        (∀ k, selfStorage frv k = selfStorage fr k) →
        frv.exec.stack = w :: fr.exec.stack →
        frv.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog t).length →
        ∃ cp wms,
          decode frv.exec.executionEnv.code frv.exec.pc
              = some (.Push .PUSH32, some ((0 : Word), 32))
          ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
              = some (.Smsf .MSTORE, .none)
          ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + 1)
              = some (.Push .PUSH32, some ((32 : Word), 32))
          ∧ decode frv.exec.executionEnv.code
              (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33)
              = some (.Push .PUSH32, some ((0 : Word), 32))
          ∧ decode frv.exec.executionEnv.code
              (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33 + UInt32.ofNat 33)
              = some (.System .RETURN, .none)
          ∧ 3 ≤ frv.exec.gasAvailable.toNat
          ∧ memoryExpansionWords? frv.exec.activeWords (0 : Word) 32 = some wms
          ∧ memExpansionChargeOf (pushFrameW frv (0 : Word) 32).exec wms
              ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
          ∧ GasConstants.Gverylow ≤ ((pushFrameW frv (0 : Word) 32).exec.gasAvailable
              - UInt64.ofNat (memExpansionChargeOf (pushFrameW frv (0 : Word) 32).exec wms)).toNat
          ∧ 3 ≤ (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) w wms []).exec.gasAvailable.toNat
          ∧ 3 ≤ (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32)
                    (0 : Word) w wms []) (32 : Word) 32).exec.gasAvailable.toNat
          ∧ frv.kind = .call cp ∧ ¬ (frv.exec.accounts == ∅) = true)
    (hcp : RecorderCoupled log fr gS cS dS) :
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
      ∧ RecorderCoupled log last gS cS dS := by
  have heval : evalExpr st 0 (.tmp t) = some w := hw
  have hgas' : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp t)).sum
      ≤ fr.exec.gasAvailable.toNat := by simpa only [chargeExpr_tmp] using hgas
  have hstk' : fr.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp t)).length ≤ 1024 := by
    rw [hcorr.stack_nil]
    simp only [chargeExpr_tmp]
    change 0 + (chargeCache prog sloadChg t).length ≤ 1024
    omega
  obtain ⟨frv, hmrv, hcpv⟩ := recorderCoupled_matRunsC hdc hord sloadChg st 0 log
    gS cS dS (fun _ => False) (.tmp t) w fr hdv hcorr.defsSound
    (rematClosureFree_empty prog hdc hord (.tmp t)) hcorr.wellScoped hcorr.storage
    (by nofun) (by nofun) hcorr.memAgree heval hgas' hstk' hcp
  obtain ⟨cp, wms, hd0, hdms, hd32, hd0', hdret, hg0, hmemms, hgasMem, hgasV,
    hg32, hg0'', hkind, hne⟩ := hret frv hmrv.runs hmrv.code hmrv.addr hmrv.storage
      hmrv.stack hmrv.pc
  have hfrvstk : frv.exec.stack = w :: ([] : Stack Word) := by
    simpa [hcorr.stack_nil] using hmrv.stack
  have hsz1 : frv.exec.stack.size + 1 ≤ 1024 := by simp [hfrvstk]
  let f1 := pushFrameW frv (0 : Word) 32
  have hf1step : StepsTo frv f1 := stepsTo_of_next
    (stepFrame_push frv .PUSH32 (0 : Word) 32 (by decide) hd0 (by decide) (by decide) hg0 hsz1)
  have hcp1 := recorderCoupled_stepsTo_other hcpv
    (by unfold isGasOp; rw [hd0]; rfl)
    (by unfold isCreate2Op; rw [hd0]; rfl)
    (by unfold isCallOp; rw [hd0]; rfl) hf1step
  have hf1stk : f1.exec.stack = (0 : Word) :: w :: ([] : Stack Word) := by
    change (0 : Word) :: frv.exec.stack = _; rw [hfrvstk]
  have hdms' : decode f1.exec.executionEnv.code f1.exec.pc = some (.Smsf .MSTORE, .none) := by
    change decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33) = _
    exact hdms
  have hf1sz : f1.exec.stack.size ≤ 1024 := by simp [hf1stk]
  have hmemms' : memoryExpansionWords? f1.exec.activeWords (0 : Word) 32 = some wms := hmemms
  let fms := mstoreFrame f1 (0 : Word) w wms []
  have hmsstep : StepsTo f1 fms := stepsTo_of_next
    (stepFrame_mstore f1 (0 : Word) w wms [] hdms' hf1stk hf1sz hmemms' hgasMem hgasV)
  have hcpms := recorderCoupled_stepsTo_other hcp1
    (by unfold isGasOp; rw [hdms']; rfl)
    (by unfold isCreate2Op; rw [hdms']; rfl)
    (by unfold isCallOp; rw [hdms']; rfl) hmsstep
  have hd32' : decode fms.exec.executionEnv.code fms.exec.pc
      = some (.Push .PUSH32, some ((32 : Word), 32)) := by
    change decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + 1) = _
    exact hd32
  have hfmsstk : fms.exec.stack = ([] : Stack Word) := rfl
  have hfmssz : fms.exec.stack.size + 1 ≤ 1024 := by simp [hfmsstk]
  let f2 := pushFrameW fms (32 : Word) 32
  have hf2step : StepsTo fms f2 := stepsTo_of_next
    (stepFrame_push fms .PUSH32 (32 : Word) 32 (by decide) hd32' (by decide) (by decide) hg32 hfmssz)
  have hcp2 := recorderCoupled_stepsTo_other hcpms
    (by unfold isGasOp; rw [hd32']; rfl)
    (by unfold isCreate2Op; rw [hd32']; rfl)
    (by unfold isCallOp; rw [hd32']; rfl) hf2step
  have hf2stk : f2.exec.stack = (32 : Word) :: ([] : Stack Word) := rfl
  have hd0'' : decode f2.exec.executionEnv.code f2.exec.pc
      = some (.Push .PUSH32, some ((0 : Word), 32)) := by
    change decode frv.exec.executionEnv.code
      (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33) = _
    exact hd0'
  have hf2sz : f2.exec.stack.size + 1 ≤ 1024 := by simp [hf2stk]
  let f3 := pushFrameW f2 (0 : Word) 32
  have hf3step : StepsTo f2 f3 := stepsTo_of_next
    (stepFrame_push f2 .PUSH32 (0 : Word) 32 (by decide) hd0'' (by decide) (by decide) hg0'' hf2sz)
  have hcp3 := recorderCoupled_stepsTo_other hcp2
    (by unfold isGasOp; rw [hd0'']; rfl)
    (by unfold isCreate2Op; rw [hd0'']; rfl)
    (by unfold isCallOp; rw [hd0'']; rfl) hf3step
  have hf3stk : f3.exec.stack = (0 : Word) :: (32 : Word) :: ([] : Stack Word) := rfl
  have hdret' : decode f3.exec.executionEnv.code f3.exec.pc = some (.System .RETURN, .none) := by
    change decode frv.exec.executionEnv.code
      (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33 + UInt32.ofNat 33) = _
    exact hdret
  have hf3sz : f3.exec.stack.size ≤ 1024 := by simp [hf3stk]
  have hf3active : f3.exec.activeWords = MachineState.M frv.exec.activeWords 0 32 := by
    change (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) w wms []).exec.activeWords = _
    rw [mstoreFrame_activeWords_eq]
    change MachineState.M frv.exec.activeWords (0 : UInt64) 32 = _
    rfl
  have hmemret : memoryExpansionWords? f3.exec.activeWords (0 : Word) (32 : Word)
      = some f3.exec.activeWords := by rw [hf3active]; exact memExpWords_zero32_covered _
  have hhalt := stepFrame_return_word f3 ([] : Stack Word) hdret' hf3stk hf3sz hmemret
  exact ⟨f3, _, hmrv.runs.trans (Runs.single hf1step) |>.trans (Runs.single hmsstep) |>.trans
    (Runs.single hf2step) |>.trans (Runs.single hf3step), hhalt, hcp3⟩

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
    {T : Trace} {C : CallStream} {D : CreateStream} {gS : List Word}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    -- RESHAPE (approved): `codeFits` + the reachable-frames CallsCode / CreateResolves seams,
    -- passed straight into the block walk (P3a). Supplied at `boundaryWalk_of_wl`.
    (hcodeFits : codeFits prog)
    (hcc : ∀ fr', Runs fr fr' → CallsCode fr')
    (hcr : ∀ fr', Runs fr fr' → CreateResolves fr')
    (hclosed : ClosedCFG prog)
    (hdrive : DriveCorrLog prog sloadChg log self st fr L gS cS dS)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hstmts : StmtTies' prog sloadChg log self L
      (Classical.choose (DriveCorrLog.present hdrive)))
    (hterm : TermTies' prog sloadChg log self L
      (Classical.choose (DriveCorrLog.present hdrive)))
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    DriveLogStep prog sloadChg log self st fr L T C D gS cS dS := by
  let b : Block := Classical.choose (DriveCorrLog.present hdrive)
  have hb : blockAt prog L = some b := Classical.choose_spec (DriveCorrLog.present hdrive)
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  have hstmts' : StmtTies' prog sloadChg log self L b := hstmts
  have hterm' : TermTies' prog sloadChg log self L b := hterm
  obtain ⟨st', frT, T', C', D', gS', cS', dS', hrunstmts, hrunsT, hcorrT,
    hstkT, hcleanT, hcpT, halT, hspT, haddrT, hkindT⟩ :=
    simStmts_coupled_block hwl hcodeFits hcc hcr hb (DriveCorrLog.corr hdrive)
      (DriveCorrLog.coupled hdrive) (DriveCorrLog.cleanHalts hdrive)
      (DriveCorrLog.selfPresent hdrive) (DriveCorrLog.addrPin hdrive)
      (DriveCorrLog.kindPin hdrive) hal hstmts' hprec
  cases ht : b.term with
  | stop =>
      left
      have hne := hterm'.1 ht st' frT hcorrT hcleanT hspT haddrT hkindT
      have hpcterm : frT.exec.pc = UInt32.ofNat (termOf prog L) := by
        rw [hcorrT.pc_eq, pcOf_eq_termOf prog L b hbt]
      have hdec : decode frT.exec.executionEnv.code frT.exec.pc
          = some (.System .STOP, .none) := by
        rw [hcorrT.code_eq, hpcterm]
        have hk : 0 < (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length := by
          rw [ht]; simp [emitTerm]
        have hbyte0 : (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[0]?
            = some Byte.stop := by rw [ht]; rfl
        have hd := decode_at_term_nonpush prog L b 0 Byte.stop hbt (by simpa using hk)
          hbyte0 (by simpa using hwl.wf.bound_stop L b hbt ht) (by decide)
        simpa using hd
      obtain ⟨last, haltSig, hlast, hhalt, hworld, hresult⟩ :=
        sim_term_halt_stop hcorrT ht haddrT.symm hdec (Classical.choose_spec hkindT) hne
      refine ⟨{ world := st'.world, result := .stopped }, ?_,
        @RunFrom.stop prog st st' T T' C C' D D' L b hb hrunstmts ht, ?_⟩
      · exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld, hresult⟩
      · have hhaltT := halt_stop frT hdec
          (by rw [hcorrT.stack_nil]; show (0 : ℕ) ≤ 1024; omega)
        apply runFromAll_of_runFromLeft_coupled_halt hcpT hhaltT
          halT.1 halT.2.1 halT.2.2
        exact @RunFromLeft.stop prog st st' T T' C C' D D' L b hb hrunstmts ht
  | ret t =>
      left
      obtain ⟨w, hw⟩ := hwl.defs.ret_def st st' T T' C C' D D' L b t hb ht hrunstmts
      obtain ⟨hstk, hrest⟩ := hterm'.2.1 t ht st' frT hcorrT hcleanT hspT haddrT hkindT
      obtain ⟨hgas, hret⟩ := hrest w hw
      have hdv : MatDecC prog hwl.defsCons hwl.defEnvOrdered
          frT.exec.executionEnv.code frT.exec.pc (.tmp t) := by
        rw [hcorrT.code_eq, hcorrT.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
        exact matDecC_of_term prog hwl.defsCons hwl.defEnvOrdered L b 0 (.tmp t) hbt
          (by simp only [matExpr_tmp]; rw [ht]
              exact ret_sub_value (matCache prog)
                (offsetTable (matCache prog) (defsOf prog) prog.blocks) t)
          (by
            simp only [matExpr_tmp]; rw [ht]
            show _ ≤ ((matCache prog t) ++ emitImm 0 ++ [Byte.mstore]
              ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]).length
            simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil]
            omega)
          (by
            simp only [matExpr_tmp, Nat.zero_add]
            exact hwl.wf.bound_ret L b t hbt ht)
      obtain ⟨last, haltSig, hlast, hhalt, hworld, hresult⟩ :=
        sim_term_halt_ret hcorrT ht haddrT.symm hw hwl.defsCons hwl.defEnvOrdered
          hdv hgas hstk hret
      refine ⟨{ world := st'.world, result := .returned w }, ?_,
        @RunFrom.ret prog st st' T T' C C' D D' L b t w hb hrunstmts ht hw, ?_⟩
      · exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld, hresult⟩
      · obtain ⟨last', haltSig', hlast', hhalt', hcpLast⟩ :=
          recorderCoupled_term_ret hcorrT hw hwl.defsCons hwl.defEnvOrdered hdv hgas hstk hret hcpT
        have heq : last' = last :=
          runs_halt_eq hhalt' (Runs.linear_to_halt hhalt hlast hlast')
        subst heq
        apply runFromAll_of_runFromLeft_coupled_halt hcpLast hhalt'
          halT.1 halT.2.1 halT.2.2
        exact @RunFromLeft.ret prog st st' T T' C C' D D' L b t w hb hrunstmts ht hw
  | jump dst =>
      right
      obtain ⟨⟨bdst, hbdst⟩, hdstlt, _⟩ := hclosed.jump_closed L b dst hb ht
      have hbdstT : prog.blocks.toList[dst.idx]? = some bdst := toList_of_blockAt hbdst
      obtain ⟨hbterm, hboff⟩ := hwl.wf.bound_jump L b dst hbt ht
      obtain ⟨hgpush, hgjump, hgjd⟩ := hterm'.2.2.1 dst bdst ht hbdstT hdstlt
        st' frT hcorrT hcleanT
      set off := offsetTable (matCache prog) (defsOf prog) prog.blocks dst.idx with hoff
      set dest : Word := UInt256.ofNat (off % 2 ^ 32) with hdest
      set newpc := UInt32.ofNat off with hnewpc
      have hemit : emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term
          = emitDest off ++ [Byte.jump] := by rw [ht]; rfl
      have hedlen : (emitDest off).length = 5 := by simp [emitDest, BytecodeLayer.Exec.offsetBytesBE]
      have htermlen : (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length = 6 := by
        rw [hemit, List.length_append, hedlen]; rfl
      have hdpush : decode frT.exec.executionEnv.code frT.exec.pc
          = some (.Push .PUSH4, some (dest, 4)) := by
        rw [hcorrT.code_eq, hcorrT.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
        exact term_dest_decode prog L b 0 off hbt
          (by intro j hj; rw [hemit, Nat.zero_add, List.getElem?_append_left hj])
          (by rw [htermlen, hedlen]; omega) (by omega)
      let frp := pushFrameW frT dest 4
      have hdjump : decode frp.exec.executionEnv.code frp.exec.pc
          = some (.Smsf .JUMP, .none) := by
        change decode frT.exec.executionEnv.code
          (frT.exec.pc + ((4 : UInt8) + 1).toUInt32) = _
        rw [show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide,
          hcorrT.code_eq, hcorrT.pc_eq, pcOf_eq_termOf prog L b hbt, ofNat_add']
        have hbyte : (emitTerm (matCache prog)
            (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[5]?
            = some Byte.jump := by
          rw [hemit, List.getElem?_append_right (by rw [hedlen]), hedlen]; rfl
        exact decode_at_term_nonpush prog L b 5 Byte.jump hbt (by rw [htermlen]; omega)
          hbyte hbterm (by decide)
      have hstk1 : frT.exec.stack.size + 1 ≤ 1024 := by simp [hstkT]
      have hpushStep : StepsTo frT frp :=
        Lir.CleanHaltExtract.stepsTo_pushFrameW frT .PUSH4 dest 4 (by decide) hdpush
          (by decide) (by decide)
          hgpush hstk1
      have hcpP : RecorderCoupled log frp gS' cS' dS' := by
        apply recorderCoupled_stepsTo_other hcpT
        · unfold isGasOp; rw [hdpush]; rfl
        · unfold isCreate2Op; rw [hdpush]; rfl
        · unfold isCallOp; rw [hdpush]; rfl
        · exact hpushStep
      have hdestword : dest.toUInt32? = some newpc := by
        rw [hdest, hnewpc]; exact ofNatMod_toUInt32? _
      have hgetdest : frp.get_dest dest = some newpc := by
        refine Frame.get_dest_of_mem _ hdestword ?_
        show newpc ∈ frp.validJumps
        rw [show frp.validJumps = frT.validJumps from rfl, hcorrT.validJumps_lower, hnewpc]
        simpa [hoff] using block_offset_validJump prog dst hdstlt
      have hfrpstk : frp.exec.stack = dest :: ([] : Stack Word) := by
        change dest :: frT.exec.stack = _; rw [hstkT]
      have hfrpsz : frp.exec.stack.size ≤ 1024 := by simp [hfrpstk]
      let fj := jumpFrame frp GasConstants.Gmid newpc ([] : Stack Word)
      have hjumpStep : StepsTo frp fj := stepsTo_of_next
        (stepFrame_jump frp dest newpc [] hdjump hfrpstk hfrpsz hgjump hgetdest)
      have hcpJ : RecorderCoupled log fj gS' cS' dS' := by
        apply recorderCoupled_stepsTo_other hcpP
        · unfold isGasOp; rw [hdjump]; rfl
        · unfold isCreate2Op; rw [hdjump]; rfl
        · unfold isCallOp; rw [hdjump]; rfl
        · exact hjumpStep
      have hdjd : decode fj.exec.executionEnv.code fj.exec.pc
          = some (.Smsf .JUMPDEST, .none) := by
        change decode frT.exec.executionEnv.code newpc = _
        rw [hcorrT.code_eq, hnewpc, hoff]
        exact decode_at_block_offset_jumpdest prog dst bdst hbdstT
          hboff
      have hfjstk : fj.exec.stack = [] := rfl
      have hjdStep : StepsTo fj (jumpdestFrame fj) := stepsTo_of_next
        (stepFrame_jumpdest fj hdjd (by simp [hfjstk]) (by exact hgjd))
      have hcpJD : RecorderCoupled log (jumpdestFrame fj) gS' cS' dS' := by
        apply recorderCoupled_stepsTo_other hcpJ
        · unfold isGasOp; rw [hdjd]; rfl
        · unfold isCreate2Op; rw [hdjd]; rfl
        · unfold isCallOp; rw [hdjd]; rfl
        · exact hjdStep
      have hrunTerm : Runs frT (jumpdestFrame fj) :=
        (Runs.step hpushStep (Runs.step hjumpStep (Runs.step hjdStep (Runs.refl _))))
      obtain ⟨_, hjdcorr⟩ := corr_at_jumpdest_landing (sloadChg := sloadChg) (obs := 0)
        (st := st') hbdstT
        (by rfl) (by change frT.exec.executionEnv.code = lower prog; exact hcorrT.code_eq)
        (by
          change fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          change frT.validJumps = validJumpDests frT.exec.executionEnv.code 0
          exact hcorrT.validJumps_eq)
        hfjstk (by change frT.exec.executionEnv.canModifyState = true; exact hcorrT.can_modify)
        (by intro k; change selfStorage frT k = st'.world k; exact hcorrT.storage k)
        ((defsSoundS_empty_iff prog st').mp hcorrT.defsSound) hcorrT.wellScoped
        (hcorrT.memAgree.transport rfl (le_refl _)) hdjd hgjd
      have hrunAll : Runs fr (jumpdestFrame fj) := hrunsT.trans hrunTerm
      refine ⟨st', T', C', D', dst, jumpdestFrame fj, gS', cS', dS', hrunAll,
        ?_, halT, ?_, ?_⟩
      · show DriveCorrLog prog sloadChg log self st' (jumpdestFrame fj) dst
          gS' cS' dS'
        exact { corr := hjdcorr
                cleanHalts := cleanHaltsNonException_forward hcleanT hrunTerm
                present := ⟨bdst, hbdst⟩
                selfPresent := selfPresent_runs_of_call hprec hspT hrunTerm
                addrPin := by rw [runs_address_preserved hrunTerm]; exact haddrT
                kindPin := by
                  obtain ⟨cp, hcp⟩ := hkindT
                  exact ⟨cp, by rw [runs_kind hrunTerm]; exact hcp⟩
                coupled := hcpJD }
      · exact totalGas_succ_lt (hrunsT.trans (Runs.step hpushStep
          (Runs.step hjumpStep (Runs.refl _)))) hgjd
      · constructor
        · intro O hO; exact RunFrom.jump hb hrunstmts ht hO
        · intro O hO; exact RunFromLeft.jump hb hrunstmts ht hO
  | branch cond thenL elseL =>
      right
      obtain ⟨⟨bthen, hbthen⟩, hthenlt, _⟩ :=
        (hclosed.branch_closed L b cond thenL elseL hb ht).1
      obtain ⟨⟨belse, hbelse⟩, helselt, _⟩ :=
        (hclosed.branch_closed L b cond thenL elseL hb ht).2
      have hbthenT := toList_of_blockAt hbthen
      have hbelseT := toList_of_blockAt hbelse
      obtain ⟨cw, hcw⟩ := hwl.defs.branch_def st st' T T' C C' D D' L b cond
        thenL elseL hb ht hrunstmts
      obtain ⟨frc, hmrc, hcpC, hgpushT, hgjumpi, hgjdT, hfalls,
        succ, frX, hdir, hrunEdge, hcorrX, hcpX, hlt⟩ :=
        hterm'.2.2.2 cond thenL elseL bthen belse ht hbthenT hbelseT hthenlt helselt
          st' frT cw hcorrT hcleanT gS' cS' dS' hcpT hcw
      have hrunAll := hrunsT.trans hrunEdge
      refine ⟨st', T', C', D', succ, frX, gS', cS', dS', hrunAll, ?_, halT, ?_, ?_⟩
      · exact { corr := hcorrX
                cleanHalts := cleanHaltsNonException_forward hcleanT hrunEdge
                present := by
                  rcases hdir with ⟨_, hs⟩ | ⟨_, hs⟩
                  · subst hs; exact ⟨bthen, hbthen⟩
                  · subst hs; exact ⟨belse, hbelse⟩
                selfPresent := selfPresent_runs_of_call hprec hspT hrunEdge
                addrPin := by rw [runs_address_preserved hrunEdge]; exact haddrT
                kindPin := by
                  obtain ⟨cp, hcp⟩ := hkindT
                  exact ⟨cp, by rw [runs_kind hrunEdge]; exact hcp⟩
                coupled := hcpX }
      · rw [driveCorr_measure, driveCorr_measure] at hlt ⊢
        exact lt_of_lt_of_le hlt (Runs.gasAvailable_le hrunsT)
      · constructor
        · intro O hO
          rcases hdir with ⟨hnz, hs⟩ | ⟨hz, hs⟩
          · subst hs; exact RunFrom.branchThen hb hrunstmts ht hcw hnz hO
          · subst hs; subst hz; exact RunFrom.branchElse hb hrunstmts ht hcw hO
        · intro O hO
          rcases hdir with ⟨hnz, hs⟩ | ⟨hz, hs⟩
          · subst hs; exact RunFromLeft.branchThen hb hrunstmts ht hcw hnz hO
          · subst hs; subst hz; exact RunFromLeft.branchElse hb hrunstmts ht hcw hO

/-- **Spilled def ⇒ `.slot` registration** (the `NonRecomputable → defsOf = .slot` bridge).
A gas/sload/call-result/create-result target is registered by `defsOf` (first-find,
`DefsConsistent`) as its spill slot. Consumed by R10a's plain-assign arm to derive the
target's recomputability from the `.remat` registration. REAL; no sorry. -/
private theorem defsOf_slot_of_nonRecomputable {prog : Program} (hdc : DefsConsistent prog)
    {t : Tmp} (h : Lir.NonRecomputable prog t) :
    defsOf prog t = some (.slot (slotOf t)) := by
  have mem_getElem :
      ∀ {b : Block} {s : Stmt}, b ∈ prog.blocks.toList → s ∈ b.stmts →
        ∃ (L : Label) (b' : Block) (pc : Nat), blockAt prog L = some b' ∧ b'.stmts[pc]? = some s := by
    intro b s hbmem hsmem
    obtain ⟨i, hi, hbget⟩ := List.mem_iff_getElem.mp hbmem
    obtain ⟨j, hj, hsget⟩ := List.mem_iff_getElem.mp hsmem
    refine ⟨⟨i⟩, b, j, ?_, ?_⟩
    · show prog.blocks[i]? = some b
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hbget]
    · rw [List.getElem?_eq_getElem hj, hsget]
  rcases h with hgas | hsload | hcall | hcreate
  · obtain ⟨b, hbmem, hsmem⟩ := hgas
    obtain ⟨L, b', pc, hb, hs⟩ := mem_getElem hbmem hsmem
    have := (hdc L b' pc hb).1 t .gas hs; simpa using this
  · obtain ⟨b, hbmem, k, hsmem⟩ := hsload
    obtain ⟨L, b', pc, hb, hs⟩ := mem_getElem hbmem hsmem
    have := (hdc L b' pc hb).1 t (.sload k) hs; simpa using this
  · obtain ⟨b, hbmem, cs, hsmem, hrt⟩ := hcall
    obtain ⟨L, b', pc, hb, hs⟩ := mem_getElem hbmem hsmem
    exact (hdc L b' pc hb).2.1 cs t hs hrt
  · obtain ⟨b, hbmem, cs, hsmem, hrt⟩ := hcreate
    obtain ⟨L, b', pc, hb, hs⟩ := mem_getElem hbmem hsmem
    exact (hdc L b' pc hb).2.2 cs t hs hrt

/-- **R10a — the statement ties, BUILT from the run** (the assembly obligation the
current headline lacks a producer for). For ANY `(st0, fr0, suffixes)` satisfying the
arms' antecedents — including OFF-RUN adversarial instances — the conclusions hold,
because each is (i) a static fact of `prog` derivable from `hwl` + the cursor, (ii)
carried over from the arm's own antecedents (`Corr`'s `wellScoped`/`memAgree` channels),
or (iii) computed from `fr0` and restart determinism
(the coupling forces any witness to reproduce the recorded future) — the §3 docstring's
precision note. This off-run-robustness is exactly the satisfiability analysis that
makes the §3 reshape non-vacuous. DERIVED-status obligation. -/
theorem stmtTies'_of_runWithLog {prog : Program} {params : CallParams} {log : RunLog}
    {fr₀ : Frame}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params)
    (hbegin : beginCall params = .inl fr₀) :
    ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies' prog sloadChg log params.recipient L b := by
  intro sloadChg L b hb
  set self := params.recipient with hself
  refine ⟨?arm1, ?arm2, ?arm3, ?arm4, ?arm5, ?arm6⟩
  -- ===================== arm (1): plain assign (neither gas nor sload) =====================
  case arm1 =>
    intro pc t e w st0 fr0 gS cS dS I hcur hne hns hcorr _hcp _hch hv
    -- `defsOf t = .remat e` (DefsConsistent, pure branch), so not a spill slot.
    have hdef : defsOf prog t = some (Lir.locOfExpr e) := by
      have := (hwl.defsCons L b pc hb).1 t e hcur
      cases e <;> first | (exact absurd rfl hne) | (exact absurd rfl (hns _)) | simpa using this
    have hslot : ∀ n, defsOf prog t ≠ some (.slot n) := by
      intro n hn; rw [hdef] at hn; simp [Lir.locOfExpr] at hn
    have hrem : rematOf prog t = some e := by
      unfold rematOf; rw [hdef]; rfl
    have hstepS : StepScopedS prog (.assign t e) :=
      ⟨fun _ _ => hrem, fun h => absurd h hne, fun k h => absurd h (hns k)⟩
    -- `t` is recomputable: were it `NonRecomputable`, `defsOf t = .slot`, contradiction.
    have hnr : ¬ Lir.NonRecomputable prog t := by
      intro hcontra
      have := defsOf_slot_of_nonRecomputable hwl.defsCons hcontra
      exact hslot _ this
    have hscoped' : ∀ t', (st0.setLocal t w).locals t' ≠ none →
        (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
        ∧ defsOf prog t' ≠ none := by
      intro t' ht'
      by_cases heq : t' = t
      · subst t'
        exact ⟨Or.inl hnr, by rw [hdef]; simp⟩
      · have hl' : st0.locals t' ≠ none := by
          simpa [IRState.setLocal, if_neg heq] using ht'
        exact hcorr.wellScoped t' hl'
    have hmem' : Lir.MemRealises prog (st0.setLocal t w) fr0 := by
      intro tw slot v hslotdef hlocals
      by_cases heq : tw = t
      · subst tw; exact absurd hslotdef (hslot slot)
      · have hl' : st0.locals tw = some v := by
          simpa [IRState.setLocal, if_neg heq] using hlocals
        exact hcorr.memAgree tw slot v hslotdef hl'
    exact ⟨hslot, hstepS, hscoped', hmem'⟩
  -- ===================== arm (2): spilled sload assign =====================
  case arm2 =>
    intro pc t k kv st0 fr0 gS cS dS I hcur hcorr _hcp _hch hkey
    have hslotdef : defsOf prog t = some (.slot (slotOf t)) := by
      have := (hwl.defsCons L b pc hb).1 t (.sload k) hcur; simpa using this
    have hisSload : Lir.isSloadDef prog t :=
      ⟨b, List.mem_of_getElem? (Lir.toList_of_blockAt hb), k, List.mem_of_getElem? hcur⟩
    have hstepS : StepScopedS prog (.assign t (.sload k)) :=
      ⟨fun _ h2 => absurd rfl (h2 k), fun h => Expr.noConfusion h, fun _ _ => hisSload⟩
    have hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw :=
      hwl.wf.slots_slot
    have hwval : evalExpr st0 0 (.sload k) = some (st0.world kv) := by
      simp [evalExpr, hkey]
    have hscoped' : ∀ t', (st0.setLocal t (st0.world kv)).locals t' ≠ none →
        (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
        ∧ defsOf prog t' ≠ none := by
      intro t' ht'
      by_cases heq : t' = t
      · subst t'
        exact ⟨Or.inr ⟨slotOf t, hslotdef⟩, by rw [hslotdef]; simp⟩
      · have hl' : st0.locals t' ≠ none := by
          simpa [IRState.setLocal, if_neg heq] using ht'
        exact hcorr.wellScoped t' hl'
    obtain ⟨hslot63, hslotplat⟩ :=
      hwl.slotAddr L b pc t hb (Or.inr (Or.inl ⟨k, hcur⟩))
    have hstkKey : fr0.exec.stack.size + (chargeCache prog sloadChg k).length ≤ 1024 := by
      rw [hcorr.stack_nil]; simpa using hwl.stack.sloadKey sloadChg L b pc t k hb hcur
    -- arm 2 — the sload-key activeWords-flatness `hawk`: the conclusion
    -- `frk.activeWords = fr0.activeWords` is exactly the `MatRunsC.activeWordsEq` field. The
    -- materialise value channel only ever runs PUSH / covered-MLOAD readback / ADD / LT frames —
    -- none grow `activeWords` — so every `MatRunsC` construction pins activeWords EQUALITY (the
    -- MSTORE spill that *would* grow it lives in the StashTail post-run, not in `MatRunsC` itself).
    have hflat : ∀ frk : Frame,
        MatRunsC prog sloadChg (.tmp k) kv fr0 frk →
        frk.exec.toMachineState.activeWords = fr0.exec.toMachineState.activeWords :=
      fun _frk hmrk => hmrk.activeWordsEq
    exact ⟨hslotdef, hstepS, hslots, hwval, hscoped', hslot63, hslotplat, hstkKey, hflat⟩
  -- ===================== arm (3): spilled gas assign (R1 conjunct) =====================
  case arm3 =>
    intro pc t st0 fr0 gS cS dS I hcur hcorr hcp hch
    have hslotdef : defsOf prog t = some (.slot (slotOf t)) := by
      have := (hwl.defsCons L b pc hb).1 t .gas hcur; simpa using this
    have hisGas : Lir.isGasDef prog t :=
      ⟨b, List.mem_of_getElem? (Lir.toList_of_blockAt hb), List.mem_of_getElem? hcur⟩
    have hstepS : StepScopedS prog (.assign t .gas) :=
      ⟨fun h => absurd rfl h, fun _ => hisGas, fun _ h => Expr.noConfusion h⟩
    have hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw :=
      hwl.wf.slots_slot
    obtain ⟨hslot63, hslotplat⟩ :=
      hwl.slotAddr L b pc t hb (Or.inl hcur)
    have hpcbound : pcOf prog L pc + 34 < 2 ^ 32 := hwl.gasBound L b pc t hb hcur
    have hghead : gS.head? = some (UInt256.ofUInt64
        (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)) :=
      gas_suffix_head_realised hb hcur hslotdef hpcbound hcorr hcp hch
    have hscoped' : ∀ t', (st0.setLocal t (UInt256.ofUInt64
            (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))).locals t' ≠ none →
          (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
          ∧ defsOf prog t' ≠ none := by
      intro t' ht'
      by_cases heq : t' = t
      · subst t'
        exact ⟨Or.inr ⟨slotOf t, hslotdef⟩, by rw [hslotdef]; simp⟩
      · have hl' : st0.locals t' ≠ none := by
          simpa [IRState.setLocal, if_neg heq] using ht'
        exact hcorr.wellScoped t' hl'
    exact ⟨hslotdef, hstepS, hslots, hghead, hscoped', hslot63, hslotplat, hpcbound⟩
  -- ===================== arm (4): sstore =====================
  case arm4 =>
    intro pc key value kw vw st0 fr0 gS cS dS I hcur _hcorr _hcp _hch _hkw _hvw
    have hstepS : StepScopedS prog (.sstore key value) := by
      intro t₀ e₀ hd₀ k he
      subst he
      have : defsOf prog t₀ = some (.remat (.sload k)) := by
        unfold rematOf at hd₀; cases hh : defsOf prog t₀ with
        | none => rw [hh] at hd₀; simp at hd₀
        | some loc =>
          cases loc with
          | slot n => rw [hh] at hd₀; simp at hd₀
          | remat e' => rw [hh] at hd₀; simp at hd₀; rw [hd₀]
      exact Lir.defsOf_ne_sload prog t₀ k this
    have hstk : (chargeCache prog sloadChg value).length
        + (chargeCache prog sloadChg key).length + 1 ≤ 1024 := by
      simpa using hwl.stack.sstore sloadChg L b pc key value hb hcur
    exact ⟨hstepS, hstk⟩
  -- ===================== arm (5): call =====================
  case arm5 =>
    intro pc cs st0 st0' fr0 cw gw gS rec cS' dS I hcur hcp hch haddr
      hcodeFits hcc hcallee hgasfwd hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
      hslotaddr hst0'
    subst hst0'
    exact callRealises_of_recorded hwl hcodeFits hb hcur hcp hch haddr hcc hcallee hgasfwd
      hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd hslotaddr
  -- ===================== arm (6): create =====================
  case arm6 =>
    intro pc cs st0 st0' fr0 valueW initOffW initSizeW saltW gS cS rec dS' I hcur hcp
      hch haddr hcodeFits hcr hvalue hoff hsize hsalt hfreeValue hfreeOff hfreeSize
      hfreeSalt hstkSalt hstkSize hstkOff hstkValue hslotaddr hst0'
    subst hst0'
    exact createRealises_of_recorded hwl hcodeFits hb hcur hcp hch haddr hcr hvalue hoff
      hsize hsalt hfreeValue hfreeOff hfreeSize hfreeSalt hstkSalt hstkSize hstkOff
      hstkValue hslotaddr

/-- **R10b — the terminator ties, BUILT** (the `runWithLog`-context restatement of R5;
kept separate so the R11 assembly consumes one hypothesis shape per tie). -/
theorem termTies'_of_runWithLog {prog : Program} {params : CallParams} {log : RunLog}
    (hwl : WellLowered prog)
    (hseams : PrecompileAssumptions prog params) :
    ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block), blockAt prog L = some b →
      TermTies' prog sloadChg log params.recipient L b := by
  intro sloadChg L b hb
  exact termTies'_of_walk hwl hseams.noErase
    (fun t hterm => hwl.retEpilogueBound L b t hb hterm) hb

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
        (D : CreateStream) (gS : List Word) (cS : List CallRecord)
        (dS : List CreateRecord),
      (∀ fr', Runs fr fr' → CallsCode fr') →
      (∀ fr', Runs fr fr' → CreateResolves fr') →
      DriveCorrLog prog sloadChg log self st fr L gS cS dS →
      StreamsAligned self log gS cS dS T C D →
      DriveLogStep prog sloadChg log self st fr L T C D gS cS dS) :
    ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream)
      (gS : List Word) (cS : List CallRecord) (dS : List CreateRecord),
      (∀ fr', Runs fr fr' → CallsCode fr') →
      (∀ fr', Runs fr fr' → CreateResolves fr') →
      DriveCorrLog prog sloadChg log self st fr L gS cS dS →
      StreamsAligned self log gS cS dS T C D →
      RunFromCoupled prog self st fr L T C D := by
  -- strong induction on the bytecode `totalGas` measure of the boundary frame, generalising over
  -- all the boundary data so the IH applies at the strictly-smaller successor.
  intro st fr L T C D gS cS dS hcc hcr hdrive hal
  induction hmeasure : totalGas [] (.inl fr) using Nat.strong_induction_on
    generalizing st fr L T C D gS cS dS with
  | _ n ih =>
    subst hmeasure
    rcases hstep st fr L T C D gS cS dS hcc hcr hdrive hal with
      hrun | ⟨st', T', C', D', succ, fr', gS', cS', dS', hruns, hdrive', hal', hlt,
        hcont, hcontAll⟩
    · -- halt disjunct: the block bottoms out; `RunFromCoupled` is delivered directly.
      exact hrun
    · -- edge disjunct: recurse at the strictly-smaller successor, then prepend the block.
      -- the seams transport across the edge `Runs fr fr'`: anything reachable from `fr'` is
      -- reachable from `fr`, so `hcc`/`hcr` at `fr` re-supply the successor's seams.
      have hcc' : ∀ fr'', Runs fr' fr'' → CallsCode fr'' := fun fr'' hr => hcc fr'' (hruns.trans hr)
      have hcr' : ∀ fr'', Runs fr' fr'' → CreateResolves fr'' := fun fr'' hr => hcr fr'' (hruns.trans hr)
      obtain ⟨O, ⟨last, haltSig, hlast, hhalt, hworld, hresult⟩, hir, hirAll⟩ :=
        ih (totalGas [] (.inl fr')) hlt st' fr' succ T' C' D' gS' cS' dS' hcc' hcr' hdrive' hal' rfl
      -- the successor's bytecode halt terminal lifts back to `fr` across the edge `Runs fr fr'`.
      exact ⟨O, ⟨last, haltSig, hruns.trans hlast, hhalt, hworld, hresult⟩,
        hcont O hir, hcontAll O hirAll⟩

/-- **P5 — the R6 boundary walk (`hrb`), reason (b).** Every `Runs fr₀`-reachable frame sits at
a reachable instruction boundary. This helper derives the nonempty-program precondition from
`hwl.closed.entry_present` / `hwl.entry0`; the byte-size seam remains explicit because
`WellLowered` is only an internal adapter and does not carry whole-program byte length. -/
theorem boundaryWalk_of_wl {prog : Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hwl : WellLowered prog)
    (hsize : (Lir.lowerBytes prog).length ≤ 2 ^ 32) :
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
(the honest R4 residual — `CreateResolves` is NOT structural, `Decode/Modellable.lean:413`).
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
    (hsize : (Lir.lowerBytes prog).length ≤ 2 ^ 32) :
    ∃ O : Observable,
      (∀ fr', Runs fr₀ fr' → CreateResolves fr')
      ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
          ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
          ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
      ∧ RunFrom prog (entryState params) (realisedGas log)
          (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ RunFromAll prog (entryState params) (realisedGas log)
          (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O := by
  let sloadChg : Tmp → ℕ := fun _ => 0
  have hcc₀ : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  have hcr₀ : ∀ fr', Runs fr₀ fr' → CreateResolves fr' :=
    createResolves_reachable hbegin hseams
  have hne : ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt →
      HaltNonException halt :=
    haltNonException_of_cleanLog (prog := prog) hrun hbegin hclean hcr₀ hcc₀
  obtain ⟨fr₀', hentryRun, hentry⟩ :=
    driveCorrLog_entry (prog := prog) (sloadChg := sloadChg) (params := params)
      (log := log) (acc := acc) (fr₀ := fr₀)
      hcode hmod hself hgas hwl hrun hclean hseams hbegin hne
  have hcc₀' : ∀ fr', Runs fr₀' fr' → CallsCode fr' :=
    fun fr' hr => hcc₀ fr' (hentryRun.trans hr)
  have hcr₀' : ∀ fr', Runs fr₀' fr' → CreateResolves fr' :=
    fun fr' hr => hcr₀ fr' (hentryRun.trans hr)
  have hal := streamsAligned_entry params.recipient log
  have hstep : ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace)
      (C : CallStream) (D : CreateStream) (gS : List Word)
      (cS : List CallRecord) (dS : List CreateRecord),
      (∀ fr', Runs fr fr' → CallsCode fr') →
      (∀ fr', Runs fr fr' → CreateResolves fr') →
      DriveCorrLog prog sloadChg log params.recipient st fr L gS cS dS →
      StreamsAligned params.recipient log gS cS dS T C D →
      DriveLogStep prog sloadChg log params.recipient st fr L T C D gS cS dS := by
    intro st fr L T C D gS cS dS hcc hcr hdrive haligned
    let b : Block := Classical.choose (DriveCorrLog.present hdrive)
    have hb : blockAt prog L = some b := Classical.choose_spec (DriveCorrLog.present hdrive)
    have hstmts : StmtTies' prog sloadChg log params.recipient L b :=
      stmtTies'_of_runWithLog hcode hmod hwl hrun hclean hseams hbegin sloadChg L b hb
    have hterm : TermTies' prog sloadChg log params.recipient L b :=
      termTies'_of_runWithLog hwl hseams sloadChg L b hb
    exact driveLogStep_of_block hwl hcodeFits hcc hcr hwl.closed hdrive haligned
      hstmts hterm hseams.noErase
  obtain ⟨O, ⟨last, haltSig, hlast, hhalt, hworld, hresult⟩, hrunFrom, hrunAll⟩ :=
    runFrom_of_driveCorrLog_rec hcodeFits hstep
      (entryState params) fr₀' prog.entry (realisedGas log)
      (realisedCall log params.recipient) (realisedCreate log params.recipient)
      log.gas log.calls log.creates hcc₀' hcr₀' hentry hal
  exact ⟨O, hcr₀, ⟨last, haltSig, hentryRun.trans hlast, hhalt, hworld, hresult⟩,
    hrunFrom, hrunAll⟩

end Lir
