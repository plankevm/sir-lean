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
    (L : Label) (pc : Nat) (st : IRState) (fr : Frame)
    (T : Trace) (C : CallStream) (D : CreateStream) (s : Stmt) : Prop :=
  ∃ (st' : IRState) (fr' : Frame) (T' : Trace) (C' : CallStream) (D' : CreateStream)
    (gS' : List Word) (sS' : List Nat) (cS' : List CallRecord) (dS' : List CreateRecord),
    EvalStmt prog st T C D s st' T' C' D'
    ∧ Runs fr fr'
    ∧ Lir.Corr prog sloadChg 0 (fun _ => False) st' fr' L (pc + 1)
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
    (hcorr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hv : evalExpr st 0 e = some w)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.assign t e) := by
  -- Fire `StmtTies'` arm (1) at this cursor with the coupling + clean-halt in hand.
  obtain ⟨hslot, hstepS, hscoped', hmem'⟩ :=
    hties.1 pc t e w st fr gS sS cS dS hcur hne hns hcorr hcp hch hv
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
  -- The post-state's strong `DefsSound` (self-repair; no live-scope clause).
  have hsound' : DefsSound prog (st.setLocal t w) :=
    defsSound_setLocal_recomputable hnr hdef hv ((defsSoundS_empty_iff prog st).mp hcorr.defsSound)
  -- Package: `st' = st.setLocal t w`, `fr' = fr`, streams/suffixes UNCHANGED.
  refine ⟨st.setLocal t w, fr, T, C, D, gS, sS, cS, dS,
    EvalStmt.assignPure (prog := prog) (T := T) (C := C) (D := D) hne hv,
    Runs.refl fr, ?_, hcorr.stack_nil, hcp, hal⟩
  exact
    { pc_eq := by rw [hpc]; exact hcorr.pc_eq
      code_eq := hcorr.code_eq
      validJumps_eq := hcorr.validJumps_eq
      stack_nil := hcorr.stack_nil
      can_modify := hcorr.can_modify
      storage := hcorr.storage
      defsSound := (defsSoundS_empty_iff prog (st.setLocal t w)).mpr hsound'
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
    (hcorr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
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
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t (.sload k)))
    (hcorr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hkey : st.locals k = some kv)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.assign t (.sload k)) := by
  sorry

/-! ### S1 — the coupling fold over a `materialise` run (`recorderCoupled_matRunsC`)

The missing Runs-level fold (Block-#1 plan §S1): running `matExpr (matCache prog) e` for a
non-`gas`/non-`sload` `e` emits ONLY `PUSH32`/`MLOAD`/`ADD`/`LT` frames (a bare `.gas`/`.sload`
is never materialised — Phase B/C), each of which is a non-recording top-level `.next` step
(`isGasOp = false`, `isSloadOp = false` from the `MatDecC` decode). So the recorder coupling
`RecorderCoupled log fr gS sS cS` rides UNCHANGED across the whole run. Proved as a JOINT
recursion mirroring `materialise_runsC` field-for-field (so the endpoint frame carries BOTH
the `MatRunsC` bundle the SSTORE `Corr`-work consumes AND the coupling), inserting one
`recorderCoupled_step_other` (R7d) per emitted opcode frame. REAL; no sorry. -/

open GasConstants in
/-- **S1 — `recorderCoupled_matRunsC`.** The joint `materialise_runsC` + coupling fold. Same
premises + conclusion as `materialise_runsC`, plus: it CARRIES the recorder coupling
`RecorderCoupled log fr gS sS cS` across the whole run to the endpoint. Every materialise frame
decodes to `PUSH32`/`MLOAD`/`ADD`/`LT` (never `GAS`/`SLOAD`), so each step is non-recording
(`recorderCoupled_step_other`, R7d). Mirror of the green `materialise_runsC` recursion (the
`matDecMeasure` strong descent — fuel-free; the `.tmp` arm resolves through `allocate prog t`
via `matCache_unfold`). -/
theorem recorderCoupled_matRunsC {prog : Program} (hdc : DefsConsistent prog)
    (hord : DefEnvOrdered prog) (sloadChg : Tmp → ℕ) (st : IRState) (obs : Word)
    (log : RunLog) (gS : List Word) (sS : List Nat) (cS : List CallRecord)
    (dS : List CreateRecord)
    (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSound prog st)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hstore : StorageAgree st fr)
    (hne : e ≠ .gas)
    (hnsl : ∀ k, e ≠ .sload k)
    (hmemreal : MemRealises prog st fr)
    (heval : evalExpr st obs e = some w)
    (hgas : (chargeExpr sloadChg (chargeCache prog sloadChg) e).sum ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + (chargeExpr sloadChg (chargeCache prog sloadChg) e).length ≤ 1024)
    (hcp : RecorderCoupled log fr gS sS cS dS) :
    ∃ fr', MatRunsC prog sloadChg e w fr fr' ∧ RecorderCoupled log fr' gS sS cS dS := by
  match e, hdec, hne, hnsl, heval, hgas, hstk with
  | .imm v, hdec, _, _, heval, hgas, hstk =>
      have hdec' : decode fr.exec.executionEnv.code fr.exec.pc
          = some (.Push .PUSH32, some (v, 32)) := by rw [matDecC_imm] at hdec; exact hdec
      have hvw : v = w := Option.some.inj heval
      subst hvw
      have hg3 : 3 ≤ fr.exec.gasAvailable.toNat := by
        simp only [chargeExpr_imm, List.sum_cons, List.sum_nil] at hgas
        simpa [show (Gverylow : ℕ) = 3 from rfl] using hgas
      have hstk1 : fr.exec.stack.size + 1 ≤ 1024 := by
        simp only [chargeExpr_imm, List.length_cons, List.length_nil] at hstk; omega
      refine ⟨pushFrameW fr v 32,
        { runs := (sim_imm fr v hdec' hg3 hstk1).1
          stack := (sim_imm fr v hdec' hg3 hstk1).2
          code := rfl, validJumps := rfl, addr := rfl, canMod := rfl
          accounts := rfl, storage := fun _ => rfl
          pc := ?_, gasCharge := ?_, gasToNat := ?_
          memBytes := rfl, memActive := le_refl _ }, ?_⟩
      · rw [pushFrameW_pc, push32_pcΔ]; simp [matExpr_imm, emitImm_length]
      · rw [chargeExpr_imm]
        show (fr.exec.gasAvailable - UInt64.ofNat Gverylow)
          = subCharges fr.exec.gasAvailable [Gverylow]
        rw [subCharges_singleton]
      · rw [chargeExpr_imm]
        show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
        have h3 : (3 : ℕ) ≤ fr.exec.gasAvailable.toNat := hg3
        rw [show (Gverylow : ℕ) = 3 from rfl,
            BytecodeLayer.UInt64.toNat_sub_ofNat _ 3 h3 (by omega)]
        simp [List.sum_cons]
      · -- coupling across the PUSH32 step (non-recording).
        exact recorderCoupled_step_other hcp
          (by unfold isGasOp; rw [hdec']; rfl) (by unfold isSloadOp; rw [hdec']; rfl)
          (stepFrame_push fr .PUSH32 v 32 (by decide) hdec' (by decide) (by decide) hg3 hstk1)
      | .gas, _, hne, _, _, _, _ => exact absurd rfl hne
  | .sload k, _, _, hnsl, _, _, _ => exact absurd rfl (hnsl k)
  | .tmp t, hdec, _, _, heval, hgas, hstk =>
      have hloc : st.locals t = some w := heval
      cases hal : allocate prog t with
      | none =>
          exact absurd (show defsOf prog t = none from hal)
            (hscoped t (by rw [hloc]; simp)).2
      | some loc =>
          cases loc with
          | remat e' =>
              -- == the pure recompute path (DefsSound) ==
              have hmc : matCache prog t = matExpr (matCache prog) e' :=
                matCache_remat prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              have hcc : chargeCache prog sloadChg t
                  = chargeExpr sloadChg (chargeCache prog sloadChg) e' :=
                chargeCache_remat prog sloadChg hdc hord (mem_defEnv_of_allocate prog hdc hal)
              obtain ⟨hremt, he'ng, he'nsl⟩ := defsOf_of_allocate_remat prog hal
              have htmd : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e' := by
                rw [matDecC_tmp_remat prog hdc hord fr.exec.executionEnv.code fr.exec.pc t e' hal]
                  at hdec
                exact hdec
              have hnr : ¬ NonRecomputable prog t := by
                rcases (hscoped t (by rw [hloc]; simp)).1 with hnr | ⟨s, hcrdef⟩
                · exact hnr
                · exfalso
                  have hdeft : defsOf prog t = some (Loc.remat e') := hal
                  rw [hdeft] at hcrdef
                  exact absurd hcrdef (by simp)
              have hdfs : some w = evalExpr st 0 e' :=
                hsound t e' w hremt hnr hloc
              have heval' : evalExpr st obs e' = some w := by
                rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
              have hgas' : (chargeExpr sloadChg (chargeCache prog sloadChg) e').sum
                  ≤ fr.exec.gasAvailable.toNat := by
                have hx := hgas; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              have hstk' : fr.exec.stack.size
                  + (chargeExpr sloadChg (chargeCache prog sloadChg) e').length ≤ 1024 := by
                have hx := hstk; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              obtain ⟨fr', hmr, hcp'⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
                log gS sS cS dS e' w fr htmd hsound hscoped hstore he'ng he'nsl hmemreal heval'
                hgas' hstk' hcp
              have hpcE : matExpr (matCache prog) (Expr.tmp t) = matExpr (matCache prog) e' := by
                simp only [matExpr_tmp]; exact hmc
              have hchgE : chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)
                  = chargeExpr sloadChg (chargeCache prog sloadChg) e' := by
                simp only [chargeExpr_tmp]; exact hcc
              exact ⟨fr',
                { runs := hmr.runs, stack := hmr.stack, code := hmr.code
                  validJumps := hmr.validJumps, addr := hmr.addr, canMod := hmr.canMod
                  accounts := hmr.accounts, storage := hmr.storage
                  pc := by rw [hpcE]; exact hmr.pc
                  gasCharge := by rw [hchgE]; exact hmr.gasCharge
                  gasToNat := by rw [hchgE]; exact hmr.gasToNat
                  memBytes := hmr.memBytes, memActive := hmr.memActive }, hcp'⟩
          | slot n =>
              -- == the memory value-channel readback arm (PUSH n ; MLOAD) ==
              have hdeft : defsOf prog t = some (.slot n) := defsOf_of_allocate_slot prog hal
              have hmd := hdec
              rw [matDecC_tmp_slot prog hdc hord fr.exec.executionEnv.code fr.exec.pc t n hal]
                at hmd
              obtain ⟨hdpush, hdmload⟩ := hmd
              have hmexp : matExpr (matCache prog) (Expr.tmp t)
                  = emitImm (UInt256.ofNat n) ++ [Byte.mload] := by
                simp only [matExpr_tmp]
                exact matCache_slot prog hdc hord (mem_defEnv_of_allocate prog hdc hal)
              have hchg : chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)
                  = [Gverylow, Gverylow] := by
                simp only [chargeExpr_tmp]
                exact chargeCache_slot prog sloadChg hdc hord (mem_defEnv_of_allocate prog hdc hal)
              obtain ⟨hcm, ham, hreal, hval⟩ := hmemreal t n w hdeft hloc
              have hsum2 : (chargeExpr sloadChg (chargeCache prog sloadChg) (Expr.tmp t)).sum
                  = Gverylow + Gverylow := by rw [hchg]; simp [List.sum_cons]
              have hgv3 : (Gverylow : ℕ) = 3 := rfl
              have hgasPush : 3 ≤ fr.exec.gasAvailable.toNat := by rw [hsum2, hgv3] at hgas; omega
              have hszfr : fr.exec.stack.size + 1 ≤ 1024 := by
                rw [hchg] at hstk; simp only [List.length_cons, List.length_nil] at hstk; omega
              -- step 1: PUSH32 n
              obtain ⟨hpushrun, hpushstk⟩ := sim_imm fr (UInt256.ofNat n) hdpush hgasPush hszfr
              set frp := pushFrameW fr (UInt256.ofNat n) 32 with hfrp
              have hfrpcode : frp.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
              have hfrpmem : frp.exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl
              have hfrpaw : frp.exec.toMachineState.activeWords
                  = fr.exec.toMachineState.activeWords := rfl
              have hfrppc : frp.exec.pc = fr.exec.pc + UInt32.ofNat 33 := by
                rw [hfrp, pushFrameW_pc, push32_pcΔ]
              have hfrpstk : frp.exec.stack = (UInt256.ofNat n) :: fr.exec.stack := by
                rw [hpushstk]; rfl
              have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; simp; omega
              -- coupling across the PUSH32 step (non-recording).
              have hcpp : RecorderCoupled log frp gS sS cS dS := by
                rw [hfrp]
                exact recorderCoupled_step_other hcp
                  (by unfold isGasOp; rw [hdpush]; rfl) (by unfold isSloadOp; rw [hdpush]; rfl)
                  (stepFrame_push fr .PUSH32 (UInt256.ofNat n) 32 (by decide) hdpush
                    (by decide) (by decide) hgasPush hszfr)
              -- step 2: MLOAD at `n` (covered ⇒ zero memory expansion)
              have hreal' : (UInt256.ofNat n).toNat + 63 < 2 ^ 64 := by
                rw [show (UInt256.ofNat n).toNat = n from by
                  rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
                exact hreal
              have hMeq : MachineState.M frp.exec.toMachineState.activeWords
                  (UInt256.ofNat n).toUInt64 32 = frp.exec.toMachineState.activeWords := by
                rw [hfrpaw]; exact M_32_eq_self_of_covered _ _ ham hreal'
              have hnoexp : memoryExpansionWords? frp.exec.activeWords (UInt256.ofNat n) 32
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
                have hemitlen : (emitImm (UInt256.ofNat n)).length = 33 := emitImm_length _
                rw [show fr.exec.pc + UInt32.ofNat 33
                      = fr.exec.pc + UInt32.ofNat (emitImm (UInt256.ofNat n)).length from by
                      rw [hemitlen]]
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
                rw [hzcost, BytecodeLayer.UInt64.toNat_sub_ofNat frp.exec.gasAvailable 0
                      (Nat.zero_le _) (by norm_num), Nat.sub_zero, hfrpgasN, hgv3]
                rw [hsum2, hgv3] at hgas; omega
              obtain ⟨hmloadrun, hmloadhd⟩ :=
                sim_mload frp (UInt256.ofNat n) frp.exec.activeWords fr.exec.stack
                  hmloaddec hfrpstk hfrpsz hnoexp hgMem hgMl
              set frm := mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords fr.exec.stack
                with hfrm
              -- coupling across the MLOAD step (non-recording).
              have hcpm : RecorderCoupled log frm gS sS cS dS := by
                rw [hfrm]
                exact recorderCoupled_step_other hcpp
                  (by unfold isGasOp; rw [hmloaddec]; rfl)
                  (by unfold isSloadOp; rw [hmloaddec]; rfl)
                  (stepFrame_mload frp (UInt256.ofNat n) frp.exec.activeWords fr.exec.stack
                    hmloaddec hfrpstk hfrpsz hnoexp hgMem hgMl)
              have hmval : ((BytecodeLayer.Dispatch.memChargedState frp.exec
                  frp.exec.activeWords).toMachineState.mload (UInt256.ofNat n)).1 = w := by
                rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat n)
                      (show (BytecodeLayer.Dispatch.memChargedState frp.exec
                          frp.exec.activeWords).toMachineState.memory
                        = fr.exec.toMachineState.memory from by rw [← hfrpmem]; rfl)
                      (show (BytecodeLayer.Dispatch.memChargedState frp.exec
                          frp.exec.activeWords).toMachineState.activeWords
                        = fr.exec.toMachineState.activeWords from by rw [← hfrpaw]; rfl)]
                exact hval
              have hfrmstk : frm.exec.stack = fr.exec.stack.push w := by
                show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.stack = _
                rw [← hmval]; rfl
              have hfrmmem : frm.exec.toMachineState.memory = fr.exec.toMachineState.memory := by
                show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.toMachineState.memory = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.toMachineState.memory
                    = frp.exec.toMachineState.memory from rfl, hfrpmem]
              have hfrmaw : frm.exec.toMachineState.activeWords
                  = fr.exec.toMachineState.activeWords := by
                show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.toMachineState.activeWords = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.toMachineState.activeWords
                    = MachineState.M frp.exec.toMachineState.activeWords
                        (UInt256.ofNat n).toUInt64 32 from rfl, hMeq, hfrpaw]
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
                  code := ?_, validJumps := ?_, addr := ?_, canMod := ?_, accounts := ?_
                  storage := ?_, pc := ?_, gasCharge := ?_, gasToNat := ?_
                  memBytes := hfrmmem
                  memActive := by rw [hfrmaw] }
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.executionEnv.code = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.executionEnv.code = frp.exec.executionEnv.code from rfl,
                    hfrpcode]
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).validJumps = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.executionEnv.address = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.executionEnv.canModifyState = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.accounts = _
                rfl
              · intro k
                show selfStorage (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack) k = _
                rfl
              · show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                  fr.exec.stack).exec.pc = _
                rw [show (mloadFrame frp (UInt256.ofNat n) frp.exec.activeWords
                      fr.exec.stack).exec.pc = frp.exec.pc + 1 from rfl, hfrppc, hmexp]
                rw [List.length_append, emitImm_length,
                    show ([Byte.mload] : List UInt8).length = 1 from rfl,
                    show (33 : ℕ) + 1 = 34 from rfl,
                    show (UInt32.ofNat 34) = UInt32.ofNat 33 + 1 from by decide]
                ac_rfl
              · rw [hchg]
                show frm.exec.gasAvailable = subCharges fr.exec.gasAvailable [Gverylow, Gverylow]
                rw [hfrmgas]
                show (fr.exec.gasAvailable - UInt64.ofNat Gverylow) - UInt64.ofNat Gverylow
                  = subCharges fr.exec.gasAvailable [Gverylow, Gverylow]
                rfl
              · rw [hsum2, hfrmgas]
                have h2 : (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat
                    = fr.exec.gasAvailable.toNat - Gverylow :=
                  BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow
                    (by rw [hgv3]; omega) (by rw [hgv3]; omega)
                rw [BytecodeLayer.UInt64.toNat_sub_ofNat _ Gverylow
                      (by rw [h2, hgv3]; omega) (by rw [hgv3]; omega), h2]
                rw [hsum2, hgv3] at hgas; omega
  | .add a b, hdec, _, _, heval, hgas, hstk =>
      obtain ⟨va, hla, vb, hlb, hwadd⟩ :
          ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb ∧ w = UInt256.add va vb := by
        simp only [evalExpr] at heval
        cases hla : st.locals a with
        | none => simp [hla] at heval
        | some va =>
            cases hlb : st.locals b with
            | none => simp [hla, hlb] at heval
            | some vb => refine ⟨va, rfl, vb, rfl, ?_⟩; simp [hla, hlb] at heval; exact heval.symm
      subst hwadd
      rw [matDecC_add] at hdec
      obtain ⟨hdb, hda, hop⟩ := hdec
      have hcadd := chargeExpr_add sloadChg (chargeCache prog sloadChg) a b
      have hevb : evalExpr st obs (.tmp b) = some vb := hlb
      have heva : evalExpr st obs (.tmp a) = some va := hla
      have hgasb : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).sum
          ≤ fr.exec.gasAvailable.toNat := by
        have hx := hgas; rw [hcadd] at hx
        simp only [List.sum_append] at hx
        show (chargeCache prog sloadChg b).sum ≤ _; omega
      have hstkb : fr.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).length ≤ 1024 := by
        have hx := hstk; rw [hcadd] at hx
        simp only [List.length_append] at hx
        show fr.exec.stack.size + (chargeCache prog sloadChg b).length ≤ 1024; omega
      obtain ⟨frb, hmrb, hcpb⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
        log gS sS cS dS (.tmp b) vb fr hdb hsound hscoped hstore (by nofun) (by nofun)
        hmemreal hevb hgasb hstkb hcp
      have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
      have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog b).length := by
        have := hmrb.pc; simpa only [matExpr_tmp] using this
      have hda' : MatDecC prog hdc hord frb.exec.executionEnv.code frb.exec.pc (.tmp a) := by
        rw [hbcode, hbpc]; exact hda
      have hsum_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)).sum
          = (chargeCache prog sloadChg b).sum + (chargeCache prog sloadChg a).sum + Gverylow := by
        rw [hcadd]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
      have hlen_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)).length
          = (chargeCache prog sloadChg b).length + (chargeCache prog sloadChg a).length + 1 := by
        rw [hcadd]; simp only [List.length_append, List.length_singleton]
      have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
        rw [hmrb.stack]; simp [Stack.push]
      have hgasa : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).sum
          ≤ frb.exec.gasAvailable.toNat := by
        rw [hmrb.gasToNat]; show (chargeCache prog sloadChg a).sum ≤ _
        rw [hsum_split] at hgas; simp only [chargeExpr_tmp] at hgas ⊢; omega
      have hstka : frb.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).length ≤ 1024 := by
        have hpb1 : 1 ≤ (chargeCache prog sloadChg b).length := chargeCache_length_pos prog sloadChg b
        rw [hlen_split] at hstk; rw [hfrbsz]
        show fr.exec.stack.size + 1 + (chargeCache prog sloadChg a).length ≤ 1024; omega
      obtain ⟨fra, hmra, hcpa⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
        log gS sS cS dS (.tmp a) va frb hda' hsound hscoped (hstore.transport hmrb.storage)
        (by nofun) (by nofun) (hmemreal.transport hmrb.memBytes hmrb.memActive)
        heva hgasa hstka hcpb
      have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
        rw [hmra.code, hbcode]
      have hapc : fra.exec.pc
          = fr.exec.pc + UInt32.ofNat (matCache prog b).length
              + UInt32.ofNat (matCache prog a).length := by
        have := hmra.pc; simp only [matExpr_tmp] at this; rw [this, hbpc]
      have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
        rw [hmra.stack, hmrb.stack]; rfl
      have hadec : decode fra.exec.executionEnv.code fra.exec.pc
          = some (.ArithLogic .ADD, .none) := by rw [hacode, hapc]; exact hop
      have haszle : fra.exec.stack.size ≤ 1024 := by
        have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length := chargeCache_length_pos prog sloadChg a
        rw [hlen_split] at hstk; rw [hfrasz]; omega
      have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
        rw [hmra.gasToNat, hmrb.gasToNat]
        simp only [chargeExpr_tmp]; rw [hsum_split] at hgas; omega
      obtain ⟨hadrun, hadstk⟩ := sim_add fra va vb fr.exec.stack hadec hastk haszle hagas
      -- coupling across the ADD step (non-recording).
      have hcp' : RecorderCoupled log (addFrame fra va vb fr.exec.stack) gS sS cS dS :=
        recorderCoupled_step_other hcpa
          (by unfold isGasOp; rw [hadec]; rfl) (by unfold isSloadOp; rw [hadec]; rfl)
          (stepFrame_add fra va vb fr.exec.stack hadec hastk haszle hagas)
      have hgc : (addFrame fra va vb fr.exec.stack).exec.gasAvailable
          = subCharges fr.exec.gasAvailable
              (chargeExpr sloadChg (chargeCache prog sloadChg) (.add a b)) := by
        rw [hcadd]
        exact gasCharge_binop_glue fr.exec.gasAvailable (chargeCache prog sloadChg b)
          (chargeCache prog sloadChg a) frb fra (addFrame fra va vb fr.exec.stack)
          hmrb.gasCharge hmra.gasCharge (charge_binOpPost_gas fra UInt256.add va vb fr.exec.stack)
      refine ⟨addFrame fra va vb fr.exec.stack, ?_, hcp'⟩
      refine
        { runs := (hmrb.runs.trans hmra.runs).trans hadrun
          stack := ?_, code := ?_, validJumps := ?_, addr := ?_, canMod := ?_, accounts := ?_
          storage := ?_, pc := ?_, gasCharge := hgc, gasToNat := ?_
          memBytes := by rw [addFrame_memory]; exact hmra.memBytes.trans hmrb.memBytes
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
      · rw [addFrame_pc, hapc, matExpr_add]
        simp only [List.length_append, List.length_singleton]
        rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1 : UInt32) = 1 from rfl]
        ac_rfl
      · rw [hgc]; exact toNat_subCharges fr.exec.gasAvailable _ hgas
  | .lt a b, hdec, _, _, heval, hgas, hstk =>
      obtain ⟨va, hla, vb, hlb, hwlt⟩ :
          ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb ∧ w = UInt256.lt va vb := by
        simp only [evalExpr] at heval
        cases hla : st.locals a with
        | none => simp [hla] at heval
        | some va =>
            cases hlb : st.locals b with
            | none => simp [hla, hlb] at heval
            | some vb => refine ⟨va, rfl, vb, rfl, ?_⟩; simp [hla, hlb] at heval; exact heval.symm
      subst hwlt
      rw [matDecC_lt] at hdec
      obtain ⟨hdb, hda, hop⟩ := hdec
      have hclt := chargeExpr_lt sloadChg (chargeCache prog sloadChg) a b
      have hevb : evalExpr st obs (.tmp b) = some vb := hlb
      have heva : evalExpr st obs (.tmp a) = some va := hla
      have hgasb : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).sum
          ≤ fr.exec.gasAvailable.toNat := by
        have hx := hgas; rw [hclt] at hx
        simp only [List.sum_append] at hx
        show (chargeCache prog sloadChg b).sum ≤ _; omega
      have hstkb : fr.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp b)).length ≤ 1024 := by
        have hx := hstk; rw [hclt] at hx
        simp only [List.length_append] at hx
        show fr.exec.stack.size + (chargeCache prog sloadChg b).length ≤ 1024; omega
      obtain ⟨frb, hmrb, hcpb⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
        log gS sS cS dS (.tmp b) vb fr hdb hsound hscoped hstore (by nofun) (by nofun)
        hmemreal hevb hgasb hstkb hcp
      have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
      have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (matCache prog b).length := by
        have := hmrb.pc; simpa only [matExpr_tmp] using this
      have hda' : MatDecC prog hdc hord frb.exec.executionEnv.code frb.exec.pc (.tmp a) := by
        rw [hbcode, hbpc]; exact hda
      have hsum_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)).sum
          = (chargeCache prog sloadChg b).sum + (chargeCache prog sloadChg a).sum + Gverylow := by
        rw [hclt]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
      have hlen_split : (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)).length
          = (chargeCache prog sloadChg b).length + (chargeCache prog sloadChg a).length + 1 := by
        rw [hclt]; simp only [List.length_append, List.length_singleton]
      have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
        rw [hmrb.stack]; simp [Stack.push]
      have hgasa : (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).sum
          ≤ frb.exec.gasAvailable.toNat := by
        rw [hmrb.gasToNat]; show (chargeCache prog sloadChg a).sum ≤ _
        rw [hsum_split] at hgas; simp only [chargeExpr_tmp] at hgas ⊢; omega
      have hstka : frb.exec.stack.size
          + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp a)).length ≤ 1024 := by
        have hpb1 : 1 ≤ (chargeCache prog sloadChg b).length := chargeCache_length_pos prog sloadChg b
        rw [hlen_split] at hstk; rw [hfrbsz]
        show fr.exec.stack.size + 1 + (chargeCache prog sloadChg a).length ≤ 1024; omega
      obtain ⟨fra, hmra, hcpa⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
        log gS sS cS dS (.tmp a) va frb hda' hsound hscoped (hstore.transport hmrb.storage)
        (by nofun) (by nofun) (hmemreal.transport hmrb.memBytes hmrb.memActive)
        heva hgasa hstka hcpb
      have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
        rw [hmra.code, hbcode]
      have hapc : fra.exec.pc
          = fr.exec.pc + UInt32.ofNat (matCache prog b).length
              + UInt32.ofNat (matCache prog a).length := by
        have := hmra.pc; simp only [matExpr_tmp] at this; rw [this, hbpc]
      have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
        rw [hmra.stack, hmrb.stack]; rfl
      have hadec : decode fra.exec.executionEnv.code fra.exec.pc
          = some (.ArithLogic .LT, .none) := by rw [hacode, hapc]; exact hop
      have haszle : fra.exec.stack.size ≤ 1024 := by
        have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by rw [hastk]; simp
        have hpa1 : 1 ≤ (chargeCache prog sloadChg a).length := chargeCache_length_pos prog sloadChg a
        rw [hlen_split] at hstk; rw [hfrasz]; omega
      have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
        rw [hmra.gasToNat, hmrb.gasToNat]
        simp only [chargeExpr_tmp]; rw [hsum_split] at hgas; omega
      obtain ⟨hadrun, hadstk⟩ := sim_lt fra va vb fr.exec.stack hadec hastk haszle hagas
      -- coupling across the LT step (non-recording).
      have hcp' : RecorderCoupled log (ltFrame fra va vb fr.exec.stack) gS sS cS dS :=
        recorderCoupled_step_other hcpa
          (by unfold isGasOp; rw [hadec]; rfl) (by unfold isSloadOp; rw [hadec]; rfl)
          (stepFrame_lt fra va vb fr.exec.stack hadec hastk haszle hagas)
      have hgc : (ltFrame fra va vb fr.exec.stack).exec.gasAvailable
          = subCharges fr.exec.gasAvailable
              (chargeExpr sloadChg (chargeCache prog sloadChg) (.lt a b)) := by
        rw [hclt]
        exact gasCharge_binop_glue fr.exec.gasAvailable (chargeCache prog sloadChg b)
          (chargeCache prog sloadChg a) frb fra (ltFrame fra va vb fr.exec.stack)
          hmrb.gasCharge hmra.gasCharge (charge_binOpPost_gas fra UInt256.lt va vb fr.exec.stack)
      refine ⟨ltFrame fra va vb fr.exec.stack, ?_, hcp'⟩
      refine
        { runs := (hmrb.runs.trans hmra.runs).trans hadrun
          stack := ?_, code := ?_, validJumps := ?_, addr := ?_, canMod := ?_, accounts := ?_
          storage := ?_, pc := ?_, gasCharge := hgc, gasToNat := ?_
          memBytes := by rw [ltFrame_memory]; exact hmra.memBytes.trans hmrb.memBytes
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
      · rw [ltFrame_pc, hapc, matExpr_lt]
        simp only [List.length_append, List.length_singleton]
        rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1 : UInt32) = 1 from rfl]
        ac_rfl
      · rw [hgc]; exact toNat_subCharges fr.exec.gasAvailable _ hgas
  termination_by matDecMeasure prog e
  decreasing_by
    all_goals
      first
        | (simp only [matDecMeasure]; omega)
        | (exact matDecMeasure_remat_lt prog hdc hord (by assumption))

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
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Lir.Corr prog sloadChg obs (fun _ => False) st fr L pc)
    (hk : st.locals key = some kw) (hv : st.locals value = some vw)
    (hsc : Lir.StepScoped prog st (.sstore key value))
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
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
      ∧ Lir.Corr prog sloadChg obs (fun _ => False) (st.setStorage kw vw) fr' L (pc + 1)
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
    materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs (.tmp value) vw fr
      hdv ((defsSoundS_empty_iff prog st).mp hcorr.defsSound) hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
      hevv hcs hstkv
  obtain ⟨frv, hmrv, hcpv⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs log gS sS cS dS
    (.tmp value) vw fr
    hdv ((defsSoundS_empty_iff prog st).mp hcorr.defsSound) hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
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
    materialise_chargeC_le_of_cleanHalt hdc hord sloadChg st obs (.tmp key) kw frv
      hdk' ((defsSoundS_empty_iff prog st).mp hcorr.defsSound) hcorr.wellScoped
      (hcorr.storage.transport hmrv.storage) (by nofun) (by nofun)
      (hcorr.memAgree.transport hmrv.memBytes hmrv.memActive) hevk hcsv hstkk
  obtain ⟨frk, hmrk, hcpk⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs log gS sS cS dS
    (.tmp key) kw frv
    hdk' ((defsSoundS_empty_iff prog st).mp hcorr.defsSound) hcorr.wellScoped
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
    · exact (defsSoundS_empty_iff prog (st.setStorage kw vw)).mpr
        (defsSound_preserved_sstore hsc ((defsSoundS_empty_iff prog st).mp hcorr.defsSound))
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
    (hcorr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hsp : SelfPresent fr)
    (hal : StreamsAligned self log gS cS dS T C D)
    (hk : st.locals key = some kw) (hvv : st.locals value = some vw)
    (hties : StmtTies' prog sloadChg log self L b) :
    CoupledAdvance prog sloadChg log self L pc st fr T C D (.sstore key value) := by
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  -- ties arm (4): `StepScopedS` + the stack-room fold (fired with coupling + clean-halt).
  obtain ⟨hstepS, hstkbound⟩ :=
    hties.2.2.2.1 pc key value kw vw st fr gS sS cS dS hcur hcorr hcp hch hk hvv
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
  -- fire S3 (`sim_sstore_stmt'`): the two-frame materialise fold + the point-wise R4 realisation
  -- + the coupling transported to the post-frame.
  obtain ⟨fr', hruns, hcorr', hstacknil', hcpf⟩ :=
    sim_sstore_stmt' hbt hcur hcorr hk hvv hsc hwl.defsCons hwl.defEnvOrdered hdv hdk hdop
      hch hsp hcp hstkbound
  -- S4 — assemble the `CoupledAdvance`: `EvalStmt.sstore` consumes NO stream head (T/C/D and
  -- gS/sS/cS ride unchanged), so the alignment `hal` carries over verbatim.
  exact ⟨st.setStorage kw vw, fr', T, C, D, gS, sS, cS, dS,
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
    {rec : CallRecord} {cS' : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcorr : Lir.Corr prog sloadChg 0 (fun _ => False) st fr L pc)
    (hcp : RecorderCoupled log fr gS sS (rec :: cS') dS)
    (hch : CleanHaltsNonException fr)
    (haddr : fr.exec.executionEnv.address = self)
    (hcallee : ∃ cw, st.locals cs.callee = some cw)
    (hgasfwd : ∃ gw, st.locals cs.gasFwd = some gw)
    (hal : StreamsAligned self log gS (rec :: cS') dS T C D)
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
    {cS : List CallRecord} {dS : List CreateRecord}
    (hwl : WellLowered prog)
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
    (hstep : ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream)
        (D : CreateStream) (gS : List Word) (sS : List Nat) (cS : List CallRecord)
        (dS : List CreateRecord),
      DriveCorrLog prog sloadChg log self st fr L gS sS cS dS →
      StreamsAligned self log gS cS dS T C D →
      DriveLogStep prog sloadChg log self st fr L T C D gS sS cS dS) :
    ∀ (st : IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord) (dS : List CreateRecord),
      DriveCorrLog prog sloadChg log self st fr L gS sS cS dS →
      StreamsAligned self log gS cS dS T C D →
      RunFromCoupled prog self st fr L T C D := by
  sorry

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
