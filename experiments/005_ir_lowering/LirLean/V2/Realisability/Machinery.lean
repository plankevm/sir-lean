import LirLean.V2.Drive.Headline
import LirLean.Assembly.Acyclic
import LirLean.Decode.BoundaryReach
import LirLean.V2.Realisability.Surface
import LirLean.V2.Modellable

/-!
# LirLean v2 — Realisability spec, MACHINERY (§5)

Split out of `RealisabilitySpec.lean` (pure relocation). Holds the Phase-3 obligation
machinery R1–R11 (§5), including the tracked sorries R3 (`callRealises_of_recorded`) and
R6 (`atReachableBoundaryVJ_step`/`_call`). Imports `Surface`. -/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch

/-! ## §5 — The Phase-3 obligations R1–R11 (every proof `sorry` = tracked debt)

Landing order (each step green, monotonically fewer sorries; target-architecture §5):
R0 (the §3 reshape, done above as statements; R0b below is its MACHINERY criterion —
land it before the R10 builders, which need the reshaped mid-block walk) → R9 → R2 →
R8 → R5/R4 → R6 → gasfree co-flagship → R7 → R1 → R3 → R10 → R11 → R12. Substantial
proofs: R0b (the sim-machinery reshape it gates), R1, R3, R6; everything else is static
folds and assembly. -/

/-! #### R0b machinery — world-irrelevance of non-`sload` `evalExpr` (the `.sload` spill
exclusion itself is the reused `Lir.defsOf_ne_sload`). -/

/-- `evalExpr` over a non-`sload` expression is unchanged by a storage write. -/
private theorem evalExpr_setStorage_noSload {st : IRState} {kw vw obs : Word} :
    ∀ {e : Expr}, (∀ k, e ≠ .sload k) →
      evalExpr (st.setStorage kw vw) obs e = evalExpr st obs e
  | .imm _, _ => rfl
  | .gas, _ => rfl
  | .tmp _, _ => rfl
  | .add _ _, _ => rfl
  | .lt _ _, _ => rfl
  | .slot _, _ => rfl
  | .sload k, h => absurd rfl (h k)

/-- `evalExpr` over a non-`sload` expression ignores the world entirely (the
world-replacement analogue, for the `call` arm). -/
private theorem evalExpr_world_noSload {locals : Tmp → Option Word} {w w' : World}
    {obs : Word} :
    ∀ {e : Expr}, (∀ k, e ≠ .sload k) →
      evalExpr ⟨locals, w'⟩ obs e = evalExpr ⟨locals, w⟩ obs e
  | .imm _, _ => rfl
  | .gas, _ => rfl
  | .tmp _, _ => rfl
  | .add _ _, _ => rfl
  | .lt _ _, _ => rfl
  | .slot _, _ => rfl
  | .sload k, h => absurd rfl (h k)

/-- **R0b — the shadowing-aware machinery-reshape criterion** (header lesson 8; NEW
round-3 tracked obligation). One `EvalStmt` step of a PROGRAM statement preserves the
scoped invariant along the `invalStep` transfer — with NO per-state side conditions: the
live-scope demands of the retired `Lir.StepScoped` are GONE (absorbed by the set), not
relocated into hypotheses. The site premises (`hb`/`hs`) + `DefsConsistent` pin the
statement's registration (a foreign, non-program statement could rebind against `defsOf`
and refute the unpinned version — that drill was run on THIS statement too).

THE MACHINERY FINDING THIS TRACKS (why the reshape is an obligation, not an option): the
CURRENT sim machinery carries the un-scoped `DefsSound` at every statement cursor
(`Corr.defsSound`, `SimStmt.lean`) and so CANNOT traverse a loop-exit iteration of a
rebinding program — at `exProg`'s loop-exit iteration, between the `t6 := gas` rebind
(block 1, pc 0) and `t8`'s reassign (pc 2), the real mid-block state has `t8` stale and
`Corr` is FALSE there (`not_defsSound_stale` is the machine-check; the second-iteration
ENTRY states are fine, which is why the block-boundary `DriveCorrLog` survives). The
Phase-3 R0 reshape must therefore: (1) replace `Corr.defsSound` by `DefsSoundS` at an
`invalStep`-threaded set for the MID-BLOCK cursors of the `SimStmtStep` spine; (2)
re-establish the strong invariant at block boundaries via `RevalidatesPerBlock` +
`defsSoundS_empty_iff` (the boundaries are where the ties consume `Corr`); (3) re-plumb
the per-arm sim lemmas' `StepScoped`/`SstoreRealises`-style inputs to `StepScopedS` +
a use-site non-invalidation premise — a USE of an invalidated tmp is where IR-vs-lowered
divergence would be REAL (the lowered code rematerialises fresh, the IR reads stale), so
the static checks must exclude it; `RevalidatesPerBlock`-conforming programs whose
within-block uses precede the invalidating rebind (or follow the healing reassign, as
`exProg`'s branch use of `t8` does) are the honest domain. NOTE (round-3 review): the
ties' own mid-block `Corr` antecedents are themselves subject to criterion (1)'s carrier
swap — arms at stale-window cursors are un-fireable by the reshaped walk (strong `Corr`
is false at those real states), so the R10a→R11 assembly routes those cursors through
the re-plumbed sim lemmas or a scoped-`Corr` restatement of the arms. DERIVED-status
obligation (a lemma about the semantics; nothing supplied to the flagship). -/
theorem defsSoundS_preserved_step {prog : Program}
    {st st' : IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
    {s : Stmt} {I : Tmp → Prop}
    {L : Label} {b : Block} {pc : Nat}
    (hcons : DefsConsistent prog)
    (hb : blockAt prog L = some b)
    (hs : b.stmts[pc]? = some s)
    (hstep : EvalStmt prog st T C D s st' T' C' D')
    (hsound : DefsSoundS prog I st) :
    DefsSoundS prog (invalStep prog I s) st' := by
  have hbmem : b ∈ prog.blocks.toList := List.mem_of_getElem? (Lir.toList_of_blockAt hb)
  have hsmem : s ∈ b.stmts := List.mem_of_getElem? hs
  cases hstep with
  | assignPure hne hv =>
    rename_i t e w
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hie : invalStep prog I (.assign t e) t₀
        = if t₀ = t then usesInExpr t e ≠ 0 else (I t₀ ∨ ReadsOf prog t t₀) := rfl
    rw [hie] at hninval
    by_cases heq : t₀ = t
    · subst t₀
      rw [if_pos rfl] at hninval
      have hself0 : usesInExpr t e = 0 := not_not.mp hninval
      by_cases hsl : ∃ k, e = .sload k
      · obtain ⟨k, rfl⟩ := hsl
        exact absurd (Or.inr (Or.inl ⟨b, hbmem, k, hsmem⟩)) hnr₀
      · have hself : defsOf prog t = some e := by
          have hc := (hcons L b pc hb).1 t e hs
          rcases e with _ | _ | _ | _ | _ | _ | _ <;>
            first | exact hc | exact absurd rfl hne | exact absurd ⟨_, rfl⟩ hsl
        have he0 : e₀ = e := Option.some.inj (hdef₀.symm.trans hself)
        subst he0
        have hw : (st.setLocal t w).locals t = some w := by simp [IRState.setLocal]
        have hww : w₀ = w := Option.some.inj (hlocal₀.symm.trans hw)
        subst hww
        rw [Lir.evalExpr_setLocal_of_unused hself0]
        exact hv.symm
    · rw [if_neg heq] at hninval
      have hnotI : ¬ I t₀ := fun h => hninval (Or.inl h)
      have hunused : usesInExpr t e₀ = 0 := by
        by_contra hu; exact hninval (Or.inr ⟨e₀, hdef₀, hu⟩)
      have hl' : st.locals t₀ = some w₀ := by
        have hh : (st.setLocal t w).locals t₀ = st.locals t₀ := by
          simp [IRState.setLocal, heq]
        rw [hh] at hlocal₀; exact hlocal₀
      have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hnotI hl'
      rw [Lir.evalExpr_setLocal_of_unused hunused]
      exact hprev
  | assignGas =>
    rename_i obs t
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hie : invalStep prog I (.assign t .gas) t₀
        = if t₀ = t then usesInExpr t .gas ≠ 0 else (I t₀ ∨ ReadsOf prog t t₀) := rfl
    rw [hie] at hninval
    by_cases heq : t₀ = t
    · subst heq
      exact absurd (Or.inl ⟨b, hbmem, hsmem⟩) hnr₀
    · rw [if_neg heq] at hninval
      have hnotI : ¬ I t₀ := fun h => hninval (Or.inl h)
      have hunused : usesInExpr t e₀ = 0 := by
        by_contra hu; exact hninval (Or.inr ⟨e₀, hdef₀, hu⟩)
      have hl' : st.locals t₀ = some w₀ := by
        have hh : (st.setLocal t obs).locals t₀ = st.locals t₀ := by
          simp [IRState.setLocal, heq]
        rw [hh] at hlocal₀; exact hlocal₀
      have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hnotI hl'
      rw [Lir.evalExpr_setLocal_of_unused hunused]
      exact hprev
  | sstore hk hv =>
    rename_i key value kw vw
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hie : invalStep prog I (.sstore key value) t₀ = I t₀ := rfl
    rw [hie] at hninval
    have hl' : st.locals t₀ = some w₀ := hlocal₀
    have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hninval hl'
    have hns : ∀ k, e₀ ≠ .sload k := fun k he => Lir.defsOf_ne_sload prog t₀ k (he ▸ hdef₀)
    rw [evalExpr_setStorage_noSload hns]
    exact hprev
  | call hcallee hgas =>
    rename_i cs calleeW gasFwdW success world'
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hns : ∀ k, e₀ ≠ .sload k := fun k he => Lir.defsOf_ne_sload prog t₀ k (he ▸ hdef₀)
    cases hrt : cs.resultTmp with
    | none =>
      have hie : invalStep prog I (.call cs) t₀ = I t₀ := by simp only [invalStep, hrt]
      rw [hie] at hninval
      simp only [hrt] at hlocal₀
      have hl' : st.locals t₀ = some w₀ := hlocal₀
      have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hninval hl'
      calc some w₀ = evalExpr st 0 e₀ := hprev
        _ = evalExpr { st with world := world' } 0 e₀ := (evalExpr_world_noSload hns).symm
    | some t =>
      have hie : invalStep prog I (.call cs) t₀
          = if t₀ = t then False else (I t₀ ∨ ReadsOf prog t t₀) := by
        simp only [invalStep, hrt]
      rw [hie] at hninval
      simp only [hrt] at hlocal₀
      by_cases heq : t₀ = t
      · subst heq
        exact absurd (Or.inr (Or.inr (Or.inl ⟨b, hbmem, cs, hsmem, hrt⟩))) hnr₀
      · rw [if_neg heq] at hninval
        have hnotI : ¬ I t₀ := fun h => hninval (Or.inl h)
        have hunused : usesInExpr t e₀ = 0 := by
          by_contra hu; exact hninval (Or.inr ⟨e₀, hdef₀, hu⟩)
        have hl' : st.locals t₀ = some w₀ := by
          simpa [IRState.setLocal, heq] using hlocal₀
        have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hnotI hl'
        rw [Lir.evalExpr_setLocal_of_unused hunused]
        calc some w₀ = evalExpr st 0 e₀ := hprev
          _ = evalExpr { st with world := world' } 0 e₀ := (evalExpr_world_noSload hns).symm
  | create hvalue hoff hsize =>
    -- verbatim twin of the `call` arm: the create pops the create stream and applies its head
    -- (world replacement + result-tmp binding) exactly as the call arm applies the call head.
    rename_i cs valueW initOffW initSizeW addrW world'
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hns : ∀ k, e₀ ≠ .sload k := fun k he => Lir.defsOf_ne_sload prog t₀ k (he ▸ hdef₀)
    cases hrt : cs.resultTmp with
    | none =>
      have hie : invalStep prog I (.create cs) t₀ = I t₀ := by simp only [invalStep, hrt]
      rw [hie] at hninval
      simp only [hrt] at hlocal₀
      have hl' : st.locals t₀ = some w₀ := hlocal₀
      have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hninval hl'
      calc some w₀ = evalExpr st 0 e₀ := hprev
        _ = evalExpr { st with world := world' } 0 e₀ := (evalExpr_world_noSload hns).symm
    | some t =>
      have hie : invalStep prog I (.create cs) t₀
          = if t₀ = t then False else (I t₀ ∨ ReadsOf prog t t₀) := by
        simp only [invalStep, hrt]
      rw [hie] at hninval
      simp only [hrt] at hlocal₀
      by_cases heq : t₀ = t
      · subst heq
        -- the create result tmp is `isCreateResult`, hence `NonRecomputable` (fourth disjunct).
        exact absurd (Or.inr (Or.inr (Or.inr ⟨b, hbmem, cs, hsmem, hrt⟩))) hnr₀
      · rw [if_neg heq] at hninval
        have hnotI : ¬ I t₀ := fun h => hninval (Or.inl h)
        have hunused : usesInExpr t e₀ = 0 := by
          by_contra hu; exact hninval (Or.inr ⟨e₀, hdef₀, hu⟩)
        have hl' : st.locals t₀ = some w₀ := by
          simpa [IRState.setLocal, heq] using hlocal₀
        have hprev : some w₀ = evalExpr st 0 e₀ := hsound t₀ e₀ w₀ hdef₀ hnr₀ hnotI hl'
        rw [Lir.evalExpr_setLocal_of_unused hunused]
        calc some w₀ = evalExpr st 0 e₀ := hprev
          _ = evalExpr { st with world := world' } 0 e₀ := (evalExpr_world_noSload hns).symm

/-- **A halting `Runs` is refl.** If `fr` halts (`stepFrame fr = .halted h`) then the only
`Runs fr fr'` is the reflexive one, so `fr = fr'`. Pure engine inversion (the `.step`/`.call`/`.create`
arms demand `.next`/`.needsCall`/`.needsCreate`, contradicting `.halted`). -/
theorem runs_halt_eq {fr fr' : Frame} {h : FrameHalt}
    (hh : stepFrame fr = .halted h) (hr : Runs fr fr') : fr = fr' := by
  cases hr with
  | refl _ => rfl
  | step hstep _ => rw [hstep.1] at hh; exact absurd hh (by nofun)
  | call hcall _ =>
      obtain ⟨_, _, _, _, hstep, _⟩ := hcall
      rw [hstep] at hh; exact absurd hh (by nofun)
  | create hc _ =>
      obtain ⟨_, _, _, hstep, _⟩ := hc
      rw [hstep] at hh; exact absurd hh (by nofun)

/-- **R2 — the clean scope read off the log** (replaces the `∀ last halt` universal `hne`
of `cleanHalts_of_runWithLog` with the decidable `log.clean`). The recorded outcome routes
every halt to `.ok`, so distinguishing a `.success`/`.revert` terminal from an exception
takes the `endCall` fingerprint `success ∨ gasRemaining ≠ 0` — exactly `RunLog.clean`
(with the documented zero-gas-revert cut). `hrb`/`hcc` are carried in the
`cleanHalts_of_runWithLog` shapes because the `Runs`↔`drive` identification may need
modellability; both are in the flagship's context anyway (R6 / `hseams.callsCode`) —
possibly droppable, kept until the proof says so. DERIVED-status obligation. -/
theorem haltNonException_of_cleanLog {prog : Lir.Program} {params : CallParams}
    {fr₀ : Frame} {log : RunLog}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀)
    (hclean : log.clean)
    (hrb : ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr')
    (hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr') :
    ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt →
      HaltNonException halt := by
  obtain ⟨frame, hbc, hdrive⟩ := runWithLog_drive hrun
  rw [hbegin] at hbc
  have hfeq : frame = fr₀ := (Sum.inl.injEq _ _).mp hbc.symm
  rw [hfeq] at hdrive
  obtain ⟨last₀, halt₀, hto₀, hhalt₀, hobs⟩ :=
    runs_of_drive_ok (seedFuel params.gas) fr₀ log.observable hdrive
      (lower_modellable hrb hcc)
  intro last halt hreach hhalt
  -- the halting terminal is unique: `last = last₀`, `halt = halt₀`.
  have hlast : last = last₀ :=
    runs_halt_eq hhalt (Runs.linear_to_halt hhalt₀ hto₀ hreach)
  subst hlast
  rw [hhalt] at hhalt₀
  have hheq : halt = halt₀ := (Signal.halted.injEq _ _).mp hhalt₀
  subst hheq
  -- non-exception terminals close by `trivial`; the exception one contradicts `hclean`.
  cases halt with
  | success e o => trivial
  | revert g o => trivial
  | exception ex =>
      exfalso
      unfold RunLog.clean at hclean
      rw [hobs] at hclean
      unfold endFrame at hclean
      cases hk : last.kind with
      | call checkpoint =>
          rw [hk] at hclean
          simp only [endCall] at hclean
          rcases hclean with h | h
          · exact absurd h (by decide)
          · exact absurd h (by decide)
      | create address checkpoint =>
          rw [hk] at hclean
          exact hclean

/-! ### R3 resume-frame structural pins (`resumeAfterCall_{code,validJumps,pc,stack}`)

The `rfl` companions of the default-target `resumeAfterCall_address`/`_memory`/`_activeWords`
(`Engine/StepWalk.lean`, `Engine/MemAlgebra.lean`), for the resume-frame conjuncts of
`CallRealisesS` (§3, conjuncts 11/17/13/14). `resumeAfterCall` rebuilds `pd.frame` as
`{ pd.frame with exec := exec'.replaceStackAndIncrPC (pd.stack.push x) }`, touching only
stack/pc/gas/accounts/substate/toMachineState and leaving `executionEnv` (hence `.code`) and
the `Frame.validJumps` field untouched; the pc advances by the default `pcΔ = 1` (past the CALL
byte) and the pushed word is exactly `callSuccessFlag result pd` (= the oracle's `successWord`,
`evmCallOracle_successWord_eq_x`). These are `WIP`-local facts ABOUT the default-target
`resumeAfterCall` def; they do NOT edit it. They discharge conjuncts 11/13/14/17 of R3's bundle
*once* the strengthened CALL-dispatch inversion supplies the `pd.frame.exec`/`pd.stack`/
`pd.{in,out}Size` framing (the Group-B residue — see R3's STATUS note, blocked on the default
target). -/

/-- Resumed frame keeps the caller's `code` (env untouched by `resumeAfterCall`). -/
theorem resumeAfterCall_code (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.executionEnv.code
      = pd.frame.exec.executionEnv.code := rfl

/-- Resumed frame keeps the caller's `validJumps` (`Frame.validJumps` field untouched). -/
theorem resumeAfterCall_validJumps (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).validJumps = pd.frame.validJumps := rfl

/-- Resumed frame's pc is the caller's advanced by one (default `pcΔ = 1`, past the CALL byte). -/
theorem resumeAfterCall_pc (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.pc = pd.frame.exec.pc + 1 := rfl

/-- Resumed frame's stack is the caller's with the CALL success flag pushed. -/
theorem resumeAfterCall_stack (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.stack
      = pd.stack.push (callSuccessFlag result pd) := rfl

/-- **R3 — call realisation from the log.** At a call cursor, the coupled frame's recorded
CALL supplies the `CallRealisesS` bundle at the REALISED oracle — the round-3 restatement
(header lesson 8): NOT the in-tree `Lir.CallRealises` verbatim (whose embedded
`StepScoped (.call cs)` live-scope clause is refutable within this theorem's own
hypothesis envelope for a `WellLowered` program whose call result has a registered
reader), but the value/trace KERNEL + the shadowing-aware static scoping (`StepScopedS`)
+ the static bundle the round-2 statement was MISSING (`hwl` — it is what derives the
`StepScopedS` residue, the result-tmp slot registration of the post-state fold, and the
Route-B slot addressability; the round-2 reviewer's "R3 carries no static bundle at all").
Kernel sources: the head `CallRecord` (`realisedCall_cons`, rfl-clean once the record
is pinned), plumbing from `materialise_runs` + the `resumeAfterCall` rfl-pins + the
Route-B tail (`stash_tail_runs`).
Calls are now a CONSUMED `CallStream` (R3′ LANDED — the foundation call-stream change): the
coupled `callSuffix` is destructured `rec :: cS'`, and its HEAD `rec` IS this cursor's call —
POSITIONALLY, per record, with NO single-call restriction (distinct dynamic calls, including a
per-iteration loop CALL, consume distinct stream heads). The address antecedent is what
identifies `rec`'s `evmV2CallEntry` effect with the effect at `fr0.address`. The post-state
`st0'` is BAKED into the conclusion as `rec`'s realised effect. DERIVED-status obligation
(with `hseams`-style context available to the R10 assembly if the plumbing needs it).

**STATUS (R3 — honest partial; theorem stays `sorry`).** Piece A (record identification
from the recorder) is LANDED, real and axiom-clean, as `recorderCoupled_call_extract` (above):
it PRODUCES the `CallReturns callFr resumeFr` witness and the `rec = {result :=
childRes.toCallResult, pending}` record identity from the coupling at the CALL cursor — the
seedFuel-vs-restart-fuel reconciliation the plan under-specified is discharged via
`child_terminates` + `drive_fuel_mono` (Piece A is genuinely, not just nominally, unblocked by
R7e). `recorderCoupled_stepsTo_other` lands the Piece-A step-1 arg-push transport atom. The
coupled `callSuffix` head `rec` pins the post-state (`realisedCall_cons`, `rfl`-clean per
record), and Piece A discharges the post-state pin `st0' = evmV2CallEntry rec …`-effect and
supplies `CallReturns` + `resumeFr`.

**BLOCKER — Piece B (the machine run) has no in-tree producer.** The bundle's arg-push run
conjuncts (`Runs fr0 callFr` + the pc/mem/activeWords pins + `decode callFr = CALL`) require a
`materialise`-driver that BUILDS the run from `Corr`/`hwl` (the five `emitImm 0` pushes then two
`materialise_runs_of_cleanHalt` calls, threading `MatDec`/`DefsSound`/`StorageAgree`/`MemRealises`
/`evalExpr`/stack-room from `Corr.memAgree`/`Corr.defsSound` + `hwl`). In-tree this run is only
ever SUPPLIED to `sim_call_stmt` (`SimStmt.lean:589` `hargs : Runs fr callFr`); no producing lemma
exists, so it must be written from scratch (~200 lines, precedent: the branch cond driver
`LowerDecode.lean:747`). Landing that driver also locates `callFr` and gives
`stepFrame callFr = .needsCall …` (feeding `recorderCoupled_call_extract`) and the Route-B tail
(`stash_tail_runs`). Secondary risk (plan §3.2): several `resumeAfterCall` frame-pins
(`resumeFr.exec.pc = callFr.exec.pc + 1`, `.stack`, `.memory`) may need a bytecode-layer
computation lemma about `resumeAfterCall` — that would live in the DEFAULT target, so per the
track rules it is STOP-and-report, not an in-`WIP` edit. A partial `refine` supplying only the
Piece-A/C conjuncts would bury the Piece-B `sorry` in a mid-bundle position (a fake close the
review's statement-diff would flag), so R3 stays a single top-level `sorry` with Piece A landed as
the two helpers above. -/
theorem callRealises_of_recorded {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 : IRState} {fr0 : Frame}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS' : List CallRecord}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    -- the coupled call suffix's HEAD `rec` IS this cursor's recorded CALL (positional,
    -- multi-call — no single-call premise):
    (hcp : RecorderCoupled log fr0 gS sS (rec :: cS'))
    (hch : CleanHaltsNonException fr0)
    (haddr : fr0.exec.executionEnv.address = self) :
    -- the post-state is `rec`'s realised `evmV2CallEntry` effect (baked in — the positional
    -- head pin, no free `st0'`):
    CallRealisesS prog sloadChg L b pc cs st0
      (match cs.resultTmp with
        | some t' => { st0 with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key }.setLocal
                        t' (callSuccessFlag rec.result rec.pending)
        | none   => { st0 with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key })
      fr0 := sorry

/-- **R4 — SSTORE realisation, point-wise at the concrete frame** (the honest replacement
of the unsatisfiable `∃ acc, SstoreRealises …` tie conjunct — header lesson 3). At the
REAL internal SSTORE frame `g` (stack `kw :: vw :: []`, SSTORE decoded, modifiable — any
write, zero included), the three `SstoreRealises` conclusions hold AT `g`: the stipend gate and the
EIP-2200 charge bound are DERIVED from the clean-halt witness (an under-gassed SSTORE would
exception, contradicting `hch`), and the presence conjunct is exactly `hsp` (the threaded
`SelfPresent`, decision 4 wired at last). NOTE (recorded blast radius): Phase 3 must also
re-plumb `sim_sstore_stmt`'s `hsstore : SstoreRealises …` input to this point-wise form —
part of the R0 reshape's edit set, not performable here (no edits to existing files). -/
theorem sstoreRealises_at_frame {g : Frame} {kw vw : Word}
    (hsp : SelfPresent g)
    (hch : CleanHaltsNonException g)
    (hstk : g.exec.stack = kw :: vw :: [])
    (hdec : decode g.exec.executionEnv.code g.exec.pc = some (.Smsf .SSTORE, .none))
    (hmod : g.exec.executionEnv.canModifyState = true) :
    (¬ g.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    ∧ sstoreChargeOf g.exec kw vw ≤ g.exec.gasAvailable.toNat
    ∧ ∃ acc, g.exec.accounts.find? g.exec.executionEnv.address = some acc := by
  have hsz : g.exec.stack.size ≤ 1024 := by
    have hsize : g.exec.stack.size = 2 := by rw [hstk]; rfl
    omega
  have hdich : (∃ e', stepFrame g = .next e')
      ∨ (∃ ex, stepFrame g = .halted (.exception ex)) := by
    by_cases hstip : g.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend
    · exact Or.inr ⟨_, stepFrame_sstore_stipend g kw vw [] hdec hstk hsz hmod hstip⟩
    · by_cases hcost : sstoreChargeOf g.exec kw vw ≤ g.exec.gasAvailable.toNat
      · exact Or.inl ⟨_, stepFrame_sstore g kw vw [] hdec hstk hsz hmod hstip hcost⟩
      · exact Or.inr ⟨_, stepFrame_sstore_oog g kw vw [] hdec hstk hsz hmod hstip (by omega)⟩
  obtain ⟨e', hnext⟩ := Lir.CleanHaltExtract.next_of_cleanHalt_continuing hch hdich
  obtain ⟨h1, h2⟩ := stepFrame_sstore_inv g kw vw [] hdec hstk hsz hmod hnext
  exact ⟨h1, h2, hsp⟩

/-- **Kind preservation across `Runs`.** A `Runs` derivation only advances `exec` (opcode
steps, `StepsTo.kind_eq`), resumes a returning CALL (`resumeAfterCall` rebuilds the caller
frame keeping its `kind`, `stepFrame_needsCall_inv`), or resumes a returning CREATE
(`resumeAfterCreate` rebuilds the creator frame keeping its `kind`, `resumeAfterCreate_kind` +
`stepFrame_needsCreate_inv`), so the frame `kind` is invariant.
Template: `selfPresent_runs` / `Runs.gasAvailable_le`. -/
theorem runs_kind {fr fr' : Frame} (h : Runs fr fr') : fr'.kind = fr.kind := by
  induction h with
  | refl _ => rfl
  | step hs _ ih => rw [ih, hs.kind_eq]
  | call hc _ ih =>
      obtain ⟨cp, pending, child, childRes, hstep, _, _, hresume⟩ := hc
      rw [ih, hresume]
      exact (Evm.stepFrame_needsCall_inv hstep).2.1
  | create hc _ ih =>
      obtain ⟨cp, pending, childRes, hstep, _, hresume⟩ := hc
      rw [ih, resumeAfterCreate_kind childRes pending _ hresume]
      exact (Evm.stepFrame_needsCreate_inv hstep).2.1

set_option maxRecDepth 8192 in
/-- **R5 — terminator ties from the walk vocabulary.** `TermTies'` holds at every present
block: its arms' antecedents are exactly what `DriveCorrLog` supplies at real boundaries
(Corr, clean-halt, self-presence, address/kind pins), and the conclusions are derived —
non-emptiness via `accounts_ne_empty_of_selfPresent`; the gas guards via the clean-halt
landing extractors (the jump pre-`JUMPDEST` landing/the branch pre-`JUMPDEST` landing patterns,
ported inline); the ret charge-sum via `materialise_charge_le_of_cleanHalt`; the ret epilogue
decode facts via `imm_leaf_decode`/`decode_at_term_nonpush` at the pc-pinned cursor; the `frv`
kind/presence facts via `runs_kind` / `selfPresent_runs_of_call` seeded from the antecedent
pins. DERIVED-status obligation.

**STATEMENT CHANGES (Phase-3 Round-3 — over-specification fixes, honesty-critical):**
  * **branch arm restricted to the WITNESSED direction.** The old arm demanded all six JUMPI
    gas guards along BOTH directions off the single pre-JUMPI frame; a single
    `CleanHaltsNonException frT` witnesses only the direction the run takes (JUMPI charges
    `Ghigh` on both arms, so the not-taken guards are refutable — e.g. `3 ≤ (jumpiFallthrough
    …).gas = Gjumpdest = 1` is FALSE when gas is provisioned for the taken path). The taken
    guards (`g1`/`g2` unconditional, both provable; `g3` under `cw ≠ 0`; `g4∧g5∧g6` under
    `cw = 0`) are the exact case-split of the branch pre-`JUMPDEST` landing; NO witnessed
    conformance content is dropped — only the unwitnessable not-taken over-demand.
  * **ret charge-sum moved under the return-value guard.** The charge fold
    `materialise_charge_le_of_cleanHalt` needs the operand value, and the IR `ret t`
    semantics (`RunFrom.ret`) itself requires `st'.locals t = some vw`; demanding the
    charge-sum bound for an UNBOUND `t` is the same unwitnessable over-demand (the `.length`
    bound stays unconditional — it is static). The epilogue block (already under the value
    guard) is unchanged in placement.
  * **`hretEmit` added — the ret epilogue's pc-bound seam.** `WellFormedLowered.bound_ret`
    only bounds `termOf + |materialise t|` (the operand), NOT the 101-byte `PUSH32 0; MSTORE;
    PUSH32 32; PUSH32 0; RETURN` full-observable epilogue; the five epilogue decodes need
    `termOf + |materialise t| + 100 < 2^32`, which is a static, satisfiable,
    checker-dischargeable well-formedness fact absent from `bound_ret` (a default-target
    under-specification not editable here). Supplied as an explicit seam, NOT a vacuity dodge
    (it is genuinely true for every real ret block).
  * **`CallPreservesSelf` DERIVED, not added to the signature.** The ret `SelfPresent frv`
    bridge (across the adversarial `Runs frT frv`) is discharged from the already-present
    `hprec` via `callPreservesSelf_modGuards hprec` (axiom-clean); no seam added — a
    strengthening over the round-2 blocker's "add `CallPreservesSelf`" instruction. -/
theorem termTies'_of_walk {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block}
    (hwl : WellLowered prog)
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hretEmit : ∀ t, b.term = .ret t →
      termOf prog L + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length + 100
        < 2 ^ 32)
    (hb : blockAt prog L = some b) :
    TermTies' prog sloadChg log self L b := by
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- STOP arm: non-emptiness from the threaded `SelfPresent`.
    intro _hterm st frT hcorr _hch hsp _haddr _hkind
    exact accounts_ne_empty_of_selfPresent hsp
  · -- RET arm.
    intro t hterm st frT hcorr hch hsp haddr hkind
    have hb100 : termOf prog L
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length + 100 < 2 ^ 32 :=
      hretEmit t hterm
    -- conjunct 2: the static stack-room bound (value-free).
    refine ⟨hwl.stack.ret sloadChg L b t hb hterm, ?_⟩
    intro vw hvw
    -- conjunct 1: the charge-sum bound (needs the returned value `vw`).
    have hdv : MatDec frT.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
        frT.exec.pc (.tmp t) := by
      rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
      exact matDec_of_term prog sloadChg L b 0 (.tmp t) hbt
        (by rw [hterm]; exact ret_sub_value prog t)
        (by rw [hterm]
            show _ ≤ ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t))
                        ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]).length
            simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil]
            omega)
        (hwl.wf.matFueled_ret L b t hbt hterm) (by rw [Nat.add_zero]; omega)
    have hstkC : frT.exec.stack.size
        + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024 := by
      rw [hcorr.stack_nil]; simpa using hwl.stack.ret sloadChg L b t hb hterm
    refine ⟨materialise_charge_le_of_cleanHalt (prog := prog) sloadChg (recomputeFuel prog) st 0
        (.tmp t) vw frT hdv hcorr.defsSound hcorr.wellScoped hcorr.storage (by nofun) (by nofun)
        hcorr.memAgree hvw hch hstkC, ?_⟩
    -- conjunct 3: the pc-pinned full-observable epilogue block
    -- (`PUSH32 0; MSTORE; PUSH32 32; PUSH32 0; RETURN`).
    intro frv hruns hcode _haddr' _hsto hstk hpc
    set lc := (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length with hlc
    have hemitR : emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term
          = materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)
            ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret] := by
      rw [hterm]; rfl
    have hfrvcode : frv.exec.executionEnv.code = lower prog := by rw [hcode, hcorr.code_eq]
    have hfrvpc : frv.exec.pc = UInt32.ofNat (termOf prog L + lc) := by
      rw [hpc, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt, ofNat_add']
    have hfrvstk : frv.exec.stack = vw :: ([] : Stack Word) := by rw [hstk, hcorr.stack_nil]
    -- pc-normalisation of the five epilogue anchors to `ofNat (termOf + (lc + off))`.
    have e33 : frv.exec.pc + UInt32.ofNat 33 = UInt32.ofNat (termOf prog L + (lc + 33)) := by
      rw [hfrvpc]; simp only [ofNat_add']; congr 1
    have e34 : frv.exec.pc + UInt32.ofNat 33 + 1 = UInt32.ofNat (termOf prog L + (lc + 34)) := by
      rw [hfrvpc]; simp only [show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add']; congr 1
    have e67 : frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33
        = UInt32.ofNat (termOf prog L + (lc + 67)) := by
      rw [hfrvpc]; simp only [show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add']; congr 1
    have e100 : frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33 + UInt32.ofNat 33
        = UInt32.ofNat (termOf prog L + (lc + 100)) := by
      rw [hfrvpc]; simp only [show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add']; congr 1
    -- the five epilogue decodes (peeled from the flat byte string).
    have hd0 : decode frv.exec.executionEnv.code frv.exec.pc
        = some (.Push .PUSH32, some ((0 : Word), 32)) := by
      rw [hfrvcode, hfrvpc]
      exact imm_leaf_decode prog (termOf prog L + lc) 0 (by omega)
        (by intro j hj
            have hja := flatBytes_at_termOf prog L b (lc + j) hbt (by
              rw [hemitR]
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
              rw [emitImm_length] at hj; omega)
            rw [show termOf prog L + (lc + j) = termOf prog L + lc + j from by omega] at hja
            rw [hja, hemitR]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, ← hlc]; rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_right (by simp only [← hlc]; omega)]
            rw [show lc + j - (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length = j
                  from by rw [← hlc]; omega])
    have hdms : decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
        = some (.Smsf .MSTORE, .none) := by
      rw [hfrvcode, e33]
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[lc + 33]?
            = some Byte.mstore := by
        rw [hemitR]
        rw [List.getElem?_append_left (by
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega)]
        rw [List.getElem?_append_left (by
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega)]
        rw [List.getElem?_append_left (by
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega)]
        rw [List.getElem?_append_right (by
              simp only [List.length_append, emitImm_length, ← hlc]; omega)]
        simp only [List.length_append, emitImm_length, ← hlc,
          show lc + 33 - (lc + 33) = 0 from by omega]
        rfl
      exact decode_at_term_nonpush prog L b (lc + 33) Byte.mstore hbt
        (by rw [hemitR]
            simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega)
        hbyte0 (by omega) (by decide)
    have hd32 : decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + 1)
        = some (.Push .PUSH32, some ((32 : Word), 32)) := by
      rw [hfrvcode, e34]
      exact imm_leaf_decode prog (termOf prog L + (lc + 34)) 32 (by omega)
        (by intro j hj
            have hja := flatBytes_at_termOf prog L b (lc + 34 + j) hbt (by
              rw [hemitR]
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
              rw [emitImm_length] at hj; omega)
            rw [show termOf prog L + (lc + 34 + j) = termOf prog L + (lc + 34) + j from by omega] at hja
            rw [hja, hemitR]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_right (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [show lc + 34 + j - (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)
                    ++ emitImm 0 ++ [Byte.mstore]).length = j from by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega])
    have hd0' : decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33)
        = some (.Push .PUSH32, some ((0 : Word), 32)) := by
      rw [hfrvcode, e67]
      exact imm_leaf_decode prog (termOf prog L + (lc + 67)) 0 (by omega)
        (by intro j hj
            have hja := flatBytes_at_termOf prog L b (lc + 67 + j) hbt (by
              rw [hemitR]
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
              rw [emitImm_length] at hj; omega)
            rw [show termOf prog L + (lc + 67 + j) = termOf prog L + (lc + 67) + j from by omega] at hja
            rw [hja, hemitR]
            rw [List.getElem?_append_left (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [List.getElem?_append_right (by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
                  rw [emitImm_length] at hj; omega)]
            rw [show lc + 67 + j - (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)
                    ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32).length = j from by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega])
    have hdret : decode frv.exec.executionEnv.code
        (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33 + UInt32.ofNat 33)
        = some (.System .RETURN, .none) := by
      rw [hfrvcode, e100]
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[lc + 100]?
            = some Byte.ret := by
        rw [hemitR, List.getElem?_append_right (by
              simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
              omega)]
        simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc,
          show lc + 100 - (lc + 33 + 1 + 33 + 33) = 0 from by omega]
        rfl
      exact decode_at_term_nonpush prog L b (lc + 100) Byte.ret hbt
        (by rw [hemitR]
            simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]
            omega)
        hbyte0 (by omega) (by decide)
    -- run the epilogue, extracting the gas/memory witnesses from the clean-halt chain.
    have hcsv : CleanHaltsNonException frv := cleanHaltsNonException_forward hch hruns
    have hszv : frv.exec.stack.size + 1 ≤ 1024 := by
      rw [hstk, hcorr.stack_nil]; show (1 : ℕ) + 1 ≤ 1024; omega
    have hgv1 : 3 ≤ frv.exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt frv .PUSH32 0 32 hcsv (by decide) hd0
        (by decide) (by decide) hszv).1
      have hvl : GasConstants.Gverylow = 3 := rfl; omega
    -- (1) `PUSH32 0`.
    have hrunpush : Runs frv (pushFrameW frv (0 : Word) 32) :=
      runs_push frv .PUSH32 0 32 (by nofun) hd0 rfl rfl hgv1 hszv
    have hcsvF1 : CleanHaltsNonException (pushFrameW frv (0 : Word) 32) :=
      cleanHaltsNonException_forward hcsv hrunpush
    have hf1stk : (pushFrameW frv (0 : Word) 32).exec.stack = (0 : Word) :: vw :: ([] : Stack Word) := by
      show (0 : Word) :: frv.exec.stack = _; rw [hfrvstk]
    have hf1sz : (pushFrameW frv (0 : Word) 32).exec.stack.size ≤ 1024 := by
      rw [hf1stk]; show (2 : ℕ) ≤ 1024; omega
    have hdmsF1 : decode (pushFrameW frv (0 : Word) 32).exec.executionEnv.code
        (pushFrameW frv (0 : Word) 32).exec.pc = some (.Smsf .MSTORE, .none) := by
      rw [pushFrameW_code, pushFrameW_pc, show ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 from by decide]
      exact hdms
    -- (2) `MSTORE(0, vw)` — the memory-expansion witness + charges.
    obtain ⟨wms, hmemF1, hgasMemF1, hgasVF1, _hstepms⟩ :=
      CleanHaltExtract.next_mstore_of_cleanHalt (pushFrameW frv (0 : Word) 32) (0 : Word) vw []
        hcsvF1 hdmsF1 hf1stk hf1sz
    have hmemFrv : memoryExpansionWords? frv.exec.activeWords (0 : Word) 32 = some wms := hmemF1
    have hrunms : Runs (pushFrameW frv (0 : Word) 32)
        (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) :=
      runs_mstore (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms [] hdmsF1 hf1stk hf1sz
        hmemF1 hgasMemF1 hgasVF1
    have hcsvMs : CleanHaltsNonException (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) :=
      cleanHaltsNonException_forward hcsvF1 hrunms
    have hmsstk : (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.stack
        = ([] : Stack Word) := by rw [mstoreFrame_stack]
    have hmssz : (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.stack.size + 1
        ≤ 1024 := by rw [hmsstk]; show (0 : ℕ) + 1 ≤ 1024; omega
    have hd32Ms : decode (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.executionEnv.code
        (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.pc
          = some (.Push .PUSH32, some ((32 : Word), 32)) := by
      rw [mstoreFrame_code, pushFrameW_code, mstoreFrame_pc, pushFrameW_pc,
          show ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 from by decide]
      exact hd32
    -- (3) `PUSH32 32`.
    have hg32 : 3 ≤ (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt
        (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) .PUSH32 32 32
        hcsvMs (by decide) hd32Ms (by decide) (by decide) hmssz).1
      have hvl : GasConstants.Gverylow = 3 := rfl; omega
    have hrunpush2 : Runs (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms [])
        (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32) :=
      runs_push (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) .PUSH32 32 32
        (by nofun) hd32Ms rfl rfl hg32 hmssz
    have hcsvF2 : CleanHaltsNonException
        (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32) :=
      cleanHaltsNonException_forward hcsvMs hrunpush2
    have hf2stk : (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32).exec.stack
        = (32 : Word) :: ([] : Stack Word) := by
      show (32 : Word) :: (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.stack = _
      rw [hmsstk]
    have hf2sz : (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32).exec.stack.size + 1
        ≤ 1024 := by rw [hf2stk]; show (1 : ℕ) + 1 ≤ 1024; omega
    have hd0'F2 : decode
        (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32).exec.executionEnv.code
        (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32).exec.pc
          = some (.Push .PUSH32, some ((0 : Word), 32)) := by
      rw [pushFrameW_code, mstoreFrame_code, pushFrameW_code, pushFrameW_pc, mstoreFrame_pc,
          pushFrameW_pc, show ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 from by decide]
      exact hd0'
    -- (4) `PUSH32 0`.
    have hg0'' : 3 ≤ (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms [])
        (32 : Word) 32).exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt
        (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []) (32 : Word) 32)
        .PUSH32 0 32 hcsvF2 (by decide) hd0'F2 (by decide) (by decide) hf2sz).1
      have hvl : GasConstants.Gverylow = 3 := rfl; omega
    obtain ⟨cp, hcpeq⟩ := hkind
    refine ⟨cp, wms, hd0, hdms, hd32, hd0', hdret, hgv1, hmemFrv, hgasMemF1, hgasVF1, hg32, hg0'', ?_, ?_⟩
    · rw [runs_kind hruns]; exact hcpeq
    · exact accounts_ne_empty_of_selfPresent (selfPresent_runs_of_call hprec hsp hruns)
  · -- JUMP arm.
    intro dst bdst hterm hbdst hdstlt st frT hcorr hch
    obtain ⟨hbterm, hboff⟩ := hwl.wf.bound_jump L b dst hbt hterm
    set off := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx with hoff
    set dest : Word := UInt256.ofNat (off % 2 ^ 32) with hdest
    set new_pc := UInt32.ofNat off with hnew
    have hemitT : emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term
          = emitDest off ++ [Byte.jump] := by rw [hterm]; rfl
    have hedlen : (emitDest off).length = 5 := by simp [emitDest, offsetBytesBE]
    have htermlen : (emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length = 6 := by
      rw [hemitT, List.length_append, hedlen]; rfl
    have hdpush : decode frT.exec.executionEnv.code frT.exec.pc
        = some (.Push .PUSH4, some (dest, 4)) := by
      rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
      exact term_dest_decode prog L b 0 off hbt
        (by intro j hj; rw [hemitT]; rw [Nat.zero_add, List.getElem?_append_left hj])
        (by rw [htermlen, hedlen]; omega) (by omega)
    have hdjump : decode frT.exec.executionEnv.code (frT.exec.pc + UInt32.ofNat 5)
        = some (.Smsf .JUMP, .none) := by
      rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt, ofNat_add']
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[5]? = some Byte.jump := by
        rw [hemitT, List.getElem?_append_right (by rw [hedlen]), hedlen]; rfl
      exact decode_at_term_nonpush prog L b 5 Byte.jump hbt (by rw [htermlen]; omega) hbyte0
        (by rw [show termOf prog L + 5 = termOf prog L + 5 from rfl]; omega) (by decide)
    have hdjd : decode (lower prog) (UInt32.ofNat off) = some (.Smsf .JUMPDEST, .none) :=
      decode_at_block_offset_jumpdest prog dst bdst hbdst (by rw [← hoff]; omega)
    have hdestword : dest.toUInt32? = some (UInt32.ofNat off) := ofNatMod_toUInt32? off
    have hgstk : frT.exec.stack = [] := hcorr.stack_nil
    have hvalid : frT.validJumps = validJumpDests (lower prog) 0 := hcorr.validJumps_lower
    have hstk1 : frT.exec.stack.size + 1 ≤ 1024 := by rw [hgstk]; show (0 : ℕ) + 1 ≤ 1024; omega
    have hgpush : 3 ≤ frT.exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt frT .PUSH4 dest 4 hch (by decide) hdpush
        (by decide) (by decide) hstk1).1
      have hvl : GasConstants.Gverylow = 3 := rfl; omega
    have hpush : Runs frT (pushFrameW frT dest 4) :=
      runs_push frT .PUSH4 dest 4 (by nofun) hdpush rfl rfl hgpush hstk1
    set frp := pushFrameW frT dest 4 with hfrp
    have hpcode : frp.exec.executionEnv.code = frT.exec.executionEnv.code := rfl
    have hppc : frp.exec.pc = frT.exec.pc + UInt32.ofNat 5 := by
      show frT.exec.pc + ((4 : UInt8) + 1).toUInt32 = _
      rw [show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide]
    have hpstk : frp.exec.stack = dest :: frT.exec.stack := rfl
    have hpjdec : decode frp.exec.executionEnv.code frp.exec.pc = some (.Smsf .JUMP, .none) := by
      rw [hpcode, hppc]; exact hdjump
    have hpjsz : frp.exec.stack.size ≤ 1024 := by
      rw [hpstk, hgstk]; show (1 : ℕ) ≤ 1024; omega
    have hgetdest : frp.get_dest dest = some new_pc := by
      refine Frame.get_dest_of_mem _ hdestword ?_
      show new_pc ∈ frp.validJumps
      rw [hfrp, pushFrameW_validJumps, hvalid, hnew]
      simpa using block_offset_validJump prog dst hdstlt
    have hcsP : CleanHaltsNonException frp := cleanHaltsNonException_forward hch hpush
    have hgjump : GasConstants.Gmid ≤ frp.exec.gasAvailable.toNat :=
      (CleanHaltExtract.next_jump_of_cleanHalt frp dest new_pc frT.exec.stack hcsP hpjdec hpstk
        hpjsz hgetdest).1
    have hjump : Runs frp (jumpFrame frp GasConstants.Gmid new_pc frT.exec.stack) :=
      runs_jump frp dest new_pc frT.exec.stack hpjdec hpstk hpjsz hgjump hgetdest
    set fj := jumpFrame frp GasConstants.Gmid new_pc frT.exec.stack with hfj
    have hfjpc : fj.exec.pc = new_pc := rfl
    have hfjcode : fj.exec.executionEnv.code = lower prog := by
      rw [hfj, jumpFrame_code, hpcode]; exact hcorr.code_eq
    have hfjstk : fj.exec.stack = [] := by rw [hfj, jumpFrame_stack]; exact hgstk
    have hfjdec : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
      rw [hfjcode, hfjpc, hnew]; exact hdjd
    have hfrun : Runs frT fj := hpush.trans hjump
    have hcsJ : CleanHaltsNonException fj := cleanHaltsNonException_forward hch hfrun
    have hfjsz : fj.exec.stack.size ≤ 1024 := by rw [hfjstk]; show (0 : ℕ) ≤ 1024; omega
    have hgjd : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat :=
      (CleanHaltExtract.next_jumpdest_of_cleanHalt fj hcsJ hfjdec hfjsz).1
    exact ⟨hgpush, hgjump, hgjd⟩
  · -- BRANCH arm.
    intro cond thenL elseL bthen belse hterm hbthen hbelse hthenlt helselt st frT cw hcorr hch hc
    obtain ⟨hbterm, hbthenoff, hbelseoff⟩ := hwl.wf.bound_branch L b cond thenL elseL hbt hterm
    have hwfCond : MatFueled (defsOf prog) (recomputeFuel prog) (.tmp cond) :=
      hwl.wf.matFueled_branch L b cond thenL elseL hbt hterm
    have hstkCond : frT.exec.stack.size
        + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024 := by
      rw [hcorr.stack_nil]; simpa using hwl.stack.branch sloadChg L b cond thenL elseL hb hterm
    set lc := (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length with hlc
    set thenOff := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx with hthenoff
    set elseOff := offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx with helseoff
    set thenW : Word := UInt256.ofNat (thenOff % 2 ^ 32) with hthenW
    set elseW : Word := UInt256.ofNat (elseOff % 2 ^ 32) with helseW
    -- (1) COND MATERIALISE via `materialise_runs_of_cleanHalt`, gas FOR FREE.
    -- the cond materialise sits at offset 0 of `emitTerm`, anchored at `frT.exec.pc = termOf`.
    have hemitT : emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term
          = materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)
            ++ emitDest thenOff ++ [Byte.jumpi] ++ emitDest elseOff ++ [Byte.jump] := by
      rw [hterm]; rfl
    have hedlen : ∀ o, (emitDest o).length = 5 := fun o => by simp [emitDest, offsetBytesBE]
    have htermlen : (emitTerm (defsOf prog) (recomputeFuel prog)
        (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length = lc + 12 := by
      rw [hemitT]; simp only [List.length_append, List.length_singleton, hedlen, ← hlc]
    have hcondMatDec : MatDec frT.exec.executionEnv.code (defsOf prog) sloadChg
        (recomputeFuel prog) frT.exec.pc (.tmp cond) := by
      rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
      exact matDec_of_term prog sloadChg L b 0 (.tmp cond) hbt
        (by intro j hj; rw [hemitT, Nat.zero_add]
            rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; rw [← hlc] at hj ⊢; omega)]
            rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; rw [← hlc] at hj ⊢; omega)]
            rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [← hlc] at hj ⊢; omega)]
            rw [List.getElem?_append_left (by rw [← hlc] at hj ⊢; exact hj)])
        (by rw [htermlen]; omega)
        hwfCond (by rw [← hlc]; omega)
    have hcondEval : V2.evalExpr st 0 (.tmp cond) = some cw := hc
    obtain ⟨frc, hmrc, _hgasCond⟩ := materialise_runs_of_cleanHalt (prog := prog) sloadChg
      (recomputeFuel prog) st 0 (.tmp cond) cw frT hcondMatDec hcorr.defsSound hcorr.wellScoped
      hcorr.storage (by nofun) (by nofun) hcorr.memAgree hcondEval hch hstkCond
    -- forward clean-halt across the cond materialise.
    have hcsC : CleanHaltsNonException frc := cleanHaltsNonException_forward hch hmrc.runs
    -- (2) DECODE BUNDLE for the branch epilogue, `frc`-relative (exactly `sim_term_edge_branch_lowered`).
    have hfrcpc : frc.exec.pc = UInt32.ofNat (termOf prog L + lc) := by
      rw [hmrc.pc, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt, ofNat_add', ← hlc]
    have hfrccode : frc.exec.executionEnv.code = lower prog := by rw [hmrc.code]; exact hcorr.code_eq
    have hdpushT : decode frc.exec.executionEnv.code frc.exec.pc
        = some (.Push .PUSH4, some (thenW, 4)) := by
      rw [hfrccode, hfrcpc]
      exact term_dest_decode prog L b lc thenOff hbt
        (by intro j hj; rw [hemitT]
            rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [hedlen] at hj; omega)]
            rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [hedlen] at hj; omega)]
            rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [hedlen] at hj; omega)]
            rw [List.getElem?_append_right (by rw [← hlc]; omega), ← hlc, show lc + j - lc = j from by omega])
        (by rw [htermlen, hedlen]; omega) (by omega)
    have hdjumpi : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 5)
        = some (.Smsf .JUMPI, .none) := by
      rw [hfrccode, hfrcpc, ofNat_add',
          show termOf prog L + lc + 5 = termOf prog L + (lc + 5) from by omega]
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[lc + 5]? = some Byte.jumpi := by
        rw [hemitT]
        rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; omega)]
        rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; omega)]
        rw [List.getElem?_append_right (by simp only [List.length_append, hedlen, ← hlc]; omega)]
        simp only [List.length_append, hedlen, ← hlc, show lc + 5 - (lc + 5) = 0 from by omega]
        rfl
      exact decode_at_term_nonpush prog L b (lc + 5) Byte.jumpi hbt (by rw [htermlen]; omega)
        hbyte0 (by omega) (by decide)
    have hdpushE : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 6)
        = some (.Push .PUSH4, some (elseW, 4)) := by
      rw [hfrccode, hfrcpc, ofNat_add',
          show termOf prog L + lc + 6 = termOf prog L + (lc + 6) from by omega]
      exact term_dest_decode prog L b (lc + 6) elseOff hbt
        (by intro j hj
            have hjlen : j < 5 := by rw [hedlen] at hj; exact hj
            rw [hemitT]
            rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen, ← hlc]; omega)]
            rw [List.getElem?_append_right (by simp only [List.length_append, List.length_singleton, hedlen, ← hlc]; omega)]
            simp only [List.length_append, List.length_singleton, hedlen, ← hlc,
              show lc + 6 + j - (lc + 5 + 1) = j from by omega])
        (by rw [htermlen, hedlen]; omega) (by omega)
    have hdjump : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 6 + UInt32.ofNat 5)
        = some (.Smsf .JUMP, .none) := by
      rw [hfrccode, hfrcpc, ofNat_add', ofNat_add',
          show termOf prog L + lc + 6 + 5 = termOf prog L + (lc + 11) from by omega]
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[lc + 11]? = some Byte.jump := by
        rw [hemitT]
        rw [List.getElem?_append_right (by simp only [List.length_append, List.length_singleton, hedlen, ← hlc]; omega)]
        simp only [List.length_append, List.length_singleton, hedlen, ← hlc,
          show lc + 11 - (lc + 5 + 1 + 5) = 0 from by omega]
        rfl
      exact decode_at_term_nonpush prog L b (lc + 11) Byte.jump hbt (by rw [htermlen]; omega)
        hbyte0 (by omega) (by decide)
    have hdjdT : decode (lower prog) (UInt32.ofNat thenOff) = some (.Smsf .JUMPDEST, .none) :=
      decode_at_block_offset_jumpdest prog thenL bthen hbthen (by rw [← hthenoff]; omega)
    have hdjdE : decode (lower prog) (UInt32.ofNat elseOff) = some (.Smsf .JUMPDEST, .none) :=
      decode_at_block_offset_jumpdest prog elseL belse hbelse (by rw [← helseoff]; omega)
    have hthenword : thenW.toUInt32? = some (UInt32.ofNat thenOff) := ofNatMod_toUInt32? thenOff
    have helseword : elseW.toUInt32? = some (UInt32.ofNat elseOff) := ofNatMod_toUInt32? elseOff
    -- materialise-endpoint facts (`frc` carries `cw` on top of `frT`'s empty stack).
    have hfrcstk : frc.exec.stack = cw :: [] := by rw [hmrc.stack, hcorr.stack_nil]; rfl
    have hfrcmod : frc.exec.executionEnv.canModifyState = true := by
      rw [hmrc.canMod]; exact hcorr.can_modify
    have hfrcstore : ∀ k, selfStorage frc k = st.world k := by
      intro k; rw [hmrc.storage k]; exact hcorr.storage k
    have hfrcmem : MemRealises prog st frc :=
      hcorr.memAgree.transport hmrc.memBytes hmrc.memActive
    have hfrcvalid : frc.validJumps = validJumpDests (lower prog) 0 := by
      rw [hmrc.validJumps]; exact hcorr.validJumps_lower
    -- (3) step: PUSH4 thenOff at `frc`.
    have hstk1 : frc.exec.stack.size + 1 ≤ 1024 := by rw [hfrcstk]; show (1:ℕ)+1≤1024; omega
    have hgpushT : 3 ≤ frc.exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt frc .PUSH4 thenW 4 hcsC (by decide)
        hdpushT (by decide) (by decide) hstk1).1
      have hvl : GasConstants.Gverylow = 3 := rfl; omega
    have hpushT : Runs frc (pushFrameW frc thenW 4) :=
      runs_push frc .PUSH4 thenW 4 (by nofun) hdpushT rfl rfl hgpushT hstk1
    set frp := pushFrameW frc thenW 4 with hfrp
    have hfrpcode : frp.exec.executionEnv.code = frc.exec.executionEnv.code := rfl
    have hfrppc : frp.exec.pc = frc.exec.pc + UInt32.ofNat 5 := by
      show frc.exec.pc + ((4 : UInt8) + 1).toUInt32 = _
      rw [show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide]
    have hfrpstk : frp.exec.stack = thenW :: cw :: [] := by
      show frc.exec.stack.push thenW = _; rw [hfrcstk]; rfl
    have hfrpjidec : decode frp.exec.executionEnv.code frp.exec.pc = some (.Smsf .JUMPI, .none) := by
      rw [hfrpcode, hfrppc]; exact hdjumpi
    have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; show (2:ℕ)≤1024; omega
    have hcsP : CleanHaltsNonException frp := cleanHaltsNonException_forward hcsC hpushT
    -- (4) case-split on the runtime condition `cw`.
    by_cases hcw : cw = 0
    · -- ELSE arm: JUMPI falls through to `PUSH4 elseOff ; JUMP` → `elseL`.
      subst hcw
      -- JUMPI gas brick (fall-through), from `hcsP`.
      have hgjumpi : GasConstants.Ghigh ≤ frp.exec.gasAvailable.toNat :=
        (CleanHaltExtract.next_jumpi_fallthrough_of_cleanHalt frp thenW ([] : Stack Word) hcsP
          hfrpjidec hfrpstk hfrpsz).1
      have hfall : Runs frp (jumpiFallthroughFrame frp ([] : Stack Word)) :=
        runs_jumpi_fallthrough frp thenW ([] : Stack Word) hfrpjidec hfrpstk hfrpsz hgjumpi
      set gff := jumpiFallthroughFrame frp ([] : Stack Word) with hgff
      have hgffcode : gff.exec.executionEnv.code = lower prog := by
        rw [hgff, jumpiFallthroughFrame_code, hfrpcode]; exact hfrccode
      have hgffstk : gff.exec.stack = [] := by rw [hgff, jumpiFallthroughFrame_stack]
      have hgffmod : gff.exec.executionEnv.canModifyState = true := by
        rw [hgff, jumpiFallthroughFrame_canMod]
        show (pushFrameW frc thenW 4).exec.executionEnv.canModifyState = true
        rw [show (pushFrameW frc thenW 4).exec.executionEnv.canModifyState
              = frc.exec.executionEnv.canModifyState from rfl]; exact hfrcmod
      have hgffstore : ∀ k, selfStorage gff k = st.world k := by
        intro k; rw [hgff, jumpiFallthroughFrame_selfStorage]
        show selfStorage frp k = st.world k
        show selfStorage (pushFrameW frc thenW 4) k = st.world k
        rw [pushFrameW_selfStorage]; exact hfrcstore k
      have hgffmem : MemRealises prog st gff :=
        hfrcmem.transport
          (by rw [hgff, jumpiFallthroughFrame_memory, hfrp, pushFrameW_memory])
          (by rw [hgff, jumpiFallthroughFrame_activeWords, hfrp, pushFrameW_activeWords])
      have hgffvalid : gff.validJumps = validJumpDests (lower prog) 0 := by
        rw [hgff, jumpiFallthroughFrame_validJumps]
        show frp.validJumps = _; rw [hfrp, pushFrameW_validJumps]; exact hfrcvalid
      have hgffpc : gff.exec.pc = frc.exec.pc + UInt32.ofNat 6 := by
        rw [hgff, jumpiFallthroughFrame_pc, hfrppc]
        rw [show (UInt32.ofNat 6) = UInt32.ofNat 5 + 1 from by decide]; ac_rfl
      have hdpushE' : decode gff.exec.executionEnv.code gff.exec.pc
          = some (.Push .PUSH4, some (elseW, 4)) := by rw [hgffcode, hgffpc, ← hfrccode]; exact hdpushE
      have hdjump' : decode gff.exec.executionEnv.code (gff.exec.pc + UInt32.ofNat 5)
          = some (.Smsf .JUMP, .none) := by rw [hgffcode, hgffpc, ← hfrccode]; exact hdjump
      -- forward clean-halt across the JUMPI fall-through.
      have hcsG : CleanHaltsNonException gff := cleanHaltsNonException_forward hcsP hfall
      -- REUSE the jump-arm landing for `elseL`: PUSH4 elseOff ; JUMP.
      set new_pc := UInt32.ofNat elseOff with hnewE
      have hgffstk1 : gff.exec.stack.size + 1 ≤ 1024 := by rw [hgffstk]; show (0:ℕ)+1≤1024; omega
      have hgpushE : 3 ≤ gff.exec.gasAvailable.toNat := by
        have := (CleanHaltExtract.next_push_of_cleanHalt gff .PUSH4 elseW 4 hcsG (by decide)
          hdpushE' (by decide) (by decide) hgffstk1).1
        have hvl : GasConstants.Gverylow = 3 := rfl; omega
      have hpushE : Runs gff (pushFrameW gff elseW 4) :=
        runs_push gff .PUSH4 elseW 4 (by nofun) hdpushE' rfl rfl hgpushE hgffstk1
      set gfp := pushFrameW gff elseW 4 with hgfp
      have hgfpcode : gfp.exec.executionEnv.code = gff.exec.executionEnv.code := rfl
      have hgfppc : gfp.exec.pc = gff.exec.pc + UInt32.ofNat 5 := by
        show gff.exec.pc + ((4 : UInt8) + 1).toUInt32 = _
        rw [show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide]
      have hgfpstk : gfp.exec.stack = elseW :: gff.exec.stack := rfl
      have hgfpjdec : decode gfp.exec.executionEnv.code gfp.exec.pc = some (.Smsf .JUMP, .none) := by
        rw [hgfpcode, hgfppc]; exact hdjump'
      have hgfpsz : gfp.exec.stack.size ≤ 1024 := by
        rw [hgfpstk, hgffstk]; show (1:ℕ) ≤ 1024; omega
      have hgetdest : gfp.get_dest elseW = some new_pc := by
        refine Frame.get_dest_of_mem _ helseword ?_
        show new_pc ∈ gfp.validJumps
        rw [hgfp, pushFrameW_validJumps, hgffvalid, hnewE]
        simpa using block_offset_validJump prog elseL helselt
      have hcsGP : CleanHaltsNonException gfp := cleanHaltsNonException_forward hcsG hpushE
      have hgjumpE : GasConstants.Gmid ≤ gfp.exec.gasAvailable.toNat :=
        (CleanHaltExtract.next_jump_of_cleanHalt gfp elseW new_pc gff.exec.stack hcsGP
          hgfpjdec hgfpstk hgfpsz hgetdest).1
      have hjumpE : Runs gfp (jumpFrame gfp GasConstants.Gmid new_pc gff.exec.stack) :=
        runs_jump gfp elseW new_pc gff.exec.stack hgfpjdec hgfpstk hgfpsz hgjumpE hgetdest
      set fj := jumpFrame gfp GasConstants.Gmid new_pc gff.exec.stack with hfj
      have hfjpc : fj.exec.pc = UInt32.ofNat elseOff := rfl
      have hfjcode : fj.exec.executionEnv.code = lower prog := by
        rw [hfj, jumpFrame_code, hgfpcode]; exact hgffcode
      have hfjstk : fj.exec.stack = [] := by rw [hfj, jumpFrame_stack]; exact hgffstk
      have hfjmod : fj.exec.executionEnv.canModifyState = true := by
        rw [hfj, jumpFrame_canMod]
        show gff.exec.executionEnv.canModifyState = true; exact hgffmod
      have hfjstore : ∀ k, selfStorage fj k = st.world k := by
        intro k; rw [hfj, jumpFrame_selfStorage]; exact hgffstore k
      have hfjdec : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
        rw [hfjcode, hfjpc]; exact hdjdE
      have hfjmem : MemRealises prog st fj :=
        hgffmem.transport
          (by rw [hfj, jumpFrame_memory, hgfp, pushFrameW_memory])
          (by rw [hfj, jumpFrame_activeWords, hgfp, pushFrameW_activeWords])
      have hfjvalid : fj.validJumps = validJumpDests fj.exec.executionEnv.code 0 := by
        rw [hfjcode, hfj, jumpFrame_validJumps, hgfp, pushFrameW_validJumps]; exact hgffvalid
      have hfrun : Runs frT fj :=
        (((hmrc.runs.trans hpushT).trans hfall).trans hpushE).trans hjumpE
      have hcsJ : CleanHaltsNonException fj := cleanHaltsNonException_forward hch hfrun
      have hfjsz : fj.exec.stack.size ≤ 1024 := by rw [hfjstk]; show (0:ℕ)≤1024; omega
      have hgjd : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat :=
        (CleanHaltExtract.next_jumpdest_of_cleanHalt fj hcsJ hfjdec hfjsz).1
      exact ⟨frc, hmrc, hgpushT, hgjumpi, fun hcontra => absurd rfl hcontra,
        fun _ => ⟨hgpushE, hgjumpE, hgjd⟩⟩
    · -- THEN arm: JUMPI taken jumps to `thenL`'s JUMPDEST.
      set new_pc := UInt32.ofNat thenOff with hnewT
      have hgetdest : frp.get_dest thenW = some new_pc := by
        refine Frame.get_dest_of_mem _ hthenword ?_
        show new_pc ∈ frp.validJumps
        rw [hfrp, pushFrameW_validJumps, hfrcvalid, hnewT]
        simpa using block_offset_validJump prog thenL hthenlt
      -- JUMPI gas brick (taken), from `hcsP`.
      have hgjumpi : GasConstants.Ghigh ≤ frp.exec.gasAvailable.toNat :=
        (CleanHaltExtract.next_jumpi_taken_of_cleanHalt frp thenW cw new_pc ([] : Stack Word) hcsP
          hfrpjidec hfrpstk hfrpsz hcw hgetdest).1
      have htaken : Runs frp (jumpFrame frp GasConstants.Ghigh new_pc ([] : Stack Word)) :=
        runs_jumpi_taken frp thenW cw new_pc ([] : Stack Word) hfrpjidec hfrpstk hfrpsz hgjumpi hcw hgetdest
      set fj := jumpFrame frp GasConstants.Ghigh new_pc ([] : Stack Word) with hfj
      have hfjpc : fj.exec.pc = new_pc := rfl
      have hfjcode : fj.exec.executionEnv.code = lower prog := by
        rw [hfj, jumpFrame_code, hfrpcode]; exact hfrccode
      have hfjstk : fj.exec.stack = [] := by rw [hfj, jumpFrame_stack]
      have hfjmod : fj.exec.executionEnv.canModifyState = true := by
        rw [hfj, jumpFrame_canMod]
        show (pushFrameW frc thenW 4).exec.executionEnv.canModifyState = true
        rw [show (pushFrameW frc thenW 4).exec.executionEnv.canModifyState
              = frc.exec.executionEnv.canModifyState from rfl]; exact hfrcmod
      have hfjstore : ∀ k, selfStorage fj k = st.world k := by
        intro k; rw [hfj, jumpFrame_selfStorage]
        show selfStorage (pushFrameW frc thenW 4) k = st.world k
        rw [pushFrameW_selfStorage]; exact hfrcstore k
      have hfjdec : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
        rw [hfjcode, hfjpc, hnewT]; exact hdjdT
      have hfjmem : MemRealises prog st fj :=
        hfrcmem.transport
          (by rw [hfj, jumpFrame_memory, hfrp, pushFrameW_memory])
          (by rw [hfj, jumpFrame_activeWords, hfrp, pushFrameW_activeWords])
      have hfjvalid : fj.validJumps = validJumpDests fj.exec.executionEnv.code 0 := by
        rw [hfjcode, hfj, jumpFrame_validJumps, hfrp, pushFrameW_validJumps]; exact hfrcvalid
      have hfrun : Runs frT fj := (hmrc.runs.trans hpushT).trans htaken
      have hcsJ : CleanHaltsNonException fj := cleanHaltsNonException_forward hch hfrun
      have hfjsz : fj.exec.stack.size ≤ 1024 := by rw [hfjstk]; show (0:ℕ)≤1024; omega
      have hgjd : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat :=
        (CleanHaltExtract.next_jumpdest_of_cleanHalt fj hcsJ hfjdec hfjsz).1
      exact ⟨frc, hmrc, hgpushT, hgjumpi, fun _ => hgjd, fun hcontra => absurd hcontra hcw⟩

-- Build-enforced axiom-cleanliness: `termTies'_of_walk` and `runs_kind` depend only on
-- `[propext, Classical.choice, Quot.sound]` (no `sorry`/`native_decide`); every gas guard,
-- epilogue decode, and self-presence bridge is derived, and `CallPreservesSelf` is discharged
-- from `hprec` via the axiom-clean `callPreservesSelf_modGuards`.

-- **R6 — the boundary walk** (`runs_atReachableBoundary`) is RELOCATED below its wiring bricks
-- (`atReachableBoundaryVJ_entry` / `atReachableBoundaryVJ_step` / `atReachableBoundaryVJ_call`
-- / `atReachableBoundaryVJ_of_runs`), which are defined later in this file. Statement FIXED
-- there with the B1/B2 side conditions; see the `§ R6 status` block and the theorem itself.

/-! #### R7 machinery — the `driveLog` accumulator homomorphism (spine-owned)

`driveLog`'s three accumulators are WRITE-ONLY until the final `.inr []` read: every
recursive call only appends (gas/sload append a singleton, `recordCall` appends at the
tail). So a run from a nonempty seed is the empty-seed run with the seeds prepended to
every recorded stream. This is the linchpin of the R7 preservation family: it lets each
step lemma peel the recorded head off the empty-seed restart. -/

/-- `recordCall` appends its record at the tail, so prepending an accumulator commutes
with it: `recordCall pending result (c0 ++ x) = c0 ++ recordCall pending result x` at
`x = []`. -/
private theorem recordCall_append (pending : Pending) (result : FrameResult)
    (c0 : List CallRecord) :
    recordCall pending result c0 = c0 ++ recordCall pending result [] := by
  cases pending with
  | call pd => simp [recordCall]
  | create _ => simp [recordCall]

/-- **The accumulator homomorphism of `driveLog`.** Running from a nonempty seed
`(g0, s0, c0)` is the empty-seed run with the seeds prepended to each recorded stream. By
induction on fuel, branch-for-branch as `driveLog_drive`; the recording branches shift by
`List.append_assoc`, every other branch threads the IH with the seeds unchanged. -/
private theorem driveLog_acc_hom :
    ∀ (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (g0 : List Word) (s0 : List Nat) (c0 : List CallRecord),
      driveLog fuel stack state g0 s0 c0
        = (driveLog fuel stack state [] [] []).map
            (fun x => (x.1, g0 ++ x.2.1, s0 ++ x.2.2.1, c0 ++ x.2.2.2)) := by
  intro fuel
  induction fuel with
  | zero => intro stack state g0 s0 c0; rfl
  | succ n ih =>
    intro stack state g0 s0 c0
    unfold driveLog
    cases state with
    | inr result =>
      dsimp only
      cases stack with
      | nil => simp [Except.map]
      | cons pending rest =>
        dsimp only
        cases hres : pending.resume result with
        | ok parent =>
          dsimp only [hres]
          split_ifs with hre
          · -- `rest.isEmpty`: the top-level CALL record fires (old proof body verbatim).
            rw [ih rest (.inl parent) g0 s0 (recordCall pending result c0),
                ih rest (.inl parent) [] [] (recordCall pending result [])]
            cases hb : driveLog n rest (.inl parent) [] [] [] with
            | error e => simp [Except.map]
            | ok val =>
              simp [Except.map, recordCall_append pending result c0, List.append_assoc]
          · -- `rest` nonempty (descended callee's inner CALL): the record is a gated no-op,
            -- the callAcc is threaded unchanged — the append-homomorphism at an unchanged
            -- accumulator (identical shape to the `halted` arm below).
            rw [ih rest (.inl parent) g0 s0 c0]
        | error e =>
          dsimp only [hres]
          split_ifs with hre
          · rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0 s0
                  (recordCall pending result c0),
                ih rest (.inr (endFrame pending.frame (.exception e))) [] []
                  (recordCall pending result [])]
            cases hb : driveLog n rest (.inr (endFrame pending.frame (.exception e))) [] [] [] with
            | error e' => simp [Except.map]
            | ok val =>
              simp [Except.map, recordCall_append pending result c0, List.append_assoc]
          · rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0 s0 c0]
    | inl current =>
      dsimp only
      cases hstep : stepFrame current with
      | next exec =>
        dsimp only [hstep]
        split_ifs with hc1 hc2
        · rw [ih stack (.inl { current with exec := exec })
                (g0 ++ [UInt256.ofUInt64 exec.gasAvailable]) s0 c0,
              ih stack (.inl { current with exec := exec })
                ([] ++ [UInt256.ofUInt64 exec.gasAvailable]) [] []]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 (s0 ++ [sloadWarmthOf current]) c0,
              ih stack (.inl { current with exec := exec }) [] ([] ++ [sloadWarmthOf current]) []]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 s0 c0]
      | halted halt =>
        dsimp only [hstep]
        rw [ih stack (.inr (endFrame current halt)) g0 s0 c0]
      | needsCall params pending =>
        dsimp only [hstep]
        cases hbc : beginCall params with
        | inl child => dsimp only [hbc]; rw [ih (.call pending :: stack) (.inl child) g0 s0 c0]
        | inr result =>
          dsimp only [hbc]; rw [ih (.call pending :: stack) (.inr (.call result)) g0 s0 c0]
      | needsCreate params pending =>
        dsimp only [hstep]
        rw [ih (.create pending :: stack) (.inl (beginCreate params)) g0 s0 c0]

/-- The gas-op gate and the sload-op gate are mutually exclusive: a frame decoding to
`SLOAD` does not decode to `GAS`. Lets R7c know the gas-`if` in `driveLog` fails first. -/
private theorem isGasOp_false_of_isSloadOp {fr : Frame} (h : isSloadOp fr = true) :
    isGasOp fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.Smsf .SLOAD := by simpa [isSloadOp] using h
  simp only [isGasOp, h']
  decide
/-! ### R6 status — the geometry track's findings (Track A / the `hrb` residue)

**R6 WITHOUT a size side condition is REFUTABLE**, so its statement above now carries
`hne : 0 < prog.blocks.size` (blocker B1). The remaining side conditions are pinned below as
real, machine-checked lemmas (no `sorry`, no weakening of R6 itself — R6's own `sorry` above is
left untouched; these are the honest partial the geometry track lands).

* **Blocker B1 — the zero-block program (a CONCRETE counterexample, `not_runs_atReachableBoundary`), NOW FIXED on the statement.**
  For `prog.blocks = #[]`, `flatBytes prog = []` so `(flatBytes prog).length = 0`. `beginCall`
  still returns `.inl fr₀` (the `.Code` branch is total, pc `0`), and `Runs.refl fr₀` reaches
  `fr₀`, yet `AtReachableBoundary` demands `boundary < 0` — false. R6 therefore needs
  `0 < prog.blocks.size` on its statement (now added as `hne`); the refutation below proves R6's
  exact side-condition-free `∀`-form is false, justifying `hne`.
* **Blocker B2 — the oversized program / pc wrap.** The engine pc is `UInt32`, so every reachable
  boundary is `< 2 ^ 32`; but `ReachesBoundary`/`validJumpDests` are `Nat` walks that, for
  `(flatBytes prog).length > 2 ^ 32`, reach boundaries `≥ 2 ^ 32`. Matching the `Nat` walk back to
  the `UInt32` pc (taken-jump arm) and the no-wrap of the sequential/CALL advance both reduce to
  the program-size bound `(flatBytes prog).length ≤ 2 ^ 32` — natural (offsets are emitted as
  4-byte `PUSH4`) but absent from the statement and not derivable for a schematic `prog`.

The reusable geometry the `Runs`-induction is assembled from is landed green below:
`lower_size_eq`, the nonemptiness brick `flatBytes_length_pos` (→ B1's positive half), the entry
seed `atReachableBoundaryVJ_entry` (BASE, under `0 < prog.blocks.size`), and the `Runs`-induction
combinator `atReachableBoundaryVJ_of_runs` threading the two edge lemmas
`atReachableBoundaryVJ_step` / `atReachableBoundaryVJ_call` (whose only residue is the STEP-PC
dispatch walk + NEXT-IN-RANGE terminal-op geometry + CALL-site inversion — the three engine bricks).
-/

/-- The zero-block witness program: `flatBytes` is `[]`, so no boundary is in range. -/
def emptyProg : Lir.Program := { blocks := #[], entry := ⟨0⟩ }

/-- A minimal code-call into `lower emptyProg` (every field defaulted; only `codeSource` matters):
`beginCall` on it takes the total `.Code` branch, so it produces an `.inl` entry frame at pc `0`. -/
def emptyParams : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := ∅, originalAccounts := ∅, substate := default,
    caller := 0, origin := 0, recipient := 0,
    codeSource := .Code (lower emptyProg), gas := 0, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-- **Blocker B1, machine-checked: R6's exact `∀`-form is FALSE.** The zero-block program
`emptyProg` entered by `emptyParams` (`beginCall = .inl _`, `Runs.refl` reaches the entry frame)
has NO reachable in-range boundary (`(flatBytes emptyProg).length = 0`), so `AtReachableBoundary`
cannot hold at the entry frame. Hence R6 needs `0 < prog.blocks.size` on its statement (the honest
side condition the geometry track surfaces — mirrors `not_defsSound_stale`, the refutation is the
point). -/
theorem not_runs_atReachableBoundary :
    ¬ (∀ (prog : Lir.Program) (params : CallParams) (fr₀ : Frame),
        beginCall params = .inl fr₀ →
        params.codeSource = .Code (lower prog) →
        ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr') := by
  intro H
  have hbc : beginCall emptyParams = .inl (codeFrame emptyParams (lower emptyProg)) :=
    beginCall_code emptyParams (lower emptyProg) rfl
  have hrb := H emptyProg emptyParams _ hbc rfl _ (Runs.refl _)
  obtain ⟨boundary, _, _, _, hlt, _⟩ := hrb
  have hlen : (Lir.flatBytes emptyProg).length = 0 := by simp [Lir.flatBytes, emptyProg]
  omega

/-- `(lower prog).size` is the length of the flat byte list (`lower` wraps `flatBytes` in a
`ByteArray`). The one-step bridge between the `ByteArray`-level engine bound (`j < c.size`, e.g.
from `reachesBoundary_of_mem_validJumpDests`) and the `List`-level range field of
`AtReachableBoundary` (`boundary < (flatBytes prog).length`). -/
theorem lower_size_eq (prog : Lir.Program) : (lower prog).size = (Lir.flatBytes prog).length := by
  rw [Lir.lower_eq_flatBytes]; simp [ByteArray.size]

/-- **The lowered program is non-empty when the CFG is.** Each block contributes at least its
leading `JUMPDEST` byte, so a non-empty block array gives a non-empty `flatBytes`. The positive
half of blocker B1 (the entry seed's `0 < length` field). -/
theorem flatBytes_length_pos (prog : Lir.Program) (h : 0 < prog.blocks.size) :
    0 < (Lir.flatBytes prog).length := by
  unfold Lir.flatBytes
  have hne : prog.blocks.toList ≠ [] := by
    intro hnil
    have : prog.blocks.toList.length = 0 := by rw [hnil]; rfl
    rw [Array.length_toList] at this; omega
  cases hb : prog.blocks.toList with
  | nil => exact absurd hb hne
  | cons b rest =>
    rw [List.flatMap_cons, List.cons_append, List.length_cons]
    omega

/-- **BASE — the entry frame sits at a reachable in-range boundary.** For a code call into
`lower prog` whose CFG is non-empty (blocker B1's side condition), the entry frame
(`= codeFrame params (lower prog)`) is at pc `0`, which is `ReachesBoundary … 0 0` (`.refl`) and
in range (`flatBytes_length_pos`) — the seed of the `Runs`-induction. -/
theorem atReachableBoundary_entry {prog : Lir.Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hne : 0 < prog.blocks.size) :
    AtReachableBoundary prog fr₀ := by
  have hfr : fr₀ = codeFrame params (lower prog) := by
    have hc : beginCall params = .inl (codeFrame params (lower prog)) :=
      beginCall_code params (lower prog) hcode
    exact (Sum.inl.injEq _ _).mp (hbegin.symm.trans hc)
  refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr]; exact codeFrame_code params (lower prog)
  · rw [hfr, codeFrame_pc]; rfl
  · exact .refl 0
  · exact flatBytes_length_pos prog hne
  · decide

/-- **The strengthened boundary invariant (in-file).** `AtReachableBoundary` PLUS the
`Frame.validJumps` fact it omits — that the frame's jump table is exactly
`validJumpDests (lower prog) 0`. The taken-JUMP edge needs this: the landing pc is a *member*
of `validJumps`, and to re-establish `ReachesBoundary` from it (via
`reachesBoundary_of_mem_validJumpDests`) the table must be pinned to `validJumpDests`, which
`AtReachableBoundary` (Modellable.lean:407) does not carry. So the naive
`AtReachableBoundary`-only combinator is a **dead route** (the taken-jump arm is unprovable
without this conjunct); R6 threads `AtReachableBoundaryVJ` instead. `validJumps` is a `Frame`
field set to `validJumpDests code 0` at frame creation (`codeFrame_validJumps`) and untouched
by every `StepsTo`/`CallReturns` (only `exec` moves), so it threads cleanly through the walk. -/
def AtReachableBoundaryVJ (prog : Lir.Program) (fr : Frame) : Prop :=
  AtReachableBoundary prog fr ∧ fr.validJumps = validJumpDests (Lir.lower prog) 0

/-- **BASE (strengthened) — the entry frame satisfies the strengthened invariant.** The
`AtReachableBoundary` half is `atReachableBoundary_entry`; the `validJumps` conjunct is
`codeFrame_validJumps` (the entry frame is `codeFrame params (lower prog)`, whose jump table is
`validJumpDests (lower prog) 0` by construction). -/
theorem atReachableBoundaryVJ_entry {prog : Lir.Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hne : 0 < prog.blocks.size) :
    AtReachableBoundaryVJ prog fr₀ := by
  have hfr : fr₀ = codeFrame params (lower prog) := by
    have hc : beginCall params = .inl (codeFrame params (lower prog)) :=
      beginCall_code params (lower prog) hcode
    exact (Sum.inl.injEq _ _).mp (hbegin.symm.trans hc)
  refine ⟨atReachableBoundary_entry hbegin hcode hne, ?_⟩
  rw [hfr, codeFrame_validJumps]

/-- **R6 STEP edge.** One `stepFrame` from a reachable in-range boundary of `lower prog` lands
at another (with the `validJumps` conjunct preserved). Everything is discharged in-file EXCEPT
two pure-engine geometry bricks whose home is a default-target file (see the R6 default-target
brief): **B-pc** (the `.next` dispatch walk: the step either advances to the sequential
successor `nextInstrPosNat b (parseInstr byte)` or lands in `validJumps`), and **B-inrange**
(the block-layout fact that a sequential-advancing instruction's successor stays in range).
The taken-jump arm is FULLY discharged here (free, via `reachesBoundary_of_mem_validJumpDests`
+ the `validJumps` conjunct). -/
theorem atReachableBoundaryVJ_step {prog : Lir.Program} {fr mid : Frame}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (h : StepsTo fr mid) (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog mid := by
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, hvj⟩ := hinv
  -- code + `validJumps` preservation (real — only `exec` moves):
  have hmcode : mid.exec.executionEnv.code = Lir.lower prog := by
    rw [stepFrame_next_execEnvAddr h.1, hcode]
  have hmvj : mid.validJumps = validJumpDests (Lir.lower prog) 0 := by
    rw [h.2]; exact hvj
  -- the boundary byte at `b` is a lowering opcode (real):
  obtain ⟨byte, hget, hop⟩ := Lir.reachable_boundary_loweringByte prog b hreach hin
  -- ── BRICK B-pc (home `LirLean/BoundaryReach.lean` / `LirLean/Engine/StepWalk.lean`) ──
  -- the `.next` `stepFrame` dispatch walk over the 16 `IsLoweringOp` arms: from the boundary
  -- `b` the successor pc is either the sequential `nextInstrPosNat b (parseInstr byte)` or a
  -- `validJumps` member (taken JUMP/JUMPI). Template `stepFrame_next_accMono`. The instance R6
  -- consumes (general statement in the default-target brief).
  have hBpc : mid.exec.pc = UInt32.ofNat (Evm.nextInstrPosNat b (Evm.parseInstr byte))
      ∨ mid.exec.pc ∈ fr.validJumps := sorry
  refine ⟨?_, hmvj⟩
  rcases hBpc with hseq | hjmp
  · -- sequential advance
    -- ── BRICK B-inrange (home `LirLean/BoundaryReach.lean` / `LirLean/Layout.lean`) ──
    -- blocks end in terminators ⇒ a sequential-advancing instruction is never the program's
    -- last, so its successor boundary stays `< (flatBytes prog).length`. SegAligned/emitBlock
    -- layout decomposition.
    have hInR : Evm.nextInstrPosNat b (Evm.parseInstr byte) < (Lir.flatBytes prog).length := sorry
    exact ⟨Evm.nextInstrPosNat b (Evm.parseInstr byte), hmcode, hseq,
      Lir.reachesBoundary_nextInstr hreach hget, hInR, lt_of_lt_of_le hInR hsize⟩
  · -- taken jump: the landing pc is a `validJumps` member ⇒ a reachable in-range boundary (FREE)
    rw [hvj] at hjmp
    obtain ⟨j, hjreach, hxj, hjlt⟩ :=
      Lir.reachesBoundary_of_mem_validJumpDests (Lir.lower prog) hjmp
    rw [lower_size_eq] at hjlt
    exact ⟨j, hmcode, by rw [hxj], hjreach, hjlt, lt_of_lt_of_le hjlt hsize⟩

/-- **R6 CALL edge.** A returning external CALL from a reachable in-range boundary of
`lower prog` resumes at another (with the `validJumps` conjunct preserved). The
`resumeAfterCall` pins (code / pc = call-site + 1 / validJumps) are discharged in-file by
unfolding; everything else is real EXCEPT two engine bricks (see the R6 default-target brief):
**B-call** (extend `stepFrame_needsCall_inv`: a `.needsCall` at a lowering-op boundary decodes
`CALL` — the only CALL-family op the lowering emits — and the pending parent frame keeps the
call-site pc and jump table), and **B-inrange** (a lowered CALL is mid-block, so its 1-byte
successor is in range). -/
theorem atReachableBoundaryVJ_call {prog : Lir.Program} {fr rf : Frame}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (h : CallReturns fr rf) (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog rf := by
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, hvj⟩ := hinv
  obtain ⟨cp, pending, child, childRes, hncall, _hEnters, _hDrive, hrf⟩ := h
  obtain ⟨byte, hget, hop⟩ := Lir.reachable_boundary_loweringByte prog b hreach hin
  -- ── BRICK B-call (home `LirLean/Engine/Descent.lean`) ──
  -- extension of `stepFrame_needsCall_inv` to the pc / jump-table / decoded-op it omits.
  have hBcall : Evm.parseInstr byte = Operation.CALL
      ∧ pending.frame.exec.pc = fr.exec.pc
      ∧ pending.frame.validJumps = fr.validJumps := sorry
  obtain ⟨hopCall, hppc, hpvj⟩ := hBcall
  -- ── BRICK B-inrange (CALL instance; same home as the STEP B-inrange) ──
  have hInR : b + 1 < (Lir.flatBytes prog).length := sorry
  -- `resumeAfterCall` pins (real, by unfolding the def):
  have hrenv : rf.exec.executionEnv = pending.frame.exec.executionEnv := by
    rw [hrf]; rfl
  have hrcode : rf.exec.executionEnv.code = Lir.lower prog := by
    rw [hrenv, (Evm.stepFrame_needsCall_inv hncall).2.2, hcode]
  have hrvj : rf.validJumps = validJumpDests (Lir.lower prog) 0 := by
    rw [hrf, show (Evm.resumeAfterCall childRes.toCallResult pending).validJumps
          = pending.frame.validJumps from rfl, hpvj, hvj]
  have hrpc : rf.exec.pc = pending.frame.exec.pc + 1 := by
    rw [hrf]; rfl
  have hbnd1 : b + 1 < 2 ^ 32 := lt_of_lt_of_le hInR hsize
  refine ⟨⟨b + 1, hrcode, ?_, ?_, hInR, hbnd1⟩, hrvj⟩
  · -- pc = ofNat (b + 1)
    rw [hrpc, hppc, hpc]; exact Lir.ofNat_add' b 1
  · -- ReachesBoundary 0 (b + 1)
    have hr := Lir.reachesBoundary_nextInstr hreach hget
    rw [hopCall] at hr
    have hnn : Evm.nextInstrPosNat b Operation.CALL = b + 1 := by
      simp [Evm.nextInstrPosNat, Evm.pushArgWidth]
    rwa [hnn] at hr

/-- **The CREATE edge is vacuous for a lowered program.** A `Runs.create` node needs
`stepFrame fr = .needsCreate …` (`CreateReturns`), which forces `currentOp fr ∈ {CREATE, CREATE2}`
(`stepFrame_needsCreate_isCreate`). But `fr` at a reachable in-range boundary decodes to an
`IsLoweringOp` opcode (`decode_reachable_boundary_loweringOp`), and the lowering emits neither
CREATE nor CREATE2 (`IsLoweringOp` is the 16-op allow-list). So the hypotheses are contradictory —
the create arm cannot arise in a lowered run, and needs no boundary-geometry brick. -/
theorem atReachableBoundaryVJ_create {prog : Lir.Program} {fr rf : Frame}
    (h : CreateReturns fr rf) (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog rf := by
  exfalso
  obtain ⟨_cp, _pending, _childRes, hncreate, _, _⟩ := h
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, _hvj⟩ := hinv
  obtain ⟨op, arg, hdecode, hlow⟩ := Lir.decode_reachable_boundary_loweringOp prog b hreach hin hbnd
  have hcoeq : currentOp fr = op := by rw [currentOp, hcode, hpc, hdecode]; rfl
  rcases stepFrame_needsCreate_isCreate hncreate with h1 | h1 <;>
    · rw [hcoeq] at h1; rw [h1] at hlow; exact absurd hlow (by decide)

/-- **The `Runs`-induction combinator (master lemma).** `AtReachableBoundaryVJ prog` is
preserved across a whole `Runs` derivation, threading through each single `StepsTo`
(`atReachableBoundaryVJ_step`), each returning external `CallReturns` (`atReachableBoundaryVJ_call`),
and each returning `CreateReturns` (`atReachableBoundaryVJ_create`, vacuous — no CREATE bytes are
emitted). The assembly of R6: seed with `atReachableBoundaryVJ_entry` (BASE), then thread the edges. -/
theorem atReachableBoundaryVJ_of_runs {prog : Lir.Program}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    {fr fr' : Frame} (hr : Runs fr fr') :
    AtReachableBoundaryVJ prog fr → AtReachableBoundaryVJ prog fr' := by
  induction hr with
  | refl _ => exact id
  | step h _ ih => exact fun hfr => ih (atReachableBoundaryVJ_step hsize h hfr)
  | call hc _ ih => exact fun hfr => ih (atReachableBoundaryVJ_call hsize hc hfr)
  | create hc _ ih => exact fun hfr => ih (atReachableBoundaryVJ_create hc hfr)

/-- **R6 — the boundary walk** (the `hrb` residue; the Track-A discharge target). Every
`Runs`-reachable frame of a `lower prog` entry sits at a reachable instruction boundary of
`lower prog` — the pc-reachability invariant that structurally discharges the no-CREATE
modellability clause (`notCreate_of_atReachableBoundary`) and scopes the future
data-segment design. One of the three substantial proofs. DERIVED-status obligation.

STATEMENT FIXED (R6 was REFUTABLE as originally stated — `not_runs_atReachableBoundary`)
with the two well-formedness side conditions the geometry track surfaced:
* B1 (`hne : 0 < prog.blocks.size`) — rules out the zero-block program the counterexample
  refutes; consumed by the entry seed. Legitimate: every real lowered program has an entry
  block, and B1 is exactly `ClosedCFG.entry_present`'s content (`entry.idx < blocks.size ⟹
  0 < blocks.size`). NOT vacuity-inducing: `beginCall` still returns `.inl fr₀`, `Runs.refl`
  still reaches the seed frame.
* B2 (`hsize : (flatBytes prog).length ≤ 2 ^ 32`) — the pc-wrap bound the taken-JUMP /
  sequential edge lemmas need to turn `boundary' < length` into the `boundary' < 2 ^ 32`
  conjunct. Legitimate: offsets are emitted as 4-byte `PUSH4`, so real programs fit the
  32-bit address space (the same bound the per-cursor `WellFormedLowered.bound_*` fields
  assert). An upper bound all real programs satisfy — not vacuity-inducing.

HONEST PARTIAL (re-architected): the reduction is now REAL and fully assembled here from the
strengthened invariant `AtReachableBoundaryVJ` (`AtReachableBoundary` + the `validJumps`
conjunct the taken-jump edge needs; the old `AtReachableBoundary`-only route was a DEAD end).
Seed = `atReachableBoundaryVJ_entry` (B1), combinator = `atReachableBoundaryVJ_of_runs`, edges
= `atReachableBoundaryVJ_step` / `atReachableBoundaryVJ_call`. Everything is discharged with
real proofs EXCEPT three pure-engine geometry bricks (marked `sorry` inside the two edges),
whose home is a default-target file OUTSIDE this task's edit surface:
* **B-pc** (`BoundaryReach.lean` / `Engine/StepWalk.lean`) — the `.next` `stepFrame` dispatch
  walk: from a lowering-op boundary the successor pc is the sequential `nextInstrPosNat` OR a
  `validJumps` member. Template `stepFrame_next_accMono`.
* **B-inrange** (`BoundaryReach.lean` / `Layout.lean`) — blocks end in terminators, so a
  sequential-advancing (or CALL) instruction's successor boundary stays `< length`. The
  hardest brick (SegAligned/emitBlock layout decomposition).
* **B-call** (`Engine/Descent.lean`) — extend `stepFrame_needsCall_inv` with the decoded op
  (`= CALL`), the pending-frame pc (`= call-site pc`) and jump table (`= call-site validJumps`).
Once these three land, R6 is axiom-clean (`[propext, Classical.choice, Quot.sound]`) by citing
them. B2 (`hsize`) is threaded into both edges (the `boundary' < length ⟹ boundary' < 2^32`
reconciliation and the taken-jump/`UInt32.ofNat` no-wrap). -/
theorem runs_atReachableBoundary {prog : Lir.Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hne : 0 < prog.blocks.size)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr' := by
  intro fr' hr
  exact (atReachableBoundaryVJ_of_runs hsize hr
    (atReachableBoundaryVJ_entry hbegin hcode hne)).1

/-! ### R7 — the recorder-coupling edge lemmas (entry + the four preservation edges)

These are what make `RecorderCoupled` a THREADABLE invariant: established once at entry,
preserved across every top-level step shape the drive walk takes. All DERIVED-status. -/

/-- **R7a — entry coupling**: a successful `runWithLog` couples the entry frame to the
WHOLE log (all three suffixes = the full streams; prefixes `[]`). Near-`rfl` from
unfolding `runWithLog` (its `driveLog` equation IS the restart equation at `fr₀`). -/
theorem recorderCoupled_entry {params : CallParams} {log : RunLog} {fr₀ : Frame}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀) :
    RecorderCoupled log fr₀ log.gas log.sloads log.calls := by
  unfold runWithLog at hrun
  rw [hbegin] at hrun
  dsimp only at hrun
  cases hdl : driveLog (seedFuel params.gas) [] (.inl fr₀) [] [] [] with
  | error e => rw [hdl] at hrun; simp at hrun
  | ok triple =>
    obtain ⟨r, gas, sloads, calls⟩ := triple
    rw [hdl] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    exact ⟨⟨seedFuel params.gas, hdl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩

/-- **R7b — the GAS step consumes the gas-suffix head**: a top-level `.next` step at a GAS
op advances the coupling to the tail and pins the consumed head to the post-charge
`gasAvailable` (exactly what `driveLog` recorded at this step). -/
theorem recorderCoupled_step_gas {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {g : Word} {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr (g :: gS) sS cS)
    (hgas : isGasOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS
    ∧ g = UInt256.ofUInt64 exec.gasAvailable := by
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hgas, List.isEmpty_nil, Bool.and_true, List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec })
      [UInt256.ofUInt64 exec.gasAvailable] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', UInt256.ofUInt64 exec.gasAvailable :: gS', sS', cS')
          : Except ExecutionException (FrameResult × List Word × List Nat × List CallRecord))
          = .ok (log.observable, g :: gS, sS, cS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgc hf5
      injection hf5 with hs hc
      injection hgc with hgeq hgSeq
      subst hobs; subst hgSeq; subst hs; subst hc
      refine ⟨⟨⟨m, hX⟩, ?_, hsp, hcpp⟩, hgeq.symm⟩
      obtain ⟨pre, hpre⟩ := hgp
      exact ⟨pre ++ [g], by rw [hpre, List.append_assoc, List.singleton_append]⟩

/-- **Gas-suffix nonemptiness at a GAS step.** If the coupling holds at `fr`, the op is
`GAS`, and the step continues (`.next exec`), the recorded gas suffix is nonempty — its
head is the datum `driveLog` is about to record. This is the *front half* of
`recorderCoupled_step_gas` (R7b), split out so `gas_suffix_head_realised` (R1) can expose
the `cons` structurally and then pin the head *value* through R7b proper. -/
private theorem gasSuffix_nonempty {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr gS sS cS)
    (hgas : isGasOp fr = true) (hstep : stepFrame fr = .next exec) :
    ∃ g gS', gS = g :: gS' := by
  obtain ⟨⟨f, hf⟩, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hgas, List.isEmpty_nil, Bool.and_true, List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec })
      [UInt256.ofUInt64 exec.gasAvailable] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', UInt256.ofUInt64 exec.gasAvailable :: gS', sS', cS')
          : Except ExecutionException (FrameResult × List Word × List Nat × List CallRecord))
          = .ok (log.observable, gS, sS, cS) := hf
      injection hf2 with hf3
      injection hf3 with _ hf4
      injection hf4 with hgc _
      exact ⟨_, _, hgc.symm⟩

/-- **R1 — the gas recorder bridge** (the riskiest obligation; the trace↔recorder
positional bridge). At a gas-assign cursor, the un-consumed gas suffix's head is the
machine GAS output at the cursor frame.

SATISFIABILITY ANALYSIS (why each hypothesis is load-bearing): the coupling's restart
equation pins `gS` to `fr`'s deterministic future; `Corr` (+ the two well-formedness side
conditions, below) pins `fr`'s pc/code to the GAS byte of `lower prog`; and the CLEAN-HALT
antecedent is what blocks the one remaining refutation — an OOG-at-GAS frame satisfies the
coupling with the run ending in an exception whose recorded suffix is `gS = []`, refuting
the head equation. Under clean halt the first restart step IS the recorded top-level GAS
read, and `driveLog` records exactly `UInt256.ofUInt64 exec.gasAvailable` of the
post-charge state (= `gasAvailable − Gbase`, the former `StmtTies` gas word — now the
`StmtTies'` gas arm — verbatim).

SIDE-CONDITION ADDITIONS (`hslotdef`/`hpcbound`, R6-style well-formedness — surfaced for
review, NOT a weakening): deriving the GAS decode from `Corr` requires that the gas assign
is actually *spilled to a slot* (`emitStmt` emits `[]` for a non-slotted `.assign t .gas`,
so the byte at the cursor would be the *next* op — the head equation is refutable without
it) and that the stash's pc range is in-bounds (`decode_gasstash`'s `+ 34 < 2^32`). Neither
is derivable from `Corr` (which pins only pc/code/stack, never the def-site byte, and never
a pc bound). Both are *exactly the sibling output conjuncts of the `StmtTies'` gas arm this
lemma feeds* (see the gas arm of `StmtTies'`), and the sole consumer
`stmtTies'_of_runWithLog` (R10a) carries `hwl : WellLowered prog`, whose `defsCons`
(`DefsConsistent`) discharges `hslotdef` while proving that very arm — so R10a has both
facts in hand at this call site. This mirrors the interface of `decode_gasstash` /
`sim_assign_gas_lowered` and of the closed `defsSoundS_preserved_step` (R0b), which takes
`DefsConsistent`. DERIVED-status obligation: never supplied. -/
theorem gas_suffix_head_realised {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {L : Label} {b : Block} {pc : Nat} {t : Tmp} {st : IRState} {fr : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t .gas))
    (hslotdef : defsOf prog t = some (.slot (slotOf t)))
    (hpcbound : pcOf prog L pc + 34 < 2 ^ 32)
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr) :
    gS.head? = some (UInt256.ofUInt64
      (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)) := by
  obtain ⟨hdecGAS, _, _⟩ :=
    decode_gasstash (Lir.toList_of_blockAt hb) hcur hslotdef hpcbound hcorr
  have hgas : isGasOp fr = true := by unfold isGasOp; rw [hdecGAS]; rfl
  have hsz : fr.exec.stack.size + 1 ≤ 1024 := by rw [hcorr.stack_nil]; simp [Stack.size]
  obtain ⟨_, hstep⟩ := Lir.CleanHaltExtract.next_gas_of_cleanHalt fr hch hdecGAS hsz
  -- `hstep : stepFrame fr = .next (gasPost fr.exec)`.
  obtain ⟨g, gS', hcons⟩ := gasSuffix_nonempty hcp hgas hstep
  rw [hcons] at hcp
  -- R7b pins the consumed head to `ofUInt64 (gasPost fr.exec).gasAvailable`.
  obtain ⟨_, hgval⟩ := recorderCoupled_step_gas hcp hgas hstep
  rw [hcons]
  show some g = _
  rw [hgval]
  -- `(gasPost fr.exec).gasAvailable = fr.exec.gasAvailable - UInt64.ofNat Gbase` (rfl: the
  -- `GAS` post-frame charges `Gbase`, `replaceStackAndIncrPC` leaves `gasAvailable`).
  rfl

/-- **R7c — the SLOAD step consumes the sload-suffix head** (the R7b twin): pins the
consumed warmth-charge to `sloadWarmthOf fr` (the PRE-step frame, as recorded). -/
theorem recorderCoupled_sload {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {n : Nat} {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr gS (n :: sS) cS)
    (hsl : isSloadOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS
    ∧ n = sloadWarmthOf fr := by
  have hng : isGasOp fr = false := isGasOp_false_of_isSloadOp hsl
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hsl, List.isEmpty_nil, Bool.and_true, Bool.false_and,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) [] [sloadWarmthOf fr] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', gS', sloadWarmthOf fr :: sS', cS')
          : Except ExecutionException (FrameResult × List Word × List Nat × List CallRecord))
          = .ok (log.observable, gS, n :: sS, cS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgSeq hf5
      injection hf5 with hsc hc
      injection hsc with hneq hsSeq
      subst hobs; subst hgSeq; subst hsSeq; subst hc
      refine ⟨⟨⟨m, hX⟩, hgp, ?_, hcpp⟩, hneq.symm⟩
      obtain ⟨pre, hpre⟩ := hsp
      exact ⟨pre ++ [n], by rw [hpre, List.append_assoc, List.singleton_append]⟩

/-- **R7d — any other top-level `.next` step preserves all three suffixes** (nothing is
recorded off the GAS/SLOAD gates). -/
theorem recorderCoupled_step_other {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr gS sS cS)
    (hng : isGasOp fr = false) (hns : isSloadOp fr = false)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS := by
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hns, List.isEmpty_nil, Bool.false_and] at hf
    exact ⟨⟨m, hf⟩, hgp, hsp, hcpp⟩

/-- **Recorder framing with a nonempty bottom stack** (the recorder-composition lemma R7e
needs). When the top segment `st` on stack `top` drains to `.ok res` (the child's black-box
run, via `drive`), running the RECORDER `driveLog` with a nonempty `bot` appended at the
bottom records NOTHING during that segment: every recording gate — gas/sload on
`stack.isEmpty`, the returning-CALL record on `rest.isEmpty` (post-gate `Spec/Recorder.lean`)
— fails because the nonempty `bot` keeps `stack`/`rest` nonempty throughout. So the
accumulator `(g0, s0, c0)` is threaded UNCHANGED up to the point `res` is delivered into
`bot`. This is the `driveLog` analogue of `drive_append_framing_lt`, with the
accumulator-invariance the `rest.isEmpty` gate buys. By induction on fuel, branch-for-branch
as `drive_append_framing_lt`; every recording gate is discharged by `hbot`. -/
private theorem driveLog_frame_nonempty (bot : List Pending) (hbot : bot.isEmpty = false)
    (g0 : List Word) (s0 : List Nat) (c0 : List CallRecord) :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∃ j, driveLog f (top ++ bot) st g0 s0 c0
          = driveLog (j + 1) bot (.inr res) g0 s0 c0 := by
  have hbne : ∀ (t : List Pending), (t ++ bot).isEmpty = false := by
    intro t; cases t with
    | nil => exact hbot
    | cons _ _ => rfl
  intro f
  induction f with
  | zero => intro top st res h; simp [drive] at h
  | succ n ih =>
    intro top st res h
    unfold drive at h
    unfold driveLog
    cases st with
    | inr result =>
      cases top with
      | nil =>
        dsimp only at h ⊢
        cases h
        exact ⟨n, rfl⟩
      | cons pending rest =>
        rw [List.cons_append]
        dsimp only at h ⊢
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h; dsimp only at h
          simp only [hres]
          split_ifs with he
          · rw [hbne rest] at he; simp at he
          · exact ih rest (.inl parent) res h
        | error e =>
          rw [hres] at h; dsimp only at h
          simp only [hres]
          split_ifs with he
          · rw [hbne rest] at he; simp at he
          · exact ih rest (.inr (endFrame pending.frame (.exception e))) res h
    | inl current =>
      dsimp only at h ⊢
      cases hstep : stepFrame current with
      | next exec =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        split_ifs with hc1 hc2
        · rw [hbne top] at hc1; simp at hc1
        · rw [hbne top] at hc2; simp at hc2
        · exact ih top (.inl { current with exec := exec }) res h
      | halted halt =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        exact ih top (.inr (endFrame current halt)) res h
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h; dsimp only at h
          dsimp only
          rw [← List.cons_append]
          exact ih (.call pending :: top) (.inl child) res h
        | inr result =>
          rw [hbc] at h; dsimp only at h
          dsimp only
          rw [← List.cons_append]
          exact ih (.call pending :: top) (.inr (.call result)) res h
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h
        dsimp only
        rw [← List.cons_append]
        exact ih (.create pending :: top) (.inl (beginCreate params)) res h

/-- **R7e — a returning external CALL consumes exactly one `CallRecord` and NO gas/sload
entries** (children are black-boxed by the recorder's gates — gas/sload by `stack.isEmpty`,
the returning-CALL record by `rest.isEmpty` — exactly as `Runs.call` black-boxes them).

RESOLVED (2026-07-03, recorder-fix) — resolution (A) taken (the Phase-3 course-correction):
the returning-CALL record in `Spec/Recorder.lean`'s delivery branch is now gated on the
resumed pending stack being empty (`rest.isEmpty`), so it fires ONLY for the top-level
program's own returning CALL, matching the gas/sload `stack.isEmpty` gates and the recorder's
docstrings. With that gate this statement is TRUE AS WRITTEN: the gate excludes a descended
callee's inner calls STRUCTURALLY (they resume on a nonempty `rest`), regardless of the child's
own call count, so the earlier "1 + child call count" escalation/asymmetry note is gone, and
`realisedCall` is faithful even when the top-level call's callee itself calls. Multiple
TOP-level calls are now handled by the positional `CallStream` (`callStreamOf` maps the WHOLE
record list, consumed head-first) — no single-call premise anywhere.

Proof: unpack the restart from `fr` (`hcp.restart`) one CALL step — `fr` descends into
`child` on the pending stack `[.call pending]` (`hstep`/`hcode`). The child terminates within
the restart's fuel (`child_ne_oof_of_framed` from the framed run's success, result reconciled
with `hcr`'s black-box `childRes` by `drive_fuel_mono`). `driveLog_frame_nonempty` then shows
the inline child records nothing on the nonempty stack, and the outer delivery (`rest = []`)
records exactly `[outerRec]` and resumes at `resumeFr`. `driveLog_acc_hom` peels that single
seeded record, exposing the restart of `resumeFr` at suffixes `(gS, sS, cS)` — the coupling. -/
theorem recorderCoupled_call {log : RunLog} {fr resumeFr : Frame}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr gS sS (rec :: cS))
    (hcr : CallReturns fr resumeFr) :
    RecorderCoupled log resumeFr gS sS cS := by
  obtain ⟨cp, pending, child, childRes, hstep, hcode, hchild, hresume⟩ := hcr
  have hcode' : beginCall cp = .inl child := hcode
  obtain ⟨⟨fuel', hrestart⟩, hgp, hsp, hcpp⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    -- Unfold the restart's first (CALL) step: `fr` descends into `child` on `[.call pending]`.
    have hdescent : driveLog (m + 1) [] (.inl fr) [] [] []
        = driveLog m (.call pending :: []) (.inl child) [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep, hcode']
    rw [hdescent] at hrestart
    -- The child terminates within fuel `m` (the framed restart succeeded).
    have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
      have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.call pending :: []) (running child) ≠ .error .OutOfFuel := by
      rw [hdrive]; simp
    have hchildm_ne : drive m [] (running child) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed m child pending [] hne
    -- Reconcile the framed child result with `hcr`'s black-box `childRes` via fuel monotonicity.
    have hchildm : drive m [] (running child) = .ok childRes := by
      have h1 := drive_fuel_mono (Nat.le_max_left m (seedFuel cp.gas)) [] (running child) hchildm_ne
      have h2 := drive_fuel_mono (Nat.le_max_right m (seedFuel cp.gas)) [] (running child)
        (by rw [hchild]; simp)
      rw [hchild] at h2
      rw [← h1, h2]
    -- Frame the recorder: the inline child records nothing; the outer delivery records `[outerRec]`.
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] []
      m [] (.inl child) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    -- Reduce the outer CALL delivery (`rest = []`): record `[outerRec]`, resume at `resumeFr`.
    have hdeliv : driveLog (j + 1) (.call pending :: []) (.inr childRes) [] [] []
        = driveLog j [] (.inl resumeFr) [] []
            [{ result := childRes.toCallResult, pending := pending }] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, List.nil_append, hresume]
    rw [hdeliv] at hrestart
    -- Peel the single seeded record via the accumulator homomorphism.
    rw [driveLog_acc_hom j [] (.inl resumeFr) [] []
      [{ result := childRes.toCallResult, pending := pending }]] at hrestart
    cases hb : driveLog j [] (.inl resumeFr) [] [] [] with
    | error e => rw [hb] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', sS'', cS''⟩ := val
      rw [hb] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ sS'',
          [{ result := childRes.toCallResult, pending := pending }] ++ cS'')
          : Except ExecutionException (FrameResult × List Word × List Nat × List CallRecord))
          = .ok (log.observable, gS, sS, rec :: cS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with hobs heq3
      injection heq3 with hgeq heq4
      injection heq4 with hseq heq5
      injection heq5 with _ hcs
      subst hobs; subst hgeq; subst hseq; subst hcs
      refine ⟨⟨j, hb⟩, hgp, hsp, ?_⟩
      obtain ⟨pre, hpre⟩ := hcpp
      exact ⟨pre ++ [rec], by rw [hpre]; simp [List.append_assoc]⟩

/-- **R7e′ — the coupling's CALL extraction** (R3's Piece-A atom; the *producing* companion of
`recorderCoupled_call`, which only consumes). At a top-level boundary frame `callFr` whose next
step is a returning external CALL (`stepFrame callFr = .needsCall cp pending`, `beginCall cp =
.inl child`), if the coupled call-suffix is `rec :: cS`, then that record is EXACTLY this CALL's
`{result := childRes.toCallResult, pending}`, the machine-side `CallReturns callFr resumeFr`
witness holds at the realised resume frame `resumeFr = resumeAfterCall childRes.toCallResult
pending`, and the coupling survives at `resumeFr` on the tail `cS`.

The `CallReturns` witness is genuinely PRODUCED here, not supplied: `child_terminates`
(`messageCall_never_outOfFuel`) gives the child's standalone seed-fuel termination
`drive (seedFuel cp.gas) [] (running child) = .ok childRes`, and `drive_fuel_mono` reconciles it
with the coupling's shared-restart-fuel child result — closing the seedFuel-vs-restart-fuel gap
that blocks reading `CallReturns` off the coupling alone (the reason `recorderCoupled_call` had to
take it as a hypothesis). The record identity is peeled from the restart equation exactly as in
`recorderCoupled_call`'s body (`driveLog_frame_nonempty` black-boxes the child, the `rest = []`
delivery records the one record, `driveLog_acc_hom` peels it), only here the head equation is
re-exposed instead of discarded. This is what makes the HEAD of `realisedCall log self`
identifiable with the realised `evmV2CallEntry` at R3's call cursor (via `realisedCall_cons`,
the positional per-record projection). -/
theorem recorderCoupled_call_extract {log : RunLog} {callFr : Frame}
    {cp : CallParams} {pending : PendingCall} {child : Frame}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS : List CallRecord}
    (hcp : RecorderCoupled log callFr gS sS (rec :: cS))
    (hstep : stepFrame callFr = .needsCall cp pending)
    (hcode : beginCall cp = .inl child) :
    ∃ childRes : FrameResult,
        CallReturns callFr (Evm.resumeAfterCall childRes.toCallResult pending)
      ∧ rec = { result := childRes.toCallResult, pending := pending }
      ∧ RecorderCoupled log (Evm.resumeAfterCall childRes.toCallResult pending) gS sS cS := by
  obtain ⟨childRes, hchild_seed⟩ := child_terminates hcode
  have hcr : CallReturns callFr (Evm.resumeAfterCall childRes.toCallResult pending) :=
    ⟨cp, pending, child, childRes, hstep, hcode, hchild_seed, rfl⟩
  refine ⟨childRes, hcr, ?_, recorderCoupled_call hcp hcr⟩
  -- The record identity: peel the restart equation (as `recorderCoupled_call`, but keep the head).
  obtain ⟨⟨fuel', hrestart⟩, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl callFr) [] [] []
        = driveLog m (.call pending :: []) (.inl child) [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep, hcode]
    rw [hdescent] at hrestart
    have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
      have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.call pending :: []) (running child) ≠ .error .OutOfFuel := by
      rw [hdrive]; simp
    have hchildm_ne : drive m [] (running child) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed m child pending [] hne
    have hchildm : drive m [] (running child) = .ok childRes := by
      have h1 := drive_fuel_mono (Nat.le_max_left m (seedFuel cp.gas)) [] (running child) hchildm_ne
      have h2 := drive_fuel_mono (Nat.le_max_right m (seedFuel cp.gas)) [] (running child)
        (by rw [hchild_seed]; simp)
      rw [hchild_seed] at h2
      rw [← h1, h2]
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] []
      m [] (.inl child) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.call pending :: []) (.inr childRes) [] [] []
        = driveLog j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] []
            [{ result := childRes.toCallResult, pending := pending }] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, List.nil_append]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] []
      [{ result := childRes.toCallResult, pending := pending }]] at hrestart
    cases hbok : driveLog j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] []
      with
    | error e => rw [hbok] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', sS'', cS''⟩ := val
      rw [hbok] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ sS'',
          [{ result := childRes.toCallResult, pending := pending }] ++ cS'')
          : Except ExecutionException (FrameResult × List Word × List Nat × List CallRecord))
          = .ok (log.observable, gS, sS, rec :: cS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with _ heq3
      injection heq3 with _ heq4
      injection heq4 with _ heq5
      injection heq5 with hrecEq _
      exact hrecEq.symm

/-- **R7d′ — coupling transport across one non-gas/non-sload `.next` step** (R3's Piece-A
arg-push atom; the `StepsTo` rephrasing of `recorderCoupled_step_other`). The CALL-argument push
prefix (`emitImm 0`×5, then the `callee`/`gasFwd` materialisations — `PUSH32`/`MLOAD`/`ADD`/`LT`,
never `GAS`/`SLOAD`) advances by `StepsTo` steps that record nothing, so the coupling is carried
frame-for-frame from the statement cursor to the CALL cursor `callFr`. Folded over the arg-push
`Runs` (once its per-frame `isGasOp`/`isSloadOp = false` facts are in hand from the lowering
decode) this is Piece-A step 1. -/
theorem recorderCoupled_stepsTo_other {log : RunLog} {fr fr' : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr gS sS cS)
    (hng : isGasOp fr = false) (hns : isSloadOp fr = false)
    (hstep : StepsTo fr fr') :
    RecorderCoupled log fr' gS sS cS := by
  obtain ⟨hs, hfr'⟩ := hstep
  rw [hfr']
  exact recorderCoupled_step_other hcp hng hns hs

/-- **R8 — presence threading** (the named replacement of the inside-out `hpresent`
hypothesis, which quantified over the walk invariant). Trivial-looking on purpose: reached
successors are present because the CFG is closed; `DriveCorrLog.present` is its consumer,
`ClosedCFG.entry_present` its seed. DERIVED-status obligation. -/
theorem present_of_closed {prog : Program} {L : Label} {b : Block} {dst : Label}
    (hclosed : ClosedCFG prog)
    (hb : blockAt prog L = some b)
    (hdst : b.term = .jump dst
      ∨ (∃ c e, b.term = .branch c dst e)
      ∨ (∃ c t, b.term = .branch c t dst)) :
    ∃ b', blockAt prog dst = some b' := by
  rcases hdst with hj | ⟨c, e, hbr⟩ | ⟨c, t, hbr⟩
  · exact (hclosed.jump_closed L b dst hb hj).1
  · exact (hclosed.branch_closed L b c dst e hb hbr).1.1
  · exact (hclosed.branch_closed L b c t dst hb hbr).2.1


end Lir.V2
