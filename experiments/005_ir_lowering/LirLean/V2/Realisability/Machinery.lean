import LirLean.V2.Drive.Headline
import LirLean.Decode.BoundaryCursor
import LirLean.Spec.BudgetDerivations
import LirLean.V2.Realisability.Surface
import LirLean.Engine.Modellable

/-!
# LirLean v2 — Realisability spec, MACHINERY (§5)

Split out of `RealisabilitySpec.lean` (pure relocation). Holds the Phase-3 obligation
machinery R1–R11 (§5), including the tracked sorries R3 (`callRealises_of_recorded`) and
the later coupled-producer obligations. Imports `Surface`. -/

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
      · have hself : defsOf prog t = some (locOfExpr e) := by
          have hc := (hcons L b pc hb).1 t e hs
          rcases e with _ | _ | _ | _ | _ | _ | _ <;>
            first | exact hc | exact absurd rfl hne | exact absurd ⟨_, rfl⟩ hsl
        -- `hdef₀` is the `rematOf`-spine fact; lift it to `defsOf` (`Loc`-valued) to
        -- match `hself` through the `locOfExpr` classification.
        have hdd : defsOf prog t = some (.remat e₀) := Lir.defsOf_of_rematOf hdef₀
        have hloc : Loc.remat e₀ = locOfExpr e := Option.some.inj (hdd.symm.trans hself)
        have he0 : e₀ = e := by
          rcases e with _ | _ | _ | _ | k | _
          · exact Loc.remat.inj hloc
          · exact Loc.remat.inj hloc
          · exact Loc.remat.inj hloc
          · exact Loc.remat.inj hloc
          · exact absurd ⟨k, rfl⟩ hsl
          · exact absurd rfl hne
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
    have hns : ∀ k, e₀ ≠ .sload k := fun k he => Lir.rematOf_ne_sload prog t₀ k (he ▸ hdef₀)
    rw [evalExpr_setStorage_noSload hns]
    exact hprev
  | call hcallee hgas =>
    rename_i cs calleeW gasFwdW success world'
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hns : ∀ k, e₀ ≠ .sload k := fun k he => Lir.rematOf_ne_sload prog t₀ k (he ▸ hdef₀)
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
  | create hvalue hoff hsize hsalt =>
    -- verbatim twin of the `call` arm: the create pops the create stream and applies its head
    -- (world replacement + result-tmp binding) exactly as the call arm applies the call head.
    rename_i cs valueW initOffW initSizeW saltW addrW world'
    intro t₀ e₀ w₀ hdef₀ hnr₀ hninval hlocal₀
    have hns : ∀ k, e₀ ≠ .sload k := fun k he => Lir.rematOf_ne_sload prog t₀ k (he ▸ hdef₀)
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
    (hcr : ∀ fr', Runs fr₀ fr' → CreateResolves fr')
    (hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr') :
    ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt →
      HaltNonException halt := by
  obtain ⟨frame, hbc, hdrive⟩ := runWithLog_drive hrun
  rw [hbegin] at hbc
  have hfeq : frame = fr₀ := (Sum.inl.injEq _ _).mp hbc.symm
  rw [hfeq] at hdrive
  obtain ⟨last₀, halt₀, hto₀, hhalt₀, hobs⟩ :=
    runs_of_drive_ok (seedFuel params.gas) fr₀ log.observable hdrive
      (lower_modellable hcr hcc)
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

/-- Resumed frame keeps the caller's `canModifyState` (`executionEnv` untouched). -/
theorem resumeAfterCall_canModifyState (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.executionEnv.canModifyState
      = pd.frame.exec.executionEnv.canModifyState := rfl

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

/-- A real call cursor statically scopes its result tmp as a call-result tmp. -/
private theorem stepScopedS_call_of_cursor {prog : Program} {L : Label} {b : Block} {pc : Nat}
    {cs : CallSpec}
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs)) :
    StepScopedS prog (.call cs) := by
  intro t ht
  unfold Lir.isCallResult
  refine ⟨b, List.mem_of_getElem? (Lir.toList_of_blockAt hb), cs, ?_, ht⟩
  exact List.mem_of_getElem? hcur

/-- World replacement preserves the call arm's static well-scoping; if a result tmp is bound, its
slot registration comes from `DefsConsistent`. -/
private theorem call_post_wellScoped {prog : Program} {L : Label} {b : Block} {pc : Nat}
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

/-- A byte inside the lowered CALL statement sits below the global `codeFits` budget. -/
private theorem call_stmt_offset_bound_of_codeFits {prog : Program} {L : Label} {b : Block}
    {pc : Nat} {cs : CallSpec}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    {k : Nat}
    (hk : k < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length) :
    pcOf prog L pc + k < 2 ^ 32 := by
  have hbyte0 :
      (emitStmt (matCache prog) (defsOf prog) (.call cs))[k]?
        = some ((emitStmt (matCache prog) (defsOf prog) (.call cs))[k]) :=
    List.getElem?_eq_getElem hk
  have hflat :
      (flatBytes prog)[pcOf prog L pc + k]?
        = some ((emitStmt (matCache prog) (defsOf prog) (.call cs))[k]) := by
    rw [flatBytes_at_pcOf_offset prog L b pc (.call cs) k (Lir.toList_of_blockAt hb) hcur hk]
    exact hbyte0
  rw [List.getElem?_eq_some_iff] at hflat
  exact lt_of_lt_of_le hflat.1 (Nat.le_of_lt hcodeFits)

/-- A nonempty byte segment inside the lowered CALL statement fits in the 32-bit pc budget. -/
private theorem call_stmt_segment_bound_of_codeFits {prog : Program} {L : Label} {b : Block}
    {pc : Nat} {cs : CallSpec} {offset : Nat} {e : Expr}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hpos : 0 < (matExpr (matCache prog) e).length)
    (hin : offset + (matExpr (matCache prog) e).length
      ≤ (emitStmt (matCache prog) (defsOf prog) (.call cs)).length) :
    pcOf prog L pc + offset + (matExpr (matCache prog) e).length ≤ 2 ^ 32 := by
  have hlast : offset + ((matExpr (matCache prog) e).length - 1)
      < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length := by
    omega
  have hboundLast :=
    call_stmt_offset_bound_of_codeFits hcodeFits hb hcur hlast
  omega

-- `callRealises_of_recorded` is RELOCATED below its Piece-A/B machinery
-- (`recorderCoupled_call_extract` / `callRealises_of_recorded_finish` /
-- `call_args_run_of_coupled`), late in this file. Statement changes there are the honest
-- discovered-hypothesis set (operand bindings, the CallsCode seam, and the missing static
-- facts), each documented at the theorem.

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

/-- `recordCreate` appends its record at the tail (CREATE twin of `recordCall_append`), so
prepending an accumulator commutes with it at `[]`. -/
private theorem recordCreate_append (pending : Pending) (result : FrameResult)
    (d0 : List CreateRecord) :
    recordCreate pending result d0 = d0 ++ recordCreate pending result [] := by
  cases pending with
  | call _ => simp [recordCreate]
  | create pd => simp [recordCreate]

/-- **The accumulator homomorphism of `driveLog`.** Running from a nonempty seed
`(g0, s0, c0)` is the empty-seed run with the seeds prepended to each recorded stream. By
induction on fuel, branch-for-branch as `driveLog_drive`; the recording branches shift by
`List.append_assoc`, every other branch threads the IH with the seeds unchanged. -/
private theorem driveLog_acc_hom :
    ∀ (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (g0 : List Word) (s0 : List Nat) (c0 : List CallRecord) (d0 : List CreateRecord),
      driveLog fuel stack state g0 s0 c0 d0
        = (driveLog fuel stack state [] [] [] []).map
            (fun x => (x.1, g0 ++ x.2.1, s0 ++ x.2.2.1, c0 ++ x.2.2.2.1, d0 ++ x.2.2.2.2)) := by
  intro fuel
  induction fuel with
  | zero => intro stack state g0 s0 c0 d0; rfl
  | succ n ih =>
    intro stack state g0 s0 c0 d0
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
          · -- `rest.isEmpty`: the top-level CALL/CREATE records fire (old proof body verbatim).
            rw [ih rest (.inl parent) g0 s0 (recordCall pending result c0)
                  (recordCreate pending result d0),
                ih rest (.inl parent) [] [] (recordCall pending result [])
                  (recordCreate pending result [])]
            cases hb : driveLog n rest (.inl parent) [] [] [] [] with
            | error e => simp [Except.map]
            | ok val =>
              simp [Except.map, recordCall_append pending result c0,
                recordCreate_append pending result d0, List.append_assoc]
          · -- `rest` nonempty (descended callee's inner descent): the records are gated no-ops,
            -- the call/create accumulators threaded unchanged — the append-homomorphism at an
            -- unchanged accumulator (identical shape to the `halted` arm below).
            rw [ih rest (.inl parent) g0 s0 c0 d0]
        | error e =>
          dsimp only [hres]
          split_ifs with hre
          · rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0 s0
                  (recordCall pending result c0) (recordCreate pending result d0),
                ih rest (.inr (endFrame pending.frame (.exception e))) [] []
                  (recordCall pending result []) (recordCreate pending result [])]
            cases hb : driveLog n rest (.inr (endFrame pending.frame (.exception e))) [] [] [] [] with
            | error e' => simp [Except.map]
            | ok val =>
              simp [Except.map, recordCall_append pending result c0,
                recordCreate_append pending result d0, List.append_assoc]
          · rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0 s0 c0 d0]
    | inl current =>
      dsimp only
      cases hstep : stepFrame current with
      | next exec =>
        dsimp only [hstep]
        split_ifs with hc1 hc2 hc3
        · rw [ih stack (.inl { current with exec := exec })
                (g0 ++ [UInt256.ofUInt64 exec.gasAvailable]) s0 c0 d0,
              ih stack (.inl { current with exec := exec })
                ([] ++ [UInt256.ofUInt64 exec.gasAvailable]) [] [] []]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 (s0 ++ [sloadWarmthOf current]) c0 d0,
              ih stack (.inl { current with exec := exec }) [] ([] ++ [sloadWarmthOf current]) [] []]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 s0 c0 (d0 ++ [softFailCreateRecord current]),
              ih stack (.inl { current with exec := exec }) [] [] [] ([] ++ [softFailCreateRecord current])]
          cases hb : driveLog n stack (.inl { current with exec := exec }) [] [] [] [] with
          | error e => simp [Except.map]
          | ok val => simp [Except.map, List.append_assoc]
        · rw [ih stack (.inl { current with exec := exec }) g0 s0 c0 d0]
      | halted halt =>
        dsimp only [hstep]
        rw [ih stack (.inr (endFrame current halt)) g0 s0 c0 d0]
      | needsCall params pending =>
        dsimp only [hstep]
        cases hbc : beginCall params with
        | inl child => dsimp only [hbc]; rw [ih (.call pending :: stack) (.inl child) g0 s0 c0 d0]
        | inr result =>
          dsimp only [hbc]; rw [ih (.call pending :: stack) (.inr (.call result)) g0 s0 c0 d0]
      | needsCreate params pending =>
        dsimp only [hstep]
        rw [ih (.create pending :: stack) (.inl (beginCreate params)) g0 s0 c0 d0]

/-- The gas-op gate and the sload-op gate are mutually exclusive: a frame decoding to
`SLOAD` does not decode to `GAS`. Lets R7c know the gas-`if` in `driveLog` fails first. -/
private theorem isGasOp_false_of_isSloadOp {fr : Frame} (h : isSloadOp fr = true) :
    isGasOp fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.Smsf .SLOAD := by simpa [isSloadOp] using h
  simp only [isGasOp, h']
  decide

/-- A CREATE2 cursor does not decode to `GAS`: the gas-`if` in `driveLog` fails at a CREATE2. -/
private theorem isGasOp_false_of_isCreate2Op {fr : Frame} (h : isCreate2Op fr = true) :
    isGasOp fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.System .CREATE2 := by simpa [isCreate2Op] using h
  simp only [isGasOp, h']
  decide

/-- A CREATE2 cursor does not decode to `SLOAD`: the sload-`if` in `driveLog` fails at a CREATE2. -/
private theorem isSloadOp_false_of_isCreate2Op {fr : Frame} (h : isCreate2Op fr = true) :
    isSloadOp fr = false := by
  have h' : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
      = Operation.System .CREATE2 := by simpa [isCreate2Op] using h
  simp only [isSloadOp, h']
  decide
/-! ### R6 status — the geometry track's findings (Track A / the `hrb` residue)

**R6 WITHOUT a size side condition is REFUTABLE**, so its statement above now carries
`hne : 0 < prog.blocks.size` (blocker B1). The side conditions are pinned below by
machine-checked lemmas.

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

The reusable geometry below threads the entry, ordinary step, CALL return, and CREATE return
edges through one strengthened boundary invariant.
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

/-- **R6 STEP edge.** One ordinary step preserves the reachable in-range boundary and valid-jump
invariants, classifying the successor as sequential or a valid jump destination. -/
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
  have hBpc : (mid.exec.pc = UInt32.ofNat (Evm.nextInstrPosNat b (Evm.parseInstr byte))
      ∧ Evm.parseInstr byte ≠ .STOP ∧ Evm.parseInstr byte ≠ .RETURN
      ∧ Evm.parseInstr byte ≠ .JUMP)
      ∨ mid.exec.pc ∈ fr.validJumps :=
    Lir.stepFrame_next_lowering_pc_or_validJump hcode hpc hbnd hget hop h.1
  refine ⟨?_, hmvj⟩
  rcases hBpc with hseq | hjmp
  · -- sequential advance
    obtain ⟨hseq, hnstop, hnreturn, hnjump⟩ := hseq
    have hInR : Evm.nextInstrPosNat b (Evm.parseInstr byte) < (Lir.flatBytes prog).length :=
      Lir.nextInstrPos_lt_flatBytes_of_cursor (Lir.flatBytes_cursor_cases hin) hreach hget
        hnstop hnreturn hnjump
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
`resumeAfterCall` pins (code / pc = call-site + 1 / validJumps), the CALL-site inversion, and
the CALL successor in-range geometry are discharged in-file. -/
theorem atReachableBoundaryVJ_call {prog : Lir.Program} {fr rf : Frame}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (h : CallReturns fr rf) (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog rf := by
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, hvj⟩ := hinv
  obtain ⟨cp, pending, child, childRes, hncall, _hEnters, _hDrive, hrf⟩ := h
  obtain ⟨byte, hget, hop⟩ := Lir.reachable_boundary_loweringByte prog b hreach hin
  have hBcall : Evm.parseInstr byte = Operation.CALL
      ∧ pending.frame.exec.pc = fr.exec.pc
      ∧ pending.frame.validJumps = fr.validJumps :=
    Lir.stepFrame_needsCall_lowering_site_inv hcode hpc hbnd hget hop hncall
  obtain ⟨hopCall, hppc, hpvj⟩ := hBcall
  have hInR : b + 1 < (Lir.flatBytes prog).length := by
    have hlt := Lir.nextInstrPos_lt_flatBytes_of_cursor (Lir.flatBytes_cursor_cases hin)
      hreach hget (by rw [hopCall]; simp) (by rw [hopCall]; simp) (by rw [hopCall]; simp)
    rw [hopCall] at hlt
    simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hlt
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

/-- **R6 CREATE edge.** A returning CREATE/CREATE2 resumes at the next reachable in-range
boundary while preserving the lowered code and valid-jump table. -/
theorem atReachableBoundaryVJ_create {prog : Lir.Program} {fr rf : Frame}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (h : CreateReturns fr rf) (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog rf := by
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, hvj⟩ := hinv
  obtain ⟨cp, pending, childRes, hncreate, _hDrive, hrf⟩ := h
  obtain ⟨byte, hget, hop⟩ := Lir.reachable_boundary_loweringByte prog b hreach hin
  obtain ⟨hopCreate, hppc, hpvj⟩ :=
    Lir.stepFrame_needsCreate_lowering_site_inv hcode hpc hbnd hget hop hncreate
  have hInR : b + 1 < (Lir.flatBytes prog).length := by
    have hnstop : Evm.parseInstr byte ≠ .STOP := by rcases hopCreate with h | h <;> rw [h] <;> simp
    have hnreturn : Evm.parseInstr byte ≠ .RETURN := by
      rcases hopCreate with h | h <;> rw [h] <;> simp
    have hnjump : Evm.parseInstr byte ≠ .JUMP := by rcases hopCreate with h | h <;> rw [h] <;> simp
    have hlt := Lir.nextInstrPos_lt_flatBytes_of_cursor (Lir.flatBytes_cursor_cases hin)
      hreach hget hnstop hnreturn hnjump
    rcases hopCreate with hcreate | hcreate2
    · rw [hcreate] at hlt
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hlt
    · rw [hcreate2] at hlt
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hlt
  have hrenv : rf.exec.executionEnv = pending.frame.exec.executionEnv :=
    resumeAfterCreate_execEnv childRes pending rf hrf
  have hrcode : rf.exec.executionEnv.code = Lir.lower prog := by
    rw [hrenv, (Evm.stepFrame_needsCreate_inv hncreate).2.2.2, hcode]
  have hrvj : rf.validJumps = validJumpDests (Lir.lower prog) 0 := by
    rw [resumeAfterCreate_validJumps childRes pending rf hrf, hpvj, hvj]
  have hrpc : rf.exec.pc = pending.frame.exec.pc + 1 :=
    resumeAfterCreate_pc childRes pending rf hrf
  refine ⟨⟨b + 1, hrcode, ?_, ?_, hInR, lt_of_lt_of_le hInR hsize⟩, hrvj⟩
  · rw [hrpc, hppc, hpc]
    exact Lir.ofNat_add' b 1
  · have hr := Lir.reachesBoundary_nextInstr hreach hget
    rcases hopCreate with hcreate | hcreate2
    · rw [hcreate] at hr
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hr
    · rw [hcreate2] at hr
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hr

/-- **The `Runs`-induction combinator (master lemma).** `AtReachableBoundaryVJ prog` is
preserved across a whole `Runs` derivation, threading through each single `StepsTo`
(`atReachableBoundaryVJ_step`), each returning external `CallReturns`
(`atReachableBoundaryVJ_call`), and each returning `CreateReturns`
(`atReachableBoundaryVJ_create`). -/
theorem atReachableBoundaryVJ_of_runs {prog : Lir.Program}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    {fr fr' : Frame} (hr : Runs fr fr') :
    AtReachableBoundaryVJ prog fr → AtReachableBoundaryVJ prog fr' := by
  induction hr with
  | refl _ => exact id
  | step h _ ih => exact fun hfr => ih (atReachableBoundaryVJ_step hsize h hfr)
  | call hc _ ih => exact fun hfr => ih (atReachableBoundaryVJ_call hsize hc hfr)
  | create hc _ ih => exact fun hfr => ih (atReachableBoundaryVJ_create hsize hc hfr)

/-- **R6 — the boundary walk** (the `hrb` residue; the Track-A discharge target). Every
`Runs`-reachable frame of a `lower prog` entry sits at a reachable instruction boundary of
`lower prog` — the pc-reachability invariant that scopes the step/call/create resume geometry
and the future data-segment design. DERIVED-status obligation.

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

The proof threads `AtReachableBoundaryVJ` through ordinary, CALL-return, and CREATE-return edges.
`hsize` converts each strict code-range fact into the invariant's `UInt32` range field. -/
theorem runs_atReachableBoundary {prog : Lir.Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog))
    (hne : 0 < prog.blocks.size)
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr' := by
  intro fr' hr
  exact (atReachableBoundaryVJ_of_runs hsize hr
    (atReachableBoundaryVJ_entry hbegin hcode hne)).1

/-! ### R7 — the recorder-coupling edge lemmas (entry + the four currently-landed preservation
edges)

These are what make `RecorderCoupled` a THREADABLE invariant: established once at entry,
preserved across every top-level step shape the drive walk takes. All DERIVED-status. -/

/-- **R7a — entry coupling**: a successful `runWithLog` couples the entry frame to the
WHOLE log (all four suffixes = the full streams; prefixes `[]`). Near-`rfl` from
unfolding `runWithLog` (its `driveLog` equation IS the restart equation at `fr₀`). -/
theorem recorderCoupled_entry {params : CallParams} {log : RunLog} {fr₀ : Frame}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀) :
    RecorderCoupled log fr₀ log.gas log.sloads log.calls log.creates := by
  unfold runWithLog at hrun
  rw [hbegin] at hrun
  dsimp only at hrun
  cases hdl : driveLog (seedFuel params.gas) [] (.inl fr₀) [] [] [] [] with
  | error e => rw [hdl] at hrun; simp at hrun
  | ok triple =>
    obtain ⟨r, gas, sloads, calls, creates⟩ := triple
    rw [hdl] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    exact ⟨⟨seedFuel params.gas, hdl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩, ⟨[], rfl⟩⟩

/-- **R7b — the GAS step consumes the gas-suffix head**: a top-level `.next` step at a GAS
op advances the coupling to the tail and pins the consumed head to the post-charge
`gasAvailable` (exactly what `driveLog` recorded at this step). -/
theorem recorderCoupled_step_gas {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {g : Word} {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr (g :: gS) sS cS dS)
    (hgas : isGasOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS dS
    ∧ g = UInt256.ofUInt64 exec.gasAvailable := by
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hgas, List.isEmpty_nil, Bool.and_true, List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec })
      [UInt256.ofUInt64 exec.gasAvailable] [] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', UInt256.ofUInt64 exec.gasAvailable :: gS', sS', cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, g :: gS, sS, cS, dS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgc hf5
      injection hf5 with hs hcd
      injection hcd with hc hd
      injection hgc with hgeq hgSeq
      subst hobs; subst hgSeq; subst hs; subst hc; subst hd
      refine ⟨⟨⟨m, hX⟩, ?_, hsp, hcpp, hdp⟩, hgeq.symm⟩
      obtain ⟨pre, hpre⟩ := hgp
      exact ⟨pre ++ [g], by rw [hpre, List.append_assoc, List.singleton_append]⟩

/-- **Gas-suffix nonemptiness at a GAS step.** If the coupling holds at `fr`, the op is
`GAS`, and the step continues (`.next exec`), the recorded gas suffix is nonempty — its
head is the datum `driveLog` is about to record. This is the *front half* of
`recorderCoupled_step_gas` (R7b), split out so `gas_suffix_head_realised` (R1) can expose
the `cons` structurally and then pin the head *value* through R7b proper. -/
private theorem gasSuffix_nonempty {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hgas : isGasOp fr = true) (hstep : stepFrame fr = .next exec) :
    ∃ g gS', gS = g :: gS' := by
  obtain ⟨⟨f, hf⟩, _, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hgas, List.isEmpty_nil, Bool.and_true, List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec })
      [UInt256.ofUInt64 exec.gasAvailable] [] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', UInt256.ofUInt64 exec.gasAvailable :: gS', sS', cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, cS, dS) := hf
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
    {dS : List CreateRecord} {I : Tmp → Prop}
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t .gas))
    (hslotdef : defsOf prog t = some (.slot (slotOf t)))
    (hpcbound : pcOf prog L pc + 34 < 2 ^ 32)
    (hcorr : Lir.Corr prog sloadChg 0 I st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS dS)
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
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS (n :: sS) cS dS)
    (hsl : isSloadOp fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS dS
    ∧ n = sloadWarmthOf fr := by
  have hng : isGasOp fr = false := isGasOp_false_of_isSloadOp hsl
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hsl, List.isEmpty_nil, Bool.and_true, Bool.false_and,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) [] [sloadWarmthOf fr] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', gS', sloadWarmthOf fr :: sS', cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, n :: sS, cS, dS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgSeq hf5
      injection hf5 with hsc hcd
      injection hsc with hneq hsSeq
      injection hcd with hc hd
      subst hobs; subst hgSeq; subst hsSeq; subst hc; subst hd
      refine ⟨⟨⟨m, hX⟩, hgp, ?_, hcpp, hdp⟩, hneq.symm⟩
      obtain ⟨pre, hpre⟩ := hsp
      exact ⟨pre ++ [n], by rw [hpre, List.append_assoc, List.singleton_append]⟩

/-- At a continuing SLOAD step, the coupled sload suffix has a head to consume. -/
theorem sloadSuffix_nonempty {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hsl : isSloadOp fr = true) (hstep : stepFrame fr = .next exec) :
    ∃ n sS', sS = n :: sS' := by
  have hng : isGasOp fr = false := isGasOp_false_of_isSloadOp hsl
  obtain ⟨⟨f, hf⟩, _, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hsl, List.isEmpty_nil, Bool.and_true, Bool.false_and,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) [] [sloadWarmthOf fr] [] []] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', gS', sloadWarmthOf fr :: sS', cS', dS')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, cS, dS) := hf
      injection hf2 with hf3
      injection hf3 with _ hf4
      injection hf4 with _ hf5
      injection hf5 with hsc _
      exact ⟨_, _, hsc.symm⟩

/-- **R7d — any other top-level `.next` step preserves all four suffixes** (nothing is
recorded off the GAS/SLOAD gates). -/
theorem recorderCoupled_step_other {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hng : isGasOp fr = false) (hns : isSloadOp fr = false)
    (hnc : isCreate2Op fr = false)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS dS := by
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hns, hnc, List.isEmpty_nil, Bool.false_and, Bool.and_false] at hf
    exact ⟨⟨m, hf⟩, hgp, hsp, hcpp, hdp⟩

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
    (g0 : List Word) (s0 : List Nat) (c0 : List CallRecord) (d0 : List CreateRecord) :
    ∀ (f : ℕ) (top : List Pending) (st : Frame ⊕ FrameResult) (res : FrameResult),
      drive f top st = .ok res →
      ∃ j, driveLog f (top ++ bot) st g0 s0 c0 d0
          = driveLog (j + 1) bot (.inr res) g0 s0 c0 d0 := by
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
        split_ifs with hc1 hc2 hc3
        · rw [hbne top] at hc1; simp at hc1
        · rw [hbne top] at hc2; simp at hc2
        · rw [hbne top] at hc3; simp at hc3
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

/-- At a top-level CALL descent, the coupled call suffix has a head to consume. -/
theorem callSuffix_nonempty {log : RunLog} {fr : Frame} {cp : CallParams}
    {pending : PendingCall} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .needsCall cp pending) :
    ∃ rec cS', cS = rec :: cS' := by
  obtain ⟨⟨fuel', hrestart⟩, _, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    unfold driveLog at hrestart
    simp only [hstep] at hrestart
    cases hbc : beginCall cp with
    | inl child =>
      simp only [hbc] at hrestart
      have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
        have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] [] []
        rw [hrestart] at hd
        simpa only [Except.map] using hd.symm
      have hstand_ne : drive m [] (.inl child) ≠ .error .OutOfFuel := by
        intro hoof
        have := framed_oof_of_standalone_oof m (.inl child) [] (.call pending :: []) hoof
        rw [List.nil_append, hdrive] at this
        simp at this
      cases hstand : drive m [] (.inl child) with
      | error e =>
        rw [drive_error_oof _ _ _ e hstand] at hstand
        exact absurd hstand hstand_ne
      | ok childRes =>
        obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] [] []
          m [] (.inl child) childRes hstand
        rw [List.nil_append] at hframe
        rw [hframe] at hrestart
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
          List.nil_append] at hrestart
        rw [driveLog_acc_hom j []
          (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] []
          [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
        cases htail : driveLog j []
            (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', sS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          injection htuple with _ hrest
          injection hrest with _ hrest
          injection hrest with _ hrest
          injection hrest with hc _
          exact ⟨_, _, hc.symm⟩
    | inr result =>
      simp only [hbc] at hrestart
      have hdrive : drive m (.call pending :: []) (.inr (.call result))
          = .ok log.observable := by
        have hd := driveLog_drive m (.call pending :: []) (.inr (.call result)) [] [] [] []
        rw [hrestart] at hd
        simpa only [Except.map] using hd.symm
      have hstand_ne : drive m [] (.inr (.call result)) ≠ .error .OutOfFuel := by
        intro hoof
        have := framed_oof_of_standalone_oof m (.inr (.call result)) []
          (.call pending :: []) hoof
        rw [List.nil_append, hdrive] at this
        simp at this
      cases hstand : drive m [] (.inr (.call result)) with
      | error e =>
        rw [drive_error_oof _ _ _ e hstand] at hstand
        exact absurd hstand hstand_ne
      | ok childRes =>
        obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] [] []
          m [] (.inr (.call result)) childRes hstand
        rw [List.nil_append] at hframe
        rw [hframe] at hrestart
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
          List.nil_append] at hrestart
        rw [driveLog_acc_hom j []
          (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] []
          [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
        cases htail : driveLog j []
            (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', sS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          injection htuple with _ hrest
          injection hrest with _ hrest
          injection hrest with _ hrest
          injection hrest with hc _
          exact ⟨_, _, hc.symm⟩

/-- At a top-level CREATE descent, the coupled create suffix has a head to consume. -/
theorem createSuffix_nonempty {log : RunLog} {fr : Frame} {cp : CreateParams}
    {pending : PendingCreate} {gS : List Word} {sS : List Nat}
    {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .needsCreate cp pending) :
    ∃ rec dS', dS = rec :: dS' := by
  obtain ⟨⟨fuel', hrestart⟩, _, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    unfold driveLog at hrestart
    simp only [hstep] at hrestart
    have hdrive : drive m (.create pending :: []) (.inl (beginCreate cp))
        = .ok log.observable := by
      have hd := driveLog_drive m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hstand_ne : drive m [] (.inl (beginCreate cp)) ≠ .error .OutOfFuel := by
      intro hoof
      have := framed_oof_of_standalone_oof m (.inl (beginCreate cp)) []
        (.create pending :: []) hoof
      rw [List.nil_append, hdrive] at this
      simp at this
    cases hstand : drive m [] (.inl (beginCreate cp)) with
    | error e =>
      rw [drive_error_oof _ _ _ e hstand] at hstand
      exact absurd hstand hstand_ne
    | ok childRes =>
      obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.create pending :: []) rfl [] [] [] []
        m [] (.inl (beginCreate cp)) childRes hstand
      rw [List.nil_append] at hframe
      rw [hframe] at hrestart
      cases hresume : resumeAfterCreate childRes.toCreateResult pending with
      | error e =>
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, hresume, List.isEmpty_nil, if_true, recordCall,
          recordCreate, List.nil_append] at hrestart
        rw [driveLog_acc_hom j []
          (.inr (endFrame (Pending.create pending).frame (.exception e))) [] [] []
          [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
        cases htail : driveLog j []
            (.inr (endFrame (Pending.create pending).frame (.exception e))) [] [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', sS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          injection htuple with _ hrest
          injection hrest with _ hrest
          injection hrest with _ hrest
          injection hrest with _ hd
          exact ⟨_, _, hd.symm⟩
      | ok resumeFr =>
        conv at hrestart =>
          lhs
          unfold driveLog
        simp only [Pending.resume, hresume, List.isEmpty_nil, if_true, recordCall,
          recordCreate, List.nil_append] at hrestart
        rw [driveLog_acc_hom j [] (.inl resumeFr) [] [] []
          [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
        cases htail : driveLog j [] (.inl resumeFr) [] [] [] [] with
        | error e => rw [htail] at hrestart; simp [Except.map] at hrestart
        | ok val =>
          obtain ⟨obs', gS', sS', cS', dS'⟩ := val
          rw [htail] at hrestart
          simp only [Except.map, List.nil_append, List.singleton_append] at hrestart
          injection hrestart with htuple
          injection htuple with _ hrest
          injection hrest with _ hrest
          injection hrest with _ hrest
          injection hrest with _ hd
          exact ⟨_, _, hd.symm⟩

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
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS (rec :: cS) dS)
    (hcr : CallReturns fr resumeFr) :
    RecorderCoupled log resumeFr gS sS cS dS := by
  obtain ⟨cp, pending, child, childRes, hstep, hcode, hchild, hresume⟩ := hcr
  have hcode' : beginCall cp = .inl child := hcode
  obtain ⟨⟨fuel', hrestart⟩, hgp, hsp, hcpp, hdp⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    -- Unfold the restart's first (CALL) step: `fr` descends into `child` on `[.call pending]`.
    have hdescent : driveLog (m + 1) [] (.inl fr) [] [] [] []
        = driveLog m (.call pending :: []) (.inl child) [] [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep, hcode']
    rw [hdescent] at hrestart
    -- The child terminates within fuel `m` (the framed restart succeeded).
    have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
      have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] [] []
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
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] [] []
      m [] (.inl child) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    -- Reduce the outer CALL delivery (`rest = []`): record `[outerRec]`, resume at `resumeFr`.
    have hdeliv : driveLog (j + 1) (.call pending :: []) (.inr childRes) [] [] [] []
        = driveLog j [] (.inl resumeFr) [] []
            [{ result := childRes.toCallResult, pending := pending }] [] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append, hresume]
    rw [hdeliv] at hrestart
    -- Peel the single seeded record via the accumulator homomorphism.
    rw [driveLog_acc_hom j [] (.inl resumeFr) [] []
      [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
    cases hb : driveLog j [] (.inl resumeFr) [] [] [] [] with
    | error e => rw [hb] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', sS'', cS'', dS''⟩ := val
      rw [hb] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ sS'',
          [{ result := childRes.toCallResult, pending := pending }] ++ cS'', [] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, rec :: cS, dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with hobs heq3
      injection heq3 with hgeq heq4
      injection heq4 with hseq heq5
      injection heq5 with hcons hd
      injection hcons with _ hcs
      subst hobs; subst hgeq; subst hseq; subst hcs; subst hd
      refine ⟨⟨j, hb⟩, hgp, hsp, ?_, hdp⟩
      obtain ⟨pre, hpre⟩ := hcpp
      exact ⟨pre ++ [rec], by rw [hpre]; simp [List.append_assoc]⟩

/-- A returning CREATE consumes exactly one create-suffix head and preserves the gas, SLOAD,
and CALL suffixes. Child execution is recorder-invisible under the nonempty pending stack; the
top-level delivery appends the single CREATE record before restarting at `resumeFr`. -/
theorem recorderCoupled_create {log : RunLog} {fr resumeFr : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS (rec :: dS))
    (hcr : CreateReturns fr resumeFr) :
    RecorderCoupled log resumeFr gS sS cS dS := by
  obtain ⟨cp, pending, childRes, hstep, hchild, hresume⟩ := hcr
  obtain ⟨⟨fuel', hrestart⟩, hgp, hsp, hcpp, hdp⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl fr) [] [] [] []
        = driveLog m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep]
    rw [hdescent] at hrestart
    have hdrive : drive m (.create pending :: []) (.inl (beginCreate cp))
        = .ok log.observable := by
      have hd := driveLog_drive m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.create pending :: []) (running (beginCreate cp))
        ≠ .error .OutOfFuel := by rw [hdrive]; simp
    have hchildm_ne : drive m [] (running (beginCreate cp)) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed' m (beginCreate cp) (.create pending) [] hne
    have hchildm : drive m [] (running (beginCreate cp)) = .ok childRes := by
      have h1 := drive_fuel_mono (Nat.le_max_left m (seedFuel cp.gas)) []
        (running (beginCreate cp)) hchildm_ne
      have h2 := drive_fuel_mono (Nat.le_max_right m (seedFuel cp.gas)) []
        (running (beginCreate cp)) (by rw [hchild]; simp)
      rw [hchild] at h2
      rw [← h1, h2]
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.create pending :: []) rfl [] [] [] []
      m [] (.inl (beginCreate cp)) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.create pending :: []) (.inr childRes) [] [] [] []
        = driveLog j [] (.inl resumeFr) [] [] []
            [{ result := childRes.toCreateResult, pending := pending }] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append, hresume]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl resumeFr) [] [] []
      [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
    cases hb : driveLog j [] (.inl resumeFr) [] [] [] [] with
    | error e => rw [hb] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', sS'', cS'', dS''⟩ := val
      rw [hb] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ sS'', [] ++ cS'',
          [{ result := childRes.toCreateResult, pending := pending }] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, cS, rec :: dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with hobs heq3
      injection heq3 with hgeq heq4
      injection heq4 with hseq heq5
      injection heq5 with hcEq hcons
      injection hcons with _ hdEq
      subst hobs; subst hgeq; subst hseq; subst hcEq; subst hdEq
      refine ⟨⟨j, hb⟩, hgp, hsp, hcpp, ?_⟩
      obtain ⟨pre, hpre⟩ := hdp
      exact ⟨pre ++ [rec], by rw [hpre]; simp [List.append_assoc]⟩

/-- A coupled CREATE head determines the returning child and its successful resume.  The
`CreateResolves` premise is the genuine retained-gas seam: it is used exactly once, to rule out
the exceptional `resumeAfterCreate` branch.  As for CALL extraction, the recorder equation then
identifies the positional head and `recorderCoupled_create` consumes it. -/
theorem recorderCoupled_create_extract {log : RunLog} {createFr : Frame}
    {cp : CreateParams} {pending : PendingCreate}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log createFr gS sS cS (rec :: dS))
    (hstep : stepFrame createFr = .needsCreate cp pending)
    (hresolve : CreateResolves createFr) :
    ∃ (childRes : FrameResult) (resumeFr : Frame),
        CreateReturns createFr resumeFr
      ∧ rec = { result := childRes.toCreateResult, pending := pending }
      ∧ resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr
      ∧ RecorderCoupled log resumeFr gS sS cS dS := by
  obtain ⟨childRes, hchild⟩ := create_child_terminates cp
  obtain ⟨resumeFr, hresume⟩ := hresolve cp pending childRes hstep hchild
  have hcr : CreateReturns createFr resumeFr :=
    ⟨cp, pending, childRes, hstep, hchild, hresume⟩
  refine ⟨childRes, resumeFr, hcr, ?_, hresume, recorderCoupled_create hcp hcr⟩
  obtain ⟨⟨fuel', hrestart⟩, _, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl createFr) [] [] [] []
        = driveLog m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep]
    rw [hdescent] at hrestart
    have hdrive : drive m (.create pending :: []) (.inl (beginCreate cp))
        = .ok log.observable := by
      have hd := driveLog_drive m (.create pending :: []) (.inl (beginCreate cp)) [] [] [] []
      rw [hrestart] at hd
      simpa only [Except.map] using hd.symm
    have hne : drive m (.create pending :: []) (running (beginCreate cp))
        ≠ .error .OutOfFuel := by rw [hdrive]; simp
    have hchildm_ne : drive m [] (running (beginCreate cp)) ≠ .error .OutOfFuel :=
      child_ne_oof_of_framed' m (beginCreate cp) (.create pending) [] hne
    have hchildm : drive m [] (running (beginCreate cp)) = .ok childRes := by
      have h1 := drive_fuel_mono (Nat.le_max_left m (seedFuel cp.gas)) []
        (running (beginCreate cp)) hchildm_ne
      have h2 := drive_fuel_mono (Nat.le_max_right m (seedFuel cp.gas)) []
        (running (beginCreate cp)) (by rw [hchild]; simp)
      rw [hchild] at h2
      rw [← h1, h2]
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.create pending :: []) rfl [] [] [] []
      m [] (.inl (beginCreate cp)) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.create pending :: []) (.inr childRes) [] [] [] []
        = driveLog j [] (.inl resumeFr) [] [] []
            [{ result := childRes.toCreateResult, pending := pending }] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append, hresume]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl resumeFr) [] [] []
      [{ result := childRes.toCreateResult, pending := pending }]] at hrestart
    cases hbok : driveLog j [] (.inl resumeFr) [] [] [] [] with
    | error e => rw [hbok] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', sS'', cS'', dS''⟩ := val
      rw [hbok] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ sS'', [] ++ cS'',
          [{ result := childRes.toCreateResult, pending := pending }] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, cS, rec :: dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with _ heq3
      injection heq3 with _ heq4
      injection heq4 with _ heq5
      injection heq5 with _ hcons
      injection hcons with hrecEq _
      exact hrecEq.symm

/-- **The soft-fail CREATE2 step consumes the create-suffix head** (the CREATE2 twin of
`recorderCoupled_sload`, over the new `driveLog` create2 `.next` gate). At a top-level CREATE2
cursor `fr` (`isCreate2Op fr = true`, `stack = []` from the outer `driveLog []`) that soft-fails
(`stepFrame fr = .next exec`, the `createArm` funds/depth/size/nonce fallback), the recorder's new
create2 gate fires (`isGasOp`/`isSloadOp` false at a CREATE2, so the first two `if`s fail and the
third records `softFailCreateRecord fr`). Peeling the restart via `driveLog_acc_hom` (as
`recorderCoupled_sload`) identifies the positional head `rec = softFailCreateRecord fr` and advances
the coupling to `{ fr with exec := exec }` — NO child descent, NO `CreateResolves`. -/
theorem recorderCoupled_create_softfail {log : RunLog} {fr : Frame} {exec : ExecutionState}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS (rec :: dS))
    (hc2 : isCreate2Op fr = true)
    (hstep : stepFrame fr = .next exec) :
    RecorderCoupled log { fr with exec := exec } gS sS cS dS
    ∧ rec = softFailCreateRecord fr := by
  have hng : isGasOp fr = false := isGasOp_false_of_isCreate2Op hc2
  have hns : isSloadOp fr = false := isSloadOp_false_of_isCreate2Op hc2
  obtain ⟨⟨f, hf⟩, hgp, hsp, hcpp, hdp⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep, hng, hns, hc2, List.isEmpty_nil, Bool.and_true,
      List.nil_append] at hf
    rw [driveLog_acc_hom m [] (.inl { fr with exec := exec }) [] [] [] [softFailCreateRecord fr]] at hf
    cases hX : driveLog m [] (.inl { fr with exec := exec }) [] [] [] [] with
    | error e => rw [hX] at hf; simp [Except.map] at hf
    | ok val =>
      obtain ⟨obs', gS', sS', cS', dS'⟩ := val
      rw [hX] at hf
      have hf2 : (Except.ok (obs', gS', sS', cS', softFailCreateRecord fr :: dS')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, cS, rec :: dS) := hf
      injection hf2 with hf3
      injection hf3 with hobs hf4
      injection hf4 with hgSeq hf5
      injection hf5 with hsSeq hcd
      injection hcd with hcEq hdEq
      injection hdEq with hreq hdSeq
      subst hobs; subst hgSeq; subst hsSeq; subst hcEq; subst hdSeq
      refine ⟨⟨⟨m, hX⟩, hgp, hsp, hcpp, ?_⟩, hreq.symm⟩
      obtain ⟨pre, hpre⟩ := hdp
      exact ⟨pre ++ [rec], by rw [hpre, List.append_assoc, List.singleton_append]⟩

/-- **A `.halted` first step records NO create.** If the coupled frame `fr` halts immediately
(`stepFrame fr = .halted halt`), the top-level restart delivers `.inr (endFrame …)` on the empty
pending stack and returns at once — so every recorded suffix, in particular the create suffix, is
empty. Used to EXCLUDE the `.halted` arm of the CREATE2 dispatch case-split (a nonempty coupled
create suffix contradicts it). -/
theorem creates_nil_of_stepFrame_halted {log : RunLog} {fr : Frame} {halt : Evm.FrameHalt}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .halted halt) :
    dS = [] := by
  obtain ⟨⟨f, hf⟩, _, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    cases m with
    | zero =>
      unfold driveLog at hf
      simp only [hstep] at hf
      simp [driveLog] at hf
    | succ k =>
      unfold driveLog at hf
      simp only [hstep] at hf
      -- delivery on the empty pending stack: `.inr (endFrame fr halt)` returns immediately.
      rw [show driveLog (k + 1) [] (.inr (endFrame fr halt)) [] [] [] []
            = .ok (endFrame fr halt, [], [], [], []) from rfl] at hf
      injection hf with hf2
      injection hf2 with _ hf3
      injection hf3 with _ hf4
      injection hf4 with _ hf5
      injection hf5 with _ hf6
      exact hf6.symm

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
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log callFr gS sS (rec :: cS) dS)
    (hstep : stepFrame callFr = .needsCall cp pending)
    (hcode : beginCall cp = .inl child) :
    ∃ childRes : FrameResult,
        CallReturns callFr (Evm.resumeAfterCall childRes.toCallResult pending)
      ∧ rec = { result := childRes.toCallResult, pending := pending }
      ∧ RecorderCoupled log (Evm.resumeAfterCall childRes.toCallResult pending) gS sS cS dS := by
  obtain ⟨childRes, hchild_seed⟩ := child_terminates hcode
  have hcr : CallReturns callFr (Evm.resumeAfterCall childRes.toCallResult pending) :=
    ⟨cp, pending, child, childRes, hstep, hcode, hchild_seed, rfl⟩
  refine ⟨childRes, hcr, ?_, recorderCoupled_call hcp hcr⟩
  -- The record identity: peel the restart equation (as `recorderCoupled_call`, but keep the head).
  obtain ⟨⟨fuel', hrestart⟩, _, _, _, _⟩ := hcp
  cases fuel' with
  | zero => simp [driveLog] at hrestart
  | succ m =>
    have hdescent : driveLog (m + 1) [] (.inl callFr) [] [] [] []
        = driveLog m (.call pending :: []) (.inl child) [] [] [] [] := by
      conv_lhs => unfold driveLog
      simp only [hstep, hcode]
    rw [hdescent] at hrestart
    have hdrive : drive m (.call pending :: []) (.inl child) = .ok log.observable := by
      have hd := driveLog_drive m (.call pending :: []) (.inl child) [] [] [] []
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
    obtain ⟨j, hframe⟩ := driveLog_frame_nonempty (.call pending :: []) rfl [] [] [] []
      m [] (.inl child) childRes hchildm
    rw [List.nil_append] at hframe
    rw [hframe] at hrestart
    have hdeliv : driveLog (j + 1) (.call pending :: []) (.inr childRes) [] [] [] []
        = driveLog j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] []
            [{ result := childRes.toCallResult, pending := pending }] [] := by
      conv_lhs => unfold driveLog
      simp only [Pending.resume, List.isEmpty_nil, if_true, recordCall, recordCreate,
        List.nil_append]
    rw [hdeliv] at hrestart
    rw [driveLog_acc_hom j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] []
      [{ result := childRes.toCallResult, pending := pending }] []] at hrestart
    cases hbok : driveLog j [] (.inl (Evm.resumeAfterCall childRes.toCallResult pending)) [] [] [] []
      with
    | error e => rw [hbok] at hrestart; simp [Except.map] at hrestart
    | ok val =>
      obtain ⟨obs'', gS'', sS'', cS'', dS''⟩ := val
      rw [hbok] at hrestart
      have heq : (Except.ok (obs'', [] ++ gS'', [] ++ sS'',
          [{ result := childRes.toCallResult, pending := pending }] ++ cS'', [] ++ dS'')
          : Except ExecutionException
              (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord))
          = .ok (log.observable, gS, sS, rec :: cS, dS) := hrestart
      simp only [List.nil_append, List.singleton_append] at heq
      injection heq with heq2
      injection heq2 with _ heq3
      injection heq3 with _ heq4
      injection heq4 with _ heq5
      injection heq5 with hcons _
      injection hcons with hrecEq _
      exact hrecEq.symm

/-- The proved finish half of R3: once Piece B has produced the CALL cursor, its arg-prefix run,
the recorder-coupled head at that cursor, the realised resume-frame pins, and the Route-B tail,
the recorded head `rec` discharges `CallRealisesS`. The only remaining debt for
`callRealises_of_recorded` is therefore the honest Piece-B cursor bundle itself. -/
private theorem callRealises_of_recorded_finish
    {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 : IRState} {fr0 callFr child : Frame}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS' : List CallRecord}
    {dS : List CreateRecord} {I : Tmp → Prop}
    {argsLen : Nat} {cp : CallParams}
    (hwl : WellLowered prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (haddr : fr0.exec.executionEnv.address = self)
    (hcorr : Corr prog sloadChg 0 I st0 fr0 L pc)
    (hargslen : argsLen = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
        ++ matCache prog cs.callee ++ matCache prog cs.gasFwd).length)
    (hargs : Runs fr0 callFr)
    (hcallpc : callFr.exec.pc = fr0.exec.pc + UInt32.ofNat argsLen)
    (hcallmem : callFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory)
    (hcallactive : fr0.exec.toMachineState.activeWords.toNat
      ≤ callFr.exec.toMachineState.activeWords.toNat)
    (hcpcall : RecorderCoupled log callFr gS sS (rec :: cS') dS)
    (hstep : stepFrame callFr = .needsCall cp rec.pending)
    (hbegin : beginCall cp = .inl child)
    (hresaddr : (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.address
      = fr0.exec.executionEnv.address)
    (hrescode : (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code = lower prog)
    (hrescanmod : (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.canModifyState
      = true)
    (hrespc : (Evm.resumeAfterCall rec.result rec.pending).exec.pc = callFr.exec.pc + 1)
    (hresstack : (Evm.resumeAfterCall rec.result rec.pending).exec.stack
      = callSuccessFlag rec.result rec.pending :: [])
    (hresmem : (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.memory
      = callFr.exec.toMachineState.memory)
    (hresactive : callFr.exec.toMachineState.activeWords.toNat
      ≤ (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.activeWords.toNat)
    (hresvalid : (Evm.resumeAfterCall rec.result rec.pending).validJumps
      = validJumpDests (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code 0)
    (htail : ∀ flag : Word,
        (Evm.resumeAfterCall rec.result rec.pending).exec.stack = flag :: [] →
        (∀ (t : Tmp), cs.resultTmp = some t →
          (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
          ∧ ∃ endFr,
              Runs (Evm.resumeAfterCall rec.result rec.pending) endFr
            ∧ endFr.exec.toMachineState.memory
                = (((Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.mstore
                    (UInt256.ofNat (slotOf t)) flag)).memory
            ∧ endFr.exec.toMachineState.activeWords
                = (((Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.mstore
                    (UInt256.ofNat (slotOf t)) flag)).activeWords
            ∧ endFr.exec.pc
                = (Evm.resumeAfterCall rec.result rec.pending).exec.pc + UInt32.ofNat 34
            ∧ endFr.exec.executionEnv.code
                = (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code
            ∧ endFr.validJumps = (Evm.resumeAfterCall rec.result rec.pending).validJumps
            ∧ endFr.exec.executionEnv.address
                = (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.address
            ∧ endFr.exec.executionEnv.canModifyState
                = (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.canModifyState
            ∧ (∀ k, selfStorage endFr k
                = selfStorage (Evm.resumeAfterCall rec.result rec.pending) k)
            ∧ endFr.exec.stack = [])
        ∧ (cs.resultTmp = none →
            Runs (Evm.resumeAfterCall rec.result rec.pending)
              (popFrame (Evm.resumeAfterCall rec.result rec.pending) []))) :
    CallRealisesS prog sloadChg I L b pc cs st0
      (match cs.resultTmp with
        | some t' => { st0 with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key }.setLocal
                        t' (callSuccessFlag rec.result rec.pending)
        | none   => { st0 with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key })
      fr0 := by
  intro _
  obtain ⟨childRes, hcall, hrec, _⟩ := recorderCoupled_call_extract hcpcall hstep hbegin
  have hresult : rec.result = childRes.toCallResult := by
    cases rec
    cases hrec
    rfl
  refine ⟨childRes.toCallResult, rec.pending, callFr,
    Evm.resumeAfterCall childRes.toCallResult rec.pending, argsLen,
    stepScopedS_call_of_cursor hb hcur, ?_, hargslen, hargs, hcallpc, hcallmem, hcallactive,
    hcall, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases cs.resultTmp <;> simp [haddr, hresult]
  · simpa [hresult] using hresaddr
  · simpa [hresult] using hrescode
  · simpa [hresult] using hrescanmod
  · simpa [hresult] using hrespc
  · simpa [hresult] using hresstack
  · simpa [hresult] using hresmem
  · simpa [hresult] using hresactive
  · simpa [hresult] using hresvalid
  · intro t hlocal
    exact call_post_wellScoped hb hcur hwl.defsCons hcorr.wellScoped t hlocal
  · simpa [hresult] using htail

/-- **R7d′ — coupling transport across one non-gas/non-sload `.next` step** (R3's Piece-A
arg-push atom; the `StepsTo` rephrasing of `recorderCoupled_step_other`). The CALL-argument push
prefix (`emitImm 0`×5, then the `callee`/`gasFwd` materialisations — `PUSH32`/`MLOAD`/`ADD`/`LT`,
never `GAS`/`SLOAD`) advances by `StepsTo` steps that record nothing, so the coupling is carried
frame-for-frame from the statement cursor to the CALL cursor `callFr`. Folded over the arg-push
`Runs` (once its per-frame `isGasOp`/`isSloadOp = false` facts are in hand from the lowering
decode) this is Piece-A step 1. -/
theorem recorderCoupled_stepsTo_other {log : RunLog} {fr fr' : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hng : isGasOp fr = false) (hns : isSloadOp fr = false)
    (hnc : isCreate2Op fr = false)
    (hstep : StepsTo fr fr') :
    RecorderCoupled log fr' gS sS cS dS := by
  obtain ⟨hs, hfr'⟩ := hstep
  rw [hfr']
  exact recorderCoupled_step_other hcp hng hns hnc hs

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
    (I : Tmp → Prop) (e : Expr) (w : Word) (fr : Frame)
    (hdec : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc e)
    (hsound : DefsSoundS prog I st)
    (hfree : RematClosureFree prog I e)
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
  match e, hfree, hdec, hne, hnsl, heval, hgas, hstk with
  | .imm v, _, hdec, _, _, heval, hgas, hstk =>
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
          memBytes := rfl, memActive := le_refl _, activeWordsEq := rfl }, ?_⟩
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
          (by unfold isCreate2Op; rw [hdec']; rfl)
          (stepFrame_push fr .PUSH32 v 32 (by decide) hdec' (by decide) (by decide) hg3 hstk1)
  | .gas, _, _, hne, _, _, _, _ => exact absurd rfl hne
  | .sload k, _, _, _, hnsl, _, _, _ => exact absurd rfl (hnsl k)
  | .tmp t, hfree, hdec, _, _, heval, hgas, hstk =>
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
              obtain ⟨hfree_t, hfree_remat⟩ := RematClosureFree.tmp_inv hfree
              have hdfs : some w = evalExpr st 0 e' :=
                hsound t e' w hremt hnr hfree_t hloc
              have heval' : evalExpr st obs e' = some w := by
                rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
              have hgas' : (chargeExpr sloadChg (chargeCache prog sloadChg) e').sum
                  ≤ fr.exec.gasAvailable.toNat := by
                have hx := hgas; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              have hstk' : fr.exec.stack.size
                  + (chargeExpr sloadChg (chargeCache prog sloadChg) e').length ≤ 1024 := by
                have hx := hstk; simp only [chargeExpr_tmp] at hx; rw [hcc] at hx; exact hx
              obtain ⟨fr', hmr, hcp'⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
                log gS sS cS dS I e' w fr htmd hsound (hfree_remat e' hal) hscoped hstore he'ng he'nsl hmemreal heval'
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
                  memBytes := hmr.memBytes, memActive := hmr.memActive
                  activeWordsEq := hmr.activeWordsEq }, hcp'⟩
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
                  (by unfold isCreate2Op; rw [hdpush]; rfl)
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
                  (by unfold isCreate2Op; rw [hmloaddec]; rfl)
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
                  memActive := by rw [hfrmaw]
                  activeWordsEq := hfrmaw }
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
  | .add a b, hfree, hdec, _, _, heval, hgas, hstk =>
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
      obtain ⟨hfreea, hfreeb⟩ := RematClosureFree.add_inv hfree
      obtain ⟨frb, hmrb, hcpb⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
        log gS sS cS dS I (.tmp b) vb fr hdb hsound hfreeb hscoped hstore (by nofun) (by nofun)
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
        log gS sS cS dS I (.tmp a) va frb hda' hsound hfreea hscoped (hstore.transport hmrb.storage)
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
          (by unfold isCreate2Op; rw [hadec]; rfl)
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
            (le_trans hmra.memActive (by rw [addFrame_activeWords]))
          activeWordsEq := by
            rw [addFrame_activeWords, hmra.activeWordsEq, hmrb.activeWordsEq] }
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
  | .lt a b, hfree, hdec, _, _, heval, hgas, hstk =>
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
      obtain ⟨hfreea, hfreeb⟩ := RematClosureFree.lt_inv hfree
      obtain ⟨frb, hmrb, hcpb⟩ := recorderCoupled_matRunsC hdc hord sloadChg st obs
        log gS sS cS dS I (.tmp b) vb fr hdb hsound hfreeb hscoped hstore (by nofun) (by nofun)
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
        log gS sS cS dS I (.tmp a) va frb hda' hsound hfreea hscoped (hstore.transport hmrb.storage)
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
          (by unfold isCreate2Op; rw [hadec]; rfl)
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
            (le_trans hmra.memActive (by rw [ltFrame_activeWords]))
          activeWordsEq := by
            rw [ltFrame_activeWords, hmra.activeWordsEq, hmrb.activeWordsEq] }
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

set_option maxRecDepth 8192 in
/-- **R5 — terminator ties from the walk vocabulary.** `TermTies'` holds at every present
block: its arms' antecedents are exactly what `DriveCorrLog` supplies at real boundaries
(Corr, clean-halt, self-presence, address/kind pins), and the conclusions are derived —
non-emptiness via `accounts_ne_empty_of_selfPresent`; the gas guards via the clean-halt
landing extractors (the jump pre-`JUMPDEST` landing/the branch pre-`JUMPDEST` landing patterns,
ported inline); the ret charge-sum via `materialise_chargeC_le_of_cleanHalt`; the ret epilogue
decode facts via `imm_leaf_decodeF`/`decode_at_term_nonpush` at the pc-pinned cursor; the `frv`
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
    `materialise_chargeC_le_of_cleanHalt` needs the operand value, and the IR `ret t`
    semantics (`RunFrom.ret`) itself requires `st'.locals t = some vw`; demanding the
    charge-sum bound for an UNBOUND `t` is the same unwitnessable over-demand (the `.length`
    bound stays unconditional — it is static). The epilogue block (already under the value
    guard) is unchanged in placement.
  * **`hretEmit` added — the ret epilogue's pc-bound seam.** `WellFormedLowered.bound_ret`
    only bounds `termOf + |matCache t|` (the operand), NOT the 101-byte `PUSH32 0; MSTORE;
    PUSH32 32; PUSH32 0; RETURN` full-observable epilogue; the five epilogue decodes need
    `termOf + |matCache t| + 100 < 2^32`, which is a static, satisfiable,
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
      termOf prog L + (matCache prog t).length + 100 < 2 ^ 32)
    (hb : blockAt prog L = some b) :
    TermTies' prog sloadChg log self L b := by
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- STOP arm: non-emptiness from the threaded `SelfPresent`.
    intro _hterm st frT hcorr _hch hsp _haddr _hkind
    exact accounts_ne_empty_of_selfPresent hsp
  · -- RET arm.
    intro t hterm st frT hcorr hch hsp haddr hkind
    have hb100 : termOf prog L + (matCache prog t).length + 100 < 2 ^ 32 :=
      hretEmit t hterm
    -- conjunct 2: the static stack-room bound (value-free).
    refine ⟨hwl.stack.ret sloadChg L b t hb hterm, ?_⟩
    intro vw hvw
    -- conjunct 1: the charge-sum bound (needs the returned value `vw`).
    have hdv : MatDecC prog hwl.defsCons hwl.defEnvOrdered frT.exec.executionEnv.code
        frT.exec.pc (.tmp t) := by
      rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
      exact matDecC_of_term prog hwl.defsCons hwl.defEnvOrdered L b 0 (.tmp t) hbt
        (by simp only [matExpr_tmp]; rw [hterm]
            exact ret_sub_value (matCache prog)
              (offsetTable (matCache prog) (defsOf prog) prog.blocks) t)
        (by simp only [matExpr_tmp]; rw [hterm]
            show _ ≤ ((matCache prog t)
                        ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]).length
            simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil]
            omega)
        (by simp only [matExpr_tmp]; omega)
    have hstkC : frT.exec.stack.size
        + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp t)).length ≤ 1024 := by
      rw [hcorr.stack_nil]; simpa using hwl.stack.ret sloadChg L b t hb hterm
    refine ⟨materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered sloadChg st 0
        (fun _ => False) (.tmp t) vw frT hdv hcorr.defsSound
        (rematClosureFree_empty prog hwl.defsCons hwl.defEnvOrdered (.tmp t)) hcorr.wellScoped hcorr.storage (by nofun) (by nofun)
        hcorr.memAgree hvw hch hstkC, ?_⟩
    -- conjunct 3: the pc-pinned full-observable epilogue block
    -- (`PUSH32 0; MSTORE; PUSH32 32; PUSH32 0; RETURN`).
    intro frv hruns hcode _haddr' _hsto hstk hpc
    set lc := (matCache prog t).length with hlc
    have hemitR : emitTerm (matCache prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term
          = matCache prog t
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
      exact imm_leaf_decodeF prog (termOf prog L + lc) 0 (by omega)
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
            rw [show lc + j - (matCache prog t).length = j
                  from by rw [← hlc]; omega])
    have hdms : decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
        = some (.Smsf .MSTORE, .none) := by
      rw [hfrvcode, e33]
      have hbyte0 : (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[lc + 33]?
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
      exact imm_leaf_decodeF prog (termOf prog L + (lc + 34)) 32 (by omega)
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
            rw [show lc + 34 + j - (matCache prog t
                    ++ emitImm 0 ++ [Byte.mstore]).length = j from by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega])
    have hd0' : decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33)
        = some (.Push .PUSH32, some ((0 : Word), 32)) := by
      rw [hfrvcode, e67]
      exact imm_leaf_decodeF prog (termOf prog L + (lc + 67)) 0 (by omega)
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
            rw [show lc + 67 + j - (matCache prog t
                    ++ emitImm 0 ++ [Byte.mstore] ++ emitImm 32).length = j from by
                  simp only [List.length_append, emitImm_length, List.length_cons, List.length_nil, ← hlc]; omega])
    have hdret : decode frv.exec.executionEnv.code
        (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33 + UInt32.ofNat 33)
        = some (.System .RETURN, .none) := by
      rw [hfrvcode, e100]
      have hbyte0 : (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[lc + 100]?
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
    set off := offsetTable (matCache prog) (defsOf prog) prog.blocks dst.idx with hoff
    set dest : Word := UInt256.ofNat (off % 2 ^ 32) with hdest
    set new_pc := UInt32.ofNat off with hnew
    have hemitT : emitTerm (matCache prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term
          = emitDest off ++ [Byte.jump] := by rw [hterm]; rfl
    have hedlen : (emitDest off).length = 5 := by simp [emitDest, offsetBytesBE]
    have htermlen : (emitTerm (matCache prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length = 6 := by
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
      have hbyte0 : (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[5]? = some Byte.jump := by
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
    intro cond thenL elseL bthen belse hterm hbthen hbelse hthenlt helselt st frT cw hcorr hch
      gS sS cS dS hcp hc
    obtain ⟨hbterm, hbthenoff, hbelseoff⟩ := hwl.wf.bound_branch L b cond thenL elseL hbt hterm
    have hstkCond : frT.exec.stack.size
        + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cond)).length ≤ 1024 := by
      rw [hcorr.stack_nil]; simpa using hwl.stack.branch sloadChg L b cond thenL elseL hb hterm
    set lc := (matCache prog cond).length with hlc
    set thenOff := offsetTable (matCache prog) (defsOf prog) prog.blocks thenL.idx with hthenoff
    set elseOff := offsetTable (matCache prog) (defsOf prog) prog.blocks elseL.idx with helseoff
    set thenW : Word := UInt256.ofNat (thenOff % 2 ^ 32) with hthenW
    set elseW : Word := UInt256.ofNat (elseOff % 2 ^ 32) with helseW
    -- (1) COND MATERIALISE via `materialise_runsC_of_cleanHalt`, gas FOR FREE.
    -- the cond materialise sits at offset 0 of `emitTerm`, anchored at `frT.exec.pc = termOf`.
    have hemitT : emitTerm (matCache prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term
          = matCache prog cond
            ++ emitDest thenOff ++ [Byte.jumpi] ++ emitDest elseOff ++ [Byte.jump] := by
      rw [hterm]; rfl
    have hedlen : ∀ o, (emitDest o).length = 5 := fun o => by simp [emitDest, offsetBytesBE]
    have htermlen : (emitTerm (matCache prog)
        (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term).length = lc + 12 := by
      rw [hemitT]; simp only [List.length_append, List.length_singleton, hedlen, ← hlc]
    have hcondMatDec : MatDecC prog hwl.defsCons hwl.defEnvOrdered frT.exec.executionEnv.code
        frT.exec.pc (.tmp cond) := by
      rw [hcorr.code_eq, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt,
          show termOf prog L = termOf prog L + 0 from by omega]
      exact matDecC_of_term prog hwl.defsCons hwl.defEnvOrdered L b 0 (.tmp cond) hbt
        (by simp only [matExpr_tmp]
            intro j hj; rw [hemitT, Nat.zero_add]
            rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; rw [← hlc] at hj ⊢; omega)]
            rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton, hedlen]; rw [← hlc] at hj ⊢; omega)]
            rw [List.getElem?_append_left (by simp only [List.length_append, hedlen]; rw [← hlc] at hj ⊢; omega)]
            rw [List.getElem?_append_left (by rw [← hlc] at hj ⊢; exact hj)])
        (by simp only [matExpr_tmp]; rw [htermlen]; omega)
        (by simp only [matExpr_tmp]; omega)
    have hcondEval : V2.evalExpr st 0 (.tmp cond) = some cw := hc
    have hgasCond := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
      sloadChg st 0 (fun _ => False) (.tmp cond) cw frT hcondMatDec hcorr.defsSound
      (rematClosureFree_empty prog hwl.defsCons hwl.defEnvOrdered (.tmp cond))
      hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree hcondEval hch hstkCond
    obtain ⟨frc, hmrc, hcpc⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
      sloadChg st 0 log gS sS cS dS (fun _ => False) (.tmp cond) cw frT hcondMatDec
      hcorr.defsSound (rematClosureFree_empty prog hwl.defsCons hwl.defEnvOrdered (.tmp cond))
      hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree hcondEval hgasCond
      hstkCond hcp
    -- forward clean-halt across the cond materialise.
    have hcsC : CleanHaltsNonException frc := cleanHaltsNonException_forward hch hmrc.runs
    -- (2) DECODE BUNDLE for the branch epilogue, `frc`-relative (exactly `sim_term_edge_branch_lowered`).
    -- (`MatRunsC.pc` is `matExpr`-spelled; the `have` bridges to the cache spelling by defeq.)
    have hpcC : frc.exec.pc = frT.exec.pc + UInt32.ofNat (matCache prog cond).length := hmrc.pc
    have hfrcpc : frc.exec.pc = UInt32.ofNat (termOf prog L + lc) := by
      rw [hpcC, hcorr.pc_eq, pcOf_eq_termOf prog L b hbt, ofNat_add', ← hlc]
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
      have hbyte0 : (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[lc + 5]? = some Byte.jumpi := by
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
      have hbyte0 : (emitTerm (matCache prog)
          (offsetTable (matCache prog) (defsOf prog) prog.blocks) b.term)[lc + 11]? = some Byte.jump := by
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
    have hpushTStep : StepsTo frc (pushFrameW frc thenW 4) := stepsTo_of_next
      (stepFrame_push frc .PUSH4 thenW 4 (by nofun) hdpushT rfl rfl hgpushT hstk1)
    have hcpP : RecorderCoupled log (pushFrameW frc thenW 4) gS sS cS dS := by
      apply recorderCoupled_stepsTo_other hcpc
      · unfold isGasOp; rw [hdpushT]; rfl
      · unfold isSloadOp; rw [hdpushT]; rfl
      · unfold isCreate2Op; rw [hdpushT]; rfl
      · exact hpushTStep
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
      have hfallStep : StepsTo frp (jumpiFallthroughFrame frp ([] : Stack Word)) :=
        stepsTo_of_next (stepFrame_jumpi_fallthrough frp thenW [] hfrpjidec hfrpstk hfrpsz hgjumpi)
      set gff := jumpiFallthroughFrame frp ([] : Stack Word) with hgff
      have hcpG : RecorderCoupled log gff gS sS cS dS := by
        apply recorderCoupled_stepsTo_other hcpP
        · unfold isGasOp; rw [hfrpjidec]; rfl
        · unfold isSloadOp; rw [hfrpjidec]; rfl
        · unfold isCreate2Op; rw [hfrpjidec]; rfl
        · exact hfallStep
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
      have hpushEStep : StepsTo gff (pushFrameW gff elseW 4) := stepsTo_of_next
        (stepFrame_push gff .PUSH4 elseW 4 (by nofun) hdpushE' rfl rfl hgpushE hgffstk1)
      set gfp := pushFrameW gff elseW 4 with hgfp
      have hcpGP : RecorderCoupled log gfp gS sS cS dS := by
        apply recorderCoupled_stepsTo_other hcpG
        · unfold isGasOp; rw [hdpushE']; rfl
        · unfold isSloadOp; rw [hdpushE']; rfl
        · unfold isCreate2Op; rw [hdpushE']; rfl
        · exact hpushEStep
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
      have hjumpEStep : StepsTo gfp
          (jumpFrame gfp GasConstants.Gmid new_pc gff.exec.stack) := stepsTo_of_next
        (stepFrame_jump gfp elseW new_pc gff.exec.stack hgfpjdec hgfpstk hgfpsz hgjumpE hgetdest)
      set fj := jumpFrame gfp GasConstants.Gmid new_pc gff.exec.stack with hfj
      have hcpJ : RecorderCoupled log fj gS sS cS dS := by
        apply recorderCoupled_stepsTo_other hcpGP
        · unfold isGasOp; rw [hgfpjdec]; rfl
        · unfold isSloadOp; rw [hgfpjdec]; rfl
        · unfold isCreate2Op; rw [hgfpjdec]; rfl
        · exact hjumpEStep
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
      have hjdStep : StepsTo fj (jumpdestFrame fj) := stepsTo_of_next
        (stepFrame_jumpdest fj hfjdec hfjsz hgjd)
      have hcpJD : RecorderCoupled log (jumpdestFrame fj) gS sS cS dS := by
        apply recorderCoupled_stepsTo_other hcpJ
        · unfold isGasOp; rw [hfjdec]; rfl
        · unfold isSloadOp; rw [hfjdec]; rfl
        · unfold isCreate2Op; rw [hfjdec]; rfl
        · exact hjdStep
      obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing (sloadChg := sloadChg)
        (obs := 0) (st := st) hbelse hfjpc hfjcode hfjvalid hfjstk hfjmod hfjstore
        ((defsSoundS_empty_iff prog st).mp hcorr.defsSound) hcorr.wellScoped hfjmem hfjdec hgjd
      have hedge : Runs frT (jumpdestFrame fj) := hfrun.trans hjdrun
      exact ⟨frc, hmrc, hcpc, hgpushT, hgjumpi, fun hcontra => absurd rfl hcontra,
        fun _ => ⟨hgpushE, hgjumpE, hgjd⟩,
        elseL, jumpdestFrame fj, Or.inr ⟨rfl, rfl⟩, hedge, hjdcorr, hcpJD,
        totalGas_succ_lt hfrun hgjd⟩
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
      have htakenStep : StepsTo frp (jumpFrame frp GasConstants.Ghigh new_pc ([] : Stack Word)) :=
        stepsTo_of_next
          (stepFrame_jumpi_taken frp thenW cw new_pc [] hfrpjidec hfrpstk hfrpsz hgjumpi hcw hgetdest)
      set fj := jumpFrame frp GasConstants.Ghigh new_pc ([] : Stack Word) with hfj
      have hcpJ : RecorderCoupled log fj gS sS cS dS := by
        apply recorderCoupled_stepsTo_other hcpP
        · unfold isGasOp; rw [hfrpjidec]; rfl
        · unfold isSloadOp; rw [hfrpjidec]; rfl
        · unfold isCreate2Op; rw [hfrpjidec]; rfl
        · exact htakenStep
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
      have hjdStep : StepsTo fj (jumpdestFrame fj) := stepsTo_of_next
        (stepFrame_jumpdest fj hfjdec hfjsz hgjd)
      have hcpJD : RecorderCoupled log (jumpdestFrame fj) gS sS cS dS := by
        apply recorderCoupled_stepsTo_other hcpJ
        · unfold isGasOp; rw [hfjdec]; rfl
        · unfold isSloadOp; rw [hfjdec]; rfl
        · unfold isCreate2Op; rw [hfjdec]; rfl
        · exact hjdStep
      obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing (sloadChg := sloadChg)
        (obs := 0) (st := st) hbthen hfjpc hfjcode hfjvalid hfjstk hfjmod hfjstore
        ((defsSoundS_empty_iff prog st).mp hcorr.defsSound) hcorr.wellScoped hfjmem hfjdec hgjd
      have hedge : Runs frT (jumpdestFrame fj) := hfrun.trans hjdrun
      exact ⟨frc, hmrc, hcpc, hgpushT, hgjumpi, fun _ => hgjd,
        fun hcontra => absurd hcontra hcw,
        thenL, jumpdestFrame fj, Or.inl ⟨hcw, rfl⟩, hedge, hjdcorr, hcpJD,
        totalGas_succ_lt hfrun hgjd⟩

-- Build-enforced axiom-cleanliness: `termTies'_of_walk` and `runs_kind` depend only on
-- `[propext, Classical.choice, Quot.sound]` (no `sorry`/`native_decide`); every gas guard,
-- epilogue decode, and self-presence bridge is derived, and `CallPreservesSelf` is discharged
-- from `hprec` via the axiom-clean `callPreservesSelf_modGuards`.

/-! ### R3 Piece B — the CALL argument-push run producer and the machine-side residues

`call_args_run_of_coupled` BUILDS the CALL argument-push run (`5 × PUSH32 0`, then the
`callee`/`gasFwd` materialise runs) from `Corr` + the coupling + clean-halt — the
"no in-tree producer" half of the old R3 blocker, closed here. The two remaining
machine-side residues (`call_dispatch_of_coupled`, `call_tail_of_cleanHalt`) are
closed below, and `callRealises_of_recorded` is real assembly over them. -/

/-- One coupled `PUSH32` step: the run, the (non-recording) coupling transport, and the
forwarded clean-halt scope at the pushed frame. Gas is DERIVED from the clean-halt witness
(`next_push_of_cleanHalt`). -/
private theorem coupled_push_step {log : RunLog} {fr : Frame} {w : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hch : CleanHaltsNonException fr)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)))
    (hsz : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrameW fr w 32)
    ∧ RecorderCoupled log (pushFrameW fr w 32) gS sS cS dS
    ∧ CleanHaltsNonException (pushFrameW fr w 32) := by
  have hg : 3 ≤ fr.exec.gasAvailable.toNat := by
    have := (CleanHaltExtract.next_push_of_cleanHalt fr .PUSH32 w 32 hch (by decide) hdec
      (by decide) (by decide) hsz).1
    have hvl : GasConstants.Gverylow = 3 := rfl
    omega
  have hrun : Runs fr (pushFrameW fr w 32) :=
    runs_push fr .PUSH32 w 32 (by nofun) hdec rfl rfl hg hsz
  have hstep : stepFrame fr = .next (pushFrameW fr w 32).exec :=
    stepFrame_push fr .PUSH32 w 32 (by nofun) hdec (by decide) (by decide) hg hsz
  exact ⟨hrun,
    recorderCoupled_step_other hcp
      (by unfold isGasOp; rw [hdec]; rfl) (by unfold isSloadOp; rw [hdec]; rfl)
      (by unfold isCreate2Op; rw [hdec]; rfl) hstep,
    cleanHaltsNonException_forward hch hrun⟩

/-- **R3 Piece B, step 1 — the CALL argument-push run producer.** From `Corr` at the CALL
cursor, the coupling, and the clean-halt scope, BUILD the run to the CALL-site frame:
the five `PUSH32 0` window/value pushes (decode read off the byte layout via
`imm_leaf_decodeF`, gas from the clean-halt extractors, coupling by
`recorderCoupled_step_other`), then the `callee`/`gasFwd` materialise runs
(`recorderCoupled_matRunsC`, gas via `materialise_chargeC_le_of_cleanHalt`). The endpoint
carries the full pin bundle `sim_call_stmt`-style plus the coupling and the forwarded
clean-halt. HONEST HYPOTHESES (discovered, reported): the operand bindings `hcallee`/
`hgasfwd` (the value channel needs values — same principle as the sload arm's antecedent
key binding, header lesson 5), the closure-freeness of both operands at the ambient set
`I` (`ScopedUses` supplies them at the walk's fold set), the two static stack-room folds
(NOT derivable from `stackFits`, whose `stmtChargeDepth` is `0` on calls — a static-fold
gap), and the flagship scalar `codeFits` (permitted threading; the decode bounds need it). -/
private theorem call_args_run_of_coupled {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 : IRState} {fr0 : Frame} {cw gw : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    {I : Tmp → Prop}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcorr : Corr prog sloadChg 0 I st0 fr0 L pc)
    (hcp : RecorderCoupled log fr0 gS sS cS dS)
    (hch : CleanHaltsNonException fr0)
    (hcallee : st0.locals cs.callee = some cw)
    (hgasfwd : st0.locals cs.gasFwd = some gw)
    (hfreeCallee : RematClosureFree prog I (.tmp cs.callee))
    (hfreeGasFwd : RematClosureFree prog I (.tmp cs.gasFwd))
    (hstkCallee : 5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024)
    (hstkGasFwd : 6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024) :
    ∃ callFr : Frame,
      Runs fr0 callFr
      ∧ callFr.exec.pc = fr0.exec.pc + UInt32.ofNat
          ((emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
            ++ matCache prog cs.callee ++ matCache prog cs.gasFwd).length)
      ∧ callFr.exec.stack = gw :: cw :: 0 :: 0 :: 0 :: 0 :: 0 :: []
      ∧ callFr.exec.executionEnv.code = lower prog
      ∧ callFr.validJumps = fr0.validJumps
      ∧ callFr.exec.executionEnv.address = fr0.exec.executionEnv.address
      ∧ callFr.exec.executionEnv.canModifyState = true
      ∧ callFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory
      ∧ fr0.exec.toMachineState.activeWords.toNat
          ≤ callFr.exec.toMachineState.activeWords.toNat
      ∧ (∀ k, selfStorage callFr k = selfStorage fr0 k)
      ∧ RecorderCoupled log callFr gS sS cS dS
      ∧ CleanHaltsNonException callFr := by
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set base := pcOf prog L pc with hbase
  set cB := matCache prog cs.callee with hcB
  set gB := matCache prog cs.gasFwd with hgB
  set tailB : List UInt8 := (match cs.resultTmp with
      | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
      | none => [Byte.pop]) with htailB
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ cB ++ gB
        ++ [Byte.call] ++ tailB := rfl
  have hemitge : 165 + cB.length + gB.length + 1
      ≤ (emitStmt (matCache prog) (defsOf prog) (.call cs)).length := by
    rw [hemit0]
    simp only [List.length_append, emitImm_length, List.length_singleton]
    omega
  -- the master 32-bit bound on any byte offset within the arg block + CALL byte.
  have hbnd : ∀ k, k < 165 + cB.length + gB.length + 1 → base + k < 2 ^ 32 := by
    intro k hk
    exact call_stmt_offset_bound_of_codeFits hcodeFits hb hcur (by omega)
  -- the emit byte segment at the cursor, re-associated to the right-nested spelling.
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length →
      (flatBytes prog)[base + j]? = (emitStmt (matCache prog) (defsOf prog) (.call cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.call cs) j hbt hcur hj
  set rest6 : List UInt8 := cB ++ (gB ++ ([Byte.call] ++ tailB)) with hrest6
  have hassoc : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = emitImm 0 ++ (emitImm 0 ++ (emitImm 0 ++ (emitImm 0 ++ (emitImm 0 ++ rest6)))) := by
    rw [hemit0, hrest6]
    simp only [List.append_assoc]
  rw [hassoc] at hseg
  -- peel the five `PUSH32 0` prefixes and the operand segments off the segment fact.
  have hseg1 := segF_suffix (flatBytes prog) base (emitImm 0)
      (emitImm 0 ++ (emitImm 0 ++ (emitImm 0 ++ (emitImm 0 ++ rest6)))) hseg
  simp only [emitImm_length] at hseg1
  have hseg2 := segF_suffix (flatBytes prog) (base + 33) (emitImm 0)
      (emitImm 0 ++ (emitImm 0 ++ (emitImm 0 ++ rest6))) hseg1
  simp only [emitImm_length] at hseg2
  have hseg3 := segF_suffix (flatBytes prog) (base + 33 + 33) (emitImm 0)
      (emitImm 0 ++ (emitImm 0 ++ rest6)) hseg2
  simp only [emitImm_length] at hseg3
  have hseg4 := segF_suffix (flatBytes prog) (base + 33 + 33 + 33) (emitImm 0)
      (emitImm 0 ++ rest6) hseg3
  simp only [emitImm_length] at hseg4
  have hseg5 := segF_suffix (flatBytes prog) (base + 33 + 33 + 33 + 33) (emitImm 0) rest6 hseg4
  simp only [emitImm_length] at hseg5
  have hseg5' : ∀ j, j < rest6.length → (flatBytes prog)[base + 165 + j]? = rest6[j]? := by
    intro j hj
    have := hseg5 j hj
    rwa [show base + 33 + 33 + 33 + 33 + 33 = base + 165 from by omega] at this
  rw [hrest6] at hseg5'
  have hsegCB := segF_prefix (flatBytes prog) (base + 165) cB
      (gB ++ ([Byte.call] ++ tailB)) hseg5'
  have hsegAfterCB := segF_suffix (flatBytes prog) (base + 165) cB
      (gB ++ ([Byte.call] ++ tailB)) hseg5'
  have hsegGB := segF_prefix (flatBytes prog) (base + 165 + cB.length) gB
      ([Byte.call] ++ tailB) hsegAfterCB
  -- the five `PUSH32 0` decode anchors.
  have hd0 : decode (lower prog) (UInt32.ofNat base)
      = some (.Push .PUSH32, some ((0 : Word), 32)) :=
    imm_leaf_decodeF prog base 0 (by have := hbnd 33 (by omega); omega)
      (segF_prefix (flatBytes prog) base (emitImm 0) _ hseg)
  have hd1 : decode (lower prog) (UInt32.ofNat (base + 33))
      = some (.Push .PUSH32, some ((0 : Word), 32)) :=
    imm_leaf_decodeF prog (base + 33) 0 (by have := hbnd 66 (by omega); omega)
      (segF_prefix (flatBytes prog) (base + 33) (emitImm 0) _ hseg1)
  have hd2 : decode (lower prog) (UInt32.ofNat (base + 33 + 33))
      = some (.Push .PUSH32, some ((0 : Word), 32)) :=
    imm_leaf_decodeF prog (base + 33 + 33) 0 (by have := hbnd 99 (by omega); omega)
      (segF_prefix (flatBytes prog) (base + 33 + 33) (emitImm 0) _ hseg2)
  have hd3 : decode (lower prog) (UInt32.ofNat (base + 33 + 33 + 33))
      = some (.Push .PUSH32, some ((0 : Word), 32)) :=
    imm_leaf_decodeF prog (base + 33 + 33 + 33) 0 (by have := hbnd 132 (by omega); omega)
      (segF_prefix (flatBytes prog) (base + 33 + 33 + 33) (emitImm 0) _ hseg3)
  have hd4 : decode (lower prog) (UInt32.ofNat (base + 33 + 33 + 33 + 33))
      = some (.Push .PUSH32, some ((0 : Word), 32)) :=
    imm_leaf_decodeF prog (base + 33 + 33 + 33 + 33) 0 (by have := hbnd 165 (by omega); omega)
      (segF_prefix (flatBytes prog) (base + 33 + 33 + 33 + 33) (emitImm 0) _ hseg4)
  -- == the five coupled pushes ==
  have hcode0 : fr0.exec.executionEnv.code = lower prog := hcorr.code_eq
  have hpc0 : fr0.exec.pc = UInt32.ofNat base := hcorr.pc_eq
  have hstk0 : fr0.exec.stack = [] := hcorr.stack_nil
  obtain ⟨hr1, hcp1, hch1⟩ := coupled_push_step hcp hch
    (by rw [hcode0, hpc0]; exact hd0)
    (by rw [hstk0]; show (0 : ℕ) + 1 ≤ 1024; omega)
  set f1 := pushFrameW fr0 0 32 with hf1
  have hf1code : f1.exec.executionEnv.code = lower prog := hcode0
  have hf1pc : f1.exec.pc = UInt32.ofNat (base + 33) := by
    rw [hf1, pushFrameW_pc, push32_pcΔ, hpc0, ofNat_add']
  have hf1stk : f1.exec.stack = (0 : Word) :: [] := by
    rw [hf1, pushFrameW_stack', hstk0]; rfl
  obtain ⟨hr2, hcp2, hch2⟩ := coupled_push_step hcp1 hch1
    (by rw [hf1code, hf1pc]; exact hd1)
    (by rw [hf1stk]; show (1 : ℕ) + 1 ≤ 1024; omega)
  set f2 := pushFrameW f1 0 32 with hf2
  have hf2code : f2.exec.executionEnv.code = lower prog := hf1code
  have hf2pc : f2.exec.pc = UInt32.ofNat (base + 33 + 33) := by
    rw [hf2, pushFrameW_pc, push32_pcΔ, hf1pc, ofNat_add']
  have hf2stk : f2.exec.stack = (0 : Word) :: (0 : Word) :: [] := by
    rw [hf2, pushFrameW_stack', hf1stk]; rfl
  obtain ⟨hr3, hcp3, hch3⟩ := coupled_push_step hcp2 hch2
    (by rw [hf2code, hf2pc]; exact hd2)
    (by rw [hf2stk]; show (2 : ℕ) + 1 ≤ 1024; omega)
  set f3 := pushFrameW f2 0 32 with hf3
  have hf3code : f3.exec.executionEnv.code = lower prog := hf2code
  have hf3pc : f3.exec.pc = UInt32.ofNat (base + 33 + 33 + 33) := by
    rw [hf3, pushFrameW_pc, push32_pcΔ, hf2pc, ofNat_add']
  have hf3stk : f3.exec.stack = (0 : Word) :: (0 : Word) :: (0 : Word) :: [] := by
    rw [hf3, pushFrameW_stack', hf2stk]; rfl
  obtain ⟨hr4, hcp4, hch4⟩ := coupled_push_step hcp3 hch3
    (by rw [hf3code, hf3pc]; exact hd3)
    (by rw [hf3stk]; show (3 : ℕ) + 1 ≤ 1024; omega)
  set f4 := pushFrameW f3 0 32 with hf4
  have hf4code : f4.exec.executionEnv.code = lower prog := hf3code
  have hf4pc : f4.exec.pc = UInt32.ofNat (base + 33 + 33 + 33 + 33) := by
    rw [hf4, pushFrameW_pc, push32_pcΔ, hf3pc, ofNat_add']
  have hf4stk : f4.exec.stack = (0 : Word) :: (0 : Word) :: (0 : Word) :: (0 : Word) :: [] := by
    rw [hf4, pushFrameW_stack', hf3stk]; rfl
  obtain ⟨hr5, hcp5, hch5⟩ := coupled_push_step hcp4 hch4
    (by rw [hf4code, hf4pc]; exact hd4)
    (by rw [hf4stk]; show (4 : ℕ) + 1 ≤ 1024; omega)
  set f5 := pushFrameW f4 0 32 with hf5
  have hf5code : f5.exec.executionEnv.code = lower prog := hf4code
  have hf5pc : f5.exec.pc = UInt32.ofNat (base + 165) := by
    rw [hf5, pushFrameW_pc, push32_pcΔ, hf4pc, ofNat_add',
        show base + 33 + 33 + 33 + 33 + 33 = base + 165 from by omega]
  have hf5stk : f5.exec.stack
      = (0 : Word) :: (0 : Word) :: (0 : Word) :: (0 : Word) :: (0 : Word) :: [] := by
    rw [hf5, pushFrameW_stack', hf4stk]; rfl
  -- fr0 → f5 transports (pushes preserve env/accounts/memory).
  have hf5sto : ∀ k, selfStorage f5 k = selfStorage fr0 k := by
    intro k
    rw [hf5, pushFrameW_selfStorage, hf4, pushFrameW_selfStorage, hf3, pushFrameW_selfStorage,
        hf2, pushFrameW_selfStorage, hf1, pushFrameW_selfStorage]
  have hf5mem : f5.exec.toMachineState.memory = fr0.exec.toMachineState.memory := rfl
  have hf5aw : f5.exec.toMachineState.activeWords = fr0.exec.toMachineState.activeWords := rfl
  have hstore5 : StorageAgree st0 f5 := hcorr.storage.transport hf5sto
  have hmem5 : MemRealises prog st0 f5 := hcorr.memAgree.transport hf5mem (by rw [hf5aw])
  -- == materialise `callee` from `f5` (value channel + coupling; gas from clean-halt) ==
  have hdcCallee : MatDecC prog hwl.defsCons hwl.defEnvOrdered f5.exec.executionEnv.code
      f5.exec.pc (.tmp cs.callee) := by
    rw [hf5code, hf5pc]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp cs.callee) (base + 165)
      (by simp only [matExpr_tmp, ← hcB]
          have := hbnd (165 + cB.length) (by omega)
          omega)
      (by simp only [matExpr_tmp, ← hcB]; exact hsegCB)
  have hevCallee : evalExpr st0 0 (.tmp cs.callee) = some cw := hcallee
  have hstk5C : f5.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cs.callee)).length ≤ 1024 := by
    rw [hf5stk]
    simp only [chargeExpr_tmp]
    show 5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024
    exact hstkCallee
  have hgasCallee := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 I (.tmp cs.callee) cw f5 hdcCallee hcorr.defsSound hfreeCallee
    hcorr.wellScoped hstore5 (by nofun) (by nofun) hmem5 hevCallee hch5 hstk5C
  obtain ⟨frc, hmrc, hcpc⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 log gS sS cS dS I (.tmp cs.callee) cw f5 hdcCallee hcorr.defsSound
    hfreeCallee hcorr.wellScoped hstore5 (by nofun) (by nofun) hmem5 hevCallee
    hgasCallee hstk5C hcp5
  have hchc : CleanHaltsNonException frc := cleanHaltsNonException_forward hch5 hmrc.runs
  have hfrccode : frc.exec.executionEnv.code = lower prog := by rw [hmrc.code, hf5code]
  have hfrcpc : frc.exec.pc = UInt32.ofNat (base + 165 + cB.length) := by
    have h := hmrc.pc
    simp only [matExpr_tmp, ← hcB] at h
    rw [h, hf5pc, ofNat_add']
  have hfrcstk : frc.exec.stack
      = cw :: (0 : Word) :: (0 : Word) :: (0 : Word) :: (0 : Word) :: (0 : Word) :: [] := by
    rw [hmrc.stack, hf5stk]; rfl
  have hstoreC : StorageAgree st0 frc := hstore5.transport hmrc.storage
  have hmemC : MemRealises prog st0 frc := hmem5.transport hmrc.memBytes hmrc.memActive
  -- == materialise `gasFwd` from `frc` ==
  have hdcGasFwd : MatDecC prog hwl.defsCons hwl.defEnvOrdered frc.exec.executionEnv.code
      frc.exec.pc (.tmp cs.gasFwd) := by
    rw [hfrccode, hfrcpc]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp cs.gasFwd)
      (base + 165 + cB.length)
      (by simp only [matExpr_tmp, ← hgB]
          have := hbnd (165 + cB.length + gB.length) (by omega)
          omega)
      (by simp only [matExpr_tmp, ← hgB]; exact hsegGB)
  have hevGasFwd : evalExpr st0 0 (.tmp cs.gasFwd) = some gw := hgasfwd
  have hstkCG : frc.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cs.gasFwd)).length ≤ 1024 := by
    rw [hfrcstk]
    simp only [chargeExpr_tmp]
    show 6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024
    exact hstkGasFwd
  have hgasGasFwd := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 I (.tmp cs.gasFwd) gw frc hdcGasFwd hcorr.defsSound hfreeGasFwd
    hcorr.wellScoped hstoreC (by nofun) (by nofun) hmemC hevGasFwd hchc hstkCG
  obtain ⟨frg, hmrg, hcpg⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 log gS sS cS dS I (.tmp cs.gasFwd) gw frc hdcGasFwd hcorr.defsSound
    hfreeGasFwd hcorr.wellScoped hstoreC (by nofun) (by nofun) hmemC hevGasFwd
    hgasGasFwd hstkCG hcpc
  -- == assemble the endpoint bundle ==
  have hruns : Runs fr0 frg :=
    hr1.trans (hr2.trans (hr3.trans (hr4.trans (hr5.trans (hmrc.runs.trans hmrg.runs)))))
  refine ⟨frg, hruns, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcpg,
    cleanHaltsNonException_forward hchc hmrg.runs⟩
  · -- pc: fr0.pc + (165 + |cB| + |gB|).
    have hlen : (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
        ++ matCache prog cs.callee ++ matCache prog cs.gasFwd).length
        = 165 + cB.length + gB.length := by
      simp only [List.length_append, emitImm_length, ← hcB, ← hgB]
    have h := hmrg.pc
    simp only [matExpr_tmp, ← hgB] at h
    rw [h, hfrcpc, hlen, hpc0, ofNat_add', ofNat_add']
    congr 1
    omega
  · -- stack: `gw :: cw :: 0⁵`.
    rw [hmrg.stack, hfrcstk]; rfl
  · rw [hmrg.code, hfrccode]
  · rw [hmrg.validJumps, hmrc.validJumps, hf5, pushFrameW_validJumps, hf4,
        pushFrameW_validJumps, hf3, pushFrameW_validJumps, hf2, pushFrameW_validJumps,
        hf1, pushFrameW_validJumps]
  · rw [hmrg.addr, hmrc.addr]; rfl
  · rw [hmrg.canMod, hmrc.canMod]
    show fr0.exec.executionEnv.canModifyState = true
    exact hcorr.can_modify
  · rw [hmrg.memBytes, hmrc.memBytes, hf5mem]
  · calc fr0.exec.toMachineState.activeWords.toNat
        = f5.exec.toMachineState.activeWords.toNat := by rw [hf5aw]
      _ ≤ frc.exec.toMachineState.activeWords.toNat := hmrc.memActive
      _ ≤ frg.exec.toMachineState.activeWords.toNat := hmrg.memActive
  · intro k
    rw [hmrg.storage k, hmrc.storage k, hf5sto k]

/-! #### The no-descent-at-depth induction (the CALL dispatch's depth-guard producer)

`driveLog`'s only call-record writes happen at a top-level CALL delivery, and every descent
(`.needsCall`/`.needsCreate`) is guarded by `depth < 1024` at the stepping frame
(`stepFrame_needsCall_depth`/`stepFrame_needsCreate_depth`, Engine/Descent). `.next` steps
preserve the execution environment (`stepFrame_next_execEnvAddr`), so a top-level restart
from a frame at depth `≥ 1024` walks `.next`/`.halted` forever at that depth and delivers
its call accumulator UNCHANGED. Contrapositive: a coupled nonempty call suffix forces
`depth < 1024` at the coupled frame. -/

/-- A top-level `.inr` delivery with an empty pending stack returns its call accumulator
verbatim. -/
private theorem driveLog_inr_calls :
    ∀ (fuel : ℕ) (r : FrameResult) (g : List Word) (s : List Nat) (c : List CallRecord)
      (d : List CreateRecord) {obs : FrameResult} {gS : List Word} {sS : List Nat}
      {cS : List CallRecord} {dS : List CreateRecord},
      driveLog fuel [] (.inr r) g s c d = .ok (obs, gS, sS, cS, dS) → cS = c := by
  intro fuel r g s c d obs gS sS cS dS h
  cases fuel with
  | zero => exact absurd h (by simp [driveLog])
  | succ n =>
    unfold driveLog at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.2.2.1.symm

/-- **The no-descent-at-depth induction.** A successful top-level `driveLog` run from a frame
at depth `≥ 1024` delivers its call accumulator unchanged: `.needsCall`/`.needsCreate` are
depth-guarded (never fire), `.next` preserves the environment (the depth rides along), and
the `.halted` delivery returns the accumulator verbatim. -/
private theorem driveLog_calls_const_of_depth :
    ∀ (fuel : ℕ) (fr : Frame) (g : List Word) (s : List Nat) (c : List CallRecord)
      (d : List CreateRecord) {obs : FrameResult} {gS : List Word} {sS : List Nat}
      {cS : List CallRecord} {dS : List CreateRecord},
      1024 ≤ fr.exec.executionEnv.depth →
      driveLog fuel [] (.inl fr) g s c d = .ok (obs, gS, sS, cS, dS) →
      cS = c := by
  intro fuel
  induction fuel with
  | zero =>
    intro fr g s c d obs gS sS cS dS _ h
    exact absurd h (by simp [driveLog])
  | succ n ih =>
    intro fr g s c d obs gS sS cS dS hdepth h
    cases hstep : stepFrame fr with
    | next exec =>
      have hdepth' : 1024 ≤ exec.executionEnv.depth := by
        rw [stepFrame_next_execEnvAddr hstep]; exact hdepth
      unfold driveLog at h
      simp only [hstep] at h
      split_ifs at h with h1 h2 h3
      · exact ih { fr with exec := exec } _ _ c _ hdepth' h
      · exact ih { fr with exec := exec } _ _ c _ hdepth' h
      · exact ih { fr with exec := exec } _ _ c _ hdepth' h
      · exact ih { fr with exec := exec } _ _ c _ hdepth' h
    | halted halt =>
      unfold driveLog at h
      simp only [hstep] at h
      exact driveLog_inr_calls n _ g s c d h
    | needsCall params pending =>
      exact absurd (stepFrame_needsCall_depth hstep) (by omega)
    | needsCreate params pending =>
      exact absurd (stepFrame_needsCreate_depth hstep) (by omega)

/-- A top-level `.inr` delivery with an empty pending stack returns its **create** accumulator
verbatim (the CREATE twin of `driveLog_inr_calls`). -/
private theorem driveLog_inr_creates :
    ∀ (fuel : ℕ) (r : FrameResult) (g : List Word) (s : List Nat) (c : List CallRecord)
      (d : List CreateRecord) {obs : FrameResult} {gS : List Word} {sS : List Nat}
      {cS : List CallRecord} {dS : List CreateRecord},
      driveLog fuel [] (.inr r) g s c d = .ok (obs, gS, sS, cS, dS) → dS = d := by
  intro fuel r g s c d obs gS sS cS dS h
  cases fuel with
  | zero => exact absurd h (by simp [driveLog])
  | succ n =>
    unfold driveLog at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.2.2.2.symm

-- NOTE (CREATE2 soft-fail recorder alignment, 2026-07-11): the create-channel twin of
-- `driveLog_calls_const_of_depth` — `driveLog_creates_const_of_depth` — has been RETIRED. Under
-- the new recorder (`Spec/Recorder.lean` `isCreate2Op`/`softFailCreateRecord`) a top-level CREATE2
-- at `depth ≥ 1024` SOFT-FAILS to a `.next` step and NOW RECORDS a soft-fail create entry (the
-- descend guard `depth < 1024` fails, so `createArm` takes the `.next` fallback and the recorder's
-- new create2 gate fires). So the create accumulator is NO LONGER constant at `depth ≥ 1024`, and
-- "a nonempty coupled create suffix forces `depth < 1024`" is no longer a theorem. The depth guard
-- for the descend arm of `create_dispatch_of_coupled` is now supplied by the two-arm disjunction
-- reshape (design spec §4), not by this induction. The CALL channel twin
-- (`driveLog_calls_const_of_depth`, above) is UNAFFECTED — lowered CALL never records a soft-fail.

/-- **R3 Piece B, step 2 — the CALL dispatch bundle** (CLOSED). At a coupled top-level frame
decoding `CALL` with the lowered argument stack
`gasFwd :: callee :: 0 :: 0 :: 0 :: 0 :: 0` and `canModifyState`, the step is
`.needsCall cp pending` with the pending pins the resume half consumes.

How each guard is discharged (nothing supplied to the flagship):
* the `value ≠ 0` static-mode screen is skipped (`value = 0` — the third pushed zero);
* the zero in/out windows make the memory-expansion witness trivial and its charge `0`;
* the `charge (gasCap + extraCost)` gate is DERIVED from the clean-halt witness (a failing
  charge exceptions — `stepFrame`'s dispatch error routes to `.halted (.exception _)`,
  contradicting `hch`), via the `CleanHaltExtract` §6 CALL brick
  (`call_extraCost_le_of_cleanHalt` / `stepFrame_call_oog`);
* the funds guard holds (`0 ≤ balance` at `Word`);
* the DEPTH guard `depth < 1024` is DERIVED FROM THE COUPLING: were `depth ≥ 1024`, the
  `.next` fallback would fire here AND at every later top-level frame (`.next` steps
  preserve `executionEnv` — `stepFrame_next_execEnvAddr` — and both `callArm`/`createArm`
  guard their descents by `depth < 1024`), so the restart from this frame could never
  deliver a call record (`driveLog_calls_const_of_depth`) — contradicting the nonempty
  coupled suffix `rec :: cS'`;
* the pending pins are then `rfl` off `BytecodeLayer.System.stepFrame_call`'s named
  `callPending` (whose saved frame is `callFr` with only `gasAvailable` recharged). -/
theorem call_dispatch_of_coupled {log : RunLog} {callFr : Frame} {cw gw : Word}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS' : List CallRecord}
    {dS : List CreateRecord}
    (hcp : RecorderCoupled log callFr gS sS (rec :: cS') dS)
    (hch : CleanHaltsNonException callFr)
    (hdec : decode callFr.exec.executionEnv.code callFr.exec.pc
      = some (.System .CALL, .none))
    (hstk : callFr.exec.stack = gw :: cw :: 0 :: 0 :: 0 :: 0 :: 0 :: [])
    (hmod : callFr.exec.executionEnv.canModifyState = true) :
    ∃ (cp : CallParams) (pending : PendingCall),
      stepFrame callFr = .needsCall cp pending
      ∧ pending.frame.exec.executionEnv = callFr.exec.executionEnv
      ∧ pending.frame.validJumps = callFr.validJumps
      ∧ pending.frame.exec.pc = callFr.exec.pc
      ∧ pending.frame.exec.toMachineState.memory = callFr.exec.toMachineState.memory
      ∧ pending.frame.exec.toMachineState.activeWords
          = callFr.exec.toMachineState.activeWords
      ∧ pending.stack = ([] : Stack Word)
      ∧ pending.inSize = 0 ∧ pending.outSize = 0 := by
  -- the depth guard, from the COUPLING: at depth ≥ 1024 the restart never descends, so it
  -- delivers no call record — contradicting the nonempty coupled suffix `rec :: cS'`.
  have hdepth : callFr.exec.executionEnv.depth < 1024 := by
    by_contra hge
    obtain ⟨⟨fuel', hrestart⟩, _, _, _, _⟩ := hcp
    have hnil : (rec :: cS' : List CallRecord) = [] :=
      driveLog_calls_const_of_depth fuel' callFr [] [] [] [] (by omega) hrestart
    exact absurd hnil (by simp)
  -- the CALL charge gate, from the clean-halt (CleanHaltExtract §6).
  have hextra :=
    Lir.CleanHaltExtract.call_extraCost_le_of_cleanHalt callFr gw cw hch hdec hstk
  have hsz : callFr.exec.stack.size ≤ 1024 := by
    rw [hstk]; show (7 : ℕ) ≤ 1024; omega
  have hstep :=
    BytecodeLayer.System.stepFrame_call callFr gw cw hdec hstk hsz hmod hdepth hextra
  exact ⟨callChildParams callFr cw gw, callPending callFr cw gw, hstep,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **R3 Piece B, step 3 — the Route-B tail at the pinned resume frame** (CLOSED). At a
frame running `lower prog` one byte past this cursor's CALL byte with the success flag
alone on the stack, the tail realises: `resultTmp = some t` runs `PUSH32 (slotOf t); MSTORE`
(`stash_tail_runs` fed the byte-layout decode anchors — the tail segment peeled off the
`emitStmt` layout via `segF_suffix`, bounded through `codeFits` — and the clean-halt
gas/expansion witnesses `next_push_of_cleanHalt`/`next_mstore_of_cleanHalt`);
`resultTmp = none` runs `POP` (exp003's `runs_pop`, fed by the `CleanHaltExtract` §6
`next_pop_of_cleanHalt` gas brick). -/
theorem call_tail_of_cleanHalt {prog : Program} {L : Label} {b : Block} {pc : Nat}
    {cs : CallSpec} {resumeFr : Frame}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcode : resumeFr.exec.executionEnv.code = lower prog)
    (hpc : resumeFr.exec.pc = UInt32.ofNat (pcOf prog L pc
      + (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ matCache prog cs.callee ++ matCache prog cs.gasFwd).length + 1))
    (hch : CleanHaltsNonException resumeFr)
    (hslotaddr : ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits) :
    ∀ flag : Word, resumeFr.exec.stack = flag :: [] →
      (∀ (t : Tmp), cs.resultTmp = some t →
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr,
            Runs resumeFr endFr
          ∧ endFr.exec.toMachineState.memory
              = ((resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag)).memory
          ∧ endFr.exec.toMachineState.activeWords
              = ((resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag)).activeWords
          ∧ endFr.exec.pc = resumeFr.exec.pc + UInt32.ofNat 34
          ∧ endFr.exec.executionEnv.code = resumeFr.exec.executionEnv.code
          ∧ endFr.validJumps = resumeFr.validJumps
          ∧ endFr.exec.executionEnv.address = resumeFr.exec.executionEnv.address
          ∧ endFr.exec.executionEnv.canModifyState
              = resumeFr.exec.executionEnv.canModifyState
          ∧ (∀ k, selfStorage endFr k = selfStorage resumeFr k)
          ∧ endFr.exec.stack = [])
      ∧ (cs.resultTmp = none → Runs resumeFr (popFrame resumeFr [])) := by
  intro flag hstkflag
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set base := pcOf prog L pc with hbase
  set argsB : List UInt8 := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hargsB
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length →
      (flatBytes prog)[base + j]? = (emitStmt (matCache prog) (defsOf prog) (.call cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.call cs) j hbt hcur hj
  have hpc' : resumeFr.exec.pc = UInt32.ofNat (base + (argsB.length + 1)) := by
    rw [hpc]; congr 1
  have hsz1 : resumeFr.exec.stack.size + 1 ≤ 1024 := by
    rw [hstkflag]; show (1 : ℕ) + 1 ≤ 1024; omega
  constructor
  · -- == `resultTmp = some t`: the `PUSH32 (slotOf t); MSTORE` stash tail ==
    intro t ht
    obtain ⟨hslot64, hslotplat⟩ := hslotaddr t ht
    refine ⟨hslot64, hslotplat, ?_⟩
    -- byte layout: `emitStmt = (argsB ++ [CALL]) ++ (emitImm (slotOf t) ++ [MSTORE])`.
    have hemit : emitStmt (matCache prog) (defsOf prog) (.call cs)
        = (argsB ++ [Byte.call]) ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) := by
      have h0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
          = argsB ++ [Byte.call]
            ++ (match cs.resultTmp with
                | some t' => emitImm (UInt256.ofNat (slotOf t')) ++ [Byte.mstore]
                | none => [Byte.pop]) := rfl
      rw [h0, ht]
    have hlen : (emitStmt (matCache prog) (defsOf prog) (.call cs)).length
        = argsB.length + 35 := by
      rw [hemit]
      simp only [List.length_append, List.length_singleton, emitImm_length]
    -- the 32-bit bound on the whole tail (through `codeFits`).
    have hbnd : base + (argsB.length + 34) < 2 ^ 32 :=
      call_stmt_offset_bound_of_codeFits hcodeFits hb hcur (by omega)
    -- the tail byte segment, rebased one past the CALL byte.
    have hsegTail := segF_suffix (flatBytes prog) base (argsB ++ [Byte.call])
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) (by rw [← hemit]; exact hseg)
    have hsegTail' : ∀ j, j < (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]).length →
        (flatBytes prog)[base + (argsB.length + 1) + j]?
          = (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])[j]? := by
      intro j hj
      have h := hsegTail j hj
      rwa [show base + (argsB ++ [Byte.call]).length + j = base + (argsB.length + 1) + j from by
            simp only [List.length_append, List.length_singleton]] at h
    -- the two decode anchors.
    have hdpushT : decode (lower prog) (UInt32.ofNat (base + (argsB.length + 1)))
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) :=
      imm_leaf_decodeF prog (base + (argsB.length + 1)) (UInt256.ofNat (slotOf t))
        (by omega)
        (segF_prefix (flatBytes prog) (base + (argsB.length + 1))
          (emitImm (UInt256.ofNat (slotOf t))) [Byte.mstore] hsegTail')
    have hdmstoreT : decode (lower prog) (UInt32.ofNat (base + (argsB.length + 1) + 33))
        = some (.Smsf .MSTORE, .none) := by
      have hpi : Evm.parseInstr Byte.mstore = .Smsf .MSTORE := by decide
      rw [← hpi]
      exact nonpush_leaf_decodeF prog (base + (argsB.length + 1)) 33 Byte.mstore
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])
        (by omega)
        (by rw [List.getElem?_append_right (by rw [emitImm_length])]
            simp [emitImm_length])
        (by decide) hsegTail'
    have hdpush : decode resumeFr.exec.executionEnv.code resumeFr.exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) := by
      rw [hcode, hpc']; exact hdpushT
    have hdmstore : decode resumeFr.exec.executionEnv.code (resumeFr.exec.pc + UInt32.ofNat 33)
        = some (.Smsf .MSTORE, .none) := by
      rw [hcode, hpc', ofNat_add']; exact hdmstoreT
    -- gas + expansion witnesses from the clean-halt chain.
    have hgasPush : 3 ≤ resumeFr.exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt resumeFr .PUSH32
        (UInt256.ofNat (slotOf t)) 32 hch (by decide) hdpush (by decide) (by decide) hsz1).1
      have hvl : (GasConstants.Gverylow : ℕ) = 3 := rfl
      omega
    have hrunPush : Runs resumeFr (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32) :=
      runs_push resumeFr .PUSH32 (UInt256.ofNat (slotOf t)) 32 (by nofun) hdpush rfl rfl
        hgasPush hsz1
    have hchP : CleanHaltsNonException (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32) :=
      cleanHaltsNonException_forward hch hrunPush
    have hfrpstk : (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32).exec.stack
        = UInt256.ofNat (slotOf t) :: flag :: [] := by
      rw [pushFrameW_stack', hstkflag]; rfl
    have hfrpdec : decode
        (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
        (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32).exec.pc
          = some (.Smsf .MSTORE, .none) := by
      rw [pushFrameW_code, pushFrameW_pc, push32_pcΔ]
      exact hdmstore
    obtain ⟨words', hmem, hgasMem, hgasVL, _⟩ :=
      CleanHaltExtract.next_mstore_of_cleanHalt
        (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32) (UInt256.ofNat (slotOf t)) flag []
        hchP hfrpdec hfrpstk (by rw [hfrpstk]; show (2 : ℕ) ≤ 1024; omega)
    -- the stash tail, assembled.
    have hstash := stash_tail_runs resumeFr (slotOf t) flag [] words' hstkflag hdpush
      hdmstore hsz1 hgasPush hmem hgasMem hgasVL
    exact ⟨_, hstash.runs, hstash.memory, hstash.activeWords, hstash.pc, hstash.code,
      hstash.validJumps, hstash.addr, hstash.canMod, hstash.storage, hstash.stack⟩
  · -- == `resultTmp = none`: the fire-and-forget `POP` ==
    intro hnone
    have hemit : emitStmt (matCache prog) (defsOf prog) (.call cs)
        = (argsB ++ [Byte.call]) ++ [Byte.pop] := by
      have h0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
          = argsB ++ [Byte.call]
            ++ (match cs.resultTmp with
                | some t' => emitImm (UInt256.ofNat (slotOf t')) ++ [Byte.mstore]
                | none => [Byte.pop]) := rfl
      rw [h0, hnone]
    have hlen : (emitStmt (matCache prog) (defsOf prog) (.call cs)).length
        = argsB.length + 2 := by
      rw [hemit]
      simp only [List.length_append, List.length_singleton]
    have hbnd : base + (argsB.length + 1) < 2 ^ 32 :=
      call_stmt_offset_bound_of_codeFits hcodeFits hb hcur (by omega)
    have hdpopT : decode (lower prog) (UInt32.ofNat (base + (argsB.length + 1)))
        = some (.Smsf .POP, .none) := by
      have hpi : Evm.parseInstr Byte.pop = .Smsf .POP := by decide
      rw [← hpi]
      exact nonpush_leaf_decodeF prog base (argsB.length + 1) Byte.pop
        (emitStmt (matCache prog) (defsOf prog) (.call cs)) hbnd
        (by rw [hemit, List.getElem?_append_right (by
              simp only [List.length_append, List.length_singleton]; omega)]
            simp only [List.length_append, List.length_singleton]
            rw [show argsB.length + 1 - (argsB.length + 1) = 0 from by omega]
            rfl)
        (by decide) hseg
    have hdpop : decode resumeFr.exec.executionEnv.code resumeFr.exec.pc
        = some (.Smsf .POP, .none) := by
      rw [hcode, hpc']; exact hdpopT
    have hszP : resumeFr.exec.stack.size ≤ 1024 := by
      rw [hstkflag]; show (1 : ℕ) ≤ 1024; omega
    have hgasPop : GasConstants.Gbase ≤ resumeFr.exec.gasAvailable.toNat :=
      (CleanHaltExtract.next_pop_of_cleanHalt resumeFr flag [] hch hdpop hstkflag hszP).1
    exact runs_pop resumeFr flag [] hdpop hstkflag hszP hgasPop

/-- **R3 — call realisation from the log** (relocated; the original design docstring is at
the retired cursor near the top of this file / in git history). CLOSED as real assembly:
`call_args_run_of_coupled` (Piece B step 1, closed) → `call_dispatch_of_coupled` (step 2,
closed) → the CallsCode seam rules out the precompile/immediate arm →
`recorderCoupled_call_extract` (Piece A, closed) identifies the head record →
`call_tail_of_cleanHalt` (step 3, closed) supplies the Route-B tail →
`callRealises_of_recorded_finish` (closed) discharges the bundle.

STATEMENT CHANGES (honest discovered hypotheses; none a per-event tie, none public):
`hcodeFits` (the flagship scalar, permitted threading); `hcc` (the CallsCode seam at the
cursor's reachable frames — already a flagship seam via `PrecompileAssumptions`); the
operand bindings + closure-freeness (the sload-arm antecedent principle, header lesson 5);
the two stack-room folds and the result-slot addressability (static facts MISSING from
`stackFits`/`IRWellFormed.slotAddr`, which do not cover call operands/results — reported
static-fold gaps). -/
theorem callRealises_of_recorded {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 : IRState} {fr0 : Frame} {cw gw : Word}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS' : List CallRecord}
    {dS : List CreateRecord} {I : Tmp → Prop}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcp : RecorderCoupled log fr0 gS sS (rec :: cS') dS)
    (hch : CleanHaltsNonException fr0)
    (haddr : fr0.exec.executionEnv.address = self)
    (hcc : ∀ fr', Runs fr0 fr' → CallsCode fr')
    (hcallee : st0.locals cs.callee = some cw)
    (hgasfwd : st0.locals cs.gasFwd = some gw)
    (hfreeCallee : RematClosureFree prog I (.tmp cs.callee))
    (hfreeGasFwd : RematClosureFree prog I (.tmp cs.gasFwd))
    (hstkCallee : 5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024)
    (hstkGasFwd : 6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024)
    (hslotaddr : ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits) :
    CallRealisesS prog sloadChg I L b pc cs st0
      (match cs.resultTmp with
        | some t' => { st0 with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key }.setLocal
                        t' (callSuccessFlag rec.result rec.pending)
        | none   => { st0 with world := fun key =>
                        evmCallOracle.postStorage rec.result rec.pending self key })
      fr0 := by
  intro hcorr
  classical
  -- Piece B step 1: the argument-push run.
  obtain ⟨callFr, hargs, hcallpc, hcallstk, hcallcode, hcallvj, hcalladdr, hcallmod,
      hcallmem, hcallact, _hcallsto, hcpcall, hchcall⟩ :=
    call_args_run_of_coupled hwl hcodeFits hb hcur hcorr hcp hch hcallee hgasfwd
      hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set argsB := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hargsB
  -- the CALL byte decode at `callFr` (byte layout + `codeFits`).
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = argsB ++ [Byte.call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none => [Byte.pop]) := rfl
  have hcallbyte : (emitStmt (matCache prog) (defsOf prog) (.call cs))[argsB.length]?
      = some Byte.call := by
    rw [hemit0, List.getElem?_append_left (by
          simp only [List.length_append, List.length_singleton]; omega),
        List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length →
      (flatBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.call cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.call cs) j hbt hcur hj
  have hargslt : argsB.length
      < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length := by
    rw [hemit0]
    simp only [List.length_append, List.length_singleton]
    omega
  have hdecCall : decode callFr.exec.executionEnv.code callFr.exec.pc
      = some (.System .CALL, .none) := by
    rw [hcallcode, hcallpc, hcorr.pc_eq, ofNat_add']
    have h := nonpush_leaf_decodeF prog (pcOf prog L pc) argsB.length Byte.call
      (emitStmt (matCache prog) (defsOf prog) (.call cs))
      (call_stmt_offset_bound_of_codeFits hcodeFits hb hcur hargslt)
      hcallbyte (by decide) hseg
    simpa using h
  -- Piece B step 2: the dispatch bundle.
  obtain ⟨cp, pending, hstep, henv, hvj, hpcpin, hmempin, hawpin, hstkpin, hinS, houtS⟩ :=
    call_dispatch_of_coupled hcpcall hchcall hdecCall hcallstk hcallmod
  -- the CallsCode seam rules out the precompile/immediate arm.
  have hccF : CallsCode callFr := hcc callFr hargs
  obtain ⟨child, hbegin⟩ : ∃ child, beginCall cp = .inl child := by
    cases hbc : beginCall cp with
    | inl c => exact ⟨c, rfl⟩
    | inr r =>
        exact absurd hbc (beginCall_isCode_of_codeSource_ne_precompiled
          (hccF cp pending hstep) r)
  -- Piece A: identify the coupled head record with this CALL.
  obtain ⟨childRes, hcall, hrec, _⟩ := recorderCoupled_call_extract hcpcall hstep hbegin
  have hpend : rec.pending = pending := by rw [hrec]
  have hresult : rec.result = childRes.toCallResult := by rw [hrec]
  have hstep' : stepFrame callFr = .needsCall cp rec.pending := by rw [hpend]; exact hstep
  -- the resume-frame pins, transported through the pending pins.
  have henv' : rec.pending.frame.exec.executionEnv = callFr.exec.executionEnv := by
    rw [hpend]; exact henv
  have hresaddr : (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.address
      = fr0.exec.executionEnv.address := by
    rw [resumeAfterCall_address, henv', hcalladdr]
  have hrescode : (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code
      = lower prog := by
    rw [resumeAfterCall_code, henv', hcallcode]
  have hrescanmod :
      (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.canModifyState = true := by
    rw [resumeAfterCall_canModifyState, henv', hcallmod]
  have hrespc : (Evm.resumeAfterCall rec.result rec.pending).exec.pc
      = callFr.exec.pc + 1 := by
    rw [resumeAfterCall_pc, hpend, hpcpin]
  have hresstack : (Evm.resumeAfterCall rec.result rec.pending).exec.stack
      = callSuccessFlag rec.result rec.pending :: [] := by
    rw [resumeAfterCall_stack, hpend, hstkpin]; rfl
  have hresmem : (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.memory
      = callFr.exec.toMachineState.memory := by
    rw [LirLean.MemAlgebra.resumeAfterCall_memory (by rw [hpend]; exact houtS), hpend, hmempin]
  have hresawEq :
      (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.activeWords
        = callFr.exec.toMachineState.activeWords := by
    rw [LirLean.MemAlgebra.resumeAfterCall_activeWords (by rw [hpend]; exact hinS)
      (by rw [hpend]; exact houtS), hpend, hawpin]
  have hresactive : callFr.exec.toMachineState.activeWords.toNat
      ≤ (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.activeWords.toNat := by
    rw [hresawEq]
  have hresvalid : (Evm.resumeAfterCall rec.result rec.pending).validJumps
      = validJumpDests (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code 0 := by
    rw [hrescode, resumeAfterCall_validJumps, hpend, hvj, hcallvj]
    exact hcorr.validJumps_lower
  -- the returning CALL, rec-spelled.
  have hcall' : CallReturns callFr (Evm.resumeAfterCall rec.result rec.pending) := by
    rw [hresult, hpend]; exact hcall
  -- clean-halt at the resume frame (forwarded across the arg run + the CALL node).
  have hchres : CleanHaltsNonException (Evm.resumeAfterCall rec.result rec.pending) :=
    cleanHaltsNonException_forward hch
      (hargs.trans (Runs.call hcall'
        (Runs.refl (Evm.resumeAfterCall rec.result rec.pending))))
  -- Piece B step 3: the Route-B tail.
  have htail := call_tail_of_cleanHalt
    (resumeFr := Evm.resumeAfterCall rec.result rec.pending)
    hcodeFits hb hcur hrescode
    (by rw [← hargsB, hrespc, hcallpc, hcorr.pc_eq,
          show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add', ofNat_add'])
    hchres hslotaddr
  -- the closed finish half.
  exact callRealises_of_recorded_finish hwl hb hcur haddr hcorr rfl hargs
    (by rw [hcallpc, hargsB]) hcallmem hcallact hcpcall hstep' hbegin hresaddr hrescode
    hrescanmod hrespc hresstack hresmem hresactive hresvalid htail hcorr

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

/-! ### R11-exact bricks — terminal suffix exhaustion (`lower_conforms_exact`, chunk 7)

At a HALTED terminal frame the restart equation has nothing left to record: `driveLog`
routes a `.halted` frame through its `.inr` arm, which at pending stack `[]` returns the
accumulators UNCHANGED — from the empty seed that is `.ok (endFrame fr h, [], [], [], [])`.
Restart determinism therefore forces EVERY coupling suffix to be nil, and pins the recorded
observable to this frame's halt. No `log.clean` is needed: the inversion is pure `driveLog`
computation at the halted frame, uniform in the halt signal.

These are the chunk-7 consumption bricks for the exact flagship `lower_conforms_exact`
(`RealisabilitySpec.lean`): the exact producer's halt case holds a `RunFromLeft` whose
leftover streams are the ALIGNED IMAGES of the terminal coupling suffixes (the
`StreamsAligned` components, taken below as three point-wise equations so this file stays
independent of the producer's vocabulary); the transport lemma collapses them to `[]` —
i.e. the `RunFromAll` leftover-`[]` shape. Stated over the COUPLING only, never over the
producer recursion. The exact flagship itself is NOT closed here. -/

/-- The shared terminal inversion: at a halted frame the restart replays to exactly
`(endFrame fr h, [], [], [], [])`, so all four suffixes are nil AND the recorded
observable is this frame's halt. -/
private theorem recorderCoupled_halted_inv {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .halted h) :
    gS = [] ∧ sS = [] ∧ cS = [] ∧ dS = [] ∧ log.observable = endFrame fr h := by
  obtain ⟨⟨f, hf⟩, _, _, _, _⟩ := hcp
  cases f with
  | zero => simp [driveLog] at hf
  | succ m =>
    unfold driveLog at hf
    simp only [hstep] at hf
    -- `hf : driveLog m [] (.inr (endFrame fr h)) [] [] [] [] = .ok (log.observable, …)`.
    cases m with
    | zero => simp [driveLog] at hf
    | succ k =>
      unfold driveLog at hf
      simp only [Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨hobs, hg, hs, hc, hd⟩ := hf
      exact ⟨hg.symm, hs.symm, hc.symm, hd.symm, hobs.symm⟩

/-- **Chunk-7 brick 1 — terminal suffix exhaustion.** At a halted terminal frame the
coupling's restart witness forces all four stream suffixes to be nil: nothing of the
recorded streams remains un-consumed. -/
theorem recorderCoupled_halted_suffixes_nil {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .halted h) :
    gS = [] ∧ sS = [] ∧ cS = [] ∧ dS = [] := by
  obtain ⟨hg, hs, hc, hd, _⟩ := recorderCoupled_halted_inv hcp hstep
  exact ⟨hg, hs, hc, hd⟩

/-- **Chunk-7 brick 2 — the terminal observable pin.** At a halted terminal frame the
recorded observable IS this frame's halt result (the coupling's restart witness replays
one halt step and stops). The exact producer's halt case uses it to identify the
`observe self (endFrame last haltSig)` conjuncts of `RunFromCoupled` with the log. -/
theorem recorderCoupled_halted_observable {log : RunLog} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .halted h) :
    log.observable = endFrame fr h :=
  (recorderCoupled_halted_inv hcp hstep).2.2.2.2

/-- **Chunk-7 brick 3 — leftover-nil transport.** If the exact walk's leftover streams are
the aligned images of the coupling suffixes (the `StreamsAligned` components, as three
point-wise equations) at a halted terminal frame, all three leftovers are nil. Stated over
the coupling, not the producer recursion. -/
theorem recorderCoupled_halted_leftovers_nil {log : RunLog} {self : AccountAddress}
    {fr : Frame} {h : FrameHalt}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    {Tleft : GasOracle} {Cleft : CallStream} {Dleft : CreateStream}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .halted h)
    (hT : Tleft = gS) (hC : Cleft = callStreamOf cS self)
    (hD : Dleft = createStreamOf dS self) :
    Tleft = [] ∧ Cleft = [] ∧ Dleft = [] := by
  obtain ⟨hg, _, hc, hd⟩ := recorderCoupled_halted_suffixes_nil hcp hstep
  subst hg; subst hc; subst hd
  exact ⟨hT, by simp [hC, callStreamOf], by simp [hD, createStreamOf]⟩

/-- **Chunk-7 brick 4 — the `RunFromAll` corollary** the exact producer consumes verbatim:
a `RunFromLeft` whose leftovers are the aligned images of the coupling suffixes at a
halted terminal frame IS a `RunFromAll` (leftover `[]` on all three streams). -/
theorem runFromAll_of_runFromLeft_coupled_halt {prog : Program} {log : RunLog}
    {self : AccountAddress} {st : IRState} {T Tleft : GasOracle} {C Cleft : CallStream}
    {D Dleft : CreateStream} {L : Label} {O : Observable} {fr : Frame} {h : FrameHalt}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    (hcp : RecorderCoupled log fr gS sS cS dS)
    (hstep : stepFrame fr = .halted h)
    (hT : Tleft = gS) (hC : Cleft = callStreamOf cS self)
    (hD : Dleft = createStreamOf dS self)
    (hleft : RunFromLeft prog st T C D L O Tleft Cleft Dleft) :
    RunFromAll prog st T C D L O := by
  obtain ⟨hTn, hCn, hDn⟩ :=
    recorderCoupled_halted_leftovers_nil hcp hstep hT hC hD
  rw [hTn, hCn, hDn] at hleft
  exact hleft

/-! ### The COUPLED CALL-head bundle (the producer arm's consumption shape)

`callRealises_of_recorded` (above) discharges `CallRealisesS`, but its statement FORGETS the
recorder coupling: the arg-push run and the returning-CALL resume are packaged as bare `Runs`/
`CallReturns` facts, so a consumer that must RE-ESTABLISH `RecorderCoupled` at the post-call
frame (the coupled producer walk, `Producer.lean`'s `simStmt_coupled_call`) cannot transport the
coupling across those opaque runs. `call_head_realises_coupled` is the SAME Piece-A/B assembly
(`call_args_run_of_coupled` → `call_dispatch_of_coupled` → the CallsCode seam →
`recorderCoupled_call_extract`), stopping BEFORE the tail and keeping the coupling alive: it
returns the CALL-site frame with its pins, the rec-spelled returning CALL, the advanced coupling
at the resume frame (tail suffix `cS'` — exactly one record consumed), and the resume-frame pins
the `Corr` re-establishment consumes. Same hypothesis ledger as `callRealises_of_recorded`
(no `hslotaddr`: the tail is not built here). -/
theorem call_head_realises_coupled {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 : IRState} {fr0 : Frame} {cw gw : Word}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS' : List CallRecord}
    {dS : List CreateRecord} {I : Tmp → Prop}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcorr : Corr prog sloadChg 0 I st0 fr0 L pc)
    (hcp : RecorderCoupled log fr0 gS sS (rec :: cS') dS)
    (hch : CleanHaltsNonException fr0)
    (hcc : ∀ fr', Runs fr0 fr' → CallsCode fr')
    (hcallee : st0.locals cs.callee = some cw)
    (hgasfwd : st0.locals cs.gasFwd = some gw)
    (hfreeCallee : RematClosureFree prog I (.tmp cs.callee))
    (hfreeGasFwd : RematClosureFree prog I (.tmp cs.gasFwd))
    (hstkCallee : 5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024)
    (hstkGasFwd : 6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024) :
    ∃ callFr : Frame,
      Runs fr0 callFr
      ∧ callFr.exec.pc = fr0.exec.pc + UInt32.ofNat
          ((emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
            ++ matCache prog cs.callee ++ matCache prog cs.gasFwd).length)
      ∧ callFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory
      ∧ fr0.exec.toMachineState.activeWords.toNat
          ≤ callFr.exec.toMachineState.activeWords.toNat
      ∧ CallReturns callFr (Evm.resumeAfterCall rec.result rec.pending)
      ∧ RecorderCoupled log (Evm.resumeAfterCall rec.result rec.pending) gS sS cS' dS
      ∧ (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.address
          = fr0.exec.executionEnv.address
      ∧ (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code = lower prog
      ∧ (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.canModifyState = true
      ∧ (Evm.resumeAfterCall rec.result rec.pending).exec.pc = callFr.exec.pc + 1
      ∧ (Evm.resumeAfterCall rec.result rec.pending).exec.stack
          = callSuccessFlag rec.result rec.pending :: []
      ∧ (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.memory
          = callFr.exec.toMachineState.memory
      ∧ callFr.exec.toMachineState.activeWords.toNat
          ≤ (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.activeWords.toNat
      ∧ (Evm.resumeAfterCall rec.result rec.pending).validJumps
          = validJumpDests (Evm.resumeAfterCall rec.result rec.pending).exec.executionEnv.code 0 := by
  classical
  -- Piece B step 1: the argument-push run (coupling + clean-halt carried to the CALL site).
  obtain ⟨callFr, hargs, hcallpc, hcallstk, hcallcode, hcallvj, hcalladdr, hcallmod,
      hcallmem, hcallact, _hcallsto, hcpcall, hchcall⟩ :=
    call_args_run_of_coupled hwl hcodeFits hb hcur hcorr hcp hch hcallee hgasfwd
      hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set argsB := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
      ++ matCache prog cs.callee ++ matCache prog cs.gasFwd with hargsB
  -- the CALL byte decode at `callFr` (byte layout + `codeFits`).
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.call cs)
      = argsB ++ [Byte.call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none => [Byte.pop]) := rfl
  have hcallbyte : (emitStmt (matCache prog) (defsOf prog) (.call cs))[argsB.length]?
      = some Byte.call := by
    rw [hemit0, List.getElem?_append_left (by
          simp only [List.length_append, List.length_singleton]; omega),
        List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length →
      (flatBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.call cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.call cs) j hbt hcur hj
  have hargslt : argsB.length
      < (emitStmt (matCache prog) (defsOf prog) (.call cs)).length := by
    rw [hemit0]
    simp only [List.length_append, List.length_singleton]
    omega
  have hdecCall : decode callFr.exec.executionEnv.code callFr.exec.pc
      = some (.System .CALL, .none) := by
    rw [hcallcode, hcallpc, hcorr.pc_eq, ofNat_add']
    have h := nonpush_leaf_decodeF prog (pcOf prog L pc) argsB.length Byte.call
      (emitStmt (matCache prog) (defsOf prog) (.call cs))
      (call_stmt_offset_bound_of_codeFits hcodeFits hb hcur hargslt)
      hcallbyte (by decide) hseg
    simpa using h
  -- Piece B step 2: the dispatch bundle.
  obtain ⟨cp, pending, hstep, henv, hvj, hpcpin, hmempin, hawpin, hstkpin, hinS, houtS⟩ :=
    call_dispatch_of_coupled hcpcall hchcall hdecCall hcallstk hcallmod
  -- the CallsCode seam rules out the precompile/immediate arm.
  have hccF : CallsCode callFr := hcc callFr hargs
  obtain ⟨child, hbegin⟩ : ∃ child, beginCall cp = .inl child := by
    cases hbc : beginCall cp with
    | inl c => exact ⟨c, rfl⟩
    | inr r =>
        exact absurd hbc (beginCall_isCode_of_codeSource_ne_precompiled
          (hccF cp pending hstep) r)
  -- Piece A: identify the coupled head record with this CALL, KEEPING the advanced coupling.
  obtain ⟨childRes, hcall, hrec, hcpres⟩ := recorderCoupled_call_extract hcpcall hstep hbegin
  have hpend : rec.pending = pending := by rw [hrec]
  have hresult : rec.result = childRes.toCallResult := by rw [hrec]
  -- the returning CALL + the advanced coupling, rec-spelled.
  have hcall' : CallReturns callFr (Evm.resumeAfterCall rec.result rec.pending) := by
    rw [hresult, hpend]; exact hcall
  have hcpres' : RecorderCoupled log (Evm.resumeAfterCall rec.result rec.pending) gS sS cS' dS := by
    rw [hresult, hpend]; exact hcpres
  -- the resume-frame pins, transported through the pending pins.
  have henv' : rec.pending.frame.exec.executionEnv = callFr.exec.executionEnv := by
    rw [hpend]; exact henv
  refine ⟨callFr, hargs, by rw [hcallpc, hargsB], hcallmem, hcallact, hcall', hcpres',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [resumeAfterCall_address, henv', hcalladdr]
  · rw [resumeAfterCall_code, henv', hcallcode]
  · rw [resumeAfterCall_canModifyState, henv', hcallmod]
  · rw [resumeAfterCall_pc, hpend, hpcpin]
  · rw [resumeAfterCall_stack, hpend, hstkpin]; rfl
  · rw [LirLean.MemAlgebra.resumeAfterCall_memory (by rw [hpend]; exact houtS), hpend, hmempin]
  · have hawEq : (Evm.resumeAfterCall rec.result rec.pending).exec.toMachineState.activeWords
        = callFr.exec.toMachineState.activeWords := by
      rw [LirLean.MemAlgebra.resumeAfterCall_activeWords (by rw [hpend]; exact hinS)
        (by rw [hpend]; exact houtS), hpend, hawpin]
    rw [hawEq]
  · rw [resumeAfterCall_code, henv', hcallcode, resumeAfterCall_validJumps, hpend, hvj, hcallvj]
    exact hcorr.validJumps_lower

/-! ### R3-CREATE — the CREATE run producer (mirror of the CALL bricks above)

The CREATE analogues of R3's Piece B. Piece A (`recorderCoupled_create_extract` /
`recorderCoupled_create`) is already closed above. The structure mirrors CALL exactly, with the
CREATE specifics:

* the argument layout is `matCache salt ++ matCache initSize ++ matCache initOffset ++ matCache
  value ++ [CREATE2]` (four materialise runs, NO zero-window pushes — CREATE2 pops
  value/off/size/salt directly), so `create_args_run_of_coupled` is FOUR `recorderCoupled_matRunsC`
  folds threaded through the clean-halt gas chain (no `coupled_push_step`);
* the tail (`PUSH32 slot; MSTORE` or `POP`) is byte-identical to CALL's — `create_tail_of_cleanHalt`
  reuses the SAME generic clean-halt tail bricks, only the byte offsets differ;
* dispatch is `.needsCreate` (via `beginCreate`, TOTAL — no precompile split) with the create resume
  reading `resumeAfterCreate` (`Except`-typed, faults on the 63/64 retention guard — the
  `CreateResolves` seam rules that out);
* the head record is a `CreateRecord` on the `dS` suffix (vs `CallRecord`/`cS`), and the resume word
  is `createAddrOrZero` (vs `callSuccessFlag`).

STATUS (after this producer round): `create_stmt_offset_bound_of_codeFits`,
`create_args_run_of_coupled`, `create_tail_of_cleanHalt` are CLOSED (direct transfers). The
`resumeAfterCreate` stack/memory/activeWords resume pins are NOW LANDED (default cone, axiom-clean:
`Lir.V2.resumeAfterCreate_stack`/`_memory`/`_activeWords_ge` in `Engine/Descent.lean`).

`create_dispatch_of_coupled`, `createRealises_of_recorded`, `create_head_realises_coupled` remain
STUBBED with tracked `sorry`s. UPDATE (CREATE2 soft-fail recorder alignment, 2026-07-11): the
recorder now logs EVERY top-level CREATE2 outcome — a descend records the child result, a SOFT-FAIL
records a `softFailCreateRecord` (world-unchanged, addr 0) — so `log.creates` aligns 1:1 with CREATE2
cursors. Consequently the create-channel depth-guard mirror `driveLog_creates_const_of_depth` is
RETIRED (a nonempty create suffix no longer forces `depth < 1024`, since a soft-fail at
`depth ≥ 1024` records). `create_dispatch_of_coupled` is to be RESHAPED to a two-arm disjunction
(descend arm ⇔ `rec.result.success`; soft-fail arm ⇔ `stepFrame = .next`), both stepFrames DERIVED
from the recorded head via the coupling — no `CreateResolves`/`CreateDescends` premise, no domain
restriction (design spec §4). -/

/-- A byte inside the lowered CREATE statement sits below the global `codeFits` budget.
(The CALL twin `call_stmt_offset_bound_of_codeFits`, specialised to `.create cs`.) -/
private theorem create_stmt_offset_bound_of_codeFits {prog : Program} {L : Label} {b : Block}
    {pc : Nat} {cs : CreateSpec}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    {k : Nat}
    (hk : k < (emitStmt (matCache prog) (defsOf prog) (.create cs)).length) :
    pcOf prog L pc + k < 2 ^ 32 := by
  have hbyte0 :
      (emitStmt (matCache prog) (defsOf prog) (.create cs))[k]?
        = some ((emitStmt (matCache prog) (defsOf prog) (.create cs))[k]) :=
    List.getElem?_eq_getElem hk
  have hflat :
      (flatBytes prog)[pcOf prog L pc + k]?
        = some ((emitStmt (matCache prog) (defsOf prog) (.create cs))[k]) := by
    rw [flatBytes_at_pcOf_offset prog L b pc (.create cs) k (Lir.toList_of_blockAt hb) hcur hk]
    exact hbyte0
  rw [List.getElem?_eq_some_iff] at hflat
  exact lt_of_lt_of_le hflat.1 (Nat.le_of_lt hcodeFits)

/-- A real create cursor statically scopes: `StepScopedS prog (.create cs)` is `True`. -/
private theorem stepScopedS_create_of_cursor {prog : Program} {cs : CreateSpec} :
    StepScopedS prog (.create cs) := trivial

/-- World replacement preserves the create arm's static well-scoping; if a result tmp is bound, its
slot registration comes from `DefsConsistent`'s create clause. (The CALL twin
`call_post_wellScoped`, for `.create`.) -/
private theorem create_post_wellScoped {prog : Program} {L : Label} {b : Block} {pc : Nat}
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

/-- **R3-CREATE, step 1 — the CREATE argument-push run producer** (CLOSED). The CREATE twin of
`call_args_run_of_coupled`. From `Corr` at the CREATE cursor, the coupling, and the clean-halt
scope, BUILD the run to the `CREATE2`-site frame: the four operand materialise runs
`matCache salt`, `matCache initSize`, `matCache initOffset`, `matCache value`
(`recorderCoupled_matRunsC`, gas via `materialise_chargeC_le_of_cleanHalt`). Unlike CALL there is
NO zero-window `PUSH32 0` prefix (`CREATE2` pops value/off/size/salt directly). The endpoint carries
the operand stack `valueW :: initOffW :: initSizeW :: saltW :: []`, the coupling, and the forwarded
clean-halt. HONEST HYPOTHESES (the CALL-arm principle, header lesson 5): the four operand bindings
(the value channel needs values), their closure-freeness at the ambient set `I` (`ScopedUses`
supplies them at the walk's fold set), the four static stack-room folds (a static-fold gap, as in
CALL), and the flagship scalar `codeFits` (the decode bounds need it). -/
private theorem create_args_run_of_coupled {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {L : Label} {b : Block} {pc : Nat} {cs : CreateSpec}
    {st0 : IRState} {fr0 : Frame} {valueW initOffW initSizeW saltW : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord} {dS : List CreateRecord}
    {I : Tmp → Prop}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hcorr : Corr prog sloadChg 0 I st0 fr0 L pc)
    (hcp : RecorderCoupled log fr0 gS sS cS dS)
    (hch : CleanHaltsNonException fr0)
    (hvalue : st0.locals cs.value = some valueW)
    (hoff : st0.locals cs.initOffset = some initOffW)
    (hsize : st0.locals cs.initSize = some initSizeW)
    (hsalt : st0.locals cs.salt = some saltW)
    (hfreeValue : RematClosureFree prog I (.tmp cs.value))
    (hfreeOff : RematClosureFree prog I (.tmp cs.initOffset))
    (hfreeSize : RematClosureFree prog I (.tmp cs.initSize))
    (hfreeSalt : RematClosureFree prog I (.tmp cs.salt))
    (hstkSalt : 0 + (chargeCache prog sloadChg cs.salt).length ≤ 1024)
    (hstkSize : 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024)
    (hstkOff : 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024)
    (hstkValue : 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024) :
    ∃ createFr : Frame,
      Runs fr0 createFr
      ∧ createFr.exec.pc = fr0.exec.pc + UInt32.ofNat
          ((matCache prog cs.salt ++ matCache prog cs.initSize
            ++ matCache prog cs.initOffset ++ matCache prog cs.value).length)
      ∧ createFr.exec.stack = valueW :: initOffW :: initSizeW :: saltW :: []
      ∧ createFr.exec.executionEnv.code = lower prog
      ∧ createFr.validJumps = fr0.validJumps
      ∧ createFr.exec.executionEnv.address = fr0.exec.executionEnv.address
      ∧ createFr.exec.executionEnv.canModifyState = true
      ∧ createFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory
      ∧ fr0.exec.toMachineState.activeWords.toNat
          ≤ createFr.exec.toMachineState.activeWords.toNat
      ∧ (∀ k, selfStorage createFr k = selfStorage fr0 k)
      ∧ RecorderCoupled log createFr gS sS cS dS
      ∧ CleanHaltsNonException createFr := by
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set base := pcOf prog L pc with hbase
  set sB := matCache prog cs.salt with hsB
  set zB := matCache prog cs.initSize with hzB
  set oB := matCache prog cs.initOffset with hoB
  set vB := matCache prog cs.value with hvB
  set tailB : List UInt8 := (match cs.resultTmp with
      | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
      | none => [Byte.pop]) with htailB
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.create cs)
      = sB ++ zB ++ oB ++ vB ++ [Byte.create2] ++ tailB := rfl
  -- the master 32-bit bound on any byte offset within the operand block + CREATE2 byte.
  have hbnd : ∀ k, k < sB.length + zB.length + oB.length + vB.length + 1 → base + k < 2 ^ 32 := by
    intro k hk
    apply create_stmt_offset_bound_of_codeFits hcodeFits hb hcur
    rw [hemit0]
    simp only [List.length_append, List.length_singleton]
    omega
  -- the emit byte segment at the cursor.
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.create cs)).length →
      (flatBytes prog)[base + j]? = (emitStmt (matCache prog) (defsOf prog) (.create cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.create cs) j hbt hcur hj
  -- right-associate the emit to peel the four operand segments.
  set rest : List UInt8 := zB ++ (oB ++ (vB ++ ([Byte.create2] ++ tailB))) with hrest
  have hassoc : emitStmt (matCache prog) (defsOf prog) (.create cs)
      = sB ++ (zB ++ (oB ++ (vB ++ ([Byte.create2] ++ tailB)))) := by
    rw [hemit0]; simp only [List.append_assoc]
  rw [hassoc] at hseg
  have hsegSB := segF_prefix (flatBytes prog) base sB rest hseg
  have hsegAfterSB := segF_suffix (flatBytes prog) base sB rest hseg
  rw [hrest] at hsegAfterSB
  have hsegZB := segF_prefix (flatBytes prog) (base + sB.length) zB
      (oB ++ (vB ++ ([Byte.create2] ++ tailB))) hsegAfterSB
  have hsegAfterZB := segF_suffix (flatBytes prog) (base + sB.length) zB
      (oB ++ (vB ++ ([Byte.create2] ++ tailB))) hsegAfterSB
  have hsegOB := segF_prefix (flatBytes prog) (base + sB.length + zB.length) oB
      (vB ++ ([Byte.create2] ++ tailB)) hsegAfterZB
  have hsegAfterOB := segF_suffix (flatBytes prog) (base + sB.length + zB.length) oB
      (vB ++ ([Byte.create2] ++ tailB)) hsegAfterZB
  have hsegVB := segF_prefix (flatBytes prog) (base + sB.length + zB.length + oB.length) vB
      ([Byte.create2] ++ tailB) hsegAfterOB
  -- == the four coupled materialise runs ==
  have hcode0 : fr0.exec.executionEnv.code = lower prog := hcorr.code_eq
  have hpc0 : fr0.exec.pc = UInt32.ofNat base := hcorr.pc_eq
  have hstk0 : fr0.exec.stack = [] := hcorr.stack_nil
  -- run 1: `salt` from `fr0`.
  have hdcS : MatDecC prog hwl.defsCons hwl.defEnvOrdered fr0.exec.executionEnv.code
      fr0.exec.pc (.tmp cs.salt) := by
    rw [hcode0, hpc0]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp cs.salt) base
      (by simp only [matExpr_tmp, ← hsB]
          have := hbnd sB.length (by omega); omega)
      (by simp only [matExpr_tmp, ← hsB]; exact hsegSB)
  have hstk0C : fr0.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cs.salt)).length ≤ 1024 := by
    rw [hstk0]; simp only [chargeExpr_tmp, Stack.size, List.length_nil]
    exact hstkSalt
  have hgasS := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 I (.tmp cs.salt) saltW fr0 hdcS hcorr.defsSound hfreeSalt
    hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree hsalt hch hstk0C
  obtain ⟨frS, hmrS, hcpS⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 log gS sS cS dS I (.tmp cs.salt) saltW fr0 hdcS hcorr.defsSound
    hfreeSalt hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree hsalt
    hgasS hstk0C hcp
  have hchS : CleanHaltsNonException frS := cleanHaltsNonException_forward hch hmrS.runs
  have hfrScode : frS.exec.executionEnv.code = lower prog := by rw [hmrS.code, hcode0]
  have hfrSpc : frS.exec.pc = UInt32.ofNat (base + sB.length) := by
    have h := hmrS.pc; simp only [matExpr_tmp, ← hsB] at h; rw [h, hpc0, ofNat_add']
  have hfrSstk : frS.exec.stack = saltW :: [] := by rw [hmrS.stack, hstk0]; rfl
  have hstoreS : StorageAgree st0 frS := hcorr.storage.transport hmrS.storage
  have hmemS : MemRealises prog st0 frS := hcorr.memAgree.transport hmrS.memBytes hmrS.memActive
  -- run 2: `initSize` from `frS`.
  have hdcZ : MatDecC prog hwl.defsCons hwl.defEnvOrdered frS.exec.executionEnv.code
      frS.exec.pc (.tmp cs.initSize) := by
    rw [hfrScode, hfrSpc]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp cs.initSize) (base + sB.length)
      (by simp only [matExpr_tmp, ← hzB]
          have := hbnd (sB.length + zB.length) (by omega); omega)
      (by simp only [matExpr_tmp, ← hzB]; exact hsegZB)
  have hstkZC : frS.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cs.initSize)).length ≤ 1024 := by
    rw [hfrSstk]; simp only [chargeExpr_tmp]
    show 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024; exact hstkSize
  have hgasZ := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 I (.tmp cs.initSize) initSizeW frS hdcZ hcorr.defsSound hfreeSize
    hcorr.wellScoped hstoreS (by nofun) (by nofun) hmemS hsize hchS hstkZC
  obtain ⟨frZ, hmrZ, hcpZ⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 log gS sS cS dS I (.tmp cs.initSize) initSizeW frS hdcZ hcorr.defsSound
    hfreeSize hcorr.wellScoped hstoreS (by nofun) (by nofun) hmemS hsize hgasZ hstkZC hcpS
  have hchZ : CleanHaltsNonException frZ := cleanHaltsNonException_forward hchS hmrZ.runs
  have hfrZcode : frZ.exec.executionEnv.code = lower prog := by rw [hmrZ.code, hfrScode]
  have hfrZpc : frZ.exec.pc = UInt32.ofNat (base + sB.length + zB.length) := by
    have h := hmrZ.pc; simp only [matExpr_tmp, ← hzB] at h; rw [h, hfrSpc, ofNat_add']
  have hfrZstk : frZ.exec.stack = initSizeW :: saltW :: [] := by rw [hmrZ.stack, hfrSstk]; rfl
  have hstoreZ : StorageAgree st0 frZ := hstoreS.transport hmrZ.storage
  have hmemZ : MemRealises prog st0 frZ := hmemS.transport hmrZ.memBytes hmrZ.memActive
  -- run 3: `initOffset` from `frZ`.
  have hdcO : MatDecC prog hwl.defsCons hwl.defEnvOrdered frZ.exec.executionEnv.code
      frZ.exec.pc (.tmp cs.initOffset) := by
    rw [hfrZcode, hfrZpc]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp cs.initOffset)
      (base + sB.length + zB.length)
      (by simp only [matExpr_tmp, ← hoB]
          have := hbnd (sB.length + zB.length + oB.length) (by omega); omega)
      (by simp only [matExpr_tmp, ← hoB]; exact hsegOB)
  have hstkOC : frZ.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cs.initOffset)).length ≤ 1024 := by
    rw [hfrZstk]; simp only [chargeExpr_tmp]
    show 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024; exact hstkOff
  have hgasO := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 I (.tmp cs.initOffset) initOffW frZ hdcO hcorr.defsSound hfreeOff
    hcorr.wellScoped hstoreZ (by nofun) (by nofun) hmemZ hoff hchZ hstkOC
  obtain ⟨frO, hmrO, hcpO⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 log gS sS cS dS I (.tmp cs.initOffset) initOffW frZ hdcO hcorr.defsSound
    hfreeOff hcorr.wellScoped hstoreZ (by nofun) (by nofun) hmemZ hoff hgasO hstkOC hcpZ
  have hchO : CleanHaltsNonException frO := cleanHaltsNonException_forward hchZ hmrO.runs
  have hfrOcode : frO.exec.executionEnv.code = lower prog := by rw [hmrO.code, hfrZcode]
  have hfrOpc : frO.exec.pc = UInt32.ofNat (base + sB.length + zB.length + oB.length) := by
    have h := hmrO.pc; simp only [matExpr_tmp, ← hoB] at h; rw [h, hfrZpc, ofNat_add']
  have hfrOstk : frO.exec.stack = initOffW :: initSizeW :: saltW :: [] := by
    rw [hmrO.stack, hfrZstk]; rfl
  have hstoreO : StorageAgree st0 frO := hstoreZ.transport hmrO.storage
  have hmemO : MemRealises prog st0 frO := hmemZ.transport hmrO.memBytes hmrO.memActive
  -- run 4: `value` from `frO`.
  have hdcV : MatDecC prog hwl.defsCons hwl.defEnvOrdered frO.exec.executionEnv.code
      frO.exec.pc (.tmp cs.value) := by
    rw [hfrOcode, hfrOpc]
    exact matDecC_of_seg prog hwl.defsCons hwl.defEnvOrdered (.tmp cs.value)
      (base + sB.length + zB.length + oB.length)
      (by simp only [matExpr_tmp, ← hvB]
          have := hbnd (sB.length + zB.length + oB.length + vB.length) (by omega); omega)
      (by simp only [matExpr_tmp, ← hvB]; exact hsegVB)
  have hstkVC : frO.exec.stack.size
      + (chargeExpr sloadChg (chargeCache prog sloadChg) (.tmp cs.value)).length ≤ 1024 := by
    rw [hfrOstk]; simp only [chargeExpr_tmp]
    show 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024; exact hstkValue
  have hgasV := materialise_chargeC_le_of_cleanHalt hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 I (.tmp cs.value) valueW frO hdcV hcorr.defsSound hfreeValue
    hcorr.wellScoped hstoreO (by nofun) (by nofun) hmemO hvalue hchO hstkVC
  obtain ⟨frV, hmrV, hcpV⟩ := recorderCoupled_matRunsC hwl.defsCons hwl.defEnvOrdered
    sloadChg st0 0 log gS sS cS dS I (.tmp cs.value) valueW frO hdcV hcorr.defsSound
    hfreeValue hcorr.wellScoped hstoreO (by nofun) (by nofun) hmemO hvalue hgasV hstkVC hcpO
  -- == assemble the endpoint bundle ==
  have hruns : Runs fr0 frV :=
    hmrS.runs.trans (hmrZ.runs.trans (hmrO.runs.trans hmrV.runs))
  refine ⟨frV, hruns, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcpV,
    cleanHaltsNonException_forward hchO hmrV.runs⟩
  · -- pc: fr0.pc + (|sB| + |zB| + |oB| + |vB|).
    have hlen : (matCache prog cs.salt ++ matCache prog cs.initSize
        ++ matCache prog cs.initOffset ++ matCache prog cs.value).length
        = sB.length + zB.length + oB.length + vB.length := by
      simp only [List.length_append, ← hsB, ← hzB, ← hoB, ← hvB]
    have h := hmrV.pc; simp only [matExpr_tmp, ← hvB] at h
    rw [h, hfrOpc, hlen, hpc0, ofNat_add', ofNat_add']
    congr 1; omega
  · rw [hmrV.stack, hfrOstk]; rfl
  · rw [hmrV.code, hfrOcode]
  · rw [hmrV.validJumps, hmrO.validJumps, hmrZ.validJumps, hmrS.validJumps]
  · rw [hmrV.addr, hmrO.addr, hmrZ.addr, hmrS.addr]
  · rw [hmrV.canMod, hmrO.canMod, hmrZ.canMod, hmrS.canMod]
    show fr0.exec.executionEnv.canModifyState = true
    exact hcorr.can_modify
  · rw [hmrV.memBytes, hmrO.memBytes, hmrZ.memBytes, hmrS.memBytes]
  · calc fr0.exec.toMachineState.activeWords.toNat
        ≤ frS.exec.toMachineState.activeWords.toNat := hmrS.memActive
      _ ≤ frZ.exec.toMachineState.activeWords.toNat := hmrZ.memActive
      _ ≤ frO.exec.toMachineState.activeWords.toNat := hmrO.memActive
      _ ≤ frV.exec.toMachineState.activeWords.toNat := hmrV.memActive
  · intro k
    rw [hmrV.storage k, hmrO.storage k, hmrZ.storage k, hmrS.storage k]

/-- **R3-CREATE, step 3 — the Route-B tail at the pinned resume frame** (CLOSED). The CREATE twin
of `call_tail_of_cleanHalt`. At a frame running `lower prog` one byte past this cursor's `CREATE2`
byte with the address word alone on the stack, the tail realises: `resultTmp = some t` runs
`PUSH32 (slotOf t); MSTORE` (`stash_tail_runs`, fed the byte-layout decode anchors peeled off the
`emitStmt` create layout and the clean-halt gas/expansion witnesses); `resultTmp = none` runs `POP`
(`runs_pop`, fed by `next_pop_of_cleanHalt`). Byte-identical machinery to the CALL tail — only the
operand-block layout (`matCache salt ++ matCache initSize ++ matCache initOffset ++ matCache value`)
and the `CREATE2` byte differ. -/
theorem create_tail_of_cleanHalt {prog : Program} {L : Label} {b : Block} {pc : Nat}
    {cs : CreateSpec} {resumeFr : Frame}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hcode : resumeFr.exec.executionEnv.code = lower prog)
    (hpc : resumeFr.exec.pc = UInt32.ofNat (pcOf prog L pc
      + (matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value).length + 1))
    (hch : CleanHaltsNonException resumeFr)
    (hslotaddr : ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits) :
    ∀ addrW : Word, resumeFr.exec.stack = addrW :: [] →
      (∀ (t : Tmp), cs.resultTmp = some t →
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr,
            Runs resumeFr endFr
          ∧ endFr.exec.toMachineState.memory
              = ((resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) addrW)).memory
          ∧ endFr.exec.toMachineState.activeWords
              = ((resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) addrW)).activeWords
          ∧ endFr.exec.pc = resumeFr.exec.pc + UInt32.ofNat 34
          ∧ endFr.exec.executionEnv.code = resumeFr.exec.executionEnv.code
          ∧ endFr.validJumps = resumeFr.validJumps
          ∧ endFr.exec.executionEnv.address = resumeFr.exec.executionEnv.address
          ∧ endFr.exec.executionEnv.canModifyState
              = resumeFr.exec.executionEnv.canModifyState
          ∧ (∀ k, selfStorage endFr k = selfStorage resumeFr k)
          ∧ endFr.exec.stack = [])
      ∧ (cs.resultTmp = none → Runs resumeFr (popFrame resumeFr [])) := by
  intro addrW hstkflag
  classical
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set base := pcOf prog L pc with hbase
  set argsB : List UInt8 := matCache prog cs.salt ++ matCache prog cs.initSize
      ++ matCache prog cs.initOffset ++ matCache prog cs.value with hargsB
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.create cs)).length →
      (flatBytes prog)[base + j]? = (emitStmt (matCache prog) (defsOf prog) (.create cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.create cs) j hbt hcur hj
  have hpc' : resumeFr.exec.pc = UInt32.ofNat (base + (argsB.length + 1)) := by
    rw [hpc]; congr 1
  have hsz1 : resumeFr.exec.stack.size + 1 ≤ 1024 := by
    rw [hstkflag]; show (1 : ℕ) + 1 ≤ 1024; omega
  constructor
  · -- == `resultTmp = some t`: the `PUSH32 (slotOf t); MSTORE` stash tail ==
    intro t ht
    obtain ⟨hslot64, hslotplat⟩ := hslotaddr t ht
    refine ⟨hslot64, hslotplat, ?_⟩
    -- byte layout: `emitStmt = (argsB ++ [CREATE2]) ++ (emitImm (slotOf t) ++ [MSTORE])`.
    have hemit : emitStmt (matCache prog) (defsOf prog) (.create cs)
        = (argsB ++ [Byte.create2]) ++ (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) := by
      have h0 : emitStmt (matCache prog) (defsOf prog) (.create cs)
          = argsB ++ [Byte.create2]
            ++ (match cs.resultTmp with
                | some t' => emitImm (UInt256.ofNat (slotOf t')) ++ [Byte.mstore]
                | none => [Byte.pop]) := rfl
      rw [h0, ht]
    have hlen : (emitStmt (matCache prog) (defsOf prog) (.create cs)).length
        = argsB.length + 35 := by
      rw [hemit]
      simp only [List.length_append, List.length_singleton, emitImm_length]
    have hbnd : base + (argsB.length + 34) < 2 ^ 32 :=
      create_stmt_offset_bound_of_codeFits hcodeFits hb hcur (by omega)
    have hsegTail := segF_suffix (flatBytes prog) base (argsB ++ [Byte.create2])
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]) (by rw [← hemit]; exact hseg)
    have hsegTail' : ∀ j, j < (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]).length →
        (flatBytes prog)[base + (argsB.length + 1) + j]?
          = (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])[j]? := by
      intro j hj
      have h := hsegTail j hj
      rwa [show base + (argsB ++ [Byte.create2]).length + j = base + (argsB.length + 1) + j from by
            simp only [List.length_append, List.length_singleton]] at h
    have hdpushT : decode (lower prog) (UInt32.ofNat (base + (argsB.length + 1)))
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) :=
      imm_leaf_decodeF prog (base + (argsB.length + 1)) (UInt256.ofNat (slotOf t))
        (by omega)
        (segF_prefix (flatBytes prog) (base + (argsB.length + 1))
          (emitImm (UInt256.ofNat (slotOf t))) [Byte.mstore] hsegTail')
    have hdmstoreT : decode (lower prog) (UInt32.ofNat (base + (argsB.length + 1) + 33))
        = some (.Smsf .MSTORE, .none) := by
      have hpi : Evm.parseInstr Byte.mstore = .Smsf .MSTORE := by decide
      rw [← hpi]
      exact nonpush_leaf_decodeF prog (base + (argsB.length + 1)) 33 Byte.mstore
        (emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore])
        (by omega)
        (by rw [List.getElem?_append_right (by rw [emitImm_length])]
            simp [emitImm_length])
        (by decide) hsegTail'
    have hdpush : decode resumeFr.exec.executionEnv.code resumeFr.exec.pc
        = some (.Push .PUSH32, some (UInt256.ofNat (slotOf t), 32)) := by
      rw [hcode, hpc']; exact hdpushT
    have hdmstore : decode resumeFr.exec.executionEnv.code (resumeFr.exec.pc + UInt32.ofNat 33)
        = some (.Smsf .MSTORE, .none) := by
      rw [hcode, hpc', ofNat_add']; exact hdmstoreT
    have hgasPush : 3 ≤ resumeFr.exec.gasAvailable.toNat := by
      have := (CleanHaltExtract.next_push_of_cleanHalt resumeFr .PUSH32
        (UInt256.ofNat (slotOf t)) 32 hch (by decide) hdpush (by decide) (by decide) hsz1).1
      have hvl : (GasConstants.Gverylow : ℕ) = 3 := rfl
      omega
    have hrunPush : Runs resumeFr (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32) :=
      runs_push resumeFr .PUSH32 (UInt256.ofNat (slotOf t)) 32 (by nofun) hdpush rfl rfl
        hgasPush hsz1
    have hchP : CleanHaltsNonException (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32) :=
      cleanHaltsNonException_forward hch hrunPush
    have hfrpstk : (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32).exec.stack
        = UInt256.ofNat (slotOf t) :: addrW :: [] := by
      rw [pushFrameW_stack', hstkflag]; rfl
    have hfrpdec : decode
        (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32).exec.executionEnv.code
        (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32).exec.pc
          = some (.Smsf .MSTORE, .none) := by
      rw [pushFrameW_code, pushFrameW_pc, push32_pcΔ]
      exact hdmstore
    obtain ⟨words', hmem, hgasMem, hgasVL, _⟩ :=
      CleanHaltExtract.next_mstore_of_cleanHalt
        (pushFrameW resumeFr (UInt256.ofNat (slotOf t)) 32) (UInt256.ofNat (slotOf t)) addrW []
        hchP hfrpdec hfrpstk (by rw [hfrpstk]; show (2 : ℕ) ≤ 1024; omega)
    have hstash := stash_tail_runs resumeFr (slotOf t) addrW [] words' hstkflag hdpush
      hdmstore hsz1 hgasPush hmem hgasMem hgasVL
    exact ⟨_, hstash.runs, hstash.memory, hstash.activeWords, hstash.pc, hstash.code,
      hstash.validJumps, hstash.addr, hstash.canMod, hstash.storage, hstash.stack⟩
  · -- == `resultTmp = none`: the fire-and-forget `POP` ==
    intro hnone
    have hemit : emitStmt (matCache prog) (defsOf prog) (.create cs)
        = (argsB ++ [Byte.create2]) ++ [Byte.pop] := by
      have h0 : emitStmt (matCache prog) (defsOf prog) (.create cs)
          = argsB ++ [Byte.create2]
            ++ (match cs.resultTmp with
                | some t' => emitImm (UInt256.ofNat (slotOf t')) ++ [Byte.mstore]
                | none => [Byte.pop]) := rfl
      rw [h0, hnone]
    have hlen : (emitStmt (matCache prog) (defsOf prog) (.create cs)).length
        = argsB.length + 2 := by
      rw [hemit]
      simp only [List.length_append, List.length_singleton]
    have hbnd : base + (argsB.length + 1) < 2 ^ 32 :=
      create_stmt_offset_bound_of_codeFits hcodeFits hb hcur (by omega)
    have hdpopT : decode (lower prog) (UInt32.ofNat (base + (argsB.length + 1)))
        = some (.Smsf .POP, .none) := by
      have hpi : Evm.parseInstr Byte.pop = .Smsf .POP := by decide
      rw [← hpi]
      exact nonpush_leaf_decodeF prog base (argsB.length + 1) Byte.pop
        (emitStmt (matCache prog) (defsOf prog) (.create cs)) hbnd
        (by rw [hemit, List.getElem?_append_right (by
              simp only [List.length_append, List.length_singleton]; omega)]
            simp only [List.length_append, List.length_singleton]
            rw [show argsB.length + 1 - (argsB.length + 1) = 0 from by omega]
            rfl)
        (by decide) hseg
    have hdpop : decode resumeFr.exec.executionEnv.code resumeFr.exec.pc
        = some (.Smsf .POP, .none) := by
      rw [hcode, hpc']; exact hdpopT
    have hszP : resumeFr.exec.stack.size ≤ 1024 := by
      rw [hstkflag]; show (1 : ℕ) ≤ 1024; omega
    have hgasPop : GasConstants.Gbase ≤ resumeFr.exec.gasAvailable.toNat :=
      (CleanHaltExtract.next_pop_of_cleanHalt resumeFr addrW [] hch hdpop hstkflag hszP).1
    exact runs_pop resumeFr addrW [] hdpop hstkflag hszP hgasPop

/-- **R3-CREATE, step 2 — the CREATE dispatch bundle** (CLOSED, two-arm disjunction; CREATE2
soft-fail recorder alignment, design spec §4).

The CREATE twin of `call_dispatch_of_coupled`. At a coupled top-level frame decoding `CREATE2` with
the lowered operand stack `valueW :: initOffW :: initSizeW :: saltW :: []`.

WHY the single-`.needsCreate` conclusion (the CALL shape) is the WRONG shape here. `createArm` steps
to `.needsCreate` only under FOUR guards (`System.lean:99,101`): `nonce < 2^64-1`,
`value ≤ selfBalance`, `depth < 1024`, `initCode.size ≤ 49152`. Otherwise it takes a CLEAN,
non-exception `.next` fallback (`resumeAfterCreate failed`, pushing `0`). The lowered CREATE2 forwards
an ARBITRARY `valueW`/`initSizeW`, so — unlike the CALL twin, whose lowered `value = 0` collapses
`callArm`'s only non-depth fallback trigger — a lowered CREATE2 can SOFT-FAIL here and
`stepFrame createFr = .needsCreate` is genuinely FALSE on that path.

RESOLUTION (landed). The recorder now logs EVERY top-level CREATE2 outcome (`Spec/Recorder.lean`): a
descend records the child result (`.needsCreate` → `.create pending` → child), a soft-fail records
`softFailCreateRecord createFr` (world-unchanged, addr 0) via the `isCreate2Op`/`.next` gate. So
`log.creates` aligns 1:1 with CREATE2 cursors, and this bundle is a two-arm disjunction whose branch is
DERIVED (not assumed) from the recorded head `rec`:

  * DESCEND arm: `stepFrame createFr = .needsCreate cp pending` with the resume-half pins
    (execEnv/validJumps/pc/memory via `stepFrame_needsCreate_(site_)inv` +
    `stepFrame_create2_needsCreate_memory`; `pending.stack = []` via
    `stepFrame_create2_needsCreate_stack` on the 4-operand `pop4` residual);
  * SOFT-FAIL arm: `stepFrame createFr = .next exec'`, `rec = softFailCreateRecord createFr`
    (`recorderCoupled_create_softfail`), `exec'` env-unchanged and pc `+1`
    (`stepFrame_create2_next_execEnv`/`_pc`).

The stepFrame is case-split directly; the DESCEND/SOFT-FAIL arm is selected by the actual step.
The `.halted` arm is excluded by the COUPLING (a `.halted` first step records no create, but the
coupled create suffix `rec :: dS'` is nonempty — `creates_nil_of_stepFrame_halted`); `.needsCall` is
impossible at a CREATE2 decode (`stepFrame_needsCall_site_inv` forces a CALL-family decode). NO
`CreateResolves`/`CreateDescends` premise, NO domain restriction (the descend guard is supplied by the
descend arm's own `.needsCreate` witness, not by the retired `driveLog_creates_const_of_depth`). The
clean-halt/`canModifyState` hypotheses (`_hch`/`_hmod`) are retained for interface parity with the
CALL twin and the create realisation consumers; the reshape itself does not consume them. -/
theorem create_dispatch_of_coupled {log : RunLog} {createFr : Frame}
    {valueW initOffW initSizeW saltW : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS' : List CreateRecord}
    (hcp : RecorderCoupled log createFr gS sS cS (rec :: dS'))
    (_hch : CleanHaltsNonException createFr)
    (hdec : decode createFr.exec.executionEnv.code createFr.exec.pc
      = some (.System .CREATE2, .none))
    (hstk : createFr.exec.stack = valueW :: initOffW :: initSizeW :: saltW :: [])
    (_hmod : createFr.exec.executionEnv.canModifyState = true) :
    -- Arm D (descend): the recorded head is a real child; the step descends.
    (∃ (cp : Evm.CreateParams) (pending : Evm.PendingCreate),
        stepFrame createFr = .needsCreate cp pending
      ∧ pending.frame.exec.executionEnv = createFr.exec.executionEnv
      ∧ pending.frame.validJumps = createFr.validJumps
      ∧ pending.frame.exec.pc = createFr.exec.pc
      ∧ pending.frame.exec.toMachineState.memory = createFr.exec.toMachineState.memory
      ∧ pending.stack = ([] : Stack Word))
    ∨
    -- Arm S (soft-fail): the recorded head is `softFailCreateRecord createFr`; the step is `.next`.
    (∃ exec' : ExecutionState,
        stepFrame createFr = .next exec'
      ∧ rec = softFailCreateRecord createFr
      ∧ exec'.executionEnv = createFr.exec.executionEnv
      ∧ exec'.pc = createFr.exec.pc + 1) := by
  have hc2 : isCreate2Op createFr = true := by
    unfold isCreate2Op; rw [hdec]; rfl
  -- Case-split on the actual step; the recorded head determines which arm.
  cases hstep : stepFrame createFr with
  | needsCreate cp pending =>
      -- DESCEND arm: pins from the CREATE2 `.needsCreate` site inversions.
      refine Or.inl ⟨cp, pending, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Evm.stepFrame_needsCreate_inv hstep).2.2.2
      · exact (Evm.stepFrame_needsCreate_site_inv hstep).2.2.1
      · exact (Evm.stepFrame_needsCreate_site_inv hstep).2.1
      · exact Evm.stepFrame_create2_needsCreate_memory (by rw [hdec]; rfl) hstep
      · obtain ⟨residual, _, _, _, _, hpop, hpdstk⟩ :=
          Evm.stepFrame_create2_needsCreate_stack (by rw [hdec]; rfl) hstep
        rw [hpdstk]
        -- `pop4` on the 4-operand lowered stack yields residual `[]`.
        rw [hstk] at hpop
        simp only [Stack.pop4] at hpop
        injection hpop with hpop'
        exact (congrArg (·.1) hpop').symm
  | next exec' =>
      -- SOFT-FAIL arm: the coupling's create head is `softFailCreateRecord createFr`.
      obtain ⟨_, hrec⟩ := recorderCoupled_create_softfail hcp hc2 hstep
      refine Or.inr ⟨exec', rfl, hrec, ?_, ?_⟩
      · exact Evm.stepFrame_create2_next_execEnv (by rw [hdec]; rfl) hstep
      · exact Evm.stepFrame_create2_next_pc (by rw [hdec]; rfl) hstep
  | halted halt =>
      -- The coupling's create suffix `rec :: dS'` is nonempty, but a `.halted` first step records
      -- NO create — contradiction.
      exact absurd (creates_nil_of_stepFrame_halted hcp hstep) (by simp)
  | needsCall cp pending =>
      -- A CREATE2 decode cannot step to `.needsCall` (that forces a CALL-family decode).
      exfalso
      rcases (Evm.stepFrame_needsCall_site_inv hstep).1 with h | h | h | h <;>
        · rw [hdec] at h; simp at h

/-- **The CREATE-site decode** at the arg-run endpoint `createFr` (the CREATE2 byte one past the
four operand pushes), pinned by the `emitStmt` byte layout + `codeFits`. The CREATE twin of the CALL
head's `hdecCall`. -/
private theorem create_site_decode {prog : Program} {L : Label} {b : Block} {pc : Nat}
    {cs : CreateSpec} {fr0 createFr : Frame}
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hfrpc : fr0.exec.pc = UInt32.ofNat (pcOf prog L pc))
    (hcallcode : createFr.exec.executionEnv.code = lower prog)
    (hcallpc : createFr.exec.pc = fr0.exec.pc + UInt32.ofNat
        ((matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value).length)) :
    decode createFr.exec.executionEnv.code createFr.exec.pc = some (.System .CREATE2, .none) := by
  have hbt : prog.blocks.toList[L.idx]? = some b := Lir.toList_of_blockAt hb
  set argsB := matCache prog cs.salt ++ matCache prog cs.initSize
      ++ matCache prog cs.initOffset ++ matCache prog cs.value with hargsB
  have hemit0 : emitStmt (matCache prog) (defsOf prog) (.create cs)
      = argsB ++ [Byte.create2]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none => [Byte.pop]) := rfl
  have hcreatebyte : (emitStmt (matCache prog) (defsOf prog) (.create cs))[argsB.length]?
      = some Byte.create2 := by
    rw [hemit0, List.getElem?_append_left (by
          simp only [List.length_append, List.length_singleton]; omega),
        List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hseg : ∀ j, j < (emitStmt (matCache prog) (defsOf prog) (.create cs)).length →
      (flatBytes prog)[pcOf prog L pc + j]?
        = (emitStmt (matCache prog) (defsOf prog) (.create cs))[j]? :=
    fun j hj => flatBytes_at_pcOf_offset prog L b pc (.create cs) j hbt hcur hj
  have hargslt : argsB.length
      < (emitStmt (matCache prog) (defsOf prog) (.create cs)).length := by
    rw [hemit0]
    simp only [List.length_append, List.length_singleton]
    omega
  rw [hcallcode, hcallpc, hfrpc, ofNat_add']
  have h := nonpush_leaf_decodeF prog (pcOf prog L pc) argsB.length Byte.create2
    (emitStmt (matCache prog) (defsOf prog) (.create cs))
    (create_stmt_offset_bound_of_codeFits hcodeFits hb hcur (by omega))
    hcreatebyte (by decide) hseg
  simpa using h

/-- **The arm-uniform CREATE resume-frame bundle** — the CREATE twin of the returning-CALL half of
`call_head_realises_coupled`, driven off the two-arm `create_dispatch_of_coupled`. From a coupled
CREATE2 site (arg-run endpoint `createFr`, coupled `rec :: dS'`, clean-halt, `CreateResolves` seam),
produce a resume frame `resumeFr`, the `Runs createFr resumeFr` edge (a `.create` node on the descend
arm; a single `.next` step on the soft-fail arm), the advanced coupling on `dS'`, and every resume
PIN — all HOLDING ON BOTH ARMS. The descend-only `CreateReturns`/`resumeAfterCreate` conjuncts are
DROPPED (`create_dispatch`'s soft-fail arm never `.needsCreate`). -/
private theorem create_resume_of_dispatch {log : RunLog}
    {createFr : Frame} {valueW initOffW initSizeW saltW : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS' : List CreateRecord}
    (hcpcall : RecorderCoupled log createFr gS sS cS (rec :: dS'))
    (hchcall : CleanHaltsNonException createFr)
    (hdecCreate : decode createFr.exec.executionEnv.code createFr.exec.pc
      = some (.System .CREATE2, .none))
    (hcreatestk : createFr.exec.stack = valueW :: initOffW :: initSizeW :: saltW :: [])
    (hcreatemod : createFr.exec.executionEnv.canModifyState = true)
    (hresolve : CreateResolves createFr) :
    ∃ resumeFr : Frame,
      Runs createFr resumeFr
      ∧ RecorderCoupled log resumeFr gS sS cS dS'
      ∧ resumeFr.exec.executionEnv = createFr.exec.executionEnv
      ∧ resumeFr.exec.pc = createFr.exec.pc + 1
      ∧ resumeFr.exec.stack = createAddrOrZero rec.result rec.pending :: []
      ∧ resumeFr.exec.toMachineState.memory = createFr.exec.toMachineState.memory
      ∧ createFr.exec.toMachineState.activeWords.toNat
          ≤ resumeFr.exec.toMachineState.activeWords.toNat
      ∧ resumeFr.validJumps = createFr.validJumps
      ∧ (∀ k, selfStorage resumeFr k
          = evmCreateOracle.postStorage rec.result rec.pending
              createFr.exec.executionEnv.address k) := by
  classical
  rcases create_dispatch_of_coupled hcpcall hchcall hdecCreate hcreatestk hcreatemod with
    ⟨cp, pending, hstep, henv, hvj, hpcpin, hmempin, hpdstk⟩
    | ⟨exec', hstep, hreceq, hexecenv, hexecpc⟩
  · -- == DESCEND arm: the returning CREATE + successful resume ==
    obtain ⟨childRes, resumeFr, hcrret, hrec, hresume, hcpres⟩ :=
      recorderCoupled_create_extract hcpcall hstep hresolve
    have hpend : rec.pending = pending := by rw [hrec]
    have hresult : rec.result = childRes.toCreateResult := by rw [hrec]
    -- the resume equation spelled with `rec.result` (a `CreateResult`) / `rec.pending`.
    have hresume' : resumeAfterCreate rec.result rec.pending = .ok resumeFr := by
      rw [hresult, hpend]; exact hresume
    refine ⟨resumeFr, Runs.create hcrret (Runs.refl _), hcpres, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- execEnv: resume keeps the pending frame's env = the CREATE-site env.
      rw [resumeAfterCreate_execEnv childRes pending resumeFr hresume, henv]
    · rw [resumeAfterCreate_pc childRes pending resumeFr hresume, hpcpin]
    · -- stack: `pending.stack.push pushedValue`; `pending.stack = []`, `pushedValue = createAddrOrZero`.
      rw [resumeAfterCreate_stack rec.result rec.pending resumeFr hresume', hpend, hpdstk]
      rfl
    · rw [resumeAfterCreate_memory rec.result rec.pending resumeFr hresume', hpend, hmempin]
    · -- activeWords: `createFr.aw = pending.frame.aw ≤ resumeFr.aw`.
      have haw : pending.frame.exec.toMachineState.activeWords
          = createFr.exec.toMachineState.activeWords :=
        Evm.stepFrame_create2_needsCreate_activeWords (by rw [hdecCreate]; rfl) hstep
      rw [← haw, ← hpend]
      exact resumeAfterCreate_activeWords_ge rec.result rec.pending resumeFr hresume'
    · rw [resumeAfterCreate_validJumps childRes pending resumeFr hresume, hvj]
    · intro k
      rw [selfStorage_eq_storageAt,
          resumeAfterCreate_execEnv childRes pending resumeFr hresume, henv]
      show (resumeFr.exec.accounts.find? createFr.exec.executionEnv.address |>.option 0
              (·.lookupStorage k)) = _
      rw [resumeAfterCreate_accounts rec.result rec.pending resumeFr hresume']
      rfl
  · -- == SOFT-FAIL arm: a single `.next` step; `rec = softFailCreateRecord createFr` ==
    obtain ⟨hcpres, _⟩ := recorderCoupled_create_softfail hcpcall
      (by unfold isCreate2Op; rw [hdecCreate]; rfl) hstep
    have hc2 : (decode createFr.exec.executionEnv.code createFr.exec.pc |>.getD (.STOP, .none)).1
        = .System .CREATE2 := by rw [hdecCreate]; rfl
    refine ⟨{ createFr with exec := exec' },
      Runs.single (stepsTo_of_next hstep), hcpres, hexecenv, hexecpc, ?_, ?_, ?_, ?_, ?_⟩
    · -- stack: `residual.push 0` with `residual = []`; and `createAddrOrZero rec = 0`.
      obtain ⟨residual, _, _, _, _, hpop, hstkeq⟩ :=
        Evm.stepFrame_create2_next_stack hc2 hstep
      rw [hstkeq]
      rw [hcreatestk] at hpop
      simp only [Stack.pop4] at hpop
      injection hpop with hpop'
      have hres0 : residual = [] := (congrArg (·.1) hpop').symm
      rw [hres0]
      rw [hreceq, createAddrOrZero_softFailCreateRecord]
      rfl
    · exact Evm.stepFrame_create2_next_memory hc2 hstep
    · -- activeWords: soft-fail resume grows the frame's activeWords to `M`.
      exact Evm.stepFrame_create2_next_activeWords hc2 hstep
    · rfl
    · -- storage: soft-fail keeps accounts (`postStorage softFail = createFr self-lens`).
      intro k
      have hacc : exec'.accounts = createFr.exec.accounts :=
        Evm.stepFrame_create2_next_accounts hc2 hstep
      have haddr : exec'.executionEnv.address = createFr.exec.executionEnv.address := by
        rw [hexecenv]
      rw [selfStorage_eq_storageAt, storageAt]
      show (exec'.accounts.find? exec'.executionEnv.address
            |>.option 0 (·.lookupStorage k)) = _
      rw [hacc, haddr, hreceq]
      rfl

/-- **The COUPLED CREATE-head bundle** (CLOSED — CREATE2 soft-fail recorder alignment). The CREATE
twin of `call_head_realises_coupled`: the SAME Piece-A/B assembly (`create_args_run_of_coupled` →
`create_dispatch_of_coupled` → the `CreateResolves` seam → `recorderCoupled_create_extract` on the
descend arm / `recorderCoupled_create_softfail` on the soft-fail arm), stopping BEFORE the tail and
keeping the coupling alive at the create resume frame (tail suffix `dS'` — exactly one create record
consumed). Consumed by the coupled producer walk's `simStmt_coupled_create` (`Producer.lean`) to
re-establish `Corr` at the post-create frame. ARM-UNIFORM resume bundle: the descend-only
`CreateReturns`/`resumeAfterCreate` conjuncts are DROPPED in favour of a single `Runs createFr
resumeFr` witness that holds on BOTH the descend (`Runs.create`) and soft-fail (`Runs.step`) arms;
every resume PIN below holds on both. -/
theorem create_head_realises_coupled {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {L : Label} {b : Block} {pc : Nat} {cs : CreateSpec}
    {st0 : IRState} {fr0 : Frame} {valueW initOffW initSizeW saltW : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS' : List CreateRecord} {I : Tmp → Prop}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hcorr : Corr prog sloadChg 0 I st0 fr0 L pc)
    (hcp : RecorderCoupled log fr0 gS sS cS (rec :: dS'))
    (hch : CleanHaltsNonException fr0)
    (hcr : ∀ fr', Runs fr0 fr' → CreateResolves fr')
    (hvalue : st0.locals cs.value = some valueW)
    (hoff : st0.locals cs.initOffset = some initOffW)
    (hsize : st0.locals cs.initSize = some initSizeW)
    (hsalt : st0.locals cs.salt = some saltW)
    (hfreeValue : RematClosureFree prog I (.tmp cs.value))
    (hfreeOff : RematClosureFree prog I (.tmp cs.initOffset))
    (hfreeSize : RematClosureFree prog I (.tmp cs.initSize))
    (hfreeSalt : RematClosureFree prog I (.tmp cs.salt))
    (hstkSalt : 0 + (chargeCache prog sloadChg cs.salt).length ≤ 1024)
    (hstkSize : 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024)
    (hstkOff : 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024)
    (hstkValue : 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024) :
    ∃ (resumeFr createFr : Frame),
      Runs fr0 createFr
      ∧ createFr.exec.pc = fr0.exec.pc + UInt32.ofNat
          ((matCache prog cs.salt ++ matCache prog cs.initSize
            ++ matCache prog cs.initOffset ++ matCache prog cs.value).length)
      ∧ createFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory
      ∧ fr0.exec.toMachineState.activeWords.toNat
          ≤ createFr.exec.toMachineState.activeWords.toNat
      ∧ Runs createFr resumeFr
      ∧ RecorderCoupled log resumeFr gS sS cS dS'
      ∧ resumeFr.exec.executionEnv.address = fr0.exec.executionEnv.address
      ∧ resumeFr.exec.executionEnv.code = lower prog
      ∧ resumeFr.exec.executionEnv.canModifyState = true
      ∧ resumeFr.exec.pc = createFr.exec.pc + 1
      ∧ resumeFr.exec.stack = createAddrOrZero rec.result rec.pending :: []
      ∧ resumeFr.exec.toMachineState.memory = createFr.exec.toMachineState.memory
      ∧ createFr.exec.toMachineState.activeWords.toNat
          ≤ resumeFr.exec.toMachineState.activeWords.toNat
      ∧ resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0
      ∧ (∀ k, selfStorage resumeFr k
          = evmCreateOracle.postStorage rec.result rec.pending
              fr0.exec.executionEnv.address k) := by
  classical
  -- Piece B step 1: the argument-push run (coupling + clean-halt carried to the CREATE site).
  obtain ⟨createFr, hargs, hcreatepc, hcreatestk, hcreatecode, hcreatevj, hcreateaddr, hcreatemod,
      hcreatemem, hcreateact, _hcreatesto, hcpcreate, hchcreate⟩ :=
    create_args_run_of_coupled hwl hcodeFits hb hcur hcorr hcp hch hvalue hoff hsize hsalt
      hfreeValue hfreeOff hfreeSize hfreeSalt hstkSalt hstkSize hstkOff hstkValue
  -- the CREATE2 byte decode at `createFr`.
  have hdecCreate := create_site_decode hcodeFits hb hcur hcorr.pc_eq hcreatecode hcreatepc
  -- the `CreateResolves` seam at the CREATE site (any reachable frame resolves).
  have hresolve : CreateResolves createFr := hcr createFr hargs
  -- the arm-uniform resume bundle.
  obtain ⟨resumeFr, hrunsCR, hcpres, hresenv, hrespc, hresstk, hresmem, hresact, hresvj, hressto⟩ :=
    create_resume_of_dispatch hcpcreate hchcreate hdecCreate hcreatestk hcreatemod hresolve
  refine ⟨resumeFr, createFr, hargs, by rw [hcreatepc], hcreatemem, hcreateact,
    hrunsCR, hcpres, ?_, ?_, ?_, hrespc, hresstk, hresmem, hresact, ?_, ?_⟩
  · rw [hresenv, hcreateaddr]
  · rw [hresenv, hcreatecode]
  · rw [hresenv, hcreatemod]
  · rw [hresvj, hcreatevj, hresenv, hcreatecode]
    exact hcorr.validJumps_lower
  · intro k; rw [hressto k, hcreateaddr]

/-- **R3-CREATE — create realisation from the log** (CLOSED — CREATE2 soft-fail recorder alignment).
The CREATE twin of `callRealises_of_recorded`, discharging `CreateRealisesS`. Assembly over the
arm-uniform `create_head_realises_coupled` (Piece A/B) + the Route-B tail `create_tail_of_cleanHalt`.
The `CreateRealisesS` conclusion was relaxed to the arm-uniform resume edge (`Runs createFr resumeFr`,
dropping the descend-only `CreateReturns`/`resumeAfterCreate` conjuncts), so both the descend and
CREATE2 soft-fail arms discharge it. NO free-∀ ties, NO single-create restriction. -/
theorem createRealises_of_recorded {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat} {cs : CreateSpec}
    {st0 : IRState} {fr0 : Frame} {valueW initOffW initSizeW saltW : Word}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    {rec : CreateRecord} {dS' : List CreateRecord} {I : Tmp → Prop}
    (hwl : WellLowered prog)
    (hcodeFits : codeFits prog)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.create cs))
    (hcp : RecorderCoupled log fr0 gS sS cS (rec :: dS'))
    (hch : CleanHaltsNonException fr0)
    (haddr : fr0.exec.executionEnv.address = self)
    (hcr : ∀ fr', Runs fr0 fr' → CreateResolves fr')
    (hvalue : st0.locals cs.value = some valueW)
    (hoff : st0.locals cs.initOffset = some initOffW)
    (hsize : st0.locals cs.initSize = some initSizeW)
    (hsalt : st0.locals cs.salt = some saltW)
    (hfreeValue : RematClosureFree prog I (.tmp cs.value))
    (hfreeOff : RematClosureFree prog I (.tmp cs.initOffset))
    (hfreeSize : RematClosureFree prog I (.tmp cs.initSize))
    (hfreeSalt : RematClosureFree prog I (.tmp cs.salt))
    (hstkSalt : 0 + (chargeCache prog sloadChg cs.salt).length ≤ 1024)
    (hstkSize : 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024)
    (hstkOff : 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024)
    (hstkValue : 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024)
    (hslotaddr : ∀ t, cs.resultTmp = some t →
      slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits) :
    CreateRealisesS prog sloadChg I L b pc cs st0
      (match cs.resultTmp with
        | some t' => { st0 with world := fun key =>
                        evmCreateOracle.postStorage rec.result rec.pending self key }.setLocal
                        t' (createAddrOrZero rec.result rec.pending)
        | none   => { st0 with world := fun key =>
                        evmCreateOracle.postStorage rec.result rec.pending self key })
      fr0 := by
  intro hcorr
  classical
  -- the coupled CREATE-head bundle (Piece A/B, coupling kept at the resume frame).
  obtain ⟨resumeFr, createFr, hargs, hcreatepc, hcreatemem, hcreateact, hrunsCR, _hcpres,
      hresaddr0, hrescode, hrescanmod, hrespc, hresstk, hresmem, hresact, hresvj, _hressto⟩ :=
    create_head_realises_coupled hwl hcodeFits hb hcur hcorr hcp hch hcr hvalue hoff hsize hsalt
      hfreeValue hfreeOff hfreeSize hfreeSalt hstkSalt hstkSize hstkOff hstkValue
  -- clean halt at the resume frame (forwarded across the arg run + the CREATE node).
  have hchres : CleanHaltsNonException resumeFr :=
    cleanHaltsNonException_forward hch (hargs.trans hrunsCR)
  -- the resume frame sits one byte past the CREATE2 byte: `pcOf + (argsLen + 1)`.
  have hrespc' : resumeFr.exec.pc = UInt32.ofNat (pcOf prog L pc
      + (matCache prog cs.salt ++ matCache prog cs.initSize
          ++ matCache prog cs.initOffset ++ matCache prog cs.value).length + 1) := by
    rw [hrespc, hcreatepc, hcorr.pc_eq,
        show (1 : UInt32) = UInt32.ofNat 1 from rfl, ofNat_add', ofNat_add']
  -- Piece B step 3: the Route-B tail.
  have htail := create_tail_of_cleanHalt (resumeFr := resumeFr)
    hcodeFits hb hcur hrescode hrespc' hchres hslotaddr
  -- assemble the `CreateRealisesS` existential.
  refine ⟨rec.result, rec.pending, createFr, resumeFr,
    (matCache prog cs.salt ++ matCache prog cs.initSize
      ++ matCache prog cs.initOffset ++ matCache prog cs.value).length,
    stepScopedS_create_of_cursor, ?_, rfl, hargs, hcreatepc, hcreatemem, hcreateact,
    hrunsCR, hresaddr0, ?_, hrescanmod, hrespc, ?_, hresmem, hresact, ?_, ?_, htail⟩
  · -- st0' pin: world = the resumed self-lens; `self = fr0.address`.
    cases cs.resultTmp <;> simp [haddr]
  · rw [hrescode]
  · rw [hresstk]
  · rw [hresvj]
  · -- the post-state scoping fold.
    exact create_post_wellScoped (world' := fun key =>
        evmCreateOracle.postStorage rec.result rec.pending fr0.exec.executionEnv.address key)
      (addrW := createAddrOrZero rec.result rec.pending)
      hb hcur hwl.defsCons hcorr.wellScoped

end Lir.V2
