import LirLean.V2.Drive.Headline
import LirLean.Decode.BoundaryReach
import LirLean.Spec.BudgetDerivations
import LirLean.V2.Realisability.Producer
import LirLean.V2.Realisability.Witness
import LirLean.V2.Realisability.WitnessParams
import LirLean.V2.Realisability.WitnessChecks

/-!
# LirLean v2 — the REALISABILITY SPEC skeleton (Phase-3 target statements; WIP-only)

**EVERY `sorry` IN THIS FILE IS TRACKED DEBT.** This module is the reviewable Phase-3
specification: the flagship `lower_conforms` (R11) is the target statement of the whole
experiment, and the obligations R1–R12 are the named gaps between the green machinery in the
tree and that flagship. All `def`s/`structure`s here are REAL (complete, no `sorry`); only
theorem PROOFS are `sorry`d. This module is deliberately registered in the NON-DEFAULT
`WIP` lean_lib — the default `LirLean` target stays sorry-free and does not import it.

## The vacuity lessons this file is shaped by

1. **The retired `Lir.GasRealises` universal** (HonestGasTie's finding, Phase 2): a single
   fixed gas word, universally quantified over frames pinned only by address, is
   unsatisfiable — one adversarial frame with a different `gasAvailable` refutes it.
2. **The free-`∀` disease in the former `StmtTies`/`TermTies`**
   (`docs/fleet-2026-07-02/skeptic-f1-verdict.md`): a variable universally quantified in the
   tie, pinned to a run-specific value in the conclusion, with no antecedent linking it to
   the run (`ob` in the gas conjunct, `w` in the sload conjunct, `st0'` in the assign
   conjunct, the address/kind/gas demands of `TermTies`). The supplied tie hypotheses of
   `lower_conforms_cyclic_assembled` are FALSE for essentially every nonempty program.
3. **NEW (this file's audit): `Lir.SstoreRealises` is itself free-`∀` unsatisfiable**
   (`LirLean/SimStmt.lean:318`): it quantifies over EVERY frame `g` pinned only by
   address + stack shape and concludes gas facts about `g` — an adversarial zero-gas frame
   with the same address/stack refutes it, so `∃ acc, SstoreRealises fr kw vw acc` (the
   `StmtTies` sstore conjunct) is false for every `fr`. The reshape here DROPS that conjunct;
   its content returns point-wise at the concrete frame (R4).
4. **NEW (this file's audit): `Lir.V2.RunDefinable` is unsatisfiable for every program
   containing a `Stmt.call` or a gas read** (`LirLean/V2/IRRun.lean`): its `stmts` field
   demands `StmtsDefinable st b.stmts` for every present block, and `StmtDefinable`'s
   `.call` arm is literally `False` while its assign arm demands `e ≠ .gas`. Folding
   `RunDefinable` into the flagship's static bundle would make the flagship VACUOUS on
   exactly the gas-reading/calling domain it exists for. `WellLowered.defs` below therefore
   uses the gas/call-aware `RunDefinableG` (this file), whose definability is threaded along
   `RunStmts` itself (the semantics natively handles the gas-stream/oracle supply).
5. Two further refutable-∃ shapes found while re-running the skeptic drill on the PLANNED
   reshape, fixed before statement: the sload arm's planned `∃ w, evalExpr st0 0 (.sload k)
   = some w` conclusion (an empty-locals `Corr` witness refutes it — the key binding must be
   an ANTECEDENT, mirroring the sstore arm), and the ret arm's `∃ vw, st'.locals t = some vw`
   conclusion (same refutation — the epilogue block is stated under a `∀ vw`-antecedent
   instead, as the original's inner block already was).
6. **NEW (independent review drill): the `defsOf`-consistency hole.** `defsOf`
   (`Lowering.lean`) is a FIRST-find over program order while `emitStmt` keys its spill
   stash on `defsOf t`, so a program that redefines a tmp with mixed pure/spill defs
   (e.g. `[.assign t (.imm 1), .assign t .gas]`) emits NO GAS byte at the shadowed def yet
   `EvalStmt.assignGas` demands a gas-stream head — refuting the flagship INSIDE its
   hypothesis envelope (`RunDefinableG`'s gas arm is unconditionally true). The per-cursor
   fact was already consumed by the walk (`defsSound_preserved_assignPure`'s `hself`,
   `DefsSound.lean`) but lived only in per-lemma side conditions — a free-∀-ADJACENT
   disease instance: a scope assumption absent from the statement's hypothesis surface.
   Fixed statically: `WellLowered.defsCons` (`DefsConsistent`, decidable, R9-checkable).
7. **RESOLVED (foundation call-stream): the single-call restriction is GONE.** The former
   function-shaped `CallOracle` replayed only the HEAD `CallRecord`, so a syntactically-single
   call inside a loop that fired per iteration with differing child outcomes refuted
   R3/`Conforms` at the second iteration — patched at the time with `SingleCall` + a decidable
   log-side `hone : log.calls.length ≤ 1`. Both are now DELETED: calls are a CONSUMED
   `CallStream` (`callStreamOf` maps the WHOLE recorded list, consumed head-first by
   `Stmt.call`), exactly the gas channel's positional solution. Distinct dynamic calls consume
   distinct stream heads, so a per-iteration loop CALL is correct — no single-call domain
   restriction anywhere.
8. **NEW (round-3 review): the inherited SCOPING conjuncts carried the same refutable-∀
   disease as the value conjuncts.** `Lir.StepScoped`'s live-scope clause
   (`DefsSound.lean:514`) demands, at an `assign t _` cursor, that NO currently-bound
   tmp's registered def reads `t` — a free-∀ over the live set, refuted BY THE FILE'S OWN
   WITNESS at `exProg`'s second loop-iteration entry (block 1, pc 0: `t6 := gas` rebinds
   `t6` while `t8` is bound from iteration 1 with `defsOf exProg t8 = some (.lt t6 t7)`),
   a real on-run state fully consistent with `Corr`/`RecorderCoupled`/
   `CleanHaltsNonException`. Mechanism: the clause is define-before-use, and a LOOP
   re-binds tmps with live dependents by construction. The root cause is deeper than the
   ties: on the loop-EXIT iteration, between the `t6` rebind and `t8`'s reassign,
   recompute-on-use `DefsSound` is ITSELF false at the real mid-block states (`t8` holds
   the stale `0` while `evalExpr (.lt t6 t7) = 1` — machine-checked at
   `not_defsSound_stale`). The LOWERING is not misbehaving — rematerialisation is
   exercised only at USE sites, and a bound-but-unused stale dependent is harmless to the
   lowered code; the INVARIANT was overclaiming. Fix (route (i), shadowing-aware): the
   ties' scoping conclusions are the STATIC residue `StepScopedS` (and `CallRealisesS`
   for the call arm); staleness is tracked by an explicit invalidation set
   (`ReadsOf`/`invalStep`/`DefsSoundS`); and the forced machinery reshape is the NEW
   tracked obligation R0b — the current sim machinery (`Corr.defsSound` at every
   statement cursor) cannot traverse a loop-exit iteration of a rebinding program. The
   witness `exProg` STAYS AS IS: it exercises rebinding-with-live-dependents by
   construction, which is exactly why it caught this.

## The scope seam added beyond the fleet sketch

* **`RunLog.clean` conservatively excludes zero-gas reverts**: exp003's `endCall` maps an
  `.exception` to `success := false, gasRemaining := 0, output := .empty`, so a genuine
  zero-gas revert is indistinguishable from an exception ON THE LOG. `clean` demands
  `success ∨ gasRemaining ≠ 0` — sound (hypothesis false ⇒ theorem silent, never unsound),
  and it cuts the zero-gas-revert corner out of scope. Tracked decision.

(The former nonzero-SSTORE scope seam is GONE: `sim_sstore` now covers zero writes /
slot clears — the read-back of a cleared slot goes through `Evm.Storage.findD_erase_self`
in `LirLean/StorageErase.lean` — so the seam predicate and the flagship's named
nonzero-write hypothesis were removed.)

Every declaration's docstring states what is SUPPLIED (hypothesis surface of the flagship /
honest seam) vs DERIVED (an R-obligation discharges it from the run or the program text).
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch

/-- **The `IRWellFormed → budgets → layout-valid` soundness bridge** (stage 1B B3). From the
static, program-text-only `IRWellFormed prog` and the two scalar budgets `codeFits`/`stackFits`,
reconstruct the full `WellLowered prog` bundle the flagships consume. This is where the ~15
per-cursor `WellFormedLowered`/`ClosedCFG` bounds are RE-DERIVED from the two scalars (B1a
`pcBounds_of_codeFits`, B1b `stackBounds_of_stackFits`); `slots_slot` is derived from
`defEnv`'s canonical spill registrations. (There is no fuel-sufficiency family anymore: the fold emission always fully
expands — structural termination on the ordered def-env, `IRWellFormed.defEnvOrdered`.)
`WellFormedLowered` stays INTERNAL (the `Sim/` lemmas keep projecting its fields) — it is
merely (re)built here, not exposed as a premise. -/
theorem wellLowered_of_IRWellFormed {prog : Program}
    (hwf : IRWellFormed prog) (hcode : codeFits prog) (hstk : stackFits prog) :
    WellLowered prog := by
  obtain ⟨hoff, hbsstore, hbsload, hbret, hbstop, hbjump, hbbranch, hgas, hretep⟩ :=
    pcBounds_of_codeFits prog hcode hwf.defsConsistent
  refine
    { wf :=
        { bound_sstore := hbsstore
          bound_sload := hbsload
          bound_ret := hbret
          bound_stop := hbstop
          bound_jump := hbjump
          bound_branch := hbbranch
          slots_slot := slots_slot_of_defsOf prog }
      defs := hwf.defineBeforeUse
      defsCons := hwf.defsConsistent
      defEnvOrdered := hwf.defEnvOrdered
      revalidates := hwf.revalidates
      scopedUses := hwf.scopedUses
      entry0 := hwf.entry0
      closed :=
        { entry_present := hwf.cfgClosed.entry_present
          entry_bound := hoff prog.entry.idx
          jump_closed := fun L b dst hb hterm =>
            let ⟨hp, hbd⟩ := hwf.cfgClosed.jump_closed L b dst hb hterm
            ⟨hp, hbd, hoff dst.idx⟩
          branch_closed := fun L b cond thenL elseL hb hterm =>
            let ⟨⟨hp1, hbd1⟩, hp2, hbd2⟩ :=
              hwf.cfgClosed.branch_closed L b cond thenL elseL hb hterm
            ⟨⟨hp1, hbd1, hoff thenL.idx⟩, hp2, hbd2, hoff elseL.idx⟩ }
      stack := stackBounds_of_stackFits prog hstk
      gasBound := hgas
      slotAddr := hwf.slotAddr
      retEpilogueBound := hretep }

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
    intro pc t e w st0 fr0 gS sS cS dS I hcur hne hns hcorr _hcp _hch hv
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
    intro pc t k kv st0 fr0 gS sS cS dS I hcur hcorr _hcp _hch hkey
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
    -- BLOCKER (arm 2 — the sload-key activeWords-flatness `hawk`): the conclusion
    -- `frk.activeWords = fr0.activeWords` is NOT derivable from the `MatRunsC` witness alone.
    -- `MatRunsC` records only `memBytes` (equal bytes) and `memActive` (activeWords ≤,
    -- `MatFoldChannel.lean:819`) — it does NOT pin activeWords EQUALITY, so an adversarial `frk`
    -- with strictly larger activeWords (same bytes) satisfies every field yet refutes this arm.
    -- The fact is TRUE (the `materialise_runsC` construction threads `pushFrameW`/`sloadFrame`/
    -- MLOAD-covered-readback frames, each `activeWords`-preserving by `rfl`), but capturing it
    -- needs a NEW `MatRunsC` field `activeWordsEq` (re-proving `materialise_runsC` and every
    -- constructor site in `MatFoldChannel.lean` — a DEFAULT-cone edit, not performable in this
    -- WIP-only file). In the old `SimStmtStep` path `hawk` was likewise an always-SUPPLIED
    -- structural residual (`LowerConforms.lean:385`, `CleanHaltExtract.lean:784`), never produced.
    have hflat : ∀ frk : Frame,
        MatRunsC prog sloadChg (.tmp k) kv fr0 frk →
        frk.exec.toMachineState.activeWords = fr0.exec.toMachineState.activeWords :=
      fun frk hmrk => sorry
    exact ⟨hslotdef, hstepS, hslots, hwval, hscoped', hslot63, hslotplat, hstkKey, hflat⟩
  -- ===================== arm (3): spilled gas assign (R1 conjunct) =====================
  case arm3 =>
    intro pc t st0 fr0 gS sS cS dS I hcur hcorr hcp hch
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
    intro pc key value kw vw st0 fr0 gS sS cS dS I hcur _hcorr _hcp _hch _hkw _hvw
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
    intro pc cs st0 st0' fr0 cw gw gS sS rec cS' dS I hcur hcp hch haddr
      hcodeFits hcc hcallee hgasfwd hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd
      hslotaddr hst0'
    subst hst0'
    exact callRealises_of_recorded hwl hcodeFits hb hcur hcp hch haddr hcc hcallee hgasfwd
      hfreeCallee hfreeGasFwd hstkCallee hstkGasFwd hslotaddr
  -- ===================== arm (6): create =====================
  case arm6 =>
    intro pc cs st0 st0' fr0 gS sS cS rec dS' I hcur hcp hch haddr hst0'
    -- BLOCKER (arm 6 — `CreateRealisesS`): there is NO `createRealises_of_recorded` producer
    -- anywhere in the tree (grep: the only `CreateRealisesS` occurrences are its `Surface.lean`
    -- definition + this arm). It is the CREATE twin of the closed `callRealises_of_recorded`
    -- (`Machinery.lean:3475`) and needs the CREATE Piece-B run machinery — the analogs of
    -- `call_args_run_of_coupled` / `call_dispatch_of_coupled` / `call_tail_of_cleanHalt` /
    -- `callRealises_of_recorded_finish` — NONE of which exist for CREATE. Piece A alone is present
    -- (`recorderCoupled_create_extract`, `Machinery.lean:2038`). The plan of record
    -- (`docs/planning/r11-run-plan-2026-07-09.md`) lists "CREATE finish half, simStmt_coupled_create"
    -- and "the create realisation bridge (recorded head → CreateReturns resume)" as PENDING
    -- prerequisites for this very theorem (its "Terminal wave"), and notes some `resumeAfterCreate`
    -- frame-pins land in the DEFAULT target (out of this WIP file's scope). Blocked until that
    -- CREATE run producer lands.
    sorry

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

/-- **The `Conforms` channel — CLOSED assembly** (the flagship's world-channel conclusion,
factored out and reused by all three flagships). Given the run's terminal world equation
(the coupled driver's output: SOME halting terminal `(last, haltSig)` reachable from the
entry frame whose `observe`-world equals `O.world`) together with the modellability facts
`hrb`/`hcc`, the recorded `log.observable` is exactly that terminal's `endFrame`, so
`O.world = (observe self log.observable).world` — i.e. `Conforms self log O`.

Pure re-use of R2's internal machinery (`runWithLog_drive` + `runs_of_drive_ok` +
`runs_halt_eq` + `Runs.linear_to_halt`), exactly as `haltNonException_of_cleanLog` uses it:
the drive-adequacy pins `log.observable = endFrame last₀ halt₀` for the run's ACTUAL
terminal, and halting-terminal uniqueness identifies `(last, haltSig)` with
`(last₀, halt₀)`. This is the "static folds and assembly" half of R11 — genuinely closeable
now (axiom-clean), independent of the missing run-producer. The flagships feed it `hrb` (R6
boundary walk) and `hcc` (`hseams.callsCode`); the world equation comes from the run. -/
theorem conforms_of_worldeq {params : CallParams} {fr₀ : Frame}
    {log : RunLog} {self : AccountAddress} {O : Observable}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀)
    (hcr : ∀ fr', Runs fr₀ fr' → CreateResolves fr')
    (hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr')
    (hworld : ∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world
        ∧ (observe self (endFrame last haltSig)).result = O.result) :
    Conforms self log O := by
  obtain ⟨frame, hbc, hdrive⟩ := runWithLog_drive hrun
  rw [hbegin] at hbc
  have hfeq : frame = fr₀ := (Sum.inl.injEq _ _).mp hbc.symm
  rw [hfeq] at hdrive
  obtain ⟨last₀, halt₀, hto₀, hhalt₀, hobs⟩ :=
    runs_of_drive_ok (seedFuel params.gas) fr₀ log.observable hdrive
      (lower_modellable hcr hcc)
  obtain ⟨last, haltSig, hreach, hhalt, hweq, hreq⟩ := hworld
  -- the halting terminal is unique: `last = last₀`, `haltSig = halt₀`.
  have hlast : last = last₀ :=
    runs_halt_eq hhalt (Runs.linear_to_halt hhalt₀ hto₀ hreach)
  subst hlast
  rw [hhalt] at hhalt₀
  have hheq : haltSig = halt₀ := (Signal.halted.injEq _ _).mp hhalt₀
  subst hheq
  -- `log.observable = endFrame last haltSig`, so the recorded world AND result agree.
  unfold Conforms
  rw [hobs]
  exact ⟨hweq.symm, hreq.symm⟩

/-- **R11 — THE FLAGSHIP.** Run the lowered bytecode once with the recording interpreter;
feed the recorded gas reads, call records AND create records into the executable IR
semantics; the IR run exists at the PINNED streams (`realisedGas log` /
`realisedCall log recipient` / `realisedCreate log recipient`, from the PINNED entry
state) and produces the same observable world.

Hypothesis ledger (the honest surface, nothing else): two definitional pins
(`hcode`/`hmod`), two decidable entry facts (`hself`/`hgas`), the source-level
`IRWellFormed` bundle plus the two scalar budgets (`codeFits`/`stackFits`), ONE decidable
scope premise (`hclean`), ONE runtime premise (`hrun`), and one honest seam
structure (`hseams`). The internal `WellLowered` adapter is rebuilt in the proof, not exposed
as a public premise. (The former `hsingle`/`hone` single-call
premises are GONE — calls are a positional `CallStream`, multi-call by construction; the
former named nonzero-write scope seam is GONE — `sim_sstore` now covers zero writes.)
The current headline's `DriveCorr`/`CallPreservesSelf`/`hpresent`/tie/`{T}`/`obs`
hypotheses are all gone: derived (R1–R10), definitional (`entryState`), or dead (the
phantom). -/
theorem lower_conforms {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
  -- The static well-formedness bundle the downstream ties/producer consume, RE-DERIVED from
  -- the IR-level well-formedness + the two scalar budgets (stage 1B bridge).
  have hwl := wellLowered_of_IRWellFormed hwf hcodeFits hstk
  have hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32 := Nat.le_of_lt hcodeFits
  -- Entry frame (from run adequacy) and the CALL-targets-code face of the seam.
  obtain ⟨fr₀, hbegin, _⟩ := runWithLog_drive hrun
  have hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  -- THE BLOCKER (Route-A, NOT a citable leaf): the coupled run-producer
  -- `runFrom_of_driveCorrLog` (the tracked WIP producer; target-architecture
  -- §5.3). It walks the `RecorderCoupled` invariant across the F2 recursion (that is what
  -- the R7 edges were gated for), instantiating the Layer-C sim lemmas ONLY at the coupled
  -- walk-frames, and yields — at the pinned oracles `realisedCall log recipient` /
  -- `entryState params` / `realisedGas log` — the IR `RunFrom`, the terminal world equation,
  -- AND the boundary walk `hrb`. It is NOT assembly over closed/citable leaves:
  --   • `lower_conforms_cyclic'` (the only in-tree run-producer) needs an UNCONDITIONAL
  --     all-frames `SimStmtStep`, which the reshaped `StmtTies'` cannot supply — its arm
  --     conclusions hold only under the load-bearing `RecorderCoupled` antecedent (§3), so
  --     the coupling-free path is exactly the vacuity the reshape exists to kill;
  --   • R6 `runs_atReachableBoundary`'s B2 side condition `(flatBytes prog).length < 2^32`
  --     is now DISCHARGED: it IS the `hcodeFits : codeFits prog` premise (that half of the
  --     old R6 blocker is closed by the 1B reshape). What still resists is producing `hrb`
  --     itself — the boundary walk comes bundled with the run through the coupled producer,
  --     not from `codeFits` alone; the coupled run-producer (below) remains open.
  -- Everything DOWNSTREAM of this producer call is real, axiom-clean assembly: `conforms_of_worldeq`
  -- (CLOSED, above) discharges the `Conforms` conjunct from the terminal world equation.
  obtain ⟨O, hcr, hworld, hrunfrom⟩ :=
    runFrom_of_driveCorrLog (prog := prog) (params := params) (log := log)
      (acc := acc) (fr₀ := fr₀)
      hcode hmod hself hgas hwl hrun hclean hseams hbegin hsize
  exact ⟨O, hrunfrom, conforms_of_worldeq hrun hbegin hcr hcc hworld⟩

/-- **R11-all — the exact-consumption strengthening**: the same flagship with the IR run
consuming the ENTIRE recorded gas stream (`RunFromAll`, leftover `[]`) — closes the
drop-the-suffix vacuity channel (§4). -/
theorem lower_conforms_exact {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFromAll prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
  have hwl := wellLowered_of_IRWellFormed hwf hcodeFits hstk
  have hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32 := Nat.le_of_lt hcodeFits
  -- This shell is aligned to the future exact producer: it must yield `RunFromAll` directly.
  -- Do not derive exactness from the plain producer; `runFromLeft_exists` only gives some
  -- leftover streams.
  obtain ⟨fr₀, hbegin, _⟩ := runWithLog_drive hrun
  have hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  obtain ⟨O, hcr, hworld, hrunfrom⟩ :
      ∃ O : Observable,
        (∀ fr', Runs fr₀ fr' → CreateResolves fr')
        ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
            ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
            ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
        ∧ RunFromAll prog (entryState params) (realisedGas log)
            (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O := sorry
  exact ⟨O, hrunfrom, conforms_of_worldeq hrun hbegin hcr hcc hworld⟩

/-- **The gas-free CO-FLAGSHIP** (target-architecture decision 2 — prove it FIRST). The
flagship restricted to `NoGasReads prog`: the gas suffix plays no role, so it needs no R1
(the riskiest obligation) — the de-risking checkpoint, and the theorem external readers
can compare to prior art (Verity/vyper-hol scope: no fork's verified semantics models gas
introspection at all). -/
theorem lower_conforms_gasfree {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hng : NoGasReads prog)
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog)
    (hcodeFits : codeFits prog)
    (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O := by
  have hwl := wellLowered_of_IRWellFormed hwf hcodeFits hstk
  have hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32 := Nat.le_of_lt hcodeFits
  -- The gas-free restriction (`hng : NoGasReads prog`) avoids R1 (no gas arm fires) and,
  -- via `realisedGas_nil_of_noGasReads`, makes the RunFrom trace empty — but it does NOT
  -- avoid the coupled-driver blocker: the sload/sstore/call arms still need the coupling.
  -- So the shell is identical to R11's; `hng` de-risks the driver internals, not the shell.
  obtain ⟨fr₀, hbegin, _⟩ := runWithLog_drive hrun
  have hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  obtain ⟨O, hcr, hworld, hrunfrom⟩ :=
    runFrom_of_driveCorrLog (prog := prog) (params := params) (log := log)
      (acc := acc) (fr₀ := fr₀)
      hcode hmod hself hgas hwl hrun hclean hseams hbegin hsize
  exact ⟨O, hrunfrom, conforms_of_worldeq hrun hbegin hcr hcc hworld⟩

/-! ### The co-flagship companion's support — the recorder's gas gate never fires

`driveLog` records a gas word only at an EMPTY-stack (top-level) frame decoding to `GAS`
(`isGasOp fr && stack.isEmpty`, `Spec/Recorder.lean`). For `NoGasReads prog` the lowered
code contains no reachable `GAS` head (`Lir.reachable_boundary_noGasByte`, the `NoGasOp`
alignment tower in `Decode/BoundaryReach.lean` §5), so it suffices to thread the R6
boundary invariant (`AtReachableBoundaryVJ`) along `driveLog`'s own recursion: at top level
by the ordinary-step edge, across descents by remembering — for the BOTTOM pending only,
the one whose resume re-empties the stack — that any delivered result resumes at a
boundary (the resume-keyed halves of the R6 CALL/CREATE edges: `driveLog` descents carry
no `CallReturns`/`CreateReturns` bundle, so the edge is re-keyed on
`stepFrame … = .needsCall`/`.needsCreate` + the resume equation, exactly the components
the geometry consumes). -/

/-- A frame at a reachable in-range boundary of a gas-read-free `lower prog` does not
decode to `GAS`: the recorder's gas gate is `false` there. -/
private theorem isGasOp_false_of_atReachableBoundary {prog : Program} {fr : Frame}
    (hng : NoGasReads prog) (hrb : AtReachableBoundary prog fr) :
    isGasOp fr = false := by
  obtain ⟨b, hcode, hpc, hreach, hin, hbnd⟩ := hrb
  obtain ⟨byte, hget, hne⟩ :=
    Lir.reachable_boundary_noGasByte prog (fun L bl hb => hng L bl hb) b hreach hin
  obtain ⟨arg, hdec⟩ := Lir.decode_of_loweringByte (prog := prog) hbnd hget
  have hgetD : (Evm.decode fr.exec.executionEnv.code fr.exec.pc
      |>.getD (Operation.STOP, .none)).1 = Evm.parseInstr byte := by
    simp [hcode, hpc, hdec]
  simp only [isGasOp, hgetD]
  exact beq_eq_false_iff_ne.mpr hne

/-- **Resume half of the R6 CALL edge**, keyed on `driveLog`'s own components: a suspended
CALL parent (`stepFrame fr = .needsCall cp pending` at a boundary frame) resumes — under ANY
delivered child result — at the next reachable in-range boundary. `atReachableBoundaryVJ_call`
minus the `CallReturns` drive components (which its geometry never consumes). -/
private theorem atReachableBoundaryVJ_resume_call {prog : Lir.Program} {fr rf : Frame}
    {cp : CallParams} {pending : PendingCall} {res : CallResult}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (hncall : stepFrame fr = .needsCall cp pending)
    (hrf : rf = resumeAfterCall res pending)
    (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog rf := by
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, hvj⟩ := hinv
  obtain ⟨byte, hget, hop⟩ := Lir.reachable_boundary_loweringByte prog b hreach hin
  obtain ⟨hopCall, hppc, hpvj⟩ :=
    Lir.stepFrame_needsCall_lowering_site_inv hcode hpc hbnd hget hop hncall
  have hInR : b + 1 < (Lir.flatBytes prog).length := by
    have hlt := Lir.nextInstrPos_lt_flatBytes_of_cursor (Lir.flatBytes_cursor_cases hin)
      hreach hget (by rw [hopCall]; simp) (by rw [hopCall]; simp) (by rw [hopCall]; simp)
    rw [hopCall] at hlt
    simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hlt
  have hrenv : rf.exec.executionEnv = pending.frame.exec.executionEnv := by
    rw [hrf]; rfl
  have hrcode : rf.exec.executionEnv.code = Lir.lower prog := by
    rw [hrenv, (Evm.stepFrame_needsCall_inv hncall).2.2, hcode]
  have hrvj : rf.validJumps = validJumpDests (Lir.lower prog) 0 := by
    rw [hrf, show (Evm.resumeAfterCall res pending).validJumps
          = pending.frame.validJumps from rfl, hpvj, hvj]
  have hrpc : rf.exec.pc = pending.frame.exec.pc + 1 := by
    rw [hrf]; rfl
  refine ⟨⟨b + 1, hrcode, ?_, ?_, hInR, lt_of_lt_of_le hInR hsize⟩, hrvj⟩
  · rw [hrpc, hppc, hpc]
    exact Lir.ofNat_add' b 1
  · have hr := Lir.reachesBoundary_nextInstr hreach hget
    rw [hopCall] at hr
    have hnn : Evm.nextInstrPosNat b Operation.CALL = b + 1 := by
      simp [Evm.nextInstrPosNat, Evm.pushArgWidth]
    rwa [hnn] at hr

/-- **Resume half of the R6 CREATE edge** (`atReachableBoundaryVJ_create` minus the drive
component): a suspended CREATE parent successfully resuming under ANY delivered child
result lands at the next reachable in-range boundary. -/
private theorem atReachableBoundaryVJ_resume_create {prog : Lir.Program} {fr rf : Frame}
    {cp : CreateParams} {pending : PendingCreate} {res : FrameResult}
    (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32)
    (hncreate : stepFrame fr = .needsCreate cp pending)
    (hrf : Evm.resumeAfterCreate res.toCreateResult pending = .ok rf)
    (hinv : AtReachableBoundaryVJ prog fr) :
    AtReachableBoundaryVJ prog rf := by
  obtain ⟨⟨b, hcode, hpc, hreach, hin, hbnd⟩, hvj⟩ := hinv
  obtain ⟨byte, hget, hop⟩ := Lir.reachable_boundary_loweringByte prog b hreach hin
  obtain ⟨hopCreate, hppc, hpvj⟩ :=
    Lir.stepFrame_needsCreate_lowering_site_inv hcode hpc hbnd hget hop hncreate
  have hInR : b + 1 < (Lir.flatBytes prog).length := by
    have hnstop : Evm.parseInstr byte ≠ .STOP := by
      rcases hopCreate with h | h <;> rw [h] <;> simp
    have hnreturn : Evm.parseInstr byte ≠ .RETURN := by
      rcases hopCreate with h | h <;> rw [h] <;> simp
    have hnjump : Evm.parseInstr byte ≠ .JUMP := by
      rcases hopCreate with h | h <;> rw [h] <;> simp
    have hlt := Lir.nextInstrPos_lt_flatBytes_of_cursor (Lir.flatBytes_cursor_cases hin)
      hreach hget hnstop hnreturn hnjump
    rcases hopCreate with hcr | hcr2
    · rw [hcr] at hlt
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hlt
    · rw [hcr2] at hlt
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hlt
  have hrenv : rf.exec.executionEnv = pending.frame.exec.executionEnv :=
    resumeAfterCreate_execEnv res pending rf hrf
  have hrcode : rf.exec.executionEnv.code = Lir.lower prog := by
    rw [hrenv, (Evm.stepFrame_needsCreate_inv hncreate).2.2.2, hcode]
  have hrvj : rf.validJumps = validJumpDests (Lir.lower prog) 0 := by
    rw [resumeAfterCreate_validJumps res pending rf hrf, hpvj, hvj]
  have hrpc : rf.exec.pc = pending.frame.exec.pc + 1 :=
    resumeAfterCreate_pc res pending rf hrf
  refine ⟨⟨b + 1, hrcode, ?_, ?_, hInR, lt_of_lt_of_le hInR hsize⟩, hrvj⟩
  · rw [hrpc, hppc, hpc]
    exact Lir.ofNat_add' b 1
  · have hr := Lir.reachesBoundary_nextInstr hreach hget
    rcases hopCreate with hcr | hcr2
    · rw [hcr] at hr
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hr
    · rw [hcr2] at hr
      simpa [Evm.nextInstrPosNat, Evm.pushArgWidth] using hr

/-- **B1 from `WellLowered`**: the CFG-closure's `entry_present` forces a non-empty block
array (the R6 entry seed's side condition). -/
private theorem blocks_pos_of_wellLowered {prog : Program} (hwl : WellLowered prog) :
    0 < prog.blocks.size := by
  obtain ⟨b, hb⟩ := hwl.closed.entry_present
  have hb' : prog.blocks[prog.entry.idx]? = some b := hb
  obtain ⟨h, _⟩ := Array.getElem?_eq_some_iff.mp hb'
  omega

/-- **B2 from `WellLowered`**: the lowered byte stream fits the 32-bit pc space. The flat
stream ends exactly at the LAST block's emitted terminator end, and every terminator kind
carries a `WellLowered` pc bound covering its own emitted bytes (`bound_stop`/`bound_jump`/
`bound_branch`/`retEpilogueBound`). -/
private theorem flatBytes_length_le_of_wellLowered {prog : Program}
    (hwl : WellLowered prog) : (Lir.flatBytes prog).length ≤ 2 ^ 32 := by
  rcases Nat.eq_zero_or_pos prog.blocks.size with hsz | hsz
  · have hnil : prog.blocks.toList = [] :=
      List.length_eq_zero_iff.mp (by rw [Array.length_toList]; exact hsz)
    unfold Lir.flatBytes
    rw [hnil]
    simp
  · have hi : prog.blocks.size - 1 < prog.blocks.toList.length := by
      rw [Array.length_toList]; omega
    set L : Label := ⟨prog.blocks.size - 1⟩ with hL
    set blk := prog.blocks.toList[prog.blocks.size - 1] with hblk
    have hb : prog.blocks.toList[L.idx]? = some blk := by
      rw [hL]
      exact List.getElem?_eq_getElem hi
    have hsplit := Lir.flatBytes_block_split prog L blk hb
    have hdrop : prog.blocks.toList.drop (L.idx + 1) = [] := by
      apply List.drop_eq_nil_of_le
      rw [Array.length_toList]
      show prog.blocks.size ≤ prog.blocks.size - 1 + 1
      omega
    rw [hdrop, List.flatMap_nil, List.append_nil] at hsplit
    have hbAt : blockAt prog L = some blk := by
      show prog.blocks[L.idx]? = some blk
      rw [← Array.getElem?_toList]
      exact hb
    have hlen : (Lir.flatBytes prog).length
        = Lir.termOf prog L
          + (Lir.emitTerm (Lir.matCache prog)
              (Lir.offsetTable (Lir.matCache prog) (Lir.defsOf prog) prog.blocks)
              blk.term).length := by
      rw [hsplit, List.length_append, List.length_cons,
        Lir.flatBytes_block_offset prog L, Lir.termOf_eq_anchor prog L blk hb]
      unfold Lir.emitBlockBody
      rw [List.length_append]
      omega
    have h33 : ∀ w : Lir.Word, (Lir.emitImm w).length = 33 := fun w => by
      simp [Lir.emitImm, Lir.wordBytesBE]
    have h5 : ∀ off : Nat, (Lir.emitDest off).length = 5 := fun off => by
      simp [Lir.emitDest, Lir.offsetBytesBE]
    cases hterm : blk.term with
    | ret t =>
        rw [hterm] at hlen
        simp only [Lir.emitTerm, List.length_append, List.length_cons, List.length_nil,
          h33] at hlen
        have hbound := hwl.retEpilogueBound L blk t hbAt hterm
        omega
    | stop =>
        rw [hterm] at hlen
        simp only [Lir.emitTerm, List.length_cons, List.length_nil] at hlen
        have hbound := hwl.wf.bound_stop L blk hb hterm
        omega
    | jump dst =>
        rw [hterm] at hlen
        simp only [Lir.emitTerm, List.length_append, List.length_cons, List.length_nil,
          h5] at hlen
        have hbound := (hwl.wf.bound_jump L blk dst hb hterm).1
        omega
    | branch cond thenL elseL =>
        rw [hterm] at hlen
        simp only [Lir.emitTerm, List.length_append, List.length_cons, List.length_nil,
          h5] at hlen
        have hbound := (hwl.wf.bound_branch L blk cond thenL elseL hb hterm).1
        omega

/-- The gas-gate walk invariant threaded along `driveLog`'s recursion: at top level (empty
pending stack) the current frame sits at a reachable in-range boundary; below top level —
whatever result the descended child delivers — the BOTTOM pending's resume lands back at
one. Only the bottom matters: the gas gate is `stack.isEmpty`-guarded, so no gas event can
fire before the stack re-empties, which happens exactly through the bottom resume. -/
private def GasWalkInv (prog : Program) (stack : List Pending)
    (state : Frame ⊕ FrameResult) : Prop :=
  (stack = [] → ∀ fr, state = .inl fr → AtReachableBoundaryVJ prog fr)
  ∧ (∀ p, stack.getLast? = some p →
      ∀ (res : FrameResult) (parent : Frame), p.resume res = .ok parent →
        AtReachableBoundaryVJ prog parent)

/-- Pushing a pending whose (top-level-only) resume obligation is discharged preserves the
walk invariant — the bottom of the grown stack is the old bottom (or the new pending, at a
top-level descent). -/
private theorem gasWalkInv_push {prog : Program} {stack : List Pending}
    {state : Frame ⊕ FrameResult}
    (hinv : GasWalkInv prog stack state) (p : Pending)
    (hp : stack = [] → ∀ (res : FrameResult) (parent : Frame),
        p.resume res = .ok parent → AtReachableBoundaryVJ prog parent) :
    ∀ state' : Frame ⊕ FrameResult, GasWalkInv prog (p :: stack) state' := by
  intro state'
  refine ⟨fun h => absurd h (by simp), ?_⟩
  intro q hq res parent hres
  cases stack with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hq
      subst hq
      exact hp rfl res parent hres
  | cons a rest =>
      rw [List.getLast?_cons_cons] at hq
      exact hinv.2 q hq res parent hres

/-- **The recorder's gas stream is frozen along a gas-read-free walk**: under the walk
invariant, `driveLog` returns its gas accumulator untouched. Fuel induction,
branch-for-branch as `driveLog_acc_hom`; the boundary invariant is threaded by the R6
ordinary-step edge (`atReachableBoundaryVJ_step`) and the resume-keyed CALL/CREATE edges
above; at every top-level `.next` step the gas gate is dead
(`isGasOp_false_of_atReachableBoundary`). -/
private theorem driveLog_gas_of_noGasReads {prog : Program}
    (hng : NoGasReads prog) (hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32) :
    ∀ (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (g0 : List Word) (s0 : List Nat) (c0 : List CallRecord) (d0 : List CreateRecord)
      (r : FrameResult) (gas : List Word) (sloads : List Nat)
      (calls : List CallRecord) (creates : List CreateRecord),
      GasWalkInv prog stack state →
      driveLog fuel stack state g0 s0 c0 d0 = .ok (r, gas, sloads, calls, creates) →
      gas = g0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack state g0 s0 c0 d0 r gas sloads calls creates _ hdl
      simp [driveLog] at hdl
  | succ n ih =>
      intro stack state g0 s0 c0 d0 r gas sloads calls creates hinv hdl
      unfold driveLog at hdl
      cases state with
      | inr result =>
          cases stack with
          | nil =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hdl
              exact hdl.2.1.symm
          | cons pending rest =>
              dsimp only at hdl
              cases hres : pending.resume result with
              | ok parent =>
                  rw [hres] at hdl
                  refine ih rest (.inl parent) g0 s0 _ _ r gas sloads calls creates ?_ hdl
                  cases rest with
                  | nil =>
                      refine ⟨fun _ fr hfr => ?_, fun p hp => by simp at hp⟩
                      rw [← (Sum.inl.injEq _ _).mp hfr]
                      exact hinv.2 pending (by simp) result parent hres
                  | cons q rest' =>
                      refine ⟨fun h => absurd h (by simp), fun p hp => hinv.2 p ?_⟩
                      rw [List.getLast?_cons_cons]
                      exact hp
              | error e =>
                  rw [hres] at hdl
                  refine ih rest (.inr (endFrame pending.frame (.exception e))) g0 s0 _ _
                    r gas sloads calls creates ?_ hdl
                  cases rest with
                  | nil =>
                      exact ⟨fun _ fr hfr => by simp at hfr, fun p hp => by simp at hp⟩
                  | cons q rest' =>
                      refine ⟨fun h => absurd h (by simp), fun p hp => hinv.2 p ?_⟩
                      rw [List.getLast?_cons_cons]
                      exact hp
      | inl current =>
          dsimp only at hdl
          cases hstep : stepFrame current with
          | next exec =>
              rw [hstep] at hdl
              dsimp only at hdl
              cases stack with
              | nil =>
                  have hb : AtReachableBoundaryVJ prog current := hinv.1 rfl current rfl
                  have hnext : GasWalkInv prog [] (.inl { current with exec := exec }) := by
                    refine ⟨fun _ fr hfr => ?_, fun p hp => by simp at hp⟩
                    rw [← (Sum.inl.injEq _ _).mp hfr]
                    exact atReachableBoundaryVJ_step hsize (stepsTo_of_next hstep) hb
                  split at hdl
                  · rename_i h
                    rw [isGasOp_false_of_atReachableBoundary hng hb.1] at h
                    simp at h
                  · split at hdl
                    · exact ih [] (.inl { current with exec := exec }) g0
                        (s0 ++ [sloadWarmthOf current]) c0 d0 r gas sloads calls creates
                        hnext hdl
                    · exact ih [] (.inl { current with exec := exec }) g0 s0 c0 d0
                        r gas sloads calls creates hnext hdl
              | cons p rest =>
                  have hcons : GasWalkInv prog (p :: rest)
                      (.inl { current with exec := exec }) :=
                    ⟨fun h => absurd h (by simp), hinv.2⟩
                  split at hdl
                  · rename_i h; simp at h
                  · split at hdl
                    · rename_i h; simp at h
                    · exact ih (p :: rest) (.inl { current with exec := exec }) g0 s0 c0 d0
                        r gas sloads calls creates hcons hdl
          | halted halt =>
              rw [hstep] at hdl
              dsimp only at hdl
              refine ih stack (.inr (endFrame current halt)) g0 s0 c0 d0
                r gas sloads calls creates ⟨fun _ fr hfr => by simp at hfr, hinv.2⟩ hdl
          | needsCall cp pending =>
              rw [hstep] at hdl
              dsimp only at hdl
              have hpush := gasWalkInv_push hinv (.call pending) (fun hnil res parent hres => by
                have hpar : resumeAfterCall res.toCallResult pending = parent := by
                  simpa [Pending.resume] using hres
                subst hnil
                exact atReachableBoundaryVJ_resume_call hsize hstep hpar.symm
                  (hinv.1 rfl current rfl))
              cases hbc : beginCall cp with
              | inl child =>
                  rw [hbc] at hdl
                  dsimp only at hdl
                  exact ih (.call pending :: stack) (.inl child) g0 s0 c0 d0
                    r gas sloads calls creates (hpush _) hdl
              | inr res =>
                  rw [hbc] at hdl
                  dsimp only at hdl
                  exact ih (.call pending :: stack) (.inr (.call res)) g0 s0 c0 d0
                    r gas sloads calls creates (hpush _) hdl
          | needsCreate cp pending =>
              rw [hstep] at hdl
              dsimp only at hdl
              have hpush := gasWalkInv_push hinv (.create pending)
                (fun hnil res parent hres => by
                  have hpar : Evm.resumeAfterCreate res.toCreateResult pending = .ok parent := by
                    simpa [Pending.resume] using hres
                  subst hnil
                  exact atReachableBoundaryVJ_resume_create hsize hstep hpar
                    (hinv.1 rfl current rfl))
              exact ih (.create pending :: stack) (.inl (beginCreate cp)) g0 s0 c0 d0
                r gas sloads calls creates (hpush _) hdl

/-- Co-flagship companion: a gas-read-free program's recorded gas stream is empty (the
recorder's GAS gate never fires at a reachable top-level boundary — needs the R6-flavoured
boundary walk to know every reachable op is an emitted one). -/
theorem realisedGas_nil_of_noGasReads {prog : Program} {params : CallParams} {log : RunLog}
    (hcode : params.codeSource = .Code (lower prog))
    (hng : NoGasReads prog)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log) :
    realisedGas log = [] := by
  have hne : 0 < prog.blocks.size := blocks_pos_of_wellLowered hwl
  have hsize : (Lir.flatBytes prog).length ≤ 2 ^ 32 :=
    flatBytes_length_le_of_wellLowered hwl
  unfold runWithLog at hrun
  cases hbc : beginCall params with
  | inr res => rw [hbc] at hrun; simp at hrun
  | inl fr₀ =>
      rw [hbc] at hrun
      dsimp only at hrun
      cases hdl : driveLog (seedFuel params.gas) [] (.inl fr₀) [] [] [] [] with
      | error e => rw [hdl] at hrun; simp at hrun
      | ok val =>
          obtain ⟨r, gas, sloads, calls, creates⟩ := val
          rw [hdl] at hrun
          simp only [Option.some.injEq] at hrun
          subst hrun
          show gas = []
          refine driveLog_gas_of_noGasReads hng hsize (seedFuel params.gas) [] (.inl fr₀)
            [] [] [] [] r gas sloads calls creates
            ⟨fun _ fr hfr => ?_, fun p hp => by simp at hp⟩ hdl
          rw [← (Sum.inl.injEq _ _).mp hfr]
          exact atReachableBoundaryVJ_entry hbc hcode hne

/-- **R12a — the flagship's antecedent is TRUE somewhere** (the machine-checked
non-vacuity guard; HonestGasTie's replacement role). Some concrete top-level call params
run `lower exProg` cleanly with every flagship hypothesis satisfied.

**CLOSED.** `WitnessParams.lean` lands the literal witness `exParams` (gas `25000`,
tuned by a measured native probe: clean `.stop`, 179 gas left, 1 loop iteration —
re-measured against the current lowering, identical landscape) and the sorry-free
reduction `exProg_satisfies_hypotheses_of_checks` from exactly two decidable
`Bool` leaves; `WitnessChecks.lean` discharges both leaves IN-KERNEL (`exCheck_true`,
`entryCallsCodeOk_exParams`) via the segmented checked-twin evaluator
(`SegmentedEval.lean` + `CheckedStep.lean` — plain `decide` on the raw evaluators is
measured-infeasible: the padded byte-window path is stuck on the opaque
`System.Platform.getNumBits`, and the seed-fuel peel OOMs the kernel; the twin
quarantines both). THREE flagged kernel cranks (`decide +kernel`, `WitnessChecks.lean`)
are the leaves' entire computational content: the two heavy leaf evaluations
(~13s / 5.5 GB each) plus the cheap `seedFuel` arithmetic pin. The `#print axioms`
guard below is `#guard_msgs`-checked (build-enforced): the reported axioms are exactly
the standard trio — no `sorryAx`, no `ofReduceBool`. -/
theorem exProg_satisfies_hypotheses :
    ∃ (params : CallParams) (log : RunLog) (acc : Account),
      params.codeSource = .Code (lower exProg)
      ∧ params.canModifyState = true
      ∧ params.accounts.find? params.recipient = some acc
      ∧ GasConstants.Gjumpdest ≤ params.gas.toNat
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ log.clean
      ∧ PrecompileAssumptions exProg params :=
  exProg_satisfies_hypotheses_of_checks exCheck_true entryCallsCodeOk_exParams

/--
info: 'Lir.V2.exProg_satisfies_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exProg_satisfies_hypotheses

/-- **R12b — end-to-end at the witness**: `lower_conforms` instantiated at `exProg`
(gas-read + sload + nonzero-sstore + call + loop, all at once — the verifereum
`deploy_result_correct`-shaped concrete instance no fork has for this feature set). -/
theorem exProg_nonvacuity :
    ∃ (params : CallParams) (log : RunLog),
      params.codeSource = .Code (lower exProg)
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ ∃ O : Observable,
          RunFrom exProg (entryState params) (realisedGas log)
            (realisedCall log params.recipient) (realisedCreate log params.recipient) exProg.entry O
          ∧ Conforms params.recipient log O := by
  -- The witness params/log come from R12a (`exProg_satisfies_hypotheses` — CLOSED:
  -- reduced in `WitnessParams.lean` to two decidable leaves, both kernel-certified in
  -- `WitnessChecks.lean`); the inner existential is EXACTLY R11's (`lower_conforms`)
  -- conclusion at `prog := exProg`. R12a carries every flagship premise except the closed
  -- static well-formedness bundle, now reshaped to `irWellFormed_exProg` + the two scalar
  -- budgets `codeFits_exProg`/`stackFits_exProg` (all `decide`/`rfl` on the concrete
  -- program), which we supply directly (same module). Axiom-clean once R11 lands (the
  -- only remaining `sorryAx` source in this chain). No single-call premise — calls are a
  -- positional `CallStream`.
  obtain ⟨params, log, _acc, hcode, hmod, hself, hgas, hrun, hclean, hseams⟩ :=
    exProg_satisfies_hypotheses
  refine ⟨params, log, hcode, hrun, ?_⟩
  exact lower_conforms hcode hmod hself hgas
    irWellFormed_exProg codeFits_exProg stackFits_exProg hrun hclean hseams

/-! ## §7 — audit note

NO `#print axioms` guards live here for the OPEN obligations BY DESIGN: every sorry'd
declaration carries `sorryAx` until its obligation lands, so axiom guards would only pin
the debt's existence. Obligations CLOSED inside this WIP lib (currently R12a,
`exProg_satisfies_hypotheses`) DO carry a `#guard_msgs`-checked `#print axioms` guard at
their declaration — build-enforced, pinning the closed subtree's axiom-cleanliness. The
default-target audit net (`Audit.lean`, Track A) must NOT cover this WIP lib; the guards
migrate there obligation-by-obligation as the remaining sorries are discharged. -/

end Lir.V2
