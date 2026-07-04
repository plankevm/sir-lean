import LirLean.V2.Drive.Headline
import LirLean.Assembly.Acyclic
import LirLean.Decode.BoundaryReach
import LirLean.V2.Realisability.Witness

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
      StmtTies' prog sloadChg log params.recipient L b := sorry

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
theorem conforms_of_worldeq {prog : Lir.Program} {params : CallParams} {fr₀ : Frame}
    {log : RunLog} {self : AccountAddress} {O : Observable}
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hbegin : beginCall params = .inl fr₀)
    (hrb : ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr')
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
      (lower_modellable hrb hcc)
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
feed the recorded gas reads and call records into the executable IR semantics; the IR run
exists at the PINNED streams (`realisedGas log` / `realisedCall log recipient`, from the
PINNED entry state) and produces the same observable world.

Hypothesis ledger (the honest surface, nothing else): two definitional pins
(`hcode`/`hmod`), two decidable entry facts (`hself`/`hgas`), one static checkable bundle
(`hwl`), ONE decidable scope premise (`hclean`), ONE runtime premise (`hrun`),
and one two-field honest seam structure (`hseams`). (The former `hsingle`/`hone` single-call
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
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) ([] : CreateStream) prog.entry O
      ∧ Conforms params.recipient log O := by
  -- Entry frame (from run adequacy) and the CALL-targets-code face of the seam.
  obtain ⟨fr₀, hbegin, _⟩ := runWithLog_drive hrun
  have hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  -- THE BLOCKER (Route-A, NOT a citable leaf): the coupled run-producer
  -- `runFrom_of_driveCorrLog` (does not exist anywhere in the tree; target-architecture
  -- §5.3). It walks the `RecorderCoupled` invariant across the F2 recursion (that is what
  -- the R7 edges were gated for), instantiating the Layer-C sim lemmas ONLY at the coupled
  -- walk-frames, and yields — at the pinned oracles `realisedCall log recipient` /
  -- `entryState params` / `realisedGas log` — the IR `RunFrom`, the terminal world equation,
  -- AND the boundary walk `hrb`. It is NOT assembly over closed/citable leaves:
  --   • `lower_conforms_cyclic'` (the only in-tree run-producer) needs an UNCONDITIONAL
  --     all-frames `SimStmtStep`, which the reshaped `StmtTies'` cannot supply — its arm
  --     conclusions hold only under the load-bearing `RecorderCoupled` antecedent (§3), so
  --     the coupling-free path is exactly the vacuity the reshape exists to kill;
  --   • R6 `runs_atReachableBoundary` cannot be cited to produce `hrb` on its own: its B2
  --     side condition `(flatBytes prog).length ≤ 2^32` has no producer from `hwl` (no
  --     `WellFormedLowered` field asserts it directly — only per-cursor bounds).
  -- Everything DOWNSTREAM of this `obtain` is real, axiom-clean assembly: `conforms_of_worldeq`
  -- (CLOSED, above) discharges the `Conforms` conjunct from the terminal world equation.
  obtain ⟨O, hrb, hworld, hrunfrom⟩ :
      ∃ O : Observable,
        (∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr')
        ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
            ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
            ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
        ∧ RunFrom prog (entryState params) (realisedGas log)
            (realisedCall log params.recipient) ([] : CreateStream) prog.entry O := sorry
  exact ⟨O, hrunfrom, conforms_of_worldeq hrun hbegin hrb hcc hworld⟩

/-- **R11-all — the exact-consumption strengthening**: the same flagship with the IR run
consuming the ENTIRE recorded gas stream (`RunFromAll`, leftover `[]`) — closes the
drop-the-suffix vacuity channel (§4). -/
theorem lower_conforms_exact {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFromAll prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) ([] : CreateStream) prog.entry O
      ∧ Conforms params.recipient log O := by
  -- As R11, but the packaged blocker yields the exact-consumption `RunFromAll` (BOTH leftovers
  -- `[]`). The coupled driver produces it directly: its walk consumes the WHOLE recorded gas
  -- AND call suffix by construction of `RecorderCoupled.restart`, so both leftovers are `[]` —
  -- it cannot be bolted on afterward via `runFromLeft_exists`, which only produces SOME leftover.
  obtain ⟨fr₀, hbegin, _⟩ := runWithLog_drive hrun
  have hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  obtain ⟨O, hrb, hworld, hrunfrom⟩ :
      ∃ O : Observable,
        (∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr')
        ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
            ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
            ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
        ∧ RunFromAll prog (entryState params) (realisedGas log)
            (realisedCall log params.recipient) ([] : CreateStream) prog.entry O := sorry
  exact ⟨O, hrunfrom, conforms_of_worldeq hrun hbegin hrb hcc hworld⟩

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
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) ([] : CreateStream) prog.entry O
      ∧ Conforms params.recipient log O := by
  -- The gas-free restriction (`hng : NoGasReads prog`) avoids R1 (no gas arm fires) and,
  -- via `realisedGas_nil_of_noGasReads`, makes the RunFrom trace empty — but it does NOT
  -- avoid the coupled-driver blocker: the sload/sstore/call arms still need the coupling.
  -- So the shell is identical to R11's; `hng` de-risks the driver internals, not the shell.
  obtain ⟨fr₀, hbegin, _⟩ := runWithLog_drive hrun
  have hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr' :=
    fun fr' hr => hseams.callsCode fr' ⟨fr₀, hbegin, hr⟩
  obtain ⟨O, hrb, hworld, hrunfrom⟩ :
      ∃ O : Observable,
        (∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr')
        ∧ (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
            ∧ (observe params.recipient (endFrame last haltSig)).world = O.world
            ∧ (observe params.recipient (endFrame last haltSig)).result = O.result)
        ∧ RunFrom prog (entryState params) (realisedGas log)
            (realisedCall log params.recipient) ([] : CreateStream) prog.entry O := sorry
  exact ⟨O, hrunfrom, conforms_of_worldeq hrun hbegin hrb hcc hworld⟩

/-- Co-flagship companion: a gas-read-free program's recorded gas stream is empty (the
recorder's GAS gate never fires at a reachable top-level boundary — needs the R6-flavoured
boundary walk to know every reachable op is an emitted one). -/
theorem realisedGas_nil_of_noGasReads {prog : Program} {params : CallParams} {log : RunLog}
    (hcode : params.codeSource = .Code (lower prog))
    (hng : NoGasReads prog)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log) :
    realisedGas log = [] := sorry

/-- **R12a — the flagship's antecedent is TRUE somewhere** (the machine-checked
non-vacuity guard; HonestGasTie's replacement role). Some concrete top-level call params
run `lower exProg` cleanly with every flagship hypothesis satisfied. The `params` witness
is deliberately EXISTENTIAL: a literal `CallParams` needs BlockHeader/ProcessedBlocks
plumbing that belongs to the R12 grind, not the spec. -/
theorem exProg_satisfies_hypotheses :
    ∃ (params : CallParams) (log : RunLog) (acc : Account),
      params.codeSource = .Code (lower exProg)
      ∧ params.canModifyState = true
      ∧ params.accounts.find? params.recipient = some acc
      ∧ GasConstants.Gjumpdest ≤ params.gas.toNat
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ log.clean
      ∧ PrecompileAssumptions exProg params := sorry

/-- **R12b — end-to-end at the witness**: `lower_conforms` instantiated at `exProg`
(gas-read + sload + nonzero-sstore + call + loop, all at once — the verifereum
`deploy_result_correct`-shaped concrete instance no fork has for this feature set). -/
theorem exProg_nonvacuity :
    ∃ (params : CallParams) (log : RunLog),
      params.codeSource = .Code (lower exProg)
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ ∃ O : Observable,
          RunFrom exProg (entryState params) (realisedGas log)
            (realisedCall log params.recipient) ([] : CreateStream) exProg.entry O
          ∧ Conforms params.recipient log O := by
  -- The witness params/log come from R12a (`exProg_satisfies_hypotheses`); the inner
  -- existential is EXACTLY R11's (`lower_conforms`) conclusion at `prog := exProg`.
  -- R12a carries every flagship premise except the closed static `wellLowered_exProg`, which we
  -- supply directly (same module). Green now (R12a is a skeleton leaf); axiom-clean once R11 +
  -- R12a land. No single-call premise — calls are a positional `CallStream`.
  obtain ⟨params, log, _acc, hcode, hmod, hself, hgas, hrun, hclean, hseams⟩ :=
    exProg_satisfies_hypotheses
  refine ⟨params, log, hcode, hrun, ?_⟩
  exact lower_conforms hcode hmod hself hgas
    wellLowered_exProg hrun hclean hseams

/-! ## §7 — audit note

NO `#print axioms` guards live here BY DESIGN: every sorry'd declaration carries `sorryAx`
until its obligation lands, so axiom guards would only pin the debt's existence. The
default-target audit net (`Audit.lean`, Track A) must NOT cover this WIP lib; the
guards migrate there obligation-by-obligation as the sorries are discharged. -/

end Lir.V2
