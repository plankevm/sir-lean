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
`DriveCorrLog` at `prog.entry` on the whole recorder suffixes. Fires: `entry_corr` (`Corr`,
with `StorageAgree` from the definitional `entryState`), `cleanHalts_of_runWithLog` (clean-halt
scope), `ClosedCFG.entry_present` (presence), `selfPresent_codeFrame` + `selfPresent_runs`
(self-presence to `fr₀`), the `codeFrame` address/kind pins, and `recorderCoupled_entry`
(coupling). Assembly, but the `entryState`↔`entry_corr` `StorageAgree` reconciliation and the
address/kind transport across `entry_corr`'s internal `Runs` need care. TRACTABILITY: now. -/
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
    ∃ st₀ : IRState, st₀ = entryState params
      ∧ DriveCorrLog prog sloadChg log params.recipient st₀ fr₀ prog.entry
          log.gas log.sloads log.calls := by
  sorry

/-! ## §2 — the per-statement COUPLED steps (the crux; reason (a))

One lemma per statement shape. Each takes the cursor statement, the `Corr` at `(L, pc)`, the
coupling `RecorderCoupled log fr …`, the clean-halt scope, the `StreamsAligned` fact, and the
matching `StmtTies'` arm output (produced by R10a `stmtTies'_of_runWithLog`), and produces the
`CoupledAdvance`. The IR `EvalStmt` is built from the aligned stream head; the bytecode `Runs`
from the Layer-C sim brick fired AT THE COUPLED FRAME; the coupling advance from the matching R7
edge. None of these factor through the unconditional `SimStmtStep`.

`sloadChg` is fixed to a chosen value once inside the walk (the sim bricks are `∀ sloadChg`;
the producer picks the canonical one). We leave it a parameter here. -/

/-- **P2-assignPure — the plain-assign coupled step** (neither `.gas` nor `.sload`). Fires
`StmtTies'` arm (1) (not-spilled + `StepScopedS` + post-state scoping + `MemRealises`), the
in-tree `sim_assign` (pure) brick for the bytecode `Runs`, and `recorderCoupled_step_other`
(R7d) — no stream head consumed (`EvalStmt.assignPure`, all suffixes/streams unchanged). The
simplest arm; the sim brick and the R7d edge both already exist green. TRACTABILITY: now. -/
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
  sorry

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
  sorry

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
    ∀ fr', Runs fr₀ fr' → CreateResolves fr' := by
  sorry

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
