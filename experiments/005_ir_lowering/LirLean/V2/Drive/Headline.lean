import LirLean.V2.DriveSim
import LirLean.V2.Drive.CallPreservesSelf

/-!
# LirLean v2 — the `DriveCorrPlus` walk and the tie-supplied headlines (`Drive/Headline`)

§6–§10 of the former `V2/TieDischarge.lean` monolith (decl names and namespaces unchanged):

* **§6** — the strengthened boundary invariant `DriveCorrPlus` (the alignment + presence
  carrier over `DriveSim.lean`'s `DriveCorr`) and its entry construction.
* **§7** — the no-bridge VALUE channels of the `DriveCorrPlus` walk
  (`memRealises_setLocal_nonspilled`, `driveCorrPlus_assign_remat_memRealises`,
  `driveCorrPlus_sload_value`/`_world`).
* **§8 (L2.0g)** — the seedable GAS-alignment bricks (`FramesRun.snoc_seed`,
  `gasLogAligned_step_gas_seed`, `GasReach`).
* **§9** — the edge wrappers `driveCorrPlus_step_jump`/`_branch`.
* **§10** — the `DriveCorrPlus` recursion (`DriveStepPlus`, `driveStepPlus_of_block`,
  `runFrom_of_driveCorrPlus`) and the headlines `lower_conforms_cyclic_tiefree` /
  `lower_conforms_cyclic_assembled`.

**Honest status (audit 2026-07-02, `docs/target-architecture-2026-07-02.md`):** the
headlines are CONDITIONAL on supplied `StmtTies`/`TermTies` (via `WellFormedLowered` for
`_assembled`), which were shown unsatisfiable as supplied — the plan of record replaces this
surface with the Phase-3 flagship (`V2/RealisabilitySpec.lean`); these theorems remain the
green machinery that reshape starts from, not a conformance claim.

The value-channel discharges + `SelfPresent` live in `Drive/SelfPresent.lean`; the
`callPreservesSelf` chain in `Drive/CallPreservesSelf.lean`; the pure engine theory in
`LirLean/Engine/`.

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/


namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps
open Lir

/-! ## §6 — the strengthened boundary invariant `DriveCorrPlus` (the alignment + presence carrier)

The drive recursion `runFrom_of_driveCorr` (`DriveSim.lean`) threads `DriveCorr` (the `Corr`
boundary + the clean-halt measure) block-by-block. To discharge the §7 *selection* (the k-th cursor
value = the k-th recorded entry) and the SSTORE presence in the SAME walk, the boundary invariant
must additionally carry, at each block-entry frame:

* `selfPresent` — the self account is present (`SelfPresent fr`), the SSTORE presence world-invariant
  (§5), transportable across each block's materialise sub-runs (account map + self address preserved);
* `gasAligned` / `sloadAligned` — that the recorder's flat gas/sload accumulators *consumed so far*
  are aligned (`GasLogAligned` / `SloadLogAligned`) with the GAS/SLOAD witness frames the walk has
  visited, so the per-cursor read at the next GAS/SLOAD site is the matching recorded entry
  (`gasRealises_obs_of_witness` / `sloadRealises_charge_of_witness`).

`DriveCorrPlus` bundles exactly these onto `DriveCorr`. The accumulators-so-far are carried as
explicit parameters (`gasAcc`/`sloadAcc`) with their witness lists (`gasFrs`/`sloadFrs`), since the
block walk does not itself project the recorder — they are the prefix of `log.gas`/`log.sloads`
consumed up to this boundary.

**Entry satisfaction is proven** (`driveCorrPlus_entry`): at the entry frame the consumed prefixes
are empty (`gasLogAligned_nil`/`sloadLogAligned_nil`) and `SelfPresent` holds by
`selfPresent_codeFrame`. **Preservation through the block step is the standing obstacle**, for two
independent reasons reported at the foot of this module: (a) the alignment witnesses can only be
*selected* in the single-`obs` `Corr` model when the consumed gas prefix is constant
(`gasRealises_obs_of_witness`), which the multi-distinct-read general case violates; (b)
`SelfPresent`-forward across a block requires self-presence preservation along the *whole* `Runs`
segment (including the `Runs.call` resume), which is not yet a lemma. -/

/-- **The strengthened drive-boundary invariant.** `DriveCorr` (the `Corr` boundary + clean-halt
measure) augmented with the SSTORE presence world-invariant `SelfPresent fr` and the gas/sload
positional-alignment witnesses for the recorder prefixes consumed up to this boundary
(`GasLogAligned gasAcc gasFrs` / `SloadLogAligned sloadAcc sloadFrs`). The carrier the drive walk
would thread to discharge the §7 selection ties and the SSTORE presence in one recursion; the entry
frame satisfies it (`driveCorrPlus_entry`). -/
structure DriveCorrPlus (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) (L : Label)
    (gasAcc : List Word) (gasFrs : List Frame)
    (sloadAcc : List Nat) (sloadFrs : List Frame) : Prop where
  /-- The base `DriveCorr` boundary (the `Corr` cursor + the clean-halt measure). -/
  base : DriveCorr prog sloadChg obs st fr L
  /-- The SSTORE presence world-invariant: the self account is present in `fr`'s accounts. -/
  selfPresent : SelfPresent fr
  /-- The gas accumulator consumed so far is positionally aligned with the GAS witness frames. -/
  gasAligned : GasLogAligned gasAcc gasFrs
  /-- The sload accumulator consumed so far is positionally aligned with the SLOAD witness frames. -/
  sloadAligned : SloadLogAligned sloadAcc sloadFrs

/-- **Entry satisfaction of `DriveCorrPlus`.** At the entry frame (a `DriveCorr` boundary whose
frame is the call's `codeFrame` with the self account present), the strengthened invariant holds
with **empty** consumed prefixes: the gas/sload alignments are the seeds
(`gasLogAligned_nil`/`sloadLogAligned_nil`) and `SelfPresent` is `selfPresent_codeFrame`. This is the
base case of the (would-be) strengthened drive recursion — the alignment witnesses start empty and
the presence invariant starts established. -/
theorem driveCorrPlus_entry {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {params : Evm.CallParams} {code : ByteArray} {L : Label} {acc : Account}
    (hbase : DriveCorr prog sloadChg obs st (codeFrame params code) L)
    (hwf : params.accounts.find? params.recipient = some acc) :
    DriveCorrPlus prog sloadChg obs st (codeFrame params code) L [] [] [] [] where
  base := hbase
  selfPresent := selfPresent_codeFrame params code hwf
  gasAligned := gasLogAligned_nil
  sloadAligned := sloadLogAligned_nil

/-! ## §7 — the no-bridge VALUE channels of the `DriveCorrPlus` walk (C3 / Group B)

The centerpiece L2.0 statement-walk is decomposed by the architect into

  * the **structure** (`Runs` + `Corr` at the terminator + working-stack-nil), reused VERBATIM from
    `sim_stmts_block` consuming the per-statement bytecode simulation `SimStmtStep` (which internally
    re-establishes the stash/sstore/call ties S1/S5/S6 — the serialized spine, supplied here);
  * the **self-presence** edge, threaded by P3 (`selfPresent_runs_of_call`, supplied `CallPreservesSelf`);
  * the **alignment** witnesses, carried VERBATIM from the `DriveCorrPlus` boundary (the per-cursor
    structural extension `gasLogAligned_step_gas`/`sloadLogAligned_step_sload` is the deferred gas/sload
    structural walk, NOT tonight's preservation walk);
  * the **value channels** — the only genuinely-new, no-P3, no-trace↔recorder-bridge content tonight:
    **S7** (assign-remat `MemRealises` transport) and **S2** (the sload value tie). These are kept
    SEPARATE from the walk (see below).

We prove S7/S2 here as standalone cursor-LOCAL lemmas (a single `Corr` cursor + its `EvalStmt` step),
exactly the altitude `SimStmtStep`/`sim_assign` consume. They are functions of the per-cursor
`Corr`/`EvalStmt` ALONE, not of the run, so they are NOT bundled into the walk (doing
so would buy nothing): the downstream Route-4b assembly applies them per cursor directly (the indexed
form bound to the run's reached `(stpc, frpc)`, NOT the universal free-`ob` `StmtTies` predicate, which
ranges over all cursors and is unreconstructable from a single run).

**The two channels that STAY SUPPLIED tonight** (satisfiable, documented, NON-vacuous):
  * **S3 (gas positional value)** `stpc'.locals t = ofUInt64 (frpc.gas − Gbase)` — NOT a value-only
    have-block: it is the TRACE↔RECORDER bridge (`EvalStmt.assignGas` peels `ob` as the HEAD of the gas
    trace, while `aligned_read_eq_obs` gives the recorder's `gasAcc[i]`; tying them needs a NEW carried
    invariant `IR-trace-consumed = gasAcc` plus the gas-channel structural walk threading
    `gasFrs[i] = gasFrame frpc`). Supplied as `hgasval`; satisfiable — supplied via `SimStmtStep` (the `StmtTies` gas conjunct), NOT discharged by any carried alignment;
    the `Plus` invariant threads ONLY `SelfPresent`, the gas/sload alignment witnesses being carried
    VERBATIM. Inhabited by any top-level GAS read.
  * **S1/S5/S6** — folded inside the supplied `SimStmtStep` (the serialized post-P3 spine).
  * **S4 (gas runtime envelopes)** — the lower-bound envelopes need the clean-halt FORWARD split
    (`cleanHalts_forward` to the cursor, then the GAS op runs), not pure descent; supplied alongside S3.
-/

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S7 core (NEW): `MemRealises` survives a non-spilled `setLocal`.** Binding a tmp `t` that is NOT
spilled to a memory slot (`∀ n, defsOf prog t ≠ some (.slot n)`) leaves the memory value channel
intact: for every spilled `t'` with `(st.setLocal t w).locals t' = some v`, necessarily `t' ≠ t` (else
`t` would be spilled, contradicting `hns`), so `(st.setLocal t w).locals t' = st.locals t'` and the
coverage+readback at `t'`'s slot is the input `MemRealises`'s. The honest content of the assign-remat
channel: the frame `fr` is UNCHANGED by a rematerialised assign (its lowered emit is empty,
`Runs.refl`), only the IR state moves, so `MemRealises` transports by this `setLocal` stability. -/
theorem memRealises_setLocal_nonspilled {prog : Program} {st : V2.IRState} {fr : Frame}
    {t : Tmp} {w : Word}
    (h : MemRealises prog st fr) (hns : ∀ n, defsOf prog t ≠ some (.slot n)) :
    MemRealises prog (st.setLocal t w) fr := by
  intro t' slot v hdef hloc
  -- `t' ≠ t`: otherwise `t' = t` is spilled (`hdef` at the slot), contradicting `hns`.
  have hne : t' ≠ t := by
    rintro rfl
    exact hns slot hdef
  -- read the bound value back through `setLocal` of the distinct tmp `t`.
  have hloc' : st.locals t' = some v := by
    have : (st.setLocal t w).locals t' = st.locals t' := by
      show (if t' = t then some w else st.locals t') = st.locals t'
      rw [if_neg hne]
    rwa [this] at hloc
  exact h t' slot v hdef hloc'

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S7 (assign-remat value channel), cursor-local.** At a cursor holding a rematerialised assign
`assign t e` (target NOT spilled, `hns`) whose IR step is the non-gas `EvalStmt.assignPure` (so the
post-state is `st.setLocal t w`), the post-state realises the frame's memory: `MemRealises prog st' fr`.
The frame is the SAME `fr` the cursor's `Corr` carries (a rematerialised assign emits no bytes), so this
is `memRealises_setLocal_nonspilled` applied to `Corr.memAgree`. No recorder, no P3 — the genuine
no-bridge content of S7 (Route 4b indexed form). -/
theorem driveCorrPlus_assign_remat_memRealises {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {t : Tmp} {e : Expr} {L : Label}
    {pc : Nat} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hstep : EvalStmt prog o st T (.assign t e) st' T')
    (hne : e ≠ .gas)
    (hns : ∀ n, defsOf prog t ≠ some (.slot n)) :
    MemRealises prog st' fr := by
  -- invert the step: non-gas assign ⇒ `assignPure`, `st' = st.setLocal t w`.
  cases hstep with
  | assignPure _ _ =>
    exact memRealises_setLocal_nonspilled hcorr.memAgree hns
  | assignGas => exact absurd rfl hne

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S2 (sload value channel), cursor-local.** At a cursor holding `assign t (.sload k)` whose IR step
is `EvalStmt`, the IR genuinely binds a value: `∃ w, evalExpr st 0 (.sload k) = some w`. This is the
`hv` field of the `assignPure` the run already performed (`.sload k ≠ .gas`), echoing the run's own
successful IR step — NON-vacuous (the run is the witness that `k` is bound and `w = st.world key`). No
recorder, no P3. -/
theorem driveCorrPlus_sload_value {prog : Program} {o : V2.CallOracle}
    {st st' : V2.IRState} {T T' : Trace} {t k : Tmp}
    (hstep : EvalStmt prog o st T (.assign t (.sload k)) st' T') :
    ∃ w, V2.evalExpr st 0 (.sload k) = some w := by
  cases hstep with
  | assignPure _ hv => exact ⟨_, hv⟩

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S2 envelope: the sload key is bound, the value is the world read.** A sharper readout of the same
`assignPure`: the IR run's sload at this cursor binds `k`'s key and the loaded word is `st.world key` —
the value `MemRealises` will position at `t`'s slot. Non-vacuous (the run is its own witness). -/
theorem driveCorrPlus_sload_value_world {prog : Program} {o : V2.CallOracle}
    {st st' : V2.IRState} {T T' : Trace} {t k : Tmp}
    (hstep : EvalStmt prog o st T (.assign t (.sload k)) st' T') :
    ∃ key, st.locals k = some key ∧ V2.evalExpr st 0 (.sload k) = some (st.world key) := by
  cases hstep with
  | assignPure _ hv =>
    -- `evalExpr st 0 (.sload k) = (do let key ← st.locals k; pure (st.world key))`.
    -- `hv : evalExpr st 0 (.sload k) = some w` forces `st.locals k = some key` and `w = st.world key`.
    cases hk : st.locals k with
    | none =>
      exfalso
      simp [V2.evalExpr, hk] at hv
    | some key =>
      exact ⟨key, rfl, by simp [V2.evalExpr, hk]⟩

/-! ### L2.0g — the GAS-ADVANCING `DriveCorrPlus` statement-walk (S3 producer)

The L2.0 statement-walk is PRESERVATION-only: it black-boxes the per-cursor frames through
`sim_stmts_block`, so it cannot grow the gas witness list `gasFrs` — it carries the alignment
VERBATIM, leaving S3 (the gas positional VALUE) SUPPLIED. The GAS-advancing walk decls that PEELED each cursor to GROW the alignment have been REMOVED (audit:
dead producers off the headline path); the seedable per-cursor gas bricks below
(`FramesRun.snoc_seed`, `gasLogAligned_step_gas_seed`, `GasReach`, `GasCursorClass`) are RETAINED salvage — for the deferred SLOAD/gas advance.

The per-cursor dispatch is the classification hypothesis `GasCursorClass`: at each cursor the walk is
told whether the statement is `assign t .gas` (a GAS cursor, with the GAS-op decode + gas envelope +
the strictly-advancing `fr0 ≠ fr1` that lets `Runs.gas_cancel` factor the GAS head out) or NOT (the
no-record arm). This is the honest per-cursor input the architect's plan dispatches on; it is
satisfiable (a real lowered `assign t .gas` decodes to `GAS` at the segment head — `emitStmt_assign_slot`
puts `materialise .gas = [GAS]` first — and the GAS op strictly advances the pc) and NON-vacuous (the
GAS arm CONSUMES the supplied S4 lower bound to fire the brick, the non-GAS arm consumes nothing).

The threaded reachability invariant is `GasReach`: the witness tail `Runs`-reaches the current cursor
frame (vacuous at the empty seed, `Runs last fr0` once non-empty). The seedable gas snoc
`gasLogAligned_step_gas_seed` handles BOTH the first GAS cursor (empty `gasFrs`, `FramesRun []`-seed)
and the snoc case (non-empty, via `FramesRun.snoc`), so the walk needs no special first-cursor arm. -/

/-- **`FramesRun` extends on the right, SEEDABLE.** Unlike `FramesRun.snoc` (which needs a non-empty
list to supply `getLast?`), this admits the empty seed: appending `g` to `[]` gives `[g]`
(`FramesRun [g] = True`), and to a non-empty list reachable-from-its-last gives the snoc. The
hypothesis is `GasReach`-style: every `last` that is the list's `getLast?` reaches `g`. -/
theorem FramesRun.snoc_seed {frs : List Frame} {g : Frame}
    (hrun : FramesRun frs) (hreach : ∀ last, frs.getLast? = some last → Runs last g) :
    FramesRun (frs ++ [g]) := by
  cases frs with
  | nil => exact trivial
  | cons a tl =>
    -- a non-empty list has `getLast? = some last` for some `last` (`getLast?_isSome`).
    obtain ⟨last, hlast⟩ : ∃ last, (a :: tl).getLast? = some last := by
      cases h : (a :: tl).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h
      | some last => exact ⟨last, rfl⟩
    exact FramesRun.snoc hrun hlast (hreach _ hlast)

/-- **The seedable per-op GAS-record step.** As `gasLogAligned_step_gas`, but the reachability
hypothesis is the `GasReach`-style `∀ last, frs.getLast? = some last → Runs last (gasFrame current)`,
so it covers BOTH the empty seed (`frs = []`, vacuous reachability, `FramesRun []`) and the snoc case.
The appended word is the recorder's literal splice `gasReadOf (gasFrame current)`; the witness list
grows by `gasFrame current`. -/
theorem gasLogAligned_step_gas_seed {gasAcc : List Word} {frs : List Frame} {current : Frame}
    {exec : ExecutionState}
    (halign : GasLogAligned gasAcc frs)
    (hreach : ∀ last, frs.getLast? = some last → Runs last (gasFrame current))
    (hdec : decode current.exec.executionEnv.code current.exec.pc = some (.Smsf .GAS, .none))
    (hsz : current.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ current.exec.gasAvailable.toNat)
    (hstep : stepFrame current = .next exec) :
    GasLogAligned (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) (frs ++ [gasFrame current]) := by
  obtain ⟨hreads, hrun⟩ := halign
  refine ⟨?_, FramesRun.snoc_seed hrun hreach⟩
  rw [List.map_append, ← hreads]
  simp only [List.map_cons, List.map_nil]
  rw [gasRecord_eq_gasReadOf current hdec hsz hgas hstep]

/-- **The per-cursor GAS-channel reachability invariant.** The witness tail `Runs`-reaches the cursor
frame: vacuously true at the empty seed (`frs = []`), and `Runs last fr0` once `frs` is non-empty.
Threaded alongside `GasLogAligned` so the GAS arm can `FramesRun.snoc_seed` the new witness frame. -/
def GasReach (frs : List Frame) (fr0 : Frame) : Prop :=
  ∀ last, frs.getLast? = some last → Runs last fr0

/-- `GasReach` transports forward along a `Runs fr0 fr0'` segment (`Runs.trans`). -/
theorem GasReach.trans {frs : List Frame} {fr0 fr0' : Frame}
    (h : GasReach frs fr0) (hseg : Runs fr0 fr0') : GasReach frs fr0' :=
  fun last hl => Runs.trans (h last hl) hseg

/-- **The per-cursor GAS classification (the walk's per-cursor dispatch input).** At cursor `pc`
holding statement `s`, with `Corr` frame `fr0` and the per-cursor lowered segment `Runs fr0 fr1`
(from `SimStmtStep`), the walk is told the cursor is EITHER a GAS cursor or not:

* **`gas` arm** — `s = .assign t .gas` (`hs`), the segment head decodes to `GAS` at `fr0` (`hdec`),
  the gas envelope `Gbase ≤ fr0.gas` holds (`hgas`, the S4 lower bound CONSUMED here), and the GAS op
  strictly advances (`hne : fr0 ≠ fr1`, satisfiable since `GAS` is non-terminal). These are exactly
  the inputs `Runs.gas_cancel` + `gasLogAligned_step_gas_seed` consume.
* **`notgas` arm** — `∀ t, s ≠ .assign t .gas` (`hnotgas`): the no-record arm, carrying the alignment
  verbatim.

A real lowered run satisfies this at every cursor (the GAS arm at spilled-gas def-sites whose stash
head is `[GAS]`, the non-GAS arm elsewhere); it is the per-cursor classification the (former)
black-box walk could not see. -/
inductive GasCursorClass (s : Stmt) (fr0 fr1 : Frame) : Prop where
  | gas (t : Tmp) (hs : s = .assign t .gas)
      (hdec : decode fr0.exec.executionEnv.code fr0.exec.pc = some (.Smsf .GAS, .none))
      (hgas : GasConstants.Gbase ≤ fr0.exec.gasAvailable.toNat)
      (hne : fr0 ≠ fr1) : GasCursorClass s fr0 fr1
  | notgas (hnotgas : ∀ t, s ≠ .assign t .gas) : GasCursorClass s fr0 fr1

/-! ## §9 — the EDGE wrappers (Tier 2 / C5): `driveCorrPlus_step_jump` / `_branch`

The non-halt (`jump`/`branch`) analogues of `drive_step_block_jump`/`drive_step_block_branch`
(`DriveSim.lean`), but threading `DriveCorrPlus` instead of the bare `DriveCorr`: where the
`DriveCorr` versions re-establish only `DriveCorr` at the successor block, these RE-ESTABLISH
`DriveCorrPlus` at the successor's entry frame `jumpdestFrame fj`. The bytecode construction is
IDENTICAL to the `DriveCorr` versions (statement-run via `sim_stmts_block`, the supplied §7 edge
bundle `hjump`/`hbranch` delivering the `JUMPDEST` landing `fj` with `Runs frT fj`,
`corr_at_jumpdest_landing` re-establishing `Corr` at the successor cursor, `cleanHalts_forward`
deriving the successor clean-halt, `totalGas_succ_lt` the strict descent, and the
`RunFrom.jump`/`.branchThen`/`.branchElse` IR continuation).

The ONLY two additions, both at the re-established successor boundary:
* **`SelfPresent (jumpdestFrame fj)`** via `selfPresent_runs_of_call hcall hdc.selfPresent hfrrun`
  — the P3 hop across the SAME `Runs fr (jumpdestFrame fj)` the wrapper already assembles. This is
  NOT circular: it consumes the boundary's `SelfPresent fr` (given) and the genuinely-constructed
  bytecode run, producing presence at a DIFFERENT frame.
* the **alignment** carried VERBATIM — the successor `DriveCorrPlus` uses the SAME
  `gasAcc`/`gasFrs`/`sloadAcc`/`sloadFrs` and is closed by `hdc.gasAligned`/`hdc.sloadAligned`. This
  is HONEST preservation, NOT a no-record-in-epilogue claim: it carries the same consumed-prefix
  forward. Advancing the prefix (`gasLogAligned_step_gas` at gas cursors) is the SEPARATE deferred
  EXTENSION, correctly NOT claimed here (matching the preservation-only stance of the L2.0 statement-walk).

The successor `DriveCorrPlus` is bound EXISTENTIALLY to the reached `jumpdestFrame fj` (Route-4b
indexed), NEVER the forbidden universal `∀ st' frT, Corr → DriveCorrPlus`. The supplied
`hjump`/`hbranch` bundles transcribe VERBATIM from `drive_step_block_jump`/`_branch` (satisfiable
per concrete program from `jump_to_block` / `sim_term_edge_branch` internals + the `ReachesBoundary`
walk), exactly as the `DriveCorr` versions consume them. `hcall : CallPreservesSelf` is the same
`.success` ext-call self seam the halt wrappers already supply (R1). -/

/-- **`driveCorrPlus` edge wrapper, `jump` arm (L2.3 / T3 / D2).** The `DriveCorrPlus` lifting of
`drive_step_block_jump`. From `DriveCorrPlus` at the boundary `L`, the block `b` with `b.term =
.jump dst`, the IR `RunStmts` to `st'`, the supplied `SimStmtStep` (folding S1/S5/S6), the P3 call
edge `CallPreservesSelf`, and the supplied §7 jump bundle `hjump` (VERBATIM from
`drive_step_block_jump`): run the block's statements then the lowered `PUSH4 dest ; JUMP ; ⟨land⟩
JUMPDEST` epilogue to the successor `dst`'s entry frame `jumpdestFrame fj`, RE-ESTABLISHING
`DriveCorrPlus` at `dst` (base via `corr_at_jumpdest_landing` + `cleanHalts_forward`; `SelfPresent`
via the P3 hop along `Runs fr (jumpdestFrame fj)`; alignment carried VERBATIM with the SAME
prefixes), the strict `totalGas` descent, and the IR continuation via `RunFrom.jump`. -/
theorem driveCorrPlus_step_jump {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T : Trace}
    {L : Label} {b : Block} {dst : Label} {bdst : Block} {fr : Frame}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hb : blockAt prog L = some b)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hbterm : b.term = .jump dst)
    (hrun : V2.RunStmts prog o st T b.stmts st' T)
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf)
    -- the terminator §7 jump bundle (supplied, VERBATIM from `drive_step_block_jump`): the
    -- post-statement `Corr`-frame `frT` runs the lowered `PUSH4 dest ; JUMP ; ⟨land⟩ JUMPDEST` to
    -- the successor's `JUMPDEST` landing `fj`, with the `Gjumpdest` margin (so the descent is
    -- provable). Dischargeable for a concrete program exactly as `sim_term_edge_jump`.
    (hjump : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      CleanHaltsNonException frT →
      ∃ fj : Frame, Runs frT fj
        ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
        ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
            prog.blocks dst.idx)
        ∧ fj.exec.executionEnv.code = lower prog
        ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
        ∧ fj.exec.stack = []
        ∧ fj.exec.executionEnv.canModifyState = true
        ∧ (∀ k, selfStorage fj k = st'.world k)
        ∧ MemRealises prog st' fj
        ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    ∃ fj : Frame,
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorrPlus prog sloadChg obs st' (jumpdestFrame fj) dst
          gasAcc gasFrs sloadAcc sloadFrs
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog o st' T dst O → RunFrom prog o st T L O) := by
  -- Layer D: run the block's statements to the terminator cursor (uses the BASE `Corr`).
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdc.base.corr hdc.base.cleanHalts hrun
  -- Layer E: the supplied jump bundle delivers the `JUMPDEST` landing `fj`. The clean-halt at the
  -- terminator cursor `frT` is the boundary's, forwarded along the statements run `fr → frT`.
  obtain ⟨fj, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk, hfjmod, hfjstore,
    hfjmem, hfjdec⟩ := hjump frT hcorrT (cleanHaltsNonException_forward hdc.base.cleanHalts hrunsT)
  -- the `JUMPDEST` step lands at `(dst, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbdst hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from the boundary's (the forward split).
  have hcleanSucc : CleanHaltsNonException (jumpdestFrame fj) :=
    cleanHaltsNonException_forward hdc.base.cleanHalts hfrrun
  -- re-establish `DriveCorrPlus` at the successor: base from the landing, `SelfPresent` via the
  -- P3 hop along the SAME `hfrrun`, alignment carried VERBATIM from the boundary.
  refine ⟨fj, hfrrun,
    { base := ⟨hjdcorr, hcleanSucc⟩
      selfPresent := selfPresent_runs_of_call hcall hdc.selfPresent hfrrun
      gasAligned := hdc.gasAligned
      sloadAligned := hdc.sloadAligned },
    totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas, ?_⟩
  -- the IR continuation: prepend this block's `RunStmts` + the `jump` terminator.
  intro O hO
  exact RunFrom.jump hb hrun hbterm hO

/-- **`driveCorrPlus` edge wrapper, `branch` arm (L2.4 / T4 / D3).** The `DriveCorrPlus` lifting of
`drive_step_block_branch`. From `DriveCorrPlus` at `L` (block `b`, `b.term = .branch cond thenL
elseL`), the block's IR `RunStmts` to `st'` (trace `T → T'`), the bound condition `st'.locals cond
= some cw`, the supplied `SimStmtStep`, the P3 call edge `CallPreservesSelf`, and the supplied §7
branch bundle `hbranch` (VERBATIM from `drive_step_block_branch`): run the statements then the
cond-materialise + `JUMPI` to the TAKEN successor `succ`'s entry frame `jumpdestFrame fj` (`succ =
thenL` when `cw ≠ 0`, `succ = elseL` when `cw = 0`), RE-ESTABLISHING `DriveCorrPlus` at `succ`
(base via `corr_at_jumpdest_landing` + `cleanHalts_forward`; `SelfPresent` via the P3 hop along
`Runs fr (jumpdestFrame fj)`; alignment carried VERBATIM), the strict `totalGas` descent, and the
IR continuation via `RunFrom.branchThen` / `.branchElse`. The cond-materialise sub-run is inside
the supplied `hbranch`'s `Runs frT fj`, so P3 threads `SelfPresent` across the whole `fr →
jumpdestFrame fj` at once — no separate materialise threading is needed. -/
theorem driveCorrPlus_step_branch {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace}
    {L : Label} {b : Block} {cond : Tmp} {cw : Word} {thenL elseL : Label} {fr : Frame}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hb : blockAt prog L = some b)
    (hbterm : b.term = .branch cond thenL elseL)
    (hrun : V2.RunStmts prog o st T b.stmts st' T')
    (hc : st'.locals cond = some cw)
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf)
    -- the terminator §7 branch bundle (supplied, VERBATIM from `drive_step_block_branch`): the
    -- post-statement `Corr`-frame `frT` runs the lowered cond-materialise + `JUMPI` to the TAKEN
    -- successor's `JUMPDEST` landing `fj`, with the taken successor `succ` resolved by `cw`.
    -- Dischargeable for a concrete program exactly as `sim_term_edge_branch`.
    (hbranch : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      CleanHaltsNonException frT →
      ∃ (succ : Label) (bsucc : Block) (fj : Frame),
        ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
        ∧ prog.blocks.toList[succ.idx]? = some bsucc
        ∧ Runs frT fj
        ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
        ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
            prog.blocks succ.idx)
        ∧ fj.exec.executionEnv.code = lower prog
        ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
        ∧ fj.exec.stack = []
        ∧ fj.exec.executionEnv.canModifyState = true
        ∧ (∀ k, selfStorage fj k = st'.world k)
        ∧ MemRealises prog st' fj
        ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    ∃ (succ : Label) (fj : Frame),
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorrPlus prog sloadChg obs st' (jumpdestFrame fj) succ
          gasAcc gasFrs sloadAcc sloadFrs
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog o st' T' succ O → RunFrom prog o st T L O) := by
  -- Layer D: run the block's statements to the terminator cursor (uses the BASE `Corr`).
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdc.base.corr hdc.base.cleanHalts hrun
  -- Layer E: the supplied branch bundle resolves the taken successor `succ` and its landing `fj`.
  -- The clean-halt at the terminator cursor `frT` is the boundary's, forwarded along `fr → frT`.
  obtain ⟨succ, bsucc, fj, hdir, hbsucc, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk,
    hfjmod, hfjstore, hfjmem, hfjdec⟩ := hbranch frT hcorrT
      (cleanHaltsNonException_forward hdc.base.cleanHalts hrunsT)
  -- the `JUMPDEST` step lands at `(succ, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbsucc hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from the boundary's (the forward split).
  have hcleanSucc : CleanHaltsNonException (jumpdestFrame fj) :=
    cleanHaltsNonException_forward hdc.base.cleanHalts hfrrun
  -- re-establish `DriveCorrPlus` at the taken successor, exactly as in the `jump` arm.
  refine ⟨succ, fj, hfrrun,
    { base := ⟨hjdcorr, hcleanSucc⟩
      selfPresent := selfPresent_runs_of_call hcall hdc.selfPresent hfrrun
      gasAligned := hdc.gasAligned
      sloadAligned := hdc.sloadAligned },
    totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas, ?_⟩
  -- the IR continuation: prepend this block's `RunStmts` + the firing `branch` terminator.
  intro O hO
  rcases hdir with ⟨hsucc, hnz⟩ | ⟨hsucc, hz⟩
  · subst hsucc
    exact RunFrom.branchThen hb hrun hbterm hc hnz hO
  · subst hsucc; subst hz
    exact RunFrom.branchElse hb hrun hbterm hc hO

/-! ## §10 — the `DriveCorrPlus` recursion (C8) and the tie-free headline (C9)

The four proven `driveCorrPlus_step_*` wrappers are the per-block leaves of a recursion that
threads the strengthened `DriveCorrPlus` invariant — exactly the `DriveCorr` tower of `DriveSim.lean`
(`driveStep_of_block` → `runFrom_of_driveCorr` → `lower_conforms_cyclic`), but lifted so that the
gas-positional / self-presence channels the `Plus` invariant carries are **re-established at every
reached boundary** rather than supplied per edge.

* **`DriveStepPlus`** — the `Plus` analogue of `DriveStep`: at a `DriveCorrPlus` boundary, either the
  block halts (the IR `RunFrom`, halt disjunct) or it takes an edge to a strictly-smaller successor
  whose re-established invariant is `DriveCorrPlus` (NOT the bare `DriveCorr`). Threading the `Plus`
  invariant through the recursion is what discharges the gas-advance (S3) / `SelfPresent` /
  `accounts ≠ ∅` channels uniformly, instead of supplying them at each boundary.
* **`driveStepPlus_of_block`** (C8) — assembles `DriveStepPlus` at one block by dispatching `b.term`
  to the four proven `driveCorrPlus_step_*` wrappers. The IR block run is `runStmts_exists` (from the
  static `RunDefinable`), exactly as `driveStep_of_block`.
* **`runFrom_of_driveCorrPlus`** — the `Plus` analogue of `runFrom_of_driveCorr`: strong induction on
  the bytecode `totalGas` measure, recursing at the strictly-smaller successor `DriveCorrPlus`.
* **`lower_conforms_cyclic_tiefree`** (C9) — feeds the `Plus`-constructed `RunFrom` into the existing
  `sim_cfg`, recovering the world equation with the gas / self channels DISCHARGED through the `Plus`
  thread. The genuinely-runtime residuals stay SUPPLIED (documented at C9). -/

/-- **The `Plus` per-block drive obligation.** As `DriveStep`, but the edge arm re-establishes the
strengthened `DriveCorrPlus` invariant (with its `Plus` accumulators) at the successor rather than
the bare `DriveCorr`. The halt arm is the IR `RunFrom` (the block bottoms out); the edge arm is a
strictly-smaller successor `DriveCorrPlus` plus the IR continuation. `runFrom_of_driveCorrPlus`
recurses on it; the gas / self channels thread through the successor invariant. -/
def DriveStepPlus (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (o : V2.CallOracle)
    (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace) : Prop :=
  -- halt arm: the block bottoms out, IR halts at `O`.
  (∃ O : V2.Observable, RunFrom prog o st T L O)
  ∨
  -- edge arm: a strictly-smaller successor boundary re-establishing `DriveCorrPlus`.
  (∃ (st' : V2.IRState) (T' : Trace) (succ : Label) (fr' : Frame)
      (gasAcc' : List Word) (gasFrs' : List Frame) (sloadAcc' : List Nat) (sloadFrs' : List Frame),
      DriveCorrPlus prog sloadChg obs st' fr' succ gasAcc' gasFrs' sloadAcc' sloadFrs'
    ∧ totalGas [] (.inl fr') < totalGas [] (.inl fr)
    ∧ (∀ O, RunFrom prog o st' T' succ O → RunFrom prog o st T L O))

/-- **C8 — `driveStepPlus_of_block`.** From `DriveCorrPlus` at `L`, the block present, the static
operand-definability `RunDefinable`, the per-statement simulation `SimStmtStep`, the P3 call edge
`CallPreservesSelf`, and the per-terminator supplied §7 bundles (the halt world-channel /
RETURN-epilogue / jump / branch edge data — exactly what the `driveCorrPlus_step_*` wrappers
consume, quantified by terminator shape), produce `DriveStepPlus` at this block. The IR block run is
`runStmts_exists` (`RunDefinable`); the conclusion is the halt disjunct for `stop`/`ret` (built by
`RunFrom.stop`/`.ret`) and the edge disjunct (the re-established successor `DriveCorrPlus`) for
`jump`/`branch`, dispatched on `b.term`. -/
theorem driveStepPlus_of_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st : V2.IRState} {fr : Frame} {L : Label} {T : Trace} {b : Block}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hb : blockAt prog L = some b)
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hdef : RunDefinable prog)
    (hcall : CallPreservesSelf)
    -- the `jump` destination block's presence (static, replacing `CFGAcyclic.succ_present`):
    (hjumpPresent : ∀ (dst : Label), b.term = .jump dst →
      ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `jump` edge bundle (used only on `jump dst`, exactly `driveCorrPlus_step_jump`'s):
    (hjump : ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ fj : Frame, Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks dst.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none))
    -- the `branch` edge bundle (used only on `branch cond thenL elseL`):
    (hbranch : ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks succ.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    DriveStepPlus prog sloadChg obs o st fr L T := by
  -- the toList form of the block presence (the wrappers' `_hb`/`hb` argument shape).
  have hbtl : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  -- run the block's statements forward (gas-free / call-free, definable from any state).
  have hrun : V2.RunStmts prog o st T b.stmts (stmtsPost st b.stmts) T :=
    runStmts_exists (hdef.stmts st L b hb)
  -- dispatch on the terminator shape.
  cases hterm : b.term with
  | stop =>
    -- halt disjunct (LEFT): the IR `RunFrom.stop`. `SelfPresent`/`accounts ≠ ∅` at the reached terminator are threaded via the `Plus`
    -- invariant; the IR `RunFrom` itself is `RunFrom.stop`.
    exact Or.inl ⟨_, RunFrom.stop hb hrun hterm⟩
  | ret t =>
    -- halt disjunct (LEFT): the IR `RunFrom.ret`; the operand is `RunDefinable.ret_def`.
    obtain ⟨w, hv⟩ := hdef.ret_def st L b t hb hterm
    exact Or.inl ⟨_, RunFrom.ret hb hrun hterm hv⟩
  | jump dst =>
    -- edge disjunct (RIGHT) via `driveCorrPlus_step_jump`; `dst`'s presence via `hjumpPresent`.
    obtain ⟨bdst, hbdst⟩ := hjumpPresent dst hterm
    obtain ⟨fj, hfrrun, hdcorr', hlt, hcont⟩ :=
      driveCorrPlus_step_jump hdc hb hbdst hterm hrun hsim hcall (hjump dst hterm)
    exact Or.inr ⟨stmtsPost st b.stmts, T, dst, jumpdestFrame fj, _, _, _, _, hdcorr', hlt, hcont⟩
  | branch cond thenL elseL =>
    -- edge disjunct (RIGHT) via `driveCorrPlus_step_branch`; the condition is `RunDefinable`.
    obtain ⟨cw, hc⟩ := hdef.branch_def st L b cond thenL elseL hb hterm
    obtain ⟨succ, fj, hfrrun, hdcorr', hlt, hcont⟩ :=
      driveCorrPlus_step_branch hdc hb hterm hrun hc hsim hcall
        (hbranch cond thenL elseL cw hterm hc)
    exact Or.inr ⟨stmtsPost st b.stmts, T, succ, jumpdestFrame fj, _, _, _, _, hdcorr', hlt, hcont⟩

/-- **`runFrom_of_driveCorrPlus`.** The `Plus` analogue of `runFrom_of_driveCorr`: from
`DriveCorrPlus … st fr L …` and the `Plus` per-block drive obligation `DriveStepPlus` at **every**
reachable boundary, the IR `RunFrom prog o st T L` exists for some observable `O`. Proved by strong
induction on the bytecode `totalGas` measure (which strictly descends per block,
`totalGas_succ_lt`), so it holds for **cyclic** CFGs — no `CFGAcyclic`. The edge arm recurses at the
strictly-smaller successor's `DriveCorrPlus`; the gas / self channels thread through the successor
invariant. -/
theorem runFrom_of_driveCorrPlus {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle}
    (hstep : ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace)
      (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      DriveStepPlus prog sloadChg obs o st fr L T) :
    ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace)
      (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      ∃ O, RunFrom prog o st T L O := by
  -- strong induction on the bytecode `totalGas` measure of the boundary frame.
  intro st fr L T gasAcc gasFrs sloadAcc sloadFrs hdc
  induction hmeasure : totalGas [] (.inl fr) using Nat.strong_induction_on
    generalizing st fr L T gasAcc gasFrs sloadAcc sloadFrs with
  | _ n ih =>
    subst hmeasure
    rcases hstep st fr L T gasAcc gasFrs sloadAcc sloadFrs hdc with
      ⟨O, hir⟩ | ⟨st', T', succ, fr', gasAcc', gasFrs', sloadAcc', sloadFrs', hdc', hlt, hcont⟩
    · -- halt arm: the block bottoms out.
      exact ⟨O, hir⟩
    · -- edge arm: recurse at the strictly-smaller successor `DriveCorrPlus`, then prepend the block.
      obtain ⟨O, hO⟩ := ih (totalGas [] (.inl fr')) hlt st' fr' succ T'
        gasAcc' gasFrs' sloadAcc' sloadFrs' hdc' rfl
      exact ⟨O, hcont O hO⟩

/-- **C9 — `lower_conforms_cyclic_tiefree`.** The tie-free headline. Given the entry `DriveCorrPlus`
(assembled at the entry frame by `driveCorrPlus_entry`), the static operand-definability
`RunDefinable`, the per-boundary block presence, the per-statement simulation `SimStmtStep`, the P3
call edge `CallPreservesSelf`, and the per-terminator supplied §7 edge bundles, the world equation
holds for the `Plus`-constructed run's existential observable — **general over CYCLIC CFGs** (no
`CFGAcyclic`/`RunDefinable`-as-acyclicity; the `totalGas` measure replaces static block-rank).

`driveStepPlus_of_block` assembles `DriveStepPlus` at every reached boundary from the supplied data,
threading the strengthened `DriveCorrPlus` invariant; `runFrom_of_driveCorrPlus` builds the IR
`RunFrom`; the existing cycle-agnostic `sim_cfg` ties it to the bytecode halt's world.

**Re-established through the `Plus` thread** (vs `lower_conforms_cyclic`, which supplies a raw
`hstep`): the SSTORE self-presence (`SelfPresent`) and `accounts ≠ ∅` invariants re-established at every reached boundary.
The `Plus` invariant threads ONLY `SelfPresent` (the gas/sload alignment witnesses are carried
VERBATIM, never advanced). **Still SUPPLIED** (genuinely-runtime residuals): the gas positional value
**S3** supplied via `SimStmtStep` (the `StmtTies` gas conjunct), NOT discharged by any carried
alignment; the `sim_cfg` per-block ties `hstmts`/`hterm` (the serialized S1/S5/S6 spine + the world-channel halt brick), the P3
`CallPreservesSelf` `.success` ext-call self seam, and the per-terminator edge bundles
`hjumpPresent`/`hjump`/`hbranch` (concrete lowered PUSH/JUMP epilogue data). -/
theorem lower_conforms_cyclic_tiefree {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress}
    {st₀ : V2.IRState} {T : Trace} {params : Evm.CallParams} {code : ByteArray} {acc : Account}
    -- the entry boundary: a `DriveCorr` at `(prog.entry, 0)` whose frame is the call's `codeFrame`,
    -- with the self account present (`hwf`). `driveCorrPlus_entry` lifts it to `DriveCorrPlus`.
    (hbase : DriveCorr prog sloadChg obs st₀ (codeFrame params code) prog.entry)
    (hwf : params.accounts.find? params.recipient = some acc)
    -- static operand-definability (benign well-formedness — NOT `CFGAcyclic`):
    (hdef : RunDefinable prog)
    -- the P3 call edge (the `.success` ext-call self seam — supplied):
    (hcall : CallPreservesSelf)
    -- block presence at every reachable `DriveCorrPlus` boundary:
    (hpresent : ∀ (st : V2.IRState) (fr : Frame) (L : Label)
        (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      ∃ b, blockAt prog L = some b)
    -- the per-statement tie (`sim_cfg`'s + `driveStepPlus_of_block`'s):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs o L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs o self L b)
    -- the `jump` destination presence, at every block (`st`-free — the destination is static):
    (hjumpPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
        ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `jump` edge bundle, at every block / post-statement frame:
    (hjump : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ fj : Frame, Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks dst.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none))
    -- the `branch` edge bundle, at every block / post-statement frame:
    (hbranch : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks succ.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs (codeFrame params code) last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world)
      ∧ RunFrom prog o st₀ T prog.entry O := by
  -- the entry `DriveCorrPlus` (empty consumed prefixes) via `driveCorrPlus_entry`.
  have hentryPlus : DriveCorrPlus prog sloadChg obs st₀ (codeFrame params code) prog.entry [] [] [] [] :=
    driveCorrPlus_entry hbase hwf
  -- assemble the per-boundary `DriveStepPlus` from `driveStepPlus_of_block` at each reached block.
  have hstep : ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace)
      (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      DriveStepPlus prog sloadChg obs o st fr L T := by
    intro st fr L T' gasAcc gasFrs sloadAcc sloadFrs hdc
    obtain ⟨b, hb⟩ := hpresent st fr L gasAcc gasFrs sloadAcc sloadFrs hdc
    exact driveStepPlus_of_block hb hdc (hstmts L b hb) hdef hcall
      (hjumpPresent L b hb) (hjump st L b hb) (hbranch st L b hb)
  -- the `Plus` recursion builds the IR `RunFrom` from the entry `DriveCorrPlus`.
  obtain ⟨O, hir⟩ :=
    runFrom_of_driveCorrPlus hstep st₀ (codeFrame params code) prog.entry T [] [] [] [] hentryPlus
  -- the EXISTING cycle-agnostic `sim_cfg`: tie the constructed run to the bytecode halt world.
  obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := sim_cfg hstmts hterm hbase.corr hbase.cleanHalts hir
  exact ⟨O, ⟨last, haltSig, hlast, hhalt, hworld⟩, hir⟩

/-- **`lower_conforms_cyclic_assembled` — the headline with `hstmts`/`hterm` BUILT, not supplied.**
Same conclusion as `lower_conforms_cyclic_tiefree`, but the two opaque `∀-L-b` per-block
simulation universals are replaced by their honest builder inputs:

* `hwfl : WellFormedLowered prog` — the purely-structural fuel/pc/offset/slot side-conditions
  (`LowerConforms.lean:142`); and
* `hstmtties`/`htermties` — the genuine §7 per-block recording-correspondence ties (`Lir.StmtTies`
  / `Lir.TermTies`), i.e. exactly the per-cursor / per-terminator runtime ties that
  `simStmtStep_block` / `simTermStep_block` consume (assign post-state realisability, the spilled
  sload/gas stash data, the SSTORE/CALL realisation seams, the RETURN-epilogue / stop frame facts,
  and the successor-block presence for edges).

The opaque `SimStmtStep`/`SimTermStep` universals (2 of the headline's 4) are thereby DISCHARGED
through `simStmtStep_block` / `simTermStep_block`. The `jump` edge universal `hjump` is **also**
DISCHARGED here: `jump_landing_of_cleanHalt` (`LowerDecode.lean`) is the green producer for the
`Plus`-thread *pre-JUMPDEST landing* frame `fj` (sitting ON the successor's `JUMPDEST` byte, BEFORE
the `JUMPDEST` step), with its three gas guards produced from the threaded `CleanHaltsNonException
frT`; the destination presence (`hjumpPresent`) and the folded pc/offset bounds
(`WellFormedLowered.bound_jump`) supply its remaining structural inputs.

The `branch` edge universal `hbranch` is **also** DISCHARGED here: `branch_landing_of_cleanHalt`
(`LowerDecode.lean`) is the green producer for the TAKEN-successor pre-JUMPDEST landing (the
cond-materialise + JUMPI split ahead of the same `jump`-arm landing); its gas guards are produced
from the threaded `CleanHaltsNonException frT`, its presence / pc-offset bounds / fuel-sufficiency
from `hbranchPresent` / `WellFormedLowered.bound_branch` / `WellFormedLowered.matFueled_branch`.

Still HONESTLY SUPPLIED (static CFG well-formedness + the non-gas-derivable structural folds, NOT
faked): the block-presence facts `hpresent`/`hjumpPresent`/`hbranchPresent`, and the cond-materialise
stack-room fold `hstkBranch` (the `hstkKey` analogue — a charge-length bound the gas thread cannot
produce). -/
theorem lower_conforms_cyclic_assembled {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress}
    {st₀ : V2.IRState} {T : Trace} {params : Evm.CallParams} {code : ByteArray} {acc : Account}
    (hbase : DriveCorr prog sloadChg obs st₀ (codeFrame params code) prog.entry)
    (hwf : params.accounts.find? params.recipient = some acc)
    (hdef : RunDefinable prog)
    (hcall : CallPreservesSelf)
    (hpresent : ∀ (st : V2.IRState) (fr : Frame) (L : Label)
        (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      ∃ b, blockAt prog L = some b)
    -- WELL-FORMEDNESS: the folded structural side-conditions (replaces the structural part of
    -- `hstmts`/`hterm`):
    (hwfl : WellFormedLowered prog)
    -- the GENUINE §7 per-block ties (replaces the runtime part of the opaque `hstmts`/`hterm`):
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs o L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs o self L b)
    (hjumpPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
        ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `branch` successor presence (static CFG well-formedness, the `hjumpPresent` analogue for
    -- both branch targets):
    (hbranchPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label), b.term = .branch cond thenL elseL →
        (∃ bthen : Block, prog.blocks.toList[thenL.idx]? = some bthen)
        ∧ (∃ belse : Block, prog.blocks.toList[elseL.idx]? = some belse))
    -- the `branch` cond-materialise stack-room fold (the structural `hstkKey`/`hstk` analogue —
    -- NOT gas-derivable; a static charge-length bound). `branch_landing_of_cleanHalt` produces the
    -- rest of the `branch` edge bundle (gas guards from the threaded clean-halt; presence /
    -- bounds / fuel-sufficiency from `hbranchPresent` / `WellFormedLowered.bound_branch` /
    -- `WellFormedLowered.matFueled_branch`).
    (hstkBranch : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label), b.term = .branch cond thenL elseL →
        (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs (codeFrame params code) last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world)
      ∧ RunFrom prog o st₀ T prog.entry O := by
  -- build the per-block `SimStmtStep` from `WellFormedLowered` + the §7 statement ties.
  have hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs o L b := by
    intro L b hbat
    obtain ⟨hassign, hsloadassign, hgasassign, hsstore, hcallties⟩ := hstmtties L b hbat
    exact simStmtStep_block (toList_of_blockAt hbat) hwfl hassign hsloadassign hgasassign hsstore
      hcallties
  -- build the per-block `SimTermStep` from `WellFormedLowered` + the §7 terminator ties.
  have hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs o self L b := by
    intro L b hbat
    obtain ⟨hsucc, hstop, hretties, hjmp, hbr⟩ := htermties L b hbat
    exact simTermStep_block (toList_of_blockAt hbat) hwfl hsucc hstop hretties hjmp hbr
  -- DISCHARGE the `jump` edge bundle from the pre-`JUMPDEST` landing producer: the destination
  -- presence (`hjumpPresent`) gives `bdst` + `dst.idx < size`, and `WellFormedLowered.bound_jump`
  -- supplies the two pc/offset bounds. `jump_landing_of_cleanHalt` then produces the landing `fj`
  -- with all three gas guards from the threaded `CleanHaltsNonException frT`.
  have hjump : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ fj : Frame, Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks dst.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    intro st L b hbat dst hbterm frT hcorrT hcsT
    obtain ⟨bdst, hbdst⟩ := hjumpPresent L b hbat dst hbterm
    have hdstlt : dst.idx < prog.blocks.size := by
      simpa using (List.getElem?_eq_some_iff.mp hbdst).1
    obtain ⟨hpc5, hoff⟩ := hwfl.bound_jump L b dst (toList_of_blockAt hbat) hbterm
    exact jump_landing_of_cleanHalt frT hcorrT hbterm (toList_of_blockAt hbat) hbdst hdstlt
      hpc5 hoff hcsT
  -- DISCHARGE the `branch` edge bundle from `branch_landing_of_cleanHalt`: the two successor
  -- presences (`hbranchPresent`) give `bthen`/`belse` + the `idx < size` bounds; the folded
  -- `WellFormedLowered.bound_branch` / `matFueled_branch` supply the pc/offset bounds and the
  -- cond-materialise fuel-sufficiency; the structural stack-room fold is `hstkBranch`. The clean-
  -- halt at the terminator cursor is forwarded along the statements run inside `driveCorrPlus_step_branch`.
  have hbranch : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks succ.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    intro st L b hbat cond thenL elseL cw hbterm hc frT hcorrT hcsT
    obtain ⟨⟨bthen, hbthen⟩, ⟨belse, hbelse⟩⟩ := hbranchPresent L b hbat cond thenL elseL hbterm
    have hthenlt : thenL.idx < prog.blocks.size := by
      simpa using (List.getElem?_eq_some_iff.mp hbthen).1
    have helselt : elseL.idx < prog.blocks.size := by
      simpa using (List.getElem?_eq_some_iff.mp hbelse).1
    obtain ⟨hbt, hbthenoff, hbelseoff⟩ := hwfl.bound_branch L b cond thenL elseL
      (toList_of_blockAt hbat) hbterm
    -- the cond-materialise stack-room fold, with `frT.stack = []` from `Corr`.
    have hstkCond : frT.exec.stack.size
        + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024 := by
      rw [hcorrT.stack_nil]
      simpa using hstkBranch L b hbat cond thenL elseL hbterm
    exact branch_landing_of_cleanHalt frT hcorrT hbterm (toList_of_blockAt hbat) hc hbthen hbelse
      hthenlt helselt hbt hbthenoff hbelseoff
      (hwfl.matFueled_branch L b cond thenL elseL (toList_of_blockAt hbat) hbterm) hstkCond hcsT
  exact lower_conforms_cyclic_tiefree hbase hwf hdef hcall hpresent hstmts hterm
    hjumpPresent hjump hbranch

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the tie-discharge deliverables.
-- C3: the no-bridge VALUE channels of the L2.0 statement-walk.
-- L2.0g: the seedable GAS-alignment bricks (GAS-advancing walk decls + S3 read-off removed, audit).
-- C4: the edge wrappers (jump/branch).
-- C8/C9: the `DriveCorrPlus` recursion assembly + the tie-free headline.
-- ASSEMBLE: the headline with `hstmts`/`hterm` built from `WellFormedLowered` + the §7 ties.
