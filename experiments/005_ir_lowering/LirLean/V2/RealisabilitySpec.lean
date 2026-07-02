import LirLean.V2.TieDischarge

/-!
# LirLean v2 — the REALISABILITY SPEC skeleton (Phase-3 target statements; Nightly-only)

**EVERY `sorry` IN THIS FILE IS TRACKED DEBT.** This module is the reviewable Phase-3
specification: the flagship `lowering_conforms` (R11) is the target statement of the whole
experiment, and the obligations R1–R12 are the named gaps between the green machinery in the
tree and that flagship. All `def`s/`structure`s here are REAL (complete, no `sorry`); only
theorem PROOFS are `sorry`d. This module is deliberately registered in the NON-DEFAULT
`Nightly` lean_lib — the default `LirLean` target stays sorry-free and does not import it.

## The vacuity lessons this file is shaped by

1. **The retired `Lir.GasRealises` universal** (HonestGasTie's finding, Phase 2): a single
   fixed gas word, universally quantified over frames pinned only by address, is
   unsatisfiable — one adversarial frame with a different `gasAvailable` refutes it.
2. **The free-`∀` disease in the current `StmtTies`/`TermTies`**
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

## The two scope seams added beyond the fleet sketch

* **`RunLog.clean` conservatively excludes zero-gas reverts**: exp003's `endCall` maps an
  `.exception` to `success := false, gasRemaining := 0, output := .empty`, so a genuine
  zero-gas revert is indistinguishable from an exception ON THE LOG. `clean` demands
  `success ∨ gasRemaining ≠ 0` — sound (hypothesis false ⇒ theorem silent, never unsound),
  and it cuts the zero-gas-revert corner out of scope. Tracked decision.
* **`NonzeroSstores`**: `sim_sstore_stmt` requires `vw ≠ 0` (the nonzero-write scope of
  `EvalStmt.sstore`, `V2/Machine.lean`), and no fleet report surfaced this in the flagship
  signature. It is a named scope seam (the flagship's `hnzw`), threaded through the walk
  invariant (`DriveCorrLog.nonzeroSstores`) — either `sim_sstore` gets extended to zero
  writes or SSTOREs get recorded in the log; until then the seam is honest and explicit.

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

/-! ## §1 — Helper definitions (all REAL; no sorry)

The flagship's hypothesis vocabulary: the entry state, the log-side clean-scope predicate,
observable agreement, the static well-formedness bundle, the honest oracle seams, and the
scope seams. -/

/-- The IR entry state of a top-level call: empty locals, world = the recipient's storage
lens of the pre-call accounts (the `find?/lookupStorage` lens `resultStorageAt`/`observe`
read, applied to `params.accounts`). Replaces the supplied entry `StorageAgree` hypothesis
of `lower_conforms_wf` BY DEFINITION — the entry world *is* the params' lens (the pin is
then `rfl`-flavoured at the entry `codeFrame`, whose `accounts` are `params.accounts`).
DERIVED status: definitional (nothing to discharge). -/
def entryState (params : CallParams) : IRState :=
  { locals := fun _ => none
    world  := fun k => (params.accounts.find? params.recipient).option 0 (·.lookupStorage k) }

/-- **The log-side clean-scope predicate** (the flagship's `hclean`). The recorded run
halted cleanly: a top-level `.call` result that either succeeded or reverted with gas left.

Ground truth (`endCall`, exp003 `Evm/Semantics/Call.lean`): `.success → success := true`;
`.revert g o → success := false, gasRemaining := g`; `.exception → success := false,
gasRemaining := 0, output := .empty`. So an exception is distinguishable from a revert ON
THE LOG only via `gasRemaining ≠ 0` — **a genuine zero-gas revert is conservatively
excluded** (scope cut; sound: the hypothesis is then false and the flagship silent). The
fleet sketch's `ResultNonException` does not exist in the tree; this is its honest
decidable-on-the-log replacement. A `.create` observable is out of scope (top-level frames
here are calls). SUPPLIED status: a decidable premise read off the log (both branches are
`Bool`/`DecidableEq` facts). R2 turns it into the `∀ last halt`-universal
`cleanHalts_of_runWithLog` consumes. -/
def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False

/-- **Observable agreement, world channel** (the flagship's conclusion edge). The IR
observable's world equals the `observe`-world of the recorded bytecode result. The
halt-result channel is the documented empty-RETURN cut (`observe` maps every result to
`.stopped`; the value channel is deferred with the rest of the RETURN-output work —
`V2/RunLog.lean`, `observe` docstring). DERIVED status: the conclusion, not a premise. -/
def Conforms (self : AccountAddress) (log : RunLog) (O : Observable) : Prop :=
  O.world = (observe self log.observable).world

/-- **Static CFG closure** — entry present and pc-bounded, every jump/branch target present,
in-bounds, and offset-bounded. Folds the current headline's `hentry0`-adjacent presence
facts, `hjumpPresent`, `hbranchPresent`, and the `offsetTable … < 2^32` bounds that
`entry_corr` and the edge bundles consume. SUPPLIED status: static, a finite check on the
program text (the R9 checker's territory); R8 is its named consumer (kills the inside-out
`hpresent`). -/
structure ClosedCFG (prog : Program) : Prop where
  /-- The entry block is present. -/
  entry_present : ∃ b, blockAt prog prog.entry = some b
  /-- The entry block's byte offset fits a 32-bit pc (what `entry_corr` consumes). -/
  entry_bound :
    offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32
  /-- Every jump target is present, in-bounds, and offset-bounded. -/
  jump_closed : ∀ (L : Label) (b : Block) (dst : Label),
    blockAt prog L = some b → b.term = .jump dst →
    (∃ b', blockAt prog dst = some b')
    ∧ dst.idx < prog.blocks.size
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32
  /-- Both branch targets are present, in-bounds, and offset-bounded. -/
  branch_closed : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    ((∃ b', blockAt prog thenL = some b')
      ∧ thenL.idx < prog.blocks.size
      ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32)
    ∧ ((∃ b', blockAt prog elseL = some b')
      ∧ elseL.idx < prog.blocks.size
      ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32)

/-- **Static stack-room bounds** — the per-cursor `chargeOf`-length ≤ 1024 folds the ties
carry (`hstkBranch` of the assembled headline; the `hstkKey` bound of the sload arm; the
sstore fold; the ret fold). Quantified `∀ sloadChg` and PROVABLE that way: `chargeOf`'s
LENGTH is structurally independent of the `sloadChg` values (each `.sload` contributes
exactly one entry whatever the charge). SUPPLIED status: static, decidable per program
(R9's checker discharges it). -/
structure StackRoomOK (prog : Program) : Prop where
  /-- The `branch` cond-materialise stack fold (the headline's `hstkBranch`). -/
  branch : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024
  /-- The spilled-sload key-prefix stack fold (the tie's `hstkKey`; the frame term is 0 at
  a statement boundary by `Corr.stack_nil`, so the pure charge-length bound suffices). -/
  sloadKey : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    (chargeOf (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k)).length ≤ 1024
  /-- The `sstore` two-operand stack fold. -/
  sstore : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.sstore key value) →
    (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
      + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024
  /-- The `ret` operand stack fold. -/
  ret : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024

/-! ### Gas/call-aware run-definability (`RunDefinableG`)

The existing `RunDefinable` (`V2/IRRun.lean`) is UNSATISFIABLE for any program with a
`Stmt.call` or a gas read (header lesson 4), so it cannot be the flagship's definability
bundle. The honest replacement threads definability along `RunStmts` itself: the semantics
natively supplies the gas word (stream head) and the call bundle (oracle query), so "the
operands of the statement at cursor `pc` are bound at every state `RunStmts` reaches by
running the prefix" is exactly the fact `RunFrom`-existence needs — and it is state-uniform
in the block-ENTRY state (the same sound over-approximation the old bundle used), while the
INTERMEDIATE states are pinned by the derivation, never free. -/

/-- Gas/call-aware operand definability of one statement at state `st`: what the matching
`EvalStmt` constructor demands of `st` (the gas word / call bundle are supplied by the
stream / oracle, so a gas assign is unconditionally definable). -/
def StmtDefinableG (st : IRState) : Stmt → Prop
  | .assign _ e => e = .gas ∨ ∃ w, evalExpr st 0 e = some w
  | .sstore key value => (∃ kw, st.locals key = some kw) ∧ (∃ vw, st.locals value = some vw)
  | .call cs => (∃ cw, st.locals cs.callee = some cw) ∧ (∃ gw, st.locals cs.gasFwd = some gw)

/-- **Gas/call-aware run-definability** — the honest replacement of `RunDefinable`
(unsatisfiable on the gas/call domain, header lesson 4). Definability is threaded along
`RunStmts` derivations: at every cursor, the statement is definable at the state reached by
running the block prefix (any oracle, any trace, any block-entry state); the `ret` operand
and `branch` condition are bound at the post-statement state. SUPPLIED status: static per
program in the same over-approximate sense as the old bundle (state-uniform in the
block-entry state); decidable for concrete programs by running the fold — R9's checker
discharges it. -/
structure RunDefinableG (prog : Program) : Prop where
  /-- Every cursor's statement is definable at every state a `RunStmts` prefix-run reaches. -/
  stmts : ∀ (o : CallOracle) (st st' : IRState) (T T' : Trace) (L : Label) (b : Block)
      (pc : Nat) (s : Stmt),
    blockAt prog L = some b → b.stmts[pc]? = some s →
    RunStmts prog o st T (b.stmts.take pc) st' T' →
    StmtDefinableG st' s
  /-- A `ret t` block's operand is bound at every `RunStmts`-post state. -/
  ret_def : ∀ (o : CallOracle) (st st' : IRState) (T T' : Trace) (L : Label) (b : Block)
      (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    RunStmts prog o st T b.stmts st' T' →
    ∃ w, st'.locals t = some w
  /-- A `branch cond _ _` block's condition is bound at every `RunStmts`-post state. -/
  branch_def : ∀ (o : CallOracle) (st st' : IRState) (T T' : Trace) (L : Label) (b : Block)
      (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    RunStmts prog o st T b.stmts st' T' →
    ∃ cw, st'.locals cond = some cw

/-- **The static well-formedness bundle** (the flagship's `hwl`) — a function of the program
text only, intended to be checker-dischargeable (R9). Folds the current headline's
`hwfl`/`hdef`/`hentry0`/presence/offset/stack-fold hypotheses into one named structure.
SUPPLIED status: one static premise; every field is decidable-in-principle per program.
NOTE the `defs` field is `RunDefinableG`, NOT the in-tree `RunDefinable` — see header
lesson 4 (the in-tree bundle is unsatisfiable for gas/call programs). -/
structure WellLowered (prog : Program) : Prop where
  /-- The folded structural side-conditions (`MatFueled` + pc/offset bounds + slot
  registration) of the `_lowered` wrappers. -/
  wf : Lir.WellFormedLowered prog
  /-- Gas/call-aware operand definability (replaces the unsatisfiable `RunDefinable`). -/
  defs : RunDefinableG prog
  /-- The entry block is block 0 (its leading `JUMPDEST` is byte 0 = the entry frame's pc). -/
  entry0 : prog.entry.idx = 0
  /-- Static CFG closure (entry/jump/branch presence + offset bounds). -/
  closed : ClosedCFG prog
  /-- The static per-cursor stack-room folds. -/
  stack : StackRoomOK prog

/-- A frame reachable from the call's entry frame: `beginCall params` began a frame and
`Runs` reaches `fr'` from it. The quantifier shape `PrecompileSeams.callsCode` needs (and
exactly the `hcc` shape `cleanHalts_of_runWithLog` consumes, once `hbegin` is split off).
The fleet sketch named this `ReachableFrom` without defining it; this is the definition. -/
def ReachableFrom (params : CallParams) (fr' : Frame) : Prop :=
  ∃ fr₀, beginCall params = .inl fr₀ ∧ Runs fr₀ fr'

/-- **The honest oracle seams** (the flagship's `hseams`) — the precompile boundary, both
faces. `noErase` is verbatim the `hprec` hypothesis of `callPreservesSelf_modGuards`
(a live precompile's `.inr` result map genuinely can erase accounts — opaque, honestly
supplied; vacuous for non-precompile-targeting programs). `callsCode` is the reachable-CALL
targets-code residual (`V2/Modellable.lean`; NOT a lowering property — an IR call whose
callee materialises a precompile address would violate it; vacuous for call-free programs).
SUPPLIED status: the irreducible seam structure — both fields are satisfiable and
non-vacuous, and neither is dischargeable from the program text. (`prog` is carried for
signature stability — a future refinement scopes `callsCode` by the program's call sites.) -/
structure PrecompileSeams (prog : Program) (params : CallParams) : Prop where
  /-- Precompile no-erase (`hprec`): an immediate `.inr` result preserves account presence. -/
  noErase : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
    ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts
  /-- Every reachable frame's CALLs target code accounts, never a precompile. -/
  callsCode : ∀ fr', ReachableFrom params fr' → CallsCode fr'

/-- **The single-CALL scope premise** (the flagship's `hsingle`): the program text contains
at most one `Stmt.call`. FORCED by `callOracleOf` reading only the head `CallRecord`
(`V2/RunLog.lean`): the function-shaped `CallOracle` cannot distinguish two dynamic calls
with identical IR-visible inputs but different EVM outcomes. R3′ records the tracked
generalization decision (calls as a consumed stream, mirroring the gas channel).
NOTE (recorded, not enforced here): a syntactically-single call INSIDE A LOOP can still
fire dynamically more than once; the R10/R11 grind must confirm the loop-free-call or
strengthen this premise — tracked with R3′. SUPPLIED status: static, decidable. -/
def SingleCall (prog : Program) : Prop :=
  (prog.blocks.toList.map (fun b =>
    (b.stmts.filter (fun s => match s with | .call _ => true | _ => false)).length)).sum ≤ 1

/-- **Gas-introspection-free scope** (the co-flagship's `hng`): no statement reads `.gas`.
Static, decidable. Under it the realised gas stream plays no role (companion sorry:
`realisedGas_nil_of_noGasReads`), so the co-flagship needs no R1 — the de-risking
checkpoint (target-architecture decision 2). -/
def NoGasReads (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ (pc : Nat) (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) → e ≠ .gas

/-- **The nonzero-SSTORE scope seam** (the flagship's `hnzw`; header scope-seam 2): every
`Runs`-reachable frame sitting at an SSTORE opcode with operands `kw :: vw :: rest` on the
stack writes a nonzero value. Needed because `sim_sstore_stmt`'s `hnz : vw ≠ 0` is the
nonzero-write scope of `EvalStmt.sstore` (zero writes are out of the current simulation's
scope). `Runs`-monotone (a suffix frame's reachable set is a subset), so the walk threads it
(`DriveCorrLog.nonzeroSstores`). SUPPLIED status: honest scope seam; tracked decision —
either extend `sim_sstore` to zero writes or record SSTOREs in the log. The op/stack shapes
mirror `sim_sstore_stmt`'s `hdop`/stack facts verbatim. -/
def NonzeroSstores (fr₀ : Frame) : Prop :=
  ∀ (fr' : Frame) (kw vw : Word) (rest : Stack Word),
    Runs fr₀ fr' →
    decode fr'.exec.executionEnv.code fr'.exec.pc = some (.Smsf .SSTORE, .none) →
    fr'.exec.stack = kw :: vw :: rest → vw ≠ 0

/-! ## §2 — The recorder-restart coupling (the hard design piece)

The tie reshape's carrier (target-architecture §3, SETTLED as option (i)): instead of the
free-`∀` value variables, the walk invariant carries ONE real coupling field — *restarting
the recording interpreter at the current top-level boundary frame reproduces the run's final
observable and exactly the un-consumed suffixes of the recorded streams*. The tie value
conjuncts then pin themselves to the SUFFIX HEAD, which the antecedent (restart determinism)
links to the run — no free variable survives.

Design notes (each load-bearing):

* **`restart` is the load-bearing field**: `driveLog` is a deterministic function, so a
  restart equation from `fr` pins the suffixes AND `log.observable` simultaneously — an
  adversarial `(fr, suffix)` pair must actually reproduce the recorded future, which is
  what makes the R1-style head equations derivable rather than refutable.
* The restart uses pending stack `[]` because coupling is stated at TOP-LEVEL boundary
  frames only (`Corr.stack_nil` cursors) — the same `stack.isEmpty` gate `driveLog` records
  under.
* **Child calls are black-boxed correctly**: a descended CALL's internal GAS/SLOAD reads are
  invisible to the restart exactly as to the original recording (the `stack.isEmpty` gate),
  so `recorderCoupled_call` consumes exactly one `CallRecord` and NO gas/sload entries.
* **Cyclic-correct**: a loop revisits the same cursor with different gas; the coupling is
  indexed by the FRAME (whose gas differs per visit), never by the cursor — no per-cursor
  value function anywhere (the fatal flaw of the rejected option (iii)).
* The three prefix fields make "consumed so far" explicit (the R10 assembly reads them);
  the entry instance is the whole log with `pre = []` (`recorderCoupled_entry`). -/

/-- **Recorder-restart coupling.** Restarting the recording interpreter at the current
top-level boundary frame `fr` reproduces the run's final observable and exactly the
un-consumed suffixes of the recorded streams; each suffix is genuinely a suffix of its
recorded stream. SUPPLIED status: never supplied to the flagship — R7 establishes it at
entry and preserves it across steps/calls; the ties CONSUME it as an antecedent. -/
structure RecorderCoupled (log : RunLog) (fr : Frame)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) : Prop where
  /-- The load-bearing restart equation: some fuel replays `fr`'s future to exactly
  `(log.observable, gasSuffix, sloadSuffix, callSuffix)`. -/
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] []
      = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix)
  /-- The gas suffix is a suffix of the recorded gas stream. -/
  gasPrefix : ∃ pre, log.gas = pre ++ gasSuffix
  /-- The sload suffix is a suffix of the recorded sload stream. -/
  sloadPrefix : ∃ pre, log.sloads = pre ++ sloadSuffix
  /-- The call suffix is a suffix of the recorded call stream. -/
  callPrefix : ∃ pre, log.calls = pre ++ callSuffix

/-- **The recoupled walk invariant** — the future replacement of `DriveCorrPlus`'s four
dead accumulator lists (which are NOT edited here; Phase 3 proper swaps them). Carried at
every top-level block-entry boundary of the drive walk:

* `corr`/`cleanHalts` — the existing `DriveCorr` content (the cursor + the non-exception
  scope), with the phantom `obs` parameter pinned to `0` (audit-confirmed unused by `Corr`;
  slated for deletion in the Phase-3 reshape — NOT deleted here, no edits to existing files);
* `present` — the reached label is present (R8's consumer; kills the inside-out `hpresent`);
* `selfPresent`/`addrPin`/`kindPin` — decision-4's rfl-preserved companions: they are what
  KILLS the unsatisfiable `TermTies` stop/ret address/kind/nonempty conjuncts (those demands
  become antecedents supplied by this invariant, and non-emptiness is DERIVED via
  `accounts_ne_empty_of_selfPresent`);
* `nonzeroSstores` — the threaded scope seam (entry-seeded from the flagship's `hnzw`,
  preserved by `Runs`-monotonicity); it supplies the sstore arm's antecedent;
* `coupled` — the §2 recorder coupling at the un-consumed suffixes.

SUPPLIED status: never supplied — established at entry (R7 entry + `entry_corr` +
`selfPresent_codeFrame`) and preserved by the walk (R7 edges + `stepPreservesSelf` +
`callPreservesSelf_modGuards hprec`). -/
structure DriveCorrLog (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog)
    (self : AccountAddress) (st : IRState) (fr : Frame) (L : Label)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) :
    Prop where
  /-- The `Corr` boundary at the block-entry cursor `(L, 0)` (phantom `obs` pinned to 0). -/
  corr : Lir.Corr prog sloadChg 0 st fr L 0
  /-- The non-exception clean-halt scope from this boundary on. -/
  cleanHalts : CleanHaltsNonException fr
  /-- The reached label is present (R8 threads it; seeded from `ClosedCFG.entry_present`). -/
  present : ∃ b, blockAt prog L = some b
  /-- The self account is present (seeded by the flagship's `hself`; preserved by
  `stepPreservesSelf` / `callPreservesSelf_modGuards`). -/
  selfPresent : SelfPresent fr
  /-- The frame executes at the self address (rfl-preserved along the walk). -/
  addrPin : fr.exec.executionEnv.address = self
  /-- The frame is a call frame (rfl-preserved along the walk). -/
  kindPin : ∃ cp, fr.kind = .call cp
  /-- The threaded nonzero-SSTORE scope seam (entry-seeded from `hnzw`; `Runs`-monotone). -/
  nonzeroSstores : NonzeroSstores fr
  /-- The §2 recorder-restart coupling at the un-consumed suffixes. -/
  coupled : RecorderCoupled log fr gasSuffix sloadSuffix callSuffix

end Lir.V2
