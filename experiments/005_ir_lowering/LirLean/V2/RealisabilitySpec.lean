import LirLean.V2.Drive.Headline

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
7. **NEW (independent review drill): `SingleCall` is syntactic but the realised oracle is
   dynamic.** `callOracleOf` replays only the HEAD `CallRecord`, so a syntactically-single
   call inside a loop that fires per iteration with differing child outcomes refutes
   R3/`Conforms` at the second iteration — the loop caveat previously recorded only as a
   docstring note, i.e. not a hypothesis. Fixed with the decidable LOG-side premise
   `hone : log.calls.length ≤ 1` on R3/R10a and all three flagships — exactly the domain
   on which the head-projection oracle is correct.
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
of the since-deleted `lower_conforms_wf` BY DEFINITION — the entry world *is* the params' lens (the pin is
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

/-- **Static `defsOf`-cursor consistency** (header lesson 6 — the review drill's shadowing
hole). Every def-site in the program text agrees with `defsOf`'s registration for its
target: a pure assign registers its own RHS; a gas/sload assign and a call result register
the spill slot `.slot (slotOf t)`.

GROUND TRUTH this pins (`Lowering.lean`): `defsOf` is a **FIRST-find over program order**
(`pairs.find?` returns the first match — NOTE its docstring says "the last assign", a
discrepancy flagged for a Wave-4 sweep; that file is not this track's edit surface), while
`emitStmt` keys its spill stash on `defsOf t`. A tmp redefined with mixed pure/spill defs
(e.g. `[.assign t (.imm 1), .assign t .gas]`) therefore emits NO GAS byte at the shadowed
def while `EvalStmt.assignGas` still demands a gas-stream head — the flagship refutation of
header lesson 6. This field excludes exactly that mismatch (including pure/pure shadowing
with a DIFFERENT RHS, which breaks recompute-on-use the same way); single-assignment
programs (`exProg`) satisfy it trivially, so benign programs stay in scope. It is the
static lift of the per-cursor `hself` side condition the DefsSound walk already consumes
(`defsSound_preserved_assignPure`, `DefsSound.lean:269`). SUPPLIED status: static,
decidable per program (the R9 checker's territory). -/
def DefsConsistent (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat), blockAt prog L = some b →
    (∀ (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) →
      defsOf prog t = some (match e with
        | .gas => .slot (slotOf t)
        | .sload _ => .slot (slotOf t)
        | e' => e'))
    ∧ (∀ (cs : CallSpec) (t : Tmp), b.stmts[pc]? = some (.call cs) → cs.resultTmp = some t →
      defsOf prog t = some (.slot (slotOf t)))

/-! ### Shadowing-aware scoping (header lesson 8 — the round-3 reshape)

`Lir.StepScoped`'s live-scope clause is a free-∀ over the CURRENT live set ("no bound
tmp's registered def reads the assign target") — define-before-use, which a LOOP violates
by construction on its second iteration (rebinding with live dependents; `exProg` block 1).
The shadowing-aware replacement (design route (i), carrier shape (b) — an explicit
invalidation set):

* `ReadsOf` — the STATIC registered-reader relation;
* `invalStep` — the per-statement invalidation-set transfer: rebinding `t` invalidates
  every registered reader of `t`; the rebound `t` itself is re-validated (unless its own
  def reads it). Liveness-INSENSITIVE by design: invalidating a reader that is not even
  bound is harmless (the invariant below claims nothing about unbound tmps), and it keeps
  the transfer a pure function of the program text and the statement — no state parameter,
  which is what makes the R0b preservation lemma side-condition-free;
* `DefsSoundS` — `DefsSound` restricted to the complement of the invalidation set: a
  stale-but-unused binding is CLAIMED NOTHING ABOUT until its reassign re-validates it
  (mid-block staleness of a bound-but-unused dependent is harmless to the lowered code:
  rematerialisation is exercised only at USE sites);
* `StepScopedS` — the static residue of `Lir.StepScoped` once the live-scope clauses move
  into the invalidation bookkeeping: state-FREE, derivable from `WellLowered`
  (`defsCons` + cursor membership), hence immune to the lesson-8 refutation;
* `RevalidatesPerBlock` — the static boundary criterion the R0b reshape rests on: folding
  `invalStep` over any present block's statements from the empty set lands back on the
  empty set, so the strong `DefsSound` (= `DefsSoundS` at `∅`, `defsSoundS_empty_iff`) is
  re-established at every block boundary — exactly where the ties consume `Corr`.

**Why carrier shape (b) over shape (a)** (a "validSince"/not-invalidated-since-binding
predicate over the walk): validity-since-binding is HISTORY-indexed — it cannot be stated
on a single `(prog, st)` pair without walk data, so it would carry the same set implicitly;
making the set explicit data with a STATIC transfer function costs one definition and buys
(i) a preservation lemma with no per-state side conditions (R0b — the live-scope demands
are gone, not relocated into hypotheses), and (ii) a decidable-in-principle boundary
criterion (`RevalidatesPerBlock`, the R9 checker's territory). A SEMANTIC invalidation
predicate ("live but stale") is NOT an option: it would make the scoped invariant a
tautology ("every non-stale binding recomputes"). -/

/-- `t'` is a **registered reader** of `t`: `t'`'s `defsOf`-registered def reads `t`.
Static (a fact of the program text); the invalidation unit of `invalStep`. -/
def ReadsOf (prog : Program) (t t' : Tmp) : Prop :=
  ∃ e', defsOf prog t' = some e' ∧ usesInExpr t e' ≠ 0

/-- **The invalidation-set transfer** of one statement. Rebinding `t` (an assign target or
a call result) invalidates every registered reader of `t`; `t` itself is re-validated by
the rebind (unless its own def reads it — a self-reading target stays invalid, harmlessly:
recompute-on-use never reproduces it, and no side condition is demanded anywhere).
`sstore` and result-free calls transfer the set unchanged: a world write invalidates NO
registered recompute — `defsOf` never registers a `.sload` (gas/sload/call results are all
routed to `.slot`, `Lowering.lean`), so no registered def reads the world. -/
def invalStep (prog : Program) (I : Tmp → Prop) : Stmt → (Tmp → Prop)
  | .assign t e => fun t' =>
      if t' = t then usesInExpr t e ≠ 0 else (I t' ∨ ReadsOf prog t t')
  | .sstore _ _ => I
  | .call cs =>
      match cs.resultTmp with
      | some t => fun t' => if t' = t then False else (I t' ∨ ReadsOf prog t t')
      | none => I

/-- **Shadowing-aware recompute soundness**: `Lir.DefsSound` restricted to the tmps
OUTSIDE the invalidation set `I`. A stale-but-unused dependent (inside `I`) is claimed
nothing about — the lesson-8 repair: the un-scoped `DefsSound` is FALSE at `exProg`'s
real mid-block loop-exit states (`not_defsSound_stale`), while `DefsSoundS` at the
`invalStep`-threaded set is preserved with no per-state side conditions (R0b). -/
def DefsSoundS (prog : Program) (I : Tmp → Prop) (st : IRState) : Prop :=
  ∀ (t : Tmp) (e : Expr) (w : Word),
    defsOf prog t = some e → ¬ Lir.NonRecomputable prog t → ¬ I t →
    st.locals t = some w → some w = evalExpr st 0 e

/-- At the EMPTY invalidation set, `DefsSoundS` is exactly the strong `DefsSound` — the
bridge between the mid-block scoped invariant and the block-boundary `Corr.defsSound` the
ties consume. PROVED (not debt). -/
theorem defsSoundS_empty_iff (prog : Program) (st : IRState) :
    DefsSoundS prog (fun _ => False) st ↔ Lir.DefsSound prog st :=
  ⟨fun h t e w hd hn hl => h t e w hd hn not_false hl,
   fun h t e w hd hn _ hl => h t e w hd hn hl⟩

/-- **The static per-step scoping residue** — `Lir.StepScoped` minus the refutable
live-scope clauses (which moved into the invalidation bookkeeping) and minus pure-assign's
`usesInExpr t e = 0` self-read clause (absorbed: a self-reading rebind leaves its target
in the invalidation set instead of demanding a side condition). State-FREE: every clause
is a fact of the program text — the registration clause from `DefsConsistent` at the
cursor, `isGasDef`/`isSloadDef`/`isCallResult` from cursor membership, and the sstore
clause from `defsOf`'s structure (it never registers a `.sload`; true of ALL programs,
the `defsOf_ne_gas` twin). DERIVED status inside the ties: computable from `hwl` + the
cursor, never a live-set demand. -/
def StepScopedS (prog : Program) : Stmt → Prop
  | .assign t e =>
      (e ≠ .gas → (∀ key, e ≠ .sload key) → defsOf prog t = some e)
      ∧ (e = .gas → Lir.isGasDef prog t)
      ∧ (∀ key, e = .sload key → Lir.isSloadDef prog t)
  | .sstore _ _ =>
      ∀ (t₀ : Tmp) (e₀ : Expr), defsOf prog t₀ = some e₀ → ∀ key, e₀ ≠ .sload key
  | .call cs => ∀ t, cs.resultTmp = some t → Lir.isCallResult prog t

/-- **The per-block boundary re-validation criterion** (R0b's static half): folding the
invalidation transfer over any present block's statements from the EMPTY set lands back
on the empty set — every within-block invalidation is healed by a reassign before the
block ends, so the strong `DefsSound` is re-established at every block boundary (where
the ties consume `Corr.defsSound`). Static; decidable in principle once the tmp universe
is listed (the `Tmp → Prop` fold gets a `List Tmp` executable twin in the R9 checker).
TRUE of `exProg` (`revalidatesPerBlock_exProg`). -/
def RevalidatesPerBlock (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ t', ¬ (b.stmts.foldl (invalStep prog) (fun _ => False)) t'

/-- **The shadowing-aware CALL realisability tie** — `Lir.CallRealises`
(`LowerConforms.lean:261`) with its embedded `Lir.StepScoped prog st0 (.call cs)`
conjunct replaced by the static `StepScopedS prog (.call cs)` (header lesson 8: the
embedded live-scope clause for the result tmp is refutable WITHIN the R10a hypothesis
envelope for any `WellLowered` program whose call result has a registered reader — not
at `exProg` itself, whose `t5` has none, but the disease shape is identical). Everything
else is VERBATIM the in-tree kernel: the realised `(result, pd)` oracle pinning, the
arg-push run + its pins, the returning `CallReturns` + resume-frame pins, the post-state
scoping fold (derivable: prior-live tmps from the `Corr` antecedent's `wellScoped`,
locals untouched by the world swap; the result tmp from `DefsConsistent`'s call clause),
and the Route-B tail. The `obs` phantom is pinned to `0` (as everywhere in this file).
The copy is deliberate, recorded Phase-3 unification debt: the R0b reshape re-plumbs
`sim_call_stmt`'s input to this form and retires the in-tree original (this track edits
no existing files). -/
def CallRealisesS (prog : Program) (sloadChg : Tmp → ℕ) (o : V2.CallOracle)
    (L : Label) (_b : Block) (pc : Nat) (cs : CallSpec) (st0 : IRState) (fr0 : Frame) :
    Prop :=
  Lir.Corr prog sloadChg 0 st0 fr0 L pc →
  ∃ (result : Evm.CallResult) (pd : Evm.PendingCall) (callFr resumeFr : Frame)
      (argsLen : Nat),
    -- the STATIC per-step scoping of the call statement (lesson 8; was `StepScoped`):
    StepScopedS prog (.call cs)
    -- the realised oracle pinning (so the abstract call step is the realised one):
    ∧ o = evmV2CallOracle result pd fr0.exec.executionEnv.address
    -- the arg-push run + its pins (the realised arg materialisation):
    ∧ argsLen = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
        ++ materialise (defsOf prog) (recomputeFuel prog) cs.callee
        ++ materialise (defsOf prog) (recomputeFuel prog) cs.gasFwd).length
    ∧ Runs fr0 callFr
    ∧ callFr.exec.pc = fr0.exec.pc + UInt32.ofNat argsLen
    ∧ callFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory
    ∧ fr0.exec.toMachineState.activeWords.toNat ≤ callFr.exec.toMachineState.activeWords.toNat
    -- the returning external CALL + realised resume:
    ∧ CallReturns callFr resumeFr
    ∧ resumeFr = Evm.resumeAfterCall result pd
    ∧ resumeFr.exec.executionEnv.address = fr0.exec.executionEnv.address
    ∧ resumeFr.exec.executionEnv.code = lower prog
    ∧ resumeFr.exec.executionEnv.canModifyState = true
    ∧ resumeFr.exec.pc = callFr.exec.pc + 1
    ∧ resumeFr.exec.stack = callSuccessFlag result pd :: []
    ∧ resumeFr.exec.toMachineState.memory = callFr.exec.toMachineState.memory
    ∧ callFr.exec.toMachineState.activeWords.toNat
        ≤ resumeFr.exec.toMachineState.activeWords.toNat
    ∧ resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0
    -- the post-state scoping fold (derivable — see the docstring):
    ∧ (∀ t, (match cs.resultTmp with
              | some t' => { st0 with world := fun key =>
                              evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }.setLocal
                              t' (callSuccessFlag result pd)
              | none   => { st0 with world := fun key =>
                              evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }).locals t ≠ none →
            (¬ Lir.NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
            ∧ defsOf prog t ≠ none)
    -- the Route-B tail's realisability (decode anchors + gas + memory-expansion witness):
    ∧ (∀ flag : Word, resumeFr.exec.stack = flag :: [] →
        (∀ (t : Tmp), cs.resultTmp = some t →
          (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
          ∧ ∃ endFr,
              Runs resumeFr endFr
            ∧ endFr.exec.toMachineState.memory
                = (resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag).memory
            ∧ endFr.exec.toMachineState.activeWords
                = (resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag).activeWords
            ∧ endFr.exec.pc = resumeFr.exec.pc + UInt32.ofNat 34
            ∧ endFr.exec.executionEnv.code = resumeFr.exec.executionEnv.code
            ∧ endFr.validJumps = resumeFr.validJumps
            ∧ endFr.exec.executionEnv.address = resumeFr.exec.executionEnv.address
            ∧ endFr.exec.executionEnv.canModifyState = resumeFr.exec.executionEnv.canModifyState
            ∧ (∀ k, selfStorage endFr k = selfStorage resumeFr k)
            ∧ endFr.exec.stack = [])
        ∧ (cs.resultTmp = none →
            Runs resumeFr (popFrame resumeFr [])))

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
  /-- Static `defsOf`-cursor consistency (header lesson 6): every def-site agrees with
  `defsOf`'s first-find registration — excludes the spill-stash/shadowing mismatch that
  refutes the flagship (`RunDefinableG` alone does NOT: its gas arm is unconditionally
  true, which is what opened the hole). -/
  defsCons : DefsConsistent prog
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
signature stability — a future refinement scopes `callsCode` by the program's call sites.)
NON-VACUITY GUARD: `noErase` quantifies over ALL `CallParams` (a global engine fact), so
the flagship's whole hypothesis set is satisfiable only if the current exp003 `beginCall`
precompile stub actually preserves account presence — R12a deliberately DOUBLES as the
machine-check of that engine fact (its `PrecompileSeams exProg params` conjunct); a failure
there is diagnosed as a SEAM problem with the engine stub, not an `exProg` problem. -/
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
LOOP CAVEAT, CLOSED AT THE THEOREM SURFACE (header lesson 7): a syntactically-single call
INSIDE A LOOP can still fire dynamically more than once, and the head-projection oracle is
then wrong from the second firing on. This def stays syntactic; the DYNAMIC at-most-one
premise is the separate decidable log-side hypothesis `hone : log.calls.length ≤ 1`
carried by R3/R10a and the flagships (read off the run like `hclean`; satisfied by
`exProg`, whose call sits outside the loop). SUPPLIED status: static, decidable. -/
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
links to the run — no free VALUE variable survives. (The SCOPING conjuncts carried their own
copy of the disease, invisible to this §: the round-3 repair is header lesson 8 / `StepScopedS`.)

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

/-! ## §3 — The reshaped ties `StmtTies'` / `TermTies'` (R0 as statements; no free value-∀)

The five statement arms and four terminator arms of the former `StmtTies`/`TermTies`
(since-deleted; formerly `LowerConforms.lean:1273-1423`), re-stated so that every formerly-free
value variable is pinned by an antecedent:

* every arm's antecedent block is: cursor statement + `Corr` (phantom `obs := 0`) +
  `RecorderCoupled` + `CleanHaltsNonException`; the suffix variables are ∀-bound but
  antecedent-pinned through the (deterministic) restart equation — an adversarial witness
  must reproduce the recorded future, which is what makes the value conclusions derivable;
* the gas arm's free `ob = …` equation becomes `gS.head? = some …` (R1 supplies it);
* the sload arm's free `w` becomes the antecedent-pinned `st0.world kv` under
  `st0.locals k = some kv` (the planned `∃ w, evalExpr … = some w` conclusion was itself
  refutable by an empty-locals `Corr` witness — header lesson 5 — so the key binding is an
  antecedent, exactly as the sstore arm's operand bindings always were);
* the plain-assign arm's free `st0'` becomes the pinned post-state `st0.setLocal t w` under
  the `evalExpr st0 0 e = some w` antecedent (the `EvalStmt.assignPure` hypothesis), and the
  arm no longer fires on `.gas`/`.sload` (killing the static contradiction with `defsOf`'s
  spilling);
* the sstore arm DROPS `∃ acc, SstoreRealises fr0 kw vw acc` entirely (header lesson 3 —
  unsatisfiable); its content returns point-wise at the concrete frame (R4). Its `vw ≠ 0`
  conclusion is kept but under the threaded `NonzeroSstores fr0` antecedent (without it, an
  adversarial coupled zero-writing frame refutes the conclusion — the log does not record
  SSTOREs, so the coupling alone cannot pin the written value);
* the `TermTies` stop/ret address/kind demands become ANTECEDENTS (supplied by
  `DriveCorrLog`'s rfl-preserved pins), and non-emptiness is the only stop conclusion
  (derivable via `accounts_ne_empty_of_selfPresent`); the ret arm's bare
  `∃ vw, st'.locals t = some vw` conclusion is DROPPED (refutable by an empty-locals `Corr`
  witness; at real states `RunDefinableG.ret_def` supplies it) — the epilogue block is
  stated under the `∀ vw`-antecedent it always had, now strengthened with an explicit pc
  pin (`frv.pc = frT.pc + |materialise t|`) so its decode conclusions are static
  `DecodeAnchors` facts rather than claims about every stack-coincident frame;
* the jump/branch gas-guard conclusions are kept verbatim but now under the
  `CleanHaltsNonException frT` antecedent, which blocks the zero-gas refutation (skeptic
  sub-claim 4's strengthening) and makes them derivable by the
  `jump_landing_of_cleanHalt`/`branch_landing_of_cleanHalt` extractors;
* successor-presence conjuncts are gone from the ties (they live in `ClosedCFG`; the
  jump/branch arms take presence as antecedents, supplied by the walk from R8);
* **(round 3, header lesson 8)** every `Lir.StepScoped` conclusion (arms 1–4) is replaced
  by the static `StepScopedS`, and the call arm's `Lir.CallRealises` by `CallRealisesS`:
  the embedded live-scope clauses ("no bound tmp's registered def reads the target") were
  refutable at `exProg`'s own second loop iteration — block 1, pc 0 (`t6 := gas` vs the
  live `t8 ↦ lt t6 t7`) and pc 1 (`t7 := 1000` vs the same `t8`) — at real on-run states
  consistent with every antecedent. Staleness accounting moved to the invalidation set
  (`invalStep`/`DefsSoundS`, R0b); the ties now claim only the static residue.

SUPPLIED status of both defs: never supplied to the flagship — R10 BUILDS them from the
run (`stmtTies'_of_runWithLog`/`termTies'_of_runWithLog`). PRECISION NOTE on the arms'
conclusions (the round-2 review's overclaim fix — they are NOT all "computed from `fr0`
and restart determinism"): each conclusion is one of (i) a static fact of `prog`,
derivable from `hwl` + the cursor (the `StepScopedS`/registration/canonicity/
addressability/stack-fold/pc-bound conjuncts), (ii) a fact carried over from the arm's
own antecedents (the `setLocal`-scoping folds from `Corr.wellScoped` + `DefsConsistent`;
the post-assign `MemRealises` from `Corr.memAgree`; the sstore `vw ≠ 0` from the threaded
`NonzeroSstores` seam), or (iii) a value/trace fact computed from `fr0`/`frT` + restart
determinism under the clean-halt antecedent (the `gS.head?` equation, the CALL kernel,
the gas guards, the epilogue anchors). No conclusion depends on a variable that is not
antecedent-pinned or static — that is the honest residue of the "no free-∀" slogan. -/

/-- **The reshaped per-block STATEMENT ties** (the R0 statement-side). See the section
docstring for the reshape rationale, arm by arm. `self` is consumed by the call arm's
realised-oracle pin. DERIVED (R10): built from `hrun`/`hclean`/`hseams` + `WellLowered` +
`SingleCall`; never supplied. -/
def StmtTies' (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog)
    (self : AccountAddress) (L : Label) (b : Block) : Prop :=
  -- (1) plain assign (neither `.gas` nor `.sload _`): post-state PINNED by the `evalExpr`
  -- antecedent; conclusions are the not-spilled fact, the STATIC per-step scoping
  -- (`StepScopedS`, lesson 8), and the pinned-post-state scoping/memory ties.
  (∀ (pc : Nat) (t : Tmp) (e : Expr) (w : Word) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t e) →
      e ≠ .gas → (∀ k, e ≠ .sload k) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      evalExpr st0 0 e = some w →
      (∀ n, defsOf prog t ≠ some (.slot n))
      ∧ StepScopedS prog (.assign t e)
      ∧ (∀ t', (st0.setLocal t w).locals t' ≠ none →
            (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
            ∧ defsOf prog t' ≠ none)
      ∧ Lir.MemRealises prog (st0.setLocal t w) fr0)
  -- (2) spilled sload assign: the key binding is an ANTECEDENT (`kv`), the read value is
  -- the storage lens at `kv` (definitional under the antecedent), the post-state is pinned.
  -- Slot registration/canonicity, addressability, the stack-room fold (sourced from
  -- `StackRoomOK.sloadKey` + `Corr.stack_nil`) and the activeWords-flatness stay.
  ∧ (∀ (pc : Nat) (t k : Tmp) (kv : Word) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t (.sload k)) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      st0.locals k = some kv →
      defsOf prog t = some (.slot (slotOf t))
      ∧ StepScopedS prog (.assign t (.sload k))
      ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
      ∧ evalExpr st0 0 (.sload k) = some (st0.world kv)
      ∧ (∀ t', (st0.setLocal t (st0.world kv)).locals t' ≠ none →
            (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
            ∧ defsOf prog t' ≠ none)
      ∧ (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
      ∧ fr0.exec.stack.size
          + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k)).length ≤ 1024
      ∧ (∀ frk : Frame,
          Lir.MatRuns (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k) kv fr0 frk →
          frk.exec.toMachineState.activeWords = fr0.exec.toMachineState.activeWords))
  -- (3) spilled gas assign — THE R1 CONJUNCT: the un-consumed gas suffix's HEAD is the
  -- machine GAS output at this frame (replaces the free-`ob` equation; the coupling +
  -- clean-halt antecedents make it derivable, R1). Post-state scoping is over the pinned
  -- head value. Slot registration/canonicity/addressability/pc-bound stay.
  ∧ (∀ (pc : Nat) (t : Tmp) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t .gas) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      defsOf prog t = some (.slot (slotOf t))
      ∧ StepScopedS prog (.assign t .gas)
      ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
      ∧ gS.head? = some (UInt256.ofUInt64
          (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))
      ∧ (∀ t', (st0.setLocal t (UInt256.ofUInt64
              (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))).locals t' ≠ none →
            (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
            ∧ defsOf prog t' ≠ none)
      ∧ ((slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ pcOf prog L pc + 34 < 2 ^ 32))
  -- (4) sstore: `StepScopedS` + the stack-room fold + `vw ≠ 0` — the latter ONLY under the
  -- threaded `NonzeroSstores fr0` antecedent (see section docstring). The unsatisfiable
  -- `∃ acc, SstoreRealises …` conjunct is GONE (its content is R4, point-wise).
  ∧ (∀ (pc : Nat) (key value : Tmp) (kw vw : Word) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.sstore key value) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      NonzeroSstores fr0 →
      st0.locals key = some kw → st0.locals value = some vw →
      StepScopedS prog (.sstore key value)
      ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
          + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024
      ∧ vw ≠ 0)
  -- (5) call: `CallRealisesS` at the realised oracle (lesson 8: the in-tree
  -- `CallRealises` embeds `StepScoped (.call cs)`, whose live-scope clause is refutable
  -- in-envelope for reader-carrying programs), kept shape-wise (it is itself
  -- `Corr → ∃ …`), under the coupling/clean-halt/address antecedents — without the
  -- clean halt an adversarial OOG-at-CALL frame refutes the `CallReturns` existential; the
  -- address pin is what lets `realisedCall log self` coincide with
  -- `evmV2CallOracle … fr0.address`. The head-of-`callSuffix` pinning arrives via R3
  -- under `SingleCall`.
  ∧ (∀ (pc : Nat) (cs : CallSpec) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.call cs) →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      fr0.exec.executionEnv.address = self →
      CallRealisesS prog sloadChg (realisedCall log self) L b pc cs st0 fr0)

/-- **The reshaped per-block TERMINATOR ties** (the R0 terminator-side). See the section
docstring: address/kind/self-presence demands are ANTECEDENTS (supplied by `DriveCorrLog`),
all gas guards sit under `CleanHaltsNonException`, the ret epilogue's inner `∀ frv` is
`Runs`+pc-pinned (never free), successor presence lives in `ClosedCFG`. `log` is carried
for signature stability with `StmtTies'` (the deferred RETURN-value channel will consume
it). DERIVED (R5/R10): built from the walk invariant; never supplied. -/
def TermTies' (prog : Program) (sloadChg : Tmp → ℕ) (_log : RunLog)
    (self : AccountAddress) (L : Label) (b : Block) : Prop :=
  -- (stop) non-emptiness only — derivable from the `SelfPresent` antecedent
  -- (`accounts_ne_empty_of_selfPresent`); the old address/kind demands are antecedents now.
  (b.term = .stop →
      ∀ (st' : IRState) (frT : Frame),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        SelfPresent frT →
        frT.exec.executionEnv.address = self →
        (∃ cp, frT.kind = .call cp) →
        ¬ (frT.exec.accounts == ∅) = true)
  -- (ret) the charge envelope (clean-halt-derived) + the pc-pinned RETURN epilogue block.
  ∧ (∀ t, b.term = .ret t →
      ∀ (st' : IRState) (frT : Frame),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        SelfPresent frT →
        frT.exec.executionEnv.address = self →
        (∃ cp, frT.kind = .call cp) →
        (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
            ≤ frT.exec.gasAvailable.toNat
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
        ∧ (∀ (vw : Word), st'.locals t = some vw →
            ∀ frv : Frame, Runs frT frv →
            frv.exec.executionEnv.code = frT.exec.executionEnv.code →
            frv.exec.executionEnv.address = frT.exec.executionEnv.address →
            (∀ k, selfStorage frv k = selfStorage frT k) →
            frv.exec.stack = vw :: frT.exec.stack →
            frv.exec.pc = frT.exec.pc + UInt32.ofNat
              (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length →
            ∃ cp,
              decode frv.exec.executionEnv.code frv.exec.pc
                  = some (.Push .PUSH32, some ((0 : Word), 32))
              ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
                  = some (.Push .PUSH32, some ((0 : Word), 32))
              ∧ decode frv.exec.executionEnv.code
                    (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
                  = some (.System .RETURN, .none)
              ∧ 3 ≤ frv.exec.gasAvailable.toNat
              ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
              ∧ frv.kind = .call cp
              ∧ ¬ (frv.exec.accounts == ∅) = true))
  -- (jump) the 3-step gas guards, now under the clean-halt antecedent (derivable via
  -- `jump_landing_of_cleanHalt`); destination presence is an antecedent (from `ClosedCFG`).
  ∧ (∀ dst bdst, b.term = .jump dst →
      prog.blocks.toList[dst.idx]? = some bdst → dst.idx < prog.blocks.size →
      ∀ (st' : IRState) (frT : Frame),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        3 ≤ frT.exec.gasAvailable.toNat
        ∧ GasConstants.Gmid ≤ (pushFrameW frT
            (UInt256.ofNat
              ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
            4).exec.gasAvailable.toNat
        ∧ GasConstants.Gjumpdest
            ≤ (jumpFrame (pushFrameW frT
                (UInt256.ofNat
                  ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
                  4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                frT.exec.stack).exec.gasAvailable.toNat)
  -- (branch) the cond-materialise `MatRuns` existence + 6 gas guards, verbatim from the
  -- current tie but under the clean-halt antecedent (derivable via
  -- `branch_landing_of_cleanHalt` + `materialise_runs_of_cleanHalt`); the condition value
  -- `cw` was always antecedent-pinned; target presence is an antecedent (from `ClosedCFG`).
  ∧ (∀ cond thenL elseL bthen belse, b.term = .branch cond thenL elseL →
      prog.blocks.toList[thenL.idx]? = some bthen →
      prog.blocks.toList[elseL.idx]? = some belse →
      thenL.idx < prog.blocks.size → elseL.idx < prog.blocks.size →
      ∀ (st' : IRState) (frT : Frame) (cw : Word),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        st'.locals cond = some cw →
        ∃ frc, Lir.MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
          ∧ 3 ≤ frc.exec.gasAvailable.toNat
          ∧ GasConstants.Ghigh ≤ (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              GasConstants.Ghigh
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
              GasConstants.Gmid
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
              (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat
                  ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat)

/-! ## §4 — Exact stream consumption: `RunFromLeft` / `RunFromAll`

`RunFrom`'s two halt constructors DROP the leftover trace `T'` (`V2/Machine.lean`), so a
bare `RunFrom … (realisedGas log) …` conclusion only speaks about the consumed PREFIX —
the last drop-the-suffix vacuity channel. `RunFromLeft` mirrors `RunFrom` constructor-for-
constructor with one extra `Trace` index exposing the leftover at the halt; `RunFromAll`
pins it to `[]` (the strengthening the target architecture marks "worth taking"). The two
adequacy lemmas make the mirror-faithfulness itself tracked debt. -/

/-- `RunFrom` with the leftover trace exposed: `RunFromLeft prog o st T L O Tleft` is
`RunFrom prog o st T L O` where the halt constructor's un-consumed trace is `Tleft`.
Constructor-for-constructor mirror of `RunFrom` (`V2/Machine.lean`); the halt arms return
their `T'` instead of dropping it, the edge arms thread it. -/
inductive RunFromLeft (prog : Program) (o : CallOracle) :
    IRState → Trace → Label → Observable → Trace → Prop where
  /-- `ret t`: run the block's statements, halt returning `t`'s value; leftover = `T'`. -/
  | ret {st st' : IRState} {T T' : Trace} {L : Label} {b : Block} {t : Tmp} {w : Word}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFromLeft prog o st T L { world := st'.world, result := .returned w } T'
  /-- `stop`: run the block's statements, halt; leftover = `T'`. -/
  | stop {st st' : IRState} {T T' : Trace} {L : Label} {b : Block}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .stop) :
      RunFromLeft prog o st T L { world := st'.world, result := .stopped } T'
  /-- `branch`, condition non-zero ⇒ recurse into `thenL`, threading the leftover. -/
  | branchThen {st st' : IRState} {T T' Tleft : Trace} {L : Label} {b : Block}
      {cond : Tmp} {cw : Word} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some cw) (hnz : cw ≠ 0)
      (hrest : RunFromLeft prog o st' T' thenL O Tleft) :
      RunFromLeft prog o st T L O Tleft
  /-- `branch`, condition zero ⇒ recurse into `elseL`, threading the leftover. -/
  | branchElse {st st' : IRState} {T T' Tleft : Trace} {L : Label} {b : Block}
      {cond : Tmp} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some 0)
      (hrest : RunFromLeft prog o st' T' elseL O Tleft) :
      RunFromLeft prog o st T L O Tleft
  /-- `jump dst` ⇒ recurse into `dst`, threading the leftover. -/
  | jump {st st' : IRState} {T T' Tleft : Trace} {L : Label} {b : Block} {dst : Label}
      {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog o st T b.stmts st' T')
      (hterm : b.term = .jump dst)
      (hrest : RunFromLeft prog o st' T' dst O Tleft) :
      RunFromLeft prog o st T L O Tleft

/-- **Exact whole-stream consumption**: the run consumes the ENTIRE supplied trace
(leftover `[]`). The flagship's strengthened conclusion (`lowering_conforms_all`) uses this
with `T := realisedGas log`, closing the positional-equality gap over the un-consumed
suffix. -/
def RunFromAll (prog : Program) (o : CallOracle) (st : IRState) (T : Trace) (L : Label)
    (O : Observable) : Prop :=
  RunFromLeft prog o st T L O []

/-- Mirror adequacy, forgetful direction: a leftover-indexed run is a run. TRACKED DEBT
(structural induction; stated so the mirror-faithfulness of `RunFromLeft` is itself
checked, not assumed). -/
theorem runFrom_of_runFromLeft {prog : Program} {o : CallOracle} {st : IRState}
    {T Tleft : Trace} {L : Label} {O : Observable}
    (h : RunFromLeft prog o st T L O Tleft) : RunFrom prog o st T L O := sorry

/-- Mirror adequacy, completion direction: every run has SOME leftover decomposition.
TRACKED DEBT (structural induction on `RunFrom`). -/
theorem runFromLeft_exists {prog : Program} {o : CallOracle} {st : IRState}
    {T : Trace} {L : Label} {O : Observable}
    (h : RunFrom prog o st T L O) : ∃ Tleft, RunFromLeft prog o st T L O Tleft := sorry

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
theorem defsSoundS_preserved_step {prog : Program} {o : CallOracle}
    {st st' : IRState} {T T' : Trace} {s : Stmt} {I : Tmp → Prop}
    {L : Label} {b : Block} {pc : Nat}
    (hcons : DefsConsistent prog)
    (hb : blockAt prog L = some b)
    (hs : b.stmts[pc]? = some s)
    (hstep : EvalStmt prog o st T s st' T')
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
  | call hcallee hgas ho =>
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
        exact absurd (Or.inr (Or.inr ⟨b, hbmem, cs, hsmem, hrt⟩)) hnr₀
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

/-- **R1 — the gas recorder bridge** (the riskiest obligation; the trace↔recorder
positional bridge). At a gas-assign cursor, the un-consumed gas suffix's head is the
machine GAS output at the cursor frame.

SATISFIABILITY ANALYSIS (why each hypothesis is load-bearing): the coupling's restart
equation pins `gS` to `fr`'s deterministic future; `Corr` pins `fr`'s pc/code to the GAS
byte of `lower prog`; and the CLEAN-HALT antecedent is what blocks the one remaining
refutation — an OOG-at-GAS frame satisfies the coupling with the run ending in an
exception whose recorded suffix is `gS = []`, refuting the head equation. Under clean
halt the first restart step IS the recorded top-level GAS read, and `driveLog` records
exactly `UInt256.ofUInt64 exec.gasAvailable` of the post-charge state (= `gasAvailable −
Gbase`, the former `StmtTies` gas word — now the `StmtTies'` gas arm — verbatim). DERIVED-status obligation: never supplied. -/
theorem gas_suffix_head_realised {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {L : Label} {b : Block} {pc : Nat} {t : Tmp} {st : IRState} {fr : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.assign t .gas))
    (hcorr : Lir.Corr prog sloadChg 0 st fr L pc)
    (hcp : RecorderCoupled log fr gS sS cS)
    (hch : CleanHaltsNonException fr) :
    gS.head? = some (UInt256.ofUInt64
      (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)) := sorry

/-- **A halting `Runs` is refl.** If `fr` halts (`stepFrame fr = .halted h`) then the only
`Runs fr fr'` is the reflexive one, so `fr = fr'`. Pure engine inversion (the `.step`/`.call`
arms demand `.next`/`.needsCall`, contradicting `.halted`). -/
theorem runs_halt_eq {fr fr' : Frame} {h : FrameHalt}
    (hh : stepFrame fr = .halted h) (hr : Runs fr fr') : fr = fr' := by
  cases hr with
  | refl _ => rfl
  | step hstep _ => rw [hstep.1] at hh; exact absurd hh (by nofun)
  | call hcall _ =>
      obtain ⟨_, _, _, _, hstep, _⟩ := hcall
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

/-- **R3 — call realisation from the log.** At a call cursor, the coupled frame's recorded
CALL supplies the `CallRealisesS` bundle at the REALISED oracle — the round-3 restatement
(header lesson 8): NOT the in-tree `Lir.CallRealises` verbatim (whose embedded
`StepScoped (.call cs)` live-scope clause is refutable within this theorem's own
hypothesis envelope for a `WellLowered` program whose call result has a registered
reader), but the value/trace KERNEL + the shadowing-aware static scoping (`StepScopedS`)
+ the static bundle the round-2 statement was MISSING (`hwl` — it is what derives the
`StepScopedS` residue, the result-tmp slot registration of the post-state fold, and the
Route-B slot addressability; the round-2 reviewer's "R3 carries no static bundle at all").
Kernel sources: the head `CallRecord` (`realisedCall_eq_evmV2`, rfl-clean once the record
is pinned), plumbing from `materialise_runs` + the `resumeAfterCall` rfl-pins + the
Route-B tail (`stash_tail_runs`).
Under `SingleCall` + the DYNAMIC at-most-one premise `hone : log.calls.length ≤ 1` the
head of the coupled `callSuffix` IS this cursor's call (the whole log records at most one
— `hone` is what makes that true of the RUN and not just the text: without it a
syntactically-single call in a loop fires per iteration and the head-projection oracle is
refuted at the second firing, header lesson 7). The address antecedent is what identifies
`realisedCall log self` with `evmV2CallOracle … fr0.address`. DERIVED-status obligation
(with `hseams`-style context available to the R10 assembly if the plumbing needs it).

**R3′ (tracked design decision, not a statement):** for multi-CALL programs the
function-shaped `CallOracle` is wrong (two dynamic calls with identical IR-visible inputs
can differ); the honest completion makes calls a CONSUMED STREAM of records — exactly the
gas channel's positional solution, and the coupling already carries `callSuffix` for it.
That generalization touches `EvalStmt.call` (IR spec surface) and is deliberately deferred;
`SingleCall` (and its loop caveat, see its docstring) is the recorded interim scope. -/
theorem callRealises_of_recorded {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 : IRState} {fr0 : Frame}
    {gS : List Word} {sS : List Nat} {cS : List CallRecord}
    (hwl : WellLowered prog)
    (hsingle : SingleCall prog)
    (hone : log.calls.length ≤ 1)
    (hb : blockAt prog L = some b)
    (hcur : b.stmts[pc]? = some (.call cs))
    (hcp : RecorderCoupled log fr0 gS sS cS)
    (hch : CleanHaltsNonException fr0)
    (haddr : fr0.exec.executionEnv.address = self) :
    CallRealisesS prog sloadChg (realisedCall log self) L b pc cs st0 fr0 := sorry

/-- **R4 — SSTORE realisation, point-wise at the concrete frame** (the honest replacement
of the unsatisfiable `∃ acc, SstoreRealises …` tie conjunct — header lesson 3). At the
REAL internal SSTORE frame `g` (stack `kw :: vw :: []`, SSTORE decoded, nonzero write,
modifiable), the three `SstoreRealises` conclusions hold AT `g`: the stipend gate and the
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
    (hnz : vw ≠ 0)
    (hmod : g.exec.executionEnv.canModifyState = true) :
    (¬ g.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    ∧ sstoreChargeOf g.exec kw vw ≤ g.exec.gasAvailable.toNat
    ∧ ∃ acc, g.exec.accounts.find? g.exec.executionEnv.address = some acc := sorry

/-- **R5 — terminator ties from the walk vocabulary.** `TermTies'` holds at every present
block: its arms' antecedents are exactly what `DriveCorrLog` supplies at real boundaries
(Corr, clean-halt, self-presence, address/kind pins), and the conclusions are derived —
non-emptiness via `accounts_ne_empty_of_selfPresent`; the gas guards via the clean-halt
landing extractors (`jump_landing_of_cleanHalt`/`branch_landing_of_cleanHalt` patterns);
the ret epilogue decode facts via `DecodeAnchors` at the pc-pinned cursor; the `frv`
kind/presence facts via `Runs`-preservation seeded from the antecedent pins (+`hprec` for
the returning-call edges, hence the seam hypothesis). DERIVED-status obligation. -/
theorem termTies'_of_walk {prog : Program} {sloadChg : Tmp → ℕ} {log : RunLog}
    {self : AccountAddress} {L : Label} {b : Block}
    (hwl : WellLowered prog)
    (hprec : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
      ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hb : blockAt prog L = some b) :
    TermTies' prog sloadChg log self L b := sorry

/-- **R6 — the boundary walk** (the `hrb` residue; the Track-A discharge target). Every
`Runs`-reachable frame of a `lower prog` entry sits at a reachable instruction boundary of
`lower prog` — the pc-reachability invariant that structurally discharges the no-CREATE
modellability clause (`notCreate_of_atReachableBoundary`) and scopes the future
data-segment design. One of the three substantial proofs. DERIVED-status obligation. -/
theorem runs_atReachableBoundary {prog : Lir.Program} {params : CallParams} {fr₀ : Frame}
    (hbegin : beginCall params = .inl fr₀)
    (hcode : params.codeSource = .Code (lower prog)) :
    ∀ fr', Runs fr₀ fr' → AtReachableBoundary prog fr' := sorry

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
          rw [ih rest (.inl parent) g0 s0 (recordCall pending result c0),
              ih rest (.inl parent) [] [] (recordCall pending result [])]
          cases hb : driveLog n rest (.inl parent) [] [] [] with
          | error e => simp [Except.map]
          | ok val =>
            simp [Except.map, recordCall_append pending result c0, List.append_assoc]
        | error e =>
          dsimp only [hres]
          rw [ih rest (.inr (endFrame pending.frame (.exception e))) g0 s0
                (recordCall pending result c0),
              ih rest (.inr (endFrame pending.frame (.exception e))) [] []
                (recordCall pending result [])]
          cases hb : driveLog n rest (.inr (endFrame pending.frame (.exception e))) [] [] [] with
          | error e' => simp [Except.map]
          | ok val =>
            simp [Except.map, recordCall_append pending result c0, List.append_assoc]
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

/-- **R7e — a returning external CALL consumes exactly one `CallRecord` and NO gas/sload
entries** (children are black-boxed by the recorder's `stack.isEmpty` gate, exactly as
`Runs.call` black-boxes them). The record's `(result, pending)` pinning to this call's
data is delivered inside R3 via restart determinism, not restated here.

BLOCKED — recorder-model asymmetry (escalated, NOT a proof-difficulty artifact). The
gas/sload records ARE gated by `stack.isEmpty` (`Recorder.lean:202,205`), so the "NO
gas/sload entries" half is sound: during the restart from `fr` the child runs on the
nonempty stack `[.call pending]`, so its gas/sload reads are not recorded. But `recordCall`
is UNGATED (`Recorder.lean:183-188`): it fires on EVERY `pending :: rest` delivery, at any
nesting depth. So if the external callee `child` itself issues returning CALLs, each appends
a `CallRecord` — in stack order the callee's inner calls complete first, so the head of the
recorded call-suffix at `fr` is the callee's FIRST inner call, and the `fr → resumeFr`
segment consumes `childInnerRecords ++ [outerRec]`, i.e. `1 + (child's own call count)`
records, NOT exactly one. The "consumes exactly one `CallRecord`" conclusion (`rec :: cS →
cS`) is therefore FALSE in general — provable only when the callee records no calls of its
own (in the flagship this is guaranteed by `hone : log.calls.length ≤ 1`, but R7e's signature
carries neither `hone` nor any local surrogate).
Resolutions (all outside spine's edit surface / statement-preserving envelope): (A) gate
`recordCall` by the RESUMED stack being empty in `Spec/Recorder.lean` (design-correct,
matches the docstring; edits an existing file); (B) thread `hone`/"child records no calls"
into R7e (added hypothesis); (C) weaken to `∃ childRecs, RecorderCoupled … cS' ∧ rec :: cS =
childRecs ++ [rec] ++ cS'` (weakened conclusion). Per the no-weaken/no-added-hypothesis rule
this is left OPEN pending the recordCall-gating decision; the shared machinery it needs
(`driveLog_acc_hom`, `isGasOp_false_of_isSloadOp`) has landed above. -/
theorem recorderCoupled_call {log : RunLog} {fr resumeFr : Frame}
    {gS : List Word} {sS : List Nat} {rec : CallRecord} {cS : List CallRecord}
    (hcp : RecorderCoupled log fr gS sS (rec :: cS))
    (hcr : CallReturns fr resumeFr) :
    RecorderCoupled log resumeFr gS sS cS := sorry

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
    ∃ b', blockAt prog dst = some b' := sorry

/-! ## §6 — the concrete non-vacuity witness (R9's anchor; R12's subject)

`exProg` exercises every interesting feature at once: a gas read feeding a forwarded-gas
CALL (gas introspection coupled to the call channel), a spilled SLOAD, a nonzero SSTORE, a
single syntactic CALL (outside the loop — see `SingleCall`'s loop caveat), and a genuine
CYCLE (block 1 loops on a gas-derived condition until gas drops below the threshold — the
cyclic-driver domain no per-cursor gas function could handle). Block/tmp layout:

* block 0: `t0 := 5; t1 := gas; t2 := sload t0; t3 := 1; sstore t0 t3; t4 := 0x100;`
  `t5 := call(callee := t4, gasFwd := t1); jump L1`
* block 1 (the loop): `t6 := gas; t7 := 1000; t8 := (t6 < t7); branch t8 L2 L1`
* block 2: `stop` -/

/-- The R12 witness program (see the §6 docstring for the layout rationale). REAL
definition — the flagship's antecedent must be machine-checkably TRUE somewhere
(HonestGasTie's replacement role, target-architecture §4.1). -/
def exProg : Program :=
  { blocks := #[
      { stmts := [
          .assign ⟨0⟩ (.imm 5),
          .assign ⟨1⟩ .gas,
          .assign ⟨2⟩ (.sload ⟨0⟩),
          .assign ⟨3⟩ (.imm 1),
          .sstore ⟨0⟩ ⟨3⟩,
          .assign ⟨4⟩ (.imm 0x100),
          .call { callee := ⟨4⟩, gasFwd := ⟨1⟩, resultTmp := some ⟨5⟩ } ],
        term := .jump ⟨1⟩ },
      { stmts := [
          .assign ⟨6⟩ .gas,
          .assign ⟨7⟩ (.imm 1000),
          .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ],
        term := .branch ⟨8⟩ ⟨2⟩ ⟨1⟩ },
      { stmts := [], term := .stop } ],
    entry := ⟨0⟩ }

/-- `exProg` is single-CALL — a PROVED (non-sorry) anchor: the scope premise is decidably
true for the witness. -/
theorem singleCall_exProg : SingleCall exProg := by unfold SingleCall; decide

-- `Block`/`Program` derive only `Repr` in `Spec/IR.lean`; the concrete-witness proofs below
-- (and R9's singleton checker) need decidable equality. Their fields already derive it.
deriving instance DecidableEq for Block
deriving instance DecidableEq for Program

/-- **`defsOf exProg` in closed form.** The two-pass `find?` over the flattened def-pairs
reduces (definitionally) to `find?` over the concrete 9-element pair list: t0↦imm5, t1/t2↦slot
(gas/sload spilled), t3↦imm1, t4↦imm0x100, t5↦slot (call result), t6↦slot (gas spilled),
t7↦imm1000, t8↦lt t6 t7 — the sole reading def. -/
theorem defsOf_exProg_eq : defsOf exProg = fun t =>
    (([ (⟨0⟩, Expr.imm 5), (⟨1⟩, Expr.slot (slotOf ⟨1⟩)), (⟨2⟩, Expr.slot (slotOf ⟨2⟩)),
        (⟨3⟩, Expr.imm 1), (⟨4⟩, Expr.imm 0x100), (⟨5⟩, Expr.slot (slotOf ⟨5⟩)),
        (⟨6⟩, Expr.slot (slotOf ⟨6⟩)), (⟨7⟩, Expr.imm 1000),
        (⟨8⟩, Expr.lt ⟨6⟩ ⟨7⟩) ] : List (Tmp × Expr)).find?
      (fun p => p.1 == t)).map (·.2) := rfl

/-- **The only registered readers in `exProg`.** A `ReadsOf` fact holds iff the reader is `t8`
and the read tmp is `t6` or `t7` (`t8`'s def `lt t6 t7` is the sole def reading any tmp). -/
theorem defsOf_exProg_reads {t t' : Tmp} (h : ReadsOf exProg t t') :
    (t = ⟨6⟩ ∨ t = ⟨7⟩) ∧ t' = ⟨8⟩ := by
  obtain ⟨e', hd, hu⟩ := h
  rw [defsOf_exProg_eq, Option.map_eq_some_iff] at hd
  obtain ⟨p, hfind, hp2⟩ := hd
  have hp1 := List.find?_some hfind
  rw [beq_iff_eq] at hp1
  have hmem := List.mem_of_find?_eq_some hfind
  subst hp2
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals (try (exfalso; revert hu; simp only [usesInExpr]; decide))
  -- only the `t8 := lt t6 t7` pair survives; `hp1 : ⟨8⟩ = t'`, `hu : usesInExpr t (lt t6 t7) ≠ 0`.
  refine ⟨?_, hp1.symm⟩
  by_contra hc
  push_neg at hc
  obtain ⟨h6, h7⟩ := hc
  apply hu
  simp only [usesInExpr, if_neg (fun he : (⟨6⟩ : Tmp) = t => h6 he.symm),
    if_neg (fun he : (⟨7⟩ : Tmp) = t => h7 he.symm)]

/-- No `exProg` def reads a tmp other than `t6`/`t7`. -/
theorem not_readsOf_exProg {t : Tmp} (h6 : t ≠ ⟨6⟩) (h7 : t ≠ ⟨7⟩) (t' : Tmp) :
    ¬ ReadsOf exProg t t' := by
  intro h
  rcases (defsOf_exProg_reads h).1 with rfl | rfl
  · exact h6 rfl
  · exact h7 rfl

/-- One `invalStep` over a pure assign whose target has no registered reader (and whose own
expr does not read the target) preserves point-wise falsity of the invalidation set. -/
theorem invalStep_false_assign {I : Tmp → Prop} {t : Tmp} {e : Expr}
    (hI : ∀ t', ¬ I t') (hu : usesInExpr t e = 0)
    (hr : ∀ t', ¬ ReadsOf exProg t t') :
    ∀ t', ¬ invalStep exProg I (.assign t e) t' := by
  intro t' h
  simp only [invalStep] at h
  by_cases hc : t' = t
  · rw [if_pos hc] at h; exact h hu
  · rw [if_neg hc] at h; exact h.elim (hI t') (hr t')

/-- `sstore` transfers the invalidation set unchanged, so it preserves point-wise falsity. -/
theorem invalStep_false_sstore {I : Tmp → Prop} {k v : Tmp}
    (hI : ∀ t', ¬ I t') : ∀ t', ¬ invalStep exProg I (.sstore k v) t' := by
  intro t' h; simp only [invalStep] at h; exact hI t' h

/-- One `invalStep` over a result-bearing call whose result tmp has no registered reader
preserves point-wise falsity. -/
theorem invalStep_false_call {I : Tmp → Prop} {cs : CallSpec} {t : Tmp}
    (hres : cs.resultTmp = some t)
    (hI : ∀ t', ¬ I t') (hr : ∀ t', ¬ ReadsOf exProg t t') :
    ∀ t', ¬ invalStep exProg I (.call cs) t' := by
  intro t' h
  simp only [invalStep, hres] at h
  by_cases hc : t' = t
  · rw [if_pos hc] at h; exact h
  · rw [if_neg hc] at h; exact h.elim (hI t') (hr t')

/-- `exProg` re-validates per block (R0b's static-boundary anchor). The only within-block
invalidation is `t6 := gas` (and the value-coincident `t7 := 1000`) staleing `t8` — its
sole registered reader — healed two statements later by `t8 := lt t6 t7`; no registered
reader of `t8` exists (the branch USE of `t8` is not a registered def), and block 0's
targets have no registered readers at all. TRACKED DEBT (a finite fold evaluation over
`Tmp → Prop`; becomes a `decide` once the R9 checker gives the fold its `List Tmp`
executable twin). -/
theorem revalidatesPerBlock_exProg : RevalidatesPerBlock exProg := by
  rintro ⟨idx⟩ b hL
  rcases idx with _ | _ | _ | n
  · -- block 0: every target has no registered reader; each step preserves falsity.
    have hb : b = Block.mk [ .assign ⟨0⟩ (.imm 5), .assign ⟨1⟩ .gas, .assign ⟨2⟩ (.sload ⟨0⟩),
        .assign ⟨3⟩ (.imm 1), .sstore ⟨0⟩ ⟨3⟩, .assign ⟨4⟩ (.imm 0x100),
        .call ⟨⟨4⟩, ⟨1⟩, some ⟨5⟩⟩ ] (.jump ⟨1⟩) := by
      have hd : blockAt exProg ⟨0⟩ = some (Block.mk [ .assign ⟨0⟩ (.imm 5), .assign ⟨1⟩ .gas,
          .assign ⟨2⟩ (.sload ⟨0⟩), .assign ⟨3⟩ (.imm 1), .sstore ⟨0⟩ ⟨3⟩, .assign ⟨4⟩ (.imm 0x100),
          .call ⟨⟨4⟩, ⟨1⟩, some ⟨5⟩⟩ ] (.jump ⟨1⟩)) := by decide
      rw [hd] at hL; exact ((Option.some.injEq _ _).mp hL).symm
    subst hb
    have h0 : ∀ t', ¬ (fun _ : Tmp => False) t' := fun _ h => h
    have h1 := invalStep_false_assign h0 (show usesInExpr ⟨0⟩ (.imm 5) = 0 by decide)
      (not_readsOf_exProg (t := ⟨0⟩) (by decide) (by decide))
    have h2 := invalStep_false_assign h1 (show usesInExpr ⟨1⟩ Expr.gas = 0 by decide)
      (not_readsOf_exProg (t := ⟨1⟩) (by decide) (by decide))
    have h3 := invalStep_false_assign h2 (show usesInExpr ⟨2⟩ (.sload ⟨0⟩) = 0 by decide)
      (not_readsOf_exProg (t := ⟨2⟩) (by decide) (by decide))
    have h4 := invalStep_false_assign h3 (show usesInExpr ⟨3⟩ (.imm 1) = 0 by decide)
      (not_readsOf_exProg (t := ⟨3⟩) (by decide) (by decide))
    have h5 := invalStep_false_sstore (k := ⟨0⟩) (v := ⟨3⟩) h4
    have h6 := invalStep_false_assign h5 (show usesInExpr ⟨4⟩ (.imm 0x100) = 0 by decide)
      (not_readsOf_exProg (t := ⟨4⟩) (by decide) (by decide))
    have h7 := invalStep_false_call
      (cs := ⟨⟨4⟩, ⟨1⟩, some ⟨5⟩⟩) (t := ⟨5⟩) rfl h6
      (not_readsOf_exProg (t := ⟨5⟩) (by decide) (by decide))
    simpa only [List.foldl_cons, List.foldl_nil] using h7
  · -- block 1 (the loop): the `t6`/`t7` rebinds stale `t8`, healed by the `t8` reassign.
    have hb : b = Block.mk [ .assign ⟨6⟩ .gas, .assign ⟨7⟩ (.imm 1000),
        .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ] (.branch ⟨8⟩ ⟨2⟩ ⟨1⟩) := by
      have hd : blockAt exProg ⟨1⟩ = some (Block.mk [ .assign ⟨6⟩ .gas, .assign ⟨7⟩ (.imm 1000),
          .assign ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) ] (.branch ⟨8⟩ ⟨2⟩ ⟨1⟩)) := by decide
      rw [hd] at hL; exact ((Option.some.injEq _ _).mp hL).symm
    subst hb
    intro t'
    simp only [List.foldl_cons, List.foldl_nil, invalStep]
    intro h
    by_cases h8 : t' = ⟨8⟩
    · rw [if_pos h8] at h; revert h; decide
    · rw [if_neg h8] at h
      rcases h with h | h
      · by_cases h7 : t' = ⟨7⟩
        · rw [if_pos h7] at h; revert h; decide
        · rw [if_neg h7] at h
          rcases h with h | h
          · by_cases h6 : t' = ⟨6⟩
            · rw [if_pos h6] at h; revert h; decide
            · rw [if_neg h6] at h
              rcases h with h | h
              · exact h
              · exact h8 (defsOf_exProg_reads h).2
          · exact h8 (defsOf_exProg_reads h).2
      · rcases (defsOf_exProg_reads h).1 with h' | h' <;> exact absurd h' (by decide)
  · -- block 2: no statements, the fold is the empty (false) set.
    have hb : b = Block.mk [] .stop := by
      have hd : blockAt exProg ⟨2⟩ = some (Block.mk [] .stop) := by decide
      rw [hd] at hL; exact ((Option.some.injEq _ _).mp hL).symm
    subst hb
    intro t' h; exact h
  · -- out of bounds: `exProg` has exactly three blocks.
    exfalso
    simp only [blockAt] at hL
    rw [Array.getElem?_eq_none (show exProg.blocks.size ≤ n + 1 + 1 + 1 by
      have h3 : exProg.blocks.size = 3 := by decide
      omega)] at hL
    simp at hL

/-- The lesson-8 stale state: `exProg`'s loop-EXIT iteration, mid-block 1, after the
`t6 := gas` rebind (fresh read `500 < 1000`) and before `t8`'s reassign — `t8` still
holds the previous iteration's `0` (that iteration's gas read was `≥ 1000`). The
`t0`–`t5` bindings are block-0 values (the gas/sload/call-result words chosen
representatively; they are `NonRecomputable`/spilled, so `DefsSound` is silent about
them either way). -/
def staleSt : IRState :=
  { locals := fun t =>
      if t = ⟨0⟩ then some 5 else if t = ⟨1⟩ then some 2000
      else if t = ⟨2⟩ then some 0 else if t = ⟨3⟩ then some 1
      else if t = ⟨4⟩ then some 0x100 else if t = ⟨5⟩ then some 1
      else if t = ⟨6⟩ then some 500 else if t = ⟨7⟩ then some 1000
      else if t = ⟨8⟩ then some 0 else none
    world := fun _ => 0 }

/-- **The machinery finding, machine-checked** (header lesson 8; R0b's motivation): the
un-scoped `DefsSound` — hence `Corr`, whose `defsSound` field it is — is FALSE at the
real mid-block state of `exProg`'s loop-exit iteration: `t8` is bound to the stale `0`
while its registered def `.lt t6 t7` recomputes to `1` under the rebound `t6`. PROVED
(not debt) — the refutation is the point. The scoped invariant is untouched here: `t8`
is exactly the tmp `invalStep` puts in the set at the `t6` rebind. -/
theorem not_defsSound_stale : ¬ Lir.DefsSound exProg staleSt := by
  intro h
  have hnr : ¬ Lir.NonRecomputable exProg ⟨8⟩ := by
    unfold Lir.NonRecomputable Lir.isGasDef Lir.isSloadDef Lir.isCallResult
    rintro (⟨b, hb, hmem⟩ | ⟨b, hb, k, hmem⟩ | ⟨b, hb, cs, hmem, hres⟩) <;>
      (simp [exProg] at hb; rcases hb with rfl | rfl | rfl <;> simp_all)
  exact absurd (h ⟨8⟩ (.lt ⟨6⟩ ⟨7⟩) 0 (by decide) hnr (by decide)) (by decide)

/-- **R9 — the static checker, stated existentially with a non-vacuity anchor.** A
PREMATURE checker `def` would be worse than debt (a wrong-but-real `lowerCheck` misleads;
a `fun _ => false` checker is the vacuity dual — sound and useless). The obligation is:
some Boolean checker is SOUND for `WellLowered` AND accepts the witness program — the
second conjunct is the anti-vacuity guard (it forces `WellLowered exProg` to actually
hold, `RunDefinableG` included). The checker DEFINITION is the debt. -/
theorem wellLowered_check_exists :
    ∃ check : Program → Bool,
      (∀ prog, check prog = true → WellLowered prog) ∧ check exProg = true := sorry

/-- **R10a — the statement ties, BUILT from the run** (the assembly obligation the
current headline lacks a producer for). For ANY `(st0, fr0, suffixes)` satisfying the
arms' antecedents — including OFF-RUN adversarial instances — the conclusions hold,
because each is (i) a static fact of `prog` derivable from `hwl` + the cursor, (ii)
carried over from the arm's own antecedents (`Corr`'s `wellScoped`/`memAgree` channels,
the threaded `NonzeroSstores` seam), or (iii) computed from `fr0` and restart determinism
(the coupling forces any witness to reproduce the recorded future) — the §3 docstring's
precision note. This off-run-robustness is exactly the satisfiability analysis that
makes the §3 reshape non-vacuous. `hnzw` is NOT needed here: the sstore arm carries `NonzeroSstores fr0` as its
own antecedent (threaded by the walk). DERIVED-status obligation. -/
theorem stmtTies'_of_runWithLog {prog : Program} {params : CallParams} {log : RunLog}
    {fr₀ : Frame}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hwl : WellLowered prog)
    (hsingle : SingleCall prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hone : log.calls.length ≤ 1)
    (hseams : PrecompileSeams prog params)
    (hbegin : beginCall params = .inl fr₀) :
    ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies' prog sloadChg log params.recipient L b := sorry

/-- **R10b — the terminator ties, BUILT** (the `runWithLog`-context restatement of R5;
kept separate so the R11 assembly consumes one hypothesis shape per tie). -/
theorem termTies'_of_runWithLog {prog : Program} {params : CallParams} {log : RunLog}
    (hwl : WellLowered prog)
    (hseams : PrecompileSeams prog params) :
    ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block), blockAt prog L = some b →
      TermTies' prog sloadChg log params.recipient L b := sorry

/-- **R11 — THE FLAGSHIP.** Run the lowered bytecode once with the recording interpreter;
feed the recorded gas reads and call records into the executable IR semantics; the IR run
exists at the PINNED oracles (`realisedGas log` / `realisedCall log recipient`, from the
PINNED entry state) and produces the same observable world.

Hypothesis ledger (the honest surface, nothing else): two definitional pins
(`hcode`/`hmod`), two decidable entry facts (`hself`/`hgas`), one static checkable bundle
(`hwl`), three decidable scope premises (`hsingle`/`hone`/`hclean` — `hone` is the
dynamic at-most-one-call twin of the syntactic `hsingle`, header lesson 7), ONE runtime
premise (`hrun`),
one two-field honest seam structure (`hseams`), and one named scope seam (`hnzw` — the
nonzero-write cut the fleet sketch missed; without it the sstore simulation cannot fire).
The current headline's `DriveCorr`/`CallPreservesSelf`/`hpresent`/tie/`{T}`/`obs`
hypotheses are all gone: derived (R1–R10), definitional (`entryState`), or dead (the
phantom). -/
theorem lowering_conforms {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hsingle : SingleCall prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hone : log.calls.length ≤ 1)
    (hseams : PrecompileSeams prog params)
    (hnzw : ∀ fr₀, beginCall params = .inl fr₀ → NonzeroSstores fr₀) :
    ∃ O : Observable,
      RunFrom prog (realisedCall log params.recipient)
        (entryState params) (realisedGas log) prog.entry O
      ∧ Conforms params.recipient log O := sorry

/-- **R11-all — the exact-consumption strengthening**: the same flagship with the IR run
consuming the ENTIRE recorded gas stream (`RunFromAll`, leftover `[]`) — closes the
drop-the-suffix vacuity channel (§4). -/
theorem lowering_conforms_all {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hsingle : SingleCall prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hone : log.calls.length ≤ 1)
    (hseams : PrecompileSeams prog params)
    (hnzw : ∀ fr₀, beginCall params = .inl fr₀ → NonzeroSstores fr₀) :
    ∃ O : Observable,
      RunFromAll prog (realisedCall log params.recipient)
        (entryState params) (realisedGas log) prog.entry O
      ∧ Conforms params.recipient log O := sorry

/-- **The gas-free CO-FLAGSHIP** (target-architecture decision 2 — prove it FIRST). The
flagship restricted to `NoGasReads prog`: the gas suffix plays no role, so it needs no R1
(the riskiest obligation) — the de-risking checkpoint, and the theorem external readers
can compare to prior art (Verity/vyper-hol scope: no fork's verified semantics models gas
introspection at all). -/
theorem lowering_conforms_gasfree {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hng : NoGasReads prog)
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hsingle : SingleCall prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hone : log.calls.length ≤ 1)
    (hseams : PrecompileSeams prog params)
    (hnzw : ∀ fr₀, beginCall params = .inl fr₀ → NonzeroSstores fr₀) :
    ∃ O : Observable,
      RunFrom prog (realisedCall log params.recipient)
        (entryState params) (realisedGas log) prog.entry O
      ∧ Conforms params.recipient log O := sorry

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
theorem r12_hypotheses_inhabited :
    ∃ (params : CallParams) (log : RunLog) (acc : Account),
      params.codeSource = .Code (lower exProg)
      ∧ params.canModifyState = true
      ∧ params.accounts.find? params.recipient = some acc
      ∧ GasConstants.Gjumpdest ≤ params.gas.toNat
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ log.clean
      ∧ log.calls.length ≤ 1
      ∧ PrecompileSeams exProg params
      ∧ (∀ fr₀, beginCall params = .inl fr₀ → NonzeroSstores fr₀) := sorry

/-- **R12b — end-to-end at the witness**: `lowering_conforms` instantiated at `exProg`
(gas-read + sload + nonzero-sstore + call + loop, all at once — the verifereum
`deploy_result_correct`-shaped concrete instance no fork has for this feature set). -/
theorem r12_end_to_end :
    ∃ (params : CallParams) (log : RunLog),
      params.codeSource = .Code (lower exProg)
      ∧ runWithLog params (seedFuel params.gas) = some log
      ∧ ∃ O : Observable,
          RunFrom exProg (realisedCall log params.recipient)
            (entryState params) (realisedGas log) exProg.entry O
          ∧ Conforms params.recipient log O := sorry

/-! ## §7 — audit note

NO `#print axioms` guards live here BY DESIGN: every sorry'd declaration carries `sorryAx`
until its obligation lands, so axiom guards would only pin the debt's existence. The
default-target audit net (`Audit.lean`, Track A) must NOT cover this Nightly lib; the
guards migrate there obligation-by-obligation as the sorries are discharged. -/

end Lir.V2
