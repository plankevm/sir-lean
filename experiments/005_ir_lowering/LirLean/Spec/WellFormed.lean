import LirLean.Spec.Semantics
import LirLean.Spec.Lowering
import LirLean.Materialise.MaterialiseGas
import LirLean.Materialise.DefsSound
import LirLean.Decode.DecodeLower
import LirLean.Assembly.Acyclic

/-!
# LirLean — IR well-formedness (default cone)

The static, program-text-only well-formedness vocabulary of the lowering claim, hoisted
into the **default (`LirLean`) cone** so the trusted surface can state it (misplacement #1,
smell 5.1 of `docs/codebase-map-2026-07-06.md`). Previously these lived in
`V2/Realisability/Surface.lean` (WIP cone); they are moved here verbatim — same names, same
namespace (`Lir.V2`), so the WIP consumers (`Machinery`/`Witness`/`Producer`/
`RealisabilitySpec`) are unaffected (they see them through `Surface`'s import of this module).

Beyond the relocation this module introduces (plan §1B B2):

* the two scalar budgets `codeFits` (pc budget) and `stackFits` (stack budget), the scalar
  distillation of the ~15 per-cursor quantified `WellFormedLowered` bounds;
* `CFGClosed`, the presence + in-bounds half of `ClosedCFG` (its offset-bound halves are
  DERIVED from `codeFits` in stage 1B-lemmas, not carried);
* `defRank`, the SSA def-order rank candidate witnessing `Acyclic`;
* the `IRWellFormed` bundle (Eduardo's name — NOT `WellFormed`, which is a different
  single-use def at `Materialise/DefsSound.lean:143`).

This stage RELOCATES + DEFINES only; the derivation lemmas (`pcBounds_of_codeFits`,
`stackBounds_of_stackFits`, `matFueled_of_acyclic`, `wellFormedLowered_of_wellFormed`) and the
flagship reshape land in stages 1B-lemmas / 1B-reshape. Sorry-free. -/

namespace Lir.V2

open Evm

/-! ## Static stack-room bounds (`StackRoomOK`) -/

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

/-! ## Gas/call-aware run-definability (`RunDefinableG`)

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
  | .create _ =>
      -- Step-1 placeholder (real total Prop): CREATE has no `EvalStmt` arm yet
      -- (Step 2), so nothing is demanded. The real operand demands (value /
      -- initOffset / initSize bound) land with the semantics arm.
      True

/-- **Gas/call-aware run-definability** — the honest replacement of `RunDefinable`
(unsatisfiable on the gas/call domain, header lesson 4). Definability is threaded along
`RunStmts` derivations: at every cursor, the statement is definable at the state reached by
running the block prefix (any gas trace, any call stream, any block-entry state); the `ret` operand
and `branch` condition are bound at the post-statement state. SUPPLIED status: static per
program in the same over-approximate sense as the old bundle (state-uniform in the
block-entry state); decidable for concrete programs by running the fold — R9's checker
discharges it. -/
structure RunDefinableG (prog : Program) : Prop where
  /-- Every cursor's statement is definable at every state a `RunStmts` prefix-run reaches. -/
  stmts : ∀ (st st' : IRState) (T T' : Trace) (C C' : CallStream) (D D' : CreateStream)
      (L : Label) (b : Block) (pc : Nat) (s : Stmt),
    blockAt prog L = some b → b.stmts[pc]? = some s →
    RunStmts prog st T C D (b.stmts.take pc) st' T' C' D' →
    StmtDefinableG st' s
  /-- A `ret t` block's operand is bound at every `RunStmts`-post state. -/
  ret_def : ∀ (st st' : IRState) (T T' : Trace) (C C' : CallStream) (D D' : CreateStream)
      (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    RunStmts prog st T C D b.stmts st' T' C' D' →
    ∃ w, st'.locals t = some w
  /-- A `branch cond _ _` block's condition is bound at every `RunStmts`-post state. -/
  branch_def : ∀ (st st' : IRState) (T T' : Trace) (C C' : CallStream) (D D' : CreateStream)
      (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    RunStmts prog st T C D b.stmts st' T' C' D' →
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

/-! ## Shadowing-aware scoping (header lesson 8 — the round-3 reshape)

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
  | .create cs =>
      -- CREATE binds its `resultTmp` (the pushed address) exactly as a call binds its
      -- success flag, so the invalidation transfer is the `.call` transfer verbatim.
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
  | .create _ =>
      -- Step-1 placeholder (real total Prop): the create-result registration clause
      -- (twin of the `.call` clause, once `isCreateResult` exists) lands with the
      -- recorder/realisation step (`docs/create/BUILD-PLAN.md` §2 Step 6).
      True

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

/-! ## §1B new — CFG closure (presence + in-bounds) and the temporary `NoSlotSource` -/

/-- **Static CFG closure — presence + in-bounds half.** The presence and in-bounds halves
of `ClosedCFG` (`Surface.lean`): entry present, every jump/branch target present and
`< prog.blocks.size`. The OFFSET-bound halves of `ClosedCFG` (`offsetTable … < 2^32`) are
deliberately DROPPED here — they are DERIVED from `codeFits` in stage 1B-lemmas
(`pcBounds_of_codeFits`), not carried as hypotheses. SUPPLIED status: static, a finite
check on the program text (R9's checker). -/
structure CFGClosed (prog : Program) : Prop where
  /-- The entry block is present. -/
  entry_present : ∃ b, blockAt prog prog.entry = some b
  /-- Every jump target is present and in-bounds. -/
  jump_closed : ∀ (L : Label) (b : Block) (dst : Label),
    blockAt prog L = some b → b.term = .jump dst →
    (∃ b', blockAt prog dst = some b') ∧ dst.idx < prog.blocks.size
  /-- Both branch targets are present and in-bounds. -/
  branch_closed : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    ((∃ b', blockAt prog thenL = some b') ∧ thenL.idx < prog.blocks.size)
    ∧ ((∃ b', blockAt prog elseL = some b') ∧ elseL.idx < prog.blocks.size)

/-- **No `.slot` source RHS** — a source `assign t e` never carries the lowering-only
`.slot` marker (the arm-1 direction of `slots_slot`). Vacuous for real IR (no source
program writes a `.slot` expression); static and decidable. TEMPORARY: `Expr.slot` is
removed in Phase 2A (decision D4), and this predicate vanishes with it. -/
def NoSlotSource (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp) (n : Nat),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t (.slot n)) → False

/-! ## §1B new — the two scalar budgets -/

/-- **The pc budget** — the whole lowered program fits a 32-bit program counter. The scalar
that DERIVES (stage 1B-lemmas) every per-cursor `bound_*`/`gasBound`/`retEpilogueBound` /
`offsetTable` bound: each is a `<sub-range> ≤ (flatBytes prog).length` fact under `codeFits`.
This IS R6's loose `hsize` (RealisabilitySpec.lean:235-237), so supplying it discharges half
the R6 blocker. -/
def codeFits (prog : Program) : Prop := (flatBytes prog).length < 2 ^ 32

/-- The `chargeOf`-stack depth (opcode-slot count) an operand materialise pushes at the
given fuel. The SLOAD runtime cost VALUES are irrelevant to the LENGTH (each `.sload`
contributes exactly one entry whatever the charge, the `StackRoomOK` docstring's `∀ sloadChg`
fact), so the length is read at `sloadChg := fun _ => 0`. -/
def chargeDepth (prog : Program) (fuel : Nat) (e : Expr) : Nat :=
  (chargeOf (defsOf prog) (fun _ => 0) fuel e).length

/-- The operand stack depth a statement's materialise pushes — the `chargeOf`-length of the
operand group `StackRoomOK` bounds (sload key at reduced fuel; sstore's value + key + the
SSTORE slot). Non-materialising statements contribute `0`. -/
def stmtChargeDepth (prog : Program) : Stmt → Nat
  | .assign _ (.sload k) => chargeDepth prog (recomputeFuel prog - 1) (.tmp k)
  | .assign _ _          => 0
  | .sstore key value    =>
      chargeDepth prog (recomputeFuel prog) (.tmp value)
        + chargeDepth prog (recomputeFuel prog) (.tmp key) + 1
  | .call _              => 0
  | .create _            => 0

/-- The operand stack depth a terminator's materialise pushes — the `branch` condition and
the `ret` operand (the `StackRoomOK.branch`/`.ret` folds). `stop`/`jump` contribute `0`. -/
def termChargeDepth (prog : Program) : Term → Nat
  | .branch cond _ _ => chargeDepth prog (recomputeFuel prog) (.tmp cond)
  | .ret t           => chargeDepth prog (recomputeFuel prog) (.tmp t)
  | .stop            => 0
  | .jump _          => 0

/-- **The maximum operand stack depth over all cursors** — the max, over every block's
terminator and statements, of the operand-materialise `chargeOf`-length. `stackFits` bounds
this single scalar by 1024, which DERIVES (stage 1B-lemmas, `stackBounds_of_stackFits`) every
`StackRoomOK` fold (each fold's operand is one of these cursors). -/
def maxChargeDepth (prog : Program) : Nat :=
  prog.blocks.foldl (fun acc b =>
    max acc (max (termChargeDepth prog b.term)
                 (b.stmts.foldl (fun a s => max a (stmtChargeDepth prog s)) 0))) 0

/-- **The stack budget** — every operand materialise fits the 1024-slot EVM stack. The scalar
that DERIVES (stage 1B-lemmas) every per-cursor `StackRoomOK` fold. -/
def stackFits (prog : Program) : Prop := maxChargeDepth prog ≤ 1024

/-- **The SSA def-order rank** — a candidate rank witnessing `Acyclic (defsOf prog)`: a tmp's
rank is its SSA id, so in a define-before-use program every def's operands (earlier tmps,
smaller id) rank strictly below their target. This is the natural topological order on the
recompute-on-use def-graph; whether it actually witnesses `Acyclic` for a given `prog` is the
`IRWellFormed.acyclicDefs` obligation (discharged per-program in stage 1B-lemmas). -/
def defRank (_prog : Program) : Tmp → Nat := fun t => t.id

/-! ## §1B new — the `IRWellFormed` bundle -/

/-- **IR well-formedness** — the static, program-text-only well-formedness of a source
program, the soundness antecedent of the lowering claim (`WellFormed → codeFits →
stackFits → WellFormedLowered`, stage 1B-reshape). Every field is a fact of the program
text, decidable-in-principle per program (R9's checker's territory). NAME: `IRWellFormed`
(Eduardo's decision) — NOT `WellFormed`, which is a different single-use def at
`Materialise/DefsSound.lean:143`. -/
structure IRWellFormed (prog : Program) : Prop where
  /-- Gas/call-aware operand definability (replaces the unsatisfiable `RunDefinable`). -/
  defineBeforeUse : RunDefinableG prog
  /-- Static `defsOf`-cursor consistency (header lesson 6). -/
  defsConsistent  : DefsConsistent prog
  /-- The entry block is block 0 (its leading `JUMPDEST` is byte 0 = the entry frame's pc). -/
  entry0          : prog.entry.idx = 0
  /-- Static CFG closure (presence + in-bounds; offset bounds are DERIVED from `codeFits`). -/
  cfgClosed       : CFGClosed prog
  /-- The recompute-on-use def-graph is acyclic under `defRank` (fuel-sufficiency witness). -/
  acyclicDefs     : Acyclic (defsOf prog) (defRank prog)
  /-- Every within-block invalidation is healed by a reassign before the block ends. -/
  revalidates     : RevalidatesPerBlock prog
  /-- No source assign carries the lowering-only `.slot` marker. TEMPORARY: removed in Phase 2A. -/
  noSlotSource    : NoSlotSource prog

end Lir.V2
