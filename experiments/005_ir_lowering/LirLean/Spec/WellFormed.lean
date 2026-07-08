import LirLean.Spec.Semantics
import LirLean.Spec.Lowering
import LirLean.Materialise.MaterialiseGas
import LirLean.Materialise.DefsSound
import LirLean.Decode.DecodeLower

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
* the `IRWellFormed` bundle (Eduardo's name — NOT `WellFormed`, which is a different
  single-use def at `Materialise/DefsSound.lean:143`).

The derivation lemmas (`pcBounds_of_codeFits`, `stackBounds_of_stackFits`,
`wellFormedLowered_of_wellFormed`) live in `Spec/BudgetDerivations.lean` and the flagship
reshape files. All budgets read the total fold caches (`matCache`/`chargeCache`) — no fuel
anywhere. Sorry-free. -/

namespace Lir.V2

open Evm

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
target: a pure assign registers the `locOfExpr`-classified `Loc` of its own RHS
(`.remat e` for `imm`/`tmp`/`add`/`lt`); a gas/sload assign and a call/create result
register the spill slot `Loc.slot (slotOf t)` — exactly the arm `defEnv` records at the
same cursor, so this field is the statement that every def-site's `defEnv` entry equals
the program-global first-find `defsOf prog t`.

GROUND TRUTH this pins (`Lowering.lean`): `defsOf` is the **FIRST-find over program order**
(`defEnv`'s `find?` view, `defsOf_eq_defEnv_find`), while `emitStmt` keys its spill stash on
`defsOf t`. A tmp redefined with mixed pure/spill defs (e.g. `[.assign t (.imm 1),
.assign t .gas]`) therefore emits NO GAS byte at the shadowed def while
`EvalStmt.assignGas` still demands a gas-stream head — the flagship refutation of header
lesson 6. This field excludes exactly that mismatch (including pure/pure shadowing with a
DIFFERENT RHS, which breaks recompute-on-use the same way); single-assignment programs
(`exProg`) satisfy it trivially, so benign programs stay in scope. It is the static lift
of the per-cursor `hself` side condition the DefsSound walk already consumes
(`defsSound_preserved_assignPure`, `DefsSound.lean:269`). SUPPLIED status: static,
decidable per program (the R9 checker's territory). -/
def DefsConsistent (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat), blockAt prog L = some b →
    (∀ (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) →
      defsOf prog t = some (match e with
        | .gas => .slot (slotOf t)
        | .sload _ => .slot (slotOf t)
        | e' => locOfExpr e'))
    ∧ (∀ (cs : CallSpec) (t : Tmp), b.stmts[pc]? = some (.call cs) → cs.resultTmp = some t →
      defsOf prog t = some (.slot (slotOf t)))
    ∧ (∀ (cs : CreateSpec) (t : Tmp), b.stmts[pc]? = some (.create cs) → cs.resultTmp = some t →
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
  ∃ e', rematOf prog t' = some e' ∧ usesInExpr t e' ≠ 0

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
    rematOf prog t = some e → ¬ Lir.NonRecomputable prog t → ¬ I t →
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
      (e ≠ .gas → (∀ key, e ≠ .sload key) → rematOf prog t = some e)
      ∧ (e = .gas → Lir.isGasDef prog t)
      ∧ (∀ key, e = .sload key → Lir.isSloadDef prog t)
  | .sstore _ _ =>
      ∀ (t₀ : Tmp) (e₀ : Expr), rematOf prog t₀ = some e₀ → ∀ key, e₀ ≠ .sload key
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

/-- **The program-order def-env is a valid ordered list** — every rematerialised entry
`(t, Loc.remat e)` at position `i` references only tmps that appear at an EARLIER position
`j < i` in `defEnv prog`. This is exactly define-before-use (SSA) on the static def-graph:
the program-order carrier is a valid topological order (design §1.2, grounded in
`RunDefinableG` self-contained blocks + `DefsConsistent` first-find). It carries no
existential rank and no fuel-fitting side condition — it is the fuel-free replacement of
the old rank-based `acyclicDefs`, carried as the `IRWellFormed.defEnvOrdered` field
(design §1.3 / D4). Decidable per program (`decide`/`rfl` for `exProg`,
`defEnvOrdered_exProg`). -/
def DefEnvOrdered (prog : Program) : Prop :=
  ∀ (i : Nat) (t : Tmp) (e : Expr),
    (defEnv prog)[i]? = some (t, Loc.remat e) →
    ∀ t' : Tmp, usesInExpr t' e ≠ 0 →
      ∃ j, j < i ∧ ∃ loc : Loc, (defEnv prog)[j]? = some (t', loc)

/-! ## §S2 (c) — `matCache` last-wins vs `defsOf`/`find?` first-find (Phase 2A step S2)

`matCache` is a `Function.update` left-fold over `defEnv prog`, so its value at `t` is the
bytes of the **last** `defEnv` entry for `t`; `defsOf`/`find?` (S2 alignment,
`defsOf_eq_defEnv_find`) reads the **first**. They agree ONLY under SSA single-binding: every
`defEnv` entry for a given tmp id must carry the SAME `Loc`. That is exactly the
`DefsConsistent` content — every def-site of a tmp registers `defsOf`'s value — so the
`Loc` is the canonical `allocate prog t` at every entry, hence last = first. This is the
per-tmp alignment the prefix-stability engines consume (`matFold_take_eq_matCache` below
and its charge twin `chargeFold_take_eq_chargeCache` in `Materialise/MatFoldChannel.lean`,
the inductive cores of `matCache_unfold`/`chargeCache_unfold`).

`DefsConsistent` constrains `assign`, `call`-result AND `create`-result def-sites (the
create-result conjunct, phase-2A P1, is the exact twin of the call-result conjunct), so the
same-`Loc` argument reads the create-result registration straight off `DefsConsistent` — the
prior explicit `hcreate` hypothesis is gone. -/

/-- **Every `defEnv` entry carries the canonical `allocate` `Loc`.** Under `DefsConsistent`,
any `defEnv` entry `(t, loc)` has `loc = allocate prog t`: the def-site's `Loc`-valued
registration in `defsOf` (`DefsConsistent`) is exactly the `Loc` `defEnv` records at that
cursor, arm by arm. -/
theorem defEnv_entry_eq_allocate (prog : Program)
    (hdc : DefsConsistent prog)
    {t : Tmp} {loc : Loc} (hmem : (t, loc) ∈ defEnv prog) :
    allocate prog t = some loc := by
  rw [defEnv] at hmem
  obtain ⟨b, hbmem, hbmap⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, hsmem, hsmap⟩ := List.mem_filterMap.mp hbmap
  obtain ⟨i, hi, hbget⟩ := List.mem_iff_getElem.mp hbmem
  obtain ⟨j, hj, hsget⟩ := List.mem_iff_getElem.mp hsmem
  have hblockAt : blockAt prog ⟨i⟩ = some b := by
    show prog.blocks[i]? = some b
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hbget]
  have hstmt : b.stmts[j]? = some s := by
    rw [List.getElem?_eq_getElem hj, hsget]
  cases s with
  | assign t' e =>
    cases e with
    | gas =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' .gas hstmt
    | sload k =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.sload k) hstmt
    | imm w =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.imm w) hstmt
    | tmp t'' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.tmp t'') hstmt
    | add a c =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.add a c) hstmt
    | lt a c =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.lt a c) hstmt
    | slot n =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.slot n) hstmt
  | sstore _ _ => simp at hsmap
  | call cs =>
    obtain ⟨callee, gasFwd, rt⟩ := cs
    cases rt with
    | none => simp at hsmap
    | some t'' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).2.1 ⟨callee, gasFwd, some t''⟩ t'' hstmt rfl
  | create cs =>
    obtain ⟨value, initOffset, initSize, salt, rt⟩ := cs
    cases rt with
    | none => simp at hsmap
    | some t'' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).2.2 ⟨value, initOffset, initSize, salt, some t''⟩ t'' hstmt rfl

/-- **`matCache` last-wins agrees with `find?` first-find — the SSA single-binding crux.**
All `defEnv` entries for one tmp id carry the SAME `Loc` (each is the canonical `allocate prog
t`, `defEnv_entry_eq_allocate`), so the last-wins `matCache` fold and the first-find `defsOf`
select the same `Loc`. The per-tmp alignment step of the prefix-stability engines
(`matFold_take_eq_matCache` / `chargeFold_take_eq_chargeCache`). -/
theorem matCache_last_eq_first (prog : Program)
    (hdc : DefsConsistent prog)
    {t : Tmp} {loc₁ loc₂ : Loc}
    (h₁ : (t, loc₁) ∈ defEnv prog) (h₂ : (t, loc₂) ∈ defEnv prog) :
    loc₁ = loc₂ :=
  Option.some.inj
    ((defEnv_entry_eq_allocate prog hdc h₁).symm.trans
      (defEnv_entry_eq_allocate prog hdc h₂))

/-! ## §P2 — the `DefEnvOrdered` first-index toolkit

The two index facts every def-env induction descends on: `findIdx` is a lower bound at any
satisfying index (`findIdx_le_of_getElem?`), and `DefEnvOrdered` places every operand of a
`.remat` entry at a strictly smaller **first** index (`defEnv_operand_findIdx_lt`). These
drive the prefix-stability engines (`matFold_take_eq_matCache` below,
`chargeFold_take_eq_chargeCache`) and the fuel-free termination measure of the value
channel (`matDecMeasure`, `Materialise/MatFoldChannel.lean`). -/

/-- **`findIdx` is a lower bound at any satisfying index.** If `l[j]? = some x` and `p x`,
then the first index satisfying `p` is `≤ j`. (Pure `List` fact, by induction on `l`; stated
over `getElem?` to avoid `getElem` proof-term bookkeeping.) -/
theorem findIdx_le_of_getElem? {α : Type _} {p : α → Bool} :
    ∀ {l : List α} {j : Nat} {x : α}, l[j]? = some x → p x = true → l.findIdx p ≤ j
  | [], _, _, hj, _ => by simp at hj
  | a :: as, 0, x, hj, hx => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj; rw [List.findIdx_cons, hx, cond_true]
  | a :: as, j + 1, x, hj, hx => by
      simp only [List.getElem?_cons_succ] at hj
      rw [List.findIdx_cons]
      cases hpa : p a with
      | true => rw [cond_true]; exact Nat.zero_le _
      | false => rw [cond_false]; exact Nat.succ_le_succ (findIdx_le_of_getElem? hj hx)

/-- An operand `t'` of the `defEnv` entry that *defines* `t` (the first-find entry, at
`findIdx`) occurs at a strictly smaller first-index. This is exactly `DefEnvOrdered` read at
`t`'s own first-index `i = findIdx (·.1 == t)`: the witnessing earlier occurrence `j < i` of
`t'` bounds `t'`'s first-index (`findIdx (·.1 == t') ≤ j`). -/
theorem defEnv_operand_findIdx_lt {prog : Program} (h : DefEnvOrdered prog)
    {t t' : Tmp} {e : Expr}
    (hget : (defEnv prog)[(defEnv prog).findIdx (fun p => p.1 == t)]? = some (t, Loc.remat e))
    (hu : usesInExpr t' e ≠ 0) :
    (defEnv prog).findIdx (fun p => p.1 == t')
      < (defEnv prog).findIdx (fun p => p.1 == t) := by
  obtain ⟨j, hji, loc', hj⟩ := h _ t e hget t' hu
  have hle : (defEnv prog).findIdx (fun p => p.1 == t') ≤ j :=
    findIdx_le_of_getElem? hj (by simp)
  omega

/-! ## §P3 — the fold fixpoint `matCache_unfold` (Phase 2A P3, design §2.3)

The single load-bearing internal fold lemma: for a `t` PRESENT in `defEnv prog`,
`matCache prog t = matLoc (matCache prog) (canonical Loc of t)`; for an ABSENT `t`,
`matCache prog t = emitImm 0`. It is a **fold-to-fold** fixpoint — NOT a fold↔fuel bridge
(unsound, design §2.2 / header) — and it is the node that replaces the deleted
`matFueled_of_acyclic`: the induction is well-founded on the def-env FIRST index
(`DefEnvOrdered`: every operand of a `.remat` entry occurs strictly earlier,
`defEnv_operand_findIdx_lt`), with SSA single-binding (`matCache_last_eq_first`, P1) aligning
the last-occurrence entries. Obligation-3 foundation; everything downstream consumes it — the
value channel (`MatDecC`/`materialise_runsC`, `Materialise/MatFoldChannel.lean`) and the sim
layer repaired onto it at the P6+P7 swap. NO reference to `materialiseExpr` anywhere. -/

/-- The initial byte-cache the `matCache` fold starts from (the undefined-tmp fallback
`emitImm 0`). Named so the def-env inductions can range over `matFold` prefixes below the
top-level `matCache`. -/
def matInit : Tmp → List UInt8 := fun _ => emitImm 0

@[simp] theorem matCache_eq_matFold (prog : Program) :
    matCache prog = matFold matInit (defEnv prog) := rfl

/-- **Operand-locality of `matExpr`.** `matExpr` reads its cache only at the tmps the
expression uses, so two caches agreeing on every used tmp emit identical bytes. -/
theorem matExpr_congr {c c' : Tmp → List UInt8} {e : Expr}
    (h : ∀ t, usesInExpr t e ≠ 0 → c t = c' t) : matExpr c e = matExpr c' e := by
  cases e with
  | imm w => rfl
  | gas => rfl
  | slot n => rfl
  | tmp t => simp only [matExpr_tmp]; exact h t (by simp [usesInExpr])
  | add a b =>
      simp only [matExpr_add]
      rw [h a (by simp [usesInExpr]), h b (by simp [usesInExpr])]
  | lt a b =>
      simp only [matExpr_lt]
      rw [h a (by simp [usesInExpr]), h b (by simp [usesInExpr])]
  | sload k => simp only [matExpr_sload]; rw [h k (by simp [usesInExpr])]

/-- **A `matFold` that never rebinds `t` leaves `t` at its initial value.** -/
theorem matFold_notMem {t : Tmp} :
    ∀ (l : List (Tmp × Loc)) (c : Tmp → List UInt8),
      t ∉ l.map Prod.fst → matFold c l t = c t
  | [], _, _ => rfl
  | p :: l, c, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [matFold_cons, matFold_notMem l (matStep c p) h.2]
      exact Function.update_of_ne h.1 _ _

/-- **Last-occurrence split of a `matFold` value.** For any list, either `t` is never a key
(and the fold's value at `t` is the initial one), or the list splits at `t`'s LAST occurrence
and the fold's value at `t` is `matLoc` of that entry's `Loc` under the prefix-fold. This is
the reusable readout of the last-wins `Function.update` fold. -/
theorem matFold_split (c : Tmp → List UInt8) (t : Tmp) :
    ∀ (l : List (Tmp × Loc)),
      (t ∉ l.map Prod.fst ∧ matFold c l t = c t) ∨
      (∃ pre loc post, l = pre ++ (t, loc) :: post ∧ t ∉ post.map Prod.fst ∧
         matFold c l t = matLoc (matFold c pre) loc) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => exact Or.inl ⟨by simp, rfl⟩
  | append_singleton l x ih =>
      have hval : matFold c (l ++ [x]) t
          = if t = x.1 then matLoc (matFold c l) x.2 else matFold c l t := by
        have hfold : matFold c (l ++ [x]) = matStep (matFold c l) x := by
          simp only [matFold, List.foldl_append]; rfl
        rw [hfold]; simp only [matStep, Function.update_apply]
      by_cases hx : t = x.1
      · refine Or.inr ⟨l, x.2, [], ?_, by simp, ?_⟩
        · have hxe : x = (t, x.2) := by rw [hx]
          rw [hxe]
        · rw [hval, if_pos hx]
      · cases ih with
        | inl h =>
            refine Or.inl ⟨?_, ?_⟩
            · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨h.1, hx⟩
            · rw [hval, if_neg hx]; exact h.2
        | inr h =>
            obtain ⟨pre, loc, post, heq, hpost, hvv⟩ := h
            refine Or.inr ⟨pre, loc, post ++ [x], ?_, ?_, ?_⟩
            · rw [heq, List.append_assoc, List.cons_append]
            · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨hpost, hx⟩
            · rw [hval, if_neg hx]; exact hvv

/-- **The `defEnv` entry at `t`'s FIRST index carries `t`'s canonical `Loc`.** Under
`DefsConsistent` every entry for `t` carries the canonical `allocate prog t`
(`defEnv_entry_eq_allocate`), and `defsOf` *is* the first-find over `defEnv`
(`defsOf_eq_defEnv_find`), so the `findIdx` (first) entry — the one
`defsOf`/`defEnv_operand_findIdx_lt` read — is `(t, loc)`. -/
theorem defEnv_findIdx_entry (prog : Program) (hdc : DefsConsistent prog)
    {t' : Tmp} {loc : Loc} (hmem : (t', loc) ∈ defEnv prog) :
    (defEnv prog)[(defEnv prog).findIdx (fun p => p.1 == t')]? = some (t', loc) := by
  have hd : defsOf prog t' = some loc := defEnv_entry_eq_allocate prog hdc hmem
  rw [defsOf_eq_defEnv_find, List.find?_eq_getElem?_findIdx, Option.map_eq_some_iff] at hd
  obtain ⟨⟨tt, locc⟩, hget, hsnd⟩ := hd
  have htt : tt = t' := by
    have := List.findIdx_of_getElem?_eq_some hget; simpa using this
  subst htt
  have hll : locc = loc := hsnd
  rw [hget, hll]

/-- **An operand of a `.remat` entry at position `i` occurs somewhere in the prefix `take i`.**
Directly `DefEnvOrdered` (operand at some `j < i`), landed to a `take`-prefix membership. -/
theorem operand_mem_take {prog : Program} (hord : DefEnvOrdered prog)
    {i : Nat} {t' t'' : Tmp} {e : Expr}
    (hget : (defEnv prog)[i]? = some (t', Loc.remat e)) (hu : usesInExpr t'' e ≠ 0) :
    t'' ∈ ((defEnv prog).take i).map Prod.fst := by
  obtain ⟨j, hji, locj, hj⟩ := hord i t' e hget t'' hu
  have hjt : ((defEnv prog).take i)[j]? = some (t'', locj) := by
    rw [List.getElem?_take, if_pos hji]; exact hj
  exact List.mem_map_of_mem (List.mem_of_getElem? hjt)

/-- **Prefix stability of `matCache`** — the induction engine of `matCache_unfold`. Any
def-env prefix that already contains an occurrence of `t'` agrees with the full `matCache` at
`t'`. Well-founded on `t'`'s first index (`DefEnvOrdered` via `defEnv_operand_findIdx_lt`);
SSA single-binding (`matCache_last_eq_first`) makes the two last-occurrence entries carry the
same `Loc`, and operand-locality (`matExpr_congr`) closes the `.remat` step. -/
theorem matFold_take_eq_matCache (prog : Program)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog) :
    ∀ (t' : Tmp) (p : Nat), t' ∈ ((defEnv prog).take p).map Prod.fst →
      matFold matInit ((defEnv prog).take p) t' = matCache prog t' := by
  have key : ∀ (n : Nat) (t' : Tmp),
      (defEnv prog).findIdx (fun p => p.1 == t') = n →
      ∀ (p : Nat), t' ∈ ((defEnv prog).take p).map Prod.fst →
        matFold matInit ((defEnv prog).take p) t' = matCache prog t' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t' hn p hmem
      have hmemFull : t' ∈ (defEnv prog).map Prod.fst := by
        obtain ⟨y, hy, hy2⟩ := List.mem_map.mp hmem
        exact List.mem_map.mpr ⟨y, List.take_subset p _ hy, hy2⟩
      rcases matFold_split matInit t' ((defEnv prog).take p) with hA | hA
      · exact absurd hmem hA.1
      obtain ⟨preA, locA, postA, hsplitA, _hpostA, hvalA⟩ := hA
      rcases matFold_split matInit t' (defEnv prog) with hB | hB
      · exact absurd hmemFull hB.1
      obtain ⟨preB, locB, postB, hsplitB, _hpostB, hvalB⟩ := hB
      have hmemA : (t', locA) ∈ defEnv prog :=
        List.take_subset p _ (by rw [hsplitA]; simp)
      have hmemB : (t', locB) ∈ defEnv prog := by rw [hsplitB]; simp
      have hll : locA = locB := matCache_last_eq_first prog hdc hmemA hmemB
      rw [hvalA, matCache_eq_matFold, hvalB, ← hll]
      have hpreA : preA = (defEnv prog).take preA.length := by
        have h1 : preA <+: (defEnv prog).take p := by
          rw [hsplitA]; exact List.prefix_append _ _
        exact List.prefix_iff_eq_take.mp (h1.trans (List.take_prefix p _))
      have hpreB : preB = (defEnv prog).take preB.length := by
        have h1 : preB <+: defEnv prog := by rw [hsplitB]; exact List.prefix_append _ _
        exact List.prefix_iff_eq_take.mp h1
      have hlenA : preA.length < p := by
        have hlen : ((defEnv prog).take p).length ≤ p := by
          rw [List.length_take]; exact Nat.min_le_left _ _
        rw [hsplitA] at hlen
        simp only [List.length_append, List.length_cons] at hlen
        omega
      have hgetA : (defEnv prog)[preA.length]? = some (t', locA) := by
        have h0 : ((defEnv prog).take p)[preA.length]? = some (t', locA) := by
          rw [hsplitA, List.getElem?_append_right (Nat.le_refl _)]; simp
        rwa [List.getElem?_take_of_lt hlenA] at h0
      have hgetB : (defEnv prog)[preB.length]? = some (t', locB) := by
        rw [hsplitB, List.getElem?_append_right (Nat.le_refl _)]; simp
      cases locA with
      | slot n => rfl
      | remat e =>
          simp only [matLoc_remat]
          apply matExpr_congr
          intro t'' hu
          have hlt : (defEnv prog).findIdx (fun p => p.1 == t'') < n := by
            rw [← hn]
            exact defEnv_operand_findIdx_lt hord (defEnv_findIdx_entry prog hdc hmemA) hu
          have hmemA'' : t'' ∈ ((defEnv prog).take preA.length).map Prod.fst :=
            operand_mem_take hord hgetA hu
          have hgetB' : (defEnv prog)[preB.length]? = some (t', Loc.remat e) := by
            rw [hgetB, hll]
          have hmemB'' : t'' ∈ ((defEnv prog).take preB.length).map Prod.fst :=
            operand_mem_take hord hgetB' hu
          have hAeq := ih _ hlt t'' rfl preA.length hmemA''
          have hBeq := ih _ hlt t'' rfl preB.length hmemB''
          rw [← hpreA] at hAeq
          rw [← hpreB] at hBeq
          rw [hAeq, hBeq]
  intro t' p hmem
  exact key _ t' rfl p hmem

/-- **`matCache_unfold` — the fold fixpoint.** For a `t` present in `defEnv prog`, the cached
bytes of `t` are `matLoc` of its (unique, SSA-canonical) `Loc` resolved under the FULL cache.
The replacement for `matFueled_of_acyclic`: proved from the prefix-stability engine, NO
fold↔fuel bridge. -/
theorem matCache_unfold (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {loc : Loc} (hmem : (t, loc) ∈ defEnv prog) :
    matCache prog t = matLoc (matCache prog) loc := by
  rcases matFold_split matInit t (defEnv prog) with hB | hB
  · exact absurd (List.mem_map.mpr ⟨(t, loc), hmem, rfl⟩) hB.1
  obtain ⟨preB, locB, postB, hsplitB, _hpostB, hvalB⟩ := hB
  have hmemB : (t, locB) ∈ defEnv prog := by rw [hsplitB]; simp
  have hll : loc = locB := matCache_last_eq_first prog hdc hmem hmemB
  rw [matCache_eq_matFold, hvalB, hll]
  have hpreB : preB = (defEnv prog).take preB.length := by
    have h1 : preB <+: defEnv prog := by rw [hsplitB]; exact List.prefix_append _ _
    exact List.prefix_iff_eq_take.mp h1
  have hgetB : (defEnv prog)[preB.length]? = some (t, locB) := by
    rw [hsplitB, List.getElem?_append_right (Nat.le_refl _)]; simp
  cases locB with
  | slot n => rfl
  | remat e =>
      simp only [matLoc_remat]
      apply matExpr_congr
      intro t'' hu
      have hgetB' : (defEnv prog)[preB.length]? = some (t, Loc.remat e) := hgetB
      have hmem'' : t'' ∈ ((defEnv prog).take preB.length).map Prod.fst :=
        operand_mem_take hord hgetB' hu
      have heq := matFold_take_eq_matCache prog hdc hord t'' preB.length hmem''
      rw [← hpreB] at heq
      rw [heq, matCache_eq_matFold]

/-- **Corollary — rematerialised tmp.** The cache bytes of a `.remat e` tmp are the
byte-assembly of `e` under the full cache. -/
theorem matCache_remat (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {e : Expr} (hmem : (t, Loc.remat e) ∈ defEnv prog) :
    matCache prog t = matExpr (matCache prog) e := by
  rw [matCache_unfold prog hdc hord hmem, matLoc_remat]

/-- **Corollary — spilled tmp.** The cache bytes of a `.slot n` tmp are the slot readback
`PUSH n; MLOAD`. -/
theorem matCache_slot (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {n : Nat} (hmem : (t, Loc.slot n) ∈ defEnv prog) :
    matCache prog t = emitImm (UInt256.ofNat n) ++ [Byte.mload] := by
  rw [matCache_unfold prog hdc hord hmem, matLoc_slot]

/-- **Corollary — absent tmp.** A tmp with no `defEnv` entry falls back to `emitImm 0`
(the fold's undefined-tmp leaf). -/
theorem matCache_absent (prog : Program) {t : Tmp}
    (hmem : t ∉ (defEnv prog).map Prod.fst) : matCache prog t = emitImm 0 := by
  rw [matCache_eq_matFold, matFold_notMem (defEnv prog) matInit hmem]; rfl

/-! ## §1B new — the two scalar budgets -/

/-- **The pc budget** — the whole lowered program fits a 32-bit program counter. The scalar
that DERIVES (stage 1B-lemmas) every per-cursor `bound_*`/`gasBound`/`retEpilogueBound` /
`offsetTable` bound: each is a `<sub-range> ≤ (flatBytes prog).length` fact under `codeFits`.
This IS R6's loose `hsize` (RealisabilitySpec.lean:235-237), so supplying it discharges half
the R6 blocker. -/
def codeFits (prog : Program) : Prop := (flatBytes prog).length < 2 ^ 32

/-! ## The stack budget — over `chargeCache` lengths (fuel-free)

The stack-room budget folds read the total charge fold `chargeCache`
(`Materialise/MaterialiseGas.lean`). The `.tmp`-only operand shape lets the depth key on the
`Tmp` directly (`chargeCache prog sc : Tmp → List ℕ`). Every fold's charge-list LENGTH is
`sloadChg`-independent (`chargeCache_length_sloadChg_eq`), so the depths read the LENGTH at
`sloadChg := fun _ => 0`. The derivation `stackBounds_of_stackFits` (every `StackRoomOK`
fold from the single scalar bound) lives in `Spec/BudgetDerivations.lean` (with the generic
max helpers). -/

/-- The charge-fold stack depth (opcode-slot count) an operand `t`'s materialise pushes, read
at `sloadChg := fun _ => 0` (the LENGTH is `sloadChg`-independent,
`chargeCache_length_sloadChg_eq`). -/
def chargeDepth (prog : Program) (t : Tmp) : Nat :=
  (chargeCache prog (fun _ => 0) t).length

/-- The operand stack depth a statement's materialise pushes over the charge fold — the
charge-length of the operand group `StackRoomOK` bounds (sload key; sstore's value + key +
the SSTORE slot). Non-materialising statements contribute `0`. -/
def stmtChargeDepth (prog : Program) : Stmt → Nat
  | .assign _ (.sload k) => chargeDepth prog k
  | .assign _ _          => 0
  | .sstore key value    => chargeDepth prog value + chargeDepth prog key + 1
  | .call _              => 0
  | .create _            => 0

/-- The operand stack depth a terminator's materialise pushes — the `branch` condition and
the `ret` operand (the `StackRoomOK.branch`/`.ret` folds). `stop`/`jump` contribute `0`. -/
def termChargeDepth (prog : Program) : Term → Nat
  | .branch cond _ _ => chargeDepth prog cond
  | .ret t           => chargeDepth prog t
  | .stop            => 0
  | .jump _          => 0

/-- **The maximum operand stack depth over all cursors** — the max, over every block's
terminator and statements, of the operand-materialise charge length. `stackFits` bounds this
single scalar by 1024, which DERIVES (`stackBounds_of_stackFits`,
`Spec/BudgetDerivations.lean`) every `StackRoomOK` fold (each fold's operand is one of these
cursors). -/
def maxChargeDepth (prog : Program) : Nat :=
  prog.blocks.foldl (fun acc b =>
    max acc (max (termChargeDepth prog b.term)
                 (b.stmts.foldl (fun a s => max a (stmtChargeDepth prog s)) 0))) 0

/-- **The stack budget** — every operand materialise fits the 1024-slot EVM stack. The scalar
that DERIVES every per-cursor `StackRoomOK` fold. -/
def stackFits (prog : Program) : Prop := maxChargeDepth prog ≤ 1024

/-- **Static stack-room bounds** — the per-cursor `chargeCache`-length ≤ 1024 folds the sims
consume, quantified `∀ sloadChg` and PROVABLE that way (the LENGTH is `sloadChg`-independent,
`chargeCache_length_sloadChg_eq`). Derived from `stackFits` by `stackBounds_of_stackFits`.
SUPPLIED status: static, decidable per program (R9's checker discharges it). -/
structure StackRoomOK (prog : Program) : Prop where
  /-- The `branch` cond-materialise stack fold. -/
  branch : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    (chargeCache prog sloadChg cond).length ≤ 1024
  /-- The spilled-sload key-prefix stack fold. -/
  sloadKey : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    (chargeCache prog sloadChg k).length ≤ 1024
  /-- The `sstore` two-operand stack fold. -/
  sstore : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.sstore key value) →
    (chargeCache prog sloadChg value).length
      + (chargeCache prog sloadChg key).length + 1 ≤ 1024
  /-- The `ret` operand stack fold. -/
  ret : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    (chargeCache prog sloadChg t).length ≤ 1024

/-! ## §1B new — the `IRWellFormed` bundle -/

/-- **IR well-formedness** — the static, program-text-only well-formedness of a source
program, the soundness antecedent of the lowering claim (`IRWellFormed → codeFits →
stackFits → WellLowered`, stage 1B-reshape `wellFormedLowered_of_IRWellFormed`). Every
field is a fact of the program text, decidable-in-principle per program (R9's checker's
territory). NAME: `IRWellFormed` (Eduardo's decision) — NOT `WellFormed`, which is a
different single-use def at `Materialise/DefsSound.lean:143`. -/
structure IRWellFormed (prog : Program) : Prop where
  /-- Gas/call-aware operand definability (replaces the unsatisfiable `RunDefinable`). -/
  defineBeforeUse : RunDefinableG prog
  /-- Static `defsOf`-cursor consistency (header lesson 6). -/
  defsConsistent  : DefsConsistent prog
  /-- The entry block is block 0 (its leading `JUMPDEST` is byte 0 = the entry frame's pc). -/
  entry0          : prog.entry.idx = 0
  /-- Static CFG closure (presence + in-bounds; offset bounds are DERIVED from `codeFits`). -/
  cfgClosed       : CFGClosed prog
  /-- Program order is a valid topological order of the recompute-on-use def-graph:
  every rematerialised `defEnv` entry references only earlier-registered tmps
  (define-before-use SSA on the ordered carrier). This is what makes the fold caches
  (`matCache`/`chargeCache`) fully expand — the `matCache_unfold`/`chargeCache_unfold`
  fixpoints and the `matDecMeasure` termination of the value channel all descend on it.
  No existential rank, no fuel-fitting side condition. Decidable per program
  (`defEnvOrdered_exProg` by `decide`). -/
  defEnvOrdered   : DefEnvOrdered prog
  /-- Every within-block invalidation is healed by a reassign before the block ends. -/
  revalidates     : RevalidatesPerBlock prog
  /-- No source assign carries the lowering-only `.slot` marker. TEMPORARY: removed in Phase 2A. -/
  noSlotSource    : NoSlotSource prog
  /-- **Spill-slot addressability** at every gas/sload cursor: the target tmp's canonical slot
  `slotOf t = t.id * 32` is byte- and platform-addressable. A bound on the tmp ids that carry
  a spilled def; not derivable from the control structure or the two budgets, so it is a
  supplied static well-formedness field (the `WellLowered.slotAddr` obligation). -/
  slotAddr        : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt prog L = some b →
    (b.stmts[pc]? = some (.assign t .gas)
      ∨ ∃ k, b.stmts[pc]? = some (.assign t (.sload k))) →
    slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits

end Lir.V2
