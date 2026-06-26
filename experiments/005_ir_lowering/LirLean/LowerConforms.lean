import LirLean.LowerDecode

/-!
# LirLean — `sim_cfg` + `lower_conforms` (Layer **F** of the general `lower_conforms` grind)

The capstone of the call-free, **world-channel** `lower_conforms` grind. It threads the
per-block bricks of Layers C–E into a whole-CFG simulation (`sim_cfg`, by induction on
`V2.RunFrom`) and then ties that to the instrumented recording interpreter `runWithLog`
(`lower_conforms`).

## The two structured per-block hypotheses

The induction is on `V2.RunFrom`, the IR CFG driver. Each constructor runs a block's
statement list and then its terminator. The statement-list simulation is Layer D
(`sim_stmts_block`); the terminator simulation is Layer E (`sim_term_halt_*` /
`sim_term_edge_*`). Rather than re-thread Layers D and E's *enormous* per-block structured
hypothesis bundles (decode coverage at every static cursor, gas/stack envelopes, the
SSTORE/SLOAD/GAS realisability ties, the jump-destination round-trips) through the CFG
induction — they are per-block and per-intermediate-frame, so they cannot be stated once up
front — we abstract them into **two** structured hypotheses at exactly the altitude of the
Layer-D / Layer-E conclusions:

* `SimStmtStep prog sloadChg obs o L b` (Layer D, `SimStmts.lean`) — the per-statement
  simulation, already the unit Layer D consumes.
* `SimTermStep prog sloadChg obs o self L b` (Layer E, here) — the per-terminator
  simulation: from `Corr` at the terminator cursor and the block's `RunStmts`-post IR state,
  either **halt** with a frame whose `observe` *world* matches the IR halt's world (the `stop`
  / `ret` arms, E1), or **run to the taken successor's entry** re-establishing `Corr` at
  `(succ, 0)` (the `jump` / `branch` arms, E2).

`SimTermStep` is the exact union of E1's and E2's conclusions, dispatched on `b.term` and the
IR run's terminator facts. Discharging it for a concrete program is a mechanical case split on
`b.term` feeding `sim_term_halt_stop` / `sim_term_halt_ret` / `sim_term_edge_jump` /
`sim_term_edge_branch` their structured-hypothesis bundles (the A1–A3 decode anchors, the E3
jump-validity, the gas envelopes) — exactly as `SimStmtStep` is discharged for the statement
arms. This is the **realisability contract**: `sim_cfg` runs the IR under the oracles the
lowered bytecode realises, and carries the per-block realisability as `SimStmtStep` /
`SimTermStep` (the `docs/ir-design-v3.md` §7 supplied-observation model).

## Scope — call-free, world channel

The block's statements must be `CallFree` (Layer D's scope — the lowered CALL leaves its
success flag on the bytecode stack, breaking the `stack = []` induction; folded in once the
flag is consumed). And the channel is the **world** (storage) component: `observe`'s `result`
is the value-free `.stopped` boundary (the RETURN value channel is the tracked deferral,
`V2/RunLog.lean` `observe` doc). `sim_cfg`'s conclusion asserts the world component of
`observe self (endFrame last halt)`.

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports the Layer-E bricks);
nothing here touches `V2/Machine.lean` / `V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch
open Lir.V2

/-! ## The per-terminator simulation hypothesis `SimTermStep`

`SimTermStep prog sloadChg obs o self L b` packages Layer E's call-free conclusion uniformly
over the four IR terminators, matching `V2.RunFrom`'s constructor shape. It is what the CFG
induction consumes after Layer D has run the block's statements to the terminator cursor.

Two productions, exactly E1's and E2's conclusions:

* **halt** (`stop` / `ret`) — given `Corr` at the terminator cursor and the matching IR halt
  observable `Oend`, produce a halting frame `last` whose `observe` *world* is `Oend.world`;
* **edge** (`jump` / `branch`) — given `Corr` at the terminator cursor and the IR's chosen
  successor `succ`, run to `succ`'s entry frame re-establishing `Corr` at `(succ, 0)`.

The dispatch is on `b.term` together with the IR-side terminator witnesses (`hterm`, and for
the edges the resolved successor), so a concrete discharge case-splits `b.term` and feeds the
four Layer-E lemmas. Quantified over the post-`RunStmts` IR state `st'` and the terminator
frame `frT` (the frame Layer D delivers at the terminator cursor). -/

/-- **The per-terminator simulation step** (Layer E, call-free, abstracted over the block).
For block `b` at label `L`, a frame `frT` in `Corr`-correspondence with the post-statement IR
state `st'` at the terminator cursor `(L, b.stmts.length)`:

* if `b.term` is a **halt** (`stop` or `ret t`), there is a halting frame `last` reached from
  `frT` whose `observe self` **world** is the IR halt's world (`st'.world` for `stop`;
  `st'.world` for `ret`, the value-free world channel);
* if `b.term` is an **edge** (`jump dst`, or `branch` taking `succ`), there is a frame `fr'`
  reached from `frT` re-establishing `Corr` at the taken successor's entry `(succ, 0)`.

The halt case carries the IR halt observable `O` so the world equation is stated against the
same `O` the `RunFrom` halt constructor produces; the edge case carries the IR-resolved
successor `succ` so the re-established `Corr` is at the block the `RunFrom` recursion enters. -/
structure SimTermStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (o : V2.CallOracle) (selfAddr : AccountAddress) (L : Label) (b : Block) : Prop where
  /-- **Halt arm** (`stop` / `ret`). From `Corr` at the terminator cursor and a halting IR
  terminator with halt-world `wHalt` (`st'.world`), a halting frame matching the world. -/
  halt : ∀ (st' : V2.IRState) (frT : Frame),
    Corr prog sloadChg obs st' frT L b.stmts.length →
    (b.term = .stop ∨ ∃ t, b.term = .ret t) →
    ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
      ∧ (observe selfAddr (endFrame last haltSig)).world = st'.world
  /-- **Edge arm** (`jump` / `branch`). From `Corr` at the terminator cursor and the
  IR-resolved successor `succ` of the edge, a frame at `succ`'s entry re-establishing `Corr`. -/
  edge : ∀ (st' : V2.IRState) (frT : Frame) (succ : Label),
    Corr prog sloadChg obs st' frT L b.stmts.length →
    (b.term = .jump succ
      ∨ (∃ cond elseL cw, b.term = .branch cond succ elseL
            ∧ st'.locals cond = some cw ∧ cw ≠ 0)
      ∨ (∃ cond thenL, b.term = .branch cond thenL succ ∧ st'.locals cond = some 0)) →
    ∃ fr', Runs frT fr' ∧ Corr prog sloadChg obs st' fr' succ 0

/-! ## `WellFormedLowered` — the structural side-conditions, folded

The per-shape `_lowered` wrappers (`sim_sstore_stmt_lowered`, `sim_term_halt_ret_lowered`,
`sim_term_edge_jump_lowered`, `sim_term_edge_branch_lowered`) carry two kinds of *structural*
(non-runtime) side-condition that depend only on the **program text**, not on the trace:

* **recompute-fuel sufficiency** — `MatFueled (defsOf prog) (recomputeFuel prog) e` for every
  expression `e` the block materialises (the `sstore` operands, the `ret` operand). This is the
  honest well-formedness tie: `recomputeFuel` exceeds the def-chain depth of every materialised
  tmp. It is **discharged structurally** from a rank-based SSA acyclicity witness in
  `Acyclic.lean` (`wellFormedLowered_of_acyclic`), so an acyclic program carries no `MatFueled`
  hypothesis (`lower_conforms_acyclic`);
* **program-size pc/offset bounds** — every static cursor / block offset fits a 32-bit pc
  (`< 2^32`). These are pure facts about `offsetTable` / `termOf` / `pcOf` and the size of
  `lower prog`.

`WellFormedLowered prog` folds exactly those structural side-conditions, quantified over every
present block and (for the statement bounds) every cursor. The builders below pull the relevant
field per shape, so the structural residual leaves the builder hypotheses entirely — only the
*genuine* runtime recording-correspondence ties (`SstoreRealises` / `hret` / gas envelopes — the
§7 supplied-observation contract) stay explicit. The `validJumps`-recording ties are no longer
among them: they are discharged structurally from `Corr` (`Corr.validJumps_lower`). -/

/-- **The folded structural well-formedness predicate.** Bundles, over every present block of
`prog`, the recompute-fuel sufficiency of each materialised operand (`MatFueled`) and the
program-size pc/offset bounds (`< 2^32`) the `_lowered` wrappers carry. Purely structural — a
function of the program text, independent of the run. The `MatFueled` fields are discharged from
acyclicity (`Acyclic.lean`); the bounds are a finite check on the lowered program size. -/
structure WellFormedLowered (prog : Program) : Prop where
  /-- `sstore` operand fuel-sufficiency, at every `sstore` cursor of every present block. -/
  matFueled_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    MatFueled (defsOf prog) (recomputeFuel prog) (.tmp value)
    ∧ MatFueled (defsOf prog) (recomputeFuel prog) (.tmp key)
  /-- `sstore` pc bound: the statement's operand bytes fit a 32-bit pc. -/
  bound_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    pcOf prog L pc
      + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2 ^ 32
  /-- `ret` operand fuel-sufficiency, at every `ret`-terminated present block. -/
  matFueled_ret : ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    MatFueled (defsOf prog) (recomputeFuel prog) (.tmp t)
  /-- `ret` pc bound: the RETURN-value operand bytes fit a 32-bit pc. -/
  bound_ret : ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    termOf prog L
      + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length ≤ 2 ^ 32
  /-- `stop` pc bound: the terminator cursor fits a 32-bit pc. -/
  bound_stop : ∀ (L : Label) (b : Block),
    prog.blocks.toList[L.idx]? = some b → b.term = .stop →
    termOf prog L < 2 ^ 32
  /-- `jump` pc/offset bounds: the `PUSH4; JUMP` bytes and the destination offset fit. -/
  bound_jump : ∀ (L : Label) (b : Block) (dst : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
    termOf prog L + 5 < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32
  /-- `branch` pc/offset bounds: the cond-materialise + two `PUSH4; J…` bytes and both
  successor offsets fit. -/
  bound_branch : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    termOf prog L
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length + 11 < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32

/-! ## Discharging `SimStmtStep` / `SimTermStep` for the call-free fragment

`SimStmtStep`/`SimTermStep` are the per-block realisability bundles `sim_cfg` consumes.
Discharging them for a concrete program is a case split on the statement / terminator
shape feeding the Layer-C/E lemmas (`sim_assign` / `sim_sstore_stmt` ; `sim_term_*`).
Those lemmas in turn carry their *own* honest structured hypotheses — the per-byte
`MatDec` decode coverage at the runtime cursors, the immediate round-trips, the gas/stack
envelopes, and the genuine SLOAD/SSTORE/GAS realisability ties (the §7
supplied-observation contract). The two builders below carry exactly that residual,
minimised to the per-(cursor/frame) ties, so `sim_cfg`/`lower_conforms` see a thin
realisability surface rather than the opaque `SimStmtStep`/`SimTermStep` props.

### The `assign`-arm discharge (fully closed down to the genuine ties)

The pure/gas `assign` arm needs *no* decode bundle — `emitStmt … (.assign _ _) = []`, so
the lowered segment is `Runs.refl` and `sim_assign` consumes only the per-step scoping
(`StepScoped`, the program-global `WellScoped` follow-up) and the post-state realisability
ties (`wellScoped'`/`SloadRealises`/`GasRealises`), threaded over the same (unchanged)
frame. `simStmtStep_assign` discharges `SimStmtStep` for an **assign-only** call-free block
down to exactly those carried ties — a complete result for the pure-arithmetic /
gas-introspection statement fragment (no storage writes). The `sstore` arm additionally
needs the `MatDec` decode coverage over `materialiseExpr` at the runtime cursors (the
generic A2 reconstruction — the documented remaining milestone), and so is carried whole. -/

/-- **`SimStmtStep` for an assign-only call-free block.** If every statement of `b` is an
`Stmt.assign`, then — given, at every cursor, the per-step scoping (`StepScoped`) and the
post-state realisability ties (the genuine recording-correspondence side-conditions:
`wellScoped`, `SloadRealises`, `GasRealises` over the post-state at the *same* frame, since
the assign emits no bytes) — `SimStmtStep` holds. Every obligation routes through
`sim_assign`; nothing is decoded (the assign lowering is empty). -/
theorem simStmtStep_assign {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hassign : ∀ s ∈ b.stmts, ∃ t e, s = .assign t e)
    -- the genuine per-cursor ties (the §7 supplied-observation contract at each step):
    (hties : ∀ (pc : Nat) (t : Tmp) (e : Expr) (st0 st0' : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.assign t e) →
        Corr prog sloadChg obs st0 fr0 L pc →
        StepScoped prog st0 (.assign t e)
        ∧ (∀ t', st0'.locals t' ≠ none →
              ¬ NonRecomputable prog t' ∧ defsOf prog t' ≠ none)
        ∧ SloadRealises sloadChg st0' fr0
        ∧ GasRealises obs fr0) :
    SimStmtStep prog sloadChg obs o L b := by
  intro pc s st0 st0' T0 T0' fr0 hget hnc hcorr hstep
  obtain ⟨t, e, hse⟩ := hassign s (List.mem_iff_getElem?.mpr ⟨pc, hget⟩)
  subst hse
  obtain ⟨hsc, hscoped', hsload', hgas'⟩ := hties pc t e st0 st0' fr0 hget hcorr
  obtain ⟨_, hc', _⟩ := sim_assign hb hget hcorr hstep hsc hscoped' hsload' hgas'
  exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩

/-! ### The `sstore`-arm discharge (decode-free via `sim_sstore_stmt_lowered`)

For an `sstore`-only call-free block, every statement routes through `sim_sstore_stmt_lowered`
— the decode bundle (the operand `MatDec`s + the consuming `SSTORE`) is already discharged
generically over `lower prog` inside the wrapper. The structural side-conditions (`MatFueled`
×2 + the pc bound) are pulled from `WellFormedLowered`; the only residual is the genuine runtime
SSTORE recording-correspondence tie (`SstoreRealises` + the non-zero-value `hnz`, the §7
supplied-observation contract at the internal SSTORE frame). -/

/-- **`SimStmtStep` for an `sstore`-only call-free block.** If every statement of `b` is an
`Stmt.sstore`, then — given `WellFormedLowered` (the structural fuel/pc side-conditions) and,
at every cursor, the genuine runtime SSTORE ties (gas/stack envelopes, `SstoreRealises`, and the
non-zero written value) — `SimStmtStep` holds. The decode is discharged inside
`sim_sstore_stmt_lowered`. -/
theorem simStmtStep_sstore {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hwf : WellFormedLowered prog)
    (hsstore : ∀ s ∈ b.stmts, ∃ key value, s = .sstore key value)
    -- the genuine per-cursor runtime SSTORE ties (the §7 supplied-observation contract):
    (hties : ∀ (pc : Nat) (key value : Tmp) (kw vw : Word) (st0 : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.sstore key value) →
        Corr prog sloadChg obs st0 fr0 L pc →
        st0.locals key = some kw → st0.locals value = some vw →
        StepScoped prog st0 (.sstore key value)
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).sum
            + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).sum
            ≤ fr0.exec.gasAvailable.toNat
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
            + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024
        ∧ (∃ acc, SstoreRealises fr0 kw vw acc) ∧ vw ≠ 0) :
    SimStmtStep prog sloadChg obs o L b := by
  intro pc s st0 st0' T0 T0' fr0 hget hnc hcorr hstep
  obtain ⟨key, value, hse⟩ := hsstore s (List.mem_iff_getElem?.mpr ⟨pc, hget⟩)
  subst hse
  -- read off the `EvalStmt.sstore` witnesses (operands + post-state).
  cases hstep with
  | sstore hk hv =>
    rename_i kw vw
    obtain ⟨hsc, hgas, hstk, ⟨acc, hsr⟩, hnz⟩ := hties pc key value kw vw st0 fr0 hget hcorr hk hv
    obtain ⟨hwfv, hwfk⟩ := hwf.matFueled_sstore L b pc key value hb hget
    exact sim_sstore_stmt_lowered hb hget hcorr hk hv hsc hwfv hwfk
      (hwf.bound_sstore L b pc key value hb hget) hgas hstk hsr hnz

/-! ### The combined call-free statement discharge

`simStmtStep_callfree` case-splits a general call-free block's statements per shape into the
`assign` / `sstore` arms — so `SimStmtStep` is CONSTRUCTIBLE for *any* call-free block, given
`WellFormedLowered` and the per-shape genuine ties. (A call-free block has no `Stmt.call`, so the
two arms are exhaustive.) -/

/-- **`SimStmtStep` for any call-free block.** Dispatches each statement on its shape:
`assign` via `sim_assign` (no decode), `sstore` via `sim_sstore_stmt_lowered` (decode discharged
inside). `WellFormedLowered` supplies the structural fuel/pc side-conditions; the per-shape
genuine runtime ties (assign post-state realisability; sstore gas/`SstoreRealises`/non-zero) are
the explicit §7 hypotheses. -/
theorem simStmtStep_callfree {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hwf : WellFormedLowered prog)
    (hcf : CallFree b.stmts)
    -- the genuine `assign`-cursor ties (post-state realisability at the unchanged frame):
    (hassign : ∀ (pc : Nat) (t : Tmp) (e : Expr) (st0 st0' : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.assign t e) →
        Corr prog sloadChg obs st0 fr0 L pc →
        StepScoped prog st0 (.assign t e)
        ∧ (∀ t', st0'.locals t' ≠ none →
              ¬ NonRecomputable prog t' ∧ defsOf prog t' ≠ none)
        ∧ SloadRealises sloadChg st0' fr0
        ∧ GasRealises obs fr0)
    -- the genuine `sstore`-cursor ties (the §7 supplied-observation contract):
    (hsstore : ∀ (pc : Nat) (key value : Tmp) (kw vw : Word) (st0 : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.sstore key value) →
        Corr prog sloadChg obs st0 fr0 L pc →
        st0.locals key = some kw → st0.locals value = some vw →
        StepScoped prog st0 (.sstore key value)
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).sum
            + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).sum
            ≤ fr0.exec.gasAvailable.toNat
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
            + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024
        ∧ (∃ acc, SstoreRealises fr0 kw vw acc) ∧ vw ≠ 0) :
    SimStmtStep prog sloadChg obs o L b := by
  intro pc s st0 st0' T0 T0' fr0 hget hnc hcorr hstep
  -- `s` is at a present cursor of a call-free block, so it is `assign` or `sstore` (not `call`).
  cases hstep with
  | assignPure hne hv =>
    rename_i t e w
    obtain ⟨hsc, hscoped', hsload', hgas'⟩ := hassign pc t e st0 (st0.setLocal t w) fr0 hget hcorr
    obtain ⟨_, hc', _⟩ := sim_assign hb hget hcorr
      (EvalStmt.assignPure (prog := prog) (o := o) (T := T0) hne hv) hsc hscoped' hsload' hgas'
    exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
  | assignGas =>
    rename_i ob t
    obtain ⟨hsc, hscoped', hsload', hgas'⟩ := hassign pc t .gas st0 (st0.setLocal t ob) fr0 hget hcorr
    obtain ⟨_, hc', _⟩ := sim_assign hb hget hcorr
      (EvalStmt.assignGas (prog := prog) (o := o) (T := T0') (t := t)) hsc hscoped' hsload' hgas'
    exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
  | sstore hk hv =>
    rename_i key value kw vw
    obtain ⟨hsc, hgas, hstk, ⟨acc, hsr⟩, hnz⟩ := hsstore pc key value kw vw st0 fr0 hget hcorr hk hv
    obtain ⟨hwfv, hwfk⟩ := hwf.matFueled_sstore L b pc key value hb hget
    exact sim_sstore_stmt_lowered hb hget hcorr hk hv hsc hwfv hwfk
      (hwf.bound_sstore L b pc key value hb hget) hgas hstk hsr hnz
  | call hcallee hgasr ho =>
    rename_i cs calleeW gasFwdW success world'
    -- `call` is excluded by `CallFree`.
    exact absurd (by show Stmt.isCall (.call cs) = true; rfl)
      (by have := hcf (.call cs) (List.mem_iff_getElem?.mpr ⟨pc, hget⟩); simpa using this)

/-! ### The `stop`-terminator discharge (fully closed down to the genuine frame facts)

For a block whose terminator is `Stmt`-free `Term.stop`, `SimTermStep`'s `edge` arm is
vacuous (its `b.term = jump/branch` hypotheses are unsatisfiable) and the `halt` arm's `ret`
disjunct is too. The remaining `stop` halt routes through `sim_term_halt_stop`, whose `STOP`
decode is itself discharged from A3 (`decode_at_term_nonpush`) + the terminator-cursor pc
bridge (`pcOf_eq_termOf`): the only residual is the genuine top-level-frame facts — the self
address (`hself`), the `.call`-kind (`hkind`), and the non-empty committed accounts (`hne`) —
exactly the `EntersAsCode`/successful-run facts the §7 contract supplies. A complete
`SimTermStep` discharge for the `stop` terminator. -/

/-- **`SimTermStep` for a `stop`-terminator block.** If `b.term = .stop`, then — given the
genuine top-level-frame facts at every terminator-cursor frame (self address `= fr.address`,
`.call`-kind, non-empty committed accounts) and the pc bound — `SimTermStep` holds. The `STOP`
decode is discharged from A3; the `edge`/`ret` arms are vacuous. -/
theorem simTermStep_stop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .stop)
    (hbound : termOf prog L < 2 ^ 32)
    -- the genuine top-level-frame facts at any terminator-cursor frame in `Corr`:
    (hframe : ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        self = frT.exec.executionEnv.address
        ∧ (∃ cp, frT.kind = .call cp)
        ∧ ¬ (frT.exec.accounts == ∅) = true) :
    SimTermStep prog sloadChg obs o self L b := by
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: only the `stop` disjunct fires (the `ret` one contradicts `hterm`).
    intro st' frT hcorr hdisj
    obtain ⟨hself, ⟨cp, hkind⟩, hne⟩ := hframe st' frT hcorr
    -- the `STOP` decode at the terminator cursor, from A3 + `pcOf_eq_termOf`.
    have hpcterm : frT.exec.pc = UInt32.ofNat (termOf prog L) := by
      rw [hcorr.pc_eq, pcOf_eq_termOf prog L b hb]
    have hdec : decode frT.exec.executionEnv.code frT.exec.pc
        = some (.System .STOP, .none) := by
      rw [hcorr.code_eq, hpcterm]
      have hk : 0 < (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length := by
        rw [hterm]; simp [emitTerm]
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[0]?
          = some Byte.stop := by rw [hterm]; rfl
      have := decode_at_term_nonpush prog L b 0 Byte.stop hb (by simpa using hk)
        hbyte0 (by simpa using hbound) (by decide)
      simpa using this
    obtain ⟨last, halt, hruns, hhalt, hworld, _⟩ :=
      sim_term_halt_stop hcorr hterm hself hdec hkind hne
    exact ⟨last, halt, hruns, hhalt, hworld⟩
  · -- edge arm: vacuous (b.term = .stop contradicts every jump/branch disjunct).
    intro st' frT succ hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩ <;> exact absurd h (by simp)

/-! ### The `ret`-terminator discharge (decode-free via `sim_term_halt_ret_lowered`)

For a block whose terminator is `Term.ret t`, `SimTermStep`'s `edge` arm is vacuous and the
`halt` arm's `stop` disjunct contradicts. The `ret` halt routes through
`sim_term_halt_ret_lowered` — the operand `MatDec` is discharged inside; `WellFormedLowered`
supplies the structural `MatFueled` + pc bound. The genuine residual is the value-channel
RETURN-site tie (`hself`, the returned-value binding `st'.locals t = some vw`, the gas/stack
envelopes, and the RETURN-site `hret` — the §7 supplied-observation contract). -/

/-- **`SimTermStep` for a `ret`-terminator block.** If `b.term = .ret t`, then — given
`WellFormedLowered` and, at every terminator-cursor frame in `Corr`, the genuine value-channel
ties (`hself`, the returned-value binding, gas/stack envelopes, the RETURN-site `hret`) —
`SimTermStep` holds. The decode is discharged inside `sim_term_halt_ret_lowered`; the
`edge`/`stop` arms are vacuous. -/
theorem simTermStep_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block} {t : Tmp}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .ret t)
    (hwf : WellFormedLowered prog)
    -- the genuine value-channel RETURN-site ties (the §7 contract) at any terminator-cursor frame:
    (hties : ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        self = frT.exec.executionEnv.address
        ∧ (∃ vw, st'.locals t = some vw)
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
            ≤ frT.exec.gasAvailable.toNat
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
        ∧ (∀ frv : Frame, Runs frT frv →
            frv.exec.executionEnv.code = frT.exec.executionEnv.code →
            frv.exec.executionEnv.address = frT.exec.executionEnv.address →
            (∀ k, selfStorage frv k = selfStorage frT k) →
            ∃ last rest output cp,
              Runs frv last
              ∧ stepFrame last = .halted (.success (returnEmptyPost last.exec rest) output)
              ∧ last.exec.executionEnv.address = frT.exec.executionEnv.address
              ∧ (∀ k, selfStorage last k = selfStorage frT k)
              ∧ last.kind = .call cp
              ∧ ¬ (last.exec.accounts == ∅) = true)) :
    SimTermStep prog sloadChg obs o self L b := by
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: only the `ret` disjunct fires (the `stop` one contradicts `hterm`).
    intro st' frT hcorr _hdisj
    obtain ⟨hself, ⟨vw, hv⟩, hgas, hstk, hret⟩ := hties st' frT hcorr
    exact sim_term_halt_ret_lowered hb hcorr hterm hself hv
      (hwf.matFueled_ret L b t hb hterm) (hwf.bound_ret L b t hb hterm) hgas hstk hret
  · -- edge arm: vacuous (b.term = .ret t contradicts every jump/branch disjunct).
    intro st' frT succ hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩ <;> exact absurd h (by simp)

/-! ### The `jump`-terminator discharge (decode-free via `sim_term_edge_jump_lowered`)

For an unconditional `Term.jump dst`, `SimTermStep`'s `halt` arm is vacuous. The `edge` arm's
`jump` disjunct (`succ = dst`) routes through `sim_term_edge_jump_lowered` — the PUSH4/JUMP/
landing-JUMPDEST decode bundle and the offset round-trip are discharged inside;
`WellFormedLowered` supplies the structural pc/offset bounds; the `validJumps`-recording tie is
discharged structurally from `Corr` (`Corr.validJumps_lower`) inside the wrapper. The genuine
residual is the gas envelopes (§7), plus the destination block's presence. -/

/-- **`SimTermStep` for a `jump`-terminator block.** If `b.term = .jump dst` with `dst` present,
then — given `WellFormedLowered` and, at every terminator-cursor frame, the genuine control-flow
ties (the gas envelopes) — `SimTermStep` holds. The decode and the `validJumps` tie are
discharged inside `sim_term_edge_jump_lowered`; the `halt` arm is vacuous. -/
theorem simTermStep_jump {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    {dst : Label} {bdst : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .jump dst)
    (hwf : WellFormedLowered prog)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hdstlt : dst.idx < prog.blocks.size)
    -- the genuine control-flow ties (gas envelopes) at any terminator-cursor frame. The
    -- `validJumps`-recording tie is no longer carried — it is discharged structurally inside
    -- `sim_term_edge_jump_lowered` from `Corr` (frame-invariant `validJumps = validJumpDests
    -- code 0` + `code = lower prog`).
    (hties : ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        3 ≤ frT.exec.gasAvailable.toNat
        ∧ GasConstants.Gmid ≤ (pushFrameW frT
            (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
            4).exec.gasAvailable.toNat
        ∧ GasConstants.Gjumpdest
            ≤ (jumpFrame (pushFrameW frT
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32)) 4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                frT.exec.stack).exec.gasAvailable.toNat) :
    SimTermStep prog sloadChg obs o self L b := by
  obtain ⟨hbt, hbo⟩ := hwf.bound_jump L b dst hb hterm
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: vacuous (b.term = .jump dst contradicts stop/ret).
    intro st' frT hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, h⟩ <;> exact absurd h (by simp)
  · -- edge arm: the `jump` disjunct (`succ = dst`).
    intro st' frT succ hcorr hdisj
    have hsucc : succ = dst := by
      rw [hterm] at hdisj
      rcases hdisj with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩
      · exact (Term.jump.inj h).symm
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    subst hsucc
    obtain ⟨hgpush, hgjump, hgjd⟩ := hties st' frT hcorr
    obtain ⟨fr', L', hL', hruns', hcorr'⟩ :=
      sim_term_edge_jump_lowered hcorr hterm hb hbdst hdstlt hbt hbo hgpush hgjump hgjd
    subst hL'
    exact ⟨fr', hruns', hcorr'⟩

/-! ### The `branch`-terminator discharge (decode-free via `sim_term_edge_branch_lowered`)

For a `Term.branch cond thenL elseL`, `SimTermStep`'s `halt` arm is vacuous. The `edge` arm's
two branch disjuncts (`cw ≠ 0 → succ = thenL`, `cw = 0 → succ = elseL`) route through
`sim_term_edge_branch_lowered`, whose strengthened cw-tied conclusion pins the resolved
successor to the runtime condition — so the `succ` `SimTermStep` asks for is exactly the one the
lowered branch lands on. The decode bundle and the `validJumps`-recording tie (via
`Corr.validJumps_lower` + `MatRuns.validJumps`) are discharged inside; `WellFormedLowered`
supplies the structural pc/offset bounds. The genuine residual is the cond-materialise run
(`MatRuns`) and the gas envelopes (§7), plus the successor blocks' presence. -/

/-- **`SimTermStep` for a `branch`-terminator block.** If `b.term = .branch cond thenL elseL`
with both successors present, then — given `WellFormedLowered` and, at every terminator-cursor
frame, the genuine control-flow ties (the cond-materialise `MatRuns`, the gas envelopes) —
`SimTermStep` holds. The cw-tied conclusion of `sim_term_edge_branch_lowered` reconciles the
`SimTermStep.edge` disjunct's chosen `succ` with the runtime-resolved branch. -/
theorem simTermStep_branch {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    {cond : Tmp} {thenL elseL : Label} {bthen belse : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .branch cond thenL elseL)
    (hwf : WellFormedLowered prog)
    (hbthen : prog.blocks.toList[thenL.idx]? = some bthen)
    (hbelse : prog.blocks.toList[elseL.idx]? = some belse)
    (hthenlt : thenL.idx < prog.blocks.size)
    (helselt : elseL.idx < prog.blocks.size)
    -- the genuine control-flow ties at any terminator-cursor frame, parametrised over the
    -- runtime condition word `cw` and the cond-materialise endpoint `frc`:
    (hties : ∀ (st' : V2.IRState) (frT : Frame) (cw : Word),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        st'.locals cond = some cw →
        ∃ frc, MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
          ∧ 3 ≤ frc.exec.gasAvailable.toNat
          ∧ GasConstants.Ghigh ≤ (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              GasConstants.Ghigh
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
              GasConstants.Gmid
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
              (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat) :
    SimTermStep prog sloadChg obs o self L b := by
  obtain ⟨hbt, hbthenoff, hbelseoff⟩ := hwf.bound_branch L b cond thenL elseL hb hterm
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: vacuous (b.term = .branch contradicts stop/ret).
    intro st' frT hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, h⟩ <;> exact absurd h (by simp)
  · -- edge arm: the two branch disjuncts, each tied to `cw` via the strengthened conclusion.
    intro st' frT succ hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨cond', elseL', cw, heq, hc, hnz⟩ | ⟨cond', thenL', heq, hc⟩
    · exact absurd h (by simp)
    · -- then-branch taken (`cw ≠ 0`), so the `SimTermStep` `succ` is `thenL`.
      obtain ⟨hcond, hsucc, helse⟩ := Term.branch.inj heq
      subst hcond; subst hsucc; subst helse
      obtain ⟨frc, hmrc, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hties st' frT cw hcorr hc
      obtain ⟨fr', L', hL', hruns', hcorr'⟩ :=
        sim_term_edge_branch_lowered hcorr hterm hb hc hbthen hbelse hthenlt helselt hmrc
          hbt hbthenoff hbelseoff hg1 hg2 hg3 hg4 hg5 hg6
      rcases hL' with ⟨_, hLt⟩ | ⟨hcw0, _⟩
      · subst hLt; exact ⟨fr', hruns', hcorr'⟩
      · exact absurd hcw0 hnz
    · -- else-branch taken (`cw = 0`), so the `SimTermStep` `succ` is `elseL`.
      obtain ⟨hcond, hthen, hsucc⟩ := Term.branch.inj heq
      subst hcond; subst hthen; subst hsucc
      obtain ⟨frc, hmrc, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hties st' frT 0 hcorr hc
      obtain ⟨fr', L', hL', hruns', hcorr'⟩ :=
        sim_term_edge_branch_lowered hcorr hterm hb hc hbthen hbelse hthenlt helselt hmrc
          hbt hbthenoff hbelseoff hg1 hg2 hg3 hg4 hg5 hg6
      rcases hL' with ⟨hcwne, _⟩ | ⟨_, hLe⟩
      · exact absurd rfl hcwne
      · subst hLe; exact ⟨fr', hruns', hcorr'⟩

/-! ### The combined call-free terminator discharge

`simTermStep_callfree` case-splits a block's terminator into the four arms — so `SimTermStep` is
CONSTRUCTIBLE for any block, given `WellFormedLowered`, the successor presence, and the per-shape
genuine §7 ties. The genuine ties are collected as one hypothesis dispatched on `b.term`. -/

/-- **`SimTermStep` for any block.** Dispatches `b.term` into the four arms
(`simTermStep_stop`/`_ret`/`_jump`/`_branch`). `WellFormedLowered` supplies the structural
fuel/pc/offset side-conditions; the per-shape genuine §7 ties are supplied by the `hstop`/`hret`/
`hjump`/`hbranch` hypotheses (each consumed only on its matching terminator shape). The successor
blocks (for the edges) are supplied by `hsucc`. -/
theorem simTermStep_callfree {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hwf : WellFormedLowered prog)
    -- successor-block presence for the edges (vacuous on halts):
    (hsucc : ∀ (L' : Label), (b.term = .jump L' ∨ (∃ c o', b.term = .branch c L' o')
        ∨ (∃ c t', b.term = .branch c t' L')) →
        ∃ b', prog.blocks.toList[L'.idx]? = some b' ∧ L'.idx < prog.blocks.size)
    -- the genuine §7 ties, dispatched on the terminator shape:
    (hstop : b.term = .stop →
        ∀ (st' : V2.IRState) (frT : Frame),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          self = frT.exec.executionEnv.address
          ∧ (∃ cp, frT.kind = .call cp)
          ∧ ¬ (frT.exec.accounts == ∅) = true)
    (hretties : ∀ t, b.term = .ret t →
        ∀ (st' : V2.IRState) (frT : Frame),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          self = frT.exec.executionEnv.address
          ∧ (∃ vw, st'.locals t = some vw)
          ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
              ≤ frT.exec.gasAvailable.toNat
          ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
          ∧ (∀ frv : Frame, Runs frT frv →
              frv.exec.executionEnv.code = frT.exec.executionEnv.code →
              frv.exec.executionEnv.address = frT.exec.executionEnv.address →
              (∀ k, selfStorage frv k = selfStorage frT k) →
              ∃ last rest output cp,
                Runs frv last
                ∧ stepFrame last = .halted (.success (returnEmptyPost last.exec rest) output)
                ∧ last.exec.executionEnv.address = frT.exec.executionEnv.address
                ∧ (∀ k, selfStorage last k = selfStorage frT k)
                ∧ last.kind = .call cp
                ∧ ¬ (last.exec.accounts == ∅) = true))
    (hjump : ∀ dst bdst, b.term = .jump dst →
        prog.blocks.toList[dst.idx]? = some bdst → dst.idx < prog.blocks.size →
        ∀ (st' : V2.IRState) (frT : Frame),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          3 ≤ frT.exec.gasAvailable.toNat
          ∧ GasConstants.Gmid ≤ (pushFrameW frT
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest
              ≤ (jumpFrame (pushFrameW frT
                  (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32)) 4)
                  GasConstants.Gmid
                  (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                  frT.exec.stack).exec.gasAvailable.toNat)
    (hbranch : ∀ cond thenL elseL bthen belse, b.term = .branch cond thenL elseL →
        prog.blocks.toList[thenL.idx]? = some bthen → prog.blocks.toList[elseL.idx]? = some belse →
        thenL.idx < prog.blocks.size → elseL.idx < prog.blocks.size →
        ∀ (st' : V2.IRState) (frT : Frame) (cw : Word),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          st'.locals cond = some cw →
          ∃ frc, MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
            ∧ 3 ≤ frc.exec.gasAvailable.toNat
            ∧ GasConstants.Ghigh ≤ (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
                4).exec.gasAvailable.toNat
            ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                GasConstants.Ghigh
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
                ([] : Stack Word)).exec.gasAvailable.toNat
            ∧ 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word)).exec.gasAvailable.toNat
            ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word))
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4).exec.gasAvailable.toNat
            ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word))
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
                (jumpiFallthroughFrame (pushFrameW frc
                  (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                  ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat) :
    SimTermStep prog sloadChg obs o self L b := by
  -- dispatch on the terminator shape.
  cases hb' : b.term with
  | stop => exact simTermStep_stop hb hb' (hwf.bound_stop L b hb hb') (hstop hb')
  | ret t => exact simTermStep_ret hb hb' hwf (hretties t hb')
  | jump dst =>
    obtain ⟨bdst, hbdst, hdstlt⟩ := hsucc dst (Or.inl hb')
    exact simTermStep_jump hb hb' hwf hbdst hdstlt (hjump dst bdst hb' hbdst hdstlt)
  | branch cond thenL elseL =>
    obtain ⟨bthen, hbthen, hthenlt⟩ := hsucc thenL (Or.inr (Or.inl ⟨cond, elseL, hb'⟩))
    obtain ⟨belse, hbelse, helselt⟩ := hsucc elseL (Or.inr (Or.inr ⟨cond, thenL, hb'⟩))
    exact simTermStep_branch hb hb' hwf hbthen hbelse hthenlt helselt
      (hbranch cond thenL elseL bthen belse hb' hbthen hbelse hthenlt helselt)

/-! ## `sim_cfg` — the whole-CFG simulation

Induction on `V2.RunFrom`. Each constructor:

* runs the block's `CallFree` statement list via Layer D (`sim_stmts_block`), from `Corr` at
  the block entry `(L, 0)` to `Corr` at the terminator cursor `(L, b.stmts.length)` with the
  working stack back to `[]`;
* then dispatches on the terminator: `stop`/`ret` halt via `SimTermStep.halt` (the world
  matches `st'.world`, which is the IR halt's world); `jump`/`branch` run to the successor's
  entry via `SimTermStep.edge`, re-establishing `Corr`, and the **IH** closes the recursion.

`RunFrom` is an inductive `Prop`, so the structural recursion on the derivation is well-founded
— no fuel. The whole-program call-freedom and per-block simulation are supplied uniformly as
the two `∀`-quantified structured hypotheses. -/

/-- **`sim_cfg` — whole-program CFG simulation (call-free, world channel).** From `Corr` at the
entry cursor `(L, 0)` and a `V2.RunFrom prog o st T L O`, where every block reached is
`CallFree` and supplies the per-statement (`SimStmtStep`) and per-terminator (`SimTermStep`)
simulations, the lowered bytecode runs from `fr` to a halting frame `last` whose `observe self`
**world** is the IR observable `O`'s world.

Induction on the `RunFrom` derivation: Layer D runs each block's statements; `SimTermStep`
either halts (matching the world, the `stop`/`ret` base cases) or steps to the taken
successor's entry where the IH applies (the `jump`/`branch` recursion). -/
theorem sim_cfg {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {o : V2.CallOracle}
    {self : AccountAddress}
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs o L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs o self L b)
    (hcf : ∀ (L : Label) (b : Block), blockAt prog L = some b → CallFree b.stmts)
    {st : V2.IRState} {T : Trace} {L : Label} {O : V2.Observable} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hrun : V2.RunFrom prog o st T L O) :
    ∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world := by
  induction hrun generalizing fr with
  | @ret st st' T T' L b t w hb hss hterm' hv =>
    -- Layer D: run the block's statements to the terminator cursor.
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    -- Layer E: `ret` halts with world = st'.world (the IR ret halt's world).
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ :=
      (hterm L b hb).halt st' frT hcorrT (Or.inr ⟨t, hterm'⟩)
    exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld⟩
  | @stop st st' T T' L b hb hss hterm' =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ :=
      (hterm L b hb).halt st' frT hcorrT (Or.inl hterm')
    exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld⟩
  | @branchThen st st' T T' L b cond cw thenL elseL O hb hss hterm' hc hnz hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    -- Layer E (edge): step to `thenL`'s entry, re-establishing `Corr` at `(thenL, 0)`.
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT thenL hcorrT
        (Or.inr (Or.inl ⟨cond, elseL, cw, hterm', hc, hnz⟩))
    -- IH on the recursion into `thenL`, from the re-established `Corr`.
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩
  | @branchElse st st' T T' L b cond thenL elseL O hb hss hterm' hc hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT elseL hcorrT
        (Or.inr (Or.inr ⟨cond, thenL, hterm', hc⟩))
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩
  | @jump st st' T T' L b dst O hb hss hterm' hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT dst hcorrT (Or.inl hterm')
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩

/-! ## `paramsFor` — the canonical top-level params running `lower prog`

`paramsFor prog accounts gas` is the `CallParams` that runs `lower prog` as a top-level code
call over `accounts` at gas `gas`, with the self/caller/origin pinned to `selfAddr` (the
storage lens `observe`/`Corr` read). It is the generic analogue of `WorkedCall.wcParams`, with
the program and the world (as the `accounts` map carrying the self account's storage) free.
`lower_conforms` is stated over an *abstract* `p : CallParams` with `EntersAsCode p fr₀`; the
canonical instantiation is `p := paramsFor …`, whose `EntersAsCode` is `paramsFor_entersAsCode`
(`beginCall_code`, the entry frame is `codeFrame (paramsFor …) (lower prog)`). The IR world
`w₀` is the self account's storage lens through `selfStorage`/`storageAt` (the `StorageAgree`
clause of the carried entry `Corr`), so it is determined by `accounts` rather than threaded
separately. -/

/-- **The canonical top-level params for `lower prog`.** Runs `lower prog` as a `.Code` call
over `accounts` at gas `gas`, self = caller = origin = recipient = `selfAddr`. The generic
analogue of `WorkedCall.wcParams`. -/
def paramsFor (prog : Program) (selfAddr : AccountAddress) (accounts : AccountMap)
    (gas : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := accounts, originalAccounts := ∅, substate := default,
    caller := selfAddr, origin := selfAddr, recipient := selfAddr,
    codeSource := .Code (lower prog), gas := gas, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-- **`paramsFor` enters as code.** `beginCall (paramsFor …)` descends into
`codeFrame (paramsFor …) (lower prog)` — the entry frame `lower_conforms`'s `hbegin` consumes
when instantiated at `p := paramsFor …`. -/
theorem paramsFor_entersAsCode (prog : Program) (selfAddr : AccountAddress)
    (accounts : AccountMap) (gas : UInt64) :
    EntersAsCode (paramsFor prog selfAddr accounts gas)
      (codeFrame (paramsFor prog selfAddr accounts gas) (lower prog)) :=
  beginCall_code (paramsFor prog selfAddr accounts gas) (lower prog) rfl

/-! ## `entry_corr` — the entry correspondence builder (the leading-JUMPDEST step)

`sim_cfg` is seeded at `Corr prog … { locals := fun _ => none, world := w₀ } fr₀ prog.entry 0`
— `Corr` at the *entry block's body cursor* `(prog.entry, 0)`, whose pc is
`pcOf prog prog.entry 0 = offsetTable … prog.entry.idx + 1`: one byte *past* the entry block's
leading `JUMPDEST`. The top-level entry frame `fr₀ = codeFrame p (lower prog)`, however, sits at
pc `0` — *on* that `JUMPDEST` (when the entry block is block 0, `offsetTable … 0 = 0`). So the
entry `Corr` is reached by the single leading-`JUMPDEST` step, exactly as a `jump`/`branch` edge
lands on a successor block's `JUMPDEST` and steps it (`corr_at_jumpdest_landing`).

`entry_corr` discharges the former `hentry` hypothesis from:

* the entry block being block `0` (`prog.entry.idx = 0`, so its `JUMPDEST` is at byte 0 = the
  codeFrame's pc) and present (`blockAt prog prog.entry = some bentry`);
* the *genuine* entry-frame realisability ties — `StorageAgree` between `w₀` and the entry
  frame's storage lens (the IR initial world *is* the accounts the run uses), and the entry
  `SloadRealises`/`GasRealises` (the §7 supplied-observation contract at the entry frame);
* the `Gjumpdest` gas margin.

The structural `Corr` clauses (code / pc / stack / canModifyState) are read off `codeFrame`
mechanically; `DefsSound`/`wellScoped` are vacuous at the empty-locals entry state
(`defsSound_entry`). -/

/-- **The entry frame field reductions.** `codeFrame p (lower prog)` runs `lower prog` at pc 0
with an empty stack, the modifiable flag of `p`, gas `p.gas`, validJumps `validJumpDests (lower
prog) 0`, and a `.call`-kind. (All `rfl` off the `codeFrame`/`codeEnv` definitions.) -/
theorem codeFrame_pc (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.pc = 0 := rfl

theorem codeFrame_stack (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.stack = [] := rfl

theorem codeFrame_code (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.executionEnv.code = code := rfl

theorem codeFrame_addr (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.executionEnv.address = p.recipient := rfl

theorem codeFrame_canMod (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.executionEnv.canModifyState = p.canModifyState := rfl

theorem codeFrame_gas (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.gasAvailable = p.gas := rfl

theorem codeFrame_validJumps (p : CallParams) (code : ByteArray) :
    (codeFrame p code).validJumps = validJumpDests code 0 := rfl

/-! ### Discharging the entry STORAGE tie definitionally

`entry_corr`'s `hstore : StorageAgree { …, world := w₀ } (codeFrame p (lower prog))` ties the
IR initial world `w₀` to the entry frame's self-storage lens. In `lower_conforms`/
`lower_conforms_acyclic` the world `w₀` is **universally quantified** (a free choice), so this
tie is not a runtime fact — it is *definitional*: choosing `w₀ := selfStorage (codeFrame …)`
makes `StorageAgree` hold by `rfl`. The lemma below records that canonical choice, banking the
`hstore` entry tie (the only entry-frame tie not intrinsic to the recording — `hsload`/`hgasr`
constrain *every* same-address frame's warmth/gas, the supplied-observation correspondence,
and so stay genuine). -/

/-- **The entry STORAGE tie, definitionally.** Taking the IR initial world to be the entry
frame's own self-storage lens (`selfStorage (codeFrame p code)`) discharges `StorageAgree` by
reflexivity. The canonical `w₀` choice for the entry-frame storage tie. -/
theorem entry_storageAgree_codeFrame (p : CallParams) (code : ByteArray) :
    StorageAgree { locals := fun _ => none, world := selfStorage (codeFrame p code) }
      (codeFrame p code) :=
  fun _ => rfl

/-- **`entry_corr` — the entry correspondence.** For an entry block `bentry` that is block `0`
(`prog.entry.idx = 0`) and present, the top-level entry frame `codeFrame p (lower prog)` —
running `lower prog` from pc 0 with empty stack, `p` modifiable — steps its leading `JUMPDEST`
(`runs_jumpdest`) to a frame in `Corr`-correspondence with the empty-locals entry state at
`(prog.entry, 0)`. The genuine ties (`StorageAgree`/`SloadRealises`/`GasRealises` at the entry
frame, and the `Gjumpdest` margin) are the entry-frame realisability contract; `DefsSound` /
`wellScoped` are vacuous at empty locals. -/
theorem entry_corr {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {w₀ : V2.World}
    {p : CallParams} {bentry : Block}
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hsload : SloadRealises sloadChg { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgas : GasConstants.Gjumpdest ≤ p.gas.toNat) :
    ∃ fr₀, Runs (codeFrame p (lower prog)) fr₀
      ∧ Corr prog sloadChg obs { locals := fun _ => none, world := w₀ } fr₀ prog.entry 0 := by
  set fe := codeFrame p (lower prog) with hfe
  -- the entry block sits at offset 0 (it is block 0), so the codeFrame's pc (= 0) is its
  -- leading `JUMPDEST` byte.
  have hbtl : prog.blocks.toList[prog.entry.idx]? = some bentry := by
    have : blockAt prog prog.entry = prog.blocks.toList[prog.entry.idx]? := by
      unfold blockAt; rw [Array.getElem?_toList]
    rwa [this] at hbentry
  have hoff0 : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx = 0 := by
    unfold offsetTable; rw [hentry0]; simp
  -- pc of the codeFrame is `UInt32.ofNat (offsetTable … entry.idx)` (= 0).
  have hpc : fe.exec.pc
      = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx) := by
    rw [hfe, codeFrame_pc, hoff0]; rfl
  have hcode : fe.exec.executionEnv.code = lower prog := by rw [hfe, codeFrame_code]
  have hvalid : fe.validJumps = validJumpDests fe.exec.executionEnv.code 0 := by
    rw [hfe, codeFrame_validJumps, codeFrame_code]
  have hstk : fe.exec.stack = [] := by rw [hfe, codeFrame_stack]
  have hcanmod : fe.exec.executionEnv.canModifyState = true := by rw [hfe, codeFrame_canMod, hmod]
  have hstore' : ∀ k, selfStorage fe k = ({ locals := fun _ => none, world := w₀ } : V2.IRState).world k :=
    hstore
  -- the leading-`JUMPDEST` decode at the entry offset.
  have hdec : decode fe.exec.executionEnv.code fe.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    rw [hcode, hpc]; exact decode_at_block_offset_jumpdest prog prog.entry bentry hbtl hbound
  have hgas' : GasConstants.Gjumpdest ≤ fe.exec.gasAvailable.toNat := by rw [hfe, codeFrame_gas]; exact hgas
  obtain ⟨hjdrun, hjdcorr⟩ :=
    corr_at_jumpdest_landing (st := { locals := fun _ => none, world := w₀ }) hbtl hpc hcode hvalid
      hstk hcanmod hstore' (defsSound_entry prog w₀) (by intro t ht; simp at ht) hsload hgasr hdec hgas'
  exact ⟨jumpdestFrame fe, hjdrun, hjdcorr⟩

/-! ## `lower_conforms` — tying `sim_cfg` to the recording interpreter

The headline. From a successful `runWithLog` over the lowered program, recover:

1. **the IR run** — `IRRun prog (realisedGas log) (realisedCall log self) w₀ O` for *some*
   observable `O`. We do **not** synthesise the `RunFrom` derivation from the bytecode
   (`runWithLog` records the *bytecode* trace, not the IR one); instead we carry the IR run as
   a structured hypothesis (`hir`) — the **IR side** of the conformance diagram, supplied for
   the program under study and itself the subject of the IR-determinism / supplied-observation
   contract (`docs/ir-design-v3.md` §7). This is the honest realisability hypothesis: the IR
   run *under the realised oracles* the bytecode produces.
2. **the world equation** — `O.world = (observe self log.observable).world`. This is the
   load-bearing conformance edge, and it is **fully discharged** here from `sim_cfg`:
   `runWithLog_messageCall` pins `messageCall = .ok log.observable.toCallResult`; `sim_cfg` +
   `messageCall_runs` pins `messageCall = .ok (toCallResult (endFrame last haltSig))`; equating
   the two `toCallResult`s (`observe` reads only `.toCallResult`) gives `observe self
   log.observable = observe self (endFrame last haltSig)`, whose world is `O.world` by
   `sim_cfg` and `IRRun.det`.

The former entry `Corr` hypothesis is now **discharged** in-proof by `entry_corr` (the
leading-`JUMPDEST` step from the top-level frame), so `lower_conforms` no longer carries it:
its replacements are the structural entry facts (`hentry0`/`hbentry`/`hbound` — the entry block
is block 0, present, pc-bounded) plus the *genuine* entry-frame realisability ties
(`hstore`/`hsload`/`hgasr`/`hgasj`). The per-block simulations (`hstmts`/`hterm`), call-freedom
(`hcf`), and the IR run (`hir`) remain the carried structured hypotheses — the
supplied-observation realisability contract (`hstmts`/`hterm` are themselves now dischargeable
per shape by `simStmtStep_assign` / `simTermStep_stop`, down to the per-cursor genuine ties and
the per-shape decode bundles — the documented A2/A3-reconstruction follow-up for the
`sstore`/`ret`/`jump`/`branch` shapes). `runWithLog` at the seed fuel makes the `messageCall`
bridge exact. -/

/-- **`lower_conforms` (call-free, world channel — under the realisability contract).** For a
program `prog`, initial world `w₀`, self address `self`, observable IR run `O` and run log
`log`: if the recording run `runWithLog p (seedFuel p.gas)` over the top-level params `p`
(canonically `paramsFor prog self accounts gas`) succeeds with `log`, where `p` is a top-level
`.Code (lower prog)` modifiable call (`hp`/`hmod`), the entry block is block 0 and present
(`hentry0`/`hbentry`/`hbound`), the genuine entry-frame realisability ties hold
(`hstore`/`hsload`/`hgasr`/`hgasj`), the per-block simulations (`hstmts`/`hterm`) and
call-freedom (`hcf`) hold, and the IR runs under the realised oracles to `O` (`hir`), then **the
IR observable's world equals the `observe` world of the recorded bytecode result**:

  `O.world = (observe self log.observable).world`.

The world edge is fully discharged from `sim_cfg` + the `messageCall` bridge + `IRRun.det`; the
IR run itself and the per-block realisability are the carried hypotheses (the §7
supplied-observation contract). -/
theorem lower_conforms {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {O : V2.Observable} {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    -- the recording run succeeded over the lowered program at the seed fuel:
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    -- the lowered program is entered as a top-level `.Code (lower prog)` call (the canonical
    -- instantiation is `p := paramsFor prog self accounts gas`); `p` may modify state:
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    -- the entry block is block 0 (its leading `JUMPDEST` is at byte 0 = the entry frame's pc),
    -- present, and the program fits a 32-bit pc:
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    -- the GENUINE entry-frame realisability ties (the §7 supplied-observation contract at the
    -- entry frame): the IR initial world `w₀` is the entry frame's storage lens, and the entry
    -- SLOAD-warmth / GAS observations hold; plus the `Gjumpdest` gas margin:
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hsload : SloadRealises sloadChg { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    -- the per-block simulations + call-freedom (the realisability contract over `lower prog`):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs (realisedCall log self) L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs (realisedCall log self) self L b)
    (hcf : ∀ (L : Label) (b : Block), blockAt prog L = some b → CallFree b.stmts)
    -- the IR run under the realised oracles (the IR side of the conformance diagram):
    (hir : V2.IRRun prog (realisedCall log self) w₀ (realisedGas log) O) :
    O.world = (observe self log.observable).world := by
  -- the lowered program enters as code from `codeFrame p (lower prog)` (`beginCall_code`).
  have hbegin : EntersAsCode p (codeFrame p (lower prog)) := beginCall_code p (lower prog) hp
  -- `entry_corr`: the leading-`JUMPDEST` step lands the entry frame in `Corr` at `(entry, 0)`.
  obtain ⟨fr₀, hjdruns, hentry⟩ :=
    entry_corr (sloadChg := sloadChg) (obs := obs) (w₀ := w₀) hmod hentry0 hbentry hbound
      hstore hsload hgasr hgasj
  -- `sim_cfg`: from the entry `Corr`, the lowered run halts with world = O.world.
  obtain ⟨last, haltSig, hruns, hhalt, hworld⟩ :=
    sim_cfg (self := self) hstmts hterm hcf hentry hir
  -- the `messageCall` bridge, two ways: the assembled `Runs` halt (entry JUMPDEST then the CFG
  -- run), and the recorder.
  have hmc_runs : messageCall p = .ok (FrameResult.toCallResult (endFrame last haltSig)) :=
    messageCall_runs p hbegin (hjdruns.trans hruns) hhalt
  have hmc_log : messageCall p = .ok log.observable.toCallResult :=
    runWithLog_messageCall hwl
  -- equate the two recorded results' `toCallResult`s.
  have htcr : log.observable.toCallResult = FrameResult.toCallResult (endFrame last haltSig) := by
    rw [hmc_log] at hmc_runs; exact Except.ok.inj hmc_runs
  -- `observe`'s world reads only `.toCallResult.accounts`, so the two `observe` worlds agree.
  have hobs : (observe self log.observable).world
      = (observe self (endFrame last haltSig)).world := by
    funext key
    show resultStorageAt log.observable self key
      = resultStorageAt (endFrame last haltSig) self key
    unfold resultStorageAt
    rw [htcr]
  rw [hobs, hworld]

/-! ## `lower_conforms_wf` — the builder-based restatement

`lower_conforms` carries the per-block simulations `hstmts`/`hterm` as *opaque*
`SimStmtStep`/`SimTermStep` props. With the builders (`simStmtStep_callfree`/`simTermStep_callfree`)
those props are now CONSTRUCTIBLE from `WellFormedLowered` (the folded structural side-conditions)
plus the genuine §7 recording-correspondence ties. `lower_conforms_wf` re-states the headline at
that altitude: its hypotheses reduce to

* **well-formedness** — `WellFormedLowered prog` (`MatFueled` + pc/offset bounds) and `CallFree`
  per block;
* **the genuine §7 ties** — the per-block statement (`StmtTies`) and terminator (`TermTies`)
  recording-correspondence bundles (collected/named below), and the entry-frame ties;
* **the IR run** — `hir`.

It delegates to `lower_conforms`, building `hstmts`/`hterm` through the combined builders. -/

/-- `prog.blocks.toList[L.idx]? = some b` from `blockAt prog L = some b` (the reverse of
`blockAt_of_toList`). -/
theorem toList_of_blockAt {prog : Program} {L : Label} {b : Block}
    (hbat : blockAt prog L = some b) : prog.blocks.toList[L.idx]? = some b := by
  have : blockAt prog L = prog.blocks.toList[L.idx]? := by
    unfold blockAt; rw [Array.getElem?_toList]
  rwa [this] at hbat

/-- **The per-block STATEMENT genuine §7 ties** — exactly what `simStmtStep_callfree` consumes:
the assign-cursor post-state realisability and the sstore-cursor runtime SSTORE ties, over every
cursor of block `b`. (The structural fuel/pc side-conditions are NOT here — they are folded into
`WellFormedLowered`.) -/
def StmtTies (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (L : Label) (b : Block) : Prop :=
  (∀ (pc : Nat) (t : Tmp) (e : Expr) (st0 st0' : V2.IRState) (fr0 : Frame),
      b.stmts[pc]? = some (.assign t e) →
      Corr prog sloadChg obs st0 fr0 L pc →
      StepScoped prog st0 (.assign t e)
      ∧ (∀ t', st0'.locals t' ≠ none → ¬ NonRecomputable prog t' ∧ defsOf prog t' ≠ none)
      ∧ SloadRealises sloadChg st0' fr0
      ∧ GasRealises obs fr0)
  ∧ (∀ (pc : Nat) (key value : Tmp) (kw vw : Word) (st0 : V2.IRState) (fr0 : Frame),
      b.stmts[pc]? = some (.sstore key value) →
      Corr prog sloadChg obs st0 fr0 L pc →
      st0.locals key = some kw → st0.locals value = some vw →
      StepScoped prog st0 (.sstore key value)
      ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).sum
          + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).sum
          ≤ fr0.exec.gasAvailable.toNat
      ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
          + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024
      ∧ (∃ acc, SstoreRealises fr0 kw vw acc) ∧ vw ≠ 0)

/-- **The per-block TERMINATOR genuine §7 ties** — exactly what `simTermStep_callfree` consumes:
the successor-block presence (for edges) and the per-shape runtime ties (`hstop`/`hretties`/
`hjump`/`hbranch`). (The structural pc/offset bounds are folded into `WellFormedLowered`.) -/
def TermTies (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (_o : V2.CallOracle)
    (self : AccountAddress) (L : Label) (b : Block) : Prop :=
  (∀ (L' : Label), (b.term = .jump L' ∨ (∃ c o', b.term = .branch c L' o')
      ∨ (∃ c t', b.term = .branch c t' L')) →
      ∃ b', prog.blocks.toList[L'.idx]? = some b' ∧ L'.idx < prog.blocks.size)
  ∧ (b.term = .stop →
      ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        self = frT.exec.executionEnv.address
        ∧ (∃ cp, frT.kind = .call cp)
        ∧ ¬ (frT.exec.accounts == ∅) = true)
  ∧ (∀ t, b.term = .ret t →
      ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        self = frT.exec.executionEnv.address
        ∧ (∃ vw, st'.locals t = some vw)
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
            ≤ frT.exec.gasAvailable.toNat
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
        ∧ (∀ frv : Frame, Runs frT frv →
            frv.exec.executionEnv.code = frT.exec.executionEnv.code →
            frv.exec.executionEnv.address = frT.exec.executionEnv.address →
            (∀ k, selfStorage frv k = selfStorage frT k) →
            ∃ last rest output cp,
              Runs frv last
              ∧ stepFrame last = .halted (.success (returnEmptyPost last.exec rest) output)
              ∧ last.exec.executionEnv.address = frT.exec.executionEnv.address
              ∧ (∀ k, selfStorage last k = selfStorage frT k)
              ∧ last.kind = .call cp
              ∧ ¬ (last.exec.accounts == ∅) = true))
  ∧ (∀ dst bdst, b.term = .jump dst →
      prog.blocks.toList[dst.idx]? = some bdst → dst.idx < prog.blocks.size →
      ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        3 ≤ frT.exec.gasAvailable.toNat
        ∧ GasConstants.Gmid ≤ (pushFrameW frT
            (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
            4).exec.gasAvailable.toNat
        ∧ GasConstants.Gjumpdest
            ≤ (jumpFrame (pushFrameW frT
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32)) 4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                frT.exec.stack).exec.gasAvailable.toNat)
  ∧ (∀ cond thenL elseL bthen belse, b.term = .branch cond thenL elseL →
      prog.blocks.toList[thenL.idx]? = some bthen → prog.blocks.toList[elseL.idx]? = some belse →
      thenL.idx < prog.blocks.size → elseL.idx < prog.blocks.size →
      ∀ (st' : V2.IRState) (frT : Frame) (cw : Word),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        st'.locals cond = some cw →
        ∃ frc, MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
          ∧ 3 ≤ frc.exec.gasAvailable.toNat
          ∧ GasConstants.Ghigh ≤ (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              GasConstants.Ghigh
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
              GasConstants.Gmid
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
              (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat)

/-- **`lower_conforms_wf` — the builder-based world-channel compiler-correctness headline.**
For a call-free program `prog` whose lowering is well-formed (`WellFormedLowered`) and whose
blocks are call-free (`hcf`), if the recording run over the top-level `.Code (lower prog)` call
succeeds (`hwl`/`hp`/`hmod`), the entry block is block 0 / present / pc-bounded
(`hentry0`/`hbentry`/`hbound`), the genuine entry-frame ties hold (`hstore`/`hsload`/`hgasr`/
`hgasj`), the genuine per-block statement (`hstmtties`) and terminator (`htermties`) §7 ties hold,
and the IR runs under the realised oracles to `O` (`hir`), then **the IR observable's world equals
the `observe` world of the recorded bytecode result**:

  `O.world = (observe self log.observable).world`.

The per-block simulations are built from `WellFormedLowered` + the §7 ties via
`simStmtStep_callfree`/`simTermStep_callfree`; the world edge is `lower_conforms`. -/
theorem lower_conforms_wf {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {O : V2.Observable} {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    -- recording run + entry-frame structural facts + entry ties (verbatim from `lower_conforms`):
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hsload : SloadRealises sloadChg { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasr : GasRealises obs (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    -- WELL-FORMEDNESS: the folded structural side-conditions + call-freedom.
    (hwf : WellFormedLowered prog)
    (hcf : ∀ (L : Label) (b : Block), blockAt prog L = some b → CallFree b.stmts)
    -- the GENUINE §7 per-block recording-correspondence ties (statement + terminator):
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs (realisedCall log self) self L b)
    -- the IR run under the realised oracles (the IR side of the conformance diagram):
    (hir : V2.IRRun prog (realisedCall log self) w₀ (realisedGas log) O) :
    O.world = (observe self log.observable).world := by
  -- build the per-block `SimStmtStep` from `WellFormedLowered` + the statement §7 ties.
  have hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs (realisedCall log self) L b := by
    intro L b hbat
    obtain ⟨hassign, hsstore⟩ := hstmtties L b hbat
    exact simStmtStep_callfree (toList_of_blockAt hbat) hwf (hcf L b hbat) hassign hsstore
  -- build the per-block `SimTermStep` from `WellFormedLowered` + the terminator §7 ties.
  have hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs (realisedCall log self) self L b := by
    intro L b hbat
    obtain ⟨hsucc, hstop, hretties, hjump, hbranch⟩ := htermties L b hbat
    exact simTermStep_callfree (toList_of_blockAt hbat) hwf hsucc hstop hretties hjump hbranch
  exact lower_conforms hwl hp hmod hentry0 hbentry hbound hstore hsload hgasr hgasj
    hstmts hterm hcf hir

end Lir

-- Build-enforced axiom-cleanliness guards for the Layer-F deliverables: the whole-CFG
-- simulation `sim_cfg`, the headline `lower_conforms` (call-free, world channel), the entry
-- correspondence builder `entry_corr` (discharges the former `hentry`), and the
-- `SimStmtStep`/`SimTermStep` discharge builders (`simStmtStep_assign`, `simTermStep_stop`)
-- all depend only on `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.sim_cfg
#print axioms Lir.lower_conforms
#print axioms Lir.lower_conforms_wf
#print axioms Lir.paramsFor_entersAsCode
#print axioms Lir.entry_corr
#print axioms Lir.simStmtStep_assign
#print axioms Lir.simStmtStep_sstore
#print axioms Lir.simStmtStep_callfree
#print axioms Lir.simTermStep_stop
#print axioms Lir.simTermStep_ret
#print axioms Lir.simTermStep_jump
#print axioms Lir.simTermStep_branch
#print axioms Lir.simTermStep_callfree
