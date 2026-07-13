# Plan: proving the general `lower_conforms` (the C grind)

> **SUPERSEDED (2026-07-03):** plan of record is `target-architecture-2026-07-02.md` + `execution-plan-2026-07-02.md`; the gas-law apparatus (Mono/Oracle/HonestGasTie) was deleted in Phase 2. The "GENUINE entry-frame realisability ties" (`GasRealises`/`SloadRealises`) referenced below were later shown **unsatisfiable** as universals (see `uniform-spill-alloc-plan.md` §0 and the target-architecture doc).

> **Update (2026-06-26):** the "general" theorem this plan delivered was actually
> **call-free** (`CallFree` gate). That distortion is now removed — calls compose via a
> memory value channel and `CallFree` is **deleted**; `lower_conforms` is general over all
> `Stmt.call`. See **`calls-value-channel-plan.md`** for the call story (the authoritative
> record). This document remains accurate for the call-free spine it built.

Decomposition from the architecture pass (2026-06-26). The headline:

```lean
theorem lower_conforms (prog : Program) (w₀ : World) (self : AccountAddress) (log : RunLog) :
    runWithLog (paramsFor (lower prog) w₀) fuel = some log →
    IRRun prog (realisedGas log) (realisedCall log self) w₀ (observe self log.observable)
```

Factors into two sides meeting at a shared `Observable`: **IR side** (`RunFrom`/`RunStmts`/`EvalStmt`
derivation — mechanical, induction on `RunFrom`, like the concrete `proto_IRRun`/`guard_IRRun`) and
**bytecode side over `lower prog`** (assemble `Runs fr₀ last`, generically — where all the hard work is).
Rich brick set already exists in `Match.lean` (`sim_imm/add/lt/sload/gas/sstore/jump/branch/call`,
`halt_stop/ret`), `Layout.lean` (`flatBytes_block_split`, `mid_index`, `stmt_byte_anchor`), `DecodeLower.lean`
(`decode_lower_nonpush/push`). Missing: the **inductive assembly engine** + the hard leaf bricks below.

## DESIGN DECISION (made 2026-06-26 — Eduardo to confirm/override)
**`WellFormed prog`**: every tmp defined by `Expr.gas` (and every call-result tmp) is **materialised at
most once** by the lowering (used ≤ once). Rationale: recompute-on-use is sound for pure exprs (recompute =
same value) but UNSOUND for `.gas` (re-emitting `GAS` reads a *fresh, different* value) and call results
(dynamic). Single-use makes the lowering faithful without a binding/DUP slot. `lower_conforms` carries
`WellFormed prog` as a hypothesis. The concrete programs (`protoIR`/`guardIR`) already satisfy it.
*Future:* lift via a stack/`DUP` binding slot (like v1's `callResult` slot) if multi-use gas is wanted.

## The DAG (bottom-up; ✶ = hard / new scaffolding)

**Layer A — decode-at-cursor over `lower prog`**
- **A1 `decode_at_stmt_head`** — head opcode of a statement decodes right. Deps: `flatBytes_at_pcOf`,
  `decode_lower_*`. *medium.*
- **A2 `decode_at_offset`** — decode at an arbitrary byte cursor inside a statement's push-sequence.
  Deps: generalize `stmt_byte_anchor` via `mid_index` (the `k=0` instance already exists). *medium.*
- **A3 `decode_at_term`** — terminator opcodes decode right. Deps: new `term_byte_anchor` from
  `flatBytes_block_split`. *medium.*

**Layer B — per-Expr materialisation (the value channel)**
- **B1 ✶ `materialise_runs`** — running `materialiseExpr defs fuel e` pushes `evalExpr … e`'s value,
  stack returns to base+1, storage unchanged, pc advanced. Induction mirroring `materialiseExpr`; leaves
  `sim_imm`, recursion `sim_add/lt/sload`, `sim_gas`; `.tmp`→`defs` recursion needs **B3**. THE linchpin.
- **B2 `materialise_gas_charge`** — gas charged = `subCharges` of a per-Expr charge-list (the honest-gas
  envelope). Deps: `toNat_subCharges` (exists). *medium, tedious; INDEPENDENT.*
- **B3 ✶ `DefsSound`** — **DONE** (`LirLean/DefsSound.lean`, axiom-clean). `WellFormed prog` (single-use
  of every gas-/call-defined tmp) formalised + decidable surrogate `WellFormedDec`; `protoIR`/`callIR`
  checked `WellFormed` by `decide`, `guardIR` proved **¬WellFormed** (it multi-uses its first gas read —
  the discriminating case the DUP-slot escape hatch would lift). `DefsSound prog st := ∀ t e w, defsOf
  prog t = some e → ¬NonRecomputable prog t → st.locals t = some w → some w = evalExpr st 0 e` (ranges over
  *recomputable, currently-assigned* tmps; non-recomputable gas/call tmps excluded — accounted by
  `WellFormed` single-use). Vacuous at entry; **preserved by all four `EvalStmt` arms** (`defsSound_preserved`)
  given honest per-step define-before-use / no-live-`sload`-across-a-write scoping side conditions (bundled
  as `StepScoped`; a program-global `WellScoped` discharging them once by a topological-order argument is
  follow-up). No `sorry`/`axiom`.

**Layer C — per-Stmt** `sim_stmt`: one `EvalStmt` step ↔ one lowered-statement `Runs` segment.
assign (0 bytes, `setLocal`, preserve `Match`+`DefsSound`) *mechanical*; sstore (2×B1 + `sim_sstore`)
*medium*; call (`sim_call` → `Runs.call`/`CallReturns`, tie realised oracle via `callRealises_bridge`) *hard*.

**Layer D** `sim_stmts`: induction on `RunStmts`, glue `sim_stmt` by `Runs.trans`; recompute-on-use gives
`M5 stack_nil` between statements. *medium.*

**Layer E — control flow**
- **E1 `sim_term_halt`** — ret/stop → halting `last` frame; `halt_stop`/`halt_ret`. ret value-faithful is
  *hard* (value channel, deferred). stop *medium*.
- **E2 ✶ `sim_term_edge`** — jump/branch land at successor entry; `sim_jump`/`sim_branch`. Needs E3.
- **E3 ✶ `block_offset_validJump`** — **DONE** (`LirLean/JumpValid.lean`, axiom-clean). Every block
  offset ∈ `validJumpDests (lower prog) 0`; byte is `JUMPDEST`, reachable skipping PUSH32/PUSH4
  immediates. Generalized `nineteen_mem_validJumps`/`wc_reaches_414` from a fixed program to an
  arbitrary `lower prog` via: a list-level `SegAligned` (instruction-aligned byte segment) predicate +
  `reaches_of_segAligned` transport (the push-skipping discharged once); `segAligned_emit*` showing
  every emission helper is aligned; `reaches_block_offset` (induction on block index, each block steps
  `blockLen` bytes matching `offsetTable`'s prefix sum). *was hard; INDEPENDENT.*

**Layer F** — **DONE** (`LirLean/LowerConforms.lean`, axiom-clean). `sim_cfg` (induction on
`RunFrom`: D `sim_stmts_block` + E `SimTermStep` halt/edge + IH) is **fully proved** — the
structural core. `lower_conforms` (call-free, WORLD channel) ties `sim_cfg` to the recorder via
`runWithLog_messageCall` + `messageCall_runs` + `observe`-reads-only-`toCallResult`: the world
edge `O.world = (observe self log.observable).world` is **fully discharged**. The per-block
realisability is carried as two structured `∀`-hypotheses at the Layer-D/E conclusion altitude:
`SimStmtStep` (D) and the new `SimTermStep` (E, this file) — the supplied-observation contract
(§7), discharged for a concrete program by a `b.term` case-split feeding the four `sim_term_*`
lemmas. The entry `Corr` (`hentry`), call-freedom (`hcf`), and the IR run under the realised
oracles (`hir`) are likewise carried hypotheses; `paramsFor`/`paramsFor_entersAsCode` give the
canonical top-level instantiation (`EntersAsCode` via `codeFrame`/`beginCall_code`). REALISABILITY-DISCHARGE PASS (2026-06-26): the former entry `Corr` hypothesis is now
**discharged** in-`lower_conforms` by `entry_corr` (the generic entry-`Corr` builder incl. the
leading-JUMPDEST step: `decode_at_block_offset_jumpdest` + `corr_at_jumpdest_landing`). Its
replacements are the structural entry facts (entry block = block 0, present, pc-bounded) and the
GENUINE entry-frame realisability ties (`StorageAgree`/`SloadRealises`/`GasRealises` at the entry
frame + `Gjumpdest` margin) — the minimal honest §7 surface. The `SimStmtStep`/`SimTermStep`
bundles now have per-shape discharge builders: `simStmtStep_assign` (an assign-only call-free
block, **fully closed** down to the per-cursor `StepScoped` + post-state realisability ties) and
`simTermStep_stop` (a `stop`-terminator block, **fully closed** — STOP decode from A3, edge/ret
arms vacuous — down to the genuine top-level-frame facts). BUILDER-CONVERGENCE PASS (2026-06-26):
all four remaining shapes now have decode-free discharge builders threading the `_lowered`
wrappers (`sim_sstore_stmt_lowered`/`sim_term_halt_ret_lowered`/`sim_term_edge_jump_lowered`/
`sim_term_edge_branch_lowered` — the A2/A3 `materialiseExpr`/`emitTerm` reconstruction is done
*inside* the wrappers, generically over `lower prog`): `simStmtStep_sstore`,
`simTermStep_ret`/`_jump`/`_branch`, plus the COMBINED `simStmtStep_callfree` /
`simTermStep_callfree` that case-split a general call-free block into the right arm — so
`SimStmtStep`/`SimTermStep` are CONSTRUCTIBLE for any call-free block. The structural
side-conditions (recompute-fuel `MatFueled` + pc/offset `< 2^32` bounds) are FOLDED into the
`WellFormedLowered prog` predicate, so they leave the builder hypotheses entirely. (The
`sim_term_edge_branch` conclusion was strengthened to cw-tie the resolved successor — `cw ≠ 0 ∧
L' = thenL ∨ cw = 0 ∧ L' = elseL` — so the `SimTermStep.edge` branch disjunct's chosen `succ`
reconciles with the runtime-resolved jump.) The builder-based headline `lower_conforms_wf`
re-states `lower_conforms` with hypotheses reduced to: `WellFormedLowered` + `CallFree`
(well-formedness), the GENUINE §7 per-block ties (`StmtTies`/`TermTies`, collected predicates) +
the entry-frame ties, and `hir`. CARRIED (the precise honest residual): `WellFormedLowered`
(`MatFueled` was carried in this historical plan; P8 has since made `WellFormedLowered`
fuel-free over `matCache` lengths / fold offsets and rebuilds it from `IRWellFormed` +
`codeFits` + `stackFits`), the per-intermediate-frame SLOAD/SSTORE/GAS + `validJumps` + RETURN-site
recording-correspondence ties (the trace-supplied gas/warmth/storage = the actual frames), and
the IR-run hypothesis `hir` (no bytecode→IR `RunFrom` synthesis). No
`sorry`/`axiom`/`native_decide`; axiom-clean `[propext, Classical.choice, Quot.sound]`.

SELF-CONTAINMENT PASS (2026-06-26): two residuals of `lower_conforms_acyclic` discharged for the
single-halting-block fragment, banked as corollaries (`LirLean/Acyclic.lean`).
- **`hir` (constructed, not assumed)** — `LirLean/IRRun.lean` builds the IR-run EXISTENCE
  ladder (frame-free, imports only `Lir.Law`): `evalStmt_exists` (gas-free non-call step total on
  `StmtDefinable`), `runStmts_exists` (gas-free call-free list, threaded `StmtsDefinable`),
  `runFrom_exists_stop`/`_ret` + `irRun_exists_stop`/`_ret` (single halting block — the DAG base
  case, no CFG measure needed). `lower_conforms_acyclic_stop` delegates to `lower_conforms_acyclic`
  with `hir` discharged by construction.
- **`hstore` (definitional)** — the entry STORAGE tie is not a runtime fact: `w₀` is free, so
  choosing `w₀ := selfStorage (codeFrame …)` makes `StorageAgree` hold by `rfl`
  (`entry_storageAgree_codeFrame`, `LirLean/LowerConforms.lean`). `lower_conforms_acyclic_stop_canonical`
  banks BOTH `hir` and `hstore`.
- **DEEP / NOT EXTRACTABLE (precise blocker).** The gas envelopes (`StmtTies`/`TermTies`) and the
  recording-correspondence (`SloadRealises`/`GasRealises`/`SstoreRealises` = recorded values) are
  quantified `∀ st' frT, Corr … frT … → …` over *arbitrary* `Corr`-corresponding frames. `sim_cfg`
  CONSUMES them to assemble `Runs`; `messageCall_runs` is forward-only (assembled `Runs` ⇒
  `messageCall`). There is NO backward lemma extracting per-frame gas/warmth from `runWithLog =
  some log`. Closing these needs a NEW forward-simulation aligning the IR run's per-cursor frames
  with `drive`/`runWithLog`'s frames step-by-step (so the bytecode frame at each IR cursor IS the
  recorded one, hence carries the recorded gas/warmth/storage). This same lemma supplies the
  general (multi-block, gas-reading) `hir` trace `realisedGas log`. Multi-block `hir` *also* needs
  a CFG-acyclicity *block*-rank measure (distinct from `Acyclic.lean`'s def-graph rank) — see
  `IRRun.lean`'s closing note (items 1–3).

## Deferred channels (separate milestones)
- **Value channel** (`returned w` ↔ RETURN window): needs `ret` lowering → `MSTORE`+`RETURN(off,32)`, new
  `runs_mstore`, `output_eq_word`, faithful `observe.result`. Gated on a lowering change. Defer.
- **Top-level `runWithLog.observable`** (vs recorded child datum): `runWithLog_drive` pins `.observable`;
  remaining = `log.calls` = program CALL sequence (single-call ≈ done via `realisedCall_eq_evmV2`; multi-call
  needs `runWithLog_calls_eq`). *medium/hard.*
- **Revert/exception**: new `IRHalt.reverted` + `EvalStmt`/`RunFrom`/`observe` paths + bytecode bridge.
  Defer entirely.

## Missing scaffolding (multi-node)
the assembly engine (D1+F1); B1+B2; B3 + gas-recompute coherence (`WellFormed`); A2/A3 anchors; E3
jump-validity; `RunFrom` determinism (DONE, `Law.lean`) / totality (single-block DONE,
`IRRun.lean`; multi-block needs a CFG block-rank measure); a generic `paramsFor` (DONE,
`LowerConforms.lean`). **THE remaining deep node: a forward-simulation aligning IR-run frames with
`drive`/`runWithLog` frames** — the source of the gas-envelope / SLOAD/GAS/SSTORE recording-
correspondence ties AND the general `hir` trace (`realisedGas log`).

## Fan-out order (executing SEQUENTIALLY on warm `ir-convergence`)
Independent leaves first: **A1–A3** (near-mechanical, unblocks B1/E) → **B2** (independent gas arith) →
**E3** (hardest independent, long leash). Then the spine: **B3+B1** → **C** → **D** → **E1/E2** → **F**.
