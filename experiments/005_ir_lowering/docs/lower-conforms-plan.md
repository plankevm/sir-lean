# Plan: proving the general `lower_conforms` (the C grind)

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

**Layer F** `sim_cfg` (induction on `RunFrom`: D1 + E1/E2/IH) → `lower_conforms` (compose via
`runWithLog_drive`/`messageCall_runs`; realised oracles aligned by `realisedGas_monotone`/`callRealises_bridge`;
needs `RunFrom` determinism — `IRRun.det` exists for the worked program, generalize).

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
jump-validity; `RunFrom` determinism/totality; a generic `paramsFor`.

## Fan-out order (executing SEQUENTIALLY on warm `ir-convergence`)
Independent leaves first: **A1–A3** (near-mechanical, unblocks B1/E) → **B2** (independent gas arith) →
**E3** (hardest independent, long leash). Then the spine: **B3+B1** → **C** → **D** → **E1/E2** → **F**.
