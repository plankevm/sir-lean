# ir-design-v3 — convergence: observe-don't-model, one law each, realisability witness

> Supersedes the *parallel-exploration* framing of v1 (`ir-design.md`, the "oracle /
> cost-accounting" line, branch `main`) and v2 (`ir-design-v2.md`, the "gas-free
> observable" line, branch `exp005-ir`). v3 is the **convergence**: keep v2's gas-free
> observable machine + event trace; fold v1's `resumeAfterCall` projections in as the
> *realisability witness* for calls; unify gas and calls under one principle.

## 0. The principle (one sentence)

**Gas and external calls are both "things the IR observes but does not model" — so model
each as an opaque value supplied by a trace event, carrying exactly *one* minimal law,
with a *realisability* side-condition that the EVM instance discharges.**

This is the CompCert external-call discipline, applied to gas as well as calls. The two
features that looked ad-hoc in v1/v2 (a gas oracle, a call oracle) become one shape.

## 1. Permissive semantics, restrictive theorem (the load-bearing idea)

- The IR *relation* is **permissive**: non-deterministic in the trace — you may supply
  any event sequence satisfying the law. (Gas: "any monotone sequence.")
- The *headline theorem* quantifies over the **realised** trace only — the one the
  lowered bytecode actually produces (the realisability side-condition).

Consequence: pathological traces (repeated `gasRead`s, all-zeros, etc.) are *admitted at
the type level and quantified away*. They never appear in any conclusion, so they are
never reasoned about. We do **not** constrain the semantics to exclude them — we exclude
them from the theorem, which is free.

## 2. Gas — SETTLED

- **Value: `Word`** (what `GAS` pushes) — realisability is then `rfl`-direct. *Not* `ℕ`.
- **`ℕ` appears only in the law, via `.toNat`** — exactly as `Runs.gasAvailable_le` is
  already stated.
- **The one law: the `gasRead` subsequence is monotone NON-INCREASING on `.toNat`.**
  Non-strict — the IR has no per-opcode cost, so `<` is unprovable here (and `<` is
  exactly the gas-static-analysis / loop-termination non-goal). Model **available** gas,
  not used (available is bounded below by `0` for free → no out-of-gas modeling; used
  would force an extra `used ≤ limit` invariant and a subtraction).
- **The law is not bolted on.** It is `Runs.gasAvailable_le`
  (`BytecodeLayer/Hoare/GasMonotone.lean`), the *same per-transition gas-descent lemmas
  the never-OutOfFuel fuel proof already needed* (`stepFrame_next_lt`,
  `systemOp_next_gas`, `resumeAfterCall_gas_le`, …), reassembled at `≤` (the `mu_bound`
  skeleton with the `+2` slack relaxed). Holds across `.call` nodes via the 63/64
  net-debit. The only genuinely-new fact was `drive_gasRemaining_le_totalGas` (gas
  *conservation*, vs the fuel *measure*).
- **`evmGasOracle`** is the realised instance; its monotonicity obligation is discharged
  by `Runs.gasAvailable_le`. The IR reasons against the abstract oracle (the law only).

## 3. Calls

- **Event:** `Event.call callee calldata world' success returndata` (v2's observable
  boundary — gas-free, no pc).
- **Realisability:** the event's fields `= what messageCall / resumeAfterCall produces`.
  This is **already discharged by v1's `evmCallOracle`** (`LirLean/Call.lean`): each field
  is a *projection of `resumeAfterCall`* (`postStorage` through the `find?/lookupStorage`
  lens, `restoredGas = gasAfterReturn`, `successWord = head of the resumed stack = x`),
  `rfl`-clean, with `evmCallOracle_successWord_eq_x` pinning the flag to exp003's
  `callSuccessFlag` (`0` on failure / insufficient balance / depth 1024, else `1`).
- **Success word delivery:** it is the one value not recomputable from a pure `Expr`, so
  it travels through the `IRState.callResult` slot and is bound once into `locals` at
  `resultTmp` (v1's insight — survives into v3 as *how* the supplied success word reaches
  the register file, keeping `Match`'s `M5 stack_nil`).

## 4. The risk surface (where the care goes — NOT the pathologies)

1. **The realisability side-condition itself.** Stated too weak → the headline drifts
   vacuous; too strong → undischargeable. State it as *equality to the `messageCall` /
   `GAS` output*, for both events, so the gas discipline and the call discipline read the
   same.
2. **`RunFrom` determinism lemma.** So the headline reads `∀ O, IRRun … O → …` ("the IR
   run on the realised trace yields *the* observable"), not "*an* observable."

Get these two right and the monotonicity pathologies never need a second thought.

## 5. Sprint

| # | milestone | needs |
|---|---|---|
| **S1** | Lock the gas-oracle interface: `Word`-valued `gasRead`, single monotone-`toNat` law sourced from `Runs.gasAvailable_le`, realisability side-condition made explicit; **add the `RunFrom` determinism lemma**; re-thread `lower_preserves_obs_mono` through the explicit interface. | B + `GasMonotone` (on `exp005-ir`) — no A |
| **S2** | Build the `Stmt.call` **event** step in `V2` (gas-free, observable boundary). | §7 defaults (below) |
| **S3** | Bring v1's `Call.lean` into the build; use `evmCallOracle` + `evmCallOracle_successWord_eq_x` as the **realisability witness** for the S2 call event. | A + B together |
| **S4** | Extend `lower_preserves_obs` to a with-CALL program → `workedCall` parity, in v2 form. | S2 + S3 |
| **S5** | Decide v1's standalone layer (`Gas.lean`/`Call.lean` cost-accounting line): excise from `main`, or keep as executable reference. | after parity |

## 6. §7 decisions — LOCKED (Eduardo, this session)

1. **`World` decoupling:** observable-native record + thin lens.
2. **Simulation direction:** forward — "IR says `O` ⇒ bytecode (enough gas) does `O`"
   (the useful compiler guarantee).
3. **calldata / returndata / value:** value-free, empty calldata/returndata first cut
   (mirrors v1 `workedCall`); **revert deferred**.
4. **`Expr.gas`:** observed `gasRead` event, no accounting (was decided 2026-06-23, §3.4).

## 7. The interaction model — SETTLED (this session)

The correctness theorem is a **supplied-observation** model, *not* a lockstep simulation —
chosen because it is the *correct* abstraction for an optimizing IR, not merely the easy one:

- An optimizing lowering has **no step-correspondence** (one IR construct → many ops,
  reordered/fused/eliminated), so lockstep / step-matching is the wrong tool.
- The supplied-observation model constrains **observables only** (the gas-read sequence,
  the call results, the final storage delta) — never intermediate steps — so it is
  **robust to arbitrary lowerings** and decoupled from lowering internals.
- It is **proof-level**: the bytecode run is a `Runs` *derivation*; "extract the
  observations" is a function on that derivation. **No JIT, no runtime co-execution.**

Gas and calls differ only in how many **IR-visible inputs** the supplied thing takes —
both are supplied/abstract because they depend on bytecode state the IR deliberately lacks
(gas counter; chain state). Neither is computed in the IR:

- **Gas — a supplied SEQUENCE** (zero IR-visible inputs). Consumed stepwise (the head pops
  as execution reaches each `GAS` — already "queried at the moment"). The IR may assume
  only monotonicity. Realisability = the bytecode `Runs` derivation's GAS subsequence.
- **Calls — a FUNCTION oracle** of the call's IR-visible inputs (callee, calldata),
  queried at the call site, returning the `(world', success[, returndata])` bundle the
  semantics **applies as a state change** (`world := world'`, bind `success`). This is
  v1's `CallOracle`; instantiated to `messageCall`/`resumeAfterCall`, realisability is
  by-construction (`rfl`). **No gas in the bundle** (V2 has no gas-in-state — post-call
  gas reads come from the gas sequence) and **no `callResult` slot** (bind `success`
  straight into `locals`; the slot was a v1 small-step/`Match` artifact).

**The one realisability contract (the honest assumption):** the lowering must preserve the
**observable interaction sequence** — the order/count of GAS-reads, the order of calls,
and the final storage delta. (Storage *writes* may be reordered — only the final delta is
observed.) Far weaker and more lowering-agnostic than step-matching.

This isolates "is the lowering observably correct" from "what gas did it cost" — the latter
is exactly what we refuse to reason about.

## 8. Aspirational target — shapes & theorems (regime (i): instrumented interpreter)

**Decision (this session): regime (i).** The realised oracles are projections of an
instrumented **`Type`-valued** interpreter (`runWithLog`), NOT extracted from the `Prop`
relation `Runs`. Reason: `Prop` is proof-irrelevant, so it cannot be eliminated into `Type`
(`realisedGas : Runs → GasOracle` does not typecheck — large elimination is restricted to
subsingletons, and `Runs` has many derivations). The instrumented interpreter is `Type`,
so its projections are honest functions and realisability is constructive/`rfl` — exactly
how the *call* oracle already works (`evmV2CallOracle` = the `resumeAfterCall` projection).
Full theory writeup: `docs/lessons/derivations-traces-and-proof-relevance.md`.

```lean
-- The oracles = the EVM facets the IR refuses to model.
abbrev GasOracle  := List Word                          -- consumed stream; ZERO IR-visible inputs
abbrev CallOracle := Word → Word → World → World × Word  -- callee → gasFwd → world ↦ (world', success)
def    MonotoneGas (g : GasOracle) : Prop               -- the ONE law (engine-free), used only at gas-branches

-- The IR run — permissive (NO law baked in); determinism makes it a function.
def IRRun (prog : Program) (gas : GasOracle) (call : CallOracle) (w₀ : World) : Observable → Prop
theorem IRRun.det : IRRun prog g c w₀ O → IRRun prog g c w₀ O' → O = O'

-- regime (i): the instrumented executable interpreter — "runs the bytecode AND records
-- the introspection points." Type-valued ⇒ realised oracles are projections (functions).
structure RunLog where
  observable : Observable
  gas        : List Word         -- GAS reads, in order   → realisedGas
  calls      : List CallRecord   -- call results, in order → realisedCall
def runWithLog (code : Bytecode) (w₀ : World) (fuel : ℕ) : Option RunLog
def realisedGas  (log : RunLog) : GasOracle  := log.gas
def realisedCall (log : RunLog) : CallOracle := callOracleOf log.calls

-- realisability = the engine meets the contracts (gas law DISCHARGED, not assumed):
theorem realisedGas_monotone (log) : runWithLog code w₀ f = some log → MonotoneGas (realisedGas log)
--   ↑ from Runs.gasAvailable_le (via adequacy runWithLog ↔ Runs)

-- THE HEADLINE (conformance): ∀ IR programs, IR under the realised oracles = the spec.
theorem lower_conforms (prog : Program) (w₀ : World) (log : RunLog) :
    runWithLog (lower prog) w₀ fuel = some log →
    IRRun prog (realisedGas log) (realisedCall log) w₀ log.observable

-- THE AGNOSTIC CLASS: oracle-untouching fragments — proved once, ∀ oracles.
theorem observable_oracle_agnostic (prog : NonGasNonCall) :
    ∀ g g' c c' w₀ O, IRRun prog g c w₀ O ↔ IRRun prog g' c' w₀ O
```

**HAVE** (on `exp005-ir`): `GasOracle`/`MonotoneGas`, `CallOracle`, `IRRun`, `IRRun.det`;
`realisedCall`+faithfulness (`evmV2CallOracle`/`callRealises_bridge`, `rfl`);
`realisedGas_monotone` (relational `GasRealises.monotoneGas` from `Runs.gasAvailable_le`);
`lower_conforms` on a concrete program (`wc_call_parity_v2`).

**NEED**: the instrumented `runWithLog` (regime (i)) + adequacy `runWithLog ↔ Runs`;
general `lower : Program → Bytecode` + its run; general `lower_conforms` (compose
per-construct lowering correctness + the two realisability facts + `IRRun.det`);
`observable_oracle_agnostic`.

**First concrete step — the `Event → List Word` collapse — DONE.** Now that calls are a
function-oracle (not trace entries), `Event` had only `gasRead` left, so `Trace ≅ List Word`.
`inductive Event` is removed; `abbrev GasOracle := List Word` is the canonical name (with
`abbrev Trace := GasOracle` kept as a thin signature-position alias), `assignGas` consumes
`obs :: T` directly, `MonotoneGas`/`Trace.gasMonotone` is the chain over the `List Word`
directly (the old `Trace.gasReads` extractor was the identity and is gone), and `GasRealises`
is `T = frs.map gasReadOf`. Axiom-clean (`{propext, Classical.choice, Quot.sound}`); every
prior theorem stayed green with equivalent statements (`Event.gasRead obs` ↦ `obs`).
