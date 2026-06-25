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
