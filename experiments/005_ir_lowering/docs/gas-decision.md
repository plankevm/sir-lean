# Gas decision (settled 2026-07-02)

**Decision by the project lead. This supersedes the gas-monotonicity framing in `ir-design-v3.md` §2/§4/§8 and the "gas introspection is the headline reason" framing in `PLAN.md`.**

## The decision

Gas was always going to be an **oracle** returning opaque values. We can only prove **exact** equivalence when the oracle's returned values are the *same* values the lowered bytecode actually produces. Gas is only defined on bytecode; defining a gas semantics for the IR would be contorted. Therefore:

1. **Gas is just another log-fed oracle.** The realisability closure runs the lowered bytecode with the recording interpreter (`runWithLog`), and **feeds the recorded gas / sload / call values into the IR oracles**, then proves **exact equality**. Gas introspection is handled the same way as external calls: an opaque value pinned to what the real run produced.
2. **The gas-monotonicity law is DROPPED.** `Trace.gasMonotone` / `MonotoneGas` (Law.lean), `realisedGas_monotone` (RunLog.lean:589), `GasRealises.monotoneGas` (Oracle.lean), `lower_preserves_obs_mono` (Mono.lean) are proved-but-unused — they add complication and buy nothing once gas is an exact log-fed value. Delete them; do **not** re-prove or weaken. No replacement theorem — the surviving gas guarantee is the per-cursor **exact-equality** `StmtTies.gas` conjunct (`ob = ofUInt64(fr.gas − Gbase)`, LowerConforms.lean:1398).
3. **Two theorems, not one.**
   - **Flagship:** the log-fed exact-equality lowering-conformance theorem (`lower_conforms_cyclic`, unconditional over `runWithLog`-halting programs).
   - **Secondary (optional):** a gas-introspection-*free* general lowering theorem for the no-`.gas` IR subset (the gas value conjunct is vacuous, needs no positional recorder bridge — the "fork-shaped" general theorem, matching what Verity/vyper-hol prove).

## Why this is the right call (prior-art corroboration)

- **verifereum** (HOL4 EVM): its gas-decrease property earns its keep *only* as the well-foundedness witness that makes `run` total (`run_tr` termination, `vfmDecreasesGasScript.sml:2063-2085`). A gas law with **no consumer** is dead weight. Ours has no consumer → delete. verifereum's `Collect`/`Enforce` domain duality (`vfmExecutionScript.sml:494`) is exactly our record-then-feed pattern.
- **Verity** (Lean, on Nethermind semantics): drops gas *entirely* (`TRUST_ASSUMPTIONS.md:59-65`). A *recorded* gas value is strictly stronger than what mature prior art does.
- Both confirm: correspondence should be **derived from a real run**, never assumed.

## Lesson (appended 2026-07-02, Phase 2 executed)

The retired `Lir.GasRealises` universal (`∀ g, g.addr = fr.addr → obs = ofUInt64 (g.gasAvailable − Gbase)`) was **unsatisfiable** for any run with two distinct same-address gas reads — HonestGasTie's finding, machine-checked as `gasRealises_universal_unsatisfiable`. The disease is the free ∀: quantifying over *every* same-address frame instead of pinning the value to the positionally-matched recorded read. The 2026-07-02 skeptic verdict (`fleet-2026-07-02/skeptic-f1-verdict.md`) shows the **same** free-∀ shape in the current `StmtTies`/`TermTies` supplied conjuncts — the vacuity check must be applied to every new tie statement (R0 of the realisability spec). With Phase 2 executed, the HonestGasTie witness file is deleted along with the law layer (`V2/Mono.lean`, `V2/Oracle.lean`, Law's `Trace.gasMonotone`/`MonotoneGas`, RunLog's `realisedGas_monotone`) — the deleted regression witnesses (`sloadRealises_universal_unsatisfiable`, `new_sloadLogAligned_two_read_satisfiable`, `sload_tie_vacuity_resolved`, `spilled_gas_value_tie_realisable`, and the gas analogues) survive only in git history and in this record; the surviving gas guarantee is the per-cursor exact-equality `StmtTies.gas` conjunct, and this paragraph is the lesson's record.
