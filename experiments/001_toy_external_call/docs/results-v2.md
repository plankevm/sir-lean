# Results: lowering v2 (gasless spec, reflexive calls, observables export)

*2026-06-11. Status: complete — `lake build` green, zero sorries/axioms across
all modules; all exported theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`.*

This documents what v2 set out to do, what was actually achieved, and — per
the brief — an honest accounting of where it fell short of the hope and what
the rough edges are. The strategic conclusion drawn from this work (retire
the toy IR, go bytecode-first) lives in
[`docs/bytecode-first-plan.md`](../../../docs/bytecode-first-plan.md).

## 1. What v2 set out to do

Philip's feedback on v1: the IR spec was low-level — it mirrored the EVM's
gas accounting opcode-for-opcode, its gas schedule was defined as the cost of
its own lowering (circular as a spec), and it leaned on a call-oracle
hypothesis. Goals, agreed with Eduardo:

1. remove the call oracle: external calls execute *arbitrary real bytecode*;
2. remove gas from the IR semantics and from the theorem statement, so the
   statement survives a gas-optimizing compiler;
3. export observables, not `injectFrame` equalities.

## 2. What was achieved

### The spec (`IR.lean`)

The IR semantics is now gasless and oracle-free. The gas counter of the
embedded EVM state is dead (never read, never influences a result); the IR
cannot run out of gas. External calls invoke EVMYulLean's own `EVM.call` —
the very function the lowered `CALL` opcode reaches — on a full tank, so
arbitrary callee bytecode runs (reentrancy included) and the callee receives
exactly the gas the program asked for. No oracle, no assumption about callee
behavior, anywhere.

### The theorems (all assumption-free; only `hsize`, a representability bound)

| Theorem | Statement (informal) |
|---|---|
| `lowering_exact` (`CallSound.lean`) | The v1 equality — bytecode under `EVM.X` *equals* the metered IR run, on the nose, at **every** gas and fuel level, errors included — with the oracle hypothesis **discharged**: `evmCallOracle_sound` proves `EVM.call` is frame-insensitive. |
| `run_erasure` (`GasErasure.lean`) | A successful gasless run is refined by the metered run on every sufficiently large representable budget, same final state up to leftover gas (`∃ G₀, ∀ G ∈ [G₀, 2²⁵⁶), …`). |
| `lowering_correct` (`Correctness.lean`) | The composition: a successful **gasless** IR run is reproduced by the lowered bytecode under every sufficiently large budget, final state equal up to frame fields + leftover gas. |
| `lowering_observables` (`Correctness.lean`) | The boundary form: `observe (EVM.X … (load program s G)) = some s'.observables` — accounts (all storage), substate (all logs), output. **No `injectFrame`, no gas, no frame fields in the conclusion.** |

Two pleasant surprises:

* **Frame insensitivity was nearly free.** What v1 carried as a hypothesis
  (`CallOracleSound`) is an 89-line file whose core proof is `if_congr` plus
  definitional equality — `EVM.call` provably never touches pc/stack/code.
  The reflexive-call design is what made it cheap: both sides of the call
  branch contain *literally the same `Θ` application*. (Compare: vyper-hol
  pays an admitted cheat (B5) at exactly this boundary because its source
  state differs from the EVM state; Verity doesn't execute calls at all.)
* **The v1 artifact was reused wholesale.** `Bytecode.lean`, `EVMLemmas.lean`
  and `Preservation.lean` (≈1700 lines of EVM-side proofs) compile unchanged;
  v2 is additive (`CallSound` 89 lines, `GasErasure` 860 lines,
  `Correctness` ~110 lines).

### The load-bearing finding: `CALL` consults gas

Discovered while designing the statement, and it permanently constrains every
future layer: even with no `GAS` opcode, gas is semantically observable
through calls — the forwarded amount is `min(g, ⌊63/64·remaining⌋)`, and a
callee that runs out of gas returns flag `0` to a caller that *continues*.
Hence the tempting statements `result ≠ OutOfGass → result = IR run` and
`∀G, OOG ∨ equal` are **false** (counterexample: modest budget, cap binds,
callee starves, flag 0 stored, clean `STOP` — a successful execution
divergent from the IR's, with no visible `OutOfGass`). The counterexample is
**executable** (`Validation.lean`, all checks enforced at build time): a
callee needing 22,106 gas (`SSTORE` then `STOP`), a caller forwarding
200,000; at budget G = 2,215,000 the bytecode completes *successfully* but
the cap forwards only 16,518 — flag 0, callee storage untouched — while the
gasless IR has flag 1 and storage written; at G = 10,000,000 observables
agree exactly. The `∃ G₀, ∀ G ≥ G₀` form is not a stylistic choice; it is
forced. For the **call-free** fragment
the conditional form *is* true and admits a ledger-free proof by vacuity
propagation (each gas check either passes or makes the result `OutOfGass`,
contradicting the hypothesis) — zero arithmetic.

## 3. Rough edges — the honest list

1. **The metered semantics still exists** (`Metered.lean`). Eduardo's
   critique stands and is conceded: it is not *necessary* (the cut is
   eliminable — vacuity propagation everywhere plus local cap arithmetic at
   call sites would do), it exists because v1's 1700 lines are stated against
   it and reuse beat rewriting. It is quarantined — it appears in zero
   exported statements — but it is real duplication: a second, gas-decorated
   copy of the semantics. A greenfield rebuild should use the leaner
   architecture (see §2's call-free finding, generalized).
2. **Fuel is still in the spec and the statements.** `Exec` carries fuel,
   consumed one unit per *lowered* opcode — a lockstep artifact that ties the
   spec to this particular lowering (Eduardo's circularity objection,
   conceded). It cannot be dropped outright — `EVM.call`'s callee execution
   is fuel-bounded — but it should be ∃-quantified away in exported
   statements. That needs a fuel-monotonicity theorem about EVMYulLean's
   whole interpreter stack (`Θ`/`Ξ`/`X`): real, unstarted work.
3. **The lockstep simulation is disposable by design.** Chunk-by-chunk
   `injectFrame` lemmas, the metered cost schedule, fuel-per-opcode: all
   break the moment the lowering optimizes. The exported statements mention
   none of them and survive; the internals would be rebuilt per lowering.
   Acceptable for a study; must be said out loud.
4. **The full-tank device.** The gasless `callStep` forwards
   `min(g, ⌊63/64·(2²⁵⁶−1−Cextra)⌋)` — i.e. exactly `g` for every sane gas
   argument, but not *literally* `g` for `g` within ~1.6% of 2²⁵⁶. The
   alternative (invoking `Θ` directly with `g`) would duplicate `EVM.call`'s
   body in the spec; the full tank was judged the smaller wart. For such
   pathological `g` (and for runs whose memory-expansion costs exceed 2²⁵⁶),
   the `∃ G₀` theorems hold **vacuously** (no representable budget
   qualifies) — honest but worth knowing.
5. **`G₀` is existential, not exported as a function.** A computable witness
   exists (the metered run *is* the cost oracle) but no `requiredGas :
   Program → Exec → Nat` is exported. Easy follow-up if consumers want it.
6. **Success-path only.** `lowering_correct`/`lowering_observables` cover
   `Gasless.run = .ok`. If the gasless run errors (`StaticModeViolation`,
   fuel exhaustion, callee `OutOfFuel`), the exported gasless theorems say
   nothing — though `lowering_exact` still gives exact error agreement
   against the metered semantics at every gas level.
7. **Cosmetics.** Right-to-left operand evaluation is kept only to make the
   erasure a step-for-step match (it is semantically unobservable now);
   `EVMLemmas.lean` still carries harmless `unusedSimpArgs` lint noise;
   `injectFrame` still appears in the strong-form statement (pinning the
   final frame) — only the observables form is fully frame-free.

## 4. Verdict

Did it come out as hoped? **Mostly yes at the statement level**: the spec a
reader sees (`IR.lean`) is gasless and oracle-free with real callee
execution, and the exported observables theorem has no frame fields, no gas
and no oracle in it — that is exactly what was asked. **No at the
architecture level**, in an instructive way: the proof still routes through a
gas ledger and a lockstep simulation, and the IR being a bijective
re-notation of bytecode means most of the proof effort buys no abstraction.
That observation, plus the findings above, motivated the decision recorded in
[`bytecode-first-plan.md`](../../../docs/bytecode-first-plan.md): retire the
toy IR, invest in a reusable reasoning layer over the (vendored, EVM-only)
bytecode semantics with theorem boundaries at the message-call level, and
make Plank SIR the first IR with a genuine abstraction gap.

## 5. File inventory (v2 delta)

| File | Lines | Role |
|---|---|---|
| `IR.lean` | rewritten | **The spec**: shared syntax/state + `Gasless` semantics |
| `Metered.lean` | new (moved from v1 `IR.lean`) | Internal gas ledger; `evmCallOracle` |
| `CallSound.lean` | 89 | `EVM.call` frame insensitivity; `lowering_exact` |
| `GasErasure.lean` | 860 | `run_erasure` (∃G₀ refinement; cap analysis at calls) |
| `Correctness.lean` | ~110 | `load`, `lowering_correct`, `Observables`, `observe`, `lowering_observables` |
| `Validation.lean` | 328 | Build-enforced `#eval` evidence (22 checks): call-free observables agreement (gasLeft 7,804,252 at G = 10M, matching v1's recorded figure; exact threshold G₀ = 2,195,748 located); the executable CALL counterexample (§2); metered = `EVM.X` on the nose even in the divergent regime |
| `Bytecode/EVMLemmas/Preservation.lean` | unchanged | v1 artifact, reused |
