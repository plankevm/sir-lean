# Experiment 001 Handoff

## Status: v2 complete — gasless spec, reflexive calls, observables export

```bash
cd experiments/001_toy_external_call
lake build                                            # green
rg -n "\bsorry\b|\badmit\b|^axiom" ToyExternalCall    # empty
```

All exported theorems depend only on `propext, Classical.choice, Quot.sound`.

**Read in this order:**

1. [`results-v2.md`](./results-v2.md) — what was achieved, the honest
   rough-edge list, and the verdict.
2. [`../../../docs/bytecode-first-plan.md`](../../../docs/bytecode-first-plan.md)
   — the discussion record and agreed next direction (retire this toy IR,
   vendor EVMYulLean EVM-only, build a bytecode reasoning layer, go straight
   to Plank SIR). **This experiment is closed; new work starts there.**
3. [`findings.md`](./findings.md) — proof-engineering patterns and dead ends
   (still fully applicable; the v2 proofs reused them throughout).
4. [`spec.md`](./spec.md) — explains the *v1* (metered) statement in depth;
   still accurate for `Metered.lean`/`Preservation.lean`, but note the spec
   is now the gasless semantics in `IR.lean` and the exported statements live
   in `Correctness.lean`.

## The exported theorems (`Correctness.lean`)

```lean
theorem lowering_correct  : Gasless.run program s = .ok s' →
  ∃ G₀, ∀ G, G₀ ≤ G → G < UInt256.size → ∃ gFin,
    EVM.X s.fuel vj (load program s G) =
      .ok (.success (injectFrame ((s'.withGas gFin).evm) lastPc [] code) .empty)

theorem lowering_observables : Gasless.run program s = .ok s' →
  ∃ G₀, ∀ G, G₀ ≤ G → G < UInt256.size →
    observe (EVM.X s.fuel vj (load program s G)) = some s'.observables
```

No oracle, no gas model in the IR, no frame fields in the observables form.
Only hypothesis besides the gasless run: `hsize` (lowered code addressable by
a 256-bit pc). Under-funded runs are deliberately unconstrained — the freedom
a gas-optimizing lowering needs. Companion exact theorem (`CallSound.lean`):
`lowering_exact` — bytecode = metered run on the nose at *every* gas/fuel
level, errors included, assumption-free.

## File map

| File | Contents |
|---|---|
| `IR.lean` | **The spec**: syntax, `Exec`, `injectFrame`, gasless semantics (`Gasless.*`) — no gas, no oracle; calls run real callee bytecode via `EVM.call` on a full tank |
| `Metered.lean` | Internal gas ledger (v1 semantics); `evmCallOracle` |
| `Bytecode.lean` | Opcode alphabet, list-first byte encoding, `lower` (unchanged from v1) |
| `EVMLemmas.lean` | Reusable lemma layer over `EVM.X` (unchanged from v1) |
| `Preservation.lean` | v1 chunk lemmas + metered `lowering_correct` (unchanged) |
| `CallSound.lean` | `EVM.call` frame insensitivity; assumption-free `lowering_exact` |
| `GasErasure.lean` | `run_erasure`: ∃G₀ gas refinement (cap analysis at calls) |
| `Correctness.lean` | `load`, `Observables`, `observe`, the two exported theorems |
| `Validation.lean` | `#eval` non-vacuity evidence on concrete programs |

## Key facts the next layer must not relearn

* **`CALL` consults gas** (63/64 forwarding cap; callee OOG → flag 0, caller
  continues). `result ≠ OutOfGass → result = IR run` is FALSE with calls;
  `∃ G₀, ∀ G ≥ G₀` is forced. Call-free fragments admit the conditional form
  with a ledger-free vacuity-propagation proof.
* **`EVM.call` is frame-insensitive** — proved cheaply (`CallSound.lean`,
  defeq bridging). Reflexive call modeling (IR call = `EVM.call` itself) is
  what made it cheap.
* **Fuel debt**: removing fuel from exported statements needs
  fuel-monotonicity of EVMYulLean's `Θ`/`Ξ`/`X` (callee `OutOfFuel` is a hard
  error, so monotonicity is the right shape). Unstarted.
* The lockstep internals (metered schedule, fuel-per-lowered-opcode, chunked
  `injectFrame` simulation) are tied to this bijective lowering and are
  disposable; the exported statement shape is the stable contract.

## Fork (forks/EVMYulLean)

Unchanged this round (v2 needed **zero** fork modifications). Standing
intentional divergences: exposed `EVM.W/Z/H`, list-based
`ByteArray.get?`/`extract'`, pure `ByteArray.zeroes` (enables `#eval`),
round-trip lemmas. Keep them; vendoring is the next step (see
bytecode-first-plan §4).
