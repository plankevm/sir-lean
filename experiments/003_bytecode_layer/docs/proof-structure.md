# The proof structure experiment 003 must follow

This is the **constitution** for how experiment 003 proves things. It is the
architecture that *emerged as correct* from experiment 001 — which is **not** the
architecture 001 shipped under the "done" label. The orchestration loop
([`../orchestration.prose`](../orchestration.prose)) enforces it; the prover and
the per-aspect verifiers are derived from it.

Seed crystal to read first:
[`001/ToyExternalCall/CallSound.lean`](../../001_toy_external_call/ToyExternalCall/CallSound.lean)
— ~30 lines that embody the whole structure. Background:
[001 `findings.md`](../../001_toy_external_call/docs/findings.md),
[001 `results-v2.md` §3](../../001_toy_external_call/docs/results-v2.md),
[`planning/bytecode-first-plan.md` §2–4](../../../docs/planning/bytecode-first-plan.md).

## Prime directive: proof-first, always-green

A `sorry`-ed abstraction proves nothing and *validates* nothing. The whole point
of using Lean is that **only a closed proof reveals which abstraction is actually
necessary.** Therefore:

- **No `sorry` ever lands.** The package is always green and axiom-clean. Every
  step ends with a whole-package `lake build` green, **zero `sorry` anywhere**,
  and `#print axioms` standard on the new theorem.
- **Abstractions are demand-driven**, never scaffolded. A definition or lemma is
  added only when it is *immediately proved* or *immediately required by a proof
  in progress*. Do not lay out a skeleton of stated-but-unproved theorems.
- **Bottom-up.** Start from the smallest theorem you can fully close about a
  concrete handwritten program at the messageCall boundary, then grow toward the
  goal (external calls) one proven step at a time. When a concrete proof would
  repeat work, *that* is when you extract a reusable lemma — and you prove it.
- **A wall is a finding, not a `sorry`.** If a step cannot be closed honestly,
  revert it and report the obstruction. An obstruction is information about what
  is genuinely hard; a `sorry` is slop that hides it.

This supersedes any top-down "state all the bricks, then fill them in" reading of
the lemma DAG below — the DAG is the *expected* shape, to be discovered and
validated by proofs, not asserted up front.

## Two architectures coexisted in 001

**What 001 shipped ("done").** A *bijective, mirror-the-machine* lowering: the IR
embeds `EVM.State`, tracks `execLength`/fuel faithfully, the coupling is literal
record equality modulo three frame fields with `injectFrame` pinning them. Proved
by a **lockstep per-opcode chunk simulation** against `EVM.X`, with a **second
gas-decorated copy of the semantics** (the metered ledger), an **oracle
hypothesis** for calls, fuel one-per-lowered-opcode, and a gas schedule *defined*
as the cost of its own lowering. Green and axiom-clean — but a re-notation of
bytecode (no abstraction), the ledger is **cut-eliminable**, and fuel +
`injectFrame` + the lockstep internals leak into statements or are disposable.
**Do not reproduce this.**

**What emerged as correct** (conceded in the docs; actually *realized* only in
`CallSound.lean`):

1. **One high-level spec, no shadow ledger.** The metered copy existed only
   because v1's lemmas were stated against it; the cut eliminates. The gas story
   is carried structurally over the single semantics.
2. **Reflexive effects → soundness by defeq/characterization.** Model an
   effectful operation as the *real* target operation, so both sides are
   definitionally the same computation and soundness is a short characterization
   proof. `CallSound`: `if_congr Iff.rfl`, `bind_map_comm` applied by `exact`
   (defeq bridges the scrutinees), structure eta for the merged state — *"no
   record-commutation simp lemmas are needed."* The v1 oracle hypothesis became a
   theorem. **No oracles, no parallel metered simulation, no record-commutation
   simp.**
3. **Structural gas, localized arithmetic.** Away from calls, gas is
   **vacuity-propagation**: at each check it either passes or the whole run is
   `OutOfGas`, contradicting success — *zero arithmetic*. The quantitative content
   (`∃G₀`, the 63/64 cap) lives **only at call sites**.
4. **Observables at the message-call boundary; mid-frame coupling is
   proof-internal.** `injectFrame` exists only because v1 stated correctness
   mid-frame against `EVM.X`. At the message-call boundary the coupling relations
   are rule premises/conclusions — internal — and never appear in exports.
5. **Spec/proof separation + characterization discipline.** Exported statements
   reach a small, human-readable surface; proofs route *through characterization
   lemmas*, never unfolding the spec, so the spec can be reshaped without breaking
   the corpus. (Same rule 002 enforces in its `AGENTS.md`.)
6. **Fuel discharged once; lockstep internals never exported** — so a statement
   survives an optimizing lowering. In leanevm, fuel is seeded from gas internally
   (`seedFuel`), so this is a single fuel-sufficiency lemma.

**One sentence:** a single high-level spec; correctness proved through
characterization lemmas about the target's real operations (modeled reflexively);
gas by vacuity-propagation everywhere except local `∃G₀`/cap arithmetic at CALL;
everything exported in observables at the message-call boundary, with fuel and
lowering-lockstep detail discharged once and kept out of every statement.

## Durable proof-engineering (orthogonal to architecture)

Carry over from [001 `findings.md`](../../001_toy_external_call/docs/findings.md)
regardless of architecture: standalone equation/characterization lemmas; **defeq
bridging** (`exact`/`show`/componentwise hypotheses) instead of simp
record-commutation; **guard alignment** via `if_pos`/`if_neg` not `simp`;
list-first byte encodings; iota-reduce (`dsimp only`) before `rw`;
position-generalized (`*_at`) lemmas. Avoid the documented dead-ends
(record-update commutation as simp lemmas; `set` for abbreviating cost/state
terms).

## The internal/exported distinction (load-bearing)

The cleanliness requirements apply to **exported statements only** — the
capstones, the public face of the CALL rule, the observables projection.
**Internal bricks are *allowed* to be low-level**: the run vocabulary, the
sequencing/chunk lemmas, the mid-frame coupling relations are proof-internal and
*should* mention pc/stack/frames. Policing cleanliness on every lemma is both
wasteful and wrong — it would reject the machinery we want internally.

## Requirements and where the loop enforces them

The loop replaces blanket adversarial review with **one targeted verifier per
requirement, fired only where that requirement is at risk**. Several are
deterministic checks the prover already produces, not agents.

| # | Requirement | Kind | Enforced at |
|---|---|---|---|
| 1 | Green `lake build`, zero `sorry`, `#print axioms` standard | **deterministic** (loop condition reads prover output) | every brick — no agent |
| 2 | **Export cleanliness**: exported statements are observables at the messageCall boundary, frame-free (no `injectFrame`), fuel-free, no lockstep internals, high-level | verifier `export-shape` | design skeleton, each capstone, final |
| 3 | **Reflexive calls**: CALL is a real `messageCall` on the child — no oracle/assumption; soundness by characterization | verifier `reflexive-call` | C′ (CALL rule), call capstone |
| 4 | **Gas honesty**: `∃G₀` where forced (counterexample exhibited), vacuity-propagation away from calls, non-vacuous | verifier `gas-honesty` | C′, call capstone |
| 5 | **Characterization discipline / single semantics**: no shadow ledger; proofs route through characterization lemmas; proof-internal defs never appear in exports | prover standing instruction **+** one integration review | prover always; reviewed once at integration |

This collapses ~27 generic-skeptic calls into ~4 sharp verifiers at ~5
checkpoints plus a free deterministic gate everywhere. Requirement 5 is both a
standing prover instruction (a coding standard, applied continuously) and a
single integration-time `characterization` review — not a per-brick gate.
