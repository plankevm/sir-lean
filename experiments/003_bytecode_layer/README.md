# Experiment 003 — bytecode reasoning-layer machinery (external calls)

> **Status: M1 and M2 proven (green, zero `sorry`, axiom-clean).** The call-free
> spine *and* external calls are proved in the target shape — observables-only,
> frame-free, fuel-free — against the real `messageCall`. Every exported theorem's
> `#print axioms` is **exactly** `[propext, Classical.choice, Quot.sound]`. Full
> detail: [`docs/results.md`](./docs/results.md) and
> [`docs/handoff.md`](./docs/handoff.md).
>
> - **M1:** `messageCall_stop_observe`, `messageCall_pushStop_observe`,
>   `messageCall_sstore_storageAt`, `messageCall_seq_storageAt`.
> - **M2 (the headline — external calls):** `messageCall_call_storageAt` (the
>   `∃G₀` storage-observable theorem; the child `CALL` is the **real reflexive**
>   `beginCall`/`drive` on the child params) and `call_counterexample` (executable
>   `∃G₀` witness: at `g = 24000` the 63/64 cap starves the callee, its `SSTORE`
>   rolls back, the cell reads `0` while the caller completes). The reflexivity
>   witness `messageCall_child_reflexive` now lives in the proof layer as
>   `Proof.messageCall_child_reflexive` (its statement names the internal caller
>   frame, so it is not on the frame-free audit surface).
> - **Both foundation obstructions the earlier run found (the `bv_decide` axiom
>   inherited by `messageCall`; `private callArm`/`createArm`) were resolved
>   upstream in leanevm** by one endorsed commit (`9cefe5b`), conformance unchanged
>   (2859/2859). That is what makes the whole experiment axiom-clean — see
>   `docs/results.md §3`.
>
> `lake build` → green (1120 jobs). No
> `sorry`/`admit`/`native_decide`/`bv_decide` in experiment code.

## Layout — where to read (core vs examples vs proofs)

The package is split so the specification is readable on its own; proof internals
are quarantined. **Read `Spec.lean` first.**

```
BytecodeLayer/
  Spec.lean         THE AUDIT SURFACE — every exported theorem (statement +
                    docstring); each delegates its proof to Proof/.
  Programs.lean     the example bytecode contracts and messageCall params.
  Observables.lean  the observable projections results are stated through.
  Reasoning/        reusable bricks (the engine): Step, the reflexive CALL rule
                    (Call), the drive vocabulary (Drive/DriveGen), and the
                    messageCall/beginCall entry characterizations (Drive/Begin).
  Hoare/            reusable interpreter proof theory: frame walks, descent and
                    drive monotonicity, clean halts, memory algebra, and charge/run
                    composition used by the IR-lowering proof.
  Proof/            proof internals (scaffolding frames, decode lemmas, the long
                    reductions): CallFree, Sequence, ExternalCall, ExternalCallGen
                    (the black-box call rule), Straightline + StraightlineInstances.
```

The proof layer never unfolds the semantics (`messageCall`/`beginCall`/`stepFrame`/
`drive`) directly: every proof routes through a `Reasoning/` characterization
lemma (`messageCall_eq_drive`, `beginCall_code`, the `stepFrame_*`/`drive*`
equations, the `stepFrame_call` rule), so the spec defs can be reshaped without
breaking the proof corpus.

## What this experiment is

The first **reasoning layer** over the bytecode semantics
([`docs/planning/bytecode-first-plan.md`](../../docs/planning/bytecode-first-plan.md)
§4.2). No source IR yet, no abstraction gap: we build and prove the *reusable
bricks* against handwritten bytecode, and show they compose into the export shape
we actually want. **External calls are the headline target** — they are where
001's findings live, where vyper-hol cheats, and where Verity doesn't even
execute.

This is **001's theorem, finally stated in the shape we wanted** — which
`leanevm` makes reachable:

| 001 (against `EVM.X`) | 003 (against `messageCall`) |
|---|---|
| mid-frame; `injectFrame` pins the final frame | **messageCall boundary; `CallResult` observables, no frame** |
| `fuel` in `Exec` and in the statement | **fuel discharged once (fuel-sufficiency); absent from statements** |
| metered gas-ledger copy of the semantics | **no ledger; lean architecture (vacuity propagation + local cap arithmetic at CALL)** |
| `X` is a fueled function | leanevm is already `stepFrame` + `drive` |
| ∃G₀ gas story | **∃G₀ unchanged — intrinsic to CALL, carries over verbatim** |

### Why leanevm gives us the new shape for free

- **Frame-free boundary.** `messageCall : CallParams → Except _ CallResult` takes
  world+calldata+gas and returns observables (`success, output, accounts,
  substate, gasRemaining`). The frame is born inside `drive` (pc 0, empty stack,
  code from the account map) and dies at halt — so **`injectFrame` has no
  analogue here.** (`Evm/Semantics/Interpreter.lean`.)
- **Fuel is internal.** `messageCall` takes no fuel; it seeds it from gas
  (`seedFuel g = 2*g + 4096`). leanevm's own comment: *"fuel … cannot run out for
  gas-respecting executions; `.OutOfFuel` signals a broken gas table, not a
  program behavior."* We prove that **once** (fuel-sufficiency) and fuel never
  appears in a statement again.
- **Already a step relation.** `stepFrame : Frame → Signal` driven by the single
  `drive` trampoline — bytecode-first §6.3's "restate X as a step relation" is
  already done.

## The lemma DAG

| Brick | Statement (schematic) |
|---|---|
| **A** Observables | `CallResult.observe : CallResult → Observables` (success, output, per-account storage, logs) |
| **B** run vocabulary | `FrameStep`/`FrameRun` over `stepFrame` (fuel-free); extended to the `drive`-level `needsCall`/`Pending`/`resume` cycle for calls |
| **C** sequencing | run A then B = run `A ++ B` when A falls through into B (decode-at-offset / code-layout reasoning) |
| **C′** CALL rule | `beginCall`/descent/`resumeAfterCall`: 63/64 cap (`callGasCap`), callee-success→flag 1, callee-OOG→flag 0→**caller continues**; the call is a **real `messageCall`** on the child (reflexive — leanevm's analogue of 001's frame-insensitivity) |
| **D** fuel-sufficiency | `messageCall p ≠ .error .OutOfFuel` for gas-respecting `p`, **including** the descent/delivery accounting (≥100 gas/descent) calls need |
| **capstone** | `∃ G₀, ∀ g ≥ G₀, (messageCall {…, code, gas := g}).map CallResult.observe = .ok <computed>` — fuel-free, frame-free, observables-only |

`C` (stepFrame-level) and `D` (drive-level) are independent — they meet only at
the capstone, so they fan out in parallel.

## Two milestones

- **M1 — call-free spine.** A, B, C, D₀ (call-free fuel-sufficiency), capstone-1
  on a straight-line handwritten program. Locks in the new *shape* —
  observables-only, fuel-free, no `injectFrame` — before call complexity.
- **M2 — external calls (the goal).** B′ (descents), C′ (CALL rule), D
  (fuel-sufficiency with descents), capstone-2 on a **caller+callee** pair that
  reproduces 001's executable `∃G₀` counterexample: at a modest `g` the cap binds,
  the callee runs out, flag 0 is stored, the caller `STOP`s cleanly — observables
  different from the full-gas run, with no `OutOfGas` anywhere.

## The foundation: `leanevm`

Supersedes vendoring EVMYulLean ourselves: `philogy/leanevm` already *is* an
EVM-only, bytecode-only Lean 4 semantics (Cancun, conformance-validated,
Apache-2.0). It lives gitignored at `forks/leanevm` as a **working base we
modify** (toolchain `lean4 v4.30.0` + mathlib; package `«evm»`, `import Evm`;
interpreter `Evm/Semantics/Interpreter.lean`). Needed semantics changes get
**upstreamed** to `philogy/leanevm` (or our fork) — no silent in-tree divergences.

```sh
./scripts/fetch-forks.sh                          # clones forks/leanevm
cd forks/leanevm
git submodule update --init EthereumTests          # conformance fixtures
lake build && lake exe conform 8                    # build + fast conformance
```

## The orchestration program

The work was driven as deterministic control flow over subagents, in phases:

```
phase 0  foundation       leanevm builds + fast conformance            (green or stop)
phase 1  design (fan-out) ─┬ map leanevm's call/exec API (read-only)
                           ├ draft fuel-sufficiency statement + strategy
                           ├ draft run vocabulary + sequencing + CALL-rule
                           └ draft Observables + the two capstones
                          → synthesize a sorry-ed skeleton that BUILDS + design.md
                          → adversarial: is the export really frame/fuel-free & reflexive?
phase 2  M1 spine         A → B → (C ∥ D₀) → capstone-1
phase 3  M2 calls         B′ → (C′ ∥ D) → capstone-2     ← external calls
phase 4  integration      characterization review + completeness (loop to fix)
phase 5  write-up         results.md / handoff.md, rough edges first-class
phase 6  review report    grounded, spec-centric human digest -> docs/review-report.md
```

Phase 6 is the **`lean-review-report`** agent: a concise, human-facing review report
built from the exported spec statements quoted verbatim from source (specs over
proofs), which independently re-greps the code and flags any doc↔source discrepancy.
It can be re-run on demand and reused on other experiments by pointing it at the
target track's sources.

### How it proves — the placed-verifier model

The proof architecture experiment 003 must follow is fixed by
[`docs/proof-structure.md`](./docs/proof-structure.md) — the structure that
*emerged as correct* from 001 (single high-level spec; reflexive effects proved
by characterization/defeq, not oracle/simulation; gas by vacuity-propagation away
from calls with local `∃G₀`/cap arithmetic at CALL; exports in observables, fuel
and lockstep detail discharged once). The prover's standing instructions encode
it.

Verification is **placed, not blanket**. Every brick has a free **deterministic
gate** (green `lake build`, zero `sorry`, standard `#print axioms` — read from the
prover's own output, no agent). On top of that, a **targeted auditor fires only
where a requirement is at risk**, giving three prove-tiers:

| Tier | Used for | Gate |
|---|---|---|
| `prove` | internal bricks (A, B, C, B′, D) — *allowed* to be low-level | deterministic only |
| `prove_export` | capstone-1 | + **export-shape** auditor (observable / frame-free / fuel-free / clean) |
| `prove_call` | C′, capstone-2 | + **export-shape** + **reflexive-call** + **gas-honesty** auditors |

Plus a one-time **characterization** review at integration (single semantics;
proofs route through characterization lemmas; no proof-internal leak into
exports). This collapses ~27 generic-skeptic calls into ~4 sharp verifiers at ~5
checkpoints. Crucially, cleanliness is policed on **exported statements only** —
internal bricks are meant to be low-level.
