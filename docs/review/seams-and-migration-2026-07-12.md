# exp005 Seams & Experiments→Canonical Migration Review — 2026-07-12

Author: review fleet synthesis. Scope: (1) is the exp005 flagship genuinely closed and what does it rest on;
(2) classification and adversarial scrutiny of every remaining seam; (3) a concrete migration plan hoisting the
vendored EVM to a top-level `EVM` package, extracting the exp005 lowering machinery, and reconciling exp002's SIR
with PR #2's canonical `sir/`; (4) open questions for the lead.

All file:line references are clickable and point at the canonical worktree at HEAD `c2228482`.

---

## 1. Executive summary

**The exp005 flagship is genuinely closed — but only after a clean rebuild, and only as a conditional theorem over
an honestly-disclosed seam bundle.** The headline
[`lower_conforms_exact`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L275)
(with [`lower_conforms`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L224) and
[`lower_conforms_gasfree`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L310))
is **green, zero literal `sorry` across the whole `LirLean` package, and axiom-clean `[propext, Classical.choice, Quot.sound]`**
after a fresh `lake build WIP` — both cones build (default `LirLean` 1177 jobs, WIP 1184 jobs). The old vacuity disease
(supplied `StmtTies`/`TermTies`, single-call restriction, `SelfPresent` as an oracle) is **cured**: the ties are now
*derived* from the recorded run, calls are consumed positionally over the whole `log.calls` list, and `SelfPresent` is
derived from a decidable entry fact. What the theorem still rests on is a small, disclosed residual: **(a)** the trusted
EVM model (vendored `EVMLean` + exp003 `BytecodeLayer`, carrying a *non-upstreamed* CREATE-totality patch chain), and
**(b)** three runtime seams bundled in `PrecompileAssumptions` (`noErase`, `callsCode`, `createResolves`) plus the
`RunLog.clean` scope premise. For a call-free & create-free program all three `PrecompileAssumptions` fields go vacuous,
collapsing the residual to just `RunLog.clean` + the trusted base. The conclusion is observables-only (world-equality +
result-equality per [`Spec/Conformance.lean:20`](../../experiments/005_ir_lowering/LirLean/Spec/Conformance.lean#L20)).

**Two verification caveats the lead must know.** First, a **stale-olean incident**: the first axiom check reported
`sorryAx` reaching the flagship via `simStmt_coupled_create` (the CREATE arm of the coupled walk); the checked-in oleans
predated the recent CREATE commits at HEAD. A rebuild made it vanish. **Anyone re-verifying MUST `lake build WIP` first
— do not trust cached oleans.** Second, **the in-tree docs are stale in three places** and understate the result:
[`lakefile.lean:28`](../../experiments/005_ir_lowering/lakefile.lean#L28) and
[`RealisabilitySpec.lean:16`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L16) still
say "sorry-carrying BY DESIGN"; and `Machinery.lean:4546` still says three CREATE lemmas "remain STUBBED with tracked
sorrys" — all now closed and axiom-clean. These should be corrected.

---

## 2. Remaining hypotheses / seams

### 2.1 Classification table

| Seam | Location | Class | Vacuous when |
|---|---|---|---|
| `PrecompileAssumptions.callsCode` | [`Spec/Seams.lean:33`](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L33); pred [`Engine/Modellable.lean:410`](../../experiments/005_ir_lowering/LirLean/Engine/Modellable.lean#L410) | **irreducible-oracle** (watch) | call-free |
| `PrecompileAssumptions.noErase` | [`Spec/Seams.lean:32`](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L32); pred `PrecompilesPreservePresence` [`Spec/Seams.lean:11`](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L11) | **irreducible-oracle label is STALE → now DISCHARGED** (benign) | call-free / non-precompile |
| `PrecompileAssumptions.createResolves` | [`Spec/Seams.lean:34`](../../experiments/005_ir_lowering/LirLean/Spec/Seams.lean#L34); pred [`Engine/Modellable.lean:421`](../../experiments/005_ir_lowering/LirLean/Engine/Modellable.lean#L421) | **irreducible-oracle** (watch) | create-free |
| `RunLog.clean` (CleanHalt / non-exception scope) | [`Spec/Conformance.lean:15`](../../experiments/005_ir_lowering/LirLean/Spec/Conformance.lean#L15); premise [`RealisabilitySpec.lean:285`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L285) | **irreducible-oracle** (benign, decidable per run) | never (always in scope, but decidable) |
| Trusted EVM base + non-upstreamed CREATE patch chain | [`EVMLean/Evm/Semantics/Create.lean:64`](../../experiments/003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L64) | **irreducible-oracle** (watch; provenance not logic) | never |
| `hself` — entry self-account presence (**was** `SelfPresent` oracle) | premise [`RealisabilitySpec.lean:279`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L279); derivation `Producer.lean:273-274` | **dischargeable** (decidable entry fact) | — |
| `IRWellFormed` bundle | [`Spec/WellFormed.lean:517`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L517); premise `RealisabilitySpec.lean:281` | **dischargeable** (decidable over prog text) | — |
| `codeFits` / `stackFits` | [`Spec/WellFormed.lean:449`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L449), [`:482`](../../experiments/005_ir_lowering/LirLean/Spec/WellFormed.lean#L482) | **dischargeable** (decidable Nat bounds) | — |
| `hcode` / `hmod` / `hgas` / `hrun` (definitional pins + run premise) | [`RealisabilitySpec.lean:277-284`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L277) | **dischargeable** (mechanical / it IS the recorder input) | — |

**Bottom line on classification:** eight of the nine listed seams are either mechanical/decidable ("chill") or already
discharged. The residual oracle surface that genuinely needs scrutiny is **four items**: `callsCode`, `createResolves`,
`RunLog.clean`, and the trusted EVM base. **None of the four is a real soundness gap under adversarial scrutiny** — all
are honest external oracles or decidable-per-program side conditions. The one previously-feared "TRUE oracle" (`noErase`)
has been *proven* and is no longer irreducible.

### 2.2 Adversarial scrutiny of the irreducible-oracle seams

For each: is it a real soundness gap or an honest external oracle? Severity, and what discharging requires.

#### `callsCode` — honest external oracle, **NOT a soundness gap**, severity **watch**

Statement: every `Runs`-reachable frame issuing a `.needsCall` targets a code account, never a precompile 1..10.

Verdict: **honest, load-bearing, non-vacuous.** It does real work — consumed via `beginCall_isCode_of_codeSource_ne_precompiled`
([`Modellable.lean:367`](../../experiments/005_ir_lowering/LirLean/Engine/Modellable.lean#L367)) as a genuine case-split
that rules out `beginCall`'s precompile `.inr` arm so the coupled walk descends into the CALL child. It is **discharged,
not merely assumed**, by a sound executable checker `callsCodeOk`
([`WitnessParams.lean:355`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/WitnessParams.lean#L355)) with proven
soundness. The flagship is instantiated on a program that actually CALLs (exProg block 0 calls `0x100`, an ordinary code
account — [`Witness.lean:47`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/Witness.lean#L47)), and
`exProg_nonvacuity` ([`RealisabilitySpec.lean:774`](../../experiments/005_ir_lowering/LirLean/V2/Realisability/RealisabilitySpec.lean#L774))
closes it by kernel computation, `#guard_msgs`-pinned to `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no
`ofReduceBool`, no `native_decide`). Excluding precompile-targeted CALLs is proper scoping — precompiles have opaque/stubbed
semantics in this engine, so such a CALL lands in un-modelled territory.

The docstring discloses the residual honestly:

```lean
-- the honest residual — a runtime fact about the program's reachable call targets,
-- NOT structurally guaranteed by the lowering (an IR Stmt.call whose callee
-- materialises a precompile address 1..10 would violate it)
```

What discharging requires: it **cannot be eliminated unconditionally** — an adversarial `lower prog` can `Stmt.call` a
callee whose runtime-materialised address is 1..10 (target popped off the stack). To narrow: (1) faithfully model the ten
precompile semantics (large engine addition), or (2) add a verified static IR analysis that every `Stmt.call` callee
materialises outside 1..10 (feasible only for compile-time-constant callees). For fully-dynamic addresses neither is
possible; the per-program `callsCodeOk` checker is the correct and complete discharge — it turns the seam into a decidable,
kernel-certified obligation per concrete program.

#### `createResolves` — honest external oracle, **NOT a soundness gap**, severity **watch**

Statement: every `Runs`-reachable `.needsCreate` whose init child terminates `.ok` resumes successfully — the 63/64
gas-retention guard does not throw `.OutOfGas` on a `UInt64` overflow.

Verdict: **honest side condition, cannot silently drop faulting executions.** The recorded log (via `driveLog`/`drive`)
is *independent* of the seam: a real CREATE OOG-fault is faithfully recorded as an exception-halted run (the `.create`
pending that returns `.error` folds into an exception halt, `DriveRuns.lean:207-211`), not lost. The seam is consumed only
on the proof side to build a `Runs.create` correspondence; if the guard actually fired at a reachable frame the seam would
be *false* and the theorem simply would not apply — it would not certify a wrong result. CREATE is genuinely modelled via
`Runs.create` (`Hoare.lean:140-154`), replacing the retired `NotCreate` exclusion. The guard is the real EVM 63/64 rule,
which passes unless the `UInt64` sum overflows.

What discharging requires: a `UInt64` no-overflow lemma showing `(gas + gasRemaining).toNat` does not wrap for gas values
reachable in `lower prog` (child retained gas is a fraction of `gas`, so `gas + gasRemaining ≤ 2·gas`; combined with a
reachable-gas bound `gas < 2^63` the sum is overflow-free and the guard structurally passes). That would let `createResolves`
be *proved* rather than assumed. Absent that arithmetic envelope it stays a supplied side condition, but per-program it is
already dischargeable by the executable trace checker. **Note:** currently only the vacuous create-free `exProg` witness
exists — a concrete witness with a reachable CREATE would demonstrate non-vacuous discharge and is worth building.

#### `RunLog.clean` — honest domain restriction, **NOT a soundness gap**, severity **benign**

Statement: the recorded terminal is a clean halt (for a `.call` observable, `success=true` OR `gasRemaining≠0`; a
top-level `.create` observable is out of scope). Excludes `OutOfGas`/the 8 `ExecutionException` variants, and
conservatively excludes genuine zero-gas reverts.

Verdict: **sound by construction, correct direction.** `endCall` maps the three `FrameHalt` constructors to distinguishable
log fingerprints; `RunLog.clean` demands `success=true ∨ gasRemaining≠0`, excluding exactly `.exception` on the log.
`haltNonException_of_cleanLog` (`Machinery.lean:269-311`) uses `hclean` **only** to close the exception arm by genuine
contradiction — it asserts nothing about external world values. If `hclean` is false the theorem is silent, never unsound.
The zero-gas-revert cut is a conservative *under*-approximation of scope: it only shrinks the covered domain, it cannot admit
a false conclusion. It is non-vacuous (`exProg_nonvacuity` exhibits a nontrivial program where it and every other premise
hold, discharged by an in-kernel recorder evaluation, `#guard_msgs`-pinned, no `sorryAx`), and it is **decidable on the
concrete run** via the `cleanb` Bool twin. It is not derivable from program text (a program can halt exceptionally on some
inputs), which is exactly why it is a *run* premise. This matches prior art — no verified EVM fork (vyper-hol/Verity)
models gas-introspection/OOG at the semantic level either.

What narrowing requires (neither needed for soundness): **(a)** recover the zero-gas-revert corner by enriching
`RunLog.observable` to record the raw `FrameHalt` tag (a "reverted" bit) so a top-level REVERT is distinguishable from an
`.exception`, then re-prove `haltNonException_of_cleanLog`'s exception arm against the richer fingerprint; **(b)** eliminate
the premise entirely would require a gas-costed IR semantics so an OOG/exception top-level run maps to a definable IR
outcome — this contradicts the deliberate gas-agnostic design and is correctly left as a disclosed boundary.

#### Trusted EVM base + non-upstreamed CREATE patch chain — **NOT a soundness gap** (provenance caveat only), severity **watch**

Two things are bundled: **(1)** the whole leanevm+003 model is the axiomatic definition of the EVM — a legitimately-external
oracle at the correct abstraction boundary; every conformance theorem is conditional on a reference model, and this one is
independently validated against the Ethereum BlockchainTests fixtures via `lake exe conform` (~22k tests). It does not make
the flagship vacuous — the conclusion is a nontrivial equivalence between the IR lowering and this model's `Runs`/`stepFrame`/`observe`.

**(2)** The sharper claim that a local patch makes `beginCreate` TOTAL and thereby *hides a fault* does **not** hold up.
`beginCreate` now returns `Frame` (confirmed at [`Create.lean:64`](../../experiments/003_bytecode_layer/EVMLean/Evm/Semantics/Create.lean#L64)):

```lean
def beginCreate (params : CreateParams) : Frame :=
```

But the removed `.error` arm was **not** a yellow-paper soft-failure — it was an artifact of RLP's `Option`-typed encoder
modeling a length ceiling that provably never fires on CREATE inputs (20-byte address + ≤8-byte nonce). That deadness is
*proved* by `contractAddressBytes_create_isSome` (`Create.lean:38`), grounded in real size lemmas, all axiom-guarded to
`{propext, Classical.choice, Quot.sound}`. The change is byte-identical on the executable path. The *net* direction of the
patch chain is toward **more** faithfulness (commit `7ecbee7` fixed an unfaithful `accounts := ∅` caller-world-wipe into a
soft-failure checkpoint before `ad67864` proved the arm dead). CREATE is genuinely modelled via `Runs.create`; the residual
`createResolves` is the honest, satisfiable side condition scrutinized above.

The one **real** residual is provenance, not logic: conformance is pinned to a *patched, un-upstreamed* leanevm (merge
`be6e742`, commits `7ecbee7`/`7b34698`/`ad67864`), so bit-for-bit the trust root differs from stock upstream until the
patches merge. What discharging requires: upstream the three commits (or obtain maintainer confirmation) so the vendored
subtree equals upstream, and run `lake exe conform --full` green on the patched `EVMLean` to re-confirm the ~22k
BlockchainTests still pass (the `ad67864` message notes the rust `evmrs` helper could not build in that environment, so this
validation was deferred to pre-merge). Cross-validating leanevm against a second executed EVM spec (KEVM / Verifereum) is a
research-scale nice-to-have, not required.

### 2.3 Which seams do we have NO real way to discharge?

- **Unconditionally impossible:** `callsCode` for **fully-dynamic callee addresses** (target popped off the stack) — no
  static analysis can force it; only per-program kernel-checked discharge or a full precompile model.
- **Requires a research-scale change:** eliminating `RunLog.clean` entirely (needs a gas-costed IR semantics, which the
  project deliberately rejects) and cross-validating the trusted EVM base against a second spec.
- **Requires an arithmetic envelope we don't have yet:** proving `createResolves` (the `UInt64` no-overflow lemma).
- **Requires an external action (not a proof):** upstreaming the CREATE patch chain to align the trust root bit-for-bit.

Everything else is decidable/mechanical per program and already has (or trivially admits) a checker.

---

## 3. Migration plan: experiments → canonical dirs

### 3.a Hoist vendored EVM `experiments/003_bytecode_layer/EVMLean` → top-level `EVM`

The vendored library is a plain in-tree Lake path package named `«evm»`
([`EVMLean/lakefile.lean:7`](../../experiments/003_bytecode_layer/EVMLean/lakefile.lean#L7)) exposing `lean_lib «Evm»` with
module root `Evm` (a squashed subtree of philogy/leanevm @ `9cefe5b`, Cancun, on `v4.30.0`). It is **not** a top-level git
submodule, so `git mv` moves it cleanly. Keep the package name `«evm»` and the `Evm` module root **unchanged** so all
**24** `import Evm` consumers (11 in exp003 BytecodeLayer, 13 in exp005 LirLean) need **zero source edits** — none reach
into `Evm.` submodules by import path.

Steps:

1. `git mv experiments/003_bytecode_layer/EVMLean EVM` (top-level).
2. [`experiments/003_bytecode_layer/lakefile.lean:7`](../../experiments/003_bytecode_layer/lakefile.lean#L7):
   `require evm from "EVMLean"` → `require evm from "../../EVM"`.
3. `experiments/003_bytecode_layer/lake-manifest.json`: the `evm` path entry `dir` `"EVMLean"` → `"../../EVM"`.
4. `experiments/005_ir_lowering/lake-manifest.json`: the **inherited** `evm` path entry `dir`
   `"../003_bytecode_layer/EVMLean"` → `"../../EVM"` (005 reaches `evm` transitively, so its manifest hardcodes the dir).
5. When PR #2's `sir/` lands, its manifest's inherited `evm` dir points at `../EVM` similarly.
6. Easiest correct path for the manifests: after editing the lakefiles, run `lake update evm` (or `lake update`) in exp003,
   exp005 (and sir) so Lake regenerates the path dirs and preserves the mathlib rev pins; then `lake build` each cone.

Do NOT copy: the build-time-cloned `sha2/`/`keccak256/`/`blake2/` dirs (gitignored, regenerated) or their nested `.git`
dirs. Keep with the engine if you want CI conformance: `Conform/`, `Conform.lean`, the `@[test_driver] lean_exe «conform»`,
`tools/evmrs/`, and the `EthereumTests` gitlink submodule — nothing outside `EVMLean` imports `Conform`, so these are
test-only. Non-blocking follow-up: sweep doc/plan `.md` references to `EVMLean/` and `003_bytecode_layer/EVMLean` paths
(track-c-review.md, semantics-crosscheck.md, create-crosscheck.md, codebase-map, calls-value-channel-plan, etc.) — they are
informational links, not build inputs, but will 404 after the move.

**Risk:** the exp005 flagship rides on this exact dependency edge. Do the whole hoist **on a branch and rebuild all three
cones green (including `lake build WIP` in exp005 to re-verify the axiom-clean flagship) before committing.** Ignore the
many `.worktrees/` and `.claude/worktrees/` copies — they are stale checkouts.

### 3.b Extract the reusable exp005 lowering machinery

Do a **staged retarget-onto-canonical-SIR migration, not a lift-and-shift.** exp005 is split into a sorry-free **default**
cone (`lean_lib LirLean`) and a WIP cone (`lean_lib WIP`, the `V2/Realisability/` flagship skeleton). Promote the default
cone only, re-keyed onto the canonical `Sir` types (`VarId`/`BlockId`, `Stmt.gas`, `Call.result`):

- **Promote (crown jewels):** `Spec/Lowering.lean` (the `lower` function), `Spec/Semantics.lean` (oracle-stream big-step,
  reconciled with `sir/`'s `Semantics/*` stubs), `Decode/` (code geometry, IR-shape-independent), `Materialise/` core value
  channel (leave `CleanHaltExtract`'s ~1000 IR-free engine lines behind), `Sim/` (per-statement simulation), `Assembly/`
  `sim_cfg` (rename to `Conformance/CfgSim`), `Spec/Recorder.lean` + `V2/{CallRealises,RecorderLemmas}`,
  `V2/Drive/DriveSim.lean`'s `totalGas` measure, and the `Frame` oracle/reflexivity half only.
- **Hoist the stranded spec vocab into the canonical `Spec` surface during the move:** `RunFromAll`, the exact-consumption
  mirrors, `evmV2CallEntry`/`evmV2CreateEntry` (currently stuck in the WIP lib).
- **Push DOWN into exp003/`bytecode_layer` (NOT into the SIR-lowering package):** all of `Engine/` (~6.4k lines of IR-free
  machine metatheory) and the IR-free majorities of `CleanHaltExtract`/`Match`/`StorageErase`/`CallPreservesSelf`. Land all
  future engine lemmas in exp003 from now on.
- **Leave behind / do NOT migrate:** the entire `V2/Realisability/` WIP cone (~12.7k lines) except its sorry-free statement
  defs; the dead v1 machine (`Frame/SmallStep.lean`) and the unconsumed result-slot channel
  (`IRState.callResult`/`bindCallResult`/`applyCall`/`Lir.Match`) — the canonical `Sir.Call` (explicit result VarId)
  supersedes it; `_attic/`; and `Audit.lean` (rewrite its axiom guards fresh for the renamed decls).

IR re-keying: `Expr.imm`/`tmp` → `Sir Expr.constant`/`var`; exp005 `Expr.gas` (an Expr) → `Sir Stmt.gas` (a Stmt);
`CallSpec` → `Sir Call` with explicit result VarId; `Tmp`→`VarId`, `Label`→`BlockId`. Also collapse the historical warts:
`Lir.V2` namespace → `Lir`/`Lir.Oracle`, `GasOracle`→`GasStream`, delete the `Trace` alias, retitle `Assembly/LowerConforms`.

**Ordering/risk:** target either a new `lean_lib` inside `sir/` (e.g. `Sir/Lowering/` + `Sir/Conformance/`) or a sibling
`sir-lowering/` package requiring both `sir` and `bytecode_layer`. **Re-prove the flagship `lower_conforms` and the
R11/R10a run-producer fresh against the canonical stack — do NOT port the 12.7k-line skeleton or build on its (now-closed
but retarget-invalidated) proofs** (proof-first/no-sorry discipline). `origin/setup-prod-sir` already scaffolds `sir/` and
deletes the same Realisability files this analysis marks as scaffolding, so it is the right base branch.

### 3.c Reconcile exp002's SIR with PR #2's canonical `sir/`

The new top-level `sir/` (PR #2, branch `origin/setup-prod-sir`) is a fresh, minimal canonical SIR: a register-based (NOT
SSA) CFG + an event-labelled small-step semantics, ~493 lines with **zero theorems yet**. It uses concrete exp003
primitives (`Word = Evm.UInt256`, `World = Evm.AccountMap`) and models GAS+CALL as trace `Event`s. It conceptually
supersedes exp002's SIR, but exp002 is a *proved* artifact (axiom-clean SCCP correctness + a semantics bridge) that `sir/`
has not yet reached. They differ on three axes: SSA+dominance-validity (exp002) vs plain register CFG (`sir/`); abstract
`UInt32`/`Word→Word` (exp002) vs concrete `UInt256`/`AccountMap` (`sir/`); no calls/gas (exp002) vs GAS/CALL as trace events
(`sir/`).

Plan — treat `sir/` as the single canonical forward-going SIR; demote exp002/exp003 to donors:

1. **Keep exp003 exactly as-is** — it is `sir/`'s dependency floor (vendored `Evm.*` + a separate bytecode/observables
   layer); nothing to fold, nothing to discard.
2. **Do NOT rewrite exp002 in place.** Port its two proven assets into `sir/`: **first** reproduce exp002's
   executable↔relational bridge (a fuel `eval?` + `eval?_iff_steps` + progress) for `sir/`'s trace-aware `SmallStep` (which
   has the relation + decode helpers but no bridge or metatheory yet); **then** port the SCCP pass (lattice `Value`, monotone
   transfer, bounded-score fixpoint, rewrite, and the `PreservesSemantics` correctness theorem) from
   [`002_ssa_cfg/SirLean/SCCP.lean`](../../experiments/002_ssa_cfg/SirLean/SCCP.lean) onto `sir/`'s register CFG.
3. **Decide SSA up front.** exp002's SCCP correctness leans on SSA invariants (`Nodup` defs, `DefinedOnAllPaths`), which
   `sir/` dropped. Prefer **(a)** reintroducing exp002's validity apparatus as an *optional refinement* over `sir/`'s
   `Program` used only by optimization passes (lower-risk, invariants already vetted) over **(b)** re-proving SCCP without SSA.
4. **Impose the Spec/Proof audit-surface discipline** (exp002 AGENTS.md: `Spec` = human surface, `Proof` = kernel-checked,
   characterization lemmas over unfolding, `#print axioms` guards) on `sir/` **before** any proofs land — `sir/` has none today.
5. **Once bridge + SCCP are ported and green/axiom-clean under `sir/`, retire `experiments/002_ssa_cfg`** (mark superseded,
   keep git history) rather than dual-maintaining a `UInt32`/abstract-world fork.

Toolchain note: `sir`, exp003, and exp002 all pin `leanprover/lean4:v4.30.0`, so they co-import — this **contradicts the
older flat/nested toolchain-lock memory** (that concerned exp003=v4.30 vs exp004=v4.22). exp002 currently requires mathlib
*directly*; `sir/` pulls mathlib only transitively through `bytecode_layer`, keeping its core mathlib-light — preserve that.

### Overall migration ordering & the single riskiest step

Recommended order: **(1) hoist EVM (3.a) on a branch, rebuild all three cones green including `lake build WIP`** → then
**(2) build the retarget on top of `origin/setup-prod-sir`**: reconcile exp002 assets into `sir/` (3.c), extract the exp005
default-cone machinery re-keyed onto `Sir` (3.b), and re-prove the flagship fresh. The **single riskiest step is 3.b's
flagship re-proof against the canonical `Sir` IR** — it is a from-scratch re-derivation of the axiom-clean headline over a
changed IR (with the R11/R10a run-producer), not a mechanical port; the 3.a hoist is the riskiest *mechanical* step because
the axiom-clean flagship rides on that exact dependency edge and a mis-pointed manifest fails silently until a full rebuild.

---

## 4. Open questions for the lead

1. **Upstream the CREATE patch chain?** The only genuine *logic-adjacent* residual is provenance: conformance is pinned to a
   patched, un-upstreamed leanevm (`7ecbee7`/`7b34698`/`ad67864`). Do we push these upstream (proved-dead `.error` arm +
   faithful soft-fail checkpoint), and do we run `lake exe conform --full` green on the patched `EVMLean` first (the rust
   `evmrs` helper build was deferred)?
2. **Build a create-exercising witness?** `createResolves` is currently only discharged *vacuously* (exProg is create-free).
   Do we want a concrete witness with a reachable CREATE to demonstrate non-vacuous kernel discharge, mirroring the
   call-exercising `exProg`?
3. **Prove `createResolves` via the `UInt64` no-overflow envelope**, or leave it as a per-program checkable side condition?
4. **Recover the zero-gas-revert corner** in `RunLog.clean` (record a `FrameHalt` reverted-bit), or accept the conservative
   scope cut as a permanent disclosed boundary?
5. **SSA in `sir/`:** reintroduce exp002's dominance-validity apparatus as an optional refinement (option 3a) so SCCP ports
   cleanly, or re-prove SCCP without SSA?
6. **Migration target shape:** a new `lean_lib` inside `sir/` (`Sir/Lowering/` + `Sir/Conformance/`) or a sibling
   `sir-lowering/` package requiring both `sir` and `bytecode_layer`?
7. **Fix the stale docs now** (`lakefile.lean:28`, `RealisabilitySpec.lean:16`, `Machinery.lean:4546` all still narrate
   sorries that no longer exist) — worth a small cleanup commit given they actively understate a closed result.
