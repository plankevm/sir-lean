# Consolidate the bytecode layer under EVM — plan (2026-07-13)

Status: **PLAN — not executed.** Branch `refactor/fold-bytecode-layer` @ `823214a3`
(fold verified green + axiom-clean `[propext, Classical.choice, Quot.sound]`).

## Goal (as set by Eduardo)

Consolidate the reasoning layers around the top-level **`evm`** package (`EVM/`),
killing the artificial experiment-package separations — **but keep the IR ("Lir")
out of EVM entirely.** "Lir" is exp005's internal name for a compiler IR; it is not
an EVM concept and must never appear in the EVM package's namespace or identity.

Decisions locked with Eduardo (2026-07-13):
- **IR topology:** leave the exp005 IR-lowering code where it is for now. First
  figure out which parts of exp005 are *strictly* about IR lowering (estimate: very
  little) vs which are EVM-generic bytecode reasoning that merely mentions `lower`.
  Migrate the generic parts into EVM **later**, alongside the new canonical IR.
- **IR name:** keep `Lir` for now. Only scrub `Lir`/`LirLean` names out of the
  EVM-bound engine modules. (Rename to the canonical IR name is a separate, later step.)
- exp004 (`v4.22.0`) stays out — toolchain-locked, cannot co-import with the
  `v4.30.0` line.

## Current state (three packages, one chain)

```
ir_lowering (experiments/005_ir_lowering, libs LirLean + WIP)
    └─ require bytecode_layer from ../003_bytecode_layer
bytecode_layer (experiments/003_bytecode_layer, lib BytecodeLayer)
    └─ require evm from ../../EVM
evm (EVM/, libs Evm + Conform, exe conform)   [trusted base + FFI + mathlib]
```

All three on `leanprover/lean4:v4.30.0`. Dependency is strictly one-way:
`Lir → BytecodeLayer → Evm`. `BytecodeLayer` imports only the `Evm` umbrella module
and is genuinely EVM-level (Hoare `Runs` reasoning, interpreter drive/measure,
semantics mirrors). This is the piece that belongs *inside* EVM.

## Problem found during planning: residual IR names leaked into the EVM-bound engine

Last night's fold moved 7 IR-free engine modules into `BytecodeLayer/Hoare/` but left
them stamped with the IR's namespace. `Lir` is therefore currently a namespace
**shared across both the exp003 and exp005 packages** — the exact thing that must not
reach EVM. Exact scope:

Files in exp003 declaring IR namespaces (6):
- `BytecodeLayer/Hoare/AccountMap.lean` — `namespace Lir` (defines `AccPresent`,
  `accMono_of_accounts_eq`, `accounts_find?_insert_mono`, `SelfAt`, …)
- `BytecodeLayer/Hoare/Descent.lean` — `namespace Lir` (19 Lir tokens)
- `BytecodeLayer/Hoare/CleanHalt.lean` — `namespace Lir`
- `BytecodeLayer/Hoare/DriveMono.lean` — `namespace Lir`
- `BytecodeLayer/Hoare/StepWalk.lean` — `namespace Lir` + ~30 `open Lir (…)` (91 tokens)
- `BytecodeLayer/Hoare/MemAlgebra.lean` — `namespace LirLean.MemAlgebra`

139 `Lir`/`LirLean` tokens total in exp003. **15 exp005 files** import
`BytecodeLayer.Hoare.*` and reference these now-EVM-side symbols, so the rename is
cross-package: rename in exp003, update references in exp005.

These predicates (`AccPresent`, `SelfAt`, account-map monotonicity, mem algebra) are
EVM-generic — nothing IR-specific about them. They just kept their old home's name.

## The EVM / non-EVM boundary

- **→ into EVM (EVM-level, generic):** all of `BytecodeLayer` + one stray exp005 file,
  `LirLean/Frame/StorageErase.lean` (pure storage-map, namespace `Evm.Storage`, zero
  IR references). After the name scrub, zero `Lir` in the EVM package.
- **→ stays in the IR package (strictly IR, NOT in EVM namespace):** the IR datatypes
  (`Spec/IR.lean`: `Expr/Stmt/Term/Block/Program`), `lower` (`Spec/Lowering.lean`),
  IR reference semantics (`Spec/Semantics.lean`), conformance vocabulary, and the three
  flagships (`Realisability/RealisabilitySpec.lean`).
- **→ to be adjudicated (Phase 2):** the bulk of exp005 (`Decode/ Sim/ Materialise/
  Drive/ CfgSim/` and most roots). These *reason about EVM bytecode execution* and only
  *mention* `lower prog` as the particular bytecode. Eduardo's hypothesis is that most
  of this is EVM-generic-but-coupled, not strictly IR — TBD by the Phase-2 criterion.

## Plan

### Phase 0 — Scrub residual IR names from the EVM-bound engine  *(now, precursor)*

Rename the 6 exp003 engine files' `Lir` / `LirLean.MemAlgebra` namespaces into a proper
EVM-package namespace (proposed: keep symbols under `BytecodeLayer.Hoare.*`, e.g.
`BytecodeLayer.Hoare.AccountMap.AccPresent`). Sweep the ~15 exp005 reference sites.
No proof-body logic changes — pure namespace/reference rename.

Gate: `lake build` + `lake build WIP` green in exp005; all three flagships
`[propext, Classical.choice, Quot.sound]`. Commit or revert.

**Outcome:** zero `Lir`/`LirLean` tokens in exp003. This is a prerequisite for Phase 1
regardless of later topology.

### Phase 1 — Dissolve exp003 into the EVM package  *(now)*

1. Move `experiments/003_bytecode_layer/BytecodeLayer/` → `EVM/BytecodeLayer/`
   (source tree only).
2. In `EVM/lakefile.lean` add `lean_lib «BytecodeLayer»` (globs `.andSubmodules
   \`BytecodeLayer`), alongside `Evm` and `Conform`. Same package → no `require`; module
   imports (`import Evm`, `import BytecodeLayer.…`) resolve by module path.
3. Delete `experiments/003_bytecode_layer/lakefile.lean`, `lake-manifest.json`,
   `lean-toolchain`, and the now-dead `require evm` edge. Retire the exp003 dir
   (or leave a stub README pointing to `EVM/BytecodeLayer/`).
4. Re-point exp005: `require bytecode_layer from "../003_bytecode_layer"` →
   `require evm from "../../EVM"`. exp005 keeps importing `BytecodeLayer.*` (now a lib
   of the `evm` package). No source moves in exp005 this phase.

Gate: build `Evm`, `Conform`, `BytecodeLayer` in the `evm` package green; build exp005
`LirLean` + `WIP` green; three flagships axiom-clean. Commit or revert.

**Outcome:** two packages — `evm` (now hosting the bytecode Hoare layer) and
`ir_lowering` (the IR + lowering, unchanged, depending on `evm`). Chain collapsed 3→2.
Satisfies "consolidate under EVM" for the generic layer; `Lir` lives only in exp005.

### Phase 2 — Classify exp005: strictly-IR vs EVM-generic-coupled  *(now/next, analysis only)*

No code movement. Produce a per-module classification doc using a crisp test:

> A module is **strictly IR** iff its theorem/def *statements* cannot be expressed
> without the IR types (`Program/Block/Stmt/Term/Expr`) or `lower`. It is
> **EVM-generic-coupled** iff it reasons about bytecode/decode/execution/gas and only
> *mentions* `lower prog` as the concrete bytecode — i.e. the statement generalizes to
> arbitrary bytecode with the IR hypotheses factored out.

Preliminary read (to be tested, not trusted):
- Likely strictly-IR: `Spec/IR.lean`, `Spec/Lowering.lean`, `Spec/Semantics.lean`,
  `Spec/Conformance.lean`, `Spec/WellFormed.lean`, the flagships, IR CALL/CREATE
  oracle vocabulary (`Frame/Call,Create,Match`, `Call.lean`, `CallRealises.lean`).
- Candidate EVM-generic-coupled (Eduardo's "most of it"): much of `Decode/` (decode,
  layout, jumpdest validity, boundary reach), `Sim/`, `Materialise/` (value-channel
  spill/recompute), `Drive/`, `CfgSim/`, `Decode/Modellable.lean` (already a
  `BytecodeLayer.Interpreter` concept, IR-entangled only via `= lower prog`).

Deliverable: `docs/planning/exp005-ir-vs-generic-classification.md` — the input to Phase 3.

### Phase 3 — Migrate EVM-generic exp005 parts into EVM  *(later, deferred)*

After the new canonical IR lands. Move the Phase-2 EVM-generic machinery into EVM's
bytecode layer (decoupled from `lower` where the criterion says it generalizes),
relocate `Frame/StorageErase.lean`, and leave the thin strictly-IR core as the
lowering-correctness package over the canonical IR. Out of scope now.

## Risks / notes

- **Verification cost.** The `WIP` lib rebuilds the full exp003+EVM cone; each green
  gate is a full slow build. Budget accordingly (a green-gated box run is a good fit,
  as with the fold).
- **Namespace collisions on merge.** Besides `Lir`, watch `Evm`, `Outcome`,
  `SharedObservable` — `BytecodeLayer` extends some of these; confirm no clashes when it
  becomes a sibling lib of `Evm` in the same package.
- **`Decode/Modellable.lean`** is a generic `ModellableStep` concept in
  `BytecodeLayer.Interpreter` but currently tied to `= lower prog`; it's the clearest
  Phase-2 "split the generic part out" candidate.
- **Every step green-gated, axiom-clean, or revert** — same discipline as the fold.
