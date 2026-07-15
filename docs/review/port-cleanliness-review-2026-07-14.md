# Ported bytecode layer — code-structure cleanliness review (2026-07-14)

Scope: the post-fold `EVM/BytecodeLayer` surface + the `experiments/005_ir_lowering/LirLean`
residue, on `refactor/fold-bytecode-layer` @ `ccf0d0d2` (split + fold + Phase C merged).
Method: four grounded read-only deep reviews (Exec surface / assembler / Hoare+Semantics engine /
exp005 residue) + whole-tree hygiene greps. Read-only; nothing was changed.

## Headline

**The port is clean at the level that matters, and carries cosmetic/organizational debt only.**
No blocker, no soundness issue, no architectural rework needed. The autonomous overnight work
produced a genuinely correct consolidation; what remains is a ~half-day to one-day mechanical
tidy pass, green-gated per step.

### Hard constraints — ALL hold (verified globally)

| Invariant | Result |
|---|---|
| No `Lir`/`LirLean` token anywhere under `EVM/` | ✅ 0 occurrences |
| No IR-concept leak (`IRState`/`defsOf`/`IRExpr`/`IRStmt`) into `EVM/BytecodeLayer` | ✅ 0 (the `Program` hits are all *bytecode*/`AsmProgram`) |
| Layering direction — nothing in `EVM/` imports exp005 | ✅ 0 back-imports |
| No `sorry`/`admit`/`axiom`/`native_decide`/`bv_decide` in `EVM/BytecodeLayer` | ✅ 0 (grep hits are docstrings *claiming* cleanliness) |
| Both cones build; 3 flagships `[propext, Classical.choice, Quot.sound]` | ✅ re-verified (1165 + 1198 jobs) |
| exp005 residue genuinely IR-only (no stranded generic mass) | ✅ confirmed — generic mass is on the `BytecodeLayer` side, only re-exported |
| Assembler de-fuse real & IR-agnostic; `lower = assemble ∘ lowerAsm` | ✅ `lower_eq_assemble_lowerAsm` by `rfl`, backed by the substantive `bytes_lowerAsm` induction |

## Findings

### Blockers
None.

### Should-fix (organizational — do before calling the port "done")

1. **IR / version vocabulary lingering in now-generic names — the single most misleading category.**
   These names imply IR/lowering/versioning in a layer that no longer has any:
   - `IRHalt` — `EVM/BytecodeLayer/Exec/Observable.lean:18` (→ `HaltResult`/`FrameHaltObs`)
   - `MatDecLower.lean` filename — `EVM/BytecodeLayer/Exec/MatDecLower.lean` contains only PUSH32
     round-trip / byte-window lemmas, zero IR content; "Mat-Dec-Lower" = Materialise/Decode/Lower
     (→ `ByteWindow.lean`/`Push32RoundTrip.lean`). Also collides in name with the *IR-side*
     `LirLean/Materialise/MatDecLower.lean`.
   - `evmV2CallEntry` / `evmV2CreateEntry` — `Exec/Recorder.lean:16,21` (drop the `V2` version tag)
   - `call_reflects_lowered` / `create_reflects_lowered` — `Exec/CallRealises.lean:28,39`
   - `lower_modellable` — `Exec/Modellable.lean:362` (no lowering here; → `modellable_of_runs`)
   Mostly mechanical renames; each re-checked green.

2. **Dead `Trace` alias.** `Exec/Observable.lean:25-26` `abbrev Trace := GasOracle` — zero live uses
   (the other `Trace` hits are `dbgTrace`/`getLeanTrace`). Delete.

3. **`MatDecLower.lean` imports the whole `Exec` aggregator for 3 lemmas.**
   `Exec/MatDecLower.lean:1` pulls the entire surface for `wordBytesBE` + two facts; it is itself
   only imported by `Asm/Geometry.lean`. Narrow the import / relocate `wordBytesBE`.

4. **Assembler DRY: the `SegAlignedP`-over-emission alignment ladder is triplicated (exp005 side).**
   `Asm/Geometry.lean` proves `segAlignedP_bytes` generically for every `AsmProgram`, and
   `LirLean/Decode/SegAligned.lean:255-263` (`segAlignedP_flatBytes`) shows the IR case transports
   straight from it. But `SegAligned.lean:70-263` re-derives the full per-construct ladder
   (`matStep`/`matFold`/`emitStmt`/`emitTerm`…) by hand, and `Decode/BoundaryReach.lean` copies that
   same induction structure two more times for `NoCallCreateOp` (`:39-160`) and `NoGasOp` (`:625+`) —
   identical induction, only the leaf `decide` differs. Parameterize the ladder over the predicate `P`.
   **This is the one item worth a real (small) refactor, not just a rename.**

5. **IR-specific def under a generic namespace.** `lower_modellable` / `AtReachableBoundary`
   (`LirLean/Decode/Modellable.lean`, takes `prog : Lir.Program`, references `Lir.lower`) live in
   `namespace BytecodeLayer.Interpreter`. Reads generic, is IR-specific — placement smell. Move to a
   `Lir.*` namespace or relabel.

6. **A frozen DRAFT interface ships in the always-imported aggregator.**
   `EVMSpec.lean` defines a second engine-abstraction (`structure EVMSpec` + `flatSpec`,
   `EVMSpec.lean:100,134`) explicitly stamped `DRAFT` and "retire `flatSem` once Eduardo confirms" —
   yet it's wired into the root aggregator `BytecodeLayer.lean:27`, while the live interface is
   `EVMSemantics`/`flatSem` (`SharedObservable.lean:148,156`, used by `Refinement`/`Equivalence`).
   Resolve the migration (promote and retire `flatSem`) or keep the draft off the main aggregator.

7. **Two dangling references** (stale symbol/doc names, harmless but misleading):
   - `Spec.lean:55` cites `docs/ir-design-v2.md` — **file does not exist**.
   - `Hoare.lean:28` names bridge theorem `messageCall_runs_completed` — **no such theorem**
     (real ones: `messageCall_runs`, `ofCall_completed_of_success`).

8. **Dangling `_attic/` references (exp005).** `experiments/005_ir_lowering/lakefile.lean` and
   `LirLean.lean` header point at `_attic/{Decode,WorkedCall,…}` — the directory does not exist.
   Drop the references (and `lake clean` the stale `V2/HonestGasTie.olean` build-cache leftover).

### Nits (batch opportunistically; none blocks anything)

- **`Observable` (singular, `Exec/Observable.lean`) vs `Observables` (plural, `Observables.lean`)** —
  near-identical names for unrelated types in sibling namespaces. Confusing to grep. *(All three
  observable files — `Exec/Observable`, `Observables`, `SharedObservable` — are genuinely three
  different altitudes: low-level oracle stream / messageCall-boundary outcome / cross-engine plain
  data. Not triplication; just the name clash.)*
- **`stub_accounts_*`** (`Exec/WitnessChecks.lean:32-104`) — "stub" = precompile stub-account, but it
  reads like an unproven sorry-stub at a glance. → `precompile_accounts_*`.
- **`Modellable.lean` sits under `Exec/` but declares into `BytecodeLayer.Interpreter`** — inconsistent
  with every sibling.
- **`CreateStream` ≡ `CallStream`** (identical `List (World × Word)` abbrevs) — add no type safety.
- **Duplicate `open` statements** — `Exec/CallRealises.lean` opens `Exec` twice; `Exec/Invariants.lean`
  opens `Evm` twice.
- **"Five-file surface" label is off by 16** — `Exec/` is 21 files under three namespaces
  (`Exec.Invariants`, `Exec.Recorder`, top-level `Exec`). Either drop the "five-file" framing in the
  planning docs or make the namespace clusters visible as `Exec/Invariants/`, `Exec/Recorder/` subdirs.
- **exp003 framing in docstrings** — many modules still narrate the folded-in engine as "experiment
  003 / the bytecode layer over leanevm" (e.g. `BytecodeLayer.lean:1`, `Programs.lean:6`,
  `DriveRuns.lean:34`). True as history, anachronistic post-fold.
- **Cross-engine cluster could be a subdir** — `SharedObservable`/`Equivalence`/`Refinement`/`EVMSpec`
  are a cohesive flat↔nested sub-topic sitting flat among the in-engine files.
- **3 unused `RecorderLemmas` re-exports (exp005)** — `sloadRecord_eq_sloadCost`, `driveLog_drive`,
  `realisedCreate_cons` have zero consumers.
- **`Gas.lean` (22 lines) / `Results.lean` (42)** — legit but thin standalone modules; could fold into
  neighbors. Low priority.
- **Repeated `HonestGasTie` / `exp003` historical narration** in several exp005 docstrings — accurate
  (the file is deleted) but trimmable.
- **`Spec.lean:22-28` self-flags** its exported program-logic rules as frame-level (vs the
  observables-only surface standard), ending "To reconcile." A standing altitude caveat, not a defect.

## What is genuinely clean (so it's on record)

- **exp005 residue is minimal and IR-only.** The ~10 tiny files are a deliberate *namespace-bridge*
  adapter layer (each re-`export`s moved generic names into `Lir` so IR proofs reference them
  unqualified) — not stub sprawl. No dead files; no EVM-generic def/lemma stranded on the IR side.
- **Assembler de-fuse is real and well-placed.** `AsmProgram`/`assemble`/`Asm/Geometry.lean` are
  IR-agnostic and live entirely in `EVM/`; the `lowerAsm` adapter sits correctly in
  `BytecodeLayer.Asm` on the exp005 side; `mem_validJumpDests_assemble_iff` is a faithful
  "valid jump dests = block-entry offsets" statement, both directions proved.
- **Layering is one-way and cohesive.** `Semantics/` → `Hoare/` → `Spec`/cross-engine, no back-edges;
  `Hoare/` (12 files) and the recorder subsystem (`Recorder`/`RecorderLemmas`/`CheckedStep`/…) are
  principled def/lemma splits, not artificial. `CleanHaltExtract.lean` (1108 lines) is cohesive, not a
  dumping ground.
- **Docstrings are unusually honest** — deferred value-channels, retired/unsatisfiable universals, and
  altitude caveats are all disclosed rather than papered over. `Audit.lean` (the axiom-footprint guard
  net) is intact and correctly last.

## Recommended cleanup shape (if pursued)

One green-gated "Phase D-lite: port hygiene" pass, each step reverting on any red:
1. Mechanical renames (should-fix #1) — sweep IR/`V2`/`lower`/`Mat` vocabulary out of generic names.
2. Delete dead `Trace` alias + duplicate `open`s + narrow `MatDecLower` import (#2, #3, nits).
3. Fix the two dangling refs + `_attic/` refs + `lake clean` stale artifacts (#7, #8).
4. Resolve or de-aggregate the `EVMSpec` DRAFT (#6).
5. *(Optional, real proof work)* parameterize the alignment ladder to kill the triplication (#4).
6. *(Optional)* relocate `Modellable`, corral the cross-engine cluster, add `Exec/` subdirs (#5, nits).

Steps 1–4 are mechanical and safe; step 5 is the only one touching proofs and is self-contained.
