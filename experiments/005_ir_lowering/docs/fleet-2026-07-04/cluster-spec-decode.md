# Fleet 2026-07-04 — Cluster report: Spec (definitions) + Decode/control-flow-validity

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Scope: the 14 files of the Spec-core and the decode / byte-layout / control-flow-validity
layer. Verdicts are for file organisation only; no `.lean` file was modified.

Flagship reminder: `RealisabilitySpec.lean` (WIP, sole sorry-carrier) imports
`Acyclic`, `BoundaryReach`, `Lir.Drive.Headline`. Lead has flagged `Acyclic` + `LowerConforms`
for deletion. **Key correction from the import graph: `LowerConforms` is imported by BOTH
`Acyclic` (doomed) AND `Lir.DriveSim` (surviving cyclic spine). So nothing in this cluster is
purely "acyclic-only"; the decode/layout tower is shared by the surviving control-flow-validity
path (`JumpValid → NoCreateBytes → Lir.Modellable → DriveSim → Headline → flagship`, and
`BoundaryReach → flagship` directly).**

## 1. File table

| File | LOC | One-line purpose | Key exports | Feeds | Verdict | Simplification note |
|------|-----|------------------|-------------|-------|---------|---------------------|
| `Spec/IR.lean` | 114 | IR datatypes (Word, Tmp, Label, Expr, Stmt, Term, Block, Program) | `Expr`, `Stmt`, `Term`, `Program`, `CallSpec` | spec-surface (root of everything) | **load-bearing** | Foundation. P9 deleted the old `Expr.slot` spill-remat marker; spill placement now lives in `Loc`. |
| `Spec/Semantics.lean` | 278 | Gas-free observable IR machine (`IRState`, `evalExpr`, `RunFrom`, `IRRun`) | `IRRun` (275), `RunFrom` (228), `evalExpr` (123), `CallStream` (99) | spec-surface; → `Lir.Law → IRRun → DriveSim` (cyclic) | **load-bearing** | The v2 spec machine. Header still calls itself "call-free prototype" (5) — stale; calls are now modelled via `CallStream`. Docstring drift only. |
| `Spec/Lowering.lean` | 358 | Pure IR→bytecode emission (`lower`, `emit*`, `defsOf`, `matCache`, offset table) | `lower` (358), `emit` (346), `defsOf` (152), `matCache` (213) | spec-surface; feeds all via `LoweringLemmas` | **load-bearing** | The lowering definition itself. Keep. |
| `Spec/Recorder.lean` | 358 | Instrumented recording interpreter `runWithLog` + oracle projections | `runWithLog` (262), `realisedGas/Sload/Call/Create` (285/291/306/321), `driveLog` (186), `observe` (340) | spec-surface; → `RecorderLemmas → SimTerm` (gas sim) + `SelfPresent` (cyclic) | **load-bearing** | Constructive oracle producer. Keep. |
| `Spec/Seams.lean` | 95 | Reviewer-facing seam register plus live `PrecompileAssumptions`/`ReachableFrom` vocabulary | `PrecompileAssumptions`, `ReachableFrom`, `SelfPresent`, `CallPreservesSelf`, `CallsCode`, `CleanHaltsNonException` | spec-surface; imported by WIP surface and audit | **load-bearing vocabulary** | Re-keyed to the live flagship: `hseams.noErase`, `hseams.callsCode`, and `hseams.createResolves` are the live fields; the older names are supporting forwarders. |
| `Spec/Conformance.lean` | 24 | Hoisted conformance vocabulary and honesty notes for the live WIP theorem surface | `entryState`, `RunLog.clean`, `Conforms`, `NoGasReads` | spec-surface; imported by WIP surface | **load-bearing vocabulary** | No longer a tombstone; keep as the trusted conformance statement surface. |
| `LoweringLemmas.lean` | 139 | Proof companions of `Spec/Lowering` (`defsOf_ne_gas/_sload`, `rematOf` projection twins, `defsOf_eq_defEnv_find`) | `defsOf_ne_gas` (21), `defsOf_ne_sload` (64), `defsOf_of_rematOf` (107), `rematOf_of_defsOf` (116), `defsOf_eq_defEnv_find` (136) | → `DecodeLower`, `Match`, `DefsSound` (broad) | **support** (load-bearing) | Tiny lemma file split off Lowering to keep it "definitions-only". Defensible, but a candidate to fold back into `Spec/Lowering` if the discipline is not worth a separate file. |
| `Layout.lean` | 204 | Byte-layout / offset-table prefix-sum arithmetic of `lower` | `flatBytes_block_split` (115), `stmt_byte_anchor` (162), `blockPrefix_length` (93) | → `DecodeAnchors`, `JumpValid` (cyclic), `Match` | **load-bearing** | Bricks feed both the gas-sim and the surviving control-flow tower. Keep. |
| `DecodeLower.lean` | 159 | Generic "decode reads back the byte at pc" bridge over `flatBytes` | `flatBytes` (46), `lower_eq_flatBytes` (61), `decode_lower_{nonpush,push}` (144/151) | → `Layout`, `DecodeAnchors`, `JumpValid` (cyclic) | **load-bearing** | Program-independent decode core. Keep. |
| `DecodeAnchors.lean` | 318 | Decode-at-cursor anchors (stmt-head / mid-stmt / terminator) | `decode_at_stmt_head_{nonpush,push}` (195/215), `decode_at_term_*` (283/300), `termOf` (156) | → `JumpValid` (cyclic), `MatDecLower`, `SimTerm` | **load-bearing** | Layer A of the sim grind; also feeds the surviving JumpValid path. Keep. |
| `LowerDecode.lean` | 1528 | Wires anchors+`MatDec` to discharge the `sim_*` decode bundles (gas-aware sim) | `sim_sstore_stmt_lowered` (134), `sim_term_edge_{jump,branch}_lowered` (417/620), `sim_assign_{gas,sload}_lowered` (1167/1379), `*_landing_of_cleanHalt` (486/769) | → `LowerConforms` (+`Audit`) | **load-bearing** (fate-linked to gas-sim stack) | The gas-aware-simulation endpoint and the single largest file (1528 LOC). Reaches the flagship only through `LowerConforms → DriveSim`. **If the gas-aware stack is retired with `LowerConforms`, this whole file (and its `SimStmt/SimTerm/Match/Materialise` feeders) goes with it.** See §3. |
| `BoundaryReach.lean` | 432 | Boundary-reachability bricks for the whole-run `AtReachableBoundary` invariant | `reachesBoundary_of_mem_validJumpDests` (90), `reachesBoundary_nextInstr` (109), `SegAlignedLowering` (135), `decode_reachable_boundary_loweringOp` (415) | → **`RealisabilitySpec` directly** (cyclic flagship) | **load-bearing** | On the surviving flagship. Header (25-32) admits the `Runs`-induction that consumes these bricks is "not yet landed" — verify the bricks are actually wired, not stranded. |
| `JumpValid.lean` | 516 | Every block offset is a valid JUMP destination of `lower prog` | `block_offset_validJump` (471), `reaches_block_offset` (413), `SegAligned` (78), `reaches_of_segAligned` (120) | → `NoCreateBytes → Modellable` (cyclic) + `SimTerm` | **load-bearing** | Base of the 3-file SegAligned tower. Keep, but see §3 merge. |
| `NoCreateBytes.lean` | 431 | Lowering emits no CREATE/CREATE2 at any reachable boundary | `reachable_boundary_notCreate` (375), `SegAlignedSafe` (50), `reaches_safe_of_segAlignedSafe` (112) | → `BoundaryReach` + `Lir.Modellable` (cyclic) | **load-bearing** | Middle of the 3-file SegAligned tower. Keep, but see §3 merge. |

## 2. Dependency sub-DAG (within this cluster)

Entry root (imported from `Evm`, no cluster deps):
```
Spec/IR ──┬─ Spec/Semantics ─(exit → Lir.Law, DefsSound)
          └─ Spec/Lowering ── LoweringLemmas ─┬─ DecodeLower ─┬─ Layout ─┐
                                              │               │          │
                                              │               └──────────┼─ DecodeAnchors
                              (exit → Match,  │                          │       │
                               DefsSound)     └──────────────────────────┘       │
```
The decode/layout/anchors tower then splits into TWO exit paths:

- **Gas-aware sim path (fate-linked to `LowerConforms`):**
  `DecodeAnchors → (MatDecLower, SimTerm) → LowerDecode → [exit: LowerConforms]`.

- **Control-flow-validity path (surviving cyclic flagship):**
  `DecodeLower + Layout + DecodeAnchors → JumpValid → NoCreateBytes → BoundaryReach → [exit: RealisabilitySpec]`;
  branch `NoCreateBytes → [exit: Lir.Modellable]`; branch `JumpValid → [exit: SimTerm]`.

Standalone spec-surface (no inbound cluster edges): `Spec/Recorder` (→ `RecorderLemmas`, exit),
`Spec/Seams` (→ WIP surface/Audit, exit), `Spec/Conformance` (→ WIP surface, exit).

Entry edges INTO the cluster from other clusters: none — `Spec/IR` is a global root.
Exit edges OUT: `Spec.Semantics→Lir.Law/DefsSound`, `LoweringLemmas→Match/DefsSound`,
`Layout/DecodeLower/DecodeAnchors→Match/MatDecLower/SimTerm`, `LowerDecode→LowerConforms/Audit`,
`Spec.Recorder→RecorderLemmas`, `JumpValid/NoCreateBytes→SimTerm/Modellable`,
`BoundaryReach→RealisabilitySpec`, `Spec.Seams→Audit`.

## 3. SIMPLIFICATION OPPORTUNITIES

**A. The triple-duplicated SegAligned tower (biggest lever, ~1400 LOC).**
`JumpValid` (`SegAligned`, JumpValid.lean:78), `NoCreateBytes` (`SegAlignedSafe`, :50), and
`BoundaryReach` (`SegAlignedLowering`, :135) each define a segment-alignment inductive and then
re-prove the *identical* emit-ladder against it: `append / nonpush / push`, `reaches_*`, and
`{emitImm, emitDest, matExpr/matLoc, emitStmt, emitTerm, emitBlockBody, loweredBlock,
flatBytes}` (15 / 17 / 18 near-identical decls respectively;
`segAligned_emitStmt` JumpValid:243 ≈ `segAlignedSafe_emitStmt` NoCreateBytes:243 ≈
`segAlignedLowering_emitStmt` BoundaryReach:282). The two strengthenings only add a per-head
predicate (`parseInstr b ∉ {CREATE,CREATE2}`; `IsLoweringOp b`). This is textbook over-split:
one `SegAlignedP (P : UInt8 → Prop)` inductive parameterised on the head predicate, with the
emit-ladder proved once (each emitted head is a concrete byte, so `P` is discharged by `decide`
at the leaves), would collapse three files into one and eliminate the largest block of
copy-paste in the cluster.

**B. `Spec/Conformance.lean` is no longer dead.** It now hosts the trusted conformance
vocabulary (`entryState`, `RunLog.clean`, `Conforms`, `NoGasReads`) imported by the WIP surface.

**C. `Spec/Seams.lean` is now live statement vocabulary.** It still contains pure forwarders for
the older reviewer-facing seam names, but it also owns `Lir.PrecompileAssumptions` and
`ReachableFrom`, so it should not be folded into `Audit` while the WIP flagship uses that surface.

**D. Minor: `LoweringLemmas.lean` (98 LOC, 3 lemmas)** was split off `Spec/Lowering` purely to
keep the latter "definitions-only". If that discipline isn't load-bearing for the reorg, merge
it back — it saves an import hop shared by `Match`/`DecodeLower`/`DefsSound`.

**E. `LowerDecode` (1528 LOC) is NOT acyclic-doomed — the lead's `LowerConforms` deletion flag
looks wrong.** `LowerDecode` reaches the flagship through `LowerConforms`, and `DriveSim.lean`
**substantively consumes** `LowerConforms`'s bricks — `sim_stmts_block` and `sim_term_halt_stop`
are used in `DriveSim.lean:242`/`:234`, not merely imported (DriveSim.lean:62 self-documents
"imports the Layer C–E bricks via `LowerConforms`"). So `LowerConforms` — and therefore this
whole decode/anchor/gas-sim tower — is load-bearing for the *surviving* cyclic flagship, not the
doomed acyclic one. P9 already deleted the old `Acyclic.lean` fuel/rank file; `LowerConforms`
cannot be dropped without first reworking DriveSim.

**Header drift (cosmetic, confirmed stale):** `Spec/Semantics.lean:5` still self-describes as the
"call-free prototype" (calls now go through `CallStream`). `Spec/Lowering.lean:25-27` and
`DecodeLower.lean:9` cite a `LirLean/Decode.lean` round-trip file that **no longer exists** — the
references are dangling and should be updated or dropped (cf. MEMORY "just-fix-cruft").
