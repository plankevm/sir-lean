# exp005 master refactor plan — 2026-07-06

> **Engine-fold status (2026-07-13).** The deferred package fold has landed. The eight IR-free
> engine modules now live in exp003 under `BytecodeLayer/Hoare/`; the lowering-dependent
> `Modellable.lean` lives under `LirLean/Decode/`. References below to a future `Engine/`
> relocation describe the historical sequencing decision, not current work.

> **Namespace-fold status (2026-07-13).** The version tier has landed: the live semantics and
> flagships now use `Lir`, while `Drive/` and `Realisability/` are top-level `LirLean/` roles.
> The older frame-reference semantics is isolated by role under `Lir.Frame`.

> **P9 status note (2026-07-08).** The Phase 2A legacy-deletion pass has landed: `Expr.slot`,
> `materialiseExpr`, `materialise`, `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`, and
> `NoSlotSource` are gone. References below to those symbols are historical planning context unless
> explicitly marked as current work.

The full actionable roadmap distilled from `docs/codebase-map-2026-07-06.md` (misplacements §4,
smells §5, decisions §6). Sequenced by dependency and by conflict with the live R11 producer.

Two standing decisions from Eduardo folded in:
- **Engine relocation is NOT done now.** `Engine/` (and its CREATE twins) keeps growing in exp005;
  the ~5,800-line engine mass merges into exp003 only when exp005 finishes and we move to the real
  thing. So misplacements #2/#9/#11 and decision D10 are **Phase 4 (post-merge)**, off this roadmap.
- **`Expr.slot` migration (D4) has landed** as Phase 2A/P9 cleanup; mentions below are retained
  only to explain the historical migration.

## Guiding constraints

1. **Proof-first, no sorry.** Prove every bridge/derived lemma bottom-up before a signature consumes
   it. Never leave the flagship depending on an unproved bridge.
2. **The R11 producer is the critical path.** Classify every item by conflict with it:
   - **Green-parallel** (Phase 1): statements, docs, derived lemmas, file moves — no producer file
     re-typed. Safe to land alongside producer work.
   - **Value-channel churn** (Phase 2): re-types `materialiseExpr`/`MatDec`/`chargeOf`/`MatRuns` and
     the `Sim/` lemmas the producer instantiates. Needs a producer-quiescent window **or** waits for
     R11 to land. Do NOT run under an active producer edit.
   - **Cosmetic/rename** (Phase 3): tree-wide string churn; after Phase 1 settles the Spec surface.
3. **Every commit honest.** No "billed as final, missing fields."

---

## Phase 1 — green-parallel to the producer

### 1A. Honesty / doc sweep (pure text)

- **5.2** — `Assembly/LowerConforms.lean` header (:5) and §1148-1177 narrate a `lower_conforms`
  deleted in b144af8 ("**fully discharged** here"). Retitle to `sim_cfg` (Layer F); replace §1148
  prose with a pointer to the live flagship (`RealisabilitySpec.lean:206`, R11) — this file's payoff
  is `sim_cfg` (:983), not a discharged headline.
- **5.9** — `DriveSim.lean:672` calls `lower_conforms_cyclic'`'s `RunDefinable` premise "benign
  well-formedness"; it is unsatisfiable for any call/create/gas program. Amend to state the
  pure-fragment restriction and point to `RunDefinableG` (Surface.lean:153).
- **5.12** — one stale-ref commit: `Machine.lean`/`LirLean/Match.lean` pre-reorg paths
  (Call.lean:7/10/23, CallRealises.lean:11, DriveSim.lean:63, SelfPresent.lean:184,
  Surface.lean:882/893, Semantics.lean:27); `LirLean/Decode.lean` (Lowering.lean:25-27); "16 lowering
  opcodes" → 18 post-CREATE/CREATE2 (SegAligned.lean:14/29, BoundaryReach.lean:23-30/118-124 — the
  enumerated allow-list is factually wrong); deleted-`NoCreateBytes` cites (SegAligned.lean:13/67,
  JumpValid.lean:41/80); flagship path missing `Realisability/` (Conformance.lean:16, Audit.lean:23);
  (NOT MemAlgebra.lean:964-994 — those 8 `#guard_msgs in #print axioms` are LIVE build-failing
  axiom-cleanliness guards, preserved on purpose by 53c2063; the map's original "enforce nothing"
  claim was wrong. Leave them.)

*Lands immediately, independently.*

### 1B. `IRWellFormed` + two scalar budgets (the `WellLowered` adapter)

**P8 status update (2026-07-08):** this section has mostly landed. The public theorem shape is
now `IRWellFormed prog` plus the scalar budgets `codeFits prog` and `stackFits prog`; the WIP
bridge rebuilds the internal `WellLowered prog` adapter consumed by the existing V2 machinery.
`WellFormedLowered` remains internal lowered-layout structure over `matCache` lengths and fold
offsets. It no longer carries fuel-sufficiency fields.

The core insight: the old `WellLowered` premise mixed pure IR structure with per-cursor lowered
layout bounds. P8 keeps the source-side facts in `IRWellFormed`, keeps the layout bounds internal,
and derives the latter from two scalars.

```lean
def codeFits  (prog : Program) : Prop := (flatBytes prog).length < 2 ^ 32   -- pc budget
def stackFits (prog : Program) : Prop := maxChargeDepth prog ≤ 1024         -- stack budget

structure IRWellFormed (prog : Program) : Prop where
  defineBeforeUse : RunDefinableG prog
  defsConsistent  : DefsConsistent prog
  entry0          : prog.entry.idx = 0
  cfgClosed       : CFGClosed prog        -- ClosedCFG minus its offset-bound halves
  defEnvOrdered   : DefEnvOrdered prog    -- ordered def-env; no rank/fuel envelope
  revalidates     : RevalidatesPerBlock prog          -- 5.3 gap #2 (exists Surface.lean:312)
```

Field-by-field disposition table and the "not preservation, it's a soundness lemma
`IRWellFormed → budgets → layout-valid`" framing: see the design discussion — unchanged.

Two payoffs beyond aesthetics:
- `codeFits` **is already** R6's loose `hsize` (Machinery.lean:1364/1408/1463/1513); the flagship
  blocker comment says it "has no producer from `hwl`" (RealisabilitySpec.lean:235-237). Supplying
  it as a premise **discharges half the R6 blocker**.
- `RevalidatesPerBlock` already exists; it just becomes a field (closes 5.3 gap #2).

**Landed shape (bottom-up, each green):**
- **B1a `pcBounds_of_codeFits`**: `codeFits` derives the `WellFormedLowered` pc/offset bounds,
  `ClosedCFG` offset bounds, and the extra `WellLowered` gas/return-epilogue bounds. The two
  spilled-stash bounds additionally consume `DefsConsistent`.
- **B1b `stackBounds_of_stackFits`**: `stackFits` derives every `StackRoomOK` fold using
  `chargeCache` lengths, with `sloadChg`-independence proved by `chargeCache_length_sloadChg_eq`.
- **B1c is obsolete**: there is no live `matFueled_*` family to derive. `DefEnvOrdered` and the
  `matCache`/`chargeCache` fold fixpoints replaced the rank/fuel envelope.
- **B2** defines `codeFits`/`stackFits`/`IRWellFormed` in `Spec/WellFormed.lean`; `CFGClosed`
  carries only presence and in-bounds facts.
- **B3/B4** are represented by `wellLowered_of_IRWellFormed`, which returns `WellLowered`
  from `IRWellFormed` + `codeFits` + `stackFits` and keeps `WellFormedLowered` internal.

**P9 update:** `NoSlotSource` and the legacy fuel/materialisation stack are gone. The remaining
adapter point is `WellLowered`, which stays internal to the WIP proof machinery.

### 1C. Spec hoist — remaining work (misplacement #1, smell 5.1)

The trusted surface can now state the core conformance vocabulary, but several exact-run
definitions are still stranded in the WIP lib. Move the remaining flagship
**statement vocabulary** into `Spec/Conformance.lean` / `Spec/Semantics.lean`, all sorry-free.
`Conforms`, `entryState`, `RunLog.clean`, and `NoGasReads` have moved to
`Spec/Conformance.lean`; `IRWellFormed`/`codeFits`/`stackFits` live in `Spec/WellFormed.lean`;
`PrecompileAssumptions` and `ReachableFrom` live in `Spec/Seams.lean`. Still stranded are the
exact-consumption `RunFromLeft`/`RunFromAll` adequacy and the realised call/create entry
vocabulary. Keep `WellFormedLowered` internal; it is not a public statement premise. Fixes the
Spec import inversion (5.10) as a side effect. Leave only sorry'd theorems in the WIP lib.

### 1D. Cheap structural relocations (green-parallel; NOT to exp003 — within exp005)

- **#4** `pcOf` + `pcOf_eq_anchor`/`flatBytes_at_pcOf` (Frame/Match.lean:67-108) → `Decode/Layout.lean`.
  Kills the geometry→coupling import inversion (DecodeAnchors.lean:3, JumpValid.lean:5 import
  Frame.Match). `termOf` already lives on the correct side.
- **#3** `Decode/Modellable.lean` (namespace `BytecodeLayer.Interpreter`, zero V2 content) → `Engine/`.
  *This is consolidation within exp005, consistent with "keep working on Engine"* — not an exp003
  move. Seam defs (`CallsCode`, `CreateResolves`) stay reachable via Spec/Seams.
- **#5** `Decode/LoweringLemmas.lean` (zero geometry; `allocate_toDefs`, `defsOf_ne_*`) → Materialise/
  or a Spec companion. *Note: partly obsoleted by 2A — `allocate_toDefs`/`defsOf_ne_*` shrink or
  vanish when `Expr.slot` goes. Consider deferring this into 2A rather than moving-then-deleting.*
- **#6** `Spec/Recorder.lean`: `gasReadOf`/`FramesRun` (:65-73, its own relocation comment) → ;
  the admitted `GasMonotone` plumbing import (:2-5) → import directly in DriveSim. Deflates the
  trusted import cone.
- **#7 / 5.7** `Spec/Seams.lean`: **landed in the post-P9 cleanup.** The live
  `PrecompileAssumptions`/`ReachableFrom` vocabulary now lives there under `Lir`, and
  `PrecompileAssumptions.noErase` is definitionally the trusted
  `Lir.Spec.PrecompilesPreservePresence` shape. The old `AcyclicWellFormed` factoring idea is
  obsolete: `WellFormedLowered` is rebuilt from `IRWellFormed` + budgets, while P9 deleted the
  rank/fuel file.

### 1E. Name the anonymous bundles (smell 5.6)

Copy-paste-by-position bundles that ripple on any clause reorder:
- 10-12-conjunct stash-endpoint bundle ×7 (StashTail.lean:174/268/340; SimStmt.lean:637/918/1078;
  LowerConforms.lean:313) → `structure StashRuns` (mirroring `MatRuns`).
- 10-conjunct jumpdest-landing bundle ×4 (DriveSim.lean:313/395/512/698) → `structure JumpdestLanding`.
- per-terminator tie bundles duplicated verbatim (LowerConforms.lean:634-670 vs 869-898; etc.) — the
  call arm's named `CallRealises` is the in-tree template; ~120 deletable lines.

*Touches `Sim/`/`StashTail` statements — coordinate lightly with the producer, but these are
definitional refactors that leave lemma conclusions identical. Can precede or follow 2A.*

---

## Phase 2 — value-channel churn (producer-quiescent window OR post-R11)

These re-type the value channel the producer's sim lemmas sit on. Land in one coordinated batch.

### 2A. Remove `Expr.slot` (decision D4, smell 5.8) — the big one

`Expr.slot` is a placement directive wearing an expression costume: never a real sub-expression
(binary ops take `Tmp`), never evaluated (`evalExpr .slot ⇒ none`, Semantics.lean:147), and the
`Loc`/`Alloc` layer built to name the policy (Lowering.lean:94-113) immediately re-flattens into
`Expr` via `Loc.toDef`. The clean shape already exists as `Loc = remat Expr | slot Nat`.

**The retype** — move the slot-load to the `.tmp` lookup boundary, so `Expr` needs no `.slot`:
```lean
def materialiseExpr (a : Alloc) : Nat → Expr → List UInt8
  | _,   .imm w   => emitImm w
  | 0,   _        => []
  | f+1, .tmp t   => match a t with
                     | some (.remat e) => materialiseExpr a f e
                     | some (.slot n)  => emitImm (ofNat n) ++ [Byte.mload]   -- inline
                     | none            => emitImm 0
  | f+1, .add x y => materialiseExpr a f (.tmp y) ++ materialiseExpr a f (.tmp x) ++ [Byte.add]
  | f+1, .lt  x y => …
  | f+1, .sload k => materialiseExpr a f (.tmp k) ++ [Byte.sload]
  | _+1, .gas     => [Byte.gas]
  -- no .slot arm
```

**Deletions this enables:** `Expr.slot` constructor (IR.lean:94); `evalExpr`'s `.slot ⇒ none`
(Semantics.lean:147) → `evalExpr` becomes total-and-pure; `Loc.toDef`/`Alloc.toDefs`
(Lowering.lean:107-113); `noSlotSource` field from `WellFormed` (added temporarily in 1B); the dead
`.slot` arm in every IR-level lemma; `defsOf_ne_gas`/`_ne_sload`/`allocate_toDefs`
(LoweringLemmas.lean) shrink or vanish. `defsOf : Program → Alloc` (returns `Loc` directly; oracle
temps ↦ `Loc.slot (slotOf t)`).

**Ripple (~100 sites):** retype `MatDec` (MaterialiseRuns.lean:237), `chargeOf`
(MaterialiseGas.lean:73), `MatFueled` (MatDecLower.lean:262), `MatRuns`, `materialise_runs`, and the
`Sim/` lemmas consuming them, from `defs : Tmp → Option Expr` to `a : Alloc`. Statements' *conclusions*
are unchanged — this is a signature/threading refactor. **This is why it is Phase 2**: the producer
instantiates these sim lemmas.

**Payoff:** `evalExpr` total; `Expr` is a clean value grammar; the flagship loses the `noSlotSource`
obligation; `Loc`/`Alloc` becomes the single placement authority (the exact shape the future Asm
layer consumes — this is the Phase-3-doable half of the Asm placement story).

**Feasibility/timing note (unchanged from prior analysis):** orthogonal to the producer's
*difficulty* (coupling-threading), so it buys no headline progress — but it removes a flagship
obligation and de-clutters ~100 sites. Best in a window where the producer is not mid-arm.

### 2B. Dissolve `WellFormedLowered` (Depth-2 of 1B)

With 1B's budgets proved, retype the `Sim/` lemmas to consume `codeFits`/`stackFits` and derive their
local pc/stack bound inline (`pcOf + k ≤ length < 2^32`), then **delete** the `bound_*` fields from
`WellFormedLowered` — the contorted statements go away entirely, not just hidden behind a lemma.
Touches the producer edit surface (sim lemma signatures) → do with 2A. Folds naturally into the Asm
layer (Phase 4), which owns pc/offset algebra; end state = flagship premise is just `WellFormed prog`
+ an Asm "assembles within budget".

### 2C. Shrink the dead v1 coupling surface (smell 5.5, misplacement #8)

`Lir.Frame.Match` (Frame/Match.lean:126), `IRState.callResult/createResult`,
`bindCallResult/bindCreateResult` (SmallStep.lean:57-124), `applyCall`/`applyCreate`
(Call.lean:158, Create.lean:131): **zero consumers** (live path is the V2 stream pop,
Semantics.lean:207-235); the CREATE mirror was *added* to the dead channel in bbd9578. Fix docstring
overclaims (SmallStep.lean:106). **Decide**: either give v1 a real conformance statement, or shrink
`Frame/{SmallStep,Call,Create}` to the consumed oracle/flag surface + reflexivity pins. Per
deep-read-before-touching: no doc names a consumer-to-be, unlike the R-skeleton — leaning shrink.

### 2D. `sim_call_stmt` interface (smell 5.4) — partial, non-producer half only

Of the 25 hyps, the *interface* faults (not the R-producer WIP): the call arm uniquely takes **Corr
exploded** (`hfrpc`/`hdefs`/`hmem` piecewise, LowerConforms.lean:355) while siblings take `hcorr`
whole — un-explode it; the six resume pins (`hrespc`/…/`hresvalidjumps`) should be **projection
lemmas** of `resumeAfterCall result pd`; `htail` should use a `_lowered` wrapper as the gas/sload
arms already do (LowerDecode.lean:710/921). Leave `hargs`-opacity and the oracle pins to the producer
track. *Touches a producer file — batch with 2A/2B.*

---

## Phase 3 — renames & cosmetic (after Phase 1 settles Spec)

- **3A (D6), namespace/folder portion LANDED:** the version namespace and directory tier are gone;
  `Drive/` and `Realisability/` are role-named top-level directories. Remaining independent cleanup:
  `GasOracle` → `GasStream`, delete the `Trace` alias (Semantics.lean:76-78), and replace `(T,C,D)`
  positional threading with a `Streams` record.
- **3B** folder charters: `Assembly/` → `CfgSim/` (nothing assembles bytes); `Decode/` →
  `CodeGeometry/`. Do with 3A.
- **5.13 grab-bag** as encountered: unify the 4 staging namespaces; retire the vestigial `WellFormed`
  single-use in DefsSound.lean:143 (name collision with the new `WellFormed` — **rename one**, flag
  now); `slotOf` docstring's nonexistent base offset (Lowering.lean:132-134); consider `lower :
  Program → Option ByteArray` (D12) once 2A lands (garbage-in → `none`).

---

## Phase 4 — post-exp005 merge (with exp003) — OUT OF SCOPE NOW

Recorded so nothing is lost, per "merge everything when exp005 finishes":
engine relocation (#2, ~5,800 ln, D10), generic byte-geometry → exp003 (#9), exp003 surface drift
(5.11: `Hoare.lean:27` false promise, `Behaves` zero consumers, `Spec.lean` stale audit wrapper),
`Machinery.lean` split (#10), and the **Asm layer extraction** (target-architecture §6, Phase 5) —
which subsumes 2B and is the final home for `Loc`/`Alloc` placement and the pc/offset budgets.

---

## Suggested landing order

1. **1A** (honesty sweep) — now, independent.
2. **1B + 1C** (WellFormed/budgets + Spec hoist part 1) — the flagship-honesty + R6-blocker-half win.
3. **1D, 1E** — structural tidy, green-parallel (defer #5 into 2A).
4. **producer-quiescent window → 2A + 2B + 2C + 2D** as one coordinated value-channel batch.
5. **3A remainder + 3B** — remaining renames, after Spec settles.
6. Phase 4 at the exp005→real-thing merge.

1A–1E run alongside the R11 producer; Phase 2 is the only hard ordering constraint (don't churn the
value channel under an active producer edit).
