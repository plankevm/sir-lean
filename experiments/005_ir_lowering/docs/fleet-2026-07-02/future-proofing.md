# Future-Proofing Review — exp005 vs. memory, allocator, data segments, multi-IR

*High-level design track (1 of 5), 2026-07-02. All paths relative to `/Users/eduardo/workspace/evm-semantics/.worktrees/ir-lowering/experiments/005_ir_lowering/` unless noted. Signature-level review; no proofs were run.*

**One correction to the brief before anything else:** the brief says "the current lowering spills tmps to STORAGE slots; real code spills to MEMORY." That is not what the code does. The lowering already spills to **EVM memory**: `slotOf t = t.id * 32` (Lowering.lean:132), the spill stash is `materialise(e) ++ PUSH slot ++ MSTORE` (Lowering.lean:186-187), readback is `PUSH slot; MLOAD` (Lowering.lean:142), and the coupling clause is `MemRealises` — an `mload`-readback tie on the frame's `MachineState.memory` (MaterialiseRuns.lean:601-606), carried as `Corr.memAgree` (SimStmt.lean:135). This matters a lot for the verdicts below: exp005 already has a working *bytecode-memory* value channel with coverage/activeWords bookkeeping and transport lemmas. What it does **not** have is IR-*visible* memory, and its memory placement is a single hardcoded deterministic function. The future-proofing question is therefore not "can memory be modeled at all" (the hard EVM-side bricks exist) but "can the IR see memory, and can placement stop being `t.id * 32`."

---

## 1. Current-design stress test

Legend: **ACCOMMODATES** (works with additive changes), **BENDS** (shape survives; a set of lemmas/interfaces must be generalized), **BREAKS** (a design commitment must be replaced).

### 1a. Memory as IR state — BENDS

- `IRState` is `{ locals : Tmp → Option Word, world : World }` with `World = Word → Word`, the self-storage lens only (V2/Machine.lean:44-52). No memory field; `Expr.slot` is explicitly lowering-only and `evalExpr (.slot _) = none` (IR.lean:66-73, Machine.lean:127). Adding `mem` to `IRState` is additive; `Observable` (Machine.lean:210-214) correctly should *not* grow a memory field (memory dies with the frame), so the observable boundary is untouched.
- **The collision point is the spill region.** IR-visible memory and spill slots share one EVM `MachineState.memory`. `MemRealises` asserts the frame's bytes at `slotOf t` equal the spilled local (MaterialiseRuns.lean:601-606); an IR `MSTORE` landing on a spill slot falsifies it. So `Corr` must carry a *partition*: spill windows ∪ IR-object windows pairwise disjoint. Today disjointness is implicit in `slotOf`'s injectivity; it must become an explicit validity predicate on the allocation (see §2).
- **The transport lemmas are the real bend.** `MemRealises.transport` requires memory bytes **unchanged** (`hmem : fr'.memory = fr.memory`, MaterialiseRuns.lean:634-651), which holds because today only spill stashes write memory and only at def-sites. Once IR statements write memory, every transport/envelope lemma keyed on frozen bytes must weaken to "agrees outside the written window" — a frame-rule shape. Similarly the `StmtTies` sload arm *supplies* activeWords-flatness of materialise sub-runs (`hawk`, LowerConforms.lean:1303-1306); IR MSTOREs introduce genuine memory expansion, so the gas-envelope derivations (`chargeMemExpansion`, `M_32_eq_self_of_covered` at MaterialiseRuns.lean:658) get new real cases. Bounded, mechanical, but touches many files (MaterialiseRuns, MemAlgebra, SimStmt, CleanHaltExtract envelopes).
- **Calls.** `emitStmt .call` pushes five literal zeros for the memory windows (Lowering.lean:191-197) and `CallOracle := Word → Word → World → (World × Word)` (Machine.lean:96). Real calldata-from-memory means the oracle gains an IR-visible input (`calldata bytes`) — exactly the extension ir-design-v3 §7 pre-declares ("a FUNCTION oracle of the call's IR-visible inputs (callee, calldata)", docs/ir-design-v3.md:115). ACCOMMODATES at the interface; the `CallRealises` bundle and `CallRecord` (V2/RunLog.lean:68-72) grow fields.

### 1b. Non-deterministic allocator — BENDS, and one line BREAKS

- The **seam already exists**: `Alloc := Tmp → Option Loc`, `Loc = remat e | slot n`, and the mechanism `emit : Alloc → Program → List UInt8` is genuinely alloc-parametric (Lowering.lean:92-101, 401-405). `lower = encode ∘ emit (allocate prog)` (Lowering.lean:413) is a one-point instantiation. This is good design — the uniform-spill-alloc pivot bought exactly the right hook.
- But the **proof layer is pinned to the one placement**. `MemRealises` quantifies over `defsOf prog t = some (.slot slot)` (fine), yet `StmtTies` demands `∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw` — twice (LowerConforms.lean:1289, 1312). That conjunct literally says "the placement is `t.id * 32`". Every theorem threading it holds *only* for the canonical allocation. This is the single most overfit line in the study relative to Philogy's asks: it must be replaced by a `SoundAlloc`/`ValidPlacement` predicate (injective, 32-byte-window-disjoint, addressable: the `slot + 63 < 2^64` and `slot < 2^numBits` bounds already appear at LowerConforms.lean:1300, 1322 and generalize verbatim). BREAKS as written; the fix is localized to the tie/`Corr` vocabulary because everything downstream consumes slots only through these predicates.
- Determinism of `offsetTable` layout arithmetic is *not* threatened: `stmt_byte_anchor` and the prefix-sum machinery (Layout.lean:94-203) depend only on emitted lengths, and spill addresses are `PUSH32` immediates, which are fixed-width — the same trick that makes `emitDest`'s `PUSH4` placement-independent (Layout.lean:44-58). So byte-layout proofs survive any placement unchanged.

### 1c. UB on undefined access — ACCOMMODATES (the pattern already exists twice)

The codebase already handles "no obligation outside the domain" in two ways, both honest:

- **Stuckness**: `evalExpr` returns `none` on undefined tmps and the `EvalStmt` rules simply don't fire (Machine.lean:120-196); the headline *constructs* the IR run from a definability supply `RunDefinable` (`StmtDefinable`/`stmtsPost` fold, V2/IRRun.lean:61-114, 257-269).
- **Scope premise**: `CleanHaltsNonException` excludes exception runs (CleanHalt.lean:41-107; audit §5 confirms non-vacuous).

Memory UB slots into the first pattern: an MLOAD of an unallocated object/offset has **no rule**, so a UB run has no `RunFrom` derivation and the theorem claims nothing. The domain premise becomes a `MemDefinable` clause inside the `RunDefinable`-style supply. See §2 for the honesty discipline.

### 1d. Data segments + CODECOPY at non-deterministic offsets — BENDS, with one genuine hazard

- **Layout arithmetic**: if data segments are placed strictly **after** all code blocks, `flatBytes_block_split`/`offsetTable`/`pcOf` anchors (Layout.lean:116-139, 163-203) are untouched — the code prefix decomposition never sees the suffix. A second prefix-sum table (`dataOffsetTable`) reuses the same pattern. Interleaved data would force re-proving every anchor; **recommend data-after-code as a design commitment**.
- **The hazard is the instruction-aligned boundary walk.** `NoCreateBytes.lean` proves no-CREATE via `SegAlignedSafe` — every instruction *head* reachable by the static alignment walk parses non-CREATE (NoCreateBytes.lean:1-58), feeding `lower_modellable`'s clause 1 (V2/Modellable.lean:17-30). Arbitrary data bytes are **not** instruction-aligned (a stray `0x7f` swallows 32 bytes; a stray `0xf0` *is* CREATE at a walked head). So the whole-code `SegAlignedSafe` framing is unsound to extend over a data suffix. The fix is the one already in flight for other reasons: scope the walk by **pc-reachability** (`AtReachableBoundary`, the Track-A residual in Modellable.lean:27-30) — execution never jumps past the last block's terminator into data (no emitted offset points there; `validJumpDests` may mark a spurious `0x5b` in data, but forward simulation never takes that edge). Verdict: BENDS, and the bend is the *same work* as discharging the existing `hrb`/pc-reachability residual, so it should be designed once, jointly.
- **IR-visibility of the offset**: the segment's bytecode offset is placement-dependent, so the IR must treat it as un-computable — Philogy's non-determinism ask. It is *not* a good fit for the oracle/log channel (it is static per placement, not a runtime observation); it is a **parameter**: IR semantics takes an environment `ρ : DataSeg → Word` for `Expr.dataOffset`, and the conformance theorem instantiates `ρ` from the layout while quantifying `∀ valid layout` (§2). CODECOPY itself needs IR memory first — **data segments are downstream of memory**.

### 1e. IR #2 with different constructs — BENDS (pattern reusable, code monomorphic)

Everything in `Lir.*` is written against the concrete `Program/Stmt/Expr/Term` (IR.lean:54-112). Genuinely IR-agnostic and reusable today: the recorder (`driveLog`/`runWithLog`/`realisedGas`/`realisedCall`, V2/RunLog.lean:156-283 — pure bytecode, zero IR content), the clean-halt scope (CleanHalt.lean), the engine bricks (Phase-4 relocation to exp003, audit §7), and the `totalGas` cyclic-CFG measure (defined in exp003: `003_bytecode_layer/BytecodeLayer/Semantics/Interpreter/Measure.lean:64`). The conformance skeleton is *interface-shaped* already — `lower_conforms` consumes opaque `∀ L b, SimStmtStep/SimTermStep` (LowerConforms.lean:1208-1211) — but monomorphic in the IR types. A second IR re-instantiates: syntax, `evalExpr`/`EvalStmt` arms, `Corr` clauses, `StmtTies` arms, per-construct sims. That's the right cost model (see §4: don't typeclass this yet).

### 1f. Endomorphism (IR→IR) passes — ACCOMMODATES for statement, one real gap

`RunFrom` is parametric in the oracle `o` and trace `T` (Machine.lean:228), determinism exists (`RunFrom.det`, V2/Law.lean header), and observables are first-class. So `∀ o T O, RunFrom (opt p) o st T L O → RunFrom p o st T L O` is expressible **today with zero new infrastructure**, purely at IR level. Composition with the flagship also works structurally, because the headline's conclusion *surfaces* `RunFrom prog o st₀ T prog.entry O` (TieDischarge.lean:4328-4331) — a pre-lowering pass refinement plugs into it directly. **The gap: the positional gas stream.** `GasOracle = List Word` consumed head-first (Machine.lean:73-78, 174-176); any pass that adds/removes/reorders `assign t .gas` changes the stream alignment, so pass correctness must carry a trace-remap `f : Trace → Trace` (and, for call-reordering passes, note `CallOracle` is a *function*, so it composes — only the gas stream is order-fragile). This is the one place the settled log-fed-oracle decision has a multi-pass cost; it needs a stated discipline, not a redesign.

---

## 2. Non-determinism design

**Recommendation: (a) — lowering parameterized by a placement, theorem `∀ valid placement`, combined with an object-granular IR memory so placements are IR-unobservable.** Concretely:

```
structure Placement where            -- extends today's Alloc
  spill : Tmp → Option Nat           -- today: slotOf
  objBase : Obj → Nat                -- IR memory objects
  dataOff : DataSeg → Nat            -- data segments (later)
structure ValidPlacement (prog) (π) : Prop where
  disjoint : …                       -- all 32-byte/len windows pairwise disjoint
  addressable : …                    -- the existing slot+63 < 2^64 / < 2^numBits bounds
lower : Placement → Program → ByteArray
theorem conforms : ∀ π, ValidPlacement prog π → runWithLog (params π prog) fuel = some log →
    … (observe self log.observable).world = O.world ∧ RunFrom prog o st₀ T prog.entry O
```

Why (a) over the alternatives:

- **(b) existential placement** gives the compiler freedom but the *user* nothing about non-chosen placements, and — decisive here — Philogy's stated purpose is to *prevent users relying on offsets*. Under (a), `RunFrom` never mentions `π`, so the IR observable `O` is pinned **before** π is chosen; any program whose behavior varied with placement simply could not satisfy the ∀-theorem. Offset-independence is enforced by the theorem's *shape*, not by an extra lemma. (b) loses exactly this.
- **(c) relational/non-deterministic IR semantics** (addresses non-deterministic *inside* the IR step relation) is the CompCert-faithful option but destroys the determinism ladder (`RunFrom.det` — needed for the "*the* observable" reading, ir-design-v3.md §4.2), makes log-feeding ill-posed (which addresses did *this* run choose?), and buys nothing once memory is object-granular. Reject.

**CompCert comparison, honestly scoped.** CompCert's memory injections solve a harder problem: compiled code merges many source blocks into one stack frame, with permissions, frees, and pointer values flowing through integers. Our setting is strictly easier: no free, no permission changes, no pointer-to-word cast (make that UB/unrepresentable at IR level — allocator returns an abstract handle `Obj`; offsets within an object are concrete words, base addresses are not `Expr`-expressible). Then the "poor man's injection" is exactly one clause added to `Corr`:

```
memInj : ∀ o off v, st.mem o off = some v →
    covered (π.objBase o + 32*off) fr ∧ (fr.…mload (π.objBase o + 32*off)).1 = v
```

— which is `MemRealises` (MaterialiseRuns.lean:601-606) with `defsOf … = .slot slot` replaced by `π`-indexed objects. The coverage/activeWords/readback bookkeeping and `mload_covered_congr` (MaterialiseRuns.lean:614-627) carry over verbatim. A full injection (with unmapped regions and value-lessdef) is **not** needed unless/until Plank IR allows casting pointers to words; if it does, revisit — that's the one trigger for the heavyweight version.

**UB as "no obligation," stated honestly.** Make UB = stuckness (no `EvalStmt` rule for out-of-bounds/dead-object access), mirroring today's undefined-tmp treatment (Machine.lean:120-127). Then the conformance theorem's domain premise is not a new ambient hypothesis — it is the same `RunDefinable`-style *supply* the headline already consumes and the closure already constructs the run from (V2/IRRun.lean:257-346), extended with a `MemDefinable` clause threaded through `stmtsPost` exactly like `StmtsDefinable` (IRRun.lean:106-114). Two honesty guards, per the project's own policy:

1. **Decidability**: state `MemDefinable` so it is checkable by evaluation on a concrete program (the fold shape already is), so on the Phase-3-style concrete instantiation it is *discharged by `decide`/`#eval`*, never left as a supplied universal — this is what keeps it out of the "supplied hypothesis = sorry-debt" trap (audit §10).
2. **Non-vacuity witness**: every UB-scoped theorem ships with at least one concrete defined-run instantiation (the remediation plan's Phase-3 item 6 discipline, remediation-plan-2026-07-02.md:40).

Anti-pattern to avoid: stating UB-freedom as a property of the *bytecode* run (e.g. "no MLOAD outside activeWords") — that inverts the direction and makes the premise undischargeable without the theorem itself.

---

## 3. Memory model sketch

**IR-level memory: object-granular, word-granular within objects.**

```
structure Obj where id : Nat                       -- allocation handle
-- IRState gains:
  mem : Obj → Option (Nat → Option Word)           -- live objects; per-object partial word map
-- Syntax:
Stmt.alloc  (t : Tmp) (size : Nat)                 -- static sizes first; binds handle to t
Stmt.mstore (o : Tmp) (off : Tmp) (v : Tmp)        -- UB if o dead / off ≥ size
Expr.mload  (o : Tmp) (off : Tmp)                  -- none (stuck) if UB
```

Flat `Word → Word` memory is the wrong first move: it makes addresses IR-visible, which re-couples programs to placement and forces option (c) above. Object granularity is what makes ∀-placement free. Byte granularity can wait for calldata/CODECOPY (data segments can enter as read-only byte objects later).

**Lowering.** `Placement.objBase : Obj → Nat` (lowering-time, per the §2 shape); `mload (o, off)` → `materialise off ++ PUSH32 (objBase o) ++ ADD ++ MLOAD` (constant-offset case folds to one `PUSH32`, matching today's spill readback at Lowering.lean:142); `mstore` symmetric; `alloc` emits nothing (static placement) — a bump-allocator/free-pointer scheme is a later *endomorphism-pass* refinement, not a lowering concern. All base pushes are `PUSH32`, so emitted lengths are placement-independent and the entire offset-table layer (Layout.lean) is untouched — the same fixed-width argument as `emitDest` (Layout.lean:44-49).

**Coupling invariant (`Corr`, SimStmt.lean:103-135).** Changes:
- `memAgree : MemRealises …` generalizes: today's spill clause becomes the `spill` component; add the `memInj` clause of §2 for objects. One predicate, two index families, same coverage/readback shape.
- New static side-fact (in `ValidPlacement`, not per-state): spill ∪ object windows disjoint.
- `storage`, `pc_eq`, `code_eq`, `validJumps_eq`, `stack_nil`, `can_modify`, `defsSound`, `wellScoped` — all unchanged.

**Value channel: stays derived-from-run; no new oracle.** The litmus that falls out of ir-design-v3 §7 (docs/ir-design-v3.md:108-110): oracles exist for values that depend on *bytecode-only* state (gas counter, chain state). IR memory is deterministic IR-internal state — the IR computes every MLOAD result itself. So `RunLog` (V2/RunLog.lean:82-91) records **nothing new**; `realisedGas`/`realisedCall`/`observe` are untouched. Only the *placement* is quantified, and it is a parameter, not an oracle. This is worth writing down as a design rule: *state goes in `IRState`, observations go in the log, placements go in `∀`.*

**Survives untouched:** RunLog/recorder + adequacy (RunLog.lean:156-343); oracle interfaces (Machine.lean:73, 96); the CFG driver shape + existence ladder (IRRun.lean — new `EvalStmt` arms only); determinism ladder (new arms); Layout.lean byte arithmetic; CleanHalt scope; `totalGas` measure driver; all exp003 engine facts.
**Bends:** `Corr`/`MemRealises` (+clauses); `MemRealises.transport` and every frozen-bytes/flat-activeWords envelope lemma (MaterialiseRuns.lean:634; LowerConforms.lean:1303-1306) → frame-rule form; `StmtTies` (+2 arms, ~the size of the existing sload-spill arms); `sim_stmt` (+2 arms — the existing spill-stash sims `sim_assign_gas`/call-result MSTORE are literally the template); `StmtsDefinable`/`RunDefinable` (+`MemDefinable`).
**Breaks (must be replaced, small):** the `slot' = slotOf tw` pins (LowerConforms.lean:1289, 1312).

---

## 4. The reusable conformance kit

**The checklist a new IR instantiates** (each item names the exp005 exemplar):

| # | Kit item | Exemplar | Status for reuse |
|---|---|---|---|
| 1 | Oracle-parameterized relational big-step semantics + observable boundary | V2/Machine.lean | pattern; re-derive per IR |
| 2 | Determinism ladder (`EvalStmt.det` → `IRRun.det`) | V2/Law.lean | pattern |
| 3 | Existence/definability ladder (`StmtDefinable`/`stmtsPost`/`RunDefinable` + CFG measure) | V2/IRRun.lean:61-346 | pattern |
| 4 | Lowering = policy/mechanism/backend split (`Alloc`/`emit`/`encode`) | Lowering.lean:388-413 | reusable shape |
| 5 | Byte-layout prefix-sum + cursor anchors | Layout.lean:94-203 | reusable **verbatim** if the block/`JUMPDEST` convention is kept |
| 6 | Coupling invariant (`Corr`: pc/code/jumps/stack-boundary/storage-lens/mem channel) | SimStmt.lean:103 | pattern |
| 7 | Per-construct sims + `StmtTies`/`TermTies` + `simStmtStep_block` builders | LowerConforms.lean:1273, 1342 | pattern |
| 8 | Clean-halt scope | CleanHalt.lean:41-107 | reusable as-is |
| 9 | Cyclic-CFG gas-descent driver (`totalGas` + strong induction) | exp003 Measure.lean:64; V2/DriveSim.lean | reusable as-is after Phase 4 |
| 10 | Recorder + realised oracles + `observe` | V2/RunLog.lean | reusable **as-is** (bytecode-pure) |
| 11 | Concrete end-to-end instantiation (anti-vacuity witness) | Phase-3 item 6 | mandatory per IR |

**Generalize NOW (cheap, high leverage):** (i) execute Phase 4 (engine facts → exp003) — it *is* the kit's foundation move, already planned; (ii) retire the `slotOf` pin for a `SoundAlloc`/`ValidPlacement` parameter (§1b) — small blast radius, kills the worst overfit, and Phase 3's tie-reshape (remediation open Q3) touches those exact conjuncts anyway; (iii) write the checklist above into a `docs/conformance-kit.md` — documentation is the cheapest generalization and Philogy's actual interface.
**Defer:** a Lean-level `IRLang` typeclass/structure abstracting Stmt/step/Corr — heavy engineering against one data point; the `∀ L b, SimStmtStep` opaque-prop interface (LowerConforms.lean:1208) already gives the skeleton's parametricity where it matters. Abstract when IR #2 exists and its deltas are known.

**Endomorphism passes.** Statable purely at IR level today (§1f): pass correctness = `RunFrom (pass p) o st T L O → RunFrom p o st (remap T) L O` plus observable equality; composition with the flagship is structural because the headline concludes in `RunFrom`. Missing, in order of need: (1) the **trace-remap discipline** for gas-read-count-changing passes (or the cheap rule: "passes may not duplicate/eliminate `Expr.gas` reads," checked syntactically); (2) a stated **composition lemma** (one-day job once Phase 3 lands, because both endpoints exist); (3) a **post-condition vocabulary** for "IR→same-IR with better post-conditions" — nothing exists; recommend starting with decidable syntactic predicates on `Program` (e.g. "all mloads statically in-bounds," "no gas reads") rather than a semantic Hoare layer, matching the project's executable-discharge style.

---

## 5. Sequencing recommendation

**Close Phase 3 on the toy first; let memory/allocator/data-segments in immediately after, in the order alloc-generalization → memory → data segments; but smuggle two cheap generality guards into Phase 3 itself.** The realisability closure is the genuinely novel step no prior-art fork has built (remediation-plan-2026-07-02.md:9), its hard content — positional log alignment, per-cursor gas-value discharge — is orthogonal to memory, and doing it first on the small IR de-risks the method before the case count roughly doubles; starting memory now would also violate the finish-each-milestone-properly rule while the flagship is still a conditional. The honest cost of toy-first: the frozen-bytes transport lemmas and `StmtTies` arms written during Phase 3 will be revisited when IR MSTOREs land — that rework is bounded (the new arms are additive; the shapes are frame-rule generalizations, not replacements) **provided** two things are done inside Phase 3 while its tie-reshape is open anyway: (1) replace the `slot' = slotOf tw` pins with the `SoundAlloc`/`ValidPlacement` parameter (§1b — otherwise every closure lemma bakes in the one placement and the ∀-placement theorem later forces a re-walk); (2) design the pc-reachability discharge (`AtReachableBoundary`, already delegated) with the code-region/data-suffix boundary in mind (§1d — same proof, one extra hypothesis slot, saves redoing the boundary walk for data segments). Data segments strictly after memory (CODECOPY needs it); the endomorphism statement + composition lemma can land any time after Phase 3 at low cost and would be a quick, visible win for Philogy's multi-pass story.