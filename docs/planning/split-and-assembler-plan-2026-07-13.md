# Clean split + assembler — plan (2026-07-13)

Status: **PLAN — not executed.** Companion to `consolidate-under-evm-plan-2026-07-13.md`
(fold/consolidation) and `exp005-ir-vs-generic-classification.md` (the split inventory).
Branch `refactor/fold-bytecode-layer` @ `823214a3` (flagships closed, axiom-clean).

## The unlock (why now)

The split-and-assembler work is **Phase 4/5 of the settled target architecture**
(`experiments/005_ir_lowering/docs/target-architecture-2026-07-02.md` §6/§7;
`docs/review/tour-2026-07-09/07-assembler.md`). Both were gated behind **R11 producer
closure**: the assembler tour doc's binding rule was *"nothing to build until the R11
producer closes"* and *"Phase 5, strictly after Phase 3."* As of the fold, all three
flagships are closed and axiom-clean `[propext, Classical.choice, Quot.sound]` (verified
by fresh build) — **R11 is closed, the gate is open.**

Two independent confirmations line up:
- The 2026-07-02 taxonomy measured exp005 as ~20% misplaced engine theory + ~57%
  frame-level lowering machinery + **<10% actual IR content**.
- Our 2026-07-13 signature-level classification independently found **~⅔ EVM-generic,
  ~⅓ strictly-IR**, and that the generic mass forms reusable bytecode theories.

Same conclusion from two methods: the split is real and mostly generic.

## Target end-state

**EVM package** (`EVM/`, lib `Evm` + `BytecodeLayer`) exports the settled five-file
surface, all IR-free:
1. `BytecodeLayer/Exec.lean` — big-step `Exec params code O` (wraps `Runs`+halted+observe);
   the flagship restates frame-free through it. Absorbs the per-opcode/CALL/CREATE effect
   bricks and clean-halt envelopes.
2. `BytecodeLayer/Exec/Recorder.lean` — `runWithLog` + event-indexed runs + adequacy; the
   "reconstruct an EVM run from recorded oracle streams" engine.
3. `BytecodeLayer/Exec/Invariants.lean` — self/account-presence, find-mono, clean-halt,
   per-op envelopes as laws; the `CallsCode`/`CreateResolves` seam surfaced once.
4. `BytecodeLayer/Asm.lean` — **the assembler**: structured `AsmProgram` + verified
   `assemble`, with the decode/jumpdest/landing geometry proven ONCE. Home of placement
   nondeterminism. (Phase C below.)
5. `BytecodeLayer/Exec/CyclicSim.lean` — the IR-agnostic gas-descent cyclic-sim driver.

**IR package** (exp005, `Lir` name kept for now) proves only IR-shaped obligations:
`lowerAsm : Program → AsmProgram`, per-statement effect sims, the coupling invariant's
*semantic* fields (`storage`/`defsSound`/`wellScoped`/`memAgree`), the value-channel policy,
and the oracle ties — "a substrate-free IR proof" the canonical IR can re-target.

## How the classification's clusters map onto the surface

| generic cluster (from classification) | → surface file |
|---|---|
| CALL/CREATE effect oracles, per-opcode `sim_*`, clean-halt bricks (`Frame/Call,Create`, `Frame/Match` B-part, `Materialise/CleanHaltExtract`, memory-spill algebra) | **Exec** |
| recorder/trace engine (`Spec/Recorder`, `RecorderLemmas`, `CheckedStep`, `SegmentedEval`, `Machinery` `RecorderCoupled` core, `WitnessParams` checker) | **Recorder** |
| self/account-presence, modellable-step / no-call-create (`Drive/CallPreservesSelf`, `SelfPresent` B-part, `Decode/Modellable`) | **Invariants** |
| code geometry / "assembler correctness" (`Decode/` layout, anchors, segAligned, jumpValid, boundaryReach, decodeLower; `CfgSim/LowerDecode`; `MatDecLower`) | **Asm** |
| cyclic drive boundary-walk (generic part of `Drive/DriveSim`, `ReachesBoundary` walk) | **CyclicSim** |
| shared aliases `Observable/CallStream/CreateStream/GasOracle/World` (today in `Spec/Semantics`) | hoist first (precursor) |

## Sequencing (decisions locked with Eduardo 2026-07-13)

**Order = split in place first, THEN fold; assembler is a follow-up; Asm v1 minimal.**
Rationale for split-before-fold: the split is entirely about the exp005→exp003 boundary
(generic mass moves *down* into `BytecodeLayer`); EVM is not involved until the fold. So we
build the five-file surface inside the still-separate `bytecode_layer` package, then fold the
*finished* surface into EVM as one mechanical move.

```
Phase 0  scrub Lir from the exp003 engine        (still first — part of splitting cleanly)
Phase B  split in place: exp005 generic → exp003 five-file surface   (packages still separate)
Phase A  fold exp003 (now holding the full surface) → EVM/BytecodeLayer   (one clean move)
Phase C  the assembler                            (follow-up, strictly after B)
Phase D  canonical IR                             (later, out of scope)
```

### Phase 0 — Scrub `Lir` from the exp003 engine  *(first)*
The 6 `BytecodeLayer/Hoare/` files carrying `namespace Lir`/`LirLean.MemAlgebra` get renamed
into `BytecodeLayer.Hoare.*`; sweep the ~15 exp005 reference sites. (Consolidation plan Phase 0.)

### Phase B — The clean split in place (non-assembler surface)  *(the bulk)*
Build `Exec`/`Recorder`/`Invariants`/`CyclicSim` inside the exp003 `bytecode_layer` package by
relocating the EVM-generic clusters *down* from exp005, re-indexed off `lower prog` where
already generic. Packages stay separate throughout; exp005 keeps `require bytecode_layer`.

- **B0 — Precursor: hoist shared aliases.** Move `Observable`, `CallStream`, `CreateStream`,
  `GasOracle`, `World := Word → Word` out of `Spec/Semantics.lean` into a shared EVM home
  (they're structurally EVM-generic). Nothing else can migrate cleanly until this lands.
- **B1 — Whole-file clean migrations (13 files).** Move as-is (support defs travel with
  them): `Frame/StorageErase`, `Frame/Call`, `Frame/Create`, `Drive/CallPreservesSelf`,
  `RecorderLemmas`, `CallRealises`, `CheckedStep`, `SegmentedEval`, `MatDecLower`,
  `CleanHaltExtract`, `Spec/Seams`, `Words`, `Spec/Recorder` (dominantly generic).
- **B2 — Mixed-file splits (14 files).** Split along the cut-lines in the classification
  doc: extract the generic theory to the surface file, leave a thin IR adapter in exp005.
  Highest-value: split `Realisability/Machinery` into a generic `RecorderCoupled`/boundary
  engine (→ Recorder) + IR adapter (`matRunsC`/`termTies'`/`callRealises`, stays). Also
  `Materialise/*` (spill substrate → Exec, value-channel core stays), `Drive/SelfPresent`,
  `Frame/Match`, `WitnessParams`.

Each B-step green-gated (`lake build` + `WIP` + flagships axiom-clean) or revert.

### Phase A — Fold exp003 (with the full surface) → EVM  *(mechanical, after B)*
Now that `BytecodeLayer` holds the whole five-file surface, fold it into `EVM/BytecodeLayer/`
as one move: add the `lean_lib`, drop the exp003 lakefile + `require evm` edge, re-point
exp005's `require` to `evm`. (Consolidation plan Phase 1, resequenced to here.)

### Phase C — The assembler  *(follow-up; strictly after B, matches "Phase 5 after Phase 4")*
De-fuse the assembler out of the IR (detailed below). Largest single bet, churns exactly the
`Decode/` files. Operates on the consolidated EVM tree (post-fold).

### Phase D — Canonical IR  *(later, out of scope here)*
The new IR targets `AsmProgram`; the thin adapters left by B2/C are what it re-implements.

## Phase C in detail — the verified assembler

### What exists (fused). `Spec/Lowering.lean` already *is* an assembler:
`emitStmt`/`emitTerm` emit byte lists; labels resolve via a two-pass `offsetTable`
(prefix-sum of `blockLen`); `PUSH4` fixed-width dest keeps the measuring pass well-defined;
`lower = encode ∘ emit`. Its correctness is the ~3.6k-line `Decode/` geometry, all stated
over `lower prog` — unusable by a second IR.

### The layer (refresh of tour §2, drift-corrected):
```
inductive AsmInstr | push (v : UInt256) | op (o : StraightOp)     -- no pc-affecting ops in a body
inductive AsmTerm  | stop | ret | jump (dst : Label) | branch (dst thenL elseL : Label)
structure AsmBlock   where body : List AsmInstr ; term : AsmTerm
structure AsmProgram where blocks : Array AsmBlock ; data : Array ByteArray   -- data segs: v2

def assemble : AsmProgram → ByteArray          -- JUMPDEST-prefixed blocks + offset table
def entryPc  : AsmProgram → Label → ℕ
def cursorPc : AsmProgram → Label → ℕ → ℕ

-- static geometry, proven ONCE about `assemble`:
theorem assemble_decode_at  : instrAt p L i = some ins → decode (assemble p) (cursorPc p L i) = some (opcodeOf ins)
theorem assemble_validJumps : validJumpDests (assemble p) 0 = entryPcSet p
theorem assemble_boundary_reach : …

-- the cursor judgment that hides Corr's four geometric fields (pc_eq/code_eq/validJumps_eq/stack_nil):
def AtCursor (p : AsmProgram) (fr : Frame) (L : Label) (i : ℕ) (stk : List UInt256) : Prop

-- dynamic landing, proven ONCE:
theorem jump_landing   : AtCursor p frT L (bodyLen p L) [] → termOf p L = .jump dst →
                         CleanHaltsNonException frT → ∃ fj, Runs frT fj ∧ AtEntry p fj dst ∧ EffectFree frT fj
theorem branch_landing : …
```

### The retarget (the whole point):
`Lir.lowerAsm : Program → AsmProgram` keeps all of Lir's materialisation policy (the
`matCache` byte segments become `AsmInstr.push`/`.op` sequences); `assemble` owns layout,
`JUMPDEST` placement, and label resolution. Then **`lower = assemble ∘ lowerAsm` via a
definitional-equality (or `rfl`-lemma) bridge to today's `emit` fold, so the closed
conformance proof survives unmodified.** Corr's four geometric fields collapse into one
`AtCursor` fact; the semantic fields stay Lir's.

### Drift to fix before starting (tour §6):
- `assemble_no_create` is **dead as specced** — CREATE2 is now an emitted opcode; replace
  with the localized "descents exactly at emitted sites" predicate over the boundary walk.
- The landing algebra has drifted into `Corr`: the live fact is
  `Sim/SimTerm.lean:corr_at_jumpdest_landing`, Corr-fused. Phase C must **de-fuse** it into
  the `AtCursor`-shaped `jump_landing` + a trivial IR-side transport (not a ready-made move).
- Treat the tour's §2.4 signatures as 2026-07-02 sketches, not a frozen spec.

### Future-proofing to smuggle in (target-arch §7) — but keep v1 minimal:
- Replace the `slot' = slotOf tw` overfit pins (`CfgSim/LowerConforms` ~1289/1312) with a
  `ValidPlacement` parameter *during* the split (those conjuncts get rewritten anyway).
- Design the boundary walk with a data-suffix in mind (data-after-code commitment);
  `SegAlignedSafe` is unsound over a data suffix — rescope to pc-reachability (same work as
  the R6 `hrb` residual).
- Keep v1 at Lir's 16-opcode alphabet + empty-stack boundaries; **defer any `IRLang`
  typeclass / opcode-alphabet generalization until a second IR exists** (let its needs drive
  it, not speculation).

## Risks (from the tour doc's own honest critique)

1. **Re-indexing is a rewrite, not a file move.** Every `Decode/` statement is *indexed* by
   Lir syntax (`flatBytes prog`, `pcOf prog`, `matCache prog`); extraction restates them over
   `assemble p`. Mitigant: a chunk *evaporates* — the `SegAlignedP` alignment tower exists
   only because `emit` yields opaque byte lists; `assemble` output is instruction-aligned by
   construction, and the `matExpr`-recursion lemmas become definitional once operand segments
   are structured `AsmInstr` lists. Net reusable mass < "~4,100 lines move."
2. **Prototype the `assemble ∘ lowerAsm` defeq bridge EARLY** — it constrains `assemble`'s
   definition to Lir's current fold shape (matCache byte granularity, two-pass offset table).
   Achievable but must be proven before committing the migration order.
3. **Verification cost.** Every step rebuilds the full `WIP` cone — slow. Green-gate each;
   a bounded box run fits (as with the fold).

## Decisions locked (Eduardo, 2026-07-13)

1. **Ordering:** split in place first, then fold (Phase 0 → B → A → C). The split works the
   exp005→exp003 boundary; EVM is untouched until the finished surface folds in as one move.
2. **Scope:** Phase B (Exec/Recorder/Invariants/CyclicSim) lands as a discrete milestone;
   Phase C (Asm) is a separate follow-up.
3. **Assembler v1:** minimal — Lir's 16-opcode alphabet, empty-stack boundaries; smuggle in the
   `ValidPlacement` + data-after-code hooks but defer any `IRLang` typeclass / alphabet
   generalization until a second IR exists.
