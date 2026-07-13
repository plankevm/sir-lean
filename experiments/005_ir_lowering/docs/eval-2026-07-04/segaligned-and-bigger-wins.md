# SegAligned de-dup + ranked structural wins (eval 2026-07-04)

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Read-only audit. Every claim cites `file:line`. Context: 51 `.lean` files, **25 518 LOC** total
(`find LirLean -name '*.lean' | wc -l` = 51; `cat | wc -l` = 25518). The three SegAligned files
are 1379 LOC = **5.4 % of the whole tree**, so this is not a rounding-error target.

---

## Part 1 — The SegAligned triplication

### 1.1 Verdict: YES, a genuine parameterized triple-duplication

`SegAligned` (`JumpValid.lean:78`), `SegAlignedSafe` (`NoCreateBytes.lean:50`),
`SegAlignedLowering` (`BoundaryReach.lean:135`) are **the same inductive** — an
instruction-aligned byte list (each opcode byte followed by exactly `pushArgWidth` immediate
bytes) — differing only by a per-instruction-head predicate `P` on the `cons` constructor:

| inductive | file:line | `cons` extra field | predicate `P (parseInstr byte)` |
|---|---|---|---|
| `SegAligned` | `JumpValid.lean:80-83` | (none) | `True` |
| `SegAlignedSafe` | `NoCreateBytes.lean:52-56` | `hsafe` (`:54`) | `parseInstr byte ≠ CREATE ∧ ≠ CREATE2` |
| `SegAlignedLowering` | `BoundaryReach.lean:137-141` | `hop` (`:139`) | `IsLoweringOp (parseInstr byte)` |

The **entire supporting ladder** is re-proven three times, line-for-line identical modulo the
extra predicate argument threaded through each proof:

- Composition: `SegAligned.append/nonpush/push` (`JumpValid.lean:91,100,107`) ≡
  `SegAlignedSafe.append/nonpush/push` (`NoCreateBytes.lean:72,82,90`) ≡
  `SegAlignedLowering.append/nonpush/push` (`BoundaryReach.lean:151,160,167`).
- Emit-ladder: `segAligned_{emitImm,emitDest,slot,materialiseExpr,materialise,emitStmt,emitTerm,
  emitBlockBody,loweredBlock}` (`JumpValid.lean:169-347`) ≡ the `segAlignedSafe_*`
  (`NoCreateBytes.lean:172-348`) ≡ the `segAlignedLowering_*` (`BoundaryReach.lean:219-382`).
  Compare `segAligned_emitStmt` (`JumpValid.lean:243`), `segAlignedSafe_emitStmt`
  (`NoCreateBytes.lean:243`), `segAlignedLowering_emitStmt` (`BoundaryReach.lean:282`): identical
  `cases`/`append` skeleton, the only per-opcode difference is `.nonpush byte (by decide)` vs
  `.nonpush byte (by decide) (by decide)` — the extra `(by decide)` discharging `P`.
- Interior transport: `reaches_safe_of_segAlignedSafe` (`NoCreateBytes.lean:112-162`) ≡
  `reaches_loweringOp_of_segAlignedLowering` (`BoundaryReach.lean:177-215`) — the same induction
  ("any boundary reached strictly inside a matched segment satisfies `P`"), byte-identical bar the
  `∃ byte … ∧ P (parseInstr byte)` conclusion.
- Whole-program lift: `segAlignedSafe_flatBytes` (`NoCreateBytes.lean:353`) ≡
  `segAlignedLowering_flatBytes` (`BoundaryReach.lean:386`).
- Forgetful maps: `SegAlignedSafe.toSegAligned` (`NoCreateBytes.lean:59`) ≡
  `SegAlignedLowering.toSegAligned` (`BoundaryReach.lean:144`) — both **unused** (grep: zero
  callers).

**What is NOT duplicated** (must be kept once each):
- `reaches_of_segAligned` (`JumpValid.lean:120`) — "reaches the segment *END*", predicate-free.
  Distinct from the two interior-`P` transports; stays with the base notion.
- The E3 headline chain in JumpValid (`lower_get?_eq:358`, `offsetTable_succ:364`,
  `lower_match_block:383`, `reaches_block_offset:413`, `block_offset_validJump:471`,
  `decode_at_block_offset_jumpdest:497`) — the jump-validity payoff, ~160 LOC, unique.
- BoundaryReach's converse jump-dest lemmas `mem_validJumpDestsAuxNat_inv:51` /
  `reachesBoundary_of_mem_validJumpDests:90`, `reachesBoundary_nextInstr:109`, and the
  `IsLoweringOp:125` predicate def + `Decidable` instance — ~90 LOC, unique R6 bricks.
- The per-tower headline restatements (`decode_reachable_boundary_{some,notCreate}`
  `NoCreateBytes.lean:391,413`; `reachable_boundary_loweringByte`,
  `decode_reachable_boundary_loweringOp` `BoundaryReach.lean:402,415`) — small, become mono/decode
  corollaries after the collapse.

### 1.2 Cleanest de-duplication: one predicate-parameterized inductive + `.mono`

The strongest lever is that **`IsLoweringOp` is the strongest of the three predicates**: every
one of the 16 lowering ops (`BoundaryReach.lean:126-129`) is non-CREATE, and `True` is implied by
anything. So prove the ladder ONCE at the tightest predicate and derive the others by monotonicity.

Introduce a new low base module (e.g. `LirLean/SegAlignedTower.lean`, imported by all three, sitting
just above `DecodeLower`), containing:

```lean
inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop where
  | nil  : SegAlignedP P []
  | cons (byte : UInt8) (imm rest : List UInt8)
      (himm : imm.length = (pushArgWidth (parseInstr byte)).toNat)
      (hP   : P (parseInstr byte))
      (hrest : SegAlignedP P rest) : SegAlignedP P (byte :: (imm ++ rest))

theorem SegAlignedP.mono {P Q} (h : ∀ op, P op → Q op) : SegAlignedP P s → SegAlignedP Q s
-- append / nonpush / push   (once, generic in P)
-- reaches_end_of_segAlignedP        (predicate-free reach-END; the old reaches_of_segAligned)
-- reaches_P_of_segAlignedP          (interior-P transport; the merged reaches_{safe,loweringOp})
-- IsLoweringOp + Decidable          (moved down here)
-- the emit-ladder proven ONCE at P := IsLoweringOp (the 16-op discharge via `by decide`)
-- segAlignedP_flatBytes  : SegAlignedP IsLoweringOp (flatBytes prog)
```

Then the three towers collapse to definitions + one-line corollaries:

```lean
abbrev SegAligned         := SegAlignedP (fun _ => True)
abbrev SegAlignedSafe     := SegAlignedP (fun op => op ≠ .System .CREATE ∧ op ≠ .System .CREATE2)
abbrev SegAlignedLowering := SegAlignedP IsLoweringOp
-- flatBytes facts for the weaker two: `segAlignedP_flatBytes.mono isLoweringOp_notCreate`, etc.
```

`NoCreateBytes.lean`'s two headlines (`decode_reachable_boundary_{some,notCreate}`) become thin
corollaries of `reachable_boundary_loweringByte` post-composed with `IsLoweringOp op → notCreate op`.
JumpValid keeps `reaches_end_of_segAlignedP` usage + its E3 headline. BoundaryReach keeps only its
unique converse/`IsLoweringOp` bricks + R6 headlines.

### 1.3 Real savings

- **LOC:** 1379 → ~650. **~700–730 LOC removed** (two full copies of the ~300-LOC
  inductive+composition+ladder+transport core, plus one of the two interior transports, plus both
  unused `toSegAligned` maps). This matches the DAG doc's "~1400 → 600" lever
  (`00-proof-plan.md:311-312`). The lead's "~800" is the honest ceiling; ~700 is the conservative
  floor.
- **Files:** 0 removed by the minimal collapse (all 3 keep their unique headlines) — or **−1 file**
  if `NoCreateBytes.lean` is reduced to nothing but its two mono-corollaries and those are absorbed
  into `BoundaryReach.lean`. That requires repointing `Decode/Modellable.lean:426` (the only external
  consumer, of `decode_reachable_boundary_some`) from `NoCreateBytes` to `BoundaryReach` and
  flipping the current `BoundaryReach imports NoCreateBytes` edge. Modest surgery; optional.

### 1.4 Risk + gate

- **Blast radius is contained to the three files.** No external module *constructs* the inductives:
  every `SegAligned*` / `IsLoweringOp` occurrence outside the three files is a **docstring/comment**
  (`Modellable.lean:23`, `DriveSim.lean:124`, `RealisabilitySpec.lean:2338,2349,2450`), never an
  `import`-level constructor use. External consumers use only the HEADLINE theorems
  (`Modellable.lean:426` → `decode_reachable_boundary_some`; the flagship uses
  `reachable_boundary_loweringByte`/`reachesBoundary_*` as opaque lemmas).
- **Risk: LOW–MEDIUM.** Mechanical, but getting the generic `induction`/`.mono` plumbing and the
  `abbrev`-vs-`def` choice right is fiddly (the `.nonpush`/`.push` smart constructors must supply
  `hP := trivial` for the `True` instance). No semantic change; all three headlines stay LIVE.
- **Gate: NONE — do now.** This lives entirely in the **default-build** decode cluster, has zero
  dependency on the flagship's open sorries or the R-series roadmap, and all three files are already
  green + axiom-clean (`JumpValid.lean:513`, `NoCreateBytes.lean:427`, `BoundaryReach.lean:431`).
  Re-run the build + the three axiom guards to confirm.

---

## Part 2 — Honest ranking of ALL structural wins

The lead is right that ~700 LOC on one dedup is not transformative against a 25 k-LOC / 51-file
tree. But SegAligned is in fact the **largest confirmed do-now LOC win**; every comparably-sized
item is gated on a roadmap decision. Ranked by (value × do-now-ability):

### Tier 1 — Do now, low risk, default build

| # | Win | LOC | Files | Risk | Gate |
|---|---|---|---|---|---|
| 1 | **SegAligned tower dedup** (Part 1) | ~700–730 | 0 (or −1) | LOW-MED | none |
| 2 | **Split `RealisabilitySpec` §6 `exProg` witness** into own file (`:2975-3613`, ~640 LOC, ~20 `private` self-contained lemmas; exits only `exProg` + `wellLowered_exProg`) | 0 removed, but the 3874-LOC flagship file → ~half | +1 | LOW (pure relocation) | none |
| 3 | **Delete dead acyclic capstone** `Lir.lower_conforms` (`LowerConforms.lean:1188`, ~63 LOC) **+ stranded** `runWithLog_messageCall` (`RecorderLemmas.lean:143`, ~20 LOC) — zero callers, plan-of-record delete | ~85 | 0 | LOW | delete together |
| 4 | **Small confirmed orphans:** `SmallStep.IRConf` + `Program.stmtAt` (genuinely dead, zero refs), `assign_sload_sub_key` (`LowerDecode.lean:68`), `chargeOf_imm_const` (`MaterialiseGas.lean:141`), `realisedCall_projection` (`SelfPresent.lean:55`) | ~40–60 | 0 | LOW | trivial |

Tier-1 total addressable now: **~900–1000 LOC removed + the biggest file halved**, all low-risk,
no roadmap dependency. That is a real ~3–4 % of the tree and the single biggest file made legible.

### Tier 2 — Medium LOC, needs one confirmation each

| # | Win | LOC | Risk | Gate |
|---|---|---|---|---|
| 5 | **`IRRun.lean` acyclic-CFG construction** — `CFGAcyclic`/`TermRankLt`/`Term.succs`/`runFrom_exists*`/`irRun_exists*`; zero code callers, DriveSim (`:17,54`) explicitly retires the static rank for the dynamic `totalGas` measure | ~150 | LOW | keep the `StmtDefinable`/`stmtsPost` fold; delete acyclic half only |
| 6 | **`jump_landing_of_cleanHalt` / `branch_landing_of_cleanHalt`** (`LowerDecode.lean:486,769`, ~410 LOC) — vestigial `Plus`-thread; flagship re-derives the landing walk inline (`RealisabilitySpec ~:1741-1899`) | ~410 | MED (green, axiom-guarded; natural home if flagship factors the walk back out) | confirm flagship will not cite them |

### Tier 3 — Largest potential deletion, but a ROADMAP decision (not dead code)

| # | Win | LOC | Risk | Gate |
|---|---|---|---|---|
| 7 | **`Drive/Headline.lean` (~200 LOC) + `SelfPresent.lean` §3-§4 `GasLogAligned`/`SloadLogAligned` (~230 LOC)** — entirely unreferenced; header designates them "retained salvage" for the R0 reshape | ~430 (single largest deletion) | HIGH uncertainty | lead must decide whether the R-series gas/sload alignment channel is still the plan; if the drive is reshaped away from them, delete |

### Tier 4 — Whole-v1-layer prune (decl-level, not file-level)

| # | Win | LOC | Risk | Gate |
|---|---|---|---|---|
| 8 | **v1 IR-semantics decls superseded by V2 twins** — `Match.lean` `evalExpr:89`, `IRState:49`, `IRHalt:60`, `setLocal:101`, `bindCallResult:110`, the `Match` STRUCTURE (`:125`, never instantiated), `lower_preserves_discharge/stop/ret` (`:550,562,577`, zero callers); each has a LIVE twin in `Spec/Semantics.lean`. The FILES stay (sim_* bricks + oracles are live) | ~100–150 | MED (must not conflate with the live frame-local `sim_*` bricks / `evmCallOracle`) | confirm no worked-example anti-vacuity artifact (Law/Call) still needs v1 |

### Tier 5 — Zero-LOC structural hygiene

| # | Win | Effect | Gate |
|---|---|---|---|
| 9 | **Engine/ namespace graduation** — 5/8 files in `Lir` despite being IR-agnostic exp003 theory; `AccountMap.lean:26,55,68` self-flags `-- RELOCATE to exp003` | 0 LOC; unblocks exp003 extraction | exp003 relocation decision |
| 10 | Fold `Spec/Seams.lean` → `Audit.lean` | −1 tiny file | cosmetic; `Spec/Conformance.lean` is a DELIBERATE tombstone (`LirLean.lean:50`) — NOT a win |

### Explicitly NOT wins (guard against a shallow second pass)

- The ~30 frame-accessor `@[simp]` families (`sstoreFrame_*`/`popFrame_*` in SimStmt;
  `jumpFrame_*`/`jumpdestFrame_*`/`jumpiFallthroughFrame_*` in SimTerm) — distinct post-frame
  constructors, each load-bearing.
- `chargeOf` mirroring `materialiseExpr` opcode-for-opcode — the intentional B1/B2 gas split.
- The covered-slot MLOAD zero-expansion argument duplicated between `MaterialiseRuns.lean:896-940`
  and `MaterialiseCleanHalt.lean:122-177` — **intentional anti-cycle** (`cluster-materialise.md:310`).
- `CallRealisesS` (`RealisabilitySpec.lean:406`) vs `Lir.CallRealises` (`LowerConforms.lean:261`) —
  real near-copy, but NAMED Phase-3 debt gated on R0b; cross-file, not now.

---

## Bottom line for the lead

SegAligned is worth doing — it is the **single largest confirmed, ungated, low-risk LOC win**
(~700 LOC, contained blast radius, default build). But it is not the whole story: the biggest
*structural* lever is **splitting the 3874-line `RealisabilitySpec` (#2)**, and the biggest
*potential deletion* is the gated `Drive/Headline` + `SelfPresent §3-4` salvage (#7, ~430 LOC,
needs a roadmap call). Bundling Tier-1 (#1–#4) gives ~900–1000 LOC removed plus the flagship file
halved, all without touching the open-sorry surface — the sensible first sweep.
