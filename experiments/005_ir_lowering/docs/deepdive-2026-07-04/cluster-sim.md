# Deep dive: the per-block simulation cluster (`Sim*` + `CleanHaltExtract`)

Audit date: 2026-07-04. Files: `LirLean/SimStmt.lean`, `LirLean/SimStmts.lean`,
`LirLean/SimTerm.lean`, `LirLean/CleanHaltExtract.lean`. Read-only; no `.lean` modified.

## Cluster verdict (headline)

This cluster is the **L4 per-block, gas-aware simulation engine** ("Corr bricks") of the
plan. It is **live, load-bearing, and SHARED by the cyclic flagship** — not acyclic-only.
The proof of sharing is concrete: `V2/DriveSim.lean` (the cyclic drive walk, imported by the
flagship's `V2/RealisabilitySpec.lean` via `V2.DriveSim`) consumes `sim_stmts_block`
(DriveSim.lean:242/268/332/417), `SimStmtStep` (DriveSim.lean:229…679), and
`corr_at_jumpdest_landing` (DriveSim.lean:337/423); and `CleanHaltExtract`'s `next_*_of_cleanHalt`
family is called **directly inside the flagship file** `V2/RealisabilitySpec.lean`
(:1415, :1650, :1668, :1689, :1759, :1781, :1796, :1913, :1935, :1995, :2022, :2034, :2064, :2600).
So the primer's claim "L4 sim engine is shared by the cyclic flagship via `sim_cfg`" is
verified, and the "delete Acyclic → drop the engine" hope is correctly rejected. The `Corr`
structure (SimStmt.lean:103) is the central invariant threaded end-to-end (LowerDecode,
LowerConforms, DriveSim=cyclic, RealisabilitySpec=flagship, Drive/Headline).

Everything in these four files is `sorry`/`axiom`-free (the sole sorry-carrier is the WIP
`RealisabilitySpec.lean`, not this cluster).

---

## File 1 — `LirLean/SimStmt.lean` (Layer C: the `Corr` bundle + per-statement arms)

**Purpose (plan-grounded).** Layer C of the general `lower_conforms` grind: define the
per-statement state-correspondence invariant `Corr` (the V2-native fusion of `Match`'s M1/M2/M3/M5
clauses + `DefsSound` (B3) + the `MemRealises` value channel) and prove, per statement shape, that
one IR `EvalStmt` step is matched by the `Runs` segment of that statement's lowered bytes,
re-establishing `Corr` at `pc+1` with an empty working stack. The value/gas/call/sload channels
are the single uniform spill mechanism (`MemRealises`), per uniform-spill-alloc.

| decl | kind | role | callers |
|---|---|---|---|
| `pcOf_succ` (:77) | theorem | shared-infra (internal): statement-cursor pc advance, re-established by every arm | internal to all arms; no external |
| `Corr` (:103) | structure | shared-infra / terminal-for-flagship: THE per-statement invariant | LowerDecode, LowerConforms:265…, DriveSim:90/235… (cyclic), RealisabilitySpec:409/634… (flagship), Drive/Headline:165 |
| `Corr.validJumps_lower` (:141) | theorem | shared-infra: structural discharge of the former `TermTies` validJumps ties | LowerDecode:473 (edge_jump caller) |
| `emitStmt_assign_remat` (:150) | theorem | shared-infra (internal): zero-length emit for rematerialised assign | `sim_assign` (:218) |
| `emitStmt_assign_slot` (:166) | theorem | shared-infra: spilled-assign emit length | LowerDecode:74/1113/1215/1297/1454 (the `_lowered` wrappers) |
| `emitStmt_sstore` (:177) | @[simp] theorem | shared-infra: sstore emit shape | `sim_sstore_stmt`; simp |
| `sim_assign` (:200) | theorem | **terminal brick** (Corr arm 1, remat): consumed by `sim_cfg` | LowerConforms:493/499/505/511/517 |
| `selfStorage_eq_storageAt` (:247) | theorem | shared-infra (internal): storage-lens bridge | sstore/call arms |
| `sstore_executionEnv` (:258) | theorem | shared-infra (internal): env-invariance of `State.sstore` | sstoreFrame_* below |
| `sstoreFrame_{code,validJumps,addr,canMod,pc,stack,memory,activeWords}` (:262–:299) | @[simp] theorems | shared-infra: SSTORE post-frame accessor reductions | `sim_sstore_stmt`; simp |
| `SstoreRealises` (:318) | def | incremental-toward `sim_cfg`: the honest SSTORE runtime side-condition (stipend gate + EIP-2200 bound + self-present) | `sim_sstore_stmt` (:372), LowerDecode:155, LowerConforms:455 |
| `sim_sstore_stmt` (:346) | theorem | **terminal brick** (Corr arm 2): gas envelope DERIVED from clean-halt via two chained `materialise_runs_of_cleanHalt` | LowerDecode:188 (`sim_sstore_stmt_lowered`) → cyclic |
| `popFrame_{canMod,memory,activeWords}`, `mstoreFrame_addr` (:550–:562) | @[simp] theorems | shared-infra: Route-B call-tail post-frame reductions | `sim_call_stmt`; simp |
| `sim_call_stmt` (:576) | theorem | **terminal brick** (Corr arm 3, Route-B, full Corr) — the 28-hyp shape lemma | LowerConforms:355 (call arm of `sim_cfg`) → cyclic |
| `sim_assign_gas` (:893) | theorem | **terminal brick** (Corr arm 1′, spilled gas, Phase B) | LowerDecode:1237 (`sim_assign_gas_lowered`) |
| `sim_assign_sload` (:1055) | theorem | **terminal brick** (Corr arm 1″, spilled sload, Phase C) | LowerDecode:1509 (`sim_assign_sload_lowered`) |

**On the `sim_call_stmt` 28-hypothesis smell (judged, per task).** It is a **genuine shape
lemma, not refactorable away**, and it is honest. Reading the body (:660–:864): the hypotheses
are the irreducible seams of an external CALL threaded through Route-B — the arg-push run + its
memory pins (`hargs`/`hcallpc`/`hcallmem`/`hcallactive`), the returning-call witness
(`CallReturns`/`resumeAfterCall`), the realised post-state pin `hst'` (the consumed call-stream
head IS this call's recorded `evmCallOracle` result — this is the oracle seam, not a cheat), the
top-level-frame facts (`.call`-kind, code=lower, canMod), and the Route-B tail bundle `htail`
(MSTORE-to-slot / POP, decode+gas+memory-expansion). The proof genuinely re-establishes the FULL
`Corr` including the `memAgree` heart (:790–:864): the just-bound result slot gets coverage +
readback = flag via `mstore_reads_back`, and every other bound slot survives the disjoint MSTORE
via `mstore_preserves_slot_grow` + `slot_windows_disjoint`. The hypotheses are all consumed; none
is vacuous. The only defensible reshape is *packaging* (bundle the ~9 `htail`/resume pins into a
structure), which is cosmetic, not a soundness change. **Not a simplification I can defend as
removing content.**

Note the `htail`/`hstash` "memory channel stated as `.memory` bytes + `.activeWords`, NOT full
`toMachineState`" comments (:638–:643, :910–:914): this is a correctness point, not a smell — the
GAS/PUSH charges drop gas, so a full-`toMachineState` equality would be unsatisfiable; only the
bytes+activeWords (what `Corr`/`MemRealises` read) are honest. Consistent across the call, gas, and
sload arms.

---

## File 2 — `LirLean/SimStmts.lean` (Layer D: statement-list glue)

**Purpose.** Glue Layer C along a whole block's statement list by `Runs.trans`, threading `Corr`
(crucially its `stack_nil`) statement-to-statement. Route B closed the call gap, so it ranges over
**all** statements (no call-free side condition). Layer C's per-statement bundles are abstracted
into one hypothesis `SimStmtStep` at the exact altitude of the Layer-C conclusion.

| decl | kind | role | callers |
|---|---|---|---|
| `SimStmtStep` (:66) | def | shared-infra: the per-cursor abstraction of the three Layer-C arms | LowerConforms:461/973/1215, DriveSim:229…679 (cyclic) |
| `sim_stmts_drop` (:91) | theorem | shared-infra (internal): general suffix induction, the actual workhorse | `sim_stmts` (:142), `sim_stmts_block` (:158) |
| `sim_stmts` (:132) | theorem | **unused convenience restatement** ("block-from-pc form"); thin wrapper of `sim_stmts_drop` | **none** (only doc mentions) — see SIMPLIFICATION CANDIDATES |
| `sim_stmts_block` (:149) | theorem | terminal/shared: `pc=0` whole-block form, the form Layer E/F consume; re-derives from `sim_stmts_drop` directly (NOT via `sim_stmts`) | LowerConforms:986/993/999/1012/1022, DriveSim:242/268/332/417 (cyclic) |

---

## File 3 — `LirLean/SimTerm.lean` (Layer E: block-terminator simulation)

**Purpose.** From the terminator-cursor frame Layer D delivers, run the lowered terminator bytes to
either **halt** matching the IR halt (E1: stop/ret) or **run to the successor entry frame**
re-establishing `Corr` at `(succ, 0)` (E2: jump/branch). Scope is full-observable for stop
(world+result) and ret (world+returned value; the ret arm now runs its own epilogue), world-channel
via `resultStorageAt_endFrame_success`.

| decl | kind | role | callers |
|---|---|---|---|
| `pcOf_eq_termOf` (:86) | theorem | shared-infra: terminator cursor = `termOf` anchor bridge | LowerConforms:580, LowerDecode:277…838, RealisabilitySpec:1496…1842 (flagship) |
| `resultStorageAt_endFrame_success` (:109) | theorem | shared-infra (internal): success-halt world bridge (`endCall` commit) | `sim_term_halt_stop`/`_ret` |
| `resultOutput_endFrame_success` (:137) | theorem | shared-infra (internal): result-channel (output) bridge | `sim_term_halt_stop`/`_ret` |
| `jumpFrame_*` / `jumpdestFrame_*` / `jumpiFallthroughFrame_*` (:150–:241) | @[simp] theorems | shared-infra: control-flow post-frame accessor reductions | E2 bricks; simp |
| `sim_term_halt_stop` (:262) | theorem | **terminal brick** (E1 stop, full observable) | LowerConforms:594 |
| `sim_term_halt_ret` (:310) | theorem | **terminal brick** (E1 ret, full observable — world AND value) | LowerDecode:289 (`_lowered`) |
| `pcOf_zero` (:487) | theorem | shared-infra (internal): successor entry cursor = offset+1 | `corr_at_jumpdest_landing` |
| `corr_at_jumpdest_landing` (:498) | theorem | shared-infra: the shared E2 JUMPDEST-landing tail | DriveSim:337/423 (cyclic), LowerConforms:1137 |
| `jump_to_block` (:539) | theorem | shared-infra (internal): shared PUSH4;JUMP;JUMPDEST tail of jump + branch-else | `sim_term_edge_jump` (:651), `sim_term_edge_branch` |
| `sim_term_edge_jump` (:623) | theorem | **terminal brick** (E2 jump) | LowerDecode:473 (`_lowered`) |
| `sim_term_edge_branch` (:666) | theorem | **terminal brick** (E2 branch, both arms) | LowerDecode:752 (`_lowered`) |

---

## File 4 — `LirLean/CleanHaltExtract.lean` (Track 1: clean-halt ⟹ gas/mem envelope producer)

**Purpose.** The **producer** that turns a `CleanHaltsNonException fr` witness (the remaining run
reaches `.success`/`.revert`, never `.exception`) into the per-opcode gas + memory-expansion
envelopes the reshaped `StmtTies'`/`TermTies'` ties consume. This is what lets the GAS/SLOAD/term
arms DERIVE their runtime envelopes instead of supplying them (killing the vacuous universals). Root
of this cluster's clean-halt chain: `CleanHaltExtract → MaterialiseCleanHalt → SimStmt → SimStmts →
SimTerm`, AND directly consumed at the assembly layer (LowerDecode/LowerConforms) and inside the
flagship (RealisabilitySpec).

Structure (grouped; all shared-infra or incremental toward the envelope/next family):

| group | decls (lines) | role | callers |
|---|---|---|---|
| §1 per-op OOG/inv bricks | `stepFrame_{gas,push,sload,add,lt}_{oog,inv}`, `stepFrame_mload_{oogNone,oogMem,oogVL,inv}`, `stepFrame_{jump,jumpdest,jumpi}_{oog,inv}` (:82–:181, :204–:408, :892–:1043) | incremental-toward the dichotomy/next layer (unfold `charge` if-branch) | consumed by the dichotomy lemmas below (in-file) |
| §2 core | `halted_runs_eq` (:408), `next_of_cleanHalt_continuing` (:425) | shared-infra: a halted frame Runs only to itself; the non-exception-forces-step core (12 in-file uses) | in-file everywhere; `next_of_cleanHalt_continuing` also RealisabilitySpec:1415 (flagship) |
| §3 dichotomy | `stepFrame_{gas,push,sload,mstore,add,lt,mload,jump,jumpdest,jumpi_taken,jumpi_fallthrough}_dichotomy` (:444–:1070) | incremental-toward the `next_*` family (each used once, in its `next_*`) | in-file only |
| §4 next extractors | `next_{gas,push,sload,mstore,add,lt,mload,jump,jumpdest,jumpi_taken,jumpi_fallthrough}_of_cleanHalt` (:520–:1098) | **terminal-for-flagship**: the workhorse extractors | LowerDecode (jump/branch landing producers), MaterialiseCleanHalt (:94…362), RealisabilitySpec (:1650…2600, flagship), `next_gas` at RealisabilitySpec:2600 |
| §5 stepsTo helpers | `stepsTo_gasFrame` (:671), `stepsTo_pushFrameW` (:679), `stepsTo_sloadFrame` (:765) | incremental-toward the two envelopes below | in-file only (`*_envelope_of_cleanHalt`) |
| §6 envelopes | `gas_envelope_of_cleanHalt` (:696), `sload_envelope_of_cleanHalt` (:785) | **terminal brick**: the full residual `sim_assign_gas/sload_lowered` consume | LowerConforms:531 / :485 |

Every `next_*_of_cleanHalt` is consumed (checked: `next_add`/`next_lt`/`next_mload` — only 1 in-file
occurrence each — are used externally in MaterialiseCleanHalt.lean:285/362/163). No dead extractor.

---

## Internal dependency sub-DAG + cross-cluster edges

```
                 CleanHaltExtract   (root of this cluster's clean-halt chain)
                    │        │
     (via MaterialiseCleanHalt, MatDecLower — outside cluster)
                    │        └────────────► LowerDecode / LowerConforms / RealisabilitySpec
                    ▼
                 SimStmt  ── imports: MaterialiseRuns, MaterialiseCleanHalt,
                    │                  V2.CallRealises, Engine.CleanHalt (all outside)
                    ▼
                 SimStmts
                    ▼
                 SimTerm  ── also imports: JumpValid, DecodeAnchors, RecorderLemmas,
                                          StashTail, Engine.MemAlgebra (outside)
```

- **Intra-cluster edges:** `SimStmt → SimStmts → SimTerm` (linear). `CleanHaltExtract` is NOT
  imported by SimStmt/SimStmts/SimTerm directly; it reaches SimStmt transitively via
  `MaterialiseCleanHalt` (which imports CleanHaltExtract and is imported by SimStmt).
- **Exit edges (who consumes this cluster):**
  - `LowerDecode.lean` imports `SimStmt`, `SimTerm`, `CleanHaltExtract` — assembles the `_lowered`
    wrappers (feeds `sim_sstore_stmt`, `sim_term_*`, `sim_assign_{gas,sload}` their decode/clean-halt
    bundles) and the `{jump,branch}_landing_of_cleanHalt` producers.
  - `LowerConforms.lean` imports `CleanHaltExtract` (transitively SimStmt/SimTerm via LowerDecode) —
    hosts `sim_cfg`, consumes `sim_assign`, `sim_stmts_block`, `SimStmtStep`, `corr_at_jumpdest_landing`,
    the two envelopes.
  - `MaterialiseCleanHalt.lean` imports `CleanHaltExtract` — the gas-FOLD `materialise_charge_le_of_cleanHalt`.
  - `V2/DriveSim.lean` (cyclic drive) — `SimStmtStep`, `sim_stmts_block`, `corr_at_jumpdest_landing`, `Corr`.
  - `V2/RealisabilitySpec.lean` (flagship, WIP) — `Corr`, `pcOf_eq_termOf`, the `next_*_of_cleanHalt`
    family, `next_of_cleanHalt_continuing`, ported inline landing/epilogue extractors.
  - `V2/Drive/Headline.lean` — `Corr`, `SimStmtStep`.
- **Entry edges (this cluster's own imports):** Spec (defs), Engine/ (CleanHalt, MemAlgebra),
  Materialise* (MaterialiseRuns/MaterialiseCleanHalt/MatDecLower), Decode/CFG (JumpValid,
  DecodeAnchors), Recorder (RecorderLemmas), StashTail, V2.CallRealises.

---

## SIMPLIFICATION CANDIDATES (conservative; evidence attached)

1. **`sim_stmts` (SimStmts.lean:132) — unused convenience restatement. NEEDS CONFIRMATION.**
   Repo-wide grep finds zero callers of the middle "block-from-`pc` form"; the only consumed forms
   are `sim_stmts_drop` (the induction) and `sim_stmts_block` (the `pc=0` whole-block form), and
   `sim_stmts_block` re-derives from `sim_stmts_drop` **directly** (:158), not through `sim_stmts`.
   The decl body is `:= sim_stmts_drop hsim hss hcorr hcs hrun` — a pure alias. It is defensible to
   delete, BUT its docstring bills it as "the Layer-D headline as the plan states it," so it may be
   retained deliberately as the plan-facing statement. Recommend confirming with the plan owner
   before removing; do not treat as dead.

2. **Stale axiom-guard docstrings — cruft cleanup (not code).**
   `CleanHaltExtract.lean:41` asserts "Every top-level result carries a `#print axioms` guard line,"
   but the file contains **zero** `#print axioms` (verified). Guards are centralized in `Audit.lean`
   (which prints axioms for downstream consumers like `materialise_runs_of_cleanHalt`,
   `jump_landing_of_cleanHalt`, `sim_assign_sload_lowered`). `SimStmts.lean:163` similarly ends with a
   dangling "Build-enforced axiom-cleanliness guard for the D-layer `sim_stmts` deliverable" comment
   with no guard beneath it. These are stale-comment sweeps (the "just fix cruft" standard), not
   soundness issues.

3. **NOT candidates (guarding against a shallow pass):**
   - The four frame-accessor `@[simp]` families (`sstoreFrame_*`, `popFrame_*`/`mstoreFrame_addr` in
     SimStmt; `jumpFrame_*`/`jumpdestFrame_*`/`jumpiFallthroughFrame_*` in SimTerm) look duplicative
     but are distinct post-frame constructors (SSTORE vs POP/MSTORE vs JUMP/JUMPDEST/JUMPI-fallthrough)
     — each is separately needed by its arm's `Corr` re-establishment. Keep.
   - `sim_call_stmt`'s 28 hypotheses are all consumed and honest (see File 1 analysis). Bundling is
     cosmetic; there is no content to remove.
   - The `.memory`+`.activeWords`-instead-of-`toMachineState` memory channel in the call/gas/sload
     tails is a soundness requirement (full equality unsatisfiable under gas drop), not looseness.
