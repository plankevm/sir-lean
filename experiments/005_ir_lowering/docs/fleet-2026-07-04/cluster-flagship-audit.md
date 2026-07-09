# Cluster audit — ASSEMBLY / FLAGSHIP / AUDIT layer (2026-07-04)

Scope: the top-of-cone files (WIP flagship + acyclic salvage + clean-halt producer +
reviewer-facing surface) and the cross-cutting "how many proof stacks" synthesis.
No `.lean` file was modified.

> **P8 status note (2026-07-08).** This audit predates the P8 well-formedness reshaping. Its
> claims that `Acyclic.lean`, `AcyclicWellFormed`, `wellFormedLowered_of_acyclic`, or `MatFueled`
> are live R9/flagship infrastructure are superseded. The public theorem shape is now
> `IRWellFormed` + `codeFits` + `stackFits`; `WellLowered` is rebuilt internally, and the
> rank/fuel definitions wait for P9 deletion.

## 1. File table

| File | LOC | Purpose | Key exports | Verdict | Simplification note |
|------|-----|---------|-------------|---------|---------------------|
| `LirLean/V2/RealisabilitySpec.lean` | 3874 | The WIP flagship + R0–R12 obligation skeleton; sole `sorry`-carrier; registered in non-default `WIP` lib | `WellLowered`, `StmtTies'`/`TermTies'`, `lower_conforms` (R11), `lower_conforms_exact`, `lower_conforms_gasfree`, `conforms_of_worldeq` (CLOSED), `exProg` + all `*_exProg` witnesses, R12a/b | **KEEP; SPLIT** | 3874 LOC in one file; 7 `/-! ## §` sections; natural fault line at §6 (the `exProg` witness ~900 LOC). See §4. |
| `LirLean/LowerConforms.lean` | 1260 | Layer F of the *green* sim core: `sim_cfg` (whole-CFG simulation) + the legacy F-layer `lower_conforms` bridge; **defines `WellFormedLowered`** | `sim_cfg` (line 970), `WellFormedLowered` (line 143), `simStmtStep_*`, `SimTermStep`, `lower_conforms` (line 1188, **DEAD**) | **KEEP FILE, delete one theorem** | NOT deletable as a file (lead's claim refuted). `sim_cfg` + `WellFormedLowered` are load-bearing. Only the top-level `lower_conforms` (1188, 73 LOC) is unreferenced dead code — prune it + its docstring. |
| `LirLean/Acyclic.lean` | 225 | legacy generic-`defs` rank/fuel support; no longer the P8 well-formedness route | `Acyclic`, `ExprRankLt`, `matFueled_tmp_of_acyclic` | **KEEP UNTIL P9** | The old `AcyclicWellFormed → WellFormedLowered` route is superseded by `IRWellFormed` + budgets rebuilding `WellLowered`; delete this file with the residual fuel stack in P9. |
| `LirLean/CleanHaltExtract.lean` | 1118 | Producer: from `CleanHaltsNonException fr` extract per-opcode gas/mem envelopes the §7 ties consume | `CleanHaltsNonException`, `cleanHaltsNonException_forward`, per-op `*_oog`/`*_inv`/`*_dichotomy`/`next_*_of_cleanHalt`, `gas_envelope_of_cleanHalt`, `sload_envelope_of_cleanHalt` | **KEEP** | Coherent, axiom-guarded, `sorry`-free. Highly regular per-opcode brick family (GAS/PUSH/SLOAD/ADD/LT/MLOAD/MSTORE/JUMP): could be macro-generated, but low priority. |
| `LirLean/RecorderLemmas.lean` | 153 | Proof companions of the recording interpreter, extracted so `Spec/Recorder.lean` stays definitions-only | `sloadRecord_eq_sloadCost`, `realisedCall_cons`, `driveLog_drive`, `runWithLog_drive`, `runWithLog_messageCall` | **KEEP** | Clean, purpose-built extraction (Wave 3 reorg). No change. |
| `LirLean/Audit.lean` | 62 | `#guard_msgs`/`#print axioms` net over the salvage layer; last import of `LirLean` root | 8 axiom-footprint guards | **KEEP** | Coherent post-2026-07-03. Correctly guards only the salvage decls; explicitly does NOT cover the WIP lib. `#check` signature-freeze for R11 is a deliberate TODO (once R11 lands). |
| `LirLean/Spec/Conformance.lean` | 24 | Tombstone stub — the vacuous re-export surface was deleted 2026-07-03 | (none — docstring only) | **KEEP as stub** or delete | Pure notice. Retained so the "canonical conformance path" resolves to an explanation, not a missing module. Defensible; could be deleted if no doc links to it. |
| `LirLean/Spec/Seams.lean` | 95 | The honest-seam reviewer surface: named wrappers for the 4 irreducible seams | `SelfPresent`, `CallPreservesSelf`, `PrecompilesPreservePresence`, `callPreservesSelf_of_precompiles`, `CallsCode`, `CleanHaltsNonException` | **KEEP** | Coherent and thin (each `def` = a rename of the real predicate). This is the correct reviewer altitude. No change. |

## 2. TWO HEADLINES?

**Refuted as stated.** There are not two peer headline *results*. There is **one flagship**
(the cyclic, ties-derived R11) sitting atop a **shared green simulation core**, plus **one
dead legacy top-level theorem**.

Statement-level comparison:

- **"Acyclic" headline** — `Lir.lower_conforms` (`LowerConforms.lean:1188`). A *conditional
  bridging lemma*, not a producer. It **consumes** the IR run as a hypothesis
  (`hir : V2.IRRun prog w₀ (realisedGas log) (realisedCall log self) O`) and **consumes** the
  per-block ties as hypotheses (`hstmts : SimStmtStep …`, `hterm : SimTermStep …`). Conclusion
  is only the **world equation** `O.world = (observe self log.observable).world` — not a
  `RunFrom` existential, not full `Conforms` (no `.result`). Its self-standing wrappers
  (`lower_conforms_acyclic*`, `lower_conforms_wf`) that *supplied* those ties were **already
  deleted** (Acyclic header lines 38–43; `Audit.lean` note). **It is currently unreferenced**
  (grep for term-level uses returns nothing) — dead code. The green `sim_cfg` in the same file
  is what is actually reused.

- **Cyclic gas-free flagship** — `Lir.V2.lower_conforms` (`RealisabilitySpec.lean:3705`) +
  `lower_conforms_exact` (3752) + `lower_conforms_gasfree` (3788). **Produces** the run:
  conclusion is `∃ O, RunFrom prog (entryState params) (realisedGas log) (realisedCall log
  recipient) prog.entry O ∧ Conforms params.recipient log O` — full `Conforms` (world **and**
  result, via the CLOSED `conforms_of_worldeq`, 3661). Ties are **DERIVED** from the run
  (R10a `stmtTies'_of_runWithLog` 3624, R10b `termTies'_of_runWithLog` 3642), not supplied.
  This is the WIP `sorry`-carrier: the single open blocker is the run-producer
  `runFrom_of_driveCorrLog` (3723–3746 `sorry`).

**Subsumption:** the cyclic flagship strictly dominates. The F-layer lemma's entire content
(a world equation, given a supplied run + supplied ties) is a strict sub-part of R11's
conclusion, and R11's downstream (`conforms_of_worldeq`) reuses the very same `sim_cfg`
machinery. There is nothing the F-layer top-level theorem proves that the flagship doesn't
subsume — it is legacy, not a competing guarantee.

**Cross-cutting "how many proof stacks":** three layers, one apex.
1. **Green sim core** (Layers A–F: `DecodeAnchors → … → SimStmt/SimTerm → SimStmts →
   LowerConforms`). Produces `sim_cfg` + `WellFormedLowered`. Shared, load-bearing.
2. **Green cyclic driver** (`V2.IRRun`, `V2.Modellable`, `V2/Drive/*`, `DriveSim`). Produces
   `lower_conforms_cyclic`/`_cyclic'` (`DriveSim.lean:624/666`) — green but **conditional on
   the same unconditional all-frames `SimStmtStep`/`SimTermStep` ties** the reshape deems
   effectively unsatisfiable, so green-but-vacuous. Uses `sim_cfg` internally
   (`DriveSim.lean:648`).
3. **WIP flagship** (`RealisabilitySpec`, `sorry`). Derives the ties (R10) and produces the
   run, killing the vacuity of stack 2. This is the only non-vacuous apex.

So: one true headline in progress, standing on two green substrates. The "acyclic vs cyclic"
dichotomy is a naming artifact (CFG-acyclicity, long since retired via `CFGAcyclic` deletion),
not two rival theorems.

## 3. EDGES THAT USED TO KEEP THE ACYCLIC STACK ALIVE

Reverse imports at the time of this audit: `Acyclic` was imported by **only**
`RealisabilitySpec`; `LowerConforms` by **`Audit`, `Acyclic`, `DriveSim`**. P8 supersedes the
`Acyclic` witness route; the table below records the old crossing and the P8 disposition:

| Edge | What is actually used across it | Load-bearing? |
|------|--------------------------------|---------------|
| `Acyclic → LowerConforms` | Historical: `WellFormedLowered` plus former `matFueled_*`/`bound_*` fields. P8: `WellFormedLowered` has no `MatFueled` fields and is rebuilt from `IRWellFormed` + budgets. | Superseded; keep only until P9 deletes the fuel stack |
| `DriveSim → LowerConforms` | `sim_cfg` (`LowerConforms.lean:970`), consumed at `DriveSim.lean:648`; plus `SimStmtStep`/`SimTermStep` types | YES — the entire cyclic flagship path runs through `sim_cfg` |
| `Audit → LowerConforms` | Transitive import chain + namespace so the guarded decls (`sim_assign_sload_lowered`, etc.) resolve; no direct symbol from the F-layer headline | Weak (transitive), but harmless |
| `RealisabilitySpec → Acyclic` | Historical `exProg` witness route through `AcyclicWellFormed` / `wellFormedLowered_of_acyclic`. P8 uses `IRWellFormed.defEnvOrdered` and `wellLowered_of_IRWellFormed` instead. | Superseded |
| `RealisabilitySpec → LowerConforms` | `WellFormedLowered` remains the internal `WellLowered.wf` adapter over fold layout; no public theorem premise exposes it. | YES, internally |

**Total deletion cost estimate for "delete Acyclic + LowerConforms":**

- The lead's request is **not achievable as a file deletion.** `LowerConforms` is load-bearing
  for the green cyclic driver, and `Acyclic` still houses residual fuel definitions until P9. To
  delete `LowerConforms` you would first relocate `WellFormedLowered`, the entire `sim_cfg` +
  Layer-F threading (`simStmtStep_*`, `SimTermStep`) that `DriveSim.lower_conforms_cyclic`
  consumes. To delete `Acyclic`, wait for P9's `materialiseExpr`/`MatFueled` sweep.
- **What IS safely removable:** exactly one dead theorem — `Lir.lower_conforms`
  (`LowerConforms.lean:1188`, 73 LOC + its docstring). It is unreferenced anywhere in the tree
  (its old wrappers are gone). Removing it, plus refreshing the `LowerConforms.lean` header
  (which still bills the file as the "capstone … `lower_conforms` grind") and the stale
  lakefile comment (`lakefile.lean:22–24`, still lists "four headlines
  `lower_conforms`/`lower_conforms_acyclic_cfg`/`lower_conforms_cyclic`/`_cyclic'`" — two of
  which no longer exist), is the real, ~80-LOC simplification hiding behind the "delete the
  acyclic stack" request.

## 4. SHOULD REALISABILITYSPEC BE SPLIT?

**Yes — one split, along the existing §6 boundary.** The file is 3874 LOC with 7 top-level
`/-! ## §` sections. Two cohesive halves:

- **The spec + obligations** (§1–§5, §7; ~2960 LOC): helper defs (`WellLowered`,
  `RunDefinableG`, shadowing-aware scoping), the recorder-restart coupling, the reshaped
  `StmtTies'`/`TermTies'`, exact-consumption `RunFrom*`, and R0–R11 (the flagships + the R6
  boundary walk + R7 recorder edges + `conforms_of_worldeq`). This is the reviewable spec.
- **The concrete witness** (§6, ~900 LOC, lines 2959–3600+): `exProg` and its ~25 discharge
  lemmas (`defsOf_exProg_eq`, `acyclic_exProg`, `acyclicWellFormedExProg`,
  `wellFormedLowered_exProg`, `runDefinableG_exProg`, `wellLowered_exProg`, `revalidatesPerBlock_exProg`,
  the `blockAt/toList_exProg*` decidable pins, etc.). This is the R9/R12 anti-vacuity machine —
  self-contained, `decide`-heavy, and conceptually distinct from the obligation statements.

Recommended: extract §6 into `LirLean/V2/RealisabilitySpecWitness.lean` (imports the spec
module), leaving R12a/R12b (`exProg_satisfies_hypotheses`, `exProg_nonvacuity`) either with
the witness or as a thin third file. This cuts the flagship spec to ~a manageable size and
isolates the `decide`-heavy witness (which is also where most compile cost lives).

**The 28-hypothesis `sim_call_stmt` smell:** still present, but it lives in
`LirLean/SimStmt.lean:576` (Layer C — NOT this cluster), with ~25 explicit named hypotheses
(`hb, hs, hfrpc, hargslen, hargs, hcallpc … htail`). RealisabilitySpec only references it
indirectly (docstrings at 404, 1353). It IS a shape-lemma smell (a monolithic per-call
contract), but it is not in the flagship file and reshaping it is a Layer-C task tracked
elsewhere. Flag it to the SimStmt-cluster owner, not here.

## 5. SIMPLIFICATION OPPORTUNITIES

1. **Delete the dead F-layer `Lir.lower_conforms`** (`LowerConforms.lean:1188`, ~73 LOC). It
   is unreferenced; `sim_cfg` (same file) is the only live export the cyclic path needs.
2. **Refresh two stale doc surfaces** exposed by (1): the `LowerConforms.lean` header (still
   calls the file the "`lower_conforms` capstone") and `lakefile.lean:22–24` (lists four
   headlines, two now nonexistent — `lower_conforms_acyclic_cfg` and the top-level
   `lower_conforms`). Per the "just fix cruft" memory, sweep these on the same change.
3. **Split RealisabilitySpec** at §6 (see §4) — the single highest-value structural change.
4. **`Spec/Conformance.lean`** — decide the tombstone's fate: keep as a documented stub or
   delete outright if nothing links to it. Low stakes either way.
5. **`CleanHaltExtract` per-opcode bricks** — the `*_oog`/`*_inv`/`*_dichotomy`/`next_*`
   family is mechanically regular across 8 opcodes; a `macro`/generator could shrink ~1000 LOC,
   but it is green and guarded — low priority, do not touch pre-flagship.
6. **Do NOT attempt to delete `Acyclic.lean` or `LowerConforms.lean` as files** — both are
   load-bearing (see §3). The lead's instruction is based on the outdated "two headlines"
   model; only the dead theorem in (1) is removable.
