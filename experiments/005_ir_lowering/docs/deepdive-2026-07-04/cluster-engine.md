# Deep-dive: the `Engine/` cluster (L1 — IR-agnostic EVM theory)

> **Plus-layer status (2026-07-13):** The vestigial Plus carrier and its orphaned helper declarations were deleted after both build cones and the flagship axiom gate passed. References below to the removed names and former module are historical descriptions, not live source pointers.


Audit date 2026-07-04. Read-only pass over the eight `experiments/003_bytecode_layer/BytecodeLayer/Hoare/*.lean` files.
Every decl signature and every load-bearing/questionable proof body was read; callers
were traced by repo-wide `grep -rn` over `LirLean/`, not just the import graph.

## Headline verdicts

* **Import-clean / IR-agnostic — confirmed.** Every Engine file imports ONLY the exp003
  bytecode layer (`Evm`, `BytecodeLayer.*`) or a sibling Engine file. Zero `import
  LirLean.Spec.*` / `LirLean.*` / any IR module. So Engine is a genuine reusable sublayer
  with **no upward (IR) import dependency** — it can graduate to exp003 as-is on the import
  axis.
* **Namespace leakage — the one real blemish.** The *content* is IR-agnostic but 5 of 8
  files sit in the experiment namespace `Lir` (`AccountMap`, part of `StepWalk`, part of
  `Descent`, `DriveMono`, `CleanHalt`). Graduation to exp003 requires renamespacing. The two
  files already in exp003-appropriate namespaces are `DriveRuns` (`BytecodeLayer.Interpreter`)
  and the inversion halves of `StepWalk`/`Descent` (`namespace Evm`). `AccountMap` carries
  explicit `-- RELOCATE to exp003 (audit §7)` markers on its three RBMap prims. `Charges` is in
  `Lir`, `MemAlgebra` in `LirLean.MemAlgebra`.
* **All eight files are `sorry`-free and axiom-clean** (`[propext, Classical.choice,
  Quot.sound]`). The only `sorry` tokens are inside docstrings asserting cleanliness. The WIP
  sorry-carrier is `RealisabilitySpec.lean`, not here. `MemAlgebra` even ships `#print
  axioms` build guards on its crux results.
* **The cluster is really 4 independent leaves + one 4-file chain**, not one monolith (see
  §sub-DAG). "Engine" is an altitude grouping, not a dependency component.

---

## Per-file sections

Role legend: **terminal-for-flagship** = consumed (transitively) by the in-progress
`Lir.lower_conforms`; **shared-infra** = building block used by multiple sibling lemmas in
the same file/cluster; **scaffold-experimental** = green + in build cone but no consumer yet,
by design a hook for a planned feature (first-class CREATE); **incremental-toward-X** = feeds a
single named lemma; **needs-confirmation** = plausibly superseded but retained as a checked
deliverable — flagged conservatively, NOT asserted dead.

### `BytecodeLayer/Hoare/AccountMap.lean` (145 LOC, `namespace Lir`)

Purpose: pure `Evm.AccountMap` presence bricks — the RBMap non-emptiness prims and the
arbitrary-address presence layer (`AccPresent`/`AccMono`) that the accMono dispatch walk
(`StepWalk`) and drive-run monotonicity (`DriveMono`) consume. Extracted verbatim from the
retired `TieDischarge.lean` monolith; marked for exp003 relocation.

| decl | kind | role | callers |
|---|---|---|---|
| `forM_from_nil` | theorem | shared-infra (RBMap `all₂`-vs-nil short-circuit) | `all2_nil_false`:62; `Drive/SelfPresent.lean` |
| `all2_nil_false` | theorem | shared-infra | `find?_some_ne_empty`:84; `Drive/SelfPresent.lean` |
| `find?_some_ne_empty` | theorem | shared-infra (find-hit ⇒ ≠∅) | `accPresent_ne_empty`:128; `Drive/SelfPresent.lean` |
| `AccPresent` | def | terminal-for-flagship (presence predicate) | `StepWalk`, `Descent`, `DriveMono`, `Spec/Seams`, `RealisabilitySpec`, `Drive/CallPreservesSelf` |
| `AccMono` | def | incremental-toward-`StepWalk`/`DriveMono` step framing | no external ref found (used only as the shape behind the `hmono` seams; see note) |
| `accounts_find?_insert_mono` | theorem | terminal-for-flagship (Brick A) | `StepWalk`, `Descent`, `DriveMono` |
| `accPresent_ne_empty` | theorem | shared-infra (Brick B) | `accMono_emptySwap`:142 (in-file) |
| `accMono_of_accounts_eq` | theorem | shared-infra (verbatim-accounts closer) | `StepWalk` |
| `accMono_emptySwap` | theorem | terminal-for-flagship (==∅ swap closer) | `DriveMono`:79 |

Note on `AccMono`: repo grep finds no *reference* to the name `AccMono` outside AccountMap.lean;
the `hmono` seams in `DriveMono`/`callPreservesSelf` are written as raw `∀ fr exec', … →
AccPresent … → AccPresent …` rather than through the `AccMono` abbreviation. So `AccMono` the
*definition* is currently ornamental (the `AccPresent`-transport it names is used everywhere, but
never via this abbrev). Conservative classification: incremental/vestigial-abbrev — needs
confirmation before removal (harmless, one line).

### `BytecodeLayer/Hoare/StepWalk.lean` (1336 LOC, `namespace Lir` + `namespace Evm`)

Purpose: THE per-opcode `.next` dispatch walk (CALLMONO Brick C) proving every non-halting
`stepFrame` step preserves (a) `executionEnv.address` and (b) account-presence at any tracked
`a`. This is what discharges `StepPreservesSelf` as a *theorem* (not a supplied hypothesis) for
every program. Also hosts the accounts/env framing prims and the halt-success presence family.

| decl | kind | role | callers |
|---|---|---|---|
| `charge_accounts_env` | theorem | shared-infra | `Descent`:60,71 + in-file |
| `chargeMemExpansion_accounts_env` | theorem | shared-infra | `Descent`:200 + in-file |
| `SelfAt` | def | terminal-for-flagship (self-presence pred) | `Drive/CallPreservesSelf`; in-file `stepFrame_next_self` |
| `resumeAfterCall_address` | theorem | shared-infra (`rfl` fact) | `CallPreservesSelf`, `RealisabilitySpec` |
| `resumeAfterCall_accounts` | theorem | shared-infra | `Descent`, `DriveMono`, `CallPreservesSelf` |
| `endCall_revert_accounts` | theorem | shared-infra | `DriveMono`:80, `Drive/SelfPresent` |
| `endCall_exception_accounts` | theorem | shared-infra | `DriveMono`:81, `Drive/SelfPresent` |
| `continueWith_next` | theorem | shared-infra (in-file, ~26 uses) | in-file dispatch arms only |
| `replaceStackAndIncrPC_accounts` | theorem | shared-infra | in-file |
| `accMono_replaceOfBase` | theorem | shared-infra | in-file |
| `sstore_accMono` | theorem | shared-infra (SSTORE arm closer) | in-file :287 |
| `tstore_accMono` | theorem | shared-infra (TSTORE arm closer) | in-file :318,773 |
| `dispatch_simple_arm_next_accMono` | theorem | shared-infra (simple-op template) | in-file (~10 arms) |
| `pushOp/unStateOp/charge_sstore/charge_tstore/unOp/binOp/ternOp/dup/swap/logArm/callArm/createArm/systemOp/smsfOp_next_accMono` | theorems | shared-infra (per-family `.next` arms) | in-file `dispatch_next_accMono` |
| `dispatch_next_accMono` | theorem | shared-infra (the whole dispatch) | in-file `stepFrame_next_*` |
| `stepFrame_next_execEnvAddr` | theorem | terminal-for-flagship | `CallPreservesSelf`, `RealisabilitySpec` |
| `stepFrame_next_accMono` | theorem | terminal-for-flagship (Brick C cap) | `CallPreservesSelf`, `DriveMono`:238, `BoundaryReach`, `RealisabilitySpec` |
| `stepFrame_next_self` | theorem | terminal-for-flagship (`a:=self` corollary) | `CallPreservesSelf` |
| `selfdestructOp/returnOrRevertOp/haltOp/systemOp_success_accMono` | theorems | shared-infra (halt-success arms) | in-file `stepFrame_halted_success_accMono` |
| `stepFrame_halted_success_accMono` | theorem | terminal-for-flagship (halt-success cap) | `CallPreservesSelf` |

The ~30 per-family `_next_accMono` arms are honest routine bodies (each unfolds one dispatch arm
and closes via `continueWith_next` / `dispatch_simple_arm_next_accMono` or the `sstore`/`tstore`
closer); they exist solely to assemble `dispatch_next_accMono`. Not dead — this is one proof
sharded by opcode family.

### `BytecodeLayer/Hoare/Descent.lean` (570 LOC, `namespace Evm` + `namespace Lir`)

Purpose: the per-kind CALL/CREATE descent structural facts (signal → begin → child run →
resume), plus the `DescentKind` interface unifying CALL and CREATE as ONE descent shape. The
CALL/CREATE `stepFrame` inversions are load-bearing for the drive presence walk; the
`DescentKind` bundle is scaffolding for Phase 3.5 first-class CREATE.

| decl | kind | role | callers |
|---|---|---|---|
| `callArm_needsCall_inv` | theorem | incremental-toward-`systemOp_needsCall_inv` | in-file :97 |
| `systemOp_needsCall_inv` | theorem | incremental-toward-`stepFrame_needsCall_inv` | in-file :114 |
| `stepFrame_needsCall_inv` | theorem | terminal-for-flagship | `DriveMono`, `CallPreservesSelf`, `RealisabilitySpec`; in-file `callDescent` |
| `createArm_needsCreate_inv` | theorem | incremental-toward-`systemOp_needsCreate_inv` | in-file :203,230 |
| `systemOp_needsCreate_inv` | theorem | incremental-toward-`stepFrame_needsCreate_inv` | in-file :243 |
| `stepFrame_needsCreate_inv` | theorem | terminal-for-flagship (CREATE presence, via DriveMono) | `DriveMono`:277, `CallPreservesSelf`; in-file `createDescent` |
| `beginCall_inl_accounts_present` | theorem | terminal-for-flagship | `DriveMono`:257, `CallPreservesSelf` |
| `beginCall_inl_checkpoint` | theorem | terminal-for-flagship | `DriveMono`:258, `CallPreservesSelf` |
| `beginCreate_ok_accounts_present` | theorem | terminal-for-flagship (CREATE arm of drive) | `DriveMono`:282; in-file `createDescent` |
| `beginCreate_ok_checkpoint` | theorem | terminal-for-flagship | `DriveMono`:284; in-file `createDescent` |
| `toCreateResult_accounts_eq` | theorem | shared-infra | in-file `resumeAfterCreate_exec_accounts_present` |
| `resumeAfterCreate_exec_accounts_present` | theorem | terminal-for-flagship | `DriveMono`:209; in-file `createDescent` |
| `resumeAfterCreate_kind` | theorem | terminal-for-flagship | `DriveMono`:221 |
| `DescentKind` | structure | scaffold-experimental (Phase 3.5 CREATE unification) | none yet — hosts `callDescent`/`createDescent` |
| `callDescent` | def | scaffold-experimental | none yet |
| `createDescent` | def | scaffold-experimental | none yet |
| `DescentKind.DescendImmediateNoErase` | def | scaffold-experimental | in-file `createDescent_descendImmediate_trivial` |
| `createDescent_descendImmediate_trivial` | theorem | scaffold-experimental | none yet |
| `DescentReturns` | def | scaffold-experimental (kind-generic `CallReturns`) | in-file `descentReturns_call_iff` |
| `descentReturns_call_iff` | theorem | scaffold-experimental (erasure `DescentReturns callDescent ↔ CallReturns`) | none yet |

Important: the `DescentKind` block (structure + 2 instances + `DescentReturns` +
`descentReturns_call_iff` + the two `DescendImmediateNoErase` decls) has **zero external
consumers**, but this is explicitly by-design scaffolding for first-class CREATE — the file's
own docstring (:400-416) states "the descent machinery (Phase 3.5's first-class CREATE)
instantiates ONE interface" and "`DescentReturns createDescent` has no consumer yet by design".
This matches the roadmap (execution-plan-2026-07-02.md, target-architecture-2026-07-02.md) that
names the `DescentKind`/CREATE oracle as inputs to first-class CREATE. Classify as
scaffold-experimental / incremental-toward-first-class-CREATE, **NOT** dead. In contrast, the
`stepFrame_needs{Call,Create}_inv` + `begin*` + `resume*` lemmas above them ARE load-bearing (the
CREATE inversion reaches the flagship via `DriveMono.drive_accounts_find_mono` →
`CallPreservesSelf` → `SelfPresent`).

### `BytecodeLayer/Hoare/DriveMono.lean` (294 LOC, `namespace Lir`)

Purpose: Brick D — account-presence monotone across a whole `drive` run
(`drive_accounts_find_mono`), the engine-level fact the `.success` shape of `CallPreservesSelf`
reduces to. Strong-fuel induction following `drive`'s own recursion; CREATE arm needs no seam
(handled in place via `stepFrame_needsCreate_inv`).

| decl | kind | role | callers |
|---|---|---|---|
| `CheckpointPresent` | def | terminal-for-flagship (invariant field) | `CallPreservesSelf`; in-file |
| `StackPresent` | def | shared-infra (invariant field) | in-file `DrivePresent` |
| `DrivePresent` | def | terminal-for-flagship (drive invariant) | `CallPreservesSelf`; in-file |
| `endFrame_call_accPresent` | theorem | incremental-toward-`endFrame_accPresent` | in-file :125 |
| `endFrame_create_accPresent` | theorem | incremental-toward-`endFrame_accPresent` | in-file :131 |
| `endFrame_accPresent` | theorem | shared-infra (halt closer) | in-file :229,244,247 |
| `drive_accounts_find_mono` | theorem | terminal-for-flagship (Brick D) | `SelfPresent`, `CallPreservesSelf`; referenced in `StepWalk` docstring |

### `BytecodeLayer/Hoare/Charges.lean` (32 LOC, `namespace Lir`)

Purpose: two general `subCharges` fold-algebra lemmas (snoc / append) — program-independent
list-fold arithmetic over exp003's gas fold. Home for the shared charge arithmetic.

| decl | kind | role | callers |
|---|---|---|---|
| `subCharges_snoc` | theorem | terminal-for-flagship (gas channel) | `MaterialiseGas.lean` |
| `subCharges_append` | theorem | terminal-for-flagship (gas channel) | `MaterialiseGas.lean` |

Header docstring (:11) also names `WorkedCall` as a consumer; no `WorkedCall` file exists in the
tree — stale doc reference (see corrections).

### `BytecodeLayer/Hoare/MemAlgebra.lean` (996 LOC, `namespace LirLean.MemAlgebra`)

Purpose: memory-channel crux lemmas for the MSTORE-flag-to-slot / MLOAD-back value channel. The
FFI wall is gone (`ffi.ByteArray.zeroes` has a pure `Array.replicate` body), so `zeroes`
size/getElem/toList, `UInt256.toByteArray` 32-byte width, the BE round-trip, and `UInt256`
`ofNat`/`toNat` reassemblies are all theorems; ships `#print axioms` guards on the crux results.

Consumed (terminal-for-flagship) crux/helpers: `mload_congr` (`MaterialiseRuns`, `SimStmt`);
`toNat_ofNat`/`ofNat_toNat`/`toNat_lt`/`toUInt64_toNat`/`M_32` (`MatDecLower`, `LowerDecode`,
`MaterialiseRuns`, `SimStmt`, `DecodeLower`); `uInt256OfByteArray_toByteArray`/`toByteArray_size`
(`SimTerm`, `Spec/Recorder`); `readWithPadding_written`/`readWithPadding_written_grow`
(`SimTerm`, `Match`); `activeWords_covers`, `mstore_memory_size`, `mstore_reads_back`,
`mstore_activeWords_covers`, `slot_windows_disjoint`, `mstore_preserves_slot`,
`mstore_preserves_slot_grow` (`SimStmt`); `mstore_memory_congr`/`mstore_activeWords_congr`
(`StashTail`). All ~35 other decls are in-file building blocks toward these (each with 2+
in-file occurrences), EXCEPT the group flagged below.

Selected key decls:

| decl | kind | role | callers |
|---|---|---|---|
| `mstore_preserves_slot` / `_grow` | theorems | terminal-for-flagship (slot framing) | `SimStmt` |
| `slot_windows_disjoint` | theorem | terminal-for-flagship | `SimStmt` |
| `mstore_reads_back` | theorem | terminal-for-flagship (grow-aware read-back, fresh slot) | `SimStmt` |
| `mstore_mload_disjoint` | theorem | shared-infra | in-file `mstore_preserves_slot`:902 |
| `mload_after_mstore` | theorem | needs-confirmation (see candidates) | none — only header + `#print axioms` guard |
| `resumeAfterCall_mload` | theorem | needs-confirmation (CALL-memory-preservation crux) | none |
| `resumeAfterCall_memory` / `_activeWords` | theorems | incremental-toward-`resumeAfterCall_mload` (dead-ends there) | in-file `resumeAfterCall_mload`:90-91 |

### `BytecodeLayer/Hoare/CleanHalt.lean` (103 LOC, `namespace Lir`)

Purpose: the clean-halt SCOPE predicates. `CleanHalts` (reaches some `.halted`) is the drive
well-foundedness witness; `CleanHaltsNonException` (reaches `.success`/`.revert`, not
`.exception`) is the honest gas-agnostic scope boundary that lets the §7 extractor DERIVE each
opcode's gas/memory envelope. This is one of the most widely consumed engine files.

| decl | kind | role | callers |
|---|---|---|---|
| `CleanHalts` | def | terminal-for-flagship (scope) | 9 files incl. `DriveSim`, `RealisabilitySpec`, `SimStmt(s)`, `LowerDecode/Conforms`, `Spec/Seams`, `MaterialiseCleanHalt`, `CleanHaltExtract`; `DriveRuns` produces its shape |
| `HaltNonException` | def | shared-infra | `CleanHaltExtract`, `DriveSim`, `RealisabilitySpec` |
| `haltNonException_success` | theorem | shared-infra | in-file `cleanHaltsNonException_of_success` |
| `haltNonException_revert` | theorem | shared-infra | in-file |
| `CleanHaltsNonException` | def | terminal-for-flagship (honest scope) | 9 files (sim tower + flagship) |
| `cleanHalts_forward` | theorem | terminal-for-flagship (forward split) | `CleanHaltExtract`, `Drive/Headline` |
| `cleanHaltsNonException_forward` | theorem | terminal-for-flagship | 9 files (sim tower + flagship) |
| `cleanHaltsNonException_toCleanHalts` | theorem | shared-infra (forgetful) | `CleanHaltExtract` |
| `cleanHaltsNonException_of_success` | theorem | shared-infra (success builder) | `CleanHaltExtract` |

### `BytecodeLayer/Hoare/DriveRuns.lean` (369 LOC, `namespace BytecodeLayer.Interpreter`)

Purpose: the reverse `drive → Runs` construction — reconstruct a halting `Runs` from a
clean-terminating top-level `drive` (no CREATE reached). Complements exp003's `Runs → drive`.
Already exp003-namespaced; imports only the bytecode layer. This is the honest scope bridge feeding
`Decode/Modellable` / `DriveSim` / the flagship.

| decl | kind | role | callers |
|---|---|---|---|
| `drive_append_framing_lt` | theorem | incremental-toward-`drive_descend_lt` | in-file :119; `RealisabilitySpec` |
| `drive_descend_lt` | theorem | shared-infra (well-founded descent) | in-file `runs_of_drive_ok`:353 |
| `ModellableStep` | def | terminal-for-flagship (scope marker) | `Decode/Modellable`; in-file |
| `drive_error_oof` | theorem | shared-infra (only-OOF errors) | in-file :201,342 |
| `child_terminates` | theorem | shared-infra | in-file :329; `RealisabilitySpec` |
| `framed_oof_of_standalone_oof` | theorem | incremental-toward-`child_ne_oof_of_framed` | in-file :260 |
| `child_ne_oof_of_framed` | theorem | shared-infra | in-file :339; `RealisabilitySpec` |
| `runs_of_drive_ok` | theorem | terminal-for-flagship (reverse construction) | `Decode/Modellable`, `DriveSim`, `RealisabilitySpec` |

---

## Internal sub-DAG + entry/exit edges

Intra-cluster imports (only ONE chain; the other four files are independent leaves):

```
AccountMap ─▶ StepWalk ─▶ Descent ─▶ DriveMono
Charges      (leaf; imports BytecodeLayer.Hoare.Sequence)
MemAlgebra   (leaf; imports Evm)
CleanHalt    (leaf; imports BytecodeLayer.Hoare)
DriveRuns    (leaf; imports BytecodeLayer.Hoare.CallSequence)
```

Incoming edges from other clusters: **NONE** (Engine imports only exp003) — this is the
clean-sublayer property, confirmed.

Outgoing (exit) edges — where Engine feeds the rest of the tree:

* `AccountMap` → `Drive/SelfPresent`, `Spec/Seams`, `Drive/CallPreservesSelf`,
  `RealisabilitySpec` (via `AccPresent`, `find?_some_ne_empty`, `forM_from_nil`,
  `all2_nil_false`, `accounts_find?_insert_mono`).
* `StepWalk` → `Drive/CallPreservesSelf`, `RealisabilitySpec`, `BoundaryReach` (Brick C
  caps + `SelfAt` + `resumeAfterCall_address`).
* `Descent` → `Drive/CallPreservesSelf`, `RealisabilitySpec` (the two `stepFrame_needs*_inv`
  + `beginCall_inl_*`).
* `DriveMono` → `Drive/SelfPresent`, `Drive/CallPreservesSelf` (Brick D + `DrivePresent`
  family).
* `CleanHalt` → the entire sim tower + flagship (9 files) — scope predicates.
* `DriveRuns` → `Decode/Modellable`, `DriveSim`, `RealisabilitySpec` — reverse construction.
* `MemAlgebra` → `MaterialiseRuns`, `SimStmt`, `SimTerm`, `Match`, `StashTail`, `MatDecLower`,
  `LowerDecode`, `DecodeLower`, `Spec/Recorder` — value/memory channel.
* `Charges` → `MaterialiseGas` — gas channel.

Every terminal exit lands (transitively) at `Lir.lower_conforms` EXCEPT the `DescentKind`
scaffold block in `Descent` (no exit — future CREATE hook).

---

## SIMPLIFICATION CANDIDATES

Conservative. Each is defended with evidence; uncertain items are flagged "needs confirmation",
not "delete".

1. **`MemAlgebra.mload_after_mstore` (:459) is superseded by `mstore_reads_back` (:713) — needs
   confirmation.** Both prove `((m.mstore addr val).mload addr).1 = val`. `mload_after_mstore`
   carries a *pre-size* premise (`addr.toNat + 32 ≤ m.memory.size`); `mstore_reads_back` is the
   grow-aware version with NO pre-size premise, matching the actual "freshly allocated tmp slot"
   use case and consumed by `SimStmt`. `mload_after_mstore` has **zero consumers** (only the
   header "Verdict" prose and a `#print axioms` guard reference it). Likely a superseded
   deliverable retained for its checked-axiom guard. Confirm nothing external depends on its
   pre-size form before removal; its helper lemmas (`copySlice_size`, `readWithPadding_written`,
   `activeWords_covers`) are shared and must stay.

2. **The `resumeAfterCall_mload` crux + its two exclusive feeders (`resumeAfterCall_memory`
   :58, `resumeAfterCall_activeWords` :69) have no consumer — needs confirmation.**
   `resumeAfterCall_mload` (:85, "CALL preserves caller memory") is advertised as a top-line
   Verdict crux with an axiom guard, but repo-wide grep shows zero uses; its two feeders feed
   only it. Either (a) the CALL memory-preservation obligation is now discharged elsewhere (e.g.
   via `MemRealises`/`Corr` coverage or `StashTail`'s `mstore_*_congr`), making this a superseded
   ~40-LOC island, or (b) it is a prepared-but-not-yet-wired crux for the memory value channel
   across CALL. Verify which before touching — do not assume dead.

3. **`AccountMap.AccMono` (:107) is a vestigial abbreviation.** Its named form has no reference
   anywhere outside AccountMap.lean; the `AccPresent`-transport it abbreviates is used pervasively
   but always written raw (`… → AccPresent … → AccPresent …`), never through this abbrev. Only
   `accMono_of_accounts_eq`/`accMono_emptySwap` mention it in their *conclusion types*. Harmless
   one-liner; flag for confirmation, not urgent.

4. **Namespace graduation debt (refactor, not deletion).** For the planned exp003 graduation of
   Engine, the `Lir`-namespaced files (`AccountMap`, `StepWalk`, `Descent` lower half,
   `DriveMono`, `CleanHalt`) need renamespacing to an engine/exp003 namespace. `AccountMap`
   already flags this (`-- RELOCATE to exp003 (audit §7)`). `DriveRuns` and the `Evm`-namespaced
   inversions are already graduation-ready. No behaviour change; pure hygiene.

5. **NOT a candidate — `DescentKind` scaffold.** Despite zero consumers, `DescentKind` /
   `callDescent` / `createDescent` / `DescentReturns` / `descentReturns_call_iff` /
   `DescendImmediateNoErase` are the deliberate first-class-CREATE unification hook (docstring
   :400-416; roadmap execution-plan/target-architecture). Keep. Listed here only to pre-empt a
   shallow "unused ⇒ delete" call.
