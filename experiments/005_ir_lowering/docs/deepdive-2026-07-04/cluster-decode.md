# Deep-dive cluster report: Decode / Layout / CFG-geometry

Scope: `LirLean/{LoweringLemmas, DecodeLower, Layout, DecodeAnchors, JumpValid, NoCreateBytes, BoundaryReach}.lean`.
Read-only audit, 2026-07-04. Every claim cites `file:line`. Usage established by repo-wide
`grep`, not import graph. Default classification is "incremental / shared-infra", not "dead".

This cluster is the **bytes ↔ IR-positions substrate** (layers L2/L3 of
`lirlean-dag-2026-07-04.md`): it turns the pure `lower prog` byte array into (a) concrete
`Evm.decode … = some (op, arg)` facts at any cursor, and (b) the two whole-program
geometric invariants (jump-dest validity, no-CREATE / lowering-op-only at every reachable
boundary). It is consumed by the Materialise/Sim layers (`MatDecLower`, `LowerDecode`,
`SimTerm`), by `Decode/Modellable.lean` (the `NotCreate` discharge), and by
`RealisabilitySpec.lean` (the flagship's R6 boundary geometry).

---

## 1. Per-file sections

### 1.1 `LoweringLemmas.lean` (98 LOC)

Purpose (grounded in header + `reorg-legibility.md §5`): the proof companions extracted out
of `Spec/Lowering.lean` so that file stays definitions-only. Two families: the `defsOf`
spill-routing exhaustiveness facts, and the `allocate` faithfulness keystone (Phase-A
"no behaviour change").

| decl | kind | role | callers |
|---|---|---|---|
| `defsOf_ne_gas` (:20) | theorem | shared-infra — Phase-B spill invariant (no gas tmp is a bare `.gas` def) | `MaterialiseCleanHalt.lean:195`, `MaterialiseRuns.lean:1083`, `RealisabilitySpec.lean:370` (tie derivation) |
| `defsOf_ne_sload` (:55) | theorem | shared-infra — Phase-C spill invariant (no sload tmp is a bare `.sload`) | `MaterialiseCleanHalt.lean:198`, `MaterialiseRuns.lean:1088`, `RealisabilitySpec.lean:1184,1190` |
| `toDef_locOfExpr` (:85) | `@[simp]` theorem | shared-infra — simp-normal-form left-inverse; consumed inside `allocate_toDefs` (:96) | none external (it is a `@[simp]` rewrite; see §3) |
| `allocate_toDefs` (:91) | theorem | shared-infra — Phase-A keystone (`allocate` re-presents `defsOf`) | `DecodeLower.emit_allocate_eq_flatBytes:56`; referenced `Spec/Lowering.lean:87,304` |

Bodies read: both `defsOf_ne_*` are honest exhaustive case-splits over `Stmt`/`Expr` arms
via `Option.map_eq_some_iff` + `List.mem_of_find?_eq_some` (:26-49, :59-82); no shortcut.
`allocate_toDefs` is a `funext` + `cases defsOf` (:92-96). All axiom-clean (no `sorry`).

### 1.2 `DecodeLower.lean` (159 LOC)

Purpose (header, "C3"): factor the *program-independent* core of `Evm.decode (lower prog) pc
= expected` so a decode fact follows from a **list-local** statement about `flatBytes prog`
(the byte at the offset + the immediate window), instead of a whole-array kernel `rfl`.

| decl | kind | role | callers |
|---|---|---|---|
| `flatBytes` (:46) | def | shared-infra — THE list model of `lower prog`; the object every layout proof indexes | ubiquitous: `Layout`, `DecodeAnchors`, `JumpValid`, `NoCreateBytes`, `BoundaryReach`, `MatDecLower`, `LowerDecode`, `RealisabilitySpec` |
| `emit_allocate_eq_flatBytes` (:54) | theorem | incremental brick toward `lower_eq_flatBytes` | only `lower_eq_flatBytes:62` |
| `lower_eq_flatBytes` (:61) | theorem | shared-infra — the `lower = ⟨flatBytes.toArray⟩` bridge | `JumpValid.lean:360,506`, `RealisabilitySpec.lean:2250`, `Spec/Lowering.lean:305` (doc) |
| `bget` (:68) | theorem | shared-infra — list-backed `ByteArray.get?` = list index | `JumpValid.lean:360,507`; internal to `lower_get?_eq` |
| `bextract` (:77) | theorem | incremental brick — immediate-window slice for PUSH | only `decode_push_of_list:126` |
| `decode_nonpush_of_list` (:100) | theorem | incremental brick | only `decode_lower_nonpush:148` |
| `decode_push_of_list` (:116) | theorem | incremental brick | only `decode_lower_push:157` |
| `decode_lower_nonpush` (:144) | theorem | shared-infra — THE non-push decode brick over `lower prog` | `MatDecLower:206`, `DecodeAnchors:208,253,295`, `JumpValid:508`, `NoCreateBytes:403`, `BoundaryReach:423` |
| `decode_lower_push` (:151) | theorem | shared-infra — THE push decode brick over `lower prog` | `MatDecLower:190`, `LowerDecode:397`, `DecodeAnchors:231,272,316`, `NoCreateBytes:406`, `BoundaryReach:426` |

Bodies read: `bget`/`bextract` are genuine `ByteArray` unfoldings (:70-88); the two generic
decode lemmas do the `UInt32.ofNat`-round-trip + `if pushArgWidth > 0` split honestly
(:104-133). The `_of_list` → `_lower` specialisations are one-line `rw [lower_eq_flatBytes]`
(:148,157). Axiom-clean.

### 1.3 `Layout.lean` (204 LOC)

Purpose (header, "C3 offset-table prefix sum"): the byte-layout arithmetic that produces the
`(flatBytes prog)[n]?` facts `DecodeLower` consumes, over an **arbitrary** program, by
prefix-sum decomposition of the offset table (not per-program `rfl`).

| decl | kind | role | callers |
|---|---|---|---|
| `emitTerm_length_labelOff` (:45) | theorem | incremental brick (offset-table well-definedness) | only `emitBlockBody_length_labelOff:57` |
| `emitBlockBody_length_labelOff` (:52) | theorem | incremental brick | only `blockLen_eq_length:66` |
| `blockLen_eq_length` (:62) | theorem | shared-infra — lowered-block length is table-independent | `Layout.blockPrefix_length:106`, `JumpValid:443,449` |
| `flatMap_split` (:73) | theorem | shared-infra — generic `flatMap` decomposition around an index | `Layout:127,187`, `DecodeAnchors:73` |
| `blockPrefix_length` (:93) | theorem | incremental brick toward `flatBytes_block_offset` | only `flatBytes_block_offset:138` |
| `flatBytes_block_split` (:115) | theorem | shared-infra — `flatBytes` decomposed around a block | `Layout:169`, `DecodeAnchors:59,111`, `JumpValid:393,503` |
| `flatBytes_block_offset` (:133) | theorem | shared-infra — block `L`'s JUMPDEST byte-offset = `offsetTable L.idx` | `Layout.stmt_byte_anchor:177`, `DecodeAnchors:67,119`, `JumpValid:403` |
| `mid_index` (:151) | theorem | shared-infra — index into middle of a 3-way append | `Layout:198`, `DecodeAnchors:84,126`, `JumpValid:406` |
| `stmt_byte_anchor` (:162) | theorem | shared-infra — the `k=0` statement-head byte anchor | `Match.lean` (`flatBytes_at_pcOf`) |

Bodies read: `stmt_byte_anchor` (:169-202) is the pivotal one — a real `set`-heavy prefix-sum
walk landing `mid_index` at the statement head; verified honest. Axiom-clean.

### 1.4 `DecodeAnchors.lean` (318 LOC)

Purpose (header, `lower-conforms-plan.md` Layer A): turn an offset-table address
`pcOf prog L pc` (or a cursor inside a statement's push-sequence, or a terminator offset)
into a concrete `Evm.decode (lower prog) …` fact. Three anchor families A1/A2/A3.

| decl | kind | role | callers |
|---|---|---|---|
| `stmt_byte_anchor_k` (:51) | theorem | incremental brick (`k`-gen of `Layout.stmt_byte_anchor`) | only `flatBytes_at_pcOf_offset:151` |
| `term_byte_anchor` (:103) | theorem | incremental brick | only `flatBytes_at_termOf:181` |
| `flatBytes_at_pcOf_offset` (:143) | theorem | shared-infra — byte at `pcOf+k` (A2 byte half) | `MatDecLower:443`, `LowerDecode:1120,1305,1463` |
| `termOf` (:156) | def | shared-infra — terminator byte offset | `MatDecLower`, `LowerConforms`, `Acyclic`, `LowerDecode`, `SimTerm`, `RealisabilitySpec` |
| `termOf_eq_anchor` (:164) | theorem | shared-infra | `SimTerm.lean` |
| `flatBytes_at_termOf` (:173) | theorem | shared-infra — byte at `termOf+k` (A3 byte half) | `MatDecLower`, `LowerDecode`, `RealisabilitySpec` |
| `decode_at_stmt_head_nonpush` (:195) | theorem | **superseded? (needs confirmation)** — A1 non-push head | **none anywhere** (§3) |
| `decode_at_stmt_head_push` (:215) | theorem | **superseded? (needs confirmation)** — A1 push head | **none anywhere** (§3) |
| `decode_at_offset_nonpush` (:241) | theorem | shared-infra — A2 non-push (trailing effecting opcode) | `LowerDecode:121,1123,1137` |
| `decode_at_offset_push` (:257) | theorem | **superseded? (needs confirmation)** — A2 push | **none anywhere** (§3) |
| `decode_at_term_nonpush` (:283) | theorem | shared-infra — A3 non-push (`RETURN/STOP/JUMP/JUMPI`) | `LowerDecode:463,530,709,737,862,888`, `LowerConforms`, `RealisabilitySpec` |
| `decode_at_term_push` (:300) | theorem | shared-infra — A3 push (`PUSH4` dest) | `LowerDecode:352` region |

Bodies: all six `decode_at_*` are thin compositions of the byte-anchor + `decode_lower_*`
bricks (:204-316). Axiom-clean.

### 1.5 `JumpValid.lean` (516 LOC) — SegAligned tower #1

Purpose (header, `lower-conforms-plan.md` node E3): every block offset is a valid JUMP
destination of `lower prog`. Introduces `SegAligned` (list-level instruction alignment) and
the "boundary walk reaches the segment end" transport, generalising the per-program
`by decide` jump-validity walks.

| decl | kind | role | callers |
|---|---|---|---|
| `ReachesBoundary.trans` (:63) | theorem | shared-infra | `BoundaryReach.reachesBoundary_nextInstr:112` + internal `reaches_block_offset:450` |
| `SegAligned` (:78) | inductive | shared-infra — base alignment notion (predicate-free) | base of `NoCreateBytes.SegAlignedSafe`/`BoundaryReach.SegAlignedLowering` (via `.toSegAligned`); internal transport |
| `SegAligned.append/nonpush/push` (:91,100,107) | theorems | incremental bricks (emit-ladder glue) | internal to `segAligned_*` |
| `reaches_of_segAligned` (:120) | theorem | shared-infra — the "reach the end" transport (needs alignment only) | `reaches_block_offset:440` |
| `segAligned_emitImm/emitDest/slot` (:169,177,185) | theorems | incremental bricks | internal |
| `segAligned_materialiseExpr/materialise` (:194,237) | theorems | incremental bricks | internal |
| `segAligned_emitStmt/emitTerm/emitBlockBody/loweredBlock` (:243,302,330,343) | theorems | incremental bricks | internal (`reaches_block_offset` via `loweredBlock:437`) |
| `lower_get?_eq` (:358) | theorem | shared-infra — `(lower prog).get? n = flatBytes[n]?` | `lower_match_block:391`, `NoCreateBytes:381`, `BoundaryReach:407` |
| `offsetTable_succ` (:364) | theorem | shared-infra — prefix-sum step | `reaches_block_offset:445` |
| `lower_match_block` (:383) | theorem | incremental brick | `reaches_block_offset:439`, `lower_byte_at_offset:463` |
| `reaches_block_offset` (:413) | theorem | shared-infra — walk reaches every block offset | `block_offset_validJump:481`; docstring-only in `NoCreateBytes` |
| `lower_byte_at_offset` (:459) | theorem | incremental brick | `block_offset_validJump:485` |
| `block_offset_validJump` (:471) | theorem | **terminal-for-flagship (E3)** | `LowerDecode`, `SimTerm`, `RealisabilitySpec` |
| `decode_at_block_offset_jumpdest` (:497) | theorem | **terminal-for-flagship** — landing-pad decode | `LowerConforms`, `LowerDecode`, `RealisabilitySpec` |

Bodies: `reaches_of_segAligned` (:120-158) and `reaches_block_offset` (:413-450) are the
pivotal inductions; read in full, honest. Header claims `[propext, Classical.choice,
Quot.sound]` only (:513-514).

### 1.6 `NoCreateBytes.lean` (431 LOC) — SegAligned tower #2

Purpose (header): the structural half of the `NotCreate` modellability clause — every byte
read *as an opcode* at any reachable boundary of `lower prog` is not CREATE/CREATE2.
Introduces `SegAlignedSafe` = `SegAligned` + per-head `parseInstr byte ∉ {CREATE, CREATE2}`.

| decl | kind | role | callers |
|---|---|---|---|
| `SegAlignedSafe` (:50) | inductive | incremental — no-CREATE-head alignment | `BoundaryReach` (mirror), `Decode/Modellable`, `DriveSim` (doc/refs) |
| `SegAlignedSafe.toSegAligned` (:59) | theorem | **unused completeness map** (§3) | none |
| `SegAlignedSafe.append/nonpush/push` (:72,82,90) | theorems | incremental bricks | internal |
| `reachesBoundary_le` (:107) | theorem | shared-infra | `BoundaryReach` transport (:186 mirror), internal :123 |
| `reaches_safe_of_segAlignedSafe` (:112) | theorem | incremental — "interior boundary satisfies notCreate" transport | internal `reachable_boundary_notCreate:382` |
| `segAlignedSafe_*` emit-ladder (:172-348) | theorems | incremental bricks (mirror of `segAligned_*`) | internal |
| `segAlignedSafe_flatBytes` (:353) | theorem | incremental brick | `reachable_boundary_notCreate:382` |
| `reachable_boundary_notCreate` (:375) | theorem | incremental brick | only `decode_reachable_boundary_some:396` |
| `decode_reachable_boundary_some` (:391) | theorem | **terminal-for-flagship** — decode-level no-CREATE | `Decode/Modellable.lean:426` |
| `decode_reachable_boundary_notCreate` (:413) | theorem | terminal-for-flagship (currentOp form) | `Decode/Modellable.lean` (declared consumer; see §3 note) |

Consumer confirmed: `Decode/Modellable.notCreate_of_atReachableBoundary` (:421-437) calls
`Lir.decode_reachable_boundary_some` (:426) to discharge `NotCreate` from
`AtReachableBoundary`. So this tower is LIVE. Axiom-clean guard :427-431.

### 1.7 `BoundaryReach.lean` (432 LOC) — SegAligned tower #3

Purpose (header): boundary-reachability bricks for the whole-run `AtReachableBoundary`
invariant (`hrb` of `Decode/Modellable.modellable_of_runs`), feeding the flagship's **R6**
(`runs_atReachableBoundary`, `RealisabilitySpec.lean:2456`). Three bricks + the
`SegAlignedLowering` allow-list tower (= `SegAligned` + per-head `IsLoweringOp`).

| decl | kind | role | callers |
|---|---|---|---|
| `mem_validJumpDestsAuxNat_inv` (:51) | theorem | incremental brick | only `reachesBoundary_of_mem_validJumpDests:95` |
| `reachesBoundary_of_mem_validJumpDests` (:90) | theorem | **incremental-toward-R6** — taken-jump → reachable-boundary converse | `RealisabilitySpec.lean` |
| `reachesBoundary_nextInstr` (:109) | theorem | **incremental-toward-R6** — sequential advance | `RealisabilitySpec.lean` |
| `IsLoweringOp` (:125) + `Decidable` inst (:131) | def/instance | **incremental-toward-R6** — the 16-op allow-list | `RealisabilitySpec.lean` |
| `SegAlignedLowering` (:135) | inductive | incremental — allow-list alignment | internal |
| `SegAlignedLowering.toSegAligned` (:144) | theorem | **unused completeness map** (§3) | none |
| `SegAlignedLowering.append/nonpush/push` (:151,160,167) | theorems | incremental bricks | internal |
| `reaches_loweringOp_of_segAlignedLowering` (:177) | theorem | incremental — "interior boundary is a lowering op" transport | internal `reachable_boundary_loweringByte:408` |
| `segAlignedLowering_*` emit-ladder (:219-395) | theorems | incremental bricks (mirror of `segAligned_*`) | internal |
| `reachable_boundary_loweringByte` (:402) | theorem | **incremental-toward-R6** — byte-level allow-list | `RealisabilitySpec.lean` |
| `decode_reachable_boundary_loweringOp` (:415) | theorem | incremental (decode-level headline, not yet consumed) | none yet (byte-level twin `:402` is what R6 uses) |

Header itself states the `Runs`-induction that would consume these "is not yet landed"
(:26-33) — so these are genuinely incremental-toward-R6, not dead. Axiom-clean guard
:431-432.

---

## 2. Internal sub-DAG and cross-cluster edges

Internal (this cluster), by import + real dependency:

```
LoweringLemmas
   └── DecodeLower        (flatBytes, lower_eq_flatBytes, decode_lower_{nonpush,push})
          ├── Layout       (flatMap_split, blockLen_eq_length, flatBytes_block_{split,offset}, mid_index, stmt_byte_anchor)
          │      └── DecodeAnchors  (flatBytes_at_{pcOf_offset,termOf}, termOf, decode_at_{offset,term}_*)
          │             └── JumpValid   (SegAligned tower #1; block_offset_validJump, decode_at_block_offset_jumpdest)
          │                    └── NoCreateBytes   (SegAlignedSafe tower #2; decode_reachable_boundary_{some,notCreate})
          │                           └── BoundaryReach   (SegAlignedLowering tower #3; reachable_boundary_loweringByte, R6 bricks)
          └── (Match imports DecodeLower + Layout for stmt_byte_anchor/flatBytes_at_pcOf)
```

Note the three SegAligned towers are stacked by import (`JumpValid → NoCreateBytes →
BoundaryReach`), each re-deriving the full emit-ladder — see §3.

Exit edges (this cluster → rest of tree):
- `flatBytes`, `decode_lower_*`, `flatBytes_at_pcOf_offset`, `termOf`, `flatBytes_at_termOf`,
  `decode_at_{offset,term}_*` → **`MatDecLower`, `LowerDecode`, `SimTerm`** (Materialise/Sim
  bricks).
- `block_offset_validJump`, `decode_at_block_offset_jumpdest`, `termOf` →
  **`LowerConforms`, `SimTerm`, `LowerDecode`, `Acyclic`**.
- `decode_reachable_boundary_{some,notCreate}` + `SegAlignedSafe` → **`Decode/Modellable`**
  (`notCreate_of_atReachableBoundary`, :421-437).
- `reachesBoundary_of_mem_validJumpDests`, `reachesBoundary_nextInstr`, `IsLoweringOp`,
  `reachable_boundary_loweringByte`, `SegAlignedSafe`, `lower_eq_flatBytes`, `termOf`,
  `flatBytes_at_termOf`, `decode_at_term_nonpush`, `decode_at_block_offset_jumpdest` →
  **`RealisabilitySpec`** (flagship R6 geometry + assorted anchors).
- `defsOf_ne_{gas,sload}` → **`MaterialiseRuns`, `MaterialiseCleanHalt`, `RealisabilitySpec`**.

Entry edges (rest of tree → this cluster): `Spec/Lowering.lean` (defs), `Evm` (decode
primitives), `Match.lean` (`pcOf`, `pcOf_eq_anchor`, `flatBytes_at_pcOf`, `blockAt_of_toList`
— DecodeAnchors imports Match).

---

## 3. SIMPLIFICATION CANDIDATES (evidence-backed)

### C1 — The three SegAligned towers are a parameterized triplication (DEFENSIBLE, high value)

`JumpValid` (516 LOC), `NoCreateBytes` (431 LOC), `BoundaryReach` (432 LOC) = 1379 LOC re-prove
the **same emit-ladder** with a per-head predicate `P`:

- `SegAligned` (`JumpValid:78`): `cons` carries `himm` only. `P = True`.
- `SegAlignedSafe` (`NoCreateBytes:50`): `cons` carries `himm` + `hsafe : parseInstr byte ∉ {CREATE, CREATE2}`.
- `SegAlignedLowering` (`BoundaryReach:135`): `cons` carries `himm` + `hop : IsLoweringOp (parseInstr byte)`.

Every member of the ladder is line-by-line identical modulo the extra predicate argument.
Compare, e.g., `segAligned_emitStmt` (`JumpValid:243-296`),
`segAlignedSafe_emitStmt` (`NoCreateBytes:243-293`),
`segAlignedLowering_emitStmt` (`BoundaryReach:282-332`): identical `cases`/`append`
structure, the only difference is `.nonpush byte (by decide)` vs
`.nonpush byte (by decide) (by decide)`. Same for `append`/`nonpush`/`push`/`toSegAligned`
and `segAligned{,Safe,Lowering}_{emitImm,emitDest,slot,materialiseExpr,materialise,
emitTerm,emitBlockBody,loweredBlock,flatBytes}`.

Two of the three transports also coincide: `reaches_safe_of_segAlignedSafe`
(`NoCreateBytes:112-162`) and `reaches_loweringOp_of_segAlignedLowering`
(`BoundaryReach:177-215`) are the same induction ("any interior reachable boundary satisfies
`P`") modulo `P`. (`JumpValid`'s `reaches_of_segAligned` is genuinely distinct — it proves
"reaches the segment *end*", predicate-free — so it stays with the base notion.)

Proposed refactor (matches the DAG doc's noted "SegAligned tower ×3 dedup ~1400→600" lever,
`lirlean-dag-2026-07-04.md:174-193`): one predicate-parameterized inductive
`SegAlignedP (P : Operation → Prop)` with the emit-ladder + `append`/`nonpush`/`push` +
interior-boundary transport proven once (the emit lemmas discharging `P` per concrete opcode
via `decide` at instantiation), then `SegAligned := SegAlignedP (fun _ => True)`,
`SegAlignedSafe := SegAlignedP notCreate`, `SegAlignedLowering := SegAlignedP IsLoweringOp`.
All three headlines (`block_offset_validJump`, `decode_reachable_boundary_*`,
`reachable_boundary_loweringByte`) are LIVE, so this is **duplication-to-collapse, NOT
supersession** — no headline is removed.

Extra fact supporting a shortcut: `IsLoweringOp op → op ≠ .System .CREATE ∧ op ≠ .System
.CREATE2` (all 16 ops at `BoundaryReach:126-129` are non-CREATE), i.e. `SegAlignedLowering`
is strictly stronger than `SegAlignedSafe`. So `NoCreateBytes`'s `decode_reachable_boundary_*`
could alternatively be *derived* from `BoundaryReach`'s `reachable_boundary_loweringByte` by
post-composing `IsLoweringOp → notCreate` — collapsing tower #2 into a thin corollary of
tower #3 (would require flipping the current `BoundaryReach imports NoCreateBytes` edge).
Either route removes ~one full tower.

### C2 — Three A-family push/head anchors have zero callers anywhere (needs confirmation)

`decode_at_stmt_head_nonpush` (`DecodeAnchors:195`), `decode_at_stmt_head_push`
(`DecodeAnchors:215`), and `decode_at_offset_push` (`DecodeAnchors:257`) have **no reference
anywhere** in the tree (grep dir-wide, only their own definitions match). Their live siblings
`decode_at_offset_nonpush` (:241) and `decode_at_term_{nonpush,push}` (:283,300) are used
throughout `LowerDecode`.

Evidence they are likely superseded rather than pending: the actual sim path decodes
statement-head and interior **push** operands through `MatDecLower`'s `MatSeg` machinery
(`matSeg_of_stmt:432`, `matDec_of_seg:290`, `imm_leaf_decode:166`, `slot_leaf_decode:236`),
which is built **directly** on `flatBytes_at_pcOf_offset` + `decode_lower_push`
(`MatDecLower:190,443`) — not on any `decode_at_*_push` / `decode_at_stmt_head_*`. The
non-push A2 anchor survives (trailing effecting opcodes: `LowerDecode:121,1123,1137`), which
is why the *nonpush* twins are live and the *push*/head twins are orphaned.

Classification: **likely-superseded-by-the-`MatSeg`-operand-decode-path**, but flagged
"needs confirmation" — they form a symmetric completeness API (A1/A2/A3 × nonpush/push per
`lower-conforms-plan.md` Layer A) and could be a deliberate kept surface. Recommend
confirming with the plan owner before removal; low LOC (~65).

### C3 — Two `toSegAligned` forgetful maps are unused (low priority, needs confirmation)

`SegAlignedSafe.toSegAligned` (`NoCreateBytes:59`) and `SegAlignedLowering.toSegAligned`
(`BoundaryReach:144`) have no callers anywhere (grep dir-wide). They are provided-for-
completeness forgetful maps. They would disappear automatically under the C1 dedup (a single
inductive needs no cross-forgetful maps). Note if C1 is not done: harmless, tiny.

### Non-candidates (explicitly NOT superseded)

- The many single-caller "incremental bricks" (`bextract`, `decode_{non,}push_of_list`,
  `emit{Term,BlockBody}_length_labelOff`, `blockPrefix_length`, `stmt_byte_anchor_k`,
  `term_byte_anchor`, `reachable_boundary_notCreate`, `segAligned*_flatBytes`,
  `mem_validJumpDestsAuxNat_inv`) are load-bearing internal steps of a live headline — keep.
- `decode_reachable_boundary_loweringOp` (`BoundaryReach:415`) has no caller yet but is the
  decode-level twin of the used byte-level `reachable_boundary_loweringByte`; the header
  (:26-33) says the consuming `Runs`-induction (R6) "is not yet landed" — incremental, keep.
- `toDef_locOfExpr` has no *named* caller but is a `@[simp]` lemma consumed by simp in
  `allocate_toDefs:96` — keep.
