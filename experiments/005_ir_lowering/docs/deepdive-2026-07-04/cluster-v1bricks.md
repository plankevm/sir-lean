# Deep-dive cluster: v1 bricks (SmallStep · Call · Create · StorageErase · Match)

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

Audit date 2026-07-04. Read-only pass. All line cites are into
`experiments/005_ir_lowering/LirLean/`.

## Executive shape

This cluster is the exp003-bound **frame-local / v1** layer. It contains three
distinct things that the fleet vocabulary lumps together as "v1 bricks", and the
audit's central finding is that they have **very different liveness**:

1. **Frame-local EVM sim bricks + byte-layout `pcOf` + storage lens** (all in
   `Match.lean`). These mention only exp003 `Frame`/`decode`/`Runs` — *not* the v1
   `Lir.IRState`. They are **shared infra consumed by the live v2 flagship path**
   (Materialise*, SimStmt, SimTerm, StashTail, CallRealises).
2. **The CALL oracle projections** (`Call.lean`: `evmCallOracle`,
   `callSuccessFlag`, `evmCallOracle_successWord_eq_x`, `call_reflects_lowered`).
   Defined over exp003 `CallResult`/`PendingCall`, **not** over `Lir.IRState`, and
   **live** — they feed `CallRealises.lean`, `SimStmt.lean`, `LowerConforms.lean`
   and `RealisabilitySpec.lean`.
3. **The genuine v1 IR operational semantics** (`SmallStep.lean` `Lir.IRState` and
   its `evalExpr`/`setLocal`/`setStorage`/`bindCallResult`, `HaltResult`, `IRConf`,
   `Program.stmtAt`; `Call.lean` `IRState.applyCall`; the `Match` **structure**;
   `Match.lean` `lower_preserves_*`). Every one of these has a **V2 twin** in
   `Spec/Semantics.lean` (`Lir.IRState`, `Lir.evalExpr`, `Lir.HaltResult`, `Lir.blockAt`,
   `Corr`) that is what the flagship actually consumes; the v1 originals are the
   *reference* small-step and are **used nowhere in the live cone** — they survive
   only in each other's proofs/docstrings.

`Create.lean` is a fourth category: **scaffold-experimental**, imported by nobody,
prepared for first-class CREATE (see `00-create-status.md`).

`StorageErase.lean` is pure `RBMap` data-structure infra, **live**: it is the only
thing that lets the zero-write SSTORE (`vw = 0` slot clear) read back, which the
flagship now depends on (`RealisabilitySpec.lean:97,775`).

---

## File: `LirLean/SmallStep.lean`

Purpose (proof plan): the **v1 reference small-step IR semantics** (`Lir.IRState`,
`evalExpr`, terminators). Its storage transformer deliberately mirrors exp003's
post-frame transformers so the `Match` invariant's `M3` clause is `rfl`-clean. The
gas-free v2 line (`Spec/Semantics.lean`, `Lir.*`) later **re-implemented** this
state as `Lir.IRState` (`.world`/`.locals`); the flagship rides the v2 copy.

| decl | kind | role | callers |
|---|---|---|---|
| `IRState` (:49) | structure | genuinely-superseded-for-flagship — v1 IR state; the flagship uses `Lir.IRState` (`Spec/Semantics.lean:48`). Only consumers of the v1 struct are v1-only decls below | none live; only Call/Match v1 decls |
| `HaltResult` (:60) | inductive | genuinely-superseded — twin `Lir.HaltResult` (`Spec/Semantics.lean:55`) is what the flagship uses | Match.lean docstrings only (`:367,401,560,574`) |
| `IRConf` (:69) | inductive | genuinely-dead — **zero references repo-wide** (only its own def line) | none anywhere |
| `evalExpr` (:89) | def | genuinely-superseded — every live `evalExpr` call is `Lir.evalExpr` (`Spec/Semantics.lean:123`; DefsSound `open Lir`). v1 `evalExpr` is never called, only named in Match docstrings | none live |
| `IRState.setLocal` (:101) | def | v1-only — used only by v1 `bindCallResult` (:114); flagship uses `Lir.IRState.setLocal` (`Spec/Semantics.lean:104`) | `bindCallResult` (SmallStep:114) |
| `IRState.bindCallResult` (:110) | def | genuinely-dead-as-code — appears only in docstrings (SmallStep/Call), never called; the v2 success-word channel is `callSuccessFlag`+`CallRealises` | none (docstrings only) |
| `IRState.setStorage` (:117) | def | v1-only — flagship uses `Lir.IRState.setStorage` (`Spec/Semantics.lean:108`); v1 copy named only in Match docstrings (`Match.lean:35,142`) | none live |
| `Program.blockAt` (:123) | def | **shared-infra / terminal-for-flagship** — `pcOf` (Match:70) and `blockAt_of_toList` (Match:84) use it; `blockAt_of_toList` is live in DecodeAnchors. (v2 keeps a local `Lir.blockAt`, `Spec/Semantics.lean:139`, but v1's is genuinely on the live `pcOf` path) | Match.lean:70,84 → DecodeAnchors:169 |
| `Program.stmtAt` (:127) | def | genuinely-dead — **zero references repo-wide** | none anywhere |

---

## File: `LirLean/Call.lean`

Purpose (proof plan §5): the **abstract CALL oracle** + its by-construction EVM
instantiation. The oracle projections are over exp003 data (`CallResult`,
`PendingCall`), so they are toolchain-portable and **live in the v2 flagship**; the
one v1-IRState-coupled decl (`applyCall`) is dead.

| decl | kind | role | callers |
|---|---|---|---|
| `CallOracle` (:79) | structure | shared-infra — carrier for `evmCallOracle` | `evmCallOracle` (Call:108) |
| `evmCallOracle` (:108) | def | **terminal-for-flagship** — `.postStorage` is load-bearing | LowerConforms:274,277,301,304; RealisabilitySpec:419-area; Spec/Semantics:97 |
| `callSuccessFlag` (:120) | def | **terminal-for-flagship** — the CALL 0/1 flag the recorder/realiser tie to | LowerConforms:275,294,302; RealisabilitySpec:419; SimStmt:665; CallRealises:28 |
| `evmCallOracle_successWord_eq_x` (:128) | theorem | **terminal-for-flagship** — pins oracle success word = `callSuccessFlag` | SimStmt:665; CallRealises:28,36,78 |
| `IRState.applyCall` (:158) | def | genuinely-dead-as-code — operates on v1 `Lir.IRState`; appears only in docstrings, never called (v2 threads the call effect via `CallRealises`) | none (docstrings only) |

Note: `call_reflects_lowered` (the reflexivity headline that consumes this file)
lives in `Match.lean`, not here; it is live (see Match table).

---

## File: `LirLean/Create.lean`

Purpose (proof plan / `00-create-status.md`): the **CREATE analogue of `Call.lean`**,
prepared scaffolding for a first-class CREATE that is **designed but not built**. In
the build cone (imported at `LirLean.lean:22`, compiles green) but **imported by no
other module**; every reference is inside `Create.lean` itself. The IR surface has
zero CREATE node, so nothing can consume it yet.

| decl | kind | role | callers |
|---|---|---|---|
| `CreateOracle` (:64) | structure | scaffold-experimental — twin of `CallOracle`; incremental-toward first-class CREATE (`00-create-status.md`; execution-plan-2026-07-02 §CREATE) | `evmCreateOracle` (Create:99) |
| `createAddrOrZero` (:75) | def | scaffold-experimental — twin of `callSuccessFlag`; the deployed-addr-or-0 value a future `create_reflects_lowered` will tie | `evmCreateOracle` (Create:102); `evmCreateOracle_addressWord_eq` (Create:108) |
| `evmCreateOracle` (:99) | def | scaffold-experimental — twin of `evmCallOracle` | `evmCreateOracle_addressWord_eq` (Create:108) |
| `evmCreateOracle_addressWord_eq` (:107) | theorem | scaffold-experimental — twin of `evmCallOracle_addressWord/_successWord_eq_x` | none yet, builds toward `create_reflects_lowered` |

Do **not** delete: the settled roadmap keeps this and puts CREATE first-class next;
its CALL twin is load-bearing, so this is "incremental toward a live need," not dead.

---

## File: `LirLean/StorageErase.lean`

Purpose: pure `RBMap`/`RBNode` erase read-back bricks that Batteries omits
(`find?_erase` has no library proof). Supplies exactly the two equations the
**zero-write SSTORE** (slot clear → `RBMap.erase`) needs. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Mentions no EVM execution concept.
**Live**: the flagship's `sim_sstore` now covers `vw = 0`, which routes through here.

| decl | kind | role | callers |
|---|---|---|---|
| `RBNode.append_toList` (:36) | theorem | shared-infra (internal) | `Path.del_toList` proof chain / `mem_erase` |
| `RBNode.Path.del_toList` (:44) | theorem | shared-infra (internal) | `erase_toList_zoom` (:66) |
| `RBNode.erase_toList_zoom` (:60) | theorem | shared-infra (internal) | `mem_erase` (:73,85) |
| `RBNode.mem_erase` (:71) | theorem | shared-infra (internal) | `find?_erase_self` (:157), `find?_erase_of_ne` (:172,178) |
| `RBNode.find?_erase_self` (:152) | theorem | shared-infra (internal) | `Evm.Storage.findD_erase_self` (:193) |
| `RBNode.find?_erase_of_ne` (:161) | theorem | shared-infra (internal) | `Evm.Storage.findD_erase_of_ne` (:213) |
| `Evm.Storage.findD_erase_self` (:189) | theorem | **terminal-for-flagship** — cleared slot reads `0` | Match:224 (`sstoreFrame_storage_self'`); named RealisabilitySpec:97,775 |
| `Evm.Storage.findD_erase_of_ne` (:199) | theorem | **terminal-for-flagship** — other slots unchanged after clear | Match:252 (`sstoreFrame_storage_frame'`) |

---

## File: `LirLean/Match.lean`

Purpose (proof plan, milestone C3): the `pcOf` byte-layout arithmetic, the storage
lens (`selfStorage`/`storageAt`), and the **atomic per-construct frame-local
simulation bricks**. The bricks state facts about exp003 `Frame`/`Runs` only, so
they are **shared** across v1 and the v2 flagship (v2's `SimStmt`/`SimTerm`/
`Materialise*`/`StashTail` consume them). The `Match` *structure* invariant itself is
the v1 artifact, superseded by v2's `Corr`.

| decl | kind | role | callers |
|---|---|---|---|
| `pcOf` (:66) | def | **terminal-for-flagship** — the offset-table cursor address; pervasive | MatDecLower, LowerConforms, LowerDecode:98, SimTerm:89, SimStmt:82 (+many) |
| `blockAt_of_toList` (:83) | theorem | shared-infra | DecodeAnchors:169 |
| `pcOf_eq_anchor` (:89) | theorem | **terminal-for-flagship** | DecodeAnchors:150, SimTerm:89,490, SimStmt:82 |
| `flatBytes_at_pcOf` (:101) | theorem | shared-infra — base case of `flatBytes_at_pcOf_offset` | DecodeAnchors:207,230 |
| `selfStorage` (:113) | def | **terminal-for-flagship** — EVM side of `M3`/`StorageAgree` | LowerConforms, LowerDecode, SimTerm, SimStmt (many) |
| `storageAt` (:120) | def | **terminal-for-flagship** — self-addr storage lens | SimTerm, SimStmt (`selfStorage_eq_storageAt`) |
| `Match` (:125) | structure | **genuinely-superseded** — the v1 invariant; **never instantiated / no field ever accessed** (`.storage_eq` grep is empty). Replaced by `Corr` (`SimStmt.lean:103`), whose overlapping field names (`stack_nil`/`code_eq`/`pc_eq`/`can_modify`) are what LowerDecode/LowerConforms read | none (docstrings only) |
| `sim_imm` (:150) | theorem | **terminal-for-flagship** | MaterialiseGas:202, MaterialiseRuns:459,884, StashTail:189, SimTerm:377,398,408 |
| `sim_gas` (:162) | theorem | **terminal-for-flagship** | StashTail:358, MaterialiseRuns |
| `sim_add` (:174) | theorem | **terminal-for-flagship** | MaterialiseRuns:1195 |
| `sim_lt` (:186) | theorem | **terminal-for-flagship** | MaterialiseRuns:1320 |
| `sim_sload` (:199) | theorem | **terminal-for-flagship** | StashTail:468 (+ SimStmt/LowerDecode refs) |
| `sstoreFrame_storage_self'` (:213) | theorem | shared-infra (internal) — feeds `sim_sstore` | `sim_sstore` (Match:279) only |
| `sstoreFrame_storage_frame'` (:234) | theorem | shared-infra (internal) — feeds `sim_sstore` | `sim_sstore` (Match:281) only |
| `sim_sstore` (:265) | theorem | **terminal-for-flagship** — covers `value = 0` (slot clear) | SimStmt:438 |
| `popFrame_code/validJumps/pc/stack` (:292/295/301/304) | @[simp] | shared-infra (simp set) | SimStmt:698,712,719,723,724 |
| `popFrame_addr` (:298), `popFrame_gas` (:307) | @[simp] | shared-infra (simp set) — no explicit citation; fire implicitly as part of the `popFrame_*` simp family | none explicit |
| `sim_mload` (:324) | theorem | **terminal-for-flagship** | MaterialiseRuns:942 |
| `sim_mstore` (:344) | theorem | **terminal-for-flagship** | StashTail:207 |
| `halt_stop` (:368) | theorem | **terminal-for-flagship** | SimTerm:275 (`sim_term_halt_stop`) |
| `returnWordPost` (:387) | def | **terminal-for-flagship** — the RETURN(0,32) post-state | SimTerm:440,442,443,467 |
| `stepFrame_return_word` (:403) | theorem | **terminal-for-flagship** | SimTerm:433 |
| `M_zero32_idem` (:443) | theorem | shared-infra (internal) — feeds `memExpWords_zero32_covered` | Match:464 only |
| `memExpWords_zero32_covered` (:454) | theorem | **terminal-for-flagship** — RETURN window coverage witness | SimTerm:432 |
| `sim_call` (:479) | theorem | **terminal-for-flagship** — `Runs.call` wrapper | SimStmt:662 |
| `call_reflects_lowered` (:519) | theorem | **terminal-for-flagship** — the §5 CALL reflexivity headline | CallRealises:92 |
| `lower_preserves_discharge` (:550) | theorem | genuinely-superseded-for-flagship — v1 top-level boundary discharge; **zero consumers repo-wide** (not even the dead acyclic capstone LowerConforms:1188). The live path discharges via `SimTerm.sim_term_halt_*` + LowerConforms | none anywhere |
| `lower_preserves_stop` (:562) | theorem | genuinely-superseded-for-flagship — as above; zero consumers | none anywhere |
| `lower_preserves_ret` (:577) | theorem | genuinely-superseded-for-flagship — as above; zero consumers | none anywhere |

---

## 2. Cluster sub-DAG + entry/exit edges

Intra-cluster imports:

```
SmallStep  ──►(imports Spec.IR, Evm)
Call       ──► SmallStep, Spec.IR
Create     ──► SmallStep, Spec.IR
StorageErase ──►(Evm, Batteries, BytecodeLayer.Semantics.Maps)   [no intra-cluster dep]
Match      ──► SmallStep, Call, StorageErase   (+ LoweringLemmas, Layout, BytecodeLayer.Hoare[.CallSequence])
```

Entry edges (cluster ← other clusters): `Spec.IR` (into SmallStep/Call/Create);
`LoweringLemmas`,`Layout` (Decode/CFG cluster, into Match); `BytecodeLayer.*` (exp003,
into Call/Create/StorageErase/Match).

Exit edges (cluster → consumers):
- `Match` → **DecodeAnchors, JumpValid, MaterialiseRuns, MaterialiseGas, CallRealises**
  (the module import fan-out), and its `sim_*`/`pcOf`/`selfStorage`/`storageAt`/oracle
  headline are transitively consumed by SimStmt, SimTerm, StashTail, LowerDecode,
  LowerConforms, RealisabilitySpec.
- `Call` → only `Match` (module import). Its `evmCallOracle`/`callSuccessFlag`/
  `evmCallOracle_successWord_eq_x` reach LowerConforms/SimStmt/CallRealises/
  RealisabilitySpec via the Match import chain.
- `StorageErase` → only `Match` (module import); names also cited in RealisabilitySpec.
- `SmallStep` → only Call/Create/Match (module imports).
- `Create` → **nothing** (dangling; scaffold).

Key structural fact: the cluster's *live* out-edges carry only frame-local EVM facts
and oracle projections. The v1 `Lir.IRState` semantics never crosses an out-edge —
the flagship re-derives that layer as `Lir.*` in `Spec/Semantics.lean`.

---

## 3. SIMPLIFICATION CANDIDATES (evidence-backed; conservative)

**High confidence (zero references repo-wide):**

- `SmallStep.IRConf` (:69) — grep across all of `LirLean/` matches only its own
  definition line. Genuinely dead.
- `SmallStep.Program.stmtAt` (:127) — same; zero references.

**Superseded-with-named-replacement (defensible, but each is part of the declared
"v1 reference semantics" — confirm the reference layer is being retired before
removal):**

- `Match.Match` structure (:125) — never instantiated; no field accessed
  (`.storage_eq` grep empty). Replacement is `Corr` (`SimStmt.lean:103`). The
  overlapping field names read as `hcorr.*` in LowerDecode/LowerConforms are `Corr`'s,
  not `Match`'s.
- `Match.lower_preserves_discharge` / `lower_preserves_stop` / `lower_preserves_ret`
  (:550/562/577) — zero consumers, including the dead acyclic capstone
  (`LowerConforms.lean:1188`). Live discharge is `SimTerm.sim_term_halt_*` +
  LowerConforms. Superseded by the v2 terminator path.
- `SmallStep.IRState.bindCallResult` (:110) and `Call.IRState.applyCall` (:158) —
  the only two v1 decls that touch the success-word channel; both appear solely in
  docstrings, never called. The v2 channel is `callSuccessFlag` + `CallRealises`.
- `SmallStep.evalExpr` (:89), `IRState.setStorage` (:117), `HaltResult` (:60) — each has a
  live V2 twin (`Lir.evalExpr` :123, `Lir.IRState.setStorage` :108, `Lir.HaltResult` :55) that
  the flagship uses; the v1 originals are never called in the live cone. `setLocal`
  (:101) and the `IRState` struct (:49) survive only to support the above v1 decls.

**Needs confirmation (do NOT remove):**

- `Create.lean` in full — dangling import graph, but the settled roadmap keeps it as
  the CREATE-first-class scaffold (its CALL twin is load-bearing). Classify as
  incremental, not dead.
- `popFrame_addr` / `popFrame_gas` (:298/307) — no explicit citation, but they are
  `@[simp]` members of the `popFrame_*` family and may fire implicitly. Keep unless a
  build check confirms they are never needed by any `simp` call.

**Caveat on the whole "v1 semantics" group:** the fleet grounding calls
`SmallStep`/`Call`/`Create`/`Match` the deliberate *v1 reference small-step* layer.
The superseded-for-flagship decls above are honestly unused by the live v2 cone, but
whether to delete them is a scoping decision about whether the v1 reference is still
wanted — flag, don't silently cut.
