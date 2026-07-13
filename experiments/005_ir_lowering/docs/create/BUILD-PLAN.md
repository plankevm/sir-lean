# CREATE / CREATE2 build plan (authoritative handoff)

> **P9 status note (2026-07-08).** This plan predates the Phase 2A deletion pass.
> `Expr.slot`, legacy fuel materialisation, `MatFueled`, `Assembly/Acyclic.lean`, and
> `NoSlotSource` references below are historical; the current value channel uses `Loc` and
> `matCache`.

Date: 2026-07-04. Branch: `exp005-create` in worktree `.worktrees/create-build`.
This is the **single doc future sessions read** to understand and continue the
CREATE build. It is a build reference, not a re-derivation — the derivations live
in the sources it cites. Paths are into `experiments/005_ir_lowering/LirLean/`
unless prefixed `exp003:` (= `experiments/003_bytecode_layer/`).

Source docs this consolidates (read them for the *why*; this doc is the *what/where*):
- `docs/eval-2026-07-04/create-implementation-plan.md` — the full read-verified survey (steps, DAG, risks R1–R7).
- `docs/eval-2026-07-04/create-step0-spike.md` — the Step 0 GO/NO-GO spike (retired R1/R4).
- `docs/create/stream-decision.md` — the R2 fork decision (parallel `CreateStream`, option A).

---

## 0. Strategy: mirror CALL, reuse three tiers

CREATE is built by transcribing the CALL ecosystem statement-for-statement. The
CALL template chain is:

```
Spec/IR.CallSpec → Semantics.EvalStmt.call → Lowering.emitStmt .call
  → Frame/Call.evmCallOracle → Frame/Match.call_reflects_lowered
  → CallRealises.evmV2CallEntry → Spec/Recorder.recordCall
  → Decode/Modellable clause-1 → flagship (Realisability/RealisabilitySpec)
```

Every CREATE artifact is the twin of the correspondingly-named CALL artifact.
The reuse splits into three tiers:

**Tier 1 — already shared, zero work (engine + reference layer).** The exp003
engine/drive altitude is already CREATE-complete and axiom-clean, and unifies both
kinds:
- `contractAddressBytes` (exp003:Create.lean:22) handles CREATE (`salt=none`, RLP
  `[creator,nonce]`) *and* CREATE2 (`salt=some`, `BE 255 ++ creator ++ salt ++
  KEC initCode`) in one function; `contractAddressBytes_create_isSome` (:38) proves
  RLP totality (the backlog "planned" item is STALE).
- `beginCreate` (exp003:Create.lean:64, **total**), `endCreate` (:141),
  `resumeAfterCreate` (:189, `Except`-typed — see R4), `createArm`
  (exp003:System.lean:73), `CreateResult` (exp003:Params.lean:63).
- Engine: `createDescent` (BytecodeLayer/Hoare/Descent.lean:502), the `.needsCreate` invariants,
  `endFrame_create_accPresent` (BytecodeLayer/Hoare/DriveMono.lean:87), the `.create`-kind arms
  in `drive`-reconstruction (BytecodeLayer/Hoare/DriveRuns.lean).

**Tier 2 — mechanical CALL twins (the bulk of the build).** Each is a
copy-rename-rethread of its CALL sibling with an identical `(World × Word)` element
type: `CreateSpec`/`Stmt.create`, `CreateStream`, `EvalStmt.create`,
`emitStmt .create`, `create_reflects_lowered`, `evmV2CreateEntry`, `recordCreate`,
`realisedCreate`, `createSuffix`. The oracle twin (`CreateOracle`,
`createAddrOrZero`, `evmCreateOracle`) is **already written and green** in
`Frame/Create.lean` (110 LOC, in the default cone via `LirLean.lean`) but consumed
by nobody yet — Step 5 is where it first gets consumed.

**Tier 3 — genuinely new, CREATE-specific costs.** Three things CALL never needed:
1. The `Runs.create` node + `CreateReturns` in exp003 (the 63/64 partiality) —
   **DONE** (Step 0, see below).
2. `create_reflects_lowered` is **not `rfl`-clean** (R3): `evmCreateOracle.postStorage`
   reads `result.accounts` directly while the resumed frame's storage comes through
   `resumeAfterCreate` — needs a short unfold, not `rfl`.
3. The sim-tower create `Corr` arm (R5): CREATE's init-code memory window is
   **nonzero**, unlike CALL's zero-window first cut, so the `memAgree`/window-disjoint
   reasoning in the `sim_call_stmt` analogue must carve out the init window.

---

## 1. STATUS (2026-07-04)

**Step 0 (exp003) — DONE.** The `Runs.create` node is cherry-picked into this
worktree (commit `90b76ff`, "exp005 create-spike (Step 0): prototype Runs.create
node in exp003"). Present and green in `exp003:BytecodeLayer/Hoare.lean`:
- `CreateReturns` (Hoare.lean:118) — carries the `.ok resumeFr` witness of the 63/64
  guard (R4 answer: witness-in-node, no new flagship seam).
- `Runs.create` constructor (Hoare.lean:153); `CreateReturns.det` (:215),
  `Runs.create_to_halt` (:301); `CreateReturns.gas_le` (GasMonotone.lean:249);
  descent bricks `driveG_needsCreate` / `drive_descend_create_eq`
  (CallSequence.lean:48/63). All exp003 `Runs` recursions carry the `| create` arm;
  `lake build` from `experiments/003_bytecode_layer` is green (1135 jobs) and
  axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Step R2 (stream fork) — SETTLED.** Commit `0126af4` records the decision:
**Option A, a parallel `CreateStream := List (World × Word)`** as a fourth threaded
channel. (Design settled; the Lean threading is done in Step 2.)

**Step 0R — NOT DONE, this is the FIRST build task.** Step 0 added the `Runs.create`
*constructor*; every exhaustive `Hoare.Runs` elimination in **exp005** now has a
missing `.create` match-arm and will fail to build. These arms are mechanical
(mostly contradiction/one-liners) and non-soundness. See §2 Step 0R for the exact
five sites (already relocated to their post-reorg/post-split files).

Everything from Step 1 onward (IR node and up) is unbuilt.

---

## 2. Ordered build steps

Bottom-up so each step builds green on the previous (proof-first, no sorry-scaffold
in the default cone). Build often — caches are warm, builds are incremental. Commit
locally on `exp005-create` at each green step.

### Step 0R (exp005) — add the `.create` arms the Step-0 constructor forces — **DO FIRST**

Goal: restore a green exp005 default build after the `Runs.create` constructor. Five
sites (from spike §3b, relocated to current reorged/split paths):

| # | File:line | Lemma | Arm needed |
|---|-----------|-------|-----------|
| 1 | `Materialise/CleanHaltExtract.lean:408` | `halted_runs_eq` | contradiction `| create` (trivial) |
| 2 | `Realisability/Machinery.lean:203` | `runs_halt_eq` | contradiction `| create` (trivial) |
| 3 | `Realisability/Machinery.lean:403` | `runs_kind` | `| create` via `resumeAfterCreate_kind` (BytecodeLayer/Hoare/Descent.lean) + `stepFrame_needsCreate_inv` (both exist) |
| 4 | `Realisability/Machinery.lean:1390` | `atReachableBoundaryVJ_of_runs` | `| create` needs NEW edge `atReachableBoundaryVJ_create` (twin of `..._call`); geometry facts exist |
| 5 | `Drive/CallPreservesSelf.lean:235` | `selfPresent_runs` | `| create` needs NEW edge `CreatePreservesSelf`, discharge via `resumeAfterCreate_exec_accounts_present` (Descent.lean:373) + `endFrame_create_accPresent` (DriveMono.lean:87), both exist |

Note: sites 2–4 (`runs_halt_eq`/`runs_kind`/`atReachableBoundaryVJ_of_runs`) were in
the monolithic `RealisabilitySpec.lean` in the spike doc; the 4-way split (commit
`f0f2b15`) moved them into `Realisability/Machinery.lean`. CALL twin: none — this
is pure ripple. Risk: LOW (spike §3b confirmed all helpers exist).

### Step 1 (exp005) — IR node

Goal: `Spec/IR.lean` gains `CreateSpec` + `Stmt.create`. CALL twin: `CallSpec` (:43),
`Stmt.call` (:85).
- `structure CreateSpec` fields: `value initOffset initSize salt : Tmp`;
  `resultTmp : Option Tmp` for the pushed address. The IR create statement is
  CREATE2-only.
  `deriving DecidableEq, Repr`. Post-P9, the result stash is represented by `Loc.slot`
  in the lowering allocation layer.
- `Stmt.create (cs : CreateSpec)`.
Risk: HIGH blast radius (R5) — a new `Stmt` constructor breaks every exhaustive
`Stmt` match: `EvalStmt`/`evalExpr` (Semantics), `emitStmt`/`defsOf` (Lowering),
`Frame/SmallStep`, `Materialise/MaterialiseRuns`, the `SegAligned` emit-ladder, the
sim tower. Expect a spread of mechanical `.create` arms before green — the deepest of
these (the sim `Corr` arm) is deferred to Step 5.

### Step 2 (exp005) — v2 semantics arm (flagship consumes this)

Goal: `Spec/Semantics.lean` gains `CreateStream` + `EvalStmt.create`; `RunStmts` /
`RunFrom` / `IRRun` gain the `CreateStream` index (threaded inertly). CALL twin:
`CallStream` (:99), `EvalStmt.call` (:187-195). **Stream decision (R2) = Option A**,
per `docs/create/stream-decision.md`:
- `abbrev CreateStream := List (World × Word)` (Semantics.lean, next to :99). Element
  type identical to `CallStream` (the `Word` carries `createAddrOrZero`, Create.lean:75,
  as `CallStream`'s carries the 0/1 flag).
- The three relations widen to 4 channels (`EvalStmt`/`RunStmts`/`RunFrom`) + `IRRun`
  gains `(D : CreateStream)`. Every **existing** constructor gains `{D : CreateStream}`
  and threads `D` **unchanged** (inert — exactly as it threads `T`/`C` today). Only
  the new arm pops it.
- `EvalStmt.create` (concrete Lean in stream-decision.md §3c): guards read
  `cs.value/initOffset/initSize` from `st.locals`, **pop the head `(world', addrW)`
  of `D`**, set `world := world'`, bind `addrW` at `cs.resultTmp` if present; `T`, `C`
  unchanged. `salt` is not read in the first cut (CREATE2 = §4 delta).
- Flagship conclusions (RS) gain a 4th stream arg `(realisedCreate log
  params.recipient)` next to `realisedCall`; until Step 6 lands they may carry an
  abstract `D`/`[]` (flagship is WIP).

Why Option A (not the merged/tagged stream B): ordering lives in the sequential
statement walk (`RunStmts`/`RunFrom` thread each stream left-to-right; each `Stmt`
pops only its own kind's head), NOT in the stream — so two per-kind channels
reconstruct any CALL;CREATE;CALL interleaving correctly (stream-decision.md §1). B
would rewrite the fragile R3/R7 region around the open flagship sorries
(`realisedCall_cons` rfl-cleanliness, `RecorderCoupled.callSuffix`, R7e); A threads
inertly and touches none of it. B remains an optional cosmetic refactor AFTER R3/R7
close. Risk: MEDIUM (large but mechanical, inert-threading blast radius — ~137
`RunFrom`, ~74 `EvalStmt`, ~72 `RunStmts` refs, plus the flagship mirror inductives
`RunFromV/RunFromLeft/RunFromAll` in `Realisability/Surface.lean` and
`SimStmtStep` in `Machinery.lean`/`Witness.lean`). See stream-decision.md §2.4: the
11 open sorries are undisturbed (3 *statements* gain a 4th arg, 0 proofs burdened).

### Step 3 (exp005) — v1 semantics arm (keeps v1 green)

Goal: `Frame/SmallStep.lean` gains `IRState.applyCreate` (twin of `IRState.applyCall`,
`Frame/Call.lean:158`) writing `storage := oracle.postStorage …` and the address into
the result slot; add the `.create` arm wherever `Stmt` is matched on the v1 line. CALL
twin: `applyCall`. Risk: LOW. Lower priority (v1 reference is superseded-for-flagship)
but required to keep v1 compiling once `Stmt` gained a constructor in Step 1.

### Step 4 (exp005) — lowering

Goal: `Spec/Lowering.lean` emits CREATE. CALL twin: `emitStmt .call` (:191-200),
`defsOf` call arm (:254).
- `Byte.create2 := 0xf5` in the `Byte` table (:46-61) — verify the byte against
  exp003 `Evm/Instr.lean`.
- `emitStmt .create`: materialise `salt`, `initSize`, `initOffset`, then `value`,
  emit `CREATE2`, then stash the pushed address to `slotOf t` via
  `PUSH slot; MSTORE` if `resultTmp = some t`, else `POP` (byte-identical to the CALL
  result stash).
- `defsOf` create-result stash arm: `.create ⟨…, some t⟩ → some (t, Loc.slot (slotOf t))`
  in the post-P9 allocation shape.
Risk: MEDIUM — the `defsOf` create arm used to interact with the old allocation-faithfulness
lemma; post-P9 the live companion facts are the `defsOf`/`rematOf` projection and `defEnv`
first-find lemmas in `Decode/LoweringLemmas.lean`, which must cover the new arm.

### Step 5 (exp005) — `Frame/Match` reflexivity (first CONSUMES the oracle)

Goal: `Frame/Match.lean` gains `sim_create` + `create_reflects_lowered`. CALL twin:
`sim_call` (:479, a `Runs.call` wrapper), `call_reflects_lowered` (:519).
- `sim_create` must be `Runs.create hc rest` — this is exactly why Step 0's
  `Runs.create` constructor is the prerequisite (without it `sim_create` is
  unstatable).
- `create_reflects_lowered`: given `CreateReturns createFr resumeFr`, produce
  `∃ result pd, … ∧ (∀ addr key, evmCreateOracle.postStorage result pd addr key =
  storageAt resumeFr addr key) ∧ evmCreateOracle.addressWord result pd =
  createAddrOrZero result pd`.
Risk: HIGH (R3, known-hard). `call_reflects_lowered` closes the storage side by `rfl`
because `evmCallOracle` projects `resumeAfterCall` directly. `evmCreateOracle.postStorage`
reads `result.accounts` **directly** (Create.lean:100-101, kept total because
`resumeAfterCreate` is `Except`-typed), while the resumed frame's storage is
`(resumeAfterCreate result pd).exec.accounts`. `resumeAfterCreate` writes `accounts :=
result.accounts` (exp003:Create.lean:203-204), so they coincide, but through the
63/64 guard and the `replaceStackAndIncrPC`/`activeWords` wrapper — **budget a short
unfold, not a `rfl`**. This is the create-specific proof cost.

Also here (part of Step 1's deferred sim ripple): the sim-tower create `Corr` arm,
the twin of `sim_call_stmt` (`Sim/SimStmt.lean:576`, the 28-hyp shape lemma). Risk:
HIGH (R5, the deepest exp005 proof). CREATE's init-code memory window
`MachineState.M … initOffset initSize` (exp003:Create.lean:207) is **nonzero**,
unlike CALL's zero-window first cut, so the `memAgree`/`slot_windows_disjoint`
reasoning must carve out the init window. Keeping the **empty-init first cut**
(`offset=size=0`) collapses this window to zero and is what makes the first landing
tractable (see R7 below).

### Step 6 (exp005) — recorder / stream realisation

Goal: fill the `CreateStream` with real recorded deliveries. CALL twins in
`CallRealises.lean` and `Spec/Recorder.lean`.
- `CallRealises.lean` (or a sibling `CreateRealises.lean`): `evmV2CreateEntry
  result pd self : World × Word := ((fun key => evmCreateOracle.postStorage result pd
  self key), evmCreateOracle.addressWord result pd)` (twin of `evmV2CallEntry` :59);
  `createRealises_bridge` (twin of `callRealises_bridge` :85) off Step 5.
- `Spec/Recorder.lean`: **un-drop** the create delivery — `recordCall`'s `.create _ =>
  callAcc` (:172) becomes a recording arm into a `createAcc : List CreateRecord`;
  add `CreateRecord` (twin of `CallRecord` :85); widen `driveLog`'s result tuple by
  **appending** `× List CreateRecord` (:184; the tuple also appears in
  `Realisability/Machinery.lean`), threaded inertly through the existing call arms,
  gated on `rest.isEmpty` (top-level only); `createStreamOf`/`realisedCreate` (twins
  of :288/:296).
- `RecorderLemmas.lean`: `realisedCreate_cons` (twin of `realisedCall_cons` :44,
  `rfl`-clean by the same `simp … List.map_cons`).
- `Realisability/Surface.lean` `RecorderCoupled` (:508): `createSuffix`/`createPrefix`
  fields (twins of `callSuffix`/`callPrefix`).
Risk: MEDIUM. Parallel additions; touch no existing call/gas/sload declaration
(stream-decision.md §2.3–2.5).

### Step 7 (exp005) — drive integration: RETIRE the CREATE exclusion

Goal: turn the flagship's *proof that no CREATE occurs* into *permission for CREATE
descents*. This is a **subtraction**, lower-risk than the additions.
- `Decode/Modellable.lean`: delete/weaken the `NotCreate` clause (`notCreate_of_atReachableBoundary`
  :25); replace with a localized "descents occur exactly at emitted CREATE/CALL sites"
  predicate over the R6 boundary walk. Re-state `lower_modellable` to permit CREATE
  descents.
- `Decode/NoCreateBytes.lean` (`SegAlignedSafe`-style tower) + `Decode/SegAligned.lean`:
  the "no CREATE byte at boundary" restriction is retired. The three `SegAligned*`
  towers were already collapsed to one `IsLoweringOp`-parameterised tower
  (`SegAlignedP`, commit `6420030`; `Decode/BoundaryReach.lean`). The clean move is to
  add `0xf0`/`0xf5` to `IsLoweringOp` (`BoundaryReach.lean`) so CREATE lands in one
  place — do NOT re-prove a CREATE-permitting tower. (R6 dedup already done, so this
  is direct.)
- Generalise `runs_of_drive_ok` (`BytecodeLayer/Hoare/DriveRuns.lean:283`): delete the
  `ModellableStep` create clause and build a `Runs.create` node in the `.needsCreate`
  arm (:364-365, currently `absurd … (hmodel …).1`), mirroring the `.needsCall` code
  arm. The two hardest ingredients (`driveG_needsCreate`, a fuel-bounded
  `drive_descend_create_eq`) are already green from Step 0. The genuinely-new sub-case
  is the `resumeAfterCreate = .error .OutOfGas` (63/64 OOG) branch, which does NOT
  build a `Runs.create` node — it must produce the same halting terminal via exception
  delivery (spike §3c/§4). This is the "largest single proof-engineering item"
  remaining. Risk: MEDIUM-HIGH (the OOG branch), but de-risked by the spike.

### Step 8 (exp005) — flagship obligation

Goal: close (or, honestly, extend the WIP statements of) the CREATE realisability
leaf in `Realisability/RealisabilitySpec.lean`. CALL twin: the R3 call-cursor tie.
- Keep the public `IRWellFormed` + `codeFits` + `stackFits` envelope and rebuild the
  internal `WellLowered` adapter as today. `Conforms` already compares world AND result,
  and a CREATE program's observable is still a `(world, IRHalt)` pair.
- The R3 call-cursor tie (`evmV2CallEntry` identified with the call cursor) gains a
  create-cursor sibling; R6 geometry (`atReachableBoundaryVJ_*`) must admit CREATE
  boundary heads.
- Extend the `exProg` witness to exercise a CREATE (and later CREATE2) so R12
  non-vacuity covers it — **do this LAST**, only once the machinery is green, to avoid
  adding sorry pressure to the already 11-open-sorry flagship.
Risk: HIGH (this is the sorry-carrier terminal DAG node). Only place a CREATE
obligation can be closed.

### CREATE2-only lowering

The reference supports both CREATE-family opcodes, but the IR create statement lowers
only to CREATE2:
- No new oracle (`createAddrOrZero`/`evmCreateOracle` read `result.address`, computed
  by the CREATE2 path).
- No new reference work (`contractAddressBytes` already branches on `salt`; CREATE2's
  `L_A` is unconditionally total — needs *less* totality plumbing than CREATE).
- Lowering: materialise `salt`, `initSize`, `initOffset`, `value`, then emit
  `Byte.create2` (0xf5); stash/discard the pushed address as usual.
- Semantics/recorder/Match/drive: kind-agnostic (project `result`/`pd`, which encode
  the salt via `PendingCreate`; `createArm` already takes `salt : Option ByteArray`).

---

## 3. DAG order (build sequence)

```
exp003 Hoare/DriveRuns (Step 0, DONE)
  → exp005 Step 0R (the five .create arms)      ← FIRST BUILD TASK
  → Spec/IR (Step 1)
  → { Spec/Semantics (Step 2), Spec/Lowering (Step 4), Frame/SmallStep (Step 3) }
  → { Decode cluster (LoweringLemmas/BoundaryReach), Frame/Match (Step 5) }
  → { CreateRealises, Spec/Recorder (Step 6) }
  → { Decode/Modellable, Decode/NoCreateBytes (Step 7) }
  → Realisability/RealisabilitySpec (Step 8)
```

Step 1 (`Spec/IR`) is the widest blast radius (every `Stmt` match). Step 8
(`RealisabilitySpec`) is the terminal node nothing imports — the only place an
obligation closes.

---

## 4. Known-hard steps and guardrails (quick index)

- **R1 (`Runs.create` soundness)** — RETIRED. Spike GO; node is green + axiom-clean.
- **R4 (63/64 partiality)** — RETIRED. `CreateReturns` carries the `.ok resumeFr`
  witness; the `.ok` CreateReturns bundle already gives Step 5/Step 7 the `.ok`
  witness they need. The OOG branch is out of scope of `Runs.create` by construction
  (handled by exception delivery in Step 7).
- **R2 (stream fork)** — SETTLED: parallel `CreateStream` (option A).
- **R3 (`create_reflects_lowered` non-`rfl`)** — OPEN, Step 5. Direct-`result.accounts`
  vs. `resumeAfterCreate`-routed storage; short unfold through the 63/64 guard.
- **R5 (sim create `Corr` arm)** — OPEN, Step 5, deepest proof. Nonzero init-code
  memory window vs. CALL's zero window; carve the init window out of `memAgree`.
- **R6 (SegAligned dedup)** — DONE (`SegAlignedP`, commit `6420030`); Step 7 just adds
  `0xf0`/`0xf5` to `IsLoweringOp`.
- **R7 (empty-init first cut)** — GUARDRAIL, keep for the first landing. Fixing
  `value=offset=size=0` collapses the init-code failure surface (no init OOG/REVERT,
  EIP-170/3541, deposit) *and* the R5 memory window. Relaxing it is a **separate
  follow-on** that must carry: a sufficient-fuel hypothesis (kills the `∅`-wipe),
  EIP-2681 nonce-overflow + EIP-3860 init-size preconditions, and sourcing
  `checkpoint.substate` from the warmed `A*` (per create-crosscheck.md, verdict GO).

## 5. Build/commit discipline

- Default cone: `lake build` (LirLean) from `experiments/005_ir_lowering` MUST end
  green AND sorry-free. Flagship: `lake build WIP` may carry ONLY the 11 pre-existing
  tracked sorries — do not add new sorries there unless the step is an explicitly NEW
  tracked CREATE obligation leaf that you REPORT.
- exp003 changes: build `experiments/003_bytecode_layer` too when touched.
- No `sorry`/`admit`/`native_decide` in the default cone, ever. No weakening a theorem
  to dodge a proof. If a step can't close honestly + green, STOP and hand off with the
  precise blocker (file:line, goal, what was tried) — do not scaffold with sorry.
- Commit locally on `exp005-create` at each green step; report the hash.
