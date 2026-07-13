# CREATE / CREATE2 status in exp005 LirLean — where it stands, what implementing it needs

> **V1 coupling status (2026-07-13):** The unused `Frame/SmallStep` machine, `Lir.Frame.Match` structure, and `apply`/`bind` result-slot transformers were deleted. Live IR semantics are in `Spec/Semantics.lean`, live correspondence is `Corr` in `Sim/SimStmt.lean`, and `Frame/Call.lean` / `Frame/Create.lean` retain only oracle projections. References below to deleted declarations are historical.

> **P9 status note (2026-07-08).** This deep dive predates the Phase 2A deletion pass. Legacy
> fuel/materialisation names below are provenance only; the current lowering value channel is
> fold-based over `Loc`/`matCache` and no longer has `Expr.slot`, `materialiseExpr`,
> `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`, or `NoSlotSource`.

Date: 2026-07-04. Read-only deep dive. Paths relative to
`experiments/005_ir_lowering/` unless noted; exp003 = `experiments/003_bytecode_layer/`.

## TL;DR

CREATE is **not** dead and **not** built. It is **prepared, greenfield scaffolding** for a
settled roadmap item (Phase 3.5, "first-class CREATE"). The oracle layer exists and compiles
green; the whole EVM reference layer under it (exp003) is complete, including CREATE2 and the
totality lemma the backlog thinks is still pending. What is missing is the **entire IR surface
and everything downstream of it** (IR node, both semantics, lowering, the Match reflexivity
theorem that would consume the oracle, the recorder/stream arm, and the drive integration). The
"delete Create.lean, it's dead" suggestion in `docs/lirlean-dag-2026-07-04.md` is the shallow
pass; it contradicts the settled roadmap in `docs/target-architecture-2026-07-02.md` and
`docs/execution-plan-2026-07-02.md`, which name this file as an *input* to the CREATE work.

## 1. What exists today (`LirLean/Create.lean`, 110 LOC)

The file mirrors `LirLean/Call.lean` field-for-field. It defines exactly four things:

- `CreateOracle` structure — `Create.lean:64`. Two projections: `postStorage`
  (`CreateResult → PendingCreate → AccountAddress → Word → Word`) and `addressWord`
  (`CreateResult → PendingCreate → Word`).
- `createAddrOrZero` — `Create.lean:75`. The deployed-address-or-0 the opcode pushes, transcribed
  verbatim from exp003's `resumeAfterCreate` `pushedValue` block (soft-fail → 0 on
  `success=false ∨ depth=1024 ∨ value>balance ∨ initCodeSize>49152`, else `.ofNat result.address`).
- `evmCreateOracle` — `Create.lean:99`. The concrete instantiation: `postStorage` reads
  `result.accounts` through the `find?/lookupStorage` lens; `addressWord := createAddrOrZero`.
- `evmCreateOracle_addressWord_eq` — `Create.lean:108`, `rfl`.

**Build status:** it is in the default build cone — imported at `LirLean.lean:22` — so it compiles
green. **Usage status:** repo-wide grep (`grep -rn "CreateOracle\|createAddrOrZero\|evmCreateOracle"
LirLean/`) shows every hit is *inside `Create.lean` itself*. Nothing else imports the file
(`grep -rn "LirLean.Create"` on the import graph is empty besides the root). So it is compiled but
not yet consumed.

## 2. Is `CreateOracle` "dead"? No — it is incremental toward a live need

Per the anti-shallow rule: what was it meant to connect to, and is that need gone? It is the
CREATE twin of `evmCallOracle` (`Call.lean:108`), and the CALL oracle is **live and load-bearing**:

- `Match.lean:519` `call_reflects_lowered` states the reflexivity headline over
  `evmCallOracle.postStorage/restoredGas/successWord`.
- `LowerConforms.lean:274,277,301,304` uses `evmCallOracle.postStorage` inside the *actual*
  conformance walk (the realised post-state pin).

So the architecture CreateOracle is scaffolding *for* is not hypothetical — its CALL analogue is in
the flagship. The need is explicitly reaffirmed in the roadmap:
`docs/execution-plan-2026-07-02.md:121-131` ("Phase 3.5 — first-class CREATE … inputs:
`LirLean/Create.lean`'s existing `CreateOracle`/`evmCreateOracle`") and
`docs/target-architecture-2026-07-02.md:182-194` ("CREATE goes first-class (settled 2026-07-02,
supersedes the 'keep parked' course-correction) … inputs are the existing `CreateOracle` layer
(Create.lean)"). The deletion suggestion lives only in the DAG legibility doc
(`docs/lirlean-dag-2026-07-04.md:110` "DEAD … Future CREATE2 scaffold"; `:181` "Delete Create.lean
(dead) — or keep as explicit CREATE2 scaffold … decision: is CREATE2 imminent?"). That doc judges
by import-graph reachability only; the roadmap answers its open question with "yes, keep it."

Caveat to record: the oracle is a deliberate **first cut**. `Create.lean:31-33` collapses the
init-code failure surface (offset = length = 0, value 0 → no init-code OOG/REVERT, EIP-170,
EIP-3541, deposit); richer init code is future work.

## 3. What the IR / semantics / lowering do for CREATE today: nothing

- **IR datatypes** (`Spec/IR.lean`): `Expr` = imm/tmp/add/lt/sload/gas/slot (`:54-74`);
  `Stmt` = assign/sstore/call (`:77-86`); `Term` = ret/stop/jump/branch (`:89-100`). **No CREATE
  node.** (`create-crosscheck.md:86-88` recorded this deliberately: the audit ran ahead of surface.)
- **v1 semantics** (`SmallStep.lean`): `grep -ni create` is empty; `evalExpr`/`stmtPost` have no
  create.
- **v2 semantics** (`IRRun.lean`): `StmtDefinable`/`stmtPost`/`EvalStmt` cover only
  `.assign/.sstore/.call` (`:61-73`). No create; no `IRState.applyCreate` (contrast the CALL
  `IRState.applyCall` at `Call.lean:158` — the create twin does not exist, grep empty).
- **Lowering** (`Spec/Lowering.lean`): `emitStmt` (`:178`) has arms only for `.assign` (`:179`),
  `.sstore` (`:189`), `.call` (`:191`) — **no CREATE/CREATE2 opcode is ever emitted.** `defsOf`
  (`:251-254`) likewise has no create-result stash arm.
- Consequently the conformance drive **structurally excludes** CREATE: `NoCreateBytes.lean`
  (`SegAlignedSafe`, the "lowering emits only 16 non-CREATE opcodes at any head") + `NotCreate`
  discharged by `notCreate_of_atReachableBoundary` (`Decode/Modellable.lean:16-27`, `DriveSim.lean:121-125`).
  Adding CREATE means *retiring* this exclusion, not extending it.

## 4. The EVM reference layer (exp003) — fully supports CREATE **and** CREATE2

Everything the IR would lower *onto* already exists and is green:

- `contractAddressBytes` — exp003 `EVMLean/Evm/Semantics/Create.lean:22`. Handles **both** kinds:
  `salt = none` → RLP `[creator, nonce]` (CREATE); `salt = some` → `BE 255 ++ creator ++ salt ++
  KEC initCode` (CREATE2, unconditionally total).
- `contractAddressBytes_create_isSome` — exp003 `Create.lean:38`. The RLP-totality theorem
  **already proven** (via `Rlp.encode_list_pair_isSome`). **This is exactly the "planned fix" the
  backlog still lists as pending** (see §5).
- `beginCreate` — exp003 `Create.lean:64`, now **total** (dead `.error` derivation arm removed,
  commits `7b34698`/`ad67864`). `endCreate` (`:141`), `resumeAfterCreate` (`:189`), plus `createArm`,
  `PendingCreate`, `CreateResult` in `System.lean` and the drive-loop `.needsCreate` handling.
- **Engine-level CREATE lemmas already green** (`BytecodeLayer/Hoare/Descent.lean`, extracted from the old
  monolith): `createArm_needsCreate_inv` (`:131`), `systemOp_needsCreate_inv` (`:163`),
  `stepFrame_needsCreate_inv` (`:238`), `beginCreate_ok_accounts_present` (`:331`),
  `beginCreate_ok_checkpoint` (`:355`), `resumeAfterCreate_exec_accounts_present` (`:373`),
  `resumeAfterCreate_kind` (`:390`), and the unifying `createDescent : DescentKind` (`:502`) with
  `createDescent_descendImmediate_trivial` (`:538`). Drive presence: `endFrame_create_accPresent`
  (`BytecodeLayer/Hoare/DriveMono.lean:87`) and the `.create`-kind arms in `BytecodeLayer/Hoare/DriveRuns.lean` (`:104,182,250,364`).

So CALL and CREATE are already unified at the **engine/drive** altitude via `DescentKind`; only the
IR-surface-and-up layers are CALL-only.

## 5. The backlog CREATE item is STALE (record-and-fix)

`docs/backlog.md:5-22` ("CREATE address-derivation dead branch") describes making `beginCreate`
total and removing the dead branch as a **"Planned fix (in progress / scheduled)"**. That work is
**already done**: exp003 `beginCreate` is total (`Create.lean:64`), the dead branch is gone, and the
totality lemma exists (`contractAddressBytes_create_isSome`, `Create.lean:38`), consistent with the
MEMORY note ("dead beginCreate .error branch REMOVED … commits 7b34698/ad67864"). The `drive_accounts_
find_mono` CREATE-fault case the backlog says would be removed is likewise moot (drive create step is
proven in place, `BytecodeLayer/Hoare/DriveMono.lean:42-47`). Only the `StackUnderflow` tag-misnomer sub-item
(`backlog.md:24-37`) survives, and it is doubly moot now that the branch producing it is deleted.

## 6. Gap-list to implement first-class CREATE (then CREATE2)

Ordered; each is confirmed-absent by grep. The roadmap (`execution-plan:119-131`,
`target-architecture:182-194`) frames all of this as **instantiating** the existing `DescentKind`
machinery, not duplicating the CALL ecosystem.

1. **IR node.** Add `Stmt.create` + a `CreateSpec` structure to `Spec/IR.lean` (mirror `CallSpec`
   at `:43`). First cut per `Create.lean:31`: fields for value/offset/length may be fixed to the
   empty-init case; carry `salt : Option _` to distinguish CREATE vs CREATE2 from day one; add a
   `resultTmp : Option Tmp` for the pushed address.
2. **Semantics.** Add a `.create` arm to v1 `SmallStep` and to v2 `IRRun` (`StmtDefinable`/
   `stmtPost`/`EvalStmt`, `:61-73`), backed by a new `IRState.applyCreate` (twin of
   `IRState.applyCall`, `Call.lean:158`) that consults `CreateOracle` for the address word and post
   storage.
3. **Lowering.** Add a `.create` arm to `emitStmt` (`Spec/Lowering.lean:178`) emitting operand
   materialisation + `CREATE`/`CREATE2` opcode (mirror the `.call` arm at `:191-197`), and a
   create-result stash arm in `defsOf` (`:254`) so the pushed address becomes an `Expr.slot`.
4. **Match reflexivity — the step that finally CONSUMES `CreateOracle`.** Prove
   `create_reflects_lowered` (twin of `Match.lean:519` `call_reflects_lowered`) pinning
   `evmCreateOracle.postStorage`/`addressWord` to the lowered `resumeAfterCreate` projections. Its
   begin-immediate law is trivial post-RLP-totality (`execution-plan:103-104`,
   `createDescent_descendImmediate_trivial`).
5. **Recorder / stream.** Add a create arm to the descent recorder / call-stream
   (`RecorderLemmas.lean:47` `evmV2CallEntry` has no create twin) — i.e. a `DescentRecord .create`
   arm and one realises-bundle instance. The multi-descent question is the same as multi-CALL (R3');
   solve as a consumed **descent stream** (`execution-plan:130-131`).
6. **Drive integration — retire, don't extend, the exclusion.** Remove/retire `NoCreateBytes.lean`
   and the `NotCreate` clause (`Decode/Modellable.lean:16-27`), replacing them with the localized
   "descents occur exactly at emitted descent sites" predicate over the R6 boundary walk
   (`execution-plan:127-131`). Discharge the create drive step using the already-green `DescentKind`
   `.create` lemmas (§4).
7. **Spec-authoring guardrails (from `create-crosscheck.md`, verdict GO).** Carry: a sufficient-fuel
   hypothesis (kills the EVMYulLean `∅`-wipe, `create-crosscheck.md:73-75`); the `L_A` totality
   lemma (already have `contractAddressBytes_create_isSome`); explicit EIP-2681 nonce-overflow and
   EIP-3860 init-size-cap preconditions (`:76-80`); and source `checkpoint.substate` from the warmed
   `A*` (`:241`) so failure arms don't bind a cold substate.

### CREATE2 as the follow-on (cheap once CREATE lands)

The reference already does both kinds in one function (`contractAddressBytes`, salt branch), and
`createAddrOrZero` is kind-agnostic, so CREATE2 is incremental over CREATE: one extra `emitStmt`/
opcode arm + a salt operand in `CreateSpec`, and the CREATE2 static-mode/size guards which already
live in the reference (`System.lean`). Per `create-crosscheck.md:169-170` CREATE2's `L_A` is
*unconditionally* total (no RLP), so it needs *less* totality plumbing than CREATE, not more.
