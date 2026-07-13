# CREATE (then CREATE2) implementation plan for exp005 LirLean

Date: 2026-07-04. Read-only survey → build plan. The lead WANTS this built.
Paths are into `experiments/005_ir_lowering/LirLean/` unless prefixed `exp003:`
(= `experiments/003_bytecode_layer/`). Every claim below was grep/read-verified.

This plan mirrors, step-for-step, how CALL was built (the CALL ecosystem is the
template: `Spec/IR.CallSpec` → `V2.EvalStmt.call` → `emitStmt .call` →
`Call.evmCallOracle` → `Match.call_reflects_lowered` → `V2/CallRealises` →
recorder `recordCall` → `Modellable` clause-1). The single biggest surprise vs.
the CALL build is in §5: **the exp003 `Runs` abstraction has no CREATE node and no
`CreateReturns` bridge, and `runs_of_drive_ok` is *predicated* on `NoCreate`
precisely because "`.needsCreate` … `Runs` cannot model" (exp003:DriveRuns.lean:27).**
That is a real exp003 dependency, not an exp005 one, and it gates the flagship.

---

## 1. What CREATE support already exists; what is stubbed

### 1a. Present and green — the oracle layer (exp005 `Create.lean`, 110 LOC)

`Create.lean` is the field-for-field twin of `Call.lean`, in the default build cone
(`LirLean.lean:22`), compiling green, but **consumed by nobody** (every ref is
in-file). It supplies exactly:

- `CreateOracle` (Create.lean:64) — two projections: `postStorage`
  (`CreateResult → PendingCreate → AccountAddress → Word → Word`) and `addressWord`
  (`CreateResult → PendingCreate → Word`). Twin of `CallOracle` (Call.lean:79),
  minus the `restoredGas` field (v2 has no gas in state).
- `createAddrOrZero` (Create.lean:75) — the deployed-address-or-0 word CREATE
  pushes, transcribed verbatim from exp003 `resumeAfterCreate`'s `pushedValue`
  block (soft-fail → 0 on `success=false ∨ depth=1024 ∨ value>balance ∨
  initCodeSize>49152`, else `.ofNat result.address`). Twin of `callSuccessFlag`
  (Call.lean:120).
- `evmCreateOracle` (Create.lean:99) — the concrete instantiation. `postStorage`
  reads `result.accounts` through the `find?/lookupStorage` lens; `addressWord :=
  createAddrOrZero`. Twin of `evmCallOracle` (Call.lean:108). NOTE: unlike
  `evmCallOracle` (which projects `(resumeAfterCall result pd).exec.accounts`,
  Call.lean:110), `evmCreateOracle.postStorage` reads `result.accounts` **directly**,
  not through `resumeAfterCreate` — because `resumeAfterCreate` is `Except`-typed
  (it can throw on the 63/64 retention guard, exp003:Create.lean:200) and the oracle
  must stay total (Create.lean:22-27). This asymmetry matters for the reflexivity
  proof in §4/step-8.
- `evmCreateOracle_addressWord_eq` (Create.lean:107) — `rfl`. Twin of
  `evmCallOracle_successWord_eq_x` (Call.lean:128).

### 1b. Present and green — the entire exp003 reference layer (both kinds)

Everything the IR would lower *onto* exists and is proven:

- `contractAddressBytes` (exp003:Create.lean:22) handles **both** kinds in one
  function: `salt=none` → RLP `[creator,nonce]` (CREATE); `salt=some` → `BE 255 ++
  creator ++ salt ++ KEC initCode` (CREATE2).
- `contractAddressBytes_create_isSome` (exp003:Create.lean:38) — RLP totality
  **already proven**; the backlog item (`docs/backlog.md:5-22`) claiming this is
  "planned/in-progress" is STALE (see 00-create-status.md §5).
- `beginCreate` (exp003:Create.lean:64) — **total** (dead `.error` arm removed,
  commits 7b34698/ad67864); `endCreate` (:141); `resumeAfterCreate` (:189,
  `Except ExecutionException Frame`).
- `createArm` (exp003:System.lean:73) emits `Signal.needsCreate params pending`;
  `PendingCreate` (exp003:Frame.lean:74); `CreateResult extends CallResult`
  (exp003:Params.lean:63); `FrameResult.toCreateResult` (exp003:Frame.lean).
- Engine altitude already CREATE-complete and axiom-clean: `createDescent :
  DescentKind` (BytecodeLayer/Hoare/Descent.lean:502) + `createDescent_descendImmediate_trivial`
  (:538); `createArm_needsCreate_inv`/`systemOp_needsCreate_inv`/
  `stepFrame_needsCreate_inv` (BytecodeLayer/Hoare/Descent.lean); `endFrame_create_accPresent`
  (BytecodeLayer/Hoare/DriveMono.lean:87); the `.create`-kind arms in `drive`-reconstruction
  (BytecodeLayer/Hoare/DriveRuns.lean:104,182,250,364).

So CALL and CREATE are unified at the **engine/drive** altitude already; only the
IR-surface-and-up layers, **and the `Runs`-level bridge**, are CALL-only.

### 1c. Missing — the IR surface and everything above it (grep-confirmed absent)

- **IR node.** `Spec/IR.lean`: `Stmt` = assign/sstore/call only (:77-86); no
  `Stmt.create`, no `CreateSpec`. `Expr.slot` (:73) — the spill marker CREATE's
  pushed address will reuse — already exists.
- **v1 semantics.** `SmallStep.lean`: `grep -i create` empty; no `IRState.applyCreate`
  (contrast `IRState.applyCall` Call.lean:158).
- **v2 semantics.** `Spec/Semantics.lean`: `EvalStmt` (:164), `RunStmts` (:198),
  `RunFrom` (:228) cover assign/sstore/call only; no `.create` constructor. The
  `CallStream` (:99, `List (World × Word)`) is the call-result stream; there is no
  create stream.
- **Lowering.** `Spec/Lowering.lean`: `emitStmt` (:178) emits opcodes for
  assign/sstore/call only — no `CREATE`(0xf0)/`CREATE2`(0xf5) byte in the `Byte`
  table (:46-61) and no create arm; `defsOf` (:247-256) has a call-result stash arm
  (`.call ⟨_,_,some t⟩ → Expr.slot`) but no create-result stash arm.
- **Match reflexivity.** No `create_reflects_lowered` (contrast
  `call_reflects_lowered` Match.lean:519); no `sim_create` (contrast `sim_call`
  Match.lean:479, which is just a `Runs.call` wrapper — and there is no `Runs.create`
  to wrap, see §5).
- **Recorder / stream.** `Spec/Recorder.lean`: `recordCall` (:172) explicitly
  **drops** create deliveries (`| .create _ => callAcc`); `driveLog` (:186) threads
  gas/sload/call accumulators only; no create channel. `V2/CallRealises.evmV2CallEntry`
  (:59) has no create twin.
- **Drive integration is a structural EXCLUSION, not a gap to fill.** The flagship
  currently *proves* no-CREATE: `NoCreateBytes.lean` (`SegAlignedSafe` — "lowering
  emits only 16 non-CREATE opcodes at any head", :50) + `Decode/Modellable.lean`
  `NotCreate` clause discharged by `notCreate_of_atReachableBoundary` (:25), wired
  into the flagship via `lower_modellable` at RS:1255 and RS:3677. Adding CREATE
  means **retiring** this exclusion, not extending it.

### 1d. Missing — the exp003 `Runs`-level CREATE bridge (the load-bearing gap)

- `grep -rn "CreateReturns\|Runs.create"` across BOTH experiments returns **nothing**.
  exp003 `Runs` (Hoare.lean:120-123) has a `call` constructor
  (`hcall : CallReturns callFr resumeFr`) but **no `create` constructor**.
- `runs_of_drive_ok` (BytecodeLayer/Hoare/DriveRuns.lean:283) is *predicated* on `ModellableStep`
  (:142) whose clause 1 is `∀ cp pending, stepFrame fr ≠ .needsCreate cp pending`,
  and the header states why: "`.needsCreate` arm, which `Runs` cannot model"
  (DriveRuns.lean:27). So CREATE is not merely absent from the IR — it is *actively
  excluded from the `Runs` abstraction the flagship's conclusion (`RunFrom` ⇐
  `runs_of_drive_ok`) rides*.

**Bottom line:** the oracle + the whole reference/engine layer are ready; the work
is (i) the exp005 IR-surface-and-up mirror of CALL, and (ii) a genuine exp003
addition — `CreateReturns` + `Runs.create` + de-`NoCreate`-ing `runs_of_drive_ok`.

---

## 2. Ordered list of definitions + lemmas to add (mirroring CALL)

Ordered bottom-up so every step builds green on the previous (proof-first, no
sorry-scaffold). Steps 0 and 6b are the exp003 additions; all others are exp005.

### Step 0 (exp003) — `CreateReturns` + `Runs.create` + generalise `runs_of_drive_ok`

This is the keystone and must go first, because nothing above the drive can express
a top-level CREATE without it.

0a. `Hoare.CreateReturns (createFr resumeFr : Frame) : Prop` — twin of
   `CallReturns` (exp003:Hoare.lean:91): `∃ params pending child childRes,
   stepFrame createFr = .needsCreate params pending ∧ EntersAsCode/child-begins-via
   beginCreate ∧ drive (seedFuel …) [] (running child) = .ok childRes ∧ resumeFr =
   (resumeAfterCreate childRes.toCreateResult pending)`. Subtlety: `resumeAfterCreate`
   is `Except`-typed, so `CreateReturns` must carry the `.ok resumeFr'` witness of the
   63/64 guard (or fold the guard into the bundle) — this is the one place CREATE is
   strictly harder than CALL. `CreateReturns.det` mirrors `CallReturns.det`
   (Hoare.lean:~160).

0b. `Runs.create` constructor on the `Runs` inductive (Hoare.lean:120): `| create
   {createFr resumeFr fr'} (hc : CreateReturns createFr resumeFr) (rest : Runs
   resumeFr fr') : Runs createFr fr'`. Extend `Runs.trans` (Hoare.lean:129) and any
   other structural recursion over `Runs` with the new arm (grep `induction … with |
   call`; each gets a `| create` arm — mechanical, mirrors `| call`).

0c. Generalise `runs_of_drive_ok` (DriveRuns.lean:283): weaken `ModellableStep`
   clause 1 so a `.needsCreate` that resolves through `beginCreate` + a terminating
   child drive builds a `Runs.create` node (using the already-green
   `endFrame_create_accPresent`, `beginCreate_ok_*`, `resumeAfterCreate_*` engine
   lemmas). The `NoCreate` side condition (DriveRuns.lean:127-142) is *deleted*, not
   satisfied. This is the largest single proof-engineering item.

### Step 1 (exp005) — IR node

`Spec/IR.lean`: add `CreateSpec` (mirror `CallSpec` :43) and `Stmt.create`
(mirror `Stmt.call` :85).

- `structure CreateSpec` fields: `value/initOffset/initSize/salt : Tmp`;
  `resultTmp : Option Tmp` for the pushed address. The IR create statement is
  CREATE2-only.
  `deriving DecidableEq, Repr`.
- `Stmt.create (cs : CreateSpec)`.

### Step 2 (exp005) — v2 semantics arm (the flagship consumes this)

`Spec/Semantics.lean`: add `EvalStmt.create` (mirror `EvalStmt.call` :187-195),
`RunStmts`/`RunFrom` need no change (they recurse on `Stmt` generically). The create
step pops a stream head `(world', addrW)` and applies it: `world := world'`, bind
`addrW` at `cs.resultTmp` if present. **Stream decision (see §5 risk R2):** either

- (minimal, mirror-CALL) add a parallel `CreateStream := List (World × Word)`
  (:99 twin) as a *fourth* threaded channel — but then `EvalStmt`/`RunStmts`/`RunFrom`
  all gain a `CreateStream` argument (invasive: 74 `EvalStmt` refs, 137 `RunFrom`
  refs); or
- (recommended, per 00-create-status.md §5 + execution-plan:130-131) a **unified
  descent stream** `List (World × Word × DescentKind)` replacing `CallStream`, where
  CALL and CREATE consume heads positionally in interleaved program order. Cleaner
  long-term, but touches the settled `CallStream` (1c77c07) and every EvalStmt.call
  site.

The element type is identical either way — `(World × Word)` — because a returning
CREATE, like a returning CALL, contributes (post-world, pushed-word). That structural
identity is what makes the descent-stream unification natural.

### Step 3 (exp005) — v1 semantics arm (reference line, keeps v1 green)

`SmallStep.lean`: add `IRState.applyCreate` (twin of `Call.IRState.applyCall`
:158) writing `storage := oracle.postStorage …` and the address into the
`callResult`-analogue slot; add the `.create` arm wherever `Stmt` is matched in the
v1 line. Lower priority (the v1 reference is superseded-for-flagship per
cluster-v1bricks.md) but needed to keep v1 compiling once `Stmt` gains a constructor.

### Step 4 (exp005) — lowering

`Spec/Lowering.lean`:

- `Byte.create2 := 0xf5` in the `Byte` table (:46-61). (Verify against exp003
  `Evm/Instr.lean` opcode bytes.)
- `emitStmt .create` arm (mirror `.call` :191-200): materialise `salt`,
  `initSize`, `initOffset`, then `value`, emit `CREATE2`, then the pushed
  address is stashed to `slotOf t` via `PUSH slot; MSTORE` if `resultTmp = some t`,
  else `POP` — byte-identical to the CALL result stash.
- `defsOf` create-result stash arm (:254 twin): `.create ⟨…, some t⟩ → some (t,
  Expr.slot (slotOf t))`.

### Step 5 (exp005) — `Match` reflexivity (finally CONSUMES the oracle)

`Match.lean`:

- `sim_create` — but note `sim_call` (Match.lean:479) is `Runs.call hcall rest`;
  `sim_create` must be `Runs.create hc rest`, which is exactly why Step 0b (the
  `Runs.create` constructor) is a prerequisite. Without Step 0 this lemma is
  unstatable.
- `create_reflects_lowered` (twin of `call_reflects_lowered` :519): given
  `CreateReturns createFr resumeFr`, `∃ result pd, … ∧ (∀ addr key,
  evmCreateOracle.postStorage result pd addr key = storageAt resumeFr addr key) ∧
  evmCreateOracle.addressWord result pd = createAddrOrZero result pd`. RISK: the
  `postStorage`-side `rfl`-cleanliness that `call_reflects_lowered` enjoys
  (:522-527) may NOT hold, because `evmCreateOracle.postStorage` reads
  `result.accounts` directly while the resumed frame's storage is
  `(resumeAfterCreate result pd).exec.accounts` — and `resumeAfterCreate` *rewrites*
  `accounts := result.accounts` (exp003:Create.lean:203-204), so they should coincide,
  but through the `Except`/63-64-guard and the `activeWords`/`replaceStackAndIncrPC`
  wrapper — a `rfl` is unlikely; expect a short unfold. This is the create-specific
  proof cost.

### Step 6 (exp005) — recorder / stream realisation

`V2/CallRealises.lean` (or a sibling `V2/CreateRealises.lean`):

- `evmV2CreateEntry result pd self : World × Word` (twin of `evmV2CallEntry` :59):
  `((fun key => evmCreateOracle.postStorage result pd self key),
  evmCreateOracle.addressWord result pd)`.
- `createRealises_bridge` (twin of `callRealises_bridge` :85) off
  `create_reflects_lowered`.

`Spec/Recorder.lean`:

- Un-drop the create delivery: `recordCall`'s `.create _ => callAcc` (:172) becomes a
  recording arm into a create channel (or the unified descent channel per §5-R2).
- Add the create accumulator to `driveLog` (:186) — a 4th positional arg mirroring
  `callAcc`, gated identically on `rest.isEmpty` (top-level only).
- `realisedCreate` projection twin of `realisedCall` (:300) / `callStreamOf` (:292).

### Step 7 (exp005) — drive integration: RETIRE the exclusion

- `Decode/Modellable.lean`: delete/weaken the `NotCreate` clause (`NoCreate` :194,
  `notCreate_of_atReachableBoundary` :25). Replace with the localized "descents occur
  exactly at emitted CREATE/CALL sites" predicate over the R6 boundary walk
  (execution-plan:127-131). `lower_modellable` (:380-area, used at RS:1255, RS:3677)
  is re-stated to permit CREATE descents.
- `NoCreateBytes.lean` (`SegAlignedSafe` tower :50): no longer needs the "no
  CREATE byte" restriction. Per cluster-decode findings, `SegAlignedSafe` is one of
  three near-identical `SegAligned*` towers; the cleanest move is to fold it into the
  `IsLoweringOp`-parameterised tower (`SegAlignedLowering`, BoundaryReach.lean:135)
  with CREATE/CREATE2 added to `IsLoweringOp` (:126-129), rather than maintain a
  separate CREATE-excluding tower.

### Step 8 (exp005) — flagship obligation

`V2/RealisabilitySpec.lean`:

- `WellLowered` bundle (:477) and `Conforms` (:155) unchanged in shape — `Conforms`
  already compares world AND result, and a CREATE program's observable is still a
  `(world, IRHalt)` pair.
- The R3 call-cursor tie (`evmV2CallEntry` identified with the call cursor at RS:2856)
  gains a create-cursor sibling; R6 geometry (`atReachableBoundaryVJ_*`, RS:2343-2383)
  must admit CREATE boundary heads.
- The exProg witness (§6, RS:2975) should be extended to exercise a CREATE (and later
  CREATE2) so R12 non-vacuity covers it — but do this LAST, only once the machinery is
  green, to avoid adding sorry pressure to the already 11-open-sorry flagship.

---

## 3. Where each piece slots into the DAG

Using the import graph in the brief:

- **Step 0 (exp003)** is *below the entire exp005 DAG* — it lands in
  `BytecodeLayer/Hoare.lean` + `BytecodeLayer/Hoare/DriveRuns.lean`. `BytecodeLayer/Hoare/DriveRuns` is imported
  by `Decode/Modellable` and `V2/DriveSim`, so changes ripple up to the flagship but the
  engine cluster stays IR-agnostic (cluster-engine: zero LirLean.Spec/V2 imports).
- **Step 1 (`Spec/IR`)** is L0 base; every module transitively re-checks. Adding a
  `Stmt` constructor forces a new match arm in **every** `Stmt` case-split: `evalExpr`/
  `EvalStmt` (Semantics), `emitStmt`/`defsOf` (Lowering), `SmallStep`, `MaterialiseRuns`,
  the `SegAligned*` emit-ladders, the sim tower. This is the widest-blast-radius step;
  expect a day of "add the `.create` arm" across the tree before anything is green.
- **Step 2 (`Spec/Semantics`)** → consumed by `V2/Law`, `DefsSound`, and transitively
  the flagship. If the descent-stream unification (§5-R2) is chosen, this is where the
  `CallStream` signature change originates and ripples through 137 `RunFrom` refs.
- **Step 4 (`Spec/Lowering`)** → consumed by `LoweringLemmas` → `DecodeLower` →
  the whole decode/CFG cluster (`JumpValid`/`NoCreateBytes`/`BoundaryReach`). The
  `defsOf` create arm interacts with `allocate_toDefs` (LoweringLemmas:91) — the
  Phase-A keystone — which must be re-proven to cover the new `defsOf` arm.
- **Step 5 (`Match`)** → sits in the v1-bricks cluster; `create_reflects_lowered`
  exits to `V2/CreateRealises` exactly as `call_reflects_lowered` exits to
  `V2/CallRealises`. Requires Step 0b (`Runs.create`) as an upstream dependency.
- **Step 6 (`V2/CallRealises` + `Spec/Recorder`)** → Recorder is imported by
  `RecorderLemmas` → `SimTerm` and feeds the flagship's `realisedCall`/`realisedCreate`.
- **Step 7 (`Modellable`/`NoCreateBytes`)** → `Modellable` imports `NoCreateBytes`;
  both feed `DriveSim` (cyclic) and the flagship R6. Retiring the exclusion is a
  *subtraction* here, which is lower-risk than the additions elsewhere.
- **Step 8 (`RealisabilitySpec`)** → the WIP sorry-carrier, terminal DAG node. Nothing
  imports it; it is the only place a create obligation can be *closed*.

DAG-order summary: `exp003 Hoare/DriveRuns` → `Spec/IR` → {`Spec/Semantics`,
`Spec/Lowering`, `SmallStep`} → {`LoweringLemmas`/decode cluster, `Match`} →
{`V2/CreateRealises`, `Spec/Recorder`} → {`Modellable`/`NoCreateBytes`} →
`RealisabilitySpec`.

---

## 4. CREATE2-only contract

Cheap by construction, because the reference already supports CREATE2 and the IR
create statement requires a salt tmp:

- **No new oracle.** `createAddrOrZero`/`evmCreateOracle` are already kind-agnostic
  (they read `result.address`, which `beginCreate` computes for the CREATE2 path,
  exp003:Create.lean:27-29,74-76). Zero change.
- **No new reference work.** `contractAddressBytes` (exp003:Create.lean:22) already
  branches on `salt`; CREATE2's preimage is `BE 255 ++ creator ++ salt ++ KEC
  initCode` and — per create-crosscheck.md:169-170 — its `L_A` is *unconditionally*
  total (no RLP), so it needs **less** totality plumbing than CREATE
  (`contractAddressBytes_create_isSome` was CREATE-only).
- **IR:** already covered — `cs.salt : Tmp`.
- **Lowering:** materialise `salt`, `initSize`, `initOffset`, `value`, then emit
  `Byte.create2` (0xf5); stash/discard the pushed address as usual.
- **Semantics/recorder/Match:** the create stream entry and `create_reflects_lowered`
  are kind-agnostic (they project `result`/`pd`, which already encode the salt via
  `PendingCreate`), so no per-kind case-split is needed above the lowering.
- **Drive:** `createArm` (exp003:System.lean:73) already takes `salt : Option
  ByteArray` and handles both; the `IsLoweringOp` set (Step 7) just lists both 0xf0
  and 0xf5.

Net: CREATE2 ≈ one `emitStmt` sub-arm + adding 0xf5 to `IsLoweringOp`.

---

## 5. Risks / unknowns

**R1 (highest) — the `Runs.create` / `CreateReturns` exp003 addition (Step 0).**
This is the load-bearing unknown. `Runs` (exp003:Hoare.lean) has no create node and
`runs_of_drive_ok` is *designed* around excluding CREATE ("`Runs` cannot model
`.needsCreate`", DriveRuns.lean:27). Adding a `Runs.create` constructor forces new
arms in every `Runs` structural recursion in *both* experiments (`Runs.trans`,
`runs_of_drive_ok`, the `Runs.gasAvailable_le` monotonicity ladder the gas
realisability rides, `cleanHalts` linearity, DriveSim's measure). This is an exp003
edit with exp005-wide ripple. It is the single item most likely to blow the estimate.
Confirm with the exp003 owner that a `Runs.create` node is acceptable before starting.

**R2 — CallStream vs. a unified descent stream (Step 2).** The `(World × Word)`
element type is identical for CALL and CREATE, so reuse is structurally natural, but
CALL and CREATE interleave in program order. Two independent parallel streams
(`CallStream` + `CreateStream`) is the minimal mirror-CALL move but is *positionally
wrong* if a program does CALL; CREATE; CALL — each stream would need to know the
absolute position. The correct model is one **merged descent stream** consumed
head-first (00-create-status.md §5, execution-plan:130-131). That means reshaping the
settled `CallStream` (1c77c07, "call-stream replaces function CallOracle") — a large,
already-litigated design surface. Decide this before Step 2; it changes the signature
of `EvalStmt`/`RunStmts`/`RunFrom` (74/72/137 refs).

**R3 — `create_reflects_lowered` is unlikely to be `rfl`-clean (Step 5).**
`call_reflects_lowered` (Match.lean:519) closes by `rfl` because `evmCallOracle`
projects `resumeAfterCall` directly. `evmCreateOracle.postStorage` deliberately reads
`result.accounts` (Create.lean:100-101) rather than `resumeAfterCreate` (which is
`Except`-typed), so the storage-coincidence proof must unfold `resumeAfterCreate`'s
`accounts := result.accounts` write (exp003:Create.lean:203) through the 63/64 guard
and the `replaceStackAndIncrPC` wrapper. Budget a real (short) proof, not a `rfl`.

**R4 — the 63/64 retention guard makes `CreateReturns` partial.** `resumeAfterCreate`
can `throw .OutOfGas` (exp003:Create.lean:200). `CallReturns` has no analogue (CALL's
resume is total). `CreateReturns` must either carry the `.ok` witness or the flagship
must supply a "enough gas retained" side condition — a new honest seam that CALL did
not have. Likely lands as a `PrecompileAssumptions`-style bundle entry (RS:550).

**R5 — `Stmt.create` blast radius (Step 1).** Adding a `Stmt` constructor breaks every
exhaustive `Stmt` match in the tree (Semantics, Lowering, SmallStep, MaterialiseRuns,
the three `SegAligned*` emit-ladders, SimStmt's per-stmt arms). Most are mechanical
`.create` arms, but the sim tower's `Corr`-re-establishment arm for create
(analogous to `sim_call_stmt`, SimStmt.lean:576, the 28-hyp shape lemma) will be a
substantial new proof — CREATE's memory footprint (init-code window `MachineState.M
… initOffset initSize`, exp003:Create.lean:207) is nonzero, unlike CALL's zero-window
first cut, so the `memAgree`/`slot_windows_disjoint` reasoning that `sim_call_stmt`
relies on may need the init window carved out. This is the deepest exp005 proof.

**R6 — retiring `NoCreateBytes` interacts with the SegAligned dedup (Step 7).**
cluster-decode identifies `SegAlignedSafe`/`SegAlignedLowering`/`SegAligned` as a
triplication collapsible to one `IsLoweringOp`-parameterised tower. The clean way to
add CREATE to the "allowed at boundary" set is to do that dedup first (add 0xf0/0xf5
to `IsLoweringOp`, BoundaryReach.lean:126), so CREATE lands in one place instead of
re-proving a CREATE-permitting `SegAligned` tower. Sequence the C1 dedup before Step 7.

**R7 — empty-init-code first cut is load-bearing for soundness, not just scope.**
Create.lean:31 fixes `offset=length=0, value=0` to collapse the init-code failure
surface (no init OOG/REVERT, EIP-170/3541, deposit). create-crosscheck.md (verdict GO)
lists the guardrails to carry when relaxing this: sufficient-fuel hypothesis (kills
the `∅`-wipe), EIP-2681 nonce-overflow + EIP-3860 init-size preconditions, and
sourcing `checkpoint.substate` from the warmed `A*`. Keep the empty-init first cut for
the initial landing; relaxing it is a separate follow-on with its own precondition
surface.
