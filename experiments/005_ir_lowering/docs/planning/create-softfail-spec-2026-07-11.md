# CREATE2 soft-fail recorder alignment — implementation spec (2026-07-11)

**Branch:** `exp005-r11-create-softfail` (base `c46f9b91`). Default cone stays
sorry-free/green; WIP cone may carry the tracked create sorries until this lands.

**Goal.** Close `create_dispatch_of_coupled` (Machinery.lean:4431, tracked `sorry`)
by option 3 (lead-approved): make the recorder log **every** top-level CREATE2
outcome — a descending create records its child result (as today), a soft-failing
top-level CREATE2 records a soft-fail entry (world-unchanged, addr 0). Then
`log.creates` aligns 1:1 with CREATE2 cursors, and `create_dispatch` becomes a
DERIVED case-split on the recorded head, adding **no** hypothesis and **no**
IR-semantics change.

---

## 0. Ground truth established by reading the code

### 0.1 The soft-fail is a `.next` step, decided in `createArm` (System.lean:73–122)

`createArm` (exp003 `EVMLean/Evm/Semantics/System.lean:73`) steps a CREATE/CREATE2:

- **soft-fail (nonce)**: if `selfAccount.nonce.toNat ≥ 2^64-1` →
  `return .next (← resumeAfterCreate failed pending).exec` (line 99–100).
- **descend**: else if `value ≤ selfBalance ∧ depth < 1024 ∧ initCode.size ≤ 49152`
  → `return .needsCreate cp pending` (line 101–121).
- **soft-fail (funds/depth/size)**: else →
  `return .next (← resumeAfterCreate failed pending).exec` (line 122).

where `failed : CreateResult` (line 91–98) is

```
{ address := default, createdAccounts := exec.createdAccounts,
  accounts := exec.accounts,                       -- PRE-OP accounts (no nonce bump)
  gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat),
  substate := exec.toState.substate, success := false, output := .empty }
```

and `pending : PendingCreate` (line 83–90) carries `callerAccounts := accounts`,
`value`, `initOffset/initSize/initCodeSize`, `frame := { fr with exec := exec }`.

**Key consequence (Gotcha #1 answer — nonce bump):** the descend branch uses
`accountsWithBump` (the creator's nonce +1). The **soft-fail** branch uses `failed`
whose `accounts := exec.accounts` — the **PRE-op accounts, NOT bumped**. So a
soft-fail leaves the accounts (and therefore storage through the self lens)
UNCHANGED. Verified independently by `createArm_next_accMono`
(`BytecodeLayer/Hoare/StepWalk.lean:746`): `exec'.executionEnv = exec.executionEnv` and presence
is preserved; and `createArm_next_pc` (`:809`): `exec'.pc = exec.pc + 1`. The
`resumeAfterCreate failed pending` writes `accounts := result.accounts = exec.accounts`
and pushes `pushedValue = 0` (because `failed.success = false`, `Create.lean:195–198`).

### 0.2 The recorder only sees DESCENDING creates today

`driveLog` (`Spec/Recorder.lean:51`) records a create **only** on the `.inr` delivery
of a `.create pending` popped off the pending stack, at `rest.isEmpty` (line 68). A
soft-fail is a `.next` step (line 76–84) — it **never pushes** `.create pending`, so it
records nothing. Hence a recorded create head today means "this cursor DESCENDED", and
`stepFrame createFr = .needsCreate` is genuinely FALSE for a soft-failing cursor whose
record came from a later cursor. That is the exact blocker documented at
Machinery.lean:4408–4429.

### 0.3 CALL has the same live depth soft-fail

`call_dispatch_of_coupled` (Machinery.lean:3319) pins the lowered CALL operand stack to
`gw :: cw :: 0 :: 0 :: 0 :: 0 :: 0` — the **value operand is 0** (`systemOp .CALL`,
System.lean:131, threads that 4th stack word as `value`). `callArm`'s only non-depth
soft-fail trigger is `value ≤ selfBalance ∧ depth < 1024` (System.lean:40); with
`value = 0` the funds guard `0 ≤ balance` is unconditional, so a lowered CALL never
soft-fails on funds. Its depth guard remains live, however: at `depth ≥ 1024` it takes the
clean `.next` branch. The CALL channel therefore mirrors this CREATE2 design with
`isCallOp`, `softFailCallRecord`, a top-level `.next` recorder gate, and a two-arm dispatch.

### 0.4 The IR side already absorbs a soft-fail head with NO change

`EvalStmt.create` (`Spec/Semantics.lean:71–81`) consumes one `(world', addrW)` create
stream head and installs it generically:

```
| create … : EvalStmt … T C ((world', addrW) :: D) (.create cs)
    (match cs.resultTmp with
       | some t => { st with world := world' }.setLocal t addrW
       | none   => { st with world := world' }) T C D
```

A soft-fail head `(currentWorld, 0)` is a perfectly ordinary instance
(`world' = currentWorld`, `addrW = 0`). **No `EvalStmt`/`RunFrom`/`CreateStream`
type change.**

---

## 1. `CreateRecord` — how to represent a soft-fail

### 1.1 Current definition (`Spec/Recorder.lean:15–17`)

```lean
structure CreateRecord where
  result : CreateResult
  pending : PendingCreate
```

### 1.2 Proposed change: **NONE to the structure**

We do **not** add an `Option` child result, a success flag, or a dedicated
constructor. A soft-fail is represented by a `CreateRecord` whose `result` is exactly
`createArm`'s `failed` value and whose `pending` is exactly `createArm`'s `pending` —
the same pair the `.next` branch feeds to `resumeAfterCreate`. This is minimal-ripple:

- `result.success = false` already flags "no deploy" (drives `addressWord = 0`);
- `result.accounts = exec.accounts` already encodes "world unchanged through self lens".

Consuming code (`createStreamOf`, `evmV2CreateEntry`, `realisedCreate_cons`,
`recorderCoupled_create*`, `simStmt_coupled_create`) is polymorphic in the record —
it never inspects `success` — so the ONLY thing that changes is **where** records are
appended (`driveLog`), not the record type. This keeps `realisedCreate_cons`
(`RecorderLemmas.lean:164`) and `StreamsAligned` (`Producer.lean:73`) unchanged by
construction.

**Rationale for not adding a flag.** The two arms of `create_dispatch` are
distinguished by `rec.result.success` (equivalently `createAddrOrZero = 0` vs `≠ 0`)
which is already derivable from the record; a dedicated constructor would force a
re-proof of every `List.map`/`cons` alignment lemma for no gain.

---

## 2. Where/how `driveLog` records a soft-failing top-level CREATE2

### 2.1 The detection pattern to mirror (`Spec/Recorder.lean:26–30, 77–84`)

`isGasOp`/`isSloadOp` decode the current op and the `.next` branch tests
`isGasOp current && stack.isEmpty` / `isSloadOp current && stack.isEmpty`
(top-level only — `stack.isEmpty` means the pending stack is `[]`, i.e. this is a
TOP-LEVEL cursor, exactly the recorder's alignment scope). Add the create twin:

```lean
def isCreate2Op (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
    == .System .CREATE2
```

(Placed next to `isSloadOp`, `Recorder.lean:31`. `.System .CREATE2` is the tag used
throughout Descent.lean, e.g. `:602`.)

### 2.2 The soft-fail record builder

A `.next` step gives us only `exec` (the post-step exec). We need the PRE-step
`current.exec` to build `failed`/`pending` (they read `current.exec.accounts`,
`current.exec.gasAvailable`, the operand stack, etc.). In the `.next` branch `current`
IS in scope. Add a builder that reconstructs exactly `createArm`'s `failed`/`pending`
from `current` and the decoded operands:

```lean
/-- The soft-fail CREATE2 record: `createArm`'s `.next`-branch `failed`/`pending`
    pair, rebuilt from the pre-step frame. `result.accounts = current.exec.accounts`
    (world unchanged through the self lens) and `result.success = false`
    (⇒ `addressWord = 0`), so `evmV2CreateEntry` maps it to `(currentWorld, 0)`. -/
def softFailCreateRecord (current : Frame) : CreateRecord :=
  let exec := current.exec
  let (stack, value, initOffset, initSize, _salt) :=
    -- exec.stack.pop4 image at a CREATE2 cursor; see §2.4 on extraction
    …
  { result :=
      { address := default
        createdAccounts := exec.createdAccounts
        accounts := exec.accounts
        gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
        substate := exec.toState.substate
        success := false
        output := .empty }
    pending :=
      { frame := current
        stack := stack
        callerAccounts := exec.accounts
        value := value
        initOffset := initOffset.toUInt64
        initSize := initSize.toUInt64
        initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size } }
```

### 2.3 The `driveLog` insertion (`Spec/Recorder.lean:76–84`)

Current `.next` branch:

```lean
| .next exec =>
  if isGasOp current && stack.isEmpty then
    driveLog fuel stack (.inl { current with exec := exec })
      (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) sloadAcc callAcc createAcc
  else if isSloadOp current && stack.isEmpty then
    driveLog fuel stack (.inl { current with exec := exec })
      gasAcc (sloadAcc ++ [sloadWarmthOf current]) callAcc createAcc
  else
    driveLog fuel stack (.inl { current with exec := exec }) gasAcc sloadAcc callAcc createAcc
```

Insert **one** new `else if`, before the final `else`:

```lean
  else if isCreate2Op current && stack.isEmpty then
    driveLog fuel stack (.inl { current with exec := exec })
      gasAcc sloadAcc callAcc (createAcc ++ [softFailCreateRecord current])
  else
    driveLog fuel stack (.inl { current with exec := exec }) gasAcc sloadAcc callAcc createAcc
```

**Why this is the whole recorder change.** A DESCENDING CREATE2 is a
`.needsCreate` step (line 90–91) — untouched. A SOFT-FAILING CREATE2 is the only
CREATE2 that reaches `.next`, and `stack.isEmpty` scopes it to top level. So the new
arm fires **iff** the cursor is a soft-failing top-level CREATE2, appending exactly
one soft-fail record — giving `log.creates` a head for every CREATE2 cursor.

### 2.4 Operand extraction detail (scaffolding note)

`softFailCreateRecord` needs the four operands `createArm` popped. Cleanest: extract
them from `current.exec.stack` via `pop4` in a `match`, mirroring `systemOp .CREATE2`
(System.lean:157). If the `pop4` shape is awkward inside `driveLog`'s definitional
context, an equivalent is to have the record builder take the ALREADY-decoded
`.needsCreate`-free operands — but since `driveLog` does not decode operands elsewhere,
the self-contained `pop4` inside `softFailCreateRecord` is preferred. The exact
`.next` witness (`stepFrame current = .next exec` at a CREATE2 decode) is what the
downstream `create_dispatch` split will invert via `createArm_next_pc/_accMono`
(StepWalk.lean:809/746) and a new `createArm_next_pushes_zero`/`_result_eq` inversion
(§4). The builder's `failed`/`pending` are DEFINITIONALLY `createArm`'s, so those
inversions are `rfl`/`simp` peels of the same term.

**`driveLog_drive` (RecorderLemmas.lean:89–123) stays green.** Its `.next` case
(line 110–114) does `split <;> [skip; split] <;> exact ih …`; adding one `else if`
adds one more split arm that ALSO only touches `createAcc`, so the same
`exact ih stack (.inl { current with exec := exec }) _ _ _ _` closes it (accumulators
erased). Update the tactic to `split <;> [skip; split <;> [skip; split]] <;> exact ih …`
(or simply `<;> split <;> … <;> exact ih …` chained to cover the extra branch).

---

## 3. `createStreamOf` / `evmV2CreateEntry` mapping (soft-fail → `(currentWorld, 0)`)

### 3.1 Mapping is already correct — NO change to these defs

`createStreamOf` (`Recorder.lean:113`) maps each record through
`evmV2CreateEntry rec.result rec.pending self` (`Spec/Recorder.lean`):

```lean
evmV2CreateEntry result pd self =
  ( fun key => evmCreateOracle.postStorage result pd self key
  , evmCreateOracle.addressWord result pd )
```

For a soft-fail record (`result = failed`, `result.success = false`,
`result.accounts = current.exec.accounts`):

- **world component** =
  `fun key => result.accounts.find? self |>.option 0 (·.lookupStorage key)`
  (`evmCreateOracle.postStorage`, `Frame/Create.lean:100`). With
  `result.accounts = current.exec.accounts` this is exactly the CREATE2-cursor frame's
  storage through the self lens = **currentWorld**. ✓
- **address component** = `evmCreateOracle.addressWord = createAddrOrZero result pd`
  (`Frame/Create.lean:102, 75–80`). Since `result.success = false`, the guard
  `result.success = false ∨ …` is true, so it returns **0**. ✓

So `evmV2CreateEntry failed pending self = (currentWorld, 0)` by `rfl`/`simp` —
matching `EvalStmt.create`'s expected head shape with `world' = currentWorld`,
`addrW = 0`. **No `EvalStmt.create` tweak, no `CreateStream` tweak.** (Gotcha #3, #6.)

### 3.2 `StreamsAligned` (Producer.lean:73) stays a `rfl`-level def

`D = createStreamOf dS self` continues to hold: `dS` now includes soft-fail records,
and `D`'s corresponding heads are their `evmV2CreateEntry` images. The producer's
per-cursor consumption (§5.5) consumes exactly one head per CREATE2 cursor.

---

## 4. Two-arm shape of `create_dispatch_of_coupled`, both stepFrames DERIVED

### 4.1 New statement (relaxed conclusion — a disjunction of two arms)

The current conclusion asserts unconditionally `stepFrame createFr = .needsCreate …`.
That is false on the soft-fail path. Replace the single existential with a
**case-split whose branch is DERIVED from the recorded head `rec`**, NOT assumed:

```lean
theorem create_dispatch_of_coupled … (same hyps) :
    -- Arm D (descend): the recorded head is a real child (addr ≠ 0 ⇔ success)
    (∃ cp pending,
        stepFrame createFr = .needsCreate cp pending
      ∧ pending.frame.exec.executionEnv = createFr.exec.executionEnv
      ∧ pending.frame.validJumps = createFr.validJumps
      ∧ pending.frame.exec.pc = createFr.exec.pc
      ∧ pending.frame.exec.toMachineState.memory = createFr.exec.toMachineState.memory
      ∧ rec.result.success = true)
    ∨
    -- Arm S (soft-fail): the recorded head is the soft-fail record; step is `.next`
    (∃ exec',
        stepFrame createFr = .next exec'
      ∧ rec = softFailCreateRecord createFr
      ∧ exec'.executionEnv = createFr.exec.executionEnv
      ∧ exec'.pc = createFr.exec.pc + 1
      ∧ exec'.toMachineState.memory = createFr.exec.toMachineState.memory
      ∧ createAddrOrZero rec.result rec.pending = 0)
```

(Exact conjuncts trimmed to what `createRealises`/`create_head` consume — see §5.)

### 4.2 How each arm's stepFrame is DERIVED from `RecorderCoupled.restart`

`hcp : RecorderCoupled log createFr gS sS cS (rec :: dS')` unfolds to a restart
equation `driveLog fuel' [] (.inl createFr) [] [] [] [] = .ok (…, rec :: dS')`
(the `⟨fuel', hrestart⟩` witness, as in `recorderCoupled_create`, Machinery.lean:1974).
Peel the FIRST step of that restart by `cases hstep : stepFrame createFr`:

- `stepFrame createFr = .needsCreate cp pending` (**DESCEND**): the restart's next
  configuration pushes `.create pending` and the first delivered create record is the
  child's — `recorderCoupled_create_extract` (Machinery.lean:2038) already turns this
  into `rec = { result := childRes.toCreateResult, pending := pending }` with
  `childRes.toCreateResult.success = …`. Descend arm; the pins come from
  `stepFrame_needsCreate_site_inv` (Descent.lean:599) exactly as CALL. The depth guard
  is already derived in-place (`driveLog_creates_const_of_depth`, Machinery.lean:4451–4456).

- `stepFrame createFr = .next exec'` (**SOFT-FAIL**): because `createFr` decodes
  `CREATE2` (hyp `hdec`), the ONLY `.next` producer at this cursor is `createArm`'s
  soft-fail arm (`stepFrame_systemOp` + `createArm_next_*`; a CREATE2 that isn't
  soft-fail is `.needsCreate`, contradiction). With `stack = []` (top level, from the
  restart being at the outer `driveLog []`), the recorder's NEW `.next` arm (§2.3)
  fires `isCreate2Op createFr && [].isEmpty = true`, appending
  `softFailCreateRecord createFr` — so the restart's next create accumulator is
  `[softFailCreateRecord createFr] ++ (tail)`; matching against `rec :: dS'` gives
  `rec = softFailCreateRecord createFr` (peel via `driveLog_acc_hom`, the same
  accumulator homomorphism used in `recorderCoupled_create`, Machinery.lean:2010).
  Then `createAddrOrZero rec.result rec.pending = 0` by §3.1, and
  `exec'.pc = createFr.exec.pc + 1`, `exec'.executionEnv = createFr.exec.executionEnv`,
  `exec'.accounts = createFr.exec.accounts` from `createArm_next_pc`/`_accMono`
  (StepWalk.lean:809/746) + `stepFrame`→`createArm` reduction.

- `stepFrame createFr = .halted _`: excluded by `hch : CleanHaltsNonException` (the
  exception arm) — a CREATE2 decode never clean-`.halted`s at this cursor (it dispatches
  to `createArm`, which returns `.next`/`.needsCreate`, never `.halted` except on the
  charge/pop faults which `hch` rules out, exactly as the CALL twin's clean-halt gate).

- `stepFrame createFr = .needsCall _ _`: impossible — CREATE2 decodes to `systemOp
  .CREATE2` (`stepFrame_systemOp` / decode `hdec`), which cannot be `.needsCall`.

**No new hypothesis.** The arm is selected by the recorded head, which is fixed by the
coupling. The `CreateResolves` seam (§5) is used only in the descend arm's resume, as
today; the soft-fail arm needs no resolve.

---

## 5. Every lemma whose statement/proof must change

### 5.1 `recorderCoupled_create` (Machinery.lean:1967) — UNCHANGED

Statement and proof are correct as-is: they consume a DESCENDING head via
`CreateReturns` (`hcr`), which is exactly the descend arm. The soft-fail head is never
a `CreateReturns` (no child descends), so this lemma is only used on the descend arm.
**No change.**

### 5.2 `recorderCoupled_create_extract` (Machinery.lean:2038) — UNCHANGED

It is GUARDED by `hstep : stepFrame createFr = .needsCreate cp pending` (its own
hypothesis) — i.e. it is the descend-arm extractor. Correct as-is. `create_dispatch`'s
descend arm calls it after establishing `.needsCreate`. **No change.** (A NEW twin
`recorderCoupled_create_softfail_extract` is added — see §5.7.)

### 5.3 `create_args_run_of_coupled` (Machinery.lean:4019) — UNCHANGED

Builds the four-operand push run `fr0 ⟶ createFr` reaching the CREATE2 cursor with
`stack = valueW :: initOffW :: initSizeW :: saltW :: []`. This is identical for descend
and soft-fail (it stops one byte BEFORE the CREATE2). It threads `RecorderCoupled`
unchanged. **No change.**

### 5.4 `create_tail_of_cleanHalt` (Machinery.lean:4239) — UNCHANGED

The Route-B tail (`PUSH32 slot; MSTORE` or `POP`) at the resume frame
`resumeFr.exec.stack = addrW :: []`. On the soft-fail arm the resumed frame is
`exec'` with `stack = 0 :: []` (createArm pushes 0), pc `+1`, memory/world unchanged —
the SAME shape the tail consumes (`addrW := 0`). The tail lemma is polymorphic in the
pushed word, so it applies verbatim to `addrW = 0`. **No statement change**; may need
the soft-fail resume-frame pins (pc, stack, memory) fed from `createArm_next_*`
instead of `resumeAfterCreate_*` — but those pins are provided by the dispatch arm, not
the tail.

### 5.5 `create_dispatch_of_coupled` (Machinery.lean:4431) — REWRITTEN (§4)

Statement becomes the two-arm disjunction (§4.1); proof case-splits on
`stepFrame createFr` and derives each arm's stepFrame from the coupling (§4.2).
The tracked `sorry` (line 4460) is replaced by the two derived arms. This is the ONLY
lemma whose CONCLUSION changes shape.

### 5.6 `createRealises_of_recorded` (Machinery.lean:4475) — proof rewritten, statement UNCHANGED

Statement (its `CreateRealisesS` conclusion and the branch on `cs.resultTmp` folding in
`createAddrOrZero rec.result rec.pending` / `evmCreateOracle.postStorage rec.result …`)
is ALREADY soft-fail-correct: on soft-fail, `createAddrOrZero rec.result rec.pending = 0`
and `postStorage rec.result … = currentWorld`, which is what the IR state fold produces.
The PROOF now case-splits on the new `create_dispatch` disjunction:

- **descend arm**: assemble as today — `create_args_run` → `.needsCreate` dispatch →
  `CreateResolves` seam (`hcr`) → `recorderCoupled_create_extract` → resume pins
  (`resumeAfterCreate_stack/_memory/_activeWords_ge`, Descent.lean:819+) →
  `create_tail_of_cleanHalt`.
- **soft-fail arm**: assemble the same skeleton but with the resume edge being a plain
  `Runs.step` (`.next exec'`) instead of `Runs.create`; the tail runs at `exec'`
  (`stack = 0 :: []`); NO `CreateResolves` needed. `recorderCoupled_create_softfail`
  (§5.7) advances the coupling past the soft-fail head.

The `sorry` (line 4512) is discharged by the two-arm assembly.

### 5.7 NEW lemmas (the soft-fail twins) — ADDED

Two small twins are needed, mirroring the descend versions:

- `recorderCoupled_create_softfail`
  (`RecorderCoupled log createFr gS sS cS (rec :: dS')` +
   `stepFrame createFr = .next exec'` +
   `rec = softFailCreateRecord createFr`) `→`
  `RecorderCoupled log { createFr with exec := exec' } gS sS cS dS'`.
  Proof: peel the restart's `.next` step (recorder appends the soft-fail head at the
  `isCreate2Op && isEmpty` arm), then the `driveLog_acc_hom` accumulator peel — a
  transcription of `recorderCoupled_create` (Machinery.lean:1967) with the child
  black-box replaced by the single `.next` step (SIMPLER: no `driveLog_frame_nonempty`
  child framing).

- `recorderCoupled_create_softfail_extract`
  (`RecorderCoupled log createFr gS sS cS (rec :: dS')` +
   `stepFrame createFr = .next exec'`) `→`
  `rec = softFailCreateRecord createFr ∧
   RecorderCoupled log { createFr with exec := exec' } gS sS cS dS'`.
  Proof: from the restart peel, the first delivered create record on a `.next` CREATE2
  cursor IS `softFailCreateRecord createFr` (recorder's new arm), then apply
  `recorderCoupled_create_softfail`.

Place both directly after `recorderCoupled_create_extract` (Machinery.lean:2054).

### 5.8 `create_head_realises_coupled` (Machinery.lean:4523) — proof rewritten, statement adjusted

Its conclusion bundles `CreateReturns createFr resumeFr` + `resumeAfterCreate rec.result
rec.pending = .ok resumeFr` + the resume-frame pins. On the soft-fail arm there is NO
`CreateReturns` and NO `resumeAfterCreate` (the resume is `createArm`'s inline `.next`).
So the conclusion must be relaxed to a **disjunction** OR — preferably — re-keyed onto a
neutral "post-create resume frame" bundle that both arms satisfy:

```
∃ resumeFr createFr,
    Runs fr0 createFr ∧ (pc/mem/aw pins on createFr) ∧
    Runs createFr resumeFr ∧                       -- `.create` edge OR `.next` step
    RecorderCoupled log resumeFr gS sS cS dS' ∧
    resumeFr.exec.stack = createAddrOrZero rec.result rec.pending :: [] ∧
    (address/code/canModify/pc+1/mem/aw/validJumps pins on resumeFr)
```

i.e. drop the `CreateReturns`/`resumeAfterCreate` conjuncts (which are descend-only)
and keep the OBSERVABLE resume-frame facts (`Runs createFr resumeFr`, stack head
`= createAddrOrZero … = addr-or-0`, pc `= createFr.pc + 1`, world unchanged relative to
`createFr` — true on BOTH arms). The `simStmt_coupled_create` consumer (§5.9) only needs
the observable resume-frame + advanced coupling to re-establish `Corr`; it does not need
the `CreateReturns` witness. This makes ONE bundle serve both arms.

Proof: case-split on `create_dispatch`; descend arm builds `Runs createFr resumeFr` via
`Runs.create` + resume pins (as today), soft-fail arm via `Runs.step` (`.next exec'`) +
`createArm_next_*` pins. The `sorry` (line 4569) is discharged.

### 5.9 `simStmt_coupled_create` (Producer.lean:1544) — proof only (statement UNCHANGED)

Currently `sorry` (statement-only, line 1576). It consumes
`create_head_realises_coupled` (now two-arm-uniform per §5.8) plus a `sim_create_stmt'`
tail carrier, then re-establishes `Corr` + `StreamsAligned` at the post-create cursor.
Because `create_head_realises_coupled`'s new bundle is arm-uniform, this proof is a
line-for-line transcription of `simStmt_coupled_call` as its docstring already promises;
the soft-fail case needs no special handling here (the resume-frame bundle is neutral).

---

## 6. Gotchas — answered

1. **Does a soft-fail change world (nonce bump)?** NO. The descend branch bumps the
   creator nonce (`accountsWithBump`), but the soft-fail `.next` uses `failed` with
   `accounts := exec.accounts` (pre-op). Verified by `createArm_next_accMono`
   (StepWalk.lean:746: `exec'.executionEnv = exec.executionEnv`, presence preserved) and
   the `resumeAfterCreate failed` write `accounts := result.accounts = exec.accounts`.
   So the recorded soft-fail world = currentWorld through the self lens, and
   `evmCreateOracle.postStorage failed … self = currentWorld` by `rfl`. (Gas DOES change
   — `gasAvailable` recomputes — but v2 has no gas in the observable state, so it is
   invisible to the IR. Confirmed: `Frame/Create.lean:63` "gas-restored field is
   dropped".)

2. **`createSuffix` consumption in `RunFrom`/`StreamsAligned`.** No adjustment needed.
   `StreamsAligned` (`D = createStreamOf dS self`) is definitional and now spans the
   soft-fail records too; `EvalStmt.create` consumes exactly one head per CREATE2 cursor
   whether descend or soft-fail (§0.4, §3.2). The 1:1 alignment is the POINT of the fix:
   every CREATE2 cursor consumes exactly one `dS` head.

3. **`EvalStmt.create`/`CreateStream` tweak?** NONE (§0.4, §3.1). The soft-fail head is
   an ordinary `(currentWorld, 0)` instance.

4. **CALL side.** Lowered CALL forces `value = 0`, eliminating funds soft-failure but not
   the live depth soft-failure. The CALL recorder now has the field-for-field twin of this
   CREATE2 design so every CALL cursor consumes exactly one call-channel head.

5. **`driveLog_drive` adequacy** (RecorderLemmas.lean:89). Stays green: the CREATE2 and
   CALL `.next` sub-branches only touch their respective accumulators and close by the
   same `ih` after splitting the recorder gates (§2.3).

6. **`realisedCreate_cons` / `createStreamOf` / `evmV2CreateEntry`** (Recorder.lean,
   Recorder.lean). UNCHANGED — polymorphic in the record; the soft-fail record maps to
   `(currentWorld, 0)` by `rfl`/`simp` (§3.1).

---

## 7. Trivial scaffolding edits made in this design pass

None beyond this document. The changes above are DESIGN; implementation (the `isCreate2Op`
+ `softFailCreateRecord` defs, the `driveLog` `.next` insertion, the `create_dispatch`
rewrite, the two new `recorderCoupled_create_softfail*` twins, and the
`createRealises`/`create_head`/`simStmt_coupled_create` proof rewrites) is the next stage.

## 8. Execution order (for the implementer)

1. `Spec/Recorder.lean`: add `isCreate2Op`, `softFailCreateRecord`, the `.next`
   insertion in `driveLog`. Rebuild DEFAULT cone; fix `driveLog_drive`
   (RecorderLemmas.lean) `.next` tactic. **Green gate.**
2. Machinery.lean: add `recorderCoupled_create_softfail` +
   `recorderCoupled_create_softfail_extract` (after :2054). **WIP gate.**
3. Machinery.lean: rewrite `create_dispatch_of_coupled` (:4431) to the two-arm
   disjunction, both arms derived. **WIP gate.**
4. Machinery.lean: discharge `createRealises_of_recorded` (:4475) and adjust +
   discharge `create_head_realises_coupled` (:4523) to the arm-uniform bundle.
5. Producer.lean: transcribe `simStmt_coupled_create` (:1544) from
   `simStmt_coupled_call`.
6. Confirm DEFAULT cone sorry-free/green; only pre-existing unrelated stubs (if any)
   remain in WIP.
