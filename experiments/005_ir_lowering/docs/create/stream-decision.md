# CREATE stream fork (R2) — decision

Date: 2026-07-04. Read-only, code-verified. Settles design fork R2 of
`docs/eval-2026-07-04/create-implementation-plan.md` §5: how CREATE results thread
through the v2 semantics stream. All line refs are into
`experiments/005_ir_lowering/LirLean/` unless prefixed.

---

## VERDICT: **Option A — a second, parallel `CreateStream`.**

`abbrev CreateStream := List (World × Word)` — a **fourth threaded channel**
alongside the gas `Trace` and the `CallStream`, consumed head-first by
`EvalStmt.create`, with the existing `CallStream` (`Spec/Semantics.lean:99`) and the
entire `realisedCall`/`callStreamOf`/`realisedCall_cons`/`RecorderCoupled.callSuffix`
machinery left **byte-identical**.

**One-paragraph why.** Option A is *not* unsound — the plan's R2 "positionally
wrong for CALL;CREATE;CALL" worry is a misdiagnosis (proof below): ordering lives in
the sequential statement walk (`RunStmts`/`RunFrom` thread each stream left-to-right
and each `Stmt` pops only its own kind's head), **not** in the stream, and the world
is threaded through `IRState` independently of which channel is popped — so two
parallel per-kind channels, each in per-kind program order, reconstruct any
interleaving correctly. With the correctness argument for B gone, B's only remaining
property is its cost: the merged/tagged stream **rewrites the exact fragile R3/R7
region that surrounds the open flagship sorries** (`realisedCall_cons`'s
`rfl`-cleanliness, `RecorderCoupled.callSuffix`, R7e "consumes exactly one
`CallRecord`"), whereas A adds a parallel channel that threads *inertly* through
every existing call/gas/sload proof and leaves that region untouched. Per the lead's
own decisive criterion — "if B risks destabilizing the open leaves, that is a strong
reason to prefer A for the first CREATE landing and defer B" — A is the landing, B is
a deferred, optional cosmetic refactor.

---

## 1. Is option A actually unsound? NO. Ordering lives in the statement walk.

The claim to test (plan R2): two parallel streams are "positionally wrong if a
program does CALL; CREATE; CALL — each stream would need to know the absolute
position." This is **false**. Here is the actual semantics.

**The stream is a threaded value, consumed by the statement *sequence*.**
`EvalStmt` has the shape (Semantics.lean:164-165)

```
EvalStmt prog : IRState → Trace → CallStream → Stmt → IRState → Trace → CallStream → Prop
```

`CallStream` is both an **input** and an **output** index. `EvalStmt.call`
(Semantics.lean:187-195) is the *only* rule that pops it:

```
| call … (hcallee …) (hgas …) :
    EvalStmt prog st T ((world', success) :: C) (.call cs)
      (match cs.resultTmp with
        | some t => { st with world := world' }.setLocal t success
        | none   => { st with world := world' })
      T C
```

The head `(world', success)` is applied as `world := world'` (into `IRState`) and
`success` is bound at `resultTmp`. Every non-call rule threads `C` **unchanged**
(`assignPure`/`assignGas`/`sstore` all output the same `C` they received).

`RunStmts.cons` (Semantics.lean:201-204) threads `C → C' → C''` across the statement
list; `RunFrom` (Semantics.lean:228-269) threads `C → C'` through the block's
`RunStmts` and then `C'` into the terminator's `RunFrom` recursion
(`jump`/`branchThen`/`branchElse`, e.g. :251, :260, :268). So **`C` is consumed
strictly left-to-right in the program's execution order of statements/terminators.**
Ordering is 100% in the sequential statement processing; the stream carries no
positional index.

**Consequence for A (worked example CALL; CREATE; CALL).** Under A the run threads
`CallStream = [c1, c2]` and `CreateStream = [cr1]`. Each element is an *absolute*
post-descent snapshot `(world', word)` (the full storage lens at that descent, not a
delta — cf. `evmV2CallEntry`, `CallRealises.lean:59, postStorage`). The walk:

| step   | rule fires        | pops from      | world becomes | binds        |
|--------|-------------------|----------------|---------------|--------------|
| CALL   | `EvalStmt.call`   | `CallStream`   | `w(c1)`       | success c1   |
| CREATE | `EvalStmt.create` | `CreateStream` | `w(cr1)`      | addr cr1     |
| CALL   | `EvalStmt.call`   | `CallStream`   | `w(c2)`       | success c2   |

The interleaving is reconstructed by the statement walk. Each channel is popped in
its own kind's program order (`c1` before `c2`; `cr1` alone). The final world is
`w(c2)` — the last descent's snapshot — because the walk applies snapshots in
program = execution = chronological order. Any SLOAD *between* two descents reads the
threaded `IRState.world`, which is the most-recently-applied snapshot regardless of
which channel supplied it. **A and B produce identical world-threading behavior**;
the only difference is bookkeeping (two lists vs. one). Branches and loops are fine
by the same argument: the recorder records the *taken path's* descents in execution
order into each kind's channel, and `RunFrom` follows the same branch (cond-driven)
and pops the same per-kind heads.

**Where the old function-oracle flaw actually was, and why it does not apply.** The
retired `CallOracle` (1c77c07) was fatal because it returned the same result for the
same IR-visible inputs — an *intra-kind* collision (two CALLs with equal inputs).
Parallel streams are positional *intra-kind* (each CALL pops a distinct head). The
*cross-kind* order (CALL vs CREATE) never needed encoding in the stream — it is the
static program structure the walk traverses. A carries exactly the positionality
that matters and no more.

**Verdict on Q1: option A is sound.** No single-descent restriction, no absolute
position needed. The correctness rationale the plan gave for B evaporates.

---

## 2. Recommendation, exact type, signature changes, blast radius, and the sorries.

### 2.1 Chosen type

```
/-- Spec/Semantics.lean, twin of `CallStream` (:99). The `Word` slot carries the
    deployed-address-or-0 the CREATE pushes (`createAddrOrZero`, Create.lean:75),
    exactly as `CallStream`'s carries the 0/1 success flag. -/
abbrev CreateStream := List (World × Word)
```

Identical element type to `CallStream`; a **separate** channel.

### 2.2 Signature changes (Step 2 core)

Add `CreateStream` as one more threaded index to the three v2 relations and their
top-level driver, threaded exactly like `CallStream`:

- `EvalStmt` : `IRState → Trace → CallStream → CreateStream → Stmt → IRState → Trace → CallStream → CreateStream → Prop`
- `RunStmts` : same 4-channel widening; `.cons` threads `D → D' → D''`.
- `RunFrom`  : `IRState → Trace → CallStream → CreateStream → Label → Observable → Prop`.
- `IRRun`    : gains a `(D : CreateStream)` parameter.

Every **existing** constructor gains `{D … : CreateStream}` and threads `D`
**unchanged** (inert), exactly as they already thread `T` past a `.call` or `C` past
an `assignGas`. Only the new `EvalStmt.create` (2.4 / §3) consumes `D`.

The flagship conclusions (RS:216-217, 263-264, 300-301, 353-354) gain a 4th stream
argument `(realisedCreate log params.recipient)` next to `(realisedCall log
params.recipient)`. `realisedCreate`/`createStreamOf` are the Step-6 recorder twins
of `realisedCall`/`callStreamOf` (`Spec/Recorder.lean:288, 296`); until Step 6 lands
the flagship statements may carry an abstract `D` or `[]` in that slot (the flagship
is WIP/sorry, so its *statements* may be threaded ahead of the recorder).

### 2.3 Blast radius (mechanical, inert-threading)

Adding an index to the `RunFrom`/`RunStmts`/`EvalStmt` inductives ripples to their
refs (plan's counts: ~137 `RunFrom`, ~74 `EvalStmt`, ~72 `RunStmts`), **plus** the
flagship's mirror inductives that re-declare the same channels:

- `Realisability/Surface.lean` — `RunFromV` / `RunFromLeft` / `RunFromAll`
  (:872, :918) and the `SimStmtStep`/tie surface (:150-178, :872-940) each gain the
  `CreateStream` index.
- `Realisability/Witness.lean` (:268, :290), `Realisability/Machinery.lean`
  `SimStmtStep` (:91) — gain the index.
- `driveLog`'s result tuple widens by **appending** `× List CreateRecord`
  (`Spec/Recorder.lean:184`; the tuple also appears at Machinery :1494, :1530, :1617,
  :1806, :1896). Appended-at-end and threaded inertly through the existing call arms.
- `RecorderCoupled` (Surface.lean:508) gains a parallel `createSuffix : List
  CreateRecord` + `createPrefix` field (twin of `callSuffix`/`callPrefix` :517-518).

**Every one of these is an ADDITION that threads inertly through existing
call/gas/sload proofs.** None changes the meaning or `rfl`-cleanliness of any
existing declaration.

### 2.4 Does A disturb the 11 open flagship sorries? **No — 3 statements move
mechanically, 0 proofs are burdened.**

The 11 tracked sorries (verified `:= sorry` terms):

| # | location | mentions | A's effect |
|---|----------|----------|------------|
| 1 | RS:134 `StmtTies'` | — (sload chg) | none |
| 2 | RS:246 `RunFrom` existential | `realisedCall` (RunFrom arg) | +4th arg in the *stated goal*; `sorry` still closes |
| 3 | RS:280 `RunFromAll` existential | `realisedCall` | same |
| 4 | RS:317 `RunFrom` (gasfree) | `realisedCall` | same |
| 5 | RS:328 `realisedGas = []` | — | none |
| 6 | RS:343 `PrecompileAssumptions` | — | none |
| 7 | Machinery:365 `fr0` | frame geometry | none |
| 8–11 | Machinery:1323/1331/1360/1363 | `validJumps`/`nextInstrPosNat`/bytes | none (pure engine geometry) |

Sorries 2–4 are `obtain … := sorry` whose *stated existential* gains the 4th stream
argument; since `sorry` discharges any goal, no new proof burden lands. Critically, A
does **not** change `realisedCall`, `callStreamOf`, or `realisedCall_cons`
(`RecorderLemmas.lean:44-48`, closed by `simp … List.map_cons` — `rfl`-clean), so
the **real** (non-sorry) R3/R7 machinery that surrounds these sorries —
`RecorderCoupled.callSuffix` destructured `rec :: cS'` and its head identified with
the cursor's `evmV2CallEntry` (Machinery:306-347, 1729-1914; R7e :1729) — is
**preserved verbatim**.

### 2.5 Why B *would* disturb the open leaves (the reason to defer it)

Option B (`List (World × Word × DescentKind)` replacing `CallStream`) forces:

- `log.calls : List CallRecord` → a merged `List DescentRecord`; `driveLog`'s
  accumulator/tuple element type changes (not appended — *changed*).
- `realisedCall := callStreamOf log.calls self` → a *filter/projection* of the merged
  list. `realisedCall_cons`'s `rfl`-cleanliness (RecorderLemmas:44-48) **breaks** —
  the head is no longer definitionally the first record; it requires a
  "head-is-a-`.call`" argument.
- `RecorderCoupled.callSuffix` (Surface.lean:508) → a descent suffix with a
  **new kind-matching well-formedness obligation** (the head's `DescentKind` must
  equal the statement's kind, or the run gets stuck — an invariant A never needs).
- R7e "a returning external CALL consumes exactly one `CallRecord`"
  (Machinery:1729-1836) must be re-derived over the merged suffix.

This is precisely the R3 call-cursor region that gates the open R11 blocker sorry
(RS:246 and the `runFrom_of_driveCorrLog` route it names, RS:223-236). Reshaping it
concurrently with the *first* CREATE landing is the destabilization the lead flagged.
(Untagged-merge — "B-lite", one `List (World × Word)` shared by both `.call` and
`.create` — avoids the semantics-side index but has the **same** recorder/realised
disturbance: it still merges `log.calls` and rewrites `realisedCall_cons`. It is not
a way out of B's cost.)

**Net:** A trades a larger *mechanical, inert* blast radius for zero disturbance of
the fragile open-leaf proofs. That is the right trade for the first landing. B (the
tagged merge) remains available as a later cosmetic unification *after* R3/R7 close,
if ever desired — it is not required for soundness.

---

## 3. Concrete Lean shape the Build phase must implement for Step 2

Depends on Step 1's `CreateSpec` (plan §2 Step 1: fields `value initOffset initSize
salt : Tmp`, `resultTmp : Option Tmp`) and `Stmt.create (cs : CreateSpec)`.

### 3a. The channel (Semantics.lean, next to `CallStream` :99)

```lean
/-- The supplied external-CREATE result stream — twin of `CallStream` (:99). Each
entry is the post-create `World` paired with the deployed-address-or-0 word CREATE
pushes (`createAddrOrZero`, Create.lean:75). Positional, consumed head-first by
`EvalStmt.create`; independent of the gas `Trace` and the `CallStream`. -/
abbrev CreateStream := List (World × Word)
```

### 3b. The four relations gain the `CreateStream` index

```lean
inductive EvalStmt (prog : Program) :
    IRState → Trace → CallStream → CreateStream → Stmt →
    IRState → Trace → CallStream → CreateStream → Prop where
  -- existing arms: add `{D : CreateStream}`, thread `D` unchanged, e.g.
  | assignPure … : EvalStmt prog st T C D (.assign t e) (st.setLocal t w) T C D
  | assignGas  … : EvalStmt prog st (obs :: T) C D (.assign t .gas) … T C D
  | sstore     … : EvalStmt prog st T C D (.sstore key value) … T C D
  | call       … : EvalStmt prog st T ((world', success) :: C) D (.call cs) … T C D
  -- NEW arm (§3c)
  | create     … : EvalStmt prog st T C ((world', addrW) :: D) (.create cs) … T C D
```

`RunStmts` / `RunFrom` / `IRRun`: mirror the `CallStream` threading for `D`
(`.cons` : `D → D' → D''`; `RunFrom.jump`/`branch*`/`ret`/`stop` thread `D → D'`
through the block's `RunStmts` then into the terminator recursion).

### 3c. The new arm — `EvalStmt.create` (twin of `.call` :187-195)

```lean
/-- `create cs`: read the create inputs from `locals` (an undefined tmp ⇒ the rule
does not fire, mirroring `.call`), **pop the head `(world', addrW)` of the CREATE
stream**, set `world := world'`, and bind the deployed address `addrW` at
`cs.resultTmp` if present. The gas `Trace` and the `CallStream` are unchanged.
Positional: the head IS this create's recorded result. The guards read every
CREATE2 operand from locals. -/
| create {st : IRState} {T : Trace} {C : CallStream} {D : CreateStream}
    {cs : CreateSpec} {valueW initOffW initSizeW saltW addrW : Word} {world' : World}
    (hvalue : st.locals cs.value = some valueW)
    (hoff   : st.locals cs.initOffset = some initOffW)
    (hsize  : st.locals cs.initSize = some initSizeW)
    (hsalt  : st.locals cs.salt = some saltW) :
    EvalStmt prog st T C ((world', addrW) :: D) (.create cs)
      (match cs.resultTmp with
        | some t => { st with world := world' }.setLocal t addrW
        | none   => { st with world := world' })
      T C D
```

Notes for the builder:
- Structurally identical to `EvalStmt.call` — pop `((world', w) :: D)`, `world :=
  world'`, bind `w` at `resultTmp` — differing only in *which* channel is popped and
  *which* locals are read as guards. This structural identity is what keeps every
  existing arm's `D`-threading inert.
- `salt : Tmp` is read by the CREATE2-only contract and must be bound before the
  statement fires.
- `RunStmts`/`RunFrom` need **no new constructor** (they recurse on `Stmt`
  generically); they only need the `D` index added and threaded.

### 3d. Downstream stubs this Step-2 shape commits the later steps to (not Step 2
itself, but named so the index lines up):

- `Spec/Recorder.lean`: `CreateRecord` (twin of `CallRecord` :85), `driveLog`'s
  `createAcc : List CreateRecord` (appended to the tuple), `recordCreate` (the
  `.create pd` arm currently dropped at :172), `createStreamOf`/`realisedCreate`
  (twins of :288/:296).
- `CreateRealises.lean`: `evmV2CreateEntry result pd self : World × Word :=
  ((fun key => evmCreateOracle.postStorage result pd self key),
  evmCreateOracle.addressWord result pd)` (twin of `evmV2CallEntry`,
  CallRealises.lean:59; the oracle already exists, `Create.lean:99`).
- `RecorderLemmas.lean`: `realisedCreate_cons` (twin of `realisedCall_cons` :44,
  `rfl`-clean by the same `simp … List.map_cons`).
- `Surface.lean` `RecorderCoupled`: `createSuffix`/`createPrefix` fields.

None of these touch the existing call/gas/sload declarations; each is a parallel
addition.
