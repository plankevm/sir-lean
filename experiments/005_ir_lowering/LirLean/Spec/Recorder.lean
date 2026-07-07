import LirLean.Spec.CallEntry
-- NOTE: `BytecodeLayer.Hoare.GasMonotone` is a LIVE import even with the gas-monotonicity
-- law deleted — `DriveSim.lean` uses `Runs.gasAvailable_le` in code, and this import is the
-- only path bringing that module into DriveSim's cone.
import BytecodeLayer.Hoare.GasMonotone

/-!
# LirLean v2 — the instrumented recording interpreter `runWithLog` (regime (i))

This module builds **the interpreter that records the points of introspection**
(`docs/ir-design-v3.md` §8, regime (i); the WHY is in
`docs/lessons/derivations-traces-and-proof-relevance.md`).

The realised gas / call oracles must be **projections of a `Type`-valued
interpreter that runs the bytecode AND records the introspection points** — so
realisability is *constructive* (a function), not a `Prop` relation. `Prop` is
proof-irrelevant, so it cannot be eliminated into `Type` (`realisedGas : Runs →
GasOracle` does not typecheck); the recording interpreter is `Type`, so its
projections (`realisedGas`/`realisedCall`) are honest functions.

## The recording approach — a **parallel** interpreter (`driveLog`)

We do **not** modify the verified `drive` (re-proving `drive` is out of scope, and
`drive` is the never-OutOfFuel/gas-descent capstone's subject). Instead `driveLog`
is a *parallel* recording interpreter that mirrors `drive`'s exact recursion one
branch at a time, threading a `RunLog` accumulator:

* on a `GAS` step (`stepFrame current = .next exec'` with the op at `current`
  decoding to `.Smsf .GAS`) it records `UInt256.ofUInt64 exec'.gasAvailable` — the
  *post-charge* gas the `GAS` opcode reports, exactly `gasReadOf` of the
  post-step frame;
* on the **top-level** program's own returning external CALL (a `.inr (.call childRes)`
  result delivered to a suspended `.call pending` with the resumed pending stack empty)
  it records the `(childRes, pending)` pair as a `CallRecord` — the minimal data from
  which `realisedCall` reproduces this CALL's `evmV2CallEntry` `(world', success)` stream
  entry; a
  descended callee's inner CALL is black-boxed (gated out), exactly as its inner gas/sload
  reads are;
* it carries the run's final observable (the top-level `FrameResult`).

Because `driveLog` mirrors `drive` branch-for-branch, **result adequacy** is
`rfl`-driven by induction on fuel: `(driveLog … acc).map (·.1) = drive …`
(`driveLog_drive`).

Bytecode-coupled (references `Frame`/`drive`/`CallResult`/`evmV2CallEntry`), so it
lives here in the bridge layer, never in the frame-free `Machine.lean`/`Law.lean`.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare

-- RELOCATED from V2/Oracle.lean (Phase 2): the two defs the §7 tie-discharge layer
-- (`V2/Drive/SelfPresent.lean` — `GasLogAligned`, `FramesRun.snoc`/`.snoc_seed`,
-- `gasRecord_eq_gasReadOf`, `gasReadOf_gasFrame_eq_obs`) still consumes. The rest of
-- the gas-law interface (`GasRealises`, `.monotoneGas`, the guard theorems) was
-- deleted with the gas-monotonicity law (docs/gas-decision.md).

/-- The `Word` a `GAS` opcode at (post-charge) frame `fr` reports: `ofUInt64` of the
frame's `gasAvailable`. The realisability bridge between a gas read and a frame. -/
def gasReadOf (fr : Frame) : Word := UInt256.ofUInt64 fr.exec.gasAvailable

/-- The GAS-frames are threaded by `Runs` in program order: each is reachable from the
previous (so the machine genuinely ran between the two reads). A `Runs`-chain over the
witness list. -/
def FramesRun : List Frame → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => Runs a b ∧ FramesRun (b :: rest)

/-! ## The per-call record

The minimal datum a returning external CALL contributes to the log: the child's
`CallResult` and the suspended `PendingCall`. From these `callStreamOf` reproduces this
record's `evmV2CallEntry result pd self` (the `resumeAfterCall` projection of
`LirLean/Spec/CallEntry.lean`) — the `(postStorage, successWord)` stream entry, by
construction. -/

/-- One external CALL's recorded data: the child's `CallResult` and the parent's
`PendingCall`. The minimal pair `callStreamOf` reads to reproduce `evmV2CallEntry`. -/
structure CallRecord where
  /-- The child call's result (`drive`'s `childRes.toCallResult`). -/
  result : CallResult
  /-- The suspended parent call (carries the resume data `resumeAfterCall` needs). -/
  pending : PendingCall

/-- One external CREATE's recorded data: the child's `CreateResult` and the parent's
`PendingCreate` — the CREATE twin of `CallRecord`. The minimal pair `createStreamOf` reads to
reproduce `evmV2CreateEntry` (`LirLean/Spec/CallEntry.lean`). -/
structure CreateRecord where
  /-- The init child's result (`drive`'s `childRes.toCreateResult`). -/
  result : CreateResult
  /-- The suspended parent create (carries the resume data `resumeAfterCreate` needs). -/
  pending : PendingCreate

/-! ## The run log (`docs/ir-design-v3.md` §8) -/

/-- **The instrumented run log** — the introspection points a bytecode run records.
`Type`-valued, so its projections (`realisedGas`/`realisedCall`) are functions.

* `observable` — the run's final top-level `FrameResult` (the bytecode boundary);
* `gas` — the `GAS` reads, in program order (→ `realisedGas`);
* `calls` — the top-level returning external CALLs' data, in program order
  (→ `realisedCall`). -/
structure RunLog where
  /-- The run's final result (the top-level `FrameResult` the run produced). -/
  observable : FrameResult
  /-- The `GAS` reads, in program order. -/
  gas : List Word
  /-- The `SLOAD` warmth-charges (`sloadCost warm`), in program order — the realised
  warmth/cost at each top-level SLOAD site (→ `realisedSload`). Parallel to `gas`. -/
  sloads : List Nat
  /-- The top-level returning external CALLs' records, in program order. -/
  calls : List CallRecord
  /-- The top-level returning external CREATEs' records, in program order
  (→ `realisedCreate`). Parallel to `calls` — the fourth threaded channel (option A,
  `docs/create/stream-decision.md`). -/
  creates : List CreateRecord

/-! ## GAS-step detection

A `.next` step is a `GAS` read exactly when the decoded op at the running frame is
`.Smsf .GAS`. We detect it from the decode, gating the record. -/

/-- `True` iff the op decoded at `fr`'s pc is `GAS` (`.Smsf .GAS`). The gate that
turns a `.next` step into a recorded gas read. -/
def isGasOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 == .Smsf .GAS

/-! ## SLOAD-step detection and the recorded warmth-charge

A `.next` step is an `SLOAD` read exactly when the decoded op at the running frame is
`.Smsf .SLOAD`. The recorded datum is the warmth-cost `sloadCost warm` charged at that
frame, where `warm = accessedStorageKeys.contains (self, key)` and `key` is the top of
the stack (`sloadPost`) — exactly the value `SloadRealises` demands (the value-level
bridge `sloadRecord_eq_sloadCost`). -/

/-- `True` iff the op decoded at `fr`'s pc is `SLOAD` (`.Smsf .SLOAD`). The gate that
turns a `.next` step into a recorded SLOAD warmth-charge (mirrors `isGasOp`). -/
def isSloadOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 == .Smsf .SLOAD

/-- The warmth-charge `SLOAD` reports at (pre-step) frame `fr`: `sloadCost warm`, where
`warm = accessedStorageKeys.contains (self, key)` and `key` is the top of `fr`'s stack
(the key SLOAD pops — `sloadPost`). This is exactly the value `SloadRealises` demands at
an SLOAD frame whose stack-head is the bound key (`sloadRecord_eq_sloadCost`). The
`none`-head case (empty stack) is unreachable at a real SLOAD step (`stepFrame_sload`
forces `stack = key :: rest`); it is `0`. -/
def sloadWarmthOf (fr : Frame) : Nat :=
  match fr.exec.stack.head? with
    | some key =>
        Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
          (fr.exec.executionEnv.address, key))
    | none => 0

/-! ## The recording interpreter `driveLog`

A parallel copy of `drive` (`EVMLean/Evm/Semantics/Interpreter.lean`) threading a
`(gas, calls)` accumulator. **Every branch is byte-for-byte `drive`'s own
branch**, with two recording points spliced in: the `GAS` `.next` step (append the
post-charge gas word) and the returning-`.call` delivery (append the
`(result, pending)` record). On success it returns `(r, gas, calls)`; the gas /
call lists are in program order (appended at each point). -/

/-- Append a returning-CALL record for a `.call` delivery; a `.create` delivery
contributes nothing. Factored out of `driveLog` so the delivery branch's
`pending.resume result` match is byte-for-byte `drive`'s (adequacy aligns).

GATE (2026-07-03, recorder-fix): `recordCall` itself is unconditional — it just
appends — but both `driveLog` delivery call sites now invoke it ONLY under the
`rest.isEmpty` guard (the resumed pending stack is empty). So a record is added
exactly for the **top-level** program's own returning CALL, never for a descended
callee's inner CALL (which resumes on a nonempty `rest`, still carrying the
parent's suspended `.call`). This matches the gas/sload `stack.isEmpty` gates:
only top-level calls record. See the `driveLog` docstring and its delivery-branch
comment for the gate placement. -/
def recordCall (pending : Pending) (result : FrameResult) (callAcc : List CallRecord) :
    List CallRecord :=
  match pending with
    | .call pd => callAcc ++ [{ result := result.toCallResult, pending := pd }]
    | .create _ => callAcc

/-- Append a returning-CREATE record for a `.create` delivery — the CREATE twin of
`recordCall`, un-dropping the create delivery `recordCall` leaves in the CALL channel
(a `.call` delivery contributes nothing to the CREATE channel, exactly as a `.create`
delivery contributes nothing to the CALL channel). Gated identically in `driveLog` on
`rest.isEmpty` (top-level only). -/
def recordCreate (pending : Pending) (result : FrameResult) (createAcc : List CreateRecord) :
    List CreateRecord :=
  match pending with
    | .call _ => createAcc
    | .create pd => createAcc ++ [{ result := result.toCreateResult, pending := pd }]

/-- The recording driver: `drive` with a `(gas, sloads, calls)` accumulator. Mirrors
`drive`'s recursion branch-for-branch; records each top-level `GAS` read's post-charge
word, each top-level `SLOAD`'s warmth-charge (`sloadCost warm`), and each top-level
returning external CALL's `(result, pending)`. All three records gate on the top-level
frame: gas/sload on `stack.isEmpty` (the running frame is the top-level one), the CALL
record on `rest.isEmpty` (the resumed pending stack is empty — the top-level program's own
CALL, not a descended callee's inner CALL). The `sloadAcc` is threaded exactly like
`gasAcc` and is erased by `.map (·.1)` (adequacy preserved by construction). -/
def driveLog (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
    (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord)
    (createAcc : List CreateRecord) :
    Except ExecutionException
      (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord) :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok (result, gasAcc, sloadAcc, callAcc, createAcc)
            | pending :: rest =>
              -- the `pending.resume result` match is byte-for-byte `drive`'s; the only
              -- difference is the accumulator carries a returning-CALL record (`recordCall`)
              -- and a returning-CREATE record (`recordCreate`), and only for the TOP-LEVEL
              -- program's own returning descents. Both records are gated on `rest.isEmpty`
              -- (the resumed pending stack), mirroring the gas/sload `stack.isEmpty` gates
              -- below: the top-level program's own descent returns with `rest = []`, while a
              -- descended callee's inner descent returns with `rest` nonempty (it still
              -- carries the parent's suspended `.call`), so it is black-boxed exactly as the
              -- callee's inner gas/sload reads are. `recordCall`/`recordCreate` are duals: a
              -- `.call` delivery records only into `callAcc`, a `.create` delivery only into
              -- `createAcc`.
              match pending.resume result with
                | .ok parent =>
                  driveLog fuel rest (.inl parent) gasAcc sloadAcc
                    (if rest.isEmpty then recordCall pending result callAcc else callAcc)
                    (if rest.isEmpty then recordCreate pending result createAcc else createAcc)
                | .error e =>
                  driveLog fuel rest (.inr (endFrame pending.frame (.exception e)))
                    gasAcc sloadAcc
                    (if rest.isEmpty then recordCall pending result callAcc else callAcc)
                    (if rest.isEmpty then recordCreate pending result createAcc else createAcc)
        | .inl current =>
          match stepFrame current with
            | .next exec =>
              -- Record a gas read iff the op at `current` is `GAS` **and** this is the
              -- top-level frame (`stack = []`). A descended CALL'd contract's *internal*
              -- GAS reads are not the IR program's observable gas sequence — the IR is a
              -- single contract, its `Expr.gas` reads are its own (top-level) frame's, and
              -- the realisability witness (`Runs.gasAvailable_le`)
              -- threads exactly the top-level frame across `CallReturns` (children
              -- black-boxed). At `stack = []` the recorded reads are then non-increasing.
              -- Symmetrically, record an SLOAD warmth-charge iff the op is `SLOAD` and this
              -- is the top-level frame — the realised warmth at the top-level program's own
              -- SLOAD sites, read off the **pre-step** frame `current` (`sloadWarmthOf`).
              -- The CALL/CREATE records above are gated identically: a descended callee
              -- resumes its own inner descents on a nonempty pending stack
              -- (`rest ⊇ [.call parent] ≠ []`), so those inner descents are excluded exactly
              -- as the callee's inner gas/sload reads are — only the top-level program's own
              -- descent (resumed at `rest = []`) is recorded.
              if isGasOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) sloadAcc callAcc createAcc
              else if isSloadOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  gasAcc (sloadAcc ++ [sloadWarmthOf current]) callAcc createAcc
              else
                driveLog fuel stack (.inl { current with exec := exec }) gasAcc sloadAcc callAcc createAcc
            | .halted halt => driveLog fuel stack (.inr (endFrame current halt)) gasAcc sloadAcc callAcc createAcc
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => driveLog fuel (.call pending :: stack) (.inl child) gasAcc sloadAcc callAcc createAcc
                | .inr result => driveLog fuel (.call pending :: stack) (.inr (.call result)) gasAcc sloadAcc callAcc createAcc
            | .needsCreate params pending =>
              -- `beginCreate` is total (mirrors `drive`): the descent is unconditional.
              driveLog fuel (.create pending :: stack) (.inl (beginCreate params)) gasAcc sloadAcc callAcc createAcc

/-! ## The top-level recording interpreter

`runWithLog code w₀ fuel` seeds a top-level frame from a `CallParams` and runs
`driveLog` on it with an empty accumulator, packaging the result into a `RunLog`.
The signature in the design doc is `Bytecode → World → ℕ → Option RunLog`; here the
entry is a `CallParams` (the exp003 entry vocabulary — `beginCall`'s input), which
carries the code, the world (accounts), and the gas. We expose the params-form (the
one the bytecode layer actually runs) and project to `Option` on the `Except`. -/

/-- **The instrumented recording interpreter** (`docs/ir-design-v3.md` §8, regime
(i)). Run the call `params` as a top-level frame, recording the `GAS` reads and the
returning external CALLs; package the introspection points as a `RunLog`. `none` on
a precompile/immediate result (no frame to instrument) or an engine error. Mirrors
`messageCall`'s entry: `beginCall params = .inl frame`, then `driveLog`. -/
def runWithLog (params : CallParams) (fuel : ℕ) : Option RunLog :=
  match beginCall params with
    | .inr _ => none
    | .inl frame =>
      match driveLog fuel [] (.inl frame) [] [] [] [] with
        | .ok (r, gas, sloads, calls, creates) =>
            some { observable := r, gas := gas, sloads := sloads, calls := calls,
                   creates := creates }
        | .error _ => none

/-! ## Projections (`docs/ir-design-v3.md` §8)

The realised oracles are projections of the `RunLog` — *functions*, because the log
is `Type`-valued. -/

/-- **The realised gas oracle.** The recorded `GAS` reads, in program order — a
`GasOracle` (`= List Word`). The whole regime-(i) point: a function, not a `Prop`
extraction. -/
def realisedGas (log : RunLog) : GasOracle := log.gas

/-- **The realised SLOAD-warmth oracle.** The recorded `SLOAD` warmth-charges
(`sloadCost warm`), in program order — the realised warmth-cost stream the §7
`SloadRealises` tie selects from (parallel to `realisedGas`). The per-cursor selection
is the deferred alignment (parallel to GAS); this is the recorded value channel. -/
def realisedSload (log : RunLog) : List Nat := log.sloads

/-- The call stream realised by a list of `CallRecord`s at self address `self`: the
per-record `evmV2CallEntry` projection, in recorded order (mirrors `realisedGas log :=
log.gas`). Each entry is a `(post-call world, success)` pair the `Stmt.call` step consumes
head-first — *positional*, keyed on the record, so multi-CALL runs are covered with no
single-call collapse. Aligned with `evmV2CallEntry` by construction. -/
def callStreamOf (calls : List CallRecord) (self : AccountAddress) : CallStream :=
  calls.map (fun rec => evmV2CallEntry rec.result rec.pending self)

/-- **The realised call stream** (`docs/ir-design-v3.md` §8, R3′): the `CallStream` read
off the log's recorded CALLs, at self address `self` — the FULL stream, consumed head-first
by `Stmt.call`. Aligned with `evmV2CallEntry` (`LirLean/Spec/CallEntry.lean`) — each
recorded CALL *is* that entry's `resumeAfterCall` projection, so the call-side realisability
is `rfl`-clean. -/
def realisedCall (log : RunLog) (self : AccountAddress) : CallStream :=
  callStreamOf log.calls self

/-- The create stream realised by a list of `CreateRecord`s at self address `self`: the
per-record `evmV2CreateEntry` projection, in recorded order (the CREATE twin of
`callStreamOf`). Each entry is a `(post-create world, deployed-address-or-0)` pair the
`Stmt.create` step consumes head-first — *positional*, keyed on the record, so multi-CREATE
runs are covered. Aligned with `evmV2CreateEntry` by construction. -/
def createStreamOf (creates : List CreateRecord) (self : AccountAddress) : CreateStream :=
  creates.map (fun rec => evmV2CreateEntry rec.result rec.pending self)

/-- **The realised create stream** (the CREATE twin of `realisedCall`): the `CreateStream` read
off the log's recorded CREATEs, at self address `self` — the FULL stream, consumed head-first
by `Stmt.create`. Aligned with `evmV2CreateEntry` (`LirLean/Spec/CallEntry.lean`) — each
recorded CREATE *is* that entry's `resumeAfterCreate` projection. -/
def realisedCreate (log : RunLog) (self : AccountAddress) : CreateStream :=
  createStreamOf log.creates self

/-! ## The `observe` bridge: bytecode `FrameResult` → IR `Observable`
(`docs/ir-design-v3.md` §8)

The conformance diagram's last edge: a function mapping the **bytecode** result (a
`FrameResult`) to the **IR's** `V2.Observable`. The IR observable is two fields:

* `world` — the self-account storage lens. The whole v2 layer reads storage through
  exp003's `find?/lookupStorage` lens (`Match.storageAt`/`selfStorage`,
  `evmCallOracle.postStorage`); `observe`'s `world` is that same lens on the result's
  committed `accounts` (`fr.toCallResult.accounts`) at the self address — the
  `FrameResult` analogue of `Match.storageAt`.
* `result` — the halt. The IR's `IRHalt` is `stopped`/`returned (w : Word)`; revert
  is out of v2 scope (`Machine.lean`, `IRHalt` doc). This channel is now **live**: it
  reads the finished frame's RETURN output (`fr.toCallResult.output : ByteArray`) — the
  faithful inverse of the `ret` lowering, which stashes the returned word to `mem[0]`
  and `RETURN(0, 32)`s it (`emitTerm .ret`). An **empty** output is the `STOP` /
  empty-`RETURN` success boundary (`.stopped`); a **non-empty** output is a genuine
  `RETURN t`, decoded big-endian back to the returned word (`uInt256OfByteArray`,
  round-tripping the 32-byte window — `MemAlgebra.uInt256OfByteArray_toByteArray`). Revert
  is out of clean scope, so the `.returned` branch is only reached for genuine RETURN
  frames. -/

/-- The self account's storage at `key` read off a finished `FrameResult`, through
exp003's observable `find?/lookupStorage` lens — the `FrameResult` analogue of
`Match.storageAt` (which reads a `Frame`). Reads the result's committed
`accounts` (`fr.toCallResult.accounts`), the map `resumeAfterCall` writes back into
`exec.accounts`, so it agrees with `storageAt (resumeAfterCall …)` by construction. -/
def resultStorageAt (fr : FrameResult) (addr : AccountAddress) (key : Word) : Word :=
  fr.toCallResult.accounts.find? addr |>.option 0 (·.lookupStorage key)

/-- **The `observe` bridge** (`docs/ir-design-v3.md` §8): map a bytecode `FrameResult`
to the IR's `V2.Observable`, at self address `self`. The `world` is the self-account
storage lens on the result's committed `accounts` (the same lens the rest of v2 uses —
`Match.storageAt` / `evmCallOracle.postStorage`); the `result` reads the finished frame's
RETURN output (`fr.toCallResult.output`) — empty ⇒ `.stopped`, else the 32-byte window
decoded big-endian to the returned word (`.returned (uInt256OfByteArray output)`), the
faithful inverse of the `ret` lowering. -/
def observe (self : AccountAddress) (fr : FrameResult) : Observable :=
  { world  := fun key => resultStorageAt fr self key
    result := let out := fr.toCallResult.output
              if out.isEmpty then .stopped else .returned (uInt256OfByteArray out) }

/-- `observe`'s result channel, unfolded: empty output ⇒ `.stopped`, else the returned
window decoded big-endian. -/
theorem observe_result (self : AccountAddress) (fr : FrameResult) :
    (observe self fr).result =
      (if fr.toCallResult.output.isEmpty then .stopped
        else .returned (uInt256OfByteArray fr.toCallResult.output)) := rfl

/-! The `workedCall` instance of the `observe`-bridged conformance (`wcRunLog`,
`realisedCall_wcRunLog`, `wc_observe_conforms`) is a *leaf example* — it couples
`LirLean.WorkedCall`, which must stay OFF the headline import cone (`SimTerm` imports this
module). It therefore lives in `LirLean/V2/WorkedCallParity.lean`, built on the general
recorder defs above (`wcRunLog`, `realisedCall`, `observe`). -/

end Lir.V2
