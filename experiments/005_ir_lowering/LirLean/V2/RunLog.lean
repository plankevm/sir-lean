import LirLean.V2.CallRealises
import LirLean.V2.Oracle
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
projections (`realisedGas`/`realisedCall`) are honest functions and
`realisedGas_monotone` is the constructive realisability the regime is for.

## The recording approach — a **parallel** interpreter (`driveLog`)

We do **not** modify the verified `drive` (re-proving `drive` is out of scope, and
`drive` is the never-OutOfFuel/gas-descent capstone's subject). Instead `driveLog`
is a *parallel* recording interpreter that mirrors `drive`'s exact recursion one
branch at a time, threading a `RunLog` accumulator:

* on a `GAS` step (`stepFrame current = .next exec'` with the op at `current`
  decoding to `.Smsf .GAS`) it records `UInt256.ofUInt64 exec'.gasAvailable` — the
  *post-charge* gas the `GAS` opcode reports, exactly `Oracle.gasReadOf` of the
  post-step frame;
* on a returning external CALL (a `.inr (.call childRes)` result delivered to a
  suspended `.call pending`) it records the `(childRes, pending)` pair as a
  `CallRecord` — the minimal data from which `realisedCall` reproduces
  `evmV2CallOracle`'s `(world', success)` projection;
* it carries the run's final observable (the top-level `FrameResult`).

Because `driveLog` mirrors `drive` branch-for-branch, **result adequacy** is
`rfl`-driven by induction on fuel: `(driveLog … acc).map (·.1) = drive …`
(`driveLog_drive`). And the recorded gas list is monotone non-increasing because
each recorded read is the machine's post-charge `gasAvailable`, and that quantity
is non-increasing across the *whole* run — the **same** `totalGas` descent the
gas-conservation lemma `drive_gasRemaining_le_totalGas` is built on, here threaded
alongside the log (`driveLog_gas_inv`). This is the constructive
`realisedGas_monotone`.

Bytecode-coupled (references `Frame`/`drive`/`CallResult`/`evmV2CallOracle`), so it
lives here in the bridge layer, never in the frame-free `Machine.lean`/`Law.lean`.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare

/-! ## The per-call record

The minimal datum a returning external CALL contributes to the log: the child's
`CallResult` and the suspended `PendingCall`. From these `realisedCall` reproduces
`evmV2CallOracle result pd self` (the `resumeAfterCall` projection of
`LirLean/V2/CallRealises.lean`) — the `(postStorage, successWord)` bundle, by
construction. -/

/-- One external CALL's recorded data: the child's `CallResult` and the parent's
`PendingCall`. The minimal pair `realisedCall` reads to reproduce `evmV2CallOracle`. -/
structure CallRecord where
  /-- The child call's result (`drive`'s `childRes.toCallResult`). -/
  result : CallResult
  /-- The suspended parent call (carries the resume data `resumeAfterCall` needs). -/
  pending : PendingCall

/-! ## The run log (`docs/ir-design-v3.md` §8) -/

/-- **The instrumented run log** — the introspection points a bytecode run records.
`Type`-valued, so its projections (`realisedGas`/`realisedCall`) are functions.

* `observable` — the run's final top-level `FrameResult` (the bytecode boundary);
* `gas` — the `GAS` reads, in program order (→ `realisedGas`);
* `calls` — the returning external CALLs' data, in program order (→ `realisedCall`). -/
structure RunLog where
  /-- The run's final result (the top-level `FrameResult` the run produced). -/
  observable : FrameResult
  /-- The `GAS` reads, in program order. -/
  gas : List Word
  /-- The `SLOAD` warmth-charges (`sloadCost warm`), in program order — the realised
  warmth/cost at each top-level SLOAD site (→ `realisedSload`). Parallel to `gas`. -/
  sloads : List Nat
  /-- The returning external CALLs' records, in program order. -/
  calls : List CallRecord

/-- The empty accumulator: no gas reads, no sload charges, no calls (the `observable` is
filled in at the top-level return). The seed for `driveLog`'s recording. -/
def RunAcc : Type := List Word × List Nat × List CallRecord

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
`RunAcc = (gas, calls)` accumulator. **Every branch is byte-for-byte `drive`'s own
branch**, with two recording points spliced in: the `GAS` `.next` step (append the
post-charge gas word) and the returning-`.call` delivery (append the
`(result, pending)` record). On success it returns `(r, gas, calls)`; the gas /
call lists are in program order (appended at each point). -/

/-- Append a returning-CALL record for a `.call` delivery; a `.create` delivery
contributes nothing. Factored out of `driveLog` so the delivery branch's
`pending.resume result` match is byte-for-byte `drive`'s (adequacy aligns). -/
def recordCall (pending : Pending) (result : FrameResult) (callAcc : List CallRecord) :
    List CallRecord :=
  match pending with
    | .call pd => callAcc ++ [{ result := result.toCallResult, pending := pd }]
    | .create _ => callAcc

/-- The recording driver: `drive` with a `(gas, sloads, calls)` accumulator. Mirrors
`drive`'s recursion branch-for-branch; records each `GAS` read's post-charge word, each
top-level `SLOAD`'s warmth-charge (`sloadCost warm`), and each returning external CALL's
`(result, pending)`. The `sloadAcc` is threaded exactly like `gasAcc` and is erased by
`.map (·.1)` (adequacy preserved by construction). -/
def driveLog (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
    (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord) :
    Except ExecutionException (FrameResult × List Word × List Nat × List CallRecord) :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok (result, gasAcc, sloadAcc, callAcc)
            | pending :: rest =>
              -- the `pending.resume result` match is byte-for-byte `drive`'s; the only
              -- difference is the accumulator carries a returning-CALL record (`recordCall`).
              match pending.resume result with
                | .ok parent =>
                  driveLog fuel rest (.inl parent) gasAcc sloadAcc (recordCall pending result callAcc)
                | .error e =>
                  driveLog fuel rest (.inr (endFrame pending.frame (.exception e)))
                    gasAcc sloadAcc (recordCall pending result callAcc)
        | .inl current =>
          match stepFrame current with
            | .next exec =>
              -- Record a gas read iff the op at `current` is `GAS` **and** this is the
              -- top-level frame (`stack = []`). A descended CALL'd contract's *internal*
              -- GAS reads are not the IR program's observable gas sequence — the IR is a
              -- single contract, its `Expr.gas` reads are its own (top-level) frame's, and
              -- the realisability witness (`Oracle.GasRealises`, `Runs.gasAvailable_le`)
              -- threads exactly the top-level frame across `CallReturns` (children
              -- black-boxed). At `stack = []` the recorded reads are then non-increasing.
              -- Symmetrically, record an SLOAD warmth-charge iff the op is `SLOAD` and this
              -- is the top-level frame — the realised warmth at the top-level program's own
              -- SLOAD sites, read off the **pre-step** frame `current` (`sloadWarmthOf`).
              if isGasOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) sloadAcc callAcc
              else if isSloadOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  gasAcc (sloadAcc ++ [sloadWarmthOf current]) callAcc
              else
                driveLog fuel stack (.inl { current with exec := exec }) gasAcc sloadAcc callAcc
            | .halted halt => driveLog fuel stack (.inr (endFrame current halt)) gasAcc sloadAcc callAcc
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => driveLog fuel (.call pending :: stack) (.inl child) gasAcc sloadAcc callAcc
                | .inr result => driveLog fuel (.call pending :: stack) (.inr (.call result)) gasAcc sloadAcc callAcc
            | .needsCreate params pending =>
              match beginCreate params with
                | .ok child => driveLog fuel (.create pending :: stack) (.inl child) gasAcc sloadAcc callAcc
                | .error _ =>
                  let exec := pending.frame.exec
                  let result : CreateResult :=
                    { address := 0
                      createdAccounts := exec.createdAccounts
                      accounts := ∅
                      gasRemaining := 0
                      substate := exec.substate
                      success := false
                      output := .empty }
                  driveLog fuel (.create pending :: stack) (.inr (.create result)) gasAcc sloadAcc callAcc

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
      match driveLog fuel [] (.inl frame) [] [] [] with
        | .ok (r, gas, sloads, calls) =>
            some { observable := r, gas := gas, sloads := sloads, calls := calls }
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

/-- **The SLOAD value-level bridge** (parallel to `gasReadOf_gasFrame_eq_obs`). At an
SLOAD frame `g` whose stack-head is the bound key (`g.exec.stack.head? = some key`), the
recorded warmth-charge `sloadWarmthOf g` is exactly the value `SloadRealises` demands at
that frame: `sloadCost (accessedStorageKeys.contains (self, key))`. `simp`-clean (it is
`sloadWarmthOf`'s `some`-branch unfolded). So once the (deferred) alignment selects that
the SLOAD cursor's recorded charge is this site's `sloadWarmthOf`, the `sloadChg k =
sloadCost …` conjunct of `SloadRealises` is discharged at the cursor frame. -/
theorem sloadRecord_eq_sloadCost (g : Frame) {key : Word}
    (hkey : g.exec.stack.head? = some key) :
    sloadWarmthOf g
      = Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
          (g.exec.executionEnv.address, key)) := by
  simp only [sloadWarmthOf, hkey]

/-- The call oracle realised by a list of `CallRecord`s at self address `self`:
the *first* record's `evmV2CallOracle` projection. For the single-CALL fragment
(the present scope) this is the realised call effect; a multi-CALL run would key on
the call site, which the per-record `pending` carries. Aligned with
`evmV2CallOracle` by construction. -/
def callOracleOf (calls : List CallRecord) (self : AccountAddress) : CallOracle :=
  match calls with
    | [] => fun _ _ w => (w, 0)   -- no CALL recorded: identity world, success 0
    | rec :: _ => evmV2CallOracle rec.result rec.pending self

/-- **The realised call oracle** (`docs/ir-design-v3.md` §8): the `CallOracle` read
off the log's recorded CALLs, at self address `self`. Aligned with `evmV2CallOracle`
(`LirLean/V2/CallRealises.lean`) — for a recorded CALL it *is* that oracle's
`resumeAfterCall` projection, so the call-side realisability is `rfl`-clean. -/
def realisedCall (log : RunLog) (self : AccountAddress) : CallOracle :=
  callOracleOf log.calls self

/-- **`realisedCall` faithfulness.** When the log recorded a CALL (`log.calls = rec ::
_`), the realised call oracle *is* `evmV2CallOracle` at that record's `(result, pending)`
— the `resumeAfterCall` projection of `LirLean/V2/CallRealises.lean`. `rfl`-clean, so
`callRealises_bridge` ties its `(world', success)` bundle to the lowered CALL's
observable by construction (the call-side realisability). -/
theorem realisedCall_eq_evmV2 {log : RunLog} {rec : CallRecord} {tl : List CallRecord}
    (self : AccountAddress) (hc : log.calls = rec :: tl) :
    realisedCall log self = evmV2CallOracle rec.result rec.pending self := by
  simp only [realisedCall, callOracleOf, hc]

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
  is out of v2 scope (`Machine.lean`, `IRHalt` doc) and a successful frame's RETURN
  output is a memory *byte window* (`endCall`'s `output : ByteArray`), not a `Word`,
  so it does **not** reconstruct the IR's value-as-word `returned w` faithfully
  (value-free scope, §6/§7). **Restriction (reported):** `observe` maps the result to
  `.stopped` (the value-free success boundary); the faithful `output → Word` for
  `returned` is deferred with the rest of the value channel. The `result` field of
  `observe` is therefore **not** exercised by the worked-call corollary below, which
  bridges the *world* component (the IR observable the realised oracle actually
  determines). -/

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
`Match.storageAt` / `evmCallOracle.postStorage`); the `result` is the value-free
success boundary `.stopped` (see the restriction note above — the faithful RETURN
`output → Word` for `.returned` is deferred with the value channel). -/
def observe (self : AccountAddress) (fr : FrameResult) : Observable :=
  { world  := fun key => resultStorageAt fr self key
    result := .stopped }

/-! ## Result adequacy: `driveLog` agrees with `drive`

`driveLog` mirrors `drive` branch-for-branch, so its result projection is exactly
`drive`'s result — the recording does not change *what* the machine computes, only
*what it remembers*. By induction on fuel, each branch reducing both sides one step
to a recursive call the IH closes (the recording splices are erased by `.map (·.1)`). -/

/-- **Result adequacy of `driveLog`.** The recording interpreter computes the same
result as `drive`: erasing the log (`Except.map (·.1)`) recovers `drive`'s output,
for *any* accumulator. Induction on fuel, one branch per `drive`/`driveLog`
transition — the two are definitionally the same control flow, the splices only
touch the (erased) accumulator. -/
theorem driveLog_drive :
    ∀ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord),
      (driveLog f stack state gasAcc sloadAcc callAcc).map (·.1) = drive f stack state := by
  intro f
  induction f with
  | zero => intro stack state gasAcc sloadAcc callAcc; rfl
  | succ n ih =>
    intro stack state gasAcc sloadAcc callAcc
    unfold driveLog drive
    -- Case on each scrutinee with `cases h : …` (substitutes *both* sides at once, so
    -- LHS and RHS never desync). Every branch reduces both sides to a recursive call
    -- the IH closes, or to the `.ok` leaf (`rfl`). The recording splices (the gas `if`,
    -- `recordCall`) only touch the erased accumulator, dropped by `Except.map (·.1)`.
    cases state with
    | inr result =>
      dsimp only
      cases stack with
      | nil => rfl
      | cons pending rest =>
        dsimp only
        cases h : pending.resume result with
        | ok parent => dsimp only [h]; exact ih rest (.inl parent) _ _ _
        | error e => dsimp only [h]; exact ih rest (.inr (endFrame pending.frame (.exception e))) _ _ _
    | inl current =>
      dsimp only
      cases h : stepFrame current with
      | next exec =>
        dsimp only [h]
        -- the nested recording `if`s (gas / sload / else) all reduce to the same recursive
        -- `driveLog` call modulo the (erased) accumulators; split every arm, close by `ih`.
        split <;> [skip; split] <;> exact ih stack (.inl { current with exec := exec }) _ _ _
      | halted halt => dsimp only [h]; exact ih stack (.inr (endFrame current halt)) _ _ _
      | needsCall params pending =>
        dsimp only [h]
        cases hbc : beginCall params with
        | inl child => dsimp only [hbc]; exact ih (.call pending :: stack) (.inl child) _ _ _
        | inr result => dsimp only [hbc]; exact ih (.call pending :: stack) (.inr (.call result)) _ _ _
      | needsCreate params pending =>
        dsimp only [h]
        cases hbcr : beginCreate params with
        | ok child => dsimp only [hbcr]; exact ih (.create pending :: stack) (.inl child) _ _ _
        | error e => dsimp only [hbcr]; exact ih (.create pending :: stack) (.inr (.create _)) _ _ _

/-! ## Gas monotonicity: the recorded reads are non-increasing (`realisedGas_monotone`)

This is the constructive realisability the whole regime is for. The recorded gas
reads are monotone NON-increasing on `.toNat` because **each recorded read is the
machine's post-charge `gasAvailable`**, and that quantity never increases across the
*whole* run — the **same** `totalGas` descent the gas-conservation lemma
`drive_gasRemaining_le_totalGas` is built on (`StepsTo.gas_le` per step, the
`gasFundsDescent_conj*` descents, `resumeAfterCall_gas_le`/`endFrame_gasRemaining_le`
deliveries — including across `.call` nodes).

We prove it as a **`Pairwise`** invariant (stronger than `IsChain`, and append-friendly:
`pairwise_append`): every earlier read relates to every later one, threaded with the
upper bound `totalGas stack state` (every recorded read is `≥` the current total gas,
since reads only ever decrease). `Pairwise.isChain` then yields `MonotoneGas`. The
branch structure mirrors `drive_gasRemaining_le_totalGas` exactly; each per-transition
`totalGas`-descent fact is reused verbatim. -/

/-- The non-increasing relation on gas words (`.toNat` order), the body of
`MonotoneGas`/`Trace.gasMonotone`. -/
abbrev geToNat (earlier later : Word) : Prop := later.toNat ≤ earlier.toNat

/-- Re-establish the lower-bound clause under a `totalGas` descent: if every read is
`≥` the old bound `B` and the new bound `B' ≤ B`, then every read is `≥ B'`. The glue
between adjacent transitions (the accumulator is unchanged, only the bound drops). -/
theorem bound_mono {gasAcc : List Word} {B B' : ℕ} (hle : B' ≤ B)
    (hb : ∀ x ∈ gasAcc, B ≤ x.toNat) : ∀ x ∈ gasAcc, B' ≤ x.toNat :=
  fun x hx => Nat.le_trans hle (hb x hx)

/-- **The gas invariant for `driveLog`.** If `driveLog` succeeds with output gas list
`gasOut`, and the accumulator `gasAcc` is already `Pairwise`-non-increasing with every
entry `≥` the current `totalGas`, then `gasOut` is `Pairwise`-non-increasing with every
entry `≥` the final result's `gasRemaining`. The two invariant clauses survive every
transition: the bound drops monotonically by the **same** per-transition `totalGas`
descents `drive_gasRemaining_le_totalGas` uses (`StepsTo.gas_le`, `endFrame_gasRemaining_le`,
the `gasFundsDescent_conj*` descents, `resumeAfterCall_gas_le`); and an appended GAS read
(only at `stack = []`, where `totalGas = activeGas`) is `≤` the bound, hence `≤` every
prior read (`pairwise_append`). Induction on fuel, mirroring `drive_gasRemaining_le_totalGas`. -/
theorem driveLog_gas_inv :
    ∀ (f : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
      (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord)
      (r : FrameResult) (gasOut : List Word) (sloadsOut : List Nat) (callsOut : List CallRecord),
      driveLog f stack state gasAcc sloadAcc callAcc = .ok (r, gasOut, sloadsOut, callsOut) →
      gasAcc.Pairwise geToNat →
      (∀ x ∈ gasAcc, totalGas stack state ≤ x.toNat) →
      gasOut.Pairwise geToNat ∧ (∀ x ∈ gasOut, FrameResult.gasRemaining r ≤ x.toNat) := by
  intro f
  induction f with
  | zero =>
    intro stack state gasAcc sloadAcc callAcc r gasOut sloadsOut callsOut h _ _
    simp [driveLog] at h
  | succ n ih =>
    intro stack state gasAcc sloadAcc callAcc r gasOut sloadsOut callsOut h hpair hbound
    unfold driveLog at h
    dsimp only at h
    cases state with
    | inr result =>
      dsimp only at h
      cases hstk : stack with
      | nil =>
        rw [hstk] at h hbound; dsimp only at h
        -- top-level result: `gasOut = gasAcc`, `r = result`; both clauses survive
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hr, hg, _, _⟩ := h
        subst hr; subst hg
        refine ⟨hpair, fun x hx => ?_⟩
        have := hbound x hx
        simpa only [totalGas, activeGas, List.map_nil, List.sum_nil, Nat.add_zero] using this
      | cons pending rest =>
        rw [hstk] at h; rw [hstk] at hbound; dsimp only at h
        -- delivery: `gasAcc` unchanged; the `totalGas` descent across the resume keeps
        -- the bound (each case the corresponding `drive_gasRemaining_le_totalGas` brick).
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at h; dsimp only at h
          -- parent gas ≤ savedGas pending + result.gasRemaining (delivery bound)
          have hcons : activeGas (.inl parent)
              ≤ Pending.savedGas pending + FrameResult.gasRemaining result := by
            cases pending with
            | call pd =>
              simp only [Pending.resume] at hres
              simp only [Except.ok.injEq] at hres; subst hres
              have hb := resumeAfterCall_gas_le result.toCallResult pd
              rw [toCallResult_gasRemaining] at hb
              simp only [activeGas, Pending.savedGas]; omega
            | create pd =>
              simp only [Pending.resume] at hres
              have hb := resumeAfterCreate_gas_le_savedGas (result := result.toCreateResult)
                (pd := pd) hres
              rw [toCreateResult_gasRemaining] at hb
              simp only [activeGas, Pending.savedGas]; omega
          have hdesc : totalGas rest (.inl parent) ≤ totalGas (pending :: rest) (.inr result) := by
            rw [totalGas_cons]; simp only [totalGas, activeGas] at hcons ⊢; omega
          exact ih rest (.inl parent) _ _ _ r gasOut sloadsOut callsOut h hpair (bound_mono hdesc hbound)
        | error e =>
          rw [hres] at h; dsimp only at h
          -- exceptional resume: the delivered result carries gas 0
          have hz : FrameResult.gasRemaining (endFrame pending.frame (.exception e)) = 0 := by
            unfold endFrame; cases pending.frame.kind <;>
              simp [FrameResult.gasRemaining, endCall, endCreate, UInt64.toNat_ofNat]
          have hdesc : totalGas rest (.inr (endFrame pending.frame (.exception e)))
              ≤ totalGas (pending :: rest) (.inr result) := by
            rw [totalGas_cons]; simp only [totalGas, activeGas, hz]; omega
          exact ih rest _ _ _ _ r gasOut sloadsOut callsOut h hpair (bound_mono hdesc hbound)
    | inl current =>
      dsimp only at h
      cases hstep : stepFrame current with
      | next exec =>
        rw [hstep] at h; dsimp only at h
        -- one opcode step never raises gas (`StepsTo.gas_le`); the active component drops.
        have hle : exec.gasAvailable.toNat ≤ current.exec.gasAvailable.toNat :=
          StepsTo.gas_le (stepsTo_of_next hstep)
        have hdesc : totalGas stack (.inl { current with exec := exec })
            ≤ totalGas stack (.inl current) := by
          simp only [totalGas, activeGas]; omega
        by_cases hg : isGasOp current && stack.isEmpty
        · -- a recorded top-level GAS read: `stack = []`, so `totalGas = activeGas`.
          rw [if_pos hg] at h
          have hempty : stack = [] := by
            simpa using (Bool.and_elim_right hg)
          -- the appended read `r₀ = ofUInt64 exec.gasAvailable`, `r₀.toNat = exec.gasAvailable.toNat`
          set r₀ := UInt256.ofUInt64 exec.gasAvailable with hr₀
          have hr₀nat : r₀.toNat = exec.gasAvailable.toNat := toNat_ofUInt64 exec.gasAvailable
          subst hempty
          -- the new bound = activeGas of post-step frame = r₀.toNat
          have hboundNat : totalGas [] (.inl { current with exec := exec }) = r₀.toNat := by
            simp only [totalGas, activeGas, List.map_nil, List.sum_nil, Nat.add_zero, hr₀nat]
          -- (P1)' the appended list is still Pairwise: new read ≤ every prior read
          have hpair' : (gasAcc ++ [r₀]).Pairwise geToNat := by
            rw [List.pairwise_append]
            refine ⟨hpair, List.pairwise_singleton .., fun x hx y hy => ?_⟩
            -- x ∈ gasAcc, y = r₀: need r₀.toNat ≤ x.toNat
            simp only [List.mem_singleton] at hy; subst hy
            -- x ≥ old totalGas (= current gas, stack []) ≥ exec gas = r₀.toNat
            have hxb := hbound x hx
            simp only [totalGas, activeGas, List.map_nil, List.sum_nil, Nat.add_zero] at hxb
            show r₀.toNat ≤ x.toNat
            rw [hr₀nat]; omega
          -- (P2)' the new bound ≤ every entry of the appended list
          have hbound' : ∀ x ∈ gasAcc ++ [r₀],
              totalGas [] (.inl { current with exec := exec }) ≤ x.toNat := by
            intro x hx
            rw [List.mem_append] at hx
            rcases hx with hx | hx
            · exact bound_mono hdesc hbound x hx
            · simp only [List.mem_singleton] at hx; subst hx
              rw [hboundNat]
          exact ih [] (.inl { current with exec := exec }) _ _ _ r gasOut sloadsOut callsOut h hpair' hbound'
        · -- not a recorded GAS read: `gasAcc` unchanged either way (the SLOAD branch only
          -- appends to the *sload* accumulator), bound drops by the step descent. Split the
          -- inner SLOAD `if`; both arms leave `gasAcc` fixed, so the same `ih` closes them.
          rw [if_neg hg] at h
          by_cases hsl : isSloadOp current && stack.isEmpty
          · rw [if_pos hsl] at h
            exact ih stack (.inl { current with exec := exec }) _ _ _ r gasOut sloadsOut callsOut h hpair
              (bound_mono hdesc hbound)
          · rw [if_neg hsl] at h
            exact ih stack (.inl { current with exec := exec }) _ _ _ r gasOut sloadsOut callsOut h hpair
              (bound_mono hdesc hbound)
      | halted halt =>
        rw [hstep] at h; dsimp only at h
        have hle := endFrame_gasRemaining_le hstep
        have hdesc : totalGas stack (.inr (endFrame current halt))
            ≤ totalGas stack (.inl current) := by
          simp only [totalGas, activeGas]; omega
        exact ih stack _ _ _ _ r gasOut sloadsOut callsOut h hpair (bound_mono hdesc hbound)
      | needsCall params pending =>
        rw [hstep] at h; dsimp only at h
        cases hbc : beginCall params with
        | inl child =>
          rw [hbc] at h; dsimp only at h
          have hdrop := gasFundsDescent_conj4 current params pending child stack hstep hbc
          have hdesc : totalGas (.call pending :: stack) (.inl child)
              ≤ totalGas stack (.inl current) := by
            rw [totalGas_cons]; simp only [totalGas, activeGas, Pending.savedGas] at hdrop ⊢; omega
          exact ih (.call pending :: stack) (.inl child) _ _ _ r gasOut sloadsOut callsOut h hpair
            (bound_mono hdesc hbound)
        | inr result =>
          rw [hbc] at h; dsimp only at h
          have hdrop := gasFundsDescent_conj5a current params pending result stack hstep hbc
          have hdesc : totalGas (.call pending :: stack) (.inr (.call result))
              ≤ totalGas stack (.inl current) := by
            rw [totalGas_cons]
            simp only [totalGas, activeGas, FrameResult.gasRemaining, Pending.savedGas] at hdrop ⊢
            omega
          exact ih (.call pending :: stack) (.inr (.call result)) _ _ _ r gasOut sloadsOut callsOut h hpair
            (bound_mono hdesc hbound)
      | needsCreate params pending =>
        rw [hstep] at h; dsimp only at h
        cases hbcr : beginCreate params with
        | ok child =>
          rw [hbcr] at h; dsimp only at h
          have hdrop := gasFundsDescent_conj4' current params pending child stack hstep hbcr
          have hdesc : totalGas (.create pending :: stack) (.inl child)
              ≤ totalGas stack (.inl current) := by
            rw [totalGas_cons]; simp only [totalGas, activeGas, Pending.savedGas] at hdrop ⊢; omega
          exact ih (.create pending :: stack) (.inl child) _ _ _ r gasOut sloadsOut callsOut h hpair
            (bound_mono hdesc hbound)
        | error e =>
          rw [hbcr] at h; dsimp only at h
          have hdrop := gasFundsDescent_conj5b current params pending stack hstep
          have hdesc : totalGas (.create pending :: stack)
              (.inr (.create
                { address := 0
                  createdAccounts := pending.frame.exec.createdAccounts
                  accounts := ∅
                  gasRemaining := 0
                  substate := pending.frame.exec.substate
                  success := false
                  output := .empty })) ≤ totalGas stack (.inl current) := by
            rw [totalGas_cons]
            simp only [totalGas, activeGas, FrameResult.gasRemaining, UInt64.toNat_ofNat,
              Pending.savedGas] at hdrop ⊢
            omega
          exact ih (.create pending :: stack) _ _ _ _ r gasOut sloadsOut callsOut h hpair
            (bound_mono hdesc hbound)

/-! ## `realisedGas_monotone` — the headline (`docs/ir-design-v3.md` §8)

The constructive realisability: the realised gas oracle (a *function* — `log.gas`)
is `MonotoneGas`, discharged from `driveLog_gas_inv` (which is, in turn, the same
`totalGas` gas-descent the never-OutOfFuel proof needed). The empty accumulator
trivially satisfies the invariant's two clauses, so a successful top-level
`runWithLog` hands the whole recorded gas list as a monotone-non-increasing stream. -/

/-- **`realisedGas_monotone` (`docs/ir-design-v3.md` §8).** If `runWithLog` succeeds
with log `log`, the realised gas oracle `realisedGas log = log.gas` is `MonotoneGas`
(monotone non-increasing on `.toNat`). Discharged from `driveLog_gas_inv` — the
recorded reads are the run's post-charge `gasAvailable` values, which never increase
(`StepsTo.gas_le` / the `totalGas` descents). This is constructive realisability: the
oracle is a projection of a `Type`-valued interpreter, and its law is *proved*, not
assumed. -/
theorem realisedGas_monotone {params : CallParams} {fuel : ℕ} {log : RunLog}
    (h : runWithLog params fuel = some log) : MonotoneGas (realisedGas log) := by
  unfold runWithLog at h
  -- the empty accumulator trivially satisfies the invariant's two clauses
  cases hbc : beginCall params with
  | inr result => rw [hbc] at h; simp at h
  | inl frame =>
    rw [hbc] at h; dsimp only at h
    cases hdl : driveLog fuel [] (.inl frame) [] [] [] with
    | error e => rw [hdl] at h; simp at h
    | ok triple =>
      obtain ⟨r, gas, sloads, calls⟩ := triple
      rw [hdl] at h
      simp only [Option.some.injEq] at h
      -- `log = { observable := r, gas := gas, sloads := sloads, calls := calls }`, so `realisedGas log = gas`
      have hgas : realisedGas log = gas := by rw [← h]; rfl
      obtain ⟨hpair, _⟩ := driveLog_gas_inv fuel [] (.inl frame) [] [] [] r gas sloads calls hdl
        (by simp) (by simp)
      show (realisedGas log).IsChain geToNat
      rw [hgas]
      exact hpair.isChain

/-! ## Adequacy: `runWithLog` agrees with the verified semantics (`drive`/`messageCall`)

The recording interpreter's `observable` is exactly the value the **verified** engine
computes. Lifting `driveLog_drive` (result adequacy of the parallel recorder) through
`runWithLog`'s entry: a successful `runWithLog params fuel` pins both `drive fuel`'s and
`messageCall`'s output (the latter at the same fuel — `runWithLog` takes the fuel
explicitly rather than `seedFuel`; the two coincide once `fuel = seedFuel params.gas`,
see `runWithLog_messageCall`). This is the `Type`-interpreter↔relation bridge the
lessons doc calls *adequacy* — extract from the function, reason with the relation. -/

/-- **Adequacy of `runWithLog` against `drive`.** A successful recording run pins
`drive`'s result to the recorded `observable`: the recording does not change *what* the
verified engine computes. Directly from `driveLog_drive`. -/
theorem runWithLog_drive {params : CallParams} {fuel : ℕ} {log : RunLog}
    (h : runWithLog params fuel = some log) :
    ∃ frame, beginCall params = .inl frame
      ∧ drive fuel [] (.inl frame) = .ok log.observable := by
  unfold runWithLog at h
  cases hbc : beginCall params with
  | inr result => rw [hbc] at h; simp at h
  | inl frame =>
    rw [hbc] at h; dsimp only at h
    cases hdl : driveLog fuel [] (.inl frame) [] [] [] with
    | error e => rw [hdl] at h; simp at h
    | ok triple =>
      obtain ⟨r, gas, sloads, calls⟩ := triple
      rw [hdl] at h; simp only [Option.some.injEq] at h
      subst h
      refine ⟨frame, rfl, ?_⟩
      -- `drive fuel [] frame = (driveLog …).map (·.1) = (.ok (r,…)).map (·.1) = .ok r = observable`
      have hd := driveLog_drive fuel [] (.inl frame) [] [] []
      rw [hdl] at hd
      simpa only [Except.map] using hd.symm

/-- **Adequacy of `runWithLog` against `messageCall`.** When run at the seed fuel
`seedFuel params.gas` (the budget `messageCall` itself uses), a successful recording run
pins the verified top-level boundary `messageCall params` to the recorded `observable`'s
call result. The honest tie between the instrumented interpreter and the exported
semantics. -/
theorem runWithLog_messageCall {params : CallParams} {log : RunLog}
    (h : runWithLog params (seedFuel params.gas) = some log) :
    messageCall params = .ok log.observable.toCallResult := by
  obtain ⟨frame, hbc, hd⟩ := runWithLog_drive h
  rw [messageCall_eq_drive params frame hbc, hd]
  rfl

/-! The `workedCall` instance of the `observe`-bridged conformance (`wcRunLog`,
`realisedCall_wcRunLog`, `wc_observe_conforms`) is a *leaf example* — it couples
`LirLean.WorkedCall`, which must stay OFF the headline import cone (`SimTerm` imports this
module). It therefore lives in `LirLean/V2/WorkedCallParity.lean`, built on the general
recorder defs above (`wcRunLog`, `realisedCall`, `observe`). -/

-- Build-enforced axiom-cleanliness guards: the recording interpreter's result
-- adequacy and the constructive `realisedGas_monotone` depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms driveLog_drive
#print axioms realisedGas_monotone
#print axioms sloadRecord_eq_sloadCost
#print axioms realisedCall_eq_evmV2
#print axioms runWithLog_drive
#print axioms runWithLog_messageCall
#print axioms observe

end Lir.V2
