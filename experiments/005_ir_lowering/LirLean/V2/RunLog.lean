import LirLean.V2.CallRealises
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
* on a returning external CALL (a `.inr (.call childRes)` result delivered to a
  suspended `.call pending`) it records the `(childRes, pending)` pair as a
  `CallRecord` — the minimal data from which `realisedCall` reproduces
  `evmV2CallOracle`'s `(world', success)` projection;
* it carries the run's final observable (the top-level `FrameResult`).

Because `driveLog` mirrors `drive` branch-for-branch, **result adequacy** is
`rfl`-driven by induction on fuel: `(driveLog … acc).map (·.1) = drive …`
(`driveLog_drive`).

Bytecode-coupled (references `Frame`/`drive`/`CallResult`/`evmV2CallOracle`), so it
lives here in the bridge layer, never in the frame-free `Machine.lean`/`Law.lean`.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare

-- RELOCATED from V2/Oracle.lean (Phase 2): the two defs the §7 tie-discharge layer
-- (`V2/TieDischarge.lean` — `GasLogAligned`, `FramesRun.snoc`/`.snoc_seed`,
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
              -- the realisability witness (`Runs.gasAvailable_le`)
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
              -- `beginCreate` is total (mirrors `drive`): the descent is unconditional.
              driveLog fuel (.create pending :: stack) (.inl (beginCreate params)) gasAcc sloadAcc callAcc

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
        exact ih (.create pending :: stack) (.inl (beginCreate params)) _ _ _

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
-- adequacy depends only on `[propext, Classical.choice, Quot.sound]`.
#print axioms driveLog_drive
#print axioms sloadRecord_eq_sloadCost
#print axioms realisedCall_eq_evmV2
#print axioms runWithLog_drive
#print axioms runWithLog_messageCall
#print axioms observe

end Lir.V2
