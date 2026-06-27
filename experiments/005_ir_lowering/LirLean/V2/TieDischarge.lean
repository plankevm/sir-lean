import LirLean.V2.DriveSim

/-!
# LirLean v2 — discharging the §7 *value* ties from the recorded run (`TieDischarge`)

The cyclic construction (`V2/DriveSim.lean`) still **supplies** the per-cursor §7 ties
(`SimStmtStep`/`SimTermStep` packing `GasRealises`/`SloadRealises`/`MemRealises` + the per-edge
bundles). This module banks the pieces of those ties that are **derivable** from the realised
`runWithLog`/`drive` execution, and lays the **positional-alignment foundation** the remaining
ties (GAS, SLOAD warmth) reduce to.

The three value channels split cleanly by *how much* of them is alignment-free:

* **CALL** (`realisedCall_projection`, §1) — already a clean recorded-CALL projection: when the
  log recorded a CALL, `realisedCall log self` **is** `evmV2CallOracle` at that record
  (`realisedCall_eq_evmV2`, `simp`-clean). The `o = evmV2CallOracle …` conjunct of `CallRealises`
  is therefore *discharged*, not supplied (the rest of `CallRealises` — the `Runs`/`CallReturns`
  resume-frame pins — is the structural call trace the drive walk's CALL-boundary produces, not a
  value tie). **Status: DISCHARGED (value channel).**

* **GAS** (§2) — the *arithmetic* is alignment-free and `rfl`: the recorder appends
  `UInt256.ofUInt64 exec.gasAvailable` at a top-level GAS `.next` step, where `exec` is the
  post-charge exec `gasPost current.exec`; that word is **exactly** `gasReadOf (gasFrame current)`
  (`gasRecord_eq_gasReadOf`), and `gasReadOf (gasFrame fr)` is exactly the word the `obs`-form
  `Lir.GasRealises` (`MaterialiseRuns.lean`) demands at the pre-charge frame `fr`
  (`gasReadOf_gasFrame_eq_obs`). What is **not** alignment-free is *which* recorded read pairs with
  *which* cursor: `realisedGas log = log.gas` is a flat program-order list, and the `obs`-form
  `Lir.GasRealises obs fr` (universal over every same-address frame) needs the alignment to know
  the cursor's `obs` is the matching list entry. That is Part 3 (§3). **Status: arithmetic bridge
  DISCHARGED; per-cursor selection reduced to the alignment.**

* **SLOAD** (`SloadRealises`, `MaterialiseRuns.lean`) — `sloadChg k` is the actual warmth cost at
  the SLOAD cursor. The recorder now logs the per-SLOAD warmth-charge (`RunLog.sloads`, the
  `sloadAcc` splice in `driveLog`, `realisedSload`, `sloadWarmthOf` — all in `V2/RunLog.lean`),
  with adequacy preserved by construction (`driveLog_drive` erases the new accumulator exactly like
  `gasAcc`). The value-level bridge `sloadRecord_eq_sloadCost` shows the recorded charge *is*
  `SloadRealises`'s required `sloadCost (accessedStorageKeys.contains (self, key))` — the exact
  GAS analogue (§4 below re-exposes it as `sloadRecord_discharges_obs`). **Status: arithmetic/value
  bridge DISCHARGED; per-cursor selection reduced to the alignment (same as GAS).**

* **SSTORE presence** (`SstoreRealises`'s third conjunct, `SimStmt.lean`) — `accounts.find? self =
  some acc` is **not** a dispatch gate (SSTORE reads through `.option 0`), so it cannot come from a
  step-inversion. §5 discharges it from the standalone world-wellformedness invariant `SelfPresent`
  (self account present in the frame's accounts): preserved by every materialise post-frame
  (`accounts` untouched, `rfl`) and holding at the entry `codeFrame` under world-wellformedness
  (`selfPresent_codeFrame`); the point-of-use `sstorePresence_of_self` then yields exactly the
  presence conjunct `sim_sstore` consumes at the internal SSTORE frame. **Status: world-invariant +
  point-of-use discharge DONE; `MatRuns`-threading is the remaining wiring (parallel to §3).**

## Part 3 — the positional-alignment foundation (§3)

The ties are per-cursor `(L, pc)`; the recorder logs a flat program-order list (`log.gas`). The
drive walk (`drive_step_block_*`, threading `DriveCorr` cursor-by-cursor) visits exactly those
cursors in order, and the recorder's top-level gate (`isGasOp current && stack.isEmpty`) means the
recorded reads are the **top-level** program's GAS reads in that same order.

The alignment substrate already exists frame-side: `Oracle.GasRealises T frs` (`V2/Oracle.lean`)
is the **list-level** realisability — `T = frs.map gasReadOf` (positional read-equality) together
with `FramesRun frs` (the GAS-frames `Runs`-threaded in program order). What is missing is the
bridge to the **recorder**: that `log.gas` (the `driveLog` accumulator) **is** `frs.map gasReadOf`
for the GAS-frames `frs` the drive walk visits. §3 defines that coupling (`GasLogAligned`) and
proves the **foundational per-op step**: a top-level GAS `.next` step grows the accumulator by
exactly `gasReadOf (gasFrame current)` and the witness list by `gasFrame current`, preserving
alignment (`gasLogAligned_step_gas`); a non-recording step leaves the accumulator fixed
(`gasLogAligned_step_norecord`). The remaining obstacle (reported below) is the full
walk-induction threading `GasLogAligned` through the `driveLog`/`drive` recursion alongside the
`DriveCorr` cursor — and then projecting the *list*-level `Oracle.GasRealises` back to the
*per-cursor* `obs`-form `Lir.GasRealises` at each GAS cursor.

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps
open Lir

/-! ## §1 — CALL: the recorded-CALL projection is `evmV2CallOracle` (DISCHARGED)

`realisedCall log self` is, when the log recorded a CALL, exactly `evmV2CallOracle` at that record
(`realisedCall_eq_evmV2`). So `CallRealises`'s realised-oracle conjunct `o = evmV2CallOracle …` is
produced from the recording, not supplied. We re-expose it as the named value-channel discharge. -/

/-- **CALL value-channel discharge.** With the run's recorded CALLs led by `rec`, the realised
oracle is `evmV2CallOracle rec.result rec.pending self` — the `resumeAfterCall` projection. This is
the `o = evmV2CallOracle …` conjunct of `CallRealises`, *discharged* from the recording
(`realisedCall_eq_evmV2`, `simp`-clean), not supplied. -/
theorem realisedCall_projection {log : RunLog} {rec : CallRecord} {tl : List CallRecord}
    (self : AccountAddress) (hc : log.calls = rec :: tl) :
    realisedCall log self = evmV2CallOracle rec.result rec.pending self :=
  realisedCall_eq_evmV2 self hc

/-! ## §2 — GAS: the arithmetic bridge (alignment-free, DISCHARGED)

The recorded read at a top-level GAS `.next` step and the word the per-cursor `obs`-form
`Lir.GasRealises` demands are the **same** `UInt256.ofUInt64 (gasAvailable − Gbase)`, with no
appeal to alignment — pure `gasPost`/`gasFrame` arithmetic. -/

/-- The recorded GAS word at a `current` whose GAS step is `stepFrame current = .next exec` is
exactly `gasReadOf (gasFrame current)`: the recorder appends `UInt256.ofUInt64 exec.gasAvailable`,
and for a GAS op `exec = gasPost current.exec`, so `{ current with exec := exec } = gasFrame
current` and the appended word is its `gasReadOf`. -/
theorem gasRecord_eq_gasReadOf (current : Frame) {exec : ExecutionState}
    (hdec : decode current.exec.executionEnv.code current.exec.pc = some (.Smsf .GAS, .none))
    (hsz : current.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ current.exec.gasAvailable.toNat)
    (hstep : stepFrame current = .next exec) :
    UInt256.ofUInt64 exec.gasAvailable = gasReadOf (gasFrame current) := by
  -- the GAS step is forced to be `gasPost current.exec`, so `exec.gasAvailable` is the post-charge gas.
  have hforced : stepFrame current = .next (Dispatch.gasPost current.exec) :=
    BytecodeLayer.Dispatch.stepFrame_gas current hdec hsz hgas
  rw [hstep] at hforced
  have hexec : exec = Dispatch.gasPost current.exec := (Signal.next.injEq _ _).mp hforced
  subst hexec
  rfl

/-- The word `gasReadOf (gasFrame fr)` is exactly the value the per-cursor `obs`-form
`Lir.GasRealises obs fr` demands at the **pre-charge** frame `fr`: both are
`UInt256.ofUInt64 (fr.exec.gasAvailable − UInt64.ofNat Gbase)`. So once the alignment supplies that
the GAS cursor's `obs` is this recorded read, `Lir.GasRealises obs fr` at the cursor frame is
`rfl`-discharged (the universal-over-`g` form additionally needs the alignment's
all-same-address-frames-agree fact — the §3 obstacle). -/
theorem gasReadOf_gasFrame_eq_obs (fr : Frame) :
    gasReadOf (gasFrame fr)
      = UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) := by
  rfl

/-! ## §3 — the positional-alignment foundation (Part 3, STARTED)

The coupling between the recorder's gas accumulator and the GAS-frames the drive walk visits, and
the foundational per-op step that advances both in lockstep. We reuse `Oracle.GasRealises`'s
witness shape (`T = frs.map gasReadOf ∧ FramesRun frs`) directly. -/

/-- **The gas-log alignment invariant.** A `driveLog` accumulator `gasAcc` is *aligned* with a
witness list of GAS-frames `frs` (the post-charge frames at each recorded GAS site, in program
order, `Runs`-threaded) when it is exactly their reported words. This is `Oracle.GasRealises` read
as an invariant on the recorder's accumulator: `gasAcc = frs.map gasReadOf` (positional
read-equality) together with `FramesRun frs` (the frames `Runs`-threaded). The drive walk threads
this alongside the `DriveCorr` cursor; §3's foundational steps show one op preserves it. -/
def GasLogAligned (gasAcc : List Word) (frs : List Frame) : Prop :=
  gasAcc = frs.map gasReadOf ∧ FramesRun frs

/-- The empty accumulator is aligned with the empty witness list — the drive walk's seed. -/
theorem gasLogAligned_nil : GasLogAligned [] [] := ⟨rfl, trivial⟩

/-- **`FramesRun` extends on the right by a `Runs`-reachable frame.** Appending a frame `g`
reachable (`Runs last g`) from the current last frame `last` of a non-empty `Runs`-threaded list
keeps it `Runs`-threaded. The structural step the GAS-record arm uses to grow the witness list. -/
theorem FramesRun.snoc :
    ∀ {frs : List Frame} {last g : Frame},
      FramesRun frs → frs.getLast? = some last → Runs last g → FramesRun (frs ++ [g])
  | [], _, _, _, hlast, _ => by simp at hlast
  | [a], last, g, _, hlast, hrun => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    exact ⟨hrun, trivial⟩
  | a :: b :: rest, last, g, h, hlast, hrun => by
    obtain ⟨hab, htl⟩ := h
    have hlast' : (b :: rest).getLast? = some last := by
      rw [List.getLast?_cons_cons] at hlast; exact hlast
    exact ⟨hab, FramesRun.snoc htl hlast' hrun⟩

/-- **Foundational per-op step — the GAS-record arm.** At a top-level GAS `.next` step
(`stepFrame current = .next exec`, `current.stack = []` so the recorder's `isGasOp && stack.isEmpty`
gate fires), the recorder appends one word and the witness list one frame, in lockstep:
the new accumulator `gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]` is aligned with
`frs ++ [gasFrame current]`, provided the current witness list ends at a frame from which
`current` (hence `gasFrame current`) is reachable (`Runs`-threaded). The appended word is exactly
`gasReadOf (gasFrame current)` (`gasRecord_eq_gasReadOf`), so read-equality extends; `FramesRun`
extends by `FramesRun.snoc`. -/
theorem gasLogAligned_step_gas {gasAcc : List Word} {frs : List Frame} {current : Frame}
    {exec : ExecutionState} {last : Frame}
    (halign : GasLogAligned gasAcc frs)
    (hlast : frs.getLast? = some last)
    (hreach : Runs last (gasFrame current))
    (hdec : decode current.exec.executionEnv.code current.exec.pc = some (.Smsf .GAS, .none))
    (hsz : current.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ current.exec.gasAvailable.toNat)
    (hstep : stepFrame current = .next exec) :
    GasLogAligned (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) (frs ++ [gasFrame current]) := by
  obtain ⟨hreads, hrun⟩ := halign
  refine ⟨?_, FramesRun.snoc hrun hlast hreach⟩
  -- read-equality: the appended word is `gasReadOf (gasFrame current)`.
  rw [List.map_append, ← hreads]
  simp only [List.map_cons, List.map_nil]
  rw [gasRecord_eq_gasReadOf current hdec hsz hgas hstep]

/-- **Foundational per-op step — the no-record arm.** Any step that is *not* a recorded top-level
GAS read leaves the gas accumulator (and the witness list) unchanged, so alignment is preserved
verbatim. This is the common case the walk-induction threads between GAS cursors (every non-GAS op,
and GAS reads inside a descended CALL where `stack ≠ []`). -/
theorem gasLogAligned_step_norecord {gasAcc : List Word} {frs : List Frame}
    (halign : GasLogAligned gasAcc frs) :
    GasLogAligned gasAcc frs := halign

/-! ### Projecting list-level alignment back to a per-cursor `obs` tie

`Oracle.GasRealises (frs.map gasReadOf) frs` (which `GasLogAligned gasAcc frs` packages, with
`gasAcc = frs.map gasReadOf`) is the *list*-level realisability. The §7 per-cursor tie is the
`obs`-form `Lir.GasRealises obs fr` at each GAS cursor `fr`. The bridge for a single read is
`gasReadOf_gasFrame_eq_obs`: at the GAS cursor frame, the matching list entry `gasReadOf (gasFrame
fr)` is the `obs` value the cursor tie demands. The reduction to alignment is then exactly: pick
the witness frame `frs[i]` for the `i`-th GAS cursor (the alignment's positional pairing) and read
off its `gasReadOf` as that cursor's `obs`. -/

/-- **The list→cursor read bridge.** The `i`-th entry of an aligned accumulator is the `obs` value
the §7 tie demands at the `i`-th GAS cursor frame `gasFrame fr` — i.e. `GasLogAligned`'s positional
read at a GAS site is exactly `Lir.GasRealises`'s required word there. The per-cursor tie is thus
the alignment's positional read, modulo the walk-induction that pairs cursor `i` with witness frame
`i` (the §3 obstacle). -/
theorem aligned_read_eq_obs {gasAcc : List Word} {frs : List Frame} {i : Nat} {fr : Frame}
    (halign : GasLogAligned gasAcc frs)
    (hwit : frs[i]? = some (gasFrame fr)) :
    gasAcc[i]? = some (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase)) := by
  obtain ⟨hreads, _⟩ := halign
  rw [hreads, List.getElem?_map, hwit]
  simp only [Option.map_some]
  rw [gasReadOf_gasFrame_eq_obs]

/-! ## §4 — SLOAD: the recorded warmth-charge bridges `SloadRealises` (value channel)

Piece 1 added the per-SLOAD warmth recording to the interpreter (`RunLog.sloads`,
`driveLog`'s `sloadAcc`, `realisedSload`, `sloadWarmthOf`) with adequacy preserved by
construction (`driveLog_drive` still erases every accumulator). The value-level bridge
`sloadRecord_eq_sloadCost` (`V2/RunLog.lean`) shows the recorded charge at an SLOAD frame
*is* `SloadRealises`'s required `sloadCost (accessedStorageKeys.contains (self, key))` —
the exact analogue of `gasReadOf_gasFrame_eq_obs` for GAS. So the SLOAD value channel is
now at the **same** maturity as GAS: arithmetic/value bridge DISCHARGED, per-cursor
selection reduced to the (deferred) positional alignment (`GasLogAligned`'s SLOAD twin).

We re-expose the bridge as the named SLOAD value-channel discharge and a per-cursor
reduction lemma (parallel to `aligned_read_eq_obs`): once the alignment supplies that the
SLOAD cursor's recorded charge is this site's `sloadWarmthOf`, the `sloadChg k =
sloadCost …` conjunct of `SloadRealises` is `rfl`-discharged at that frame. -/

/-- **SLOAD value-channel discharge** (parallel to `gasReadOf_gasFrame_eq_obs`). The
recorded warmth-charge `sloadWarmthOf g` at an SLOAD frame `g` whose stack-head is the
bound key is exactly `SloadRealises`'s demanded `sloadCost (accessedStorageKeys.contains
(self, key))`. This is the value the recorder now logs (Piece 1); the per-cursor tie is
its positional selection (the deferred alignment, as for GAS). -/
theorem sloadRecord_discharges_obs (g : Frame) {key : Word}
    (hkey : g.exec.stack.head? = some key) :
    sloadWarmthOf g
      = Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
          (g.exec.executionEnv.address, key)) :=
  sloadRecord_eq_sloadCost g hkey

/-! ## §5 — SSTORE: the account-presence world invariant `SelfPresent` (standalone discharge)

`SstoreRealises`'s third conjunct (`accounts.find? self = some acc`) is **not** a dispatch
gate (SSTORE reads storage through `.option 0`, so it cannot come from step-inversion). It
is a *world-wellformedness* fact: the executing (self) account is present in the frame's
accounts throughout the run. We discharge it from a standalone invariant `SelfPresent`.

`SelfPresent fr` says the self account is present in `fr`'s accounts. It holds at the entry
`codeFrame` under world-wellformedness (the called account is present — code is loaded from
it; `selfPresent_codeFrame`), and it is preserved by every materialise post-frame
(`addFrame`/`ltFrame`/`sloadFrame`/`gasFrame`/`pushFrameW` — the `.next` building blocks the
SSTORE arm's internal frame `frk` is reached through), each of which leaves `accounts`
untouched (`rfl`). The remaining wiring — threading `SelfPresent` through the
`materialise_runs`/`MatRuns` sub-runs alongside the existing clauses — is the analogue of
§3's walk-induction (reported below). The **point-of-use** discharge `sstorePresence_of_self`
turns `SelfPresent` at the SSTORE frame into exactly the presence conjunct
`SstoreRealises`/`sim_sstore` consumes there (`hsstore frk … |>.2.2`). -/

/-- **The self-account-presence world invariant.** The frame's self (executing) account is
present in its account map. The standalone wellformedness fact discharging
`SstoreRealises`'s presence conjunct (which is not a dispatch gate). -/
def SelfPresent (fr : Frame) : Prop :=
  ∃ acc : Account, fr.exec.accounts.find? fr.exec.executionEnv.address = some acc

/-- **Point-of-use SSTORE-presence discharge.** From `SelfPresent g` at the SSTORE frame
`g`, the presence conjunct `g.exec.accounts.find? g.exec.executionEnv.address = some acc`
(with `acc` the witnessed account) holds — exactly the third component `sim_sstore` reads
off `SstoreRealises` at the concrete internal frame `frk` (`hsstore frk … |>.2.2`). This is
the world-invariant discharge of the non-gate presence side-condition. -/
theorem sstorePresence_of_self {g : Frame} (h : SelfPresent g) :
    ∃ acc : Account, g.exec.accounts.find? g.exec.executionEnv.address = some acc := h

/-! ### `SelfPresent` is preserved by each materialise post-frame (the `.next` bricks)

Each materialise post-frame is `{ fr with exec := <post> }` where `<post>`
(`binOpPost`/`sloadPost`/`gasPost`/the PUSH state) touches only stack / pc / gas / substate
— **never** `accounts` (`replaceStackAndIncrPC`, `State.sload = addAccessedStorageKey`). So
both the account map and the self address are literally `fr`'s, and `SelfPresent` transports
by `rfl`. These are the per-op preservation steps the (deferred) `MatRuns`-threading composes. -/

/-- `SelfPresent` preserved across `addFrame` (`accounts`/`address` untouched). -/
theorem selfPresent_addFrame {fr : Frame} (a b : Word) (rest : Stack Word)
    (h : SelfPresent fr) : SelfPresent (addFrame fr a b rest) := h

/-- `SelfPresent` preserved across `ltFrame`. -/
theorem selfPresent_ltFrame {fr : Frame} (a b : Word) (rest : Stack Word)
    (h : SelfPresent fr) : SelfPresent (ltFrame fr a b rest) := h

/-- `SelfPresent` preserved across `sloadFrame` (SLOAD touches only `substate`/stack). -/
theorem selfPresent_sloadFrame {fr : Frame} (key : Word) (rest : Stack Word)
    (h : SelfPresent fr) : SelfPresent (sloadFrame fr key rest) := h

/-- `SelfPresent` preserved across `gasFrame`. -/
theorem selfPresent_gasFrame {fr : Frame}
    (h : SelfPresent fr) : SelfPresent (gasFrame fr) := h

/-- `SelfPresent` preserved across `pushFrameW` (PUSH touches only stack/pc/gas). -/
theorem selfPresent_pushFrameW {fr : Frame} (w : Word) (width : UInt8)
    (h : SelfPresent fr) : SelfPresent (pushFrameW fr w width) := h

/-! ### `SelfPresent` at the entry `codeFrame` (world-wellformedness)

The entry frame's accounts are `codeAccounts params` (`beginCall`'s value-transfer map) and
the self address is `params.recipient`. The recipient is present whenever the pre-call world
has it (`params.accounts.find? recipient = some _`) — the natural wellformedness assumption
(you run code *from* an existing account): the credit branch re-inserts it. (`codeAccounts`
may also create it when `value ≠ 0`; we take the present-in-`params.accounts` form, the one
a wellformed top-level call satisfies.) -/

/-- **`SelfPresent` at the entry frame** under world-wellformedness. If the called account
`params.recipient` is present in the pre-call world, it is present in the entry
`codeFrame`'s accounts (`codeAccounts` re-inserts the credited recipient), so
`SelfPresent (codeFrame params code)`. The base case of the reachability invariant. -/
theorem selfPresent_codeFrame (params : Evm.CallParams) (code : ByteArray) {acc : Account}
    (hwf : params.accounts.find? params.recipient = some acc) :
    SelfPresent (codeFrame params code) := by
  -- `SelfPresent` only needs *existence*; show the recipient lookup is `some _` after the
  -- credit (and after the caller-debit, which either overwrites at `recipient` or is `ne`).
  show ∃ a, (codeAccounts params).find? params.recipient = some a
  unfold codeAccounts
  -- the recipient was present (`hwf`), so the credit `match` reduces to the credit insert.
  simp only [hwf]
  -- reading `recipient` back after the credit insert is `some _`.
  have hrec₁ : (params.accounts.insert params.recipient
        { acc with balance := acc.balance + params.value }).find? params.recipient
      = some { acc with balance := acc.balance + params.value } :=
    accounts_find?_insert_self params.accounts params.recipient _
  -- the caller-debit `match` on `…find? caller`: `none` ⇒ the credited map; `some _` ⇒ debit insert.
  cases hcal : (params.accounts.insert params.recipient
      { acc with balance := acc.balance + params.value }).find? params.caller with
  | none => exact ⟨_, hrec₁⟩
  | some cacc =>
    -- caller-debit insert: reading `recipient` is `some _` whether caller = recipient (overwrite)
    -- or caller ≠ recipient (lookup unchanged) — case on the addresses.
    by_cases hcr : params.caller = params.recipient
    · rw [hcr]; exact ⟨_, accounts_find?_insert_self _ params.recipient _⟩
    · rw [accounts_find?_insert_of_ne _ _ (fun hc => hcr hc.symm)]
      exact ⟨_, hrec₁⟩

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the tie-discharge deliverables.
#print axioms Lir.V2.realisedCall_projection
#print axioms Lir.V2.gasRecord_eq_gasReadOf
#print axioms Lir.V2.gasReadOf_gasFrame_eq_obs
#print axioms Lir.V2.gasLogAligned_nil
#print axioms Lir.V2.FramesRun.snoc
#print axioms Lir.V2.gasLogAligned_step_gas
#print axioms Lir.V2.aligned_read_eq_obs
#print axioms Lir.V2.sloadRecord_discharges_obs
#print axioms Lir.V2.sstorePresence_of_self
#print axioms Lir.V2.selfPresent_addFrame
#print axioms Lir.V2.selfPresent_sloadFrame
#print axioms Lir.V2.selfPresent_codeFrame
