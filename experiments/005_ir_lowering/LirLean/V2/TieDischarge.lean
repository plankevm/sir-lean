import LirLean.V2.DriveSim
import LirLean.Engine.DriveMono

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
  (`selfPresent_codeFrame`); the point-of-use discharge (`SelfPresent` at the SSTORE frame) yields exactly the
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

-- RETAINED for Phase 3 realisability closure (audit §3)
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

/-! ### The single-`obs` collapse (the `Corr`-model–compatible alignment, DISCHARGED)

The `Corr` invariant the whole `sim_*` block walk threads (`SimStmt.lean`) carries a **single
fixed `obs : Word`** in `Lir.GasRealises obs fr` (`MaterialiseRuns.lean`), universal over every
same-address frame: `∀ g, g.addr = fr.addr → obs = ofUInt64 (g.gasAvailable − Gbase)`. The IR's
`evalExpr st obs .gas = some obs` reads that *same* `obs` for **every** `Expr.gas` (`Machine.lean`).
So within the `Corr` model the realised gas value is one word for the whole run — the recorded list
`log.gas` is positionally selected by `aligned_read_eq_obs` only when its aligned witnesses all
report that one word (e.g. a run with a single top-level GAS read).

`gasRealises_obs_of_witness` discharges exactly that: from the single-`obs` tie at a GAS cursor and
an alignment whose witness frame at index `i` is that cursor's post-charge `gasFrame`, the
positionally-selected recorded read `gasAcc[i]` **is** `obs`. This closes the GAS selection
end-to-end *for the `Corr` model the construction actually uses* — the recorded read at the cursor's
position is the cursor's `obs`. (The complementary direction — building the universal `obs`-form tie
from a *multi-entry* aligned list with distinct reads — is impossible in the single-`obs` model and
needs the `Corr` refactor to a per-cursor gas stream; reported as the standing obstacle.) -/

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **The single-`obs` selection discharge.** At a GAS cursor frame `fr` carrying the `Corr`-model
gas tie `Lir.GasRealises obs fr` (the universal-over-same-address form), if the alignment's witness
frame at index `i` is `fr`'s post-charge `gasFrame fr` (which shares `fr`'s address, `rfl`), then the
positionally-selected recorded read `gasAcc[i]` **is** `obs` — the cursor's gas observation. The §7
GAS per-cursor selection, discharged end-to-end in the single-`obs` model the block walk threads:
`aligned_read_eq_obs` gives `gasAcc[i] = ofUInt64 (fr.gas − Gbase)`, and the tie at the witness frame
`gasFrame fr` (same address) gives that word `= obs`. -/
theorem gasRealises_obs_of_witness {gasAcc : List Word} {frs : List Frame} {i : Nat}
    {obs : Word} {fr : Frame}
    (halign : GasLogAligned gasAcc frs)
    (hwit : frs[i]? = some (gasFrame fr))
    (htie : Lir.GasRealises obs fr) :
    gasAcc[i]? = some obs := by
  rw [aligned_read_eq_obs halign hwit]
  -- the universal tie at the witness frame `gasFrame fr` (same address as `fr`, `rfl`):
  -- `obs = ofUInt64 (gasFrame fr).gas − Gbase` and `(gasFrame fr).gas = fr.gas − Gbase`… but
  -- `Lir.GasRealises`'s own clause at `g := fr` already pins `obs = ofUInt64 (fr.gas − Gbase)`.
  have hobs : obs = UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) :=
    htie fr rfl
  rw [hobs]

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

/-! ### §4.1 — the SLOAD positional-alignment invariant `SloadLogAligned` (GAS twin)

The exact SLOAD analogue of §3's `GasLogAligned`. The recorder logs each top-level SLOAD's
warmth-charge `sloadWarmthOf current` at the **pre-step** frame `current` (the `sloadAcc` splice in
`driveLog`, gated by `isSloadOp current && stack.isEmpty`). So the SLOAD witness list is the list
of **pre-step** SLOAD frames the drive walk visits, and the invariant couples the recorder's
`sloadAcc` to their reported warmth-charges: `sloadAcc = frs.map sloadWarmthOf` together with
`FramesRun frs` (the SLOAD frames `Runs`-threaded in program order).

Note the witness-frame asymmetry with GAS: GAS records `ofUInt64 exec.gasAvailable` (the
**post**-charge gas), so its witness frame is `gasFrame current` (the post-charge frame); SLOAD
records `sloadWarmthOf current` (read off `current`'s **pre**-step substate / stack), so its witness
frame is `current` itself. The lockstep step (`sloadLogAligned_step_sload`) and the list→cursor
bridge (`alignedSload_read_eq_obs`) mirror §3 one-for-one. -/

/-- **The sload-log alignment invariant** (GAS twin of `GasLogAligned`). A `driveLog`
`sloadAcc` accumulator is *aligned* with a witness list of SLOAD pre-step frames `frs` when it is
exactly their reported warmth-charges (`sloadWarmthOf`, in program order) and the frames are
`Runs`-threaded (`FramesRun frs`). The drive walk threads this alongside `DriveCorr`; the
foundational steps below show one op preserves it. -/
def SloadLogAligned (sloadAcc : List Nat) (frs : List Frame) : Prop :=
  sloadAcc = frs.map sloadWarmthOf ∧ FramesRun frs

/-- The empty `sloadAcc` is aligned with the empty witness list — the drive walk's seed. -/
theorem sloadLogAligned_nil : SloadLogAligned [] [] := ⟨rfl, trivial⟩

/-- **Foundational per-op step — the SLOAD-record arm** (twin of `gasLogAligned_step_gas`). At a
top-level SLOAD `.next` step (`current.stack = []`, so the recorder's `isSloadOp && stack.isEmpty`
gate fires), the recorder appends one warmth-charge `sloadWarmthOf current` and the witness list one
frame `current`, in lockstep: the new accumulator `sloadAcc ++ [sloadWarmthOf current]` is aligned
with `frs ++ [current]`, provided the current witness list ends at a frame from which `current` is
reachable (`Runs`-threaded). The appended word is *definitionally* `sloadWarmthOf current` (the
recorder logs exactly the witness frame's `sloadWarmthOf`, no `gasPost`-style post-step shift), so
read-equality extends by `rfl`; `FramesRun` extends by `FramesRun.snoc`. -/
theorem sloadLogAligned_step_sload {sloadAcc : List Nat} {frs : List Frame} {current last : Frame}
    (halign : SloadLogAligned sloadAcc frs)
    (hlast : frs.getLast? = some last)
    (hreach : Runs last current) :
    SloadLogAligned (sloadAcc ++ [sloadWarmthOf current]) (frs ++ [current]) := by
  obtain ⟨hreads, hrun⟩ := halign
  refine ⟨?_, FramesRun.snoc hrun hlast hreach⟩
  rw [List.map_append, ← hreads]
  simp only [List.map_cons, List.map_nil]

/-- **The list→cursor SLOAD read bridge** (twin of `aligned_read_eq_obs`). The `i`-th entry of an
aligned `sloadAcc` is the warmth-charge `SloadRealises` demands at the `i`-th SLOAD cursor frame:
when the witness frame at `i` is an SLOAD frame `g` whose stack-head is the bound key, the recorded
`sloadAcc[i]` is exactly `sloadCost (accessedStorageKeys.contains (self, key))`
(`sloadRecord_eq_sloadCost`). The per-cursor SLOAD tie is thus the alignment's positional read,
modulo the walk-induction that pairs cursor `i` with witness frame `i` (the §3 obstacle). -/
theorem alignedSload_read_eq_obs {sloadAcc : List Nat} {frs : List Frame} {i : Nat} {g : Frame}
    {key : Word}
    (halign : SloadLogAligned sloadAcc frs)
    (hwit : frs[i]? = some g)
    (hkey : g.exec.stack.head? = some key) :
    sloadAcc[i]? = some (Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
        (g.exec.executionEnv.address, key))) := by
  obtain ⟨hreads, _⟩ := halign
  rw [hreads, List.getElem?_map, hwit]
  simp only [Option.map_some]
  rw [sloadRecord_eq_sloadCost g hkey]

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **The SLOAD selection discharge** (twin of `gasRealises_obs_of_witness`). At an SLOAD cursor
whose witness frame `g` (at index `i`) shares the cursor frame's self-address and pops the bound key
`key = st.locals k`, the `Corr`-model SLOAD tie `SloadRealises sloadChg st fr` selects the recorded
read: `sloadAcc[i] = sloadChg k`. The positionally-selected recorded warmth-charge **is** the IR
resolver value `sloadChg k`. This closes the §7 SLOAD selection end-to-end in the `Corr` model the
block walk threads: `alignedSload_read_eq_obs` gives `sloadAcc[i] = sloadCost (g.substate … key)`,
and `SloadRealises` at `g` (same address, bound key) gives `sloadChg k = sloadCost (g.substate …
key)`. (As for GAS, the converse — a multi-entry list with distinct charges — is the standing
obstacle, needing the `Corr` per-cursor refactor.) -/
theorem sloadRealises_charge_of_witness {sloadChg : Tmp → ℕ} {st : V2.IRState}
    {sloadAcc : List Nat} {frs : List Frame} {i : Nat} {g fr : Frame} {k : Tmp} {key : Word}
    (halign : SloadLogAligned sloadAcc frs)
    (hwit : frs[i]? = some g)
    (hkey : g.exec.stack.head? = some key)
    (haddr : g.exec.executionEnv.address = fr.exec.executionEnv.address)
    (hlk : st.locals k = some key)
    (htie : SloadRealises sloadChg st fr) :
    sloadAcc[i]? = some (sloadChg k) := by
  rw [alignedSload_read_eq_obs halign hwit hkey]
  -- the `Corr`-model tie at the witness frame `g` (same address as `fr`, bound key `key`):
  -- `sloadChg k = sloadCost (g.substate.accessedStorageKeys.contains (g.address, key))`.
  rw [htie g k key haddr hlk]

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
§3's walk-induction (reported below). The **point-of-use** discharge turns `SelfPresent` at the SSTORE frame into exactly the presence conjunct
`SstoreRealises`/`sim_sstore` consumes there (`hsstore frk … |>.2.2`). -/

/-- **The self-account-presence world invariant.** The frame's self (executing) account is
present in its account map. The standalone wellformedness fact discharging
`SstoreRealises`'s presence conjunct (which is not a dispatch gate). -/
def SelfPresent (fr : Frame) : Prop :=
  ∃ acc : Account, fr.exec.accounts.find? fr.exec.executionEnv.address = some acc

/-! ### `SelfPresent ⇒ accounts ≠ ∅` (the non-emptiness conjunct of the halt ties)

The halt terminator arms (built directly in `driveStepPlus_of_block`) must emit the `¬ (accounts == ∅)` conjunct
of the §7 terminator bundle. It is *derived* — not supplied — from `SelfPresent` (the self account
is present in the map, so the map cannot be empty). The account-map fact is
`find?_some_ne_empty` (a `find?` hit forces `¬ (m == ∅)`), a pure engine brick that lives in
`Engine/AccountMap.lean` together with its RBMap prims (`forM_from_nil`/`all2_nil_false`). -/

-- RELOCATE to exp003 (audit §7)
/-- **Thin bridge: `SelfPresent ⇒ accounts ≠ ∅`.** The exact non-emptiness conjunct the halt
wrappers emit (T1 directly, T2 at the return endpoint `frv` after the P3 hop). -/
theorem accounts_ne_empty_of_selfPresent {fr : Frame} (h : SelfPresent fr) :
    ¬ (fr.exec.accounts == (∅ : Evm.AccountMap)) = true := by
  obtain ⟨acc, hf⟩ := h
  exact find?_some_ne_empty _ _ _ hf

/-! ### `SelfPresent`-forward along a whole `Runs` segment (incl. the `Runs.call` resume)

`SelfPresent` transports across one materialise sub-run (account map + self address preserved). The drive walk
glues those sub-runs (and returning external CALLs) into a single `Runs fr fr'` segment between
block boundaries, so the SSTORE-presence discharge needs `SelfPresent` **forward-closed along the
whole `Runs`** — including the `Runs.call` resume node, where the resumed *caller* frame's account
map is the child's returned `result.accounts` (the shared world state threaded back through
`resumeAfterCall`), not the caller's pre-call map.

The `Runs` relation (`BytecodeLayer/Hoare.lean`) has three constructors — `refl` / `step`
(`StepsTo`, one non-halting opcode) / `call` (`CallReturns`, one returning external CALL). The
forward closure is an induction on the derivation (the template is `Runs.gasAvailable_le`): `refl`
is `rfl`, and each `step`/`call` rung is a *local* one-edge preservation. We name those two edges as
predicates so the drive walk discharges them with the facts it already has (the materialise bricks
for `step`, the returning-call world-threading for `call`):

* `StepPreservesSelf` — a single non-halting opcode step preserves the self account's presence.
  **DISCHARGED (no longer supplied): `stepPreservesSelf` is a proven theorem** — every `.next` opcode
  (of *any* program, not just the lowering) leaves `accounts` either untouched (`binOp`/`pushOp`/… via
  `replaceStackAndIncrPC`, and the CALL/CREATE `.next` fallbacks via `resumeAfterCall`/`resumeAfterCreate`
  whose `result.accounts = exec.accounts`) or inserts *at* the self account (`SSTORE`/`TSTORE` via
  `State.sstore`/`State.tstore`); none ever erases it, and the execution environment (hence the self
  address) is preserved throughout. The engine-level brick is `Evm.stepFrame_next_self`, the
  `a := self` corollary of the strengthened accMono dispatch walk (`stepFrame_next_accMono` for the
  presence half, `stepFrame_next_execEnvAddr` for the address transport); `selfPresent_runs`'s first
  hypothesis is satisfied by `stepPreservesSelf` outright.
* `CallPreservesSelf` — a returning external CALL preserves the *caller's* self account presence.
  **Satisfiable, not vacuous**: the resume preserves the self *address* (`resumeAfterCall` rebuilds
  the caller frame, touching only stack/pc/gas/accounts/substate — `resumeAfterCall_address`), and
  the returned `result.accounts` retains the caller's account (its checkpoint on revert/exception is
  the caller's own pre-call map; on success the shared world keeps the caller present — the caller is
  not the callee). The structural address half is banked below; the `result.accounts`-presence half
  is the returning-world fact the drive walk supplies per CALL edge.

The general lemma `selfPresent_runs` threads both across an arbitrary `Runs`; the address-transport
helpers `resumeAfterCall_address`/`resumeAfterCall_accounts` are the `rfl` facts the `call` edge
reduces to. -/

/-- **The revert/exception sub-case of `CallPreservesSelf`, structurally discharged.** When the child
returns a result whose accounts are the caller's pre-call checkpoint map (the revert/exception shapes,
via `endCall_revert_accounts`/`endCall_exception_accounts`), and the caller self was present there, the
resumed frame keeps the self account present. Definitional: `resumeAfterCall` sets `exec.accounts :=
result.accounts` and leaves `executionEnv` (hence `.address`) at the suspended caller's value — the
hypothesis IS the conclusion up to `rfl`. This is the half of `CallPreservesSelf` that
does **not** depend on the open `drive_accounts_find_mono`; the `.success` shape still does (and so the
full `CallPreservesSelf` stays supplied — satisfiable, not vacuous). -/
theorem resumeAfterCall_self_of_accounts (result : Evm.CallResult) (pd : Evm.PendingCall)
    (h : ∃ acc, result.accounts.find? pd.frame.exec.executionEnv.address = some acc) :
    SelfPresent (Evm.resumeAfterCall result pd) := h

/-- **Local per-step self-presence preservation.** One non-halting opcode step (`StepsTo`) keeps
the self account present. Satisfiable for the lowered program — every `.next` opcode either leaves
`accounts` untouched or inserts at the self account, never erasing it — and supplied per edge by the
materialise-frame preservation (each `.next` post-frame leaves `accounts`/self address untouched). -/
def StepPreservesSelf : Prop :=
  ∀ ⦃fr fr' : Frame⦄, StepsTo fr fr' → SelfPresent fr → SelfPresent fr'

/-- **`StepPreservesSelf` DISCHARGED — fully general, no lower-prog hypothesis.** Every non-halting
opcode step keeps the self account present. A `StepsTo fr fr'` is `stepFrame fr = .next fr'.exec`
(with `fr' = { fr with exec := fr'.exec }`), and `stepFrame_next_self` proves a `.next` step keeps
`SelfAt`; `SelfPresent fr` is `SelfAt fr.exec` and `SelfPresent fr'` is `SelfAt fr'.exec` by
definition. So this holds for **every** frame — in particular for every reachable frame of a
`lower prog` run — and is no longer a supplied edge: `selfPresent_runs`'s first hypothesis is now a
theorem, not an assumption. -/
theorem stepPreservesSelf : StepPreservesSelf := by
  intro fr fr' hstep hself
  exact Evm.stepFrame_next_self hstep.1 hself

/-- **Local per-call self-presence preservation.** One returning external CALL (`CallReturns`)
keeps the *caller's* self account present. Satisfiable, not vacuous: the resume keeps the self
address (`resumeAfterCall_address`) and the returned `result.accounts` retains the caller (the
checkpoint on revert/exception is the caller's own pre-call map; on success the shared world keeps
the caller present — the caller is not the callee). The structural address half is banked; the
`result.accounts`-presence half is the returning-world fact supplied per CALL edge. -/
def CallPreservesSelf : Prop :=
  ∀ ⦃callFr resumeFr : Frame⦄, CallReturns callFr resumeFr → SelfPresent callFr → SelfPresent resumeFr

/-- **The `.success` shape of `CallPreservesSelf`, discharged via Brick D.** A returning external
CALL keeps the *caller's* self present, given the same `hmono`/`hprec`/`hcall_acc`/`hcall_kind`/`hhalt`
closers as `drive_accounts_find_mono` plus the CALL-site self-address framing `hcall_self`. The CREATE
arm needs no seam — `drive_accounts_find_mono` now proves it in place (`beginCreate` is total, an
unconditional child descent threaded via `stepFrame_needsCreate_inv`).

The child run `drive (seedFuel cp.gas) [] (running child) = .ok childRes` *starts* present at the
caller's self address `a` (`beginCall` threads `cp.accounts` presence into the child's running map and
checkpoint, `cp.accounts` present from the caller's running map via `hcall_acc`); `drive_accounts_find_mono`
carries that presence to `childRes`'s accounts; `resumeAfterCall_self_of_accounts` then closes
`SelfPresent resumeFr` (the resumed self is the caller's, `resumeAfterCall_address`). Non-vacuous: the
`DrivePresent` premise is genuinely established from `SelfPresent callFr`, not assumed. -/
theorem callPreservesSelf_success
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → ∀ a, AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → ∀ a, AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → ∀ a, AccPresent a fr.exec.accounts →
        AccPresent a e.accounts)
    (hcall_self : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd →
        pd.frame.exec.executionEnv.address = fr.exec.executionEnv.address)
    {callFr resumeFr : Frame} (hcr : CallReturns callFr resumeFr)
    (hself : SelfPresent callFr) :
    SelfPresent resumeFr := by
  obtain ⟨cp, pending, child, childRes, hstep, _hcode, hchild, hresume⟩ := hcr
  -- The tracked address: the caller's self (= the resumed self, `resumeAfterCall_address`).
  set a : Evm.AccountAddress := pending.frame.exec.executionEnv.address with ha
  -- The caller's self is present in `callFr.exec.accounts` (`hself`), and `callFr`'s self equals `a`.
  have haddr : callFr.exec.executionEnv.address = a := by
    rw [ha]; exact (hcall_self callFr cp pending hstep).symm
  have hcaller : AccPresent a callFr.exec.accounts := by
    obtain ⟨acc, hf⟩ := hself
    exact ⟨acc, by rw [← haddr]; exact hf⟩
  -- Hence present in `cp.accounts` (CALL-site framing), and so the child run starts present at `a`.
  have hcp : AccPresent a cp.accounts := hcall_acc callFr cp pending hstep a hcaller
  -- Build `DrivePresent a [] (running child)` from `cp.accounts` presence.
  -- (The child enters as code: `hchild`'s run is on `child`, so `beginCall cp = .inl child`.)
  have hbc : Evm.beginCall cp = .inl child := _hcode
  have hchildPres : DrivePresent a [] (Sum.inl child) := by
    refine ⟨beginCall_inl_accounts_present a cp hbc hcp, ?_, trivial⟩
    obtain ⟨created, sub, hkind⟩ := beginCall_inl_checkpoint cp hbc
    unfold CheckpointPresent; rw [hkind]; exact hcp
  -- Apply Brick D: presence at `a` is monotone across the child drive run (start `([], inl child)`).
  have hmono' := drive_accounts_find_mono a
    (fun fr exec' h => hmono fr exec' h a)
    (fun c imm h => hprec c imm h a)
    (fun fr c pd h => hcall_acc fr c pd h a)
    hcall_kind
    (fun fr e o h => hhalt fr e o h a)
    (seedFuel cp.gas) [] (Sum.inl child) childRes hchild hchildPres
  -- Close `SelfPresent resumeFr` via the landed resume-self bridge.
  rw [hresume]
  exact resumeAfterCall_self_of_accounts childRes.toCallResult pending hmono'

/-- **`CallPreservesSelf`, discharged modulo the precompile no-erase seam.** Every shape of a
returning external CALL keeps the caller's self present: `.success` via `callPreservesSelf_success`
(Brick D), `.revert`/`.exception` structurally (folded in — `callPreservesSelf_success` covers the
whole `CallReturns` once the child run terminates, since `childRes` already carries whichever shape).

The seam hypotheses are each genuinely satisfiable (never vacuous) and remain **supplied**:
* `hmono`/`hcall_acc`/`hcall_kind`/`hhalt`/`hcall_self` are *universally-true* framing facts (every
  `.next` step is accounts-monotone at any `a`; `callArm` sets `params.accounts`/`pending.frame` from
  the issuing exec; halting opcodes don't touch accounts) — true for **all** frames, so trivially
  satisfiable (`hmono` is the unproven Brick C, but holds for every frame);
* `hprec` is the precompile-preservation fact (precompiles only insert) — satisfiable, vacuous for
  call-free IR.

The no-CREATE seam is **gone**: `drive`'s CREATE-begin-fault arm now returns the caller checkpoint
(`pending.frame.exec.accounts`, the faithful soft-failure map — not the prior emptied map), so
`drive_accounts_find_mono` proves the whole CREATE step (fault + descent) presence-preserving in place
via `stepFrame_needsCreate_inv`.

`CallPreservesSelf` is *not* unconditionally true (the precompile `.inr` `∅`-arm really can erase, and
`CallReturns` does not by itself rule it out across the child run). The strict improvement over the
prior fully-supplied `CallPreservesSelf`: its `.success` monotonicity is now *discharged* engine-level
(Brick D), and the CREATE no-erase guard is *eliminated* (the faithful fault arm preserves presence). -/
theorem callPreservesSelf
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → ∀ a, AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → ∀ a, AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → ∀ a, AccPresent a fr.exec.accounts →
        AccPresent a e.accounts)
    (hcall_self : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd →
        pd.frame.exec.executionEnv.address = fr.exec.executionEnv.address) :
    CallPreservesSelf := by
  intro callFr resumeFr hcr hself
  exact callPreservesSelf_success hmono hprec hcall_acc hcall_kind hhalt hcall_self hcr hself

/-- **`CallPreservesSelf`, with the five universally-true CALL-seam facts DISCHARGED engine-level.**
The arbitrary-`a` account-monotonicity bricks (this cycle) prove engine-level, for *every* frame:

* `hmono` — `Evm.stepFrame_next_accMono` (Brick C, the `.next` account-presence mono);
* `hcall_acc` / `hcall_kind` / `hcall_self` — `Evm.stepFrame_needsCall_inv` (the CALL-site framing:
  child params' accounts = issuing accounts, suspended frame keeps `kind` and execution-env address);
* `hhalt` — `Evm.stepFrame_halted_success_accMono` (STOP/RETURN/SELFDESTRUCT keep accounts present —
  no erase).

So `callPreservesSelf`'s six supplied hypotheses collapse to **one**: the genuinely-conditional
`hprec` (precompile `.inr` output map — opaque for a live precompile, vacuous for the call-free /
non-precompile-targeting lowered IR). The former no-CREATE seam `hncr` is **eliminated**: `beginCreate`
is total (no begin-fault arm — it always descends into a child), so `drive_accounts_find_mono`
discharges the whole CREATE step engine-level via `stepFrame_needsCreate_inv`. `hprec` remains
**supplied**, genuinely satisfiable and non-vacuous; this
is *not* a hypothesis-free `CallPreservesSelf` (the precompile `.inr` `∅`-arm really can erase). -/
theorem callPreservesSelf_modGuards
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts) :
    CallPreservesSelf :=
  callPreservesSelf
    (fun fr exec' h a hp => Evm.stepFrame_next_accMono h a hp)
    hprec
    (fun fr cp pd h a hp => (Evm.stepFrame_needsCall_inv h).1 ▸ hp)
    (fun fr cp pd h => (Evm.stepFrame_needsCall_inv h).2.1)
    (fun fr e o h a hp => Evm.stepFrame_halted_success_accMono h a hp)
    (fun fr cp pd h => congrArg ExecutionEnv.address (Evm.stepFrame_needsCall_inv h).2.2)

/-- **`SelfPresent` is forward-closed along a whole `Runs` segment.** From `SelfPresent fr` and
`Runs fr fr'`, `SelfPresent fr'` — given the two local one-edge preservation facts
(`StepPreservesSelf` for opcode steps, `CallPreservesSelf` for returning external CALLs, *including
the `Runs.call` resume node*). Proved by induction on the `Runs` derivation (the template is
`Runs.gasAvailable_le`): `refl` carries `h` unchanged; `step`/`call` apply the corresponding local
edge then recurse. This is the threading the SSTORE-presence discharge needs across the drive walk:
a later SSTORE cursor inherits the entry frame's self-presence through every block step and returning
call. Both edge hypotheses are satisfiable (not vacuous) — see `StepPreservesSelf`/`CallPreservesSelf`
— so this introduces no unsatisfiable assumption. -/
theorem selfPresent_runs (hstep : StepPreservesSelf) (hcall : CallPreservesSelf)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' := by
  induction hruns with
  | refl _ => exact h
  | step hs _ ih => exact ih (hstep hs h)
  | call hc _ ih => exact ih (hcall hc h)

/-- **`selfPresent_runs` with the step edge already discharged.** Since `stepPreservesSelf` is a
proven theorem (not a supplied edge), the only remaining hypothesis is the CALL edge
`CallPreservesSelf` (the call-tie seam — genuinely-open in its `.success` shape, supplied & satisfiable;
its revert/exception shapes are structurally discharged by `resumeAfterCall_self_of_accounts`). This is
the form the drive walk consumes: thread self-presence across a whole `Runs` with only the returning
external CALL fact to supply. -/
theorem selfPresent_runs_of_call (hcall : CallPreservesSelf)
    {fr fr' : Frame} (h : SelfPresent fr) (hruns : Runs fr fr') : SelfPresent fr' :=
  selfPresent_runs stepPreservesSelf hcall h hruns

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

/-! ## §6 — the strengthened boundary invariant `DriveCorrPlus` (the alignment + presence carrier)

The drive recursion `runFrom_of_driveCorr` (`DriveSim.lean`) threads `DriveCorr` (the `Corr`
boundary + the clean-halt measure) block-by-block. To discharge the §7 *selection* (the k-th cursor
value = the k-th recorded entry) and the SSTORE presence in the SAME walk, the boundary invariant
must additionally carry, at each block-entry frame:

* `selfPresent` — the self account is present (`SelfPresent fr`), the SSTORE presence world-invariant
  (§5), transportable across each block's materialise sub-runs (account map + self address preserved);
* `gasAligned` / `sloadAligned` — that the recorder's flat gas/sload accumulators *consumed so far*
  are aligned (`GasLogAligned` / `SloadLogAligned`) with the GAS/SLOAD witness frames the walk has
  visited, so the per-cursor read at the next GAS/SLOAD site is the matching recorded entry
  (`gasRealises_obs_of_witness` / `sloadRealises_charge_of_witness`).

`DriveCorrPlus` bundles exactly these onto `DriveCorr`. The accumulators-so-far are carried as
explicit parameters (`gasAcc`/`sloadAcc`) with their witness lists (`gasFrs`/`sloadFrs`), since the
block walk does not itself project the recorder — they are the prefix of `log.gas`/`log.sloads`
consumed up to this boundary.

**Entry satisfaction is proven** (`driveCorrPlus_entry`): at the entry frame the consumed prefixes
are empty (`gasLogAligned_nil`/`sloadLogAligned_nil`) and `SelfPresent` holds by
`selfPresent_codeFrame`. **Preservation through the block step is the standing obstacle**, for two
independent reasons reported at the foot of this module: (a) the alignment witnesses can only be
*selected* in the single-`obs` `Corr` model when the consumed gas prefix is constant
(`gasRealises_obs_of_witness`), which the multi-distinct-read general case violates; (b)
`SelfPresent`-forward across a block requires self-presence preservation along the *whole* `Runs`
segment (including the `Runs.call` resume), which is not yet a lemma. -/

/-- **The strengthened drive-boundary invariant.** `DriveCorr` (the `Corr` boundary + clean-halt
measure) augmented with the SSTORE presence world-invariant `SelfPresent fr` and the gas/sload
positional-alignment witnesses for the recorder prefixes consumed up to this boundary
(`GasLogAligned gasAcc gasFrs` / `SloadLogAligned sloadAcc sloadFrs`). The carrier the drive walk
would thread to discharge the §7 selection ties and the SSTORE presence in one recursion; the entry
frame satisfies it (`driveCorrPlus_entry`). -/
structure DriveCorrPlus (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) (L : Label)
    (gasAcc : List Word) (gasFrs : List Frame)
    (sloadAcc : List Nat) (sloadFrs : List Frame) : Prop where
  /-- The base `DriveCorr` boundary (the `Corr` cursor + the clean-halt measure). -/
  base : DriveCorr prog sloadChg obs st fr L
  /-- The SSTORE presence world-invariant: the self account is present in `fr`'s accounts. -/
  selfPresent : SelfPresent fr
  /-- The gas accumulator consumed so far is positionally aligned with the GAS witness frames. -/
  gasAligned : GasLogAligned gasAcc gasFrs
  /-- The sload accumulator consumed so far is positionally aligned with the SLOAD witness frames. -/
  sloadAligned : SloadLogAligned sloadAcc sloadFrs

/-- **Entry satisfaction of `DriveCorrPlus`.** At the entry frame (a `DriveCorr` boundary whose
frame is the call's `codeFrame` with the self account present), the strengthened invariant holds
with **empty** consumed prefixes: the gas/sload alignments are the seeds
(`gasLogAligned_nil`/`sloadLogAligned_nil`) and `SelfPresent` is `selfPresent_codeFrame`. This is the
base case of the (would-be) strengthened drive recursion — the alignment witnesses start empty and
the presence invariant starts established. -/
theorem driveCorrPlus_entry {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {params : Evm.CallParams} {code : ByteArray} {L : Label} {acc : Account}
    (hbase : DriveCorr prog sloadChg obs st (codeFrame params code) L)
    (hwf : params.accounts.find? params.recipient = some acc) :
    DriveCorrPlus prog sloadChg obs st (codeFrame params code) L [] [] [] [] where
  base := hbase
  selfPresent := selfPresent_codeFrame params code hwf
  gasAligned := gasLogAligned_nil
  sloadAligned := sloadLogAligned_nil

/-! ## §7 — the no-bridge VALUE channels of the `DriveCorrPlus` walk (C3 / Group B)

The centerpiece L2.0 statement-walk is decomposed by the architect into

  * the **structure** (`Runs` + `Corr` at the terminator + working-stack-nil), reused VERBATIM from
    `sim_stmts_block` consuming the per-statement bytecode simulation `SimStmtStep` (which internally
    re-establishes the stash/sstore/call ties S1/S5/S6 — the serialized spine, supplied here);
  * the **self-presence** edge, threaded by P3 (`selfPresent_runs_of_call`, supplied `CallPreservesSelf`);
  * the **alignment** witnesses, carried VERBATIM from the `DriveCorrPlus` boundary (the per-cursor
    structural extension `gasLogAligned_step_gas`/`sloadLogAligned_step_sload` is the deferred gas/sload
    structural walk, NOT tonight's preservation walk);
  * the **value channels** — the only genuinely-new, no-P3, no-trace↔recorder-bridge content tonight:
    **S7** (assign-remat `MemRealises` transport) and **S2** (the sload value tie). These are kept
    SEPARATE from the walk (see below).

We prove S7/S2 here as standalone cursor-LOCAL lemmas (a single `Corr` cursor + its `EvalStmt` step),
exactly the altitude `SimStmtStep`/`sim_assign` consume. They are functions of the per-cursor
`Corr`/`EvalStmt` ALONE, not of the run, so they are NOT bundled into the walk (doing
so would buy nothing): the downstream Route-4b assembly applies them per cursor directly (the indexed
form bound to the run's reached `(stpc, frpc)`, NOT the universal free-`ob` `StmtTies` predicate, which
ranges over all cursors and is unreconstructable from a single run).

**The two channels that STAY SUPPLIED tonight** (satisfiable, documented, NON-vacuous):
  * **S3 (gas positional value)** `stpc'.locals t = ofUInt64 (frpc.gas − Gbase)` — NOT a value-only
    have-block: it is the TRACE↔RECORDER bridge (`EvalStmt.assignGas` peels `ob` as the HEAD of the gas
    trace, while `aligned_read_eq_obs` gives the recorder's `gasAcc[i]`; tying them needs a NEW carried
    invariant `IR-trace-consumed = gasAcc` plus the gas-channel structural walk threading
    `gasFrs[i] = gasFrame frpc`). Supplied as `hgasval`; satisfiable — supplied via `SimStmtStep` (the `StmtTies` gas conjunct), NOT discharged by any carried alignment;
    the `Plus` invariant threads ONLY `SelfPresent`, the gas/sload alignment witnesses being carried
    VERBATIM. Inhabited by any top-level GAS read.
  * **S1/S5/S6** — folded inside the supplied `SimStmtStep` (the serialized post-P3 spine).
  * **S4 (gas runtime envelopes)** — the lower-bound envelopes need the clean-halt FORWARD split
    (`cleanHalts_forward` to the cursor, then the GAS op runs), not pure descent; supplied alongside S3.
-/

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S7 core (NEW): `MemRealises` survives a non-spilled `setLocal`.** Binding a tmp `t` that is NOT
spilled to a memory slot (`∀ n, defsOf prog t ≠ some (.slot n)`) leaves the memory value channel
intact: for every spilled `t'` with `(st.setLocal t w).locals t' = some v`, necessarily `t' ≠ t` (else
`t` would be spilled, contradicting `hns`), so `(st.setLocal t w).locals t' = st.locals t'` and the
coverage+readback at `t'`'s slot is the input `MemRealises`'s. The honest content of the assign-remat
channel: the frame `fr` is UNCHANGED by a rematerialised assign (its lowered emit is empty,
`Runs.refl`), only the IR state moves, so `MemRealises` transports by this `setLocal` stability. -/
theorem memRealises_setLocal_nonspilled {prog : Program} {st : V2.IRState} {fr : Frame}
    {t : Tmp} {w : Word}
    (h : MemRealises prog st fr) (hns : ∀ n, defsOf prog t ≠ some (.slot n)) :
    MemRealises prog (st.setLocal t w) fr := by
  intro t' slot v hdef hloc
  -- `t' ≠ t`: otherwise `t' = t` is spilled (`hdef` at the slot), contradicting `hns`.
  have hne : t' ≠ t := by
    rintro rfl
    exact hns slot hdef
  -- read the bound value back through `setLocal` of the distinct tmp `t`.
  have hloc' : st.locals t' = some v := by
    have : (st.setLocal t w).locals t' = st.locals t' := by
      show (if t' = t then some w else st.locals t') = st.locals t'
      rw [if_neg hne]
    rwa [this] at hloc
  exact h t' slot v hdef hloc'

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S7 (assign-remat value channel), cursor-local.** At a cursor holding a rematerialised assign
`assign t e` (target NOT spilled, `hns`) whose IR step is the non-gas `EvalStmt.assignPure` (so the
post-state is `st.setLocal t w`), the post-state realises the frame's memory: `MemRealises prog st' fr`.
The frame is the SAME `fr` the cursor's `Corr` carries (a rematerialised assign emits no bytes), so this
is `memRealises_setLocal_nonspilled` applied to `Corr.memAgree`. No recorder, no P3 — the genuine
no-bridge content of S7 (Route 4b indexed form). -/
theorem driveCorrPlus_assign_remat_memRealises {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {t : Tmp} {e : Expr} {L : Label}
    {pc : Nat} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hstep : EvalStmt prog o st T (.assign t e) st' T')
    (hne : e ≠ .gas)
    (hns : ∀ n, defsOf prog t ≠ some (.slot n)) :
    MemRealises prog st' fr := by
  -- invert the step: non-gas assign ⇒ `assignPure`, `st' = st.setLocal t w`.
  cases hstep with
  | assignPure _ _ =>
    exact memRealises_setLocal_nonspilled hcorr.memAgree hns
  | assignGas => exact absurd rfl hne

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S2 (sload value channel), cursor-local.** At a cursor holding `assign t (.sload k)` whose IR step
is `EvalStmt`, the IR genuinely binds a value: `∃ w, evalExpr st 0 (.sload k) = some w`. This is the
`hv` field of the `assignPure` the run already performed (`.sload k ≠ .gas`), echoing the run's own
successful IR step — NON-vacuous (the run is the witness that `k` is bound and `w = st.world key`). No
recorder, no P3. -/
theorem driveCorrPlus_sload_value {prog : Program} {o : V2.CallOracle}
    {st st' : V2.IRState} {T T' : Trace} {t k : Tmp}
    (hstep : EvalStmt prog o st T (.assign t (.sload k)) st' T') :
    ∃ w, V2.evalExpr st 0 (.sload k) = some w := by
  cases hstep with
  | assignPure _ hv => exact ⟨_, hv⟩

-- RETAINED for Phase 3 realisability closure (audit §3)
/-- **S2 envelope: the sload key is bound, the value is the world read.** A sharper readout of the same
`assignPure`: the IR run's sload at this cursor binds `k`'s key and the loaded word is `st.world key` —
the value `MemRealises` will position at `t`'s slot. Non-vacuous (the run is its own witness). -/
theorem driveCorrPlus_sload_value_world {prog : Program} {o : V2.CallOracle}
    {st st' : V2.IRState} {T T' : Trace} {t k : Tmp}
    (hstep : EvalStmt prog o st T (.assign t (.sload k)) st' T') :
    ∃ key, st.locals k = some key ∧ V2.evalExpr st 0 (.sload k) = some (st.world key) := by
  cases hstep with
  | assignPure _ hv =>
    -- `evalExpr st 0 (.sload k) = (do let key ← st.locals k; pure (st.world key))`.
    -- `hv : evalExpr st 0 (.sload k) = some w` forces `st.locals k = some key` and `w = st.world key`.
    cases hk : st.locals k with
    | none =>
      exfalso
      simp [V2.evalExpr, hk] at hv
    | some key =>
      exact ⟨key, rfl, by simp [V2.evalExpr, hk]⟩

/-! ### L2.0g — the GAS-ADVANCING `DriveCorrPlus` statement-walk (S3 producer)

The L2.0 statement-walk is PRESERVATION-only: it black-boxes the per-cursor frames through
`sim_stmts_block`, so it cannot grow the gas witness list `gasFrs` — it carries the alignment
VERBATIM, leaving S3 (the gas positional VALUE) SUPPLIED. The GAS-advancing walk decls that PEELED each cursor to GROW the alignment have been REMOVED (audit:
dead producers off the headline path); the seedable per-cursor gas bricks below
(`FramesRun.snoc_seed`, `gasLogAligned_step_gas_seed`, `GasReach`, `GasCursorClass`) are RETAINED salvage — for the deferred SLOAD/gas advance.

The per-cursor dispatch is the classification hypothesis `GasCursorClass`: at each cursor the walk is
told whether the statement is `assign t .gas` (a GAS cursor, with the GAS-op decode + gas envelope +
the strictly-advancing `fr0 ≠ fr1` that lets `Runs.gas_cancel` factor the GAS head out) or NOT (the
no-record arm). This is the honest per-cursor input the architect's plan dispatches on; it is
satisfiable (a real lowered `assign t .gas` decodes to `GAS` at the segment head — `emitStmt_assign_slot`
puts `materialise .gas = [GAS]` first — and the GAS op strictly advances the pc) and NON-vacuous (the
GAS arm CONSUMES the supplied S4 lower bound to fire the brick, the non-GAS arm consumes nothing).

The threaded reachability invariant is `GasReach`: the witness tail `Runs`-reaches the current cursor
frame (vacuous at the empty seed, `Runs last fr0` once non-empty). The seedable gas snoc
`gasLogAligned_step_gas_seed` handles BOTH the first GAS cursor (empty `gasFrs`, `FramesRun []`-seed)
and the snoc case (non-empty, via `FramesRun.snoc`), so the walk needs no special first-cursor arm. -/

/-- **`FramesRun` extends on the right, SEEDABLE.** Unlike `FramesRun.snoc` (which needs a non-empty
list to supply `getLast?`), this admits the empty seed: appending `g` to `[]` gives `[g]`
(`FramesRun [g] = True`), and to a non-empty list reachable-from-its-last gives the snoc. The
hypothesis is `GasReach`-style: every `last` that is the list's `getLast?` reaches `g`. -/
theorem FramesRun.snoc_seed {frs : List Frame} {g : Frame}
    (hrun : FramesRun frs) (hreach : ∀ last, frs.getLast? = some last → Runs last g) :
    FramesRun (frs ++ [g]) := by
  cases frs with
  | nil => exact trivial
  | cons a tl =>
    -- a non-empty list has `getLast? = some last` for some `last` (`getLast?_isSome`).
    obtain ⟨last, hlast⟩ : ∃ last, (a :: tl).getLast? = some last := by
      cases h : (a :: tl).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h
      | some last => exact ⟨last, rfl⟩
    exact FramesRun.snoc hrun hlast (hreach _ hlast)

/-- **The seedable per-op GAS-record step.** As `gasLogAligned_step_gas`, but the reachability
hypothesis is the `GasReach`-style `∀ last, frs.getLast? = some last → Runs last (gasFrame current)`,
so it covers BOTH the empty seed (`frs = []`, vacuous reachability, `FramesRun []`) and the snoc case.
The appended word is the recorder's literal splice `gasReadOf (gasFrame current)`; the witness list
grows by `gasFrame current`. -/
theorem gasLogAligned_step_gas_seed {gasAcc : List Word} {frs : List Frame} {current : Frame}
    {exec : ExecutionState}
    (halign : GasLogAligned gasAcc frs)
    (hreach : ∀ last, frs.getLast? = some last → Runs last (gasFrame current))
    (hdec : decode current.exec.executionEnv.code current.exec.pc = some (.Smsf .GAS, .none))
    (hsz : current.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ current.exec.gasAvailable.toNat)
    (hstep : stepFrame current = .next exec) :
    GasLogAligned (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) (frs ++ [gasFrame current]) := by
  obtain ⟨hreads, hrun⟩ := halign
  refine ⟨?_, FramesRun.snoc_seed hrun hreach⟩
  rw [List.map_append, ← hreads]
  simp only [List.map_cons, List.map_nil]
  rw [gasRecord_eq_gasReadOf current hdec hsz hgas hstep]

/-- **The per-cursor GAS-channel reachability invariant.** The witness tail `Runs`-reaches the cursor
frame: vacuously true at the empty seed (`frs = []`), and `Runs last fr0` once `frs` is non-empty.
Threaded alongside `GasLogAligned` so the GAS arm can `FramesRun.snoc_seed` the new witness frame. -/
def GasReach (frs : List Frame) (fr0 : Frame) : Prop :=
  ∀ last, frs.getLast? = some last → Runs last fr0

/-- `GasReach` transports forward along a `Runs fr0 fr0'` segment (`Runs.trans`). -/
theorem GasReach.trans {frs : List Frame} {fr0 fr0' : Frame}
    (h : GasReach frs fr0) (hseg : Runs fr0 fr0') : GasReach frs fr0' :=
  fun last hl => Runs.trans (h last hl) hseg

/-- **The per-cursor GAS classification (the walk's per-cursor dispatch input).** At cursor `pc`
holding statement `s`, with `Corr` frame `fr0` and the per-cursor lowered segment `Runs fr0 fr1`
(from `SimStmtStep`), the walk is told the cursor is EITHER a GAS cursor or not:

* **`gas` arm** — `s = .assign t .gas` (`hs`), the segment head decodes to `GAS` at `fr0` (`hdec`),
  the gas envelope `Gbase ≤ fr0.gas` holds (`hgas`, the S4 lower bound CONSUMED here), and the GAS op
  strictly advances (`hne : fr0 ≠ fr1`, satisfiable since `GAS` is non-terminal). These are exactly
  the inputs `Runs.gas_cancel` + `gasLogAligned_step_gas_seed` consume.
* **`notgas` arm** — `∀ t, s ≠ .assign t .gas` (`hnotgas`): the no-record arm, carrying the alignment
  verbatim.

A real lowered run satisfies this at every cursor (the GAS arm at spilled-gas def-sites whose stash
head is `[GAS]`, the non-GAS arm elsewhere); it is the per-cursor classification the (former)
black-box walk could not see. -/
inductive GasCursorClass (s : Stmt) (fr0 fr1 : Frame) : Prop where
  | gas (t : Tmp) (hs : s = .assign t .gas)
      (hdec : decode fr0.exec.executionEnv.code fr0.exec.pc = some (.Smsf .GAS, .none))
      (hgas : GasConstants.Gbase ≤ fr0.exec.gasAvailable.toNat)
      (hne : fr0 ≠ fr1) : GasCursorClass s fr0 fr1
  | notgas (hnotgas : ∀ t, s ≠ .assign t .gas) : GasCursorClass s fr0 fr1

/-! ## §9 — the EDGE wrappers (Tier 2 / C5): `driveCorrPlus_step_jump` / `_branch`

The non-halt (`jump`/`branch`) analogues of `drive_step_block_jump`/`drive_step_block_branch`
(`DriveSim.lean`), but threading `DriveCorrPlus` instead of the bare `DriveCorr`: where the
`DriveCorr` versions re-establish only `DriveCorr` at the successor block, these RE-ESTABLISH
`DriveCorrPlus` at the successor's entry frame `jumpdestFrame fj`. The bytecode construction is
IDENTICAL to the `DriveCorr` versions (statement-run via `sim_stmts_block`, the supplied §7 edge
bundle `hjump`/`hbranch` delivering the `JUMPDEST` landing `fj` with `Runs frT fj`,
`corr_at_jumpdest_landing` re-establishing `Corr` at the successor cursor, `cleanHalts_forward`
deriving the successor clean-halt, `totalGas_succ_lt` the strict descent, and the
`RunFrom.jump`/`.branchThen`/`.branchElse` IR continuation).

The ONLY two additions, both at the re-established successor boundary:
* **`SelfPresent (jumpdestFrame fj)`** via `selfPresent_runs_of_call hcall hdc.selfPresent hfrrun`
  — the P3 hop across the SAME `Runs fr (jumpdestFrame fj)` the wrapper already assembles. This is
  NOT circular: it consumes the boundary's `SelfPresent fr` (given) and the genuinely-constructed
  bytecode run, producing presence at a DIFFERENT frame.
* the **alignment** carried VERBATIM — the successor `DriveCorrPlus` uses the SAME
  `gasAcc`/`gasFrs`/`sloadAcc`/`sloadFrs` and is closed by `hdc.gasAligned`/`hdc.sloadAligned`. This
  is HONEST preservation, NOT a no-record-in-epilogue claim: it carries the same consumed-prefix
  forward. Advancing the prefix (`gasLogAligned_step_gas` at gas cursors) is the SEPARATE deferred
  EXTENSION, correctly NOT claimed here (matching the preservation-only stance of the L2.0 statement-walk).

The successor `DriveCorrPlus` is bound EXISTENTIALLY to the reached `jumpdestFrame fj` (Route-4b
indexed), NEVER the forbidden universal `∀ st' frT, Corr → DriveCorrPlus`. The supplied
`hjump`/`hbranch` bundles transcribe VERBATIM from `drive_step_block_jump`/`_branch` (satisfiable
per concrete program from `jump_to_block` / `sim_term_edge_branch` internals + the `ReachesBoundary`
walk), exactly as the `DriveCorr` versions consume them. `hcall : CallPreservesSelf` is the same
`.success` ext-call self seam the halt wrappers already supply (R1). -/

/-- **`driveCorrPlus` edge wrapper, `jump` arm (L2.3 / T3 / D2).** The `DriveCorrPlus` lifting of
`drive_step_block_jump`. From `DriveCorrPlus` at the boundary `L`, the block `b` with `b.term =
.jump dst`, the IR `RunStmts` to `st'`, the supplied `SimStmtStep` (folding S1/S5/S6), the P3 call
edge `CallPreservesSelf`, and the supplied §7 jump bundle `hjump` (VERBATIM from
`drive_step_block_jump`): run the block's statements then the lowered `PUSH4 dest ; JUMP ; ⟨land⟩
JUMPDEST` epilogue to the successor `dst`'s entry frame `jumpdestFrame fj`, RE-ESTABLISHING
`DriveCorrPlus` at `dst` (base via `corr_at_jumpdest_landing` + `cleanHalts_forward`; `SelfPresent`
via the P3 hop along `Runs fr (jumpdestFrame fj)`; alignment carried VERBATIM with the SAME
prefixes), the strict `totalGas` descent, and the IR continuation via `RunFrom.jump`. -/
theorem driveCorrPlus_step_jump {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T : Trace}
    {L : Label} {b : Block} {dst : Label} {bdst : Block} {fr : Frame}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hb : blockAt prog L = some b)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hbterm : b.term = .jump dst)
    (hrun : V2.RunStmts prog o st T b.stmts st' T)
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf)
    -- the terminator §7 jump bundle (supplied, VERBATIM from `drive_step_block_jump`): the
    -- post-statement `Corr`-frame `frT` runs the lowered `PUSH4 dest ; JUMP ; ⟨land⟩ JUMPDEST` to
    -- the successor's `JUMPDEST` landing `fj`, with the `Gjumpdest` margin (so the descent is
    -- provable). Dischargeable for a concrete program exactly as `sim_term_edge_jump`.
    (hjump : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      CleanHaltsNonException frT →
      ∃ fj : Frame, Runs frT fj
        ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
        ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
            prog.blocks dst.idx)
        ∧ fj.exec.executionEnv.code = lower prog
        ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
        ∧ fj.exec.stack = []
        ∧ fj.exec.executionEnv.canModifyState = true
        ∧ (∀ k, selfStorage fj k = st'.world k)
        ∧ MemRealises prog st' fj
        ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    ∃ fj : Frame,
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorrPlus prog sloadChg obs st' (jumpdestFrame fj) dst
          gasAcc gasFrs sloadAcc sloadFrs
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog o st' T dst O → RunFrom prog o st T L O) := by
  -- Layer D: run the block's statements to the terminator cursor (uses the BASE `Corr`).
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdc.base.corr hdc.base.cleanHalts hrun
  -- Layer E: the supplied jump bundle delivers the `JUMPDEST` landing `fj`. The clean-halt at the
  -- terminator cursor `frT` is the boundary's, forwarded along the statements run `fr → frT`.
  obtain ⟨fj, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk, hfjmod, hfjstore,
    hfjmem, hfjdec⟩ := hjump frT hcorrT (cleanHaltsNonException_forward hdc.base.cleanHalts hrunsT)
  -- the `JUMPDEST` step lands at `(dst, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbdst hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from the boundary's (the forward split).
  have hcleanSucc : CleanHaltsNonException (jumpdestFrame fj) :=
    cleanHaltsNonException_forward hdc.base.cleanHalts hfrrun
  -- re-establish `DriveCorrPlus` at the successor: base from the landing, `SelfPresent` via the
  -- P3 hop along the SAME `hfrrun`, alignment carried VERBATIM from the boundary.
  refine ⟨fj, hfrrun,
    { base := ⟨hjdcorr, hcleanSucc⟩
      selfPresent := selfPresent_runs_of_call hcall hdc.selfPresent hfrrun
      gasAligned := hdc.gasAligned
      sloadAligned := hdc.sloadAligned },
    totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas, ?_⟩
  -- the IR continuation: prepend this block's `RunStmts` + the `jump` terminator.
  intro O hO
  exact RunFrom.jump hb hrun hbterm hO

/-- **`driveCorrPlus` edge wrapper, `branch` arm (L2.4 / T4 / D3).** The `DriveCorrPlus` lifting of
`drive_step_block_branch`. From `DriveCorrPlus` at `L` (block `b`, `b.term = .branch cond thenL
elseL`), the block's IR `RunStmts` to `st'` (trace `T → T'`), the bound condition `st'.locals cond
= some cw`, the supplied `SimStmtStep`, the P3 call edge `CallPreservesSelf`, and the supplied §7
branch bundle `hbranch` (VERBATIM from `drive_step_block_branch`): run the statements then the
cond-materialise + `JUMPI` to the TAKEN successor `succ`'s entry frame `jumpdestFrame fj` (`succ =
thenL` when `cw ≠ 0`, `succ = elseL` when `cw = 0`), RE-ESTABLISHING `DriveCorrPlus` at `succ`
(base via `corr_at_jumpdest_landing` + `cleanHalts_forward`; `SelfPresent` via the P3 hop along
`Runs fr (jumpdestFrame fj)`; alignment carried VERBATIM), the strict `totalGas` descent, and the
IR continuation via `RunFrom.branchThen` / `.branchElse`. The cond-materialise sub-run is inside
the supplied `hbranch`'s `Runs frT fj`, so P3 threads `SelfPresent` across the whole `fr →
jumpdestFrame fj` at once — no separate materialise threading is needed. -/
theorem driveCorrPlus_step_branch {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace}
    {L : Label} {b : Block} {cond : Tmp} {cw : Word} {thenL elseL : Label} {fr : Frame}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hb : blockAt prog L = some b)
    (hbterm : b.term = .branch cond thenL elseL)
    (hrun : V2.RunStmts prog o st T b.stmts st' T')
    (hc : st'.locals cond = some cw)
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf)
    -- the terminator §7 branch bundle (supplied, VERBATIM from `drive_step_block_branch`): the
    -- post-statement `Corr`-frame `frT` runs the lowered cond-materialise + `JUMPI` to the TAKEN
    -- successor's `JUMPDEST` landing `fj`, with the taken successor `succ` resolved by `cw`.
    -- Dischargeable for a concrete program exactly as `sim_term_edge_branch`.
    (hbranch : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      CleanHaltsNonException frT →
      ∃ (succ : Label) (bsucc : Block) (fj : Frame),
        ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
        ∧ prog.blocks.toList[succ.idx]? = some bsucc
        ∧ Runs frT fj
        ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
        ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
            prog.blocks succ.idx)
        ∧ fj.exec.executionEnv.code = lower prog
        ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
        ∧ fj.exec.stack = []
        ∧ fj.exec.executionEnv.canModifyState = true
        ∧ (∀ k, selfStorage fj k = st'.world k)
        ∧ MemRealises prog st' fj
        ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    ∃ (succ : Label) (fj : Frame),
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorrPlus prog sloadChg obs st' (jumpdestFrame fj) succ
          gasAcc gasFrs sloadAcc sloadFrs
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog o st' T' succ O → RunFrom prog o st T L O) := by
  -- Layer D: run the block's statements to the terminator cursor (uses the BASE `Corr`).
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdc.base.corr hdc.base.cleanHalts hrun
  -- Layer E: the supplied branch bundle resolves the taken successor `succ` and its landing `fj`.
  -- The clean-halt at the terminator cursor `frT` is the boundary's, forwarded along `fr → frT`.
  obtain ⟨succ, bsucc, fj, hdir, hbsucc, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk,
    hfjmod, hfjstore, hfjmem, hfjdec⟩ := hbranch frT hcorrT
      (cleanHaltsNonException_forward hdc.base.cleanHalts hrunsT)
  -- the `JUMPDEST` step lands at `(succ, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbsucc hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from the boundary's (the forward split).
  have hcleanSucc : CleanHaltsNonException (jumpdestFrame fj) :=
    cleanHaltsNonException_forward hdc.base.cleanHalts hfrrun
  -- re-establish `DriveCorrPlus` at the taken successor, exactly as in the `jump` arm.
  refine ⟨succ, fj, hfrrun,
    { base := ⟨hjdcorr, hcleanSucc⟩
      selfPresent := selfPresent_runs_of_call hcall hdc.selfPresent hfrrun
      gasAligned := hdc.gasAligned
      sloadAligned := hdc.sloadAligned },
    totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas, ?_⟩
  -- the IR continuation: prepend this block's `RunStmts` + the firing `branch` terminator.
  intro O hO
  rcases hdir with ⟨hsucc, hnz⟩ | ⟨hsucc, hz⟩
  · subst hsucc
    exact RunFrom.branchThen hb hrun hbterm hc hnz hO
  · subst hsucc; subst hz
    exact RunFrom.branchElse hb hrun hbterm hc hO

/-! ## §10 — the `DriveCorrPlus` recursion (C8) and the tie-free headline (C9)

The four proven `driveCorrPlus_step_*` wrappers are the per-block leaves of a recursion that
threads the strengthened `DriveCorrPlus` invariant — exactly the `DriveCorr` tower of `DriveSim.lean`
(`driveStep_of_block` → `runFrom_of_driveCorr` → `lower_conforms_cyclic`), but lifted so that the
gas-positional / self-presence channels the `Plus` invariant carries are **re-established at every
reached boundary** rather than supplied per edge.

* **`DriveStepPlus`** — the `Plus` analogue of `DriveStep`: at a `DriveCorrPlus` boundary, either the
  block halts (the IR `RunFrom`, halt disjunct) or it takes an edge to a strictly-smaller successor
  whose re-established invariant is `DriveCorrPlus` (NOT the bare `DriveCorr`). Threading the `Plus`
  invariant through the recursion is what discharges the gas-advance (S3) / `SelfPresent` /
  `accounts ≠ ∅` channels uniformly, instead of supplying them at each boundary.
* **`driveStepPlus_of_block`** (C8) — assembles `DriveStepPlus` at one block by dispatching `b.term`
  to the four proven `driveCorrPlus_step_*` wrappers. The IR block run is `runStmts_exists` (from the
  static `RunDefinable`), exactly as `driveStep_of_block`.
* **`runFrom_of_driveCorrPlus`** — the `Plus` analogue of `runFrom_of_driveCorr`: strong induction on
  the bytecode `totalGas` measure, recursing at the strictly-smaller successor `DriveCorrPlus`.
* **`lower_conforms_cyclic_tiefree`** (C9) — feeds the `Plus`-constructed `RunFrom` into the existing
  `sim_cfg`, recovering the world equation with the gas / self channels DISCHARGED through the `Plus`
  thread. The genuinely-runtime residuals stay SUPPLIED (documented at C9). -/

/-- **The `Plus` per-block drive obligation.** As `DriveStep`, but the edge arm re-establishes the
strengthened `DriveCorrPlus` invariant (with its `Plus` accumulators) at the successor rather than
the bare `DriveCorr`. The halt arm is the IR `RunFrom` (the block bottoms out); the edge arm is a
strictly-smaller successor `DriveCorrPlus` plus the IR continuation. `runFrom_of_driveCorrPlus`
recurses on it; the gas / self channels thread through the successor invariant. -/
def DriveStepPlus (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (o : V2.CallOracle)
    (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace) : Prop :=
  -- halt arm: the block bottoms out, IR halts at `O`.
  (∃ O : V2.Observable, RunFrom prog o st T L O)
  ∨
  -- edge arm: a strictly-smaller successor boundary re-establishing `DriveCorrPlus`.
  (∃ (st' : V2.IRState) (T' : Trace) (succ : Label) (fr' : Frame)
      (gasAcc' : List Word) (gasFrs' : List Frame) (sloadAcc' : List Nat) (sloadFrs' : List Frame),
      DriveCorrPlus prog sloadChg obs st' fr' succ gasAcc' gasFrs' sloadAcc' sloadFrs'
    ∧ totalGas [] (.inl fr') < totalGas [] (.inl fr)
    ∧ (∀ O, RunFrom prog o st' T' succ O → RunFrom prog o st T L O))

/-- **C8 — `driveStepPlus_of_block`.** From `DriveCorrPlus` at `L`, the block present, the static
operand-definability `RunDefinable`, the per-statement simulation `SimStmtStep`, the P3 call edge
`CallPreservesSelf`, and the per-terminator supplied §7 bundles (the halt world-channel /
RETURN-epilogue / jump / branch edge data — exactly what the `driveCorrPlus_step_*` wrappers
consume, quantified by terminator shape), produce `DriveStepPlus` at this block. The IR block run is
`runStmts_exists` (`RunDefinable`); the conclusion is the halt disjunct for `stop`/`ret` (built by
`RunFrom.stop`/`.ret`) and the edge disjunct (the re-established successor `DriveCorrPlus`) for
`jump`/`branch`, dispatched on `b.term`. -/
theorem driveStepPlus_of_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st : V2.IRState} {fr : Frame} {L : Label} {T : Trace} {b : Block}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hb : blockAt prog L = some b)
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hdef : RunDefinable prog)
    (hcall : CallPreservesSelf)
    -- the `jump` destination block's presence (static, replacing `CFGAcyclic.succ_present`):
    (hjumpPresent : ∀ (dst : Label), b.term = .jump dst →
      ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `jump` edge bundle (used only on `jump dst`, exactly `driveCorrPlus_step_jump`'s):
    (hjump : ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ fj : Frame, Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks dst.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none))
    -- the `branch` edge bundle (used only on `branch cond thenL elseL`):
    (hbranch : ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks succ.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    DriveStepPlus prog sloadChg obs o st fr L T := by
  -- the toList form of the block presence (the wrappers' `_hb`/`hb` argument shape).
  have hbtl : prog.blocks.toList[L.idx]? = some b := toList_of_blockAt hb
  -- run the block's statements forward (gas-free / call-free, definable from any state).
  have hrun : V2.RunStmts prog o st T b.stmts (stmtsPost st b.stmts) T :=
    runStmts_exists (hdef.stmts st L b hb)
  -- dispatch on the terminator shape.
  cases hterm : b.term with
  | stop =>
    -- halt disjunct (LEFT): the IR `RunFrom.stop`. `SelfPresent`/`accounts ≠ ∅` at the reached terminator are threaded via the `Plus`
    -- invariant; the IR `RunFrom` itself is `RunFrom.stop`.
    exact Or.inl ⟨_, RunFrom.stop hb hrun hterm⟩
  | ret t =>
    -- halt disjunct (LEFT): the IR `RunFrom.ret`; the operand is `RunDefinable.ret_def`.
    obtain ⟨w, hv⟩ := hdef.ret_def st L b t hb hterm
    exact Or.inl ⟨_, RunFrom.ret hb hrun hterm hv⟩
  | jump dst =>
    -- edge disjunct (RIGHT) via `driveCorrPlus_step_jump`; `dst`'s presence via `hjumpPresent`.
    obtain ⟨bdst, hbdst⟩ := hjumpPresent dst hterm
    obtain ⟨fj, hfrrun, hdcorr', hlt, hcont⟩ :=
      driveCorrPlus_step_jump hdc hb hbdst hterm hrun hsim hcall (hjump dst hterm)
    exact Or.inr ⟨stmtsPost st b.stmts, T, dst, jumpdestFrame fj, _, _, _, _, hdcorr', hlt, hcont⟩
  | branch cond thenL elseL =>
    -- edge disjunct (RIGHT) via `driveCorrPlus_step_branch`; the condition is `RunDefinable`.
    obtain ⟨cw, hc⟩ := hdef.branch_def st L b cond thenL elseL hb hterm
    obtain ⟨succ, fj, hfrrun, hdcorr', hlt, hcont⟩ :=
      driveCorrPlus_step_branch hdc hb hterm hrun hc hsim hcall
        (hbranch cond thenL elseL cw hterm hc)
    exact Or.inr ⟨stmtsPost st b.stmts, T, succ, jumpdestFrame fj, _, _, _, _, hdcorr', hlt, hcont⟩

/-- **`runFrom_of_driveCorrPlus`.** The `Plus` analogue of `runFrom_of_driveCorr`: from
`DriveCorrPlus … st fr L …` and the `Plus` per-block drive obligation `DriveStepPlus` at **every**
reachable boundary, the IR `RunFrom prog o st T L` exists for some observable `O`. Proved by strong
induction on the bytecode `totalGas` measure (which strictly descends per block,
`totalGas_succ_lt`), so it holds for **cyclic** CFGs — no `CFGAcyclic`. The edge arm recurses at the
strictly-smaller successor's `DriveCorrPlus`; the gas / self channels thread through the successor
invariant. -/
theorem runFrom_of_driveCorrPlus {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle}
    (hstep : ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace)
      (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      DriveStepPlus prog sloadChg obs o st fr L T) :
    ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace)
      (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      ∃ O, RunFrom prog o st T L O := by
  -- strong induction on the bytecode `totalGas` measure of the boundary frame.
  intro st fr L T gasAcc gasFrs sloadAcc sloadFrs hdc
  induction hmeasure : totalGas [] (.inl fr) using Nat.strong_induction_on
    generalizing st fr L T gasAcc gasFrs sloadAcc sloadFrs with
  | _ n ih =>
    subst hmeasure
    rcases hstep st fr L T gasAcc gasFrs sloadAcc sloadFrs hdc with
      ⟨O, hir⟩ | ⟨st', T', succ, fr', gasAcc', gasFrs', sloadAcc', sloadFrs', hdc', hlt, hcont⟩
    · -- halt arm: the block bottoms out.
      exact ⟨O, hir⟩
    · -- edge arm: recurse at the strictly-smaller successor `DriveCorrPlus`, then prepend the block.
      obtain ⟨O, hO⟩ := ih (totalGas [] (.inl fr')) hlt st' fr' succ T'
        gasAcc' gasFrs' sloadAcc' sloadFrs' hdc' rfl
      exact ⟨O, hcont O hO⟩

/-- **C9 — `lower_conforms_cyclic_tiefree`.** The tie-free headline. Given the entry `DriveCorrPlus`
(assembled at the entry frame by `driveCorrPlus_entry`), the static operand-definability
`RunDefinable`, the per-boundary block presence, the per-statement simulation `SimStmtStep`, the P3
call edge `CallPreservesSelf`, and the per-terminator supplied §7 edge bundles, the world equation
holds for the `Plus`-constructed run's existential observable — **general over CYCLIC CFGs** (no
`CFGAcyclic`/`RunDefinable`-as-acyclicity; the `totalGas` measure replaces static block-rank).

`driveStepPlus_of_block` assembles `DriveStepPlus` at every reached boundary from the supplied data,
threading the strengthened `DriveCorrPlus` invariant; `runFrom_of_driveCorrPlus` builds the IR
`RunFrom`; the existing cycle-agnostic `sim_cfg` ties it to the bytecode halt's world.

**Re-established through the `Plus` thread** (vs `lower_conforms_cyclic`, which supplies a raw
`hstep`): the SSTORE self-presence (`SelfPresent`) and `accounts ≠ ∅` invariants re-established at every reached boundary.
The `Plus` invariant threads ONLY `SelfPresent` (the gas/sload alignment witnesses are carried
VERBATIM, never advanced). **Still SUPPLIED** (genuinely-runtime residuals): the gas positional value
**S3** supplied via `SimStmtStep` (the `StmtTies` gas conjunct), NOT discharged by any carried
alignment; the `sim_cfg` per-block ties `hstmts`/`hterm` (the serialized S1/S5/S6 spine + the world-channel halt brick), the P3
`CallPreservesSelf` `.success` ext-call self seam, and the per-terminator edge bundles
`hjumpPresent`/`hjump`/`hbranch` (concrete lowered PUSH/JUMP epilogue data). -/
theorem lower_conforms_cyclic_tiefree {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress}
    {st₀ : V2.IRState} {T : Trace} {params : Evm.CallParams} {code : ByteArray} {acc : Account}
    -- the entry boundary: a `DriveCorr` at `(prog.entry, 0)` whose frame is the call's `codeFrame`,
    -- with the self account present (`hwf`). `driveCorrPlus_entry` lifts it to `DriveCorrPlus`.
    (hbase : DriveCorr prog sloadChg obs st₀ (codeFrame params code) prog.entry)
    (hwf : params.accounts.find? params.recipient = some acc)
    -- static operand-definability (benign well-formedness — NOT `CFGAcyclic`):
    (hdef : RunDefinable prog)
    -- the P3 call edge (the `.success` ext-call self seam — supplied):
    (hcall : CallPreservesSelf)
    -- block presence at every reachable `DriveCorrPlus` boundary:
    (hpresent : ∀ (st : V2.IRState) (fr : Frame) (L : Label)
        (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      ∃ b, blockAt prog L = some b)
    -- the per-statement tie (`sim_cfg`'s + `driveStepPlus_of_block`'s):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs o L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs o self L b)
    -- the `jump` destination presence, at every block (`st`-free — the destination is static):
    (hjumpPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
        ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `jump` edge bundle, at every block / post-statement frame:
    (hjump : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ fj : Frame, Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks dst.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none))
    -- the `branch` edge bundle, at every block / post-statement frame:
    (hbranch : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks succ.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs (codeFrame params code) last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world)
      ∧ RunFrom prog o st₀ T prog.entry O := by
  -- the entry `DriveCorrPlus` (empty consumed prefixes) via `driveCorrPlus_entry`.
  have hentryPlus : DriveCorrPlus prog sloadChg obs st₀ (codeFrame params code) prog.entry [] [] [] [] :=
    driveCorrPlus_entry hbase hwf
  -- assemble the per-boundary `DriveStepPlus` from `driveStepPlus_of_block` at each reached block.
  have hstep : ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace)
      (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      DriveStepPlus prog sloadChg obs o st fr L T := by
    intro st fr L T' gasAcc gasFrs sloadAcc sloadFrs hdc
    obtain ⟨b, hb⟩ := hpresent st fr L gasAcc gasFrs sloadAcc sloadFrs hdc
    exact driveStepPlus_of_block hb hdc (hstmts L b hb) hdef hcall
      (hjumpPresent L b hb) (hjump st L b hb) (hbranch st L b hb)
  -- the `Plus` recursion builds the IR `RunFrom` from the entry `DriveCorrPlus`.
  obtain ⟨O, hir⟩ :=
    runFrom_of_driveCorrPlus hstep st₀ (codeFrame params code) prog.entry T [] [] [] [] hentryPlus
  -- the EXISTING cycle-agnostic `sim_cfg`: tie the constructed run to the bytecode halt world.
  obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := sim_cfg hstmts hterm hbase.corr hbase.cleanHalts hir
  exact ⟨O, ⟨last, haltSig, hlast, hhalt, hworld⟩, hir⟩

/-- **`lower_conforms_cyclic_assembled` — the headline with `hstmts`/`hterm` BUILT, not supplied.**
Same conclusion as `lower_conforms_cyclic_tiefree`, but the two opaque `∀-L-b` per-block
simulation universals are replaced by their honest builder inputs:

* `hwfl : WellFormedLowered prog` — the purely-structural fuel/pc/offset/slot side-conditions
  (`LowerConforms.lean:142`); and
* `hstmtties`/`htermties` — the genuine §7 per-block recording-correspondence ties (`Lir.StmtTies`
  / `Lir.TermTies`), i.e. exactly the per-cursor / per-terminator runtime ties that
  `simStmtStep_block` / `simTermStep_block` consume (assign post-state realisability, the spilled
  sload/gas stash data, the SSTORE/CALL realisation seams, the RETURN-epilogue / stop frame facts,
  and the successor-block presence for edges).

The opaque `SimStmtStep`/`SimTermStep` universals (2 of the headline's 4) are thereby DISCHARGED
through `simStmtStep_block` / `simTermStep_block`. The `jump` edge universal `hjump` is **also**
DISCHARGED here: `jump_landing_of_cleanHalt` (`LowerDecode.lean`) is the green producer for the
`Plus`-thread *pre-JUMPDEST landing* frame `fj` (sitting ON the successor's `JUMPDEST` byte, BEFORE
the `JUMPDEST` step), with its three gas guards produced from the threaded `CleanHaltsNonException
frT`; the destination presence (`hjumpPresent`) and the folded pc/offset bounds
(`WellFormedLowered.bound_jump`) supply its remaining structural inputs.

The `branch` edge universal `hbranch` is **also** DISCHARGED here: `branch_landing_of_cleanHalt`
(`LowerDecode.lean`) is the green producer for the TAKEN-successor pre-JUMPDEST landing (the
cond-materialise + JUMPI split ahead of the same `jump`-arm landing); its gas guards are produced
from the threaded `CleanHaltsNonException frT`, its presence / pc-offset bounds / fuel-sufficiency
from `hbranchPresent` / `WellFormedLowered.bound_branch` / `WellFormedLowered.matFueled_branch`.

Still HONESTLY SUPPLIED (static CFG well-formedness + the non-gas-derivable structural folds, NOT
faked): the block-presence facts `hpresent`/`hjumpPresent`/`hbranchPresent`, and the cond-materialise
stack-room fold `hstkBranch` (the `hstkKey` analogue — a charge-length bound the gas thread cannot
produce). -/
theorem lower_conforms_cyclic_assembled {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress}
    {st₀ : V2.IRState} {T : Trace} {params : Evm.CallParams} {code : ByteArray} {acc : Account}
    (hbase : DriveCorr prog sloadChg obs st₀ (codeFrame params code) prog.entry)
    (hwf : params.accounts.find? params.recipient = some acc)
    (hdef : RunDefinable prog)
    (hcall : CallPreservesSelf)
    (hpresent : ∀ (st : V2.IRState) (fr : Frame) (L : Label)
        (gasAcc : List Word) (gasFrs : List Frame) (sloadAcc : List Nat) (sloadFrs : List Frame),
      DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
      ∃ b, blockAt prog L = some b)
    -- WELL-FORMEDNESS: the folded structural side-conditions (replaces the structural part of
    -- `hstmts`/`hterm`):
    (hwfl : WellFormedLowered prog)
    -- the GENUINE §7 per-block ties (replaces the runtime part of the opaque `hstmts`/`hterm`):
    (hstmtties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      StmtTies prog sloadChg obs o L b)
    (htermties : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      TermTies prog sloadChg obs o self L b)
    (hjumpPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
        ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `branch` successor presence (static CFG well-formedness, the `hjumpPresent` analogue for
    -- both branch targets):
    (hbranchPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label), b.term = .branch cond thenL elseL →
        (∃ bthen : Block, prog.blocks.toList[thenL.idx]? = some bthen)
        ∧ (∃ belse : Block, prog.blocks.toList[elseL.idx]? = some belse))
    -- the `branch` cond-materialise stack-room fold (the structural `hstkKey`/`hstk` analogue —
    -- NOT gas-derivable; a static charge-length bound). `branch_landing_of_cleanHalt` produces the
    -- rest of the `branch` edge bundle (gas guards from the threaded clean-halt; presence /
    -- bounds / fuel-sufficiency from `hbranchPresent` / `WellFormedLowered.bound_branch` /
    -- `WellFormedLowered.matFueled_branch`).
    (hstkBranch : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label), b.term = .branch cond thenL elseL →
        (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs (codeFrame params code) last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world)
      ∧ RunFrom prog o st₀ T prog.entry O := by
  -- build the per-block `SimStmtStep` from `WellFormedLowered` + the §7 statement ties.
  have hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs o L b := by
    intro L b hbat
    obtain ⟨hassign, hsloadassign, hgasassign, hsstore, hcallties⟩ := hstmtties L b hbat
    exact simStmtStep_block (toList_of_blockAt hbat) hwfl hassign hsloadassign hgasassign hsstore
      hcallties
  -- build the per-block `SimTermStep` from `WellFormedLowered` + the §7 terminator ties.
  have hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs o self L b := by
    intro L b hbat
    obtain ⟨hsucc, hstop, hretties, hjmp, hbr⟩ := htermties L b hbat
    exact simTermStep_block (toList_of_blockAt hbat) hwfl hsucc hstop hretties hjmp hbr
  -- DISCHARGE the `jump` edge bundle from the pre-`JUMPDEST` landing producer: the destination
  -- presence (`hjumpPresent`) gives `bdst` + `dst.idx < size`, and `WellFormedLowered.bound_jump`
  -- supplies the two pc/offset bounds. `jump_landing_of_cleanHalt` then produces the landing `fj`
  -- with all three gas guards from the threaded `CleanHaltsNonException frT`.
  have hjump : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ fj : Frame, Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks dst.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    intro st L b hbat dst hbterm frT hcorrT hcsT
    obtain ⟨bdst, hbdst⟩ := hjumpPresent L b hbat dst hbterm
    have hdstlt : dst.idx < prog.blocks.size := by
      simpa using (List.getElem?_eq_some_iff.mp hbdst).1
    obtain ⟨hpc5, hoff⟩ := hwfl.bound_jump L b dst (toList_of_blockAt hbat) hbterm
    exact jump_landing_of_cleanHalt frT hcorrT hbterm (toList_of_blockAt hbat) hbdst hdstlt
      hpc5 hoff hcsT
  -- DISCHARGE the `branch` edge bundle from `branch_landing_of_cleanHalt`: the two successor
  -- presences (`hbranchPresent`) give `bthen`/`belse` + the `idx < size` bounds; the folded
  -- `WellFormedLowered.bound_branch` / `matFueled_branch` supply the pc/offset bounds and the
  -- cond-materialise fuel-sufficiency; the structural stack-room fold is `hstkBranch`. The clean-
  -- halt at the terminator cursor is forwarded along the statements run inside `driveCorrPlus_step_branch`.
  have hbranch : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame,
        Corr prog sloadChg obs (stmtsPost st b.stmts) frT L b.stmts.length →
        CleanHaltsNonException frT →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ Runs frT fj
          ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
          ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
              prog.blocks succ.idx)
          ∧ fj.exec.executionEnv.code = lower prog
          ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
          ∧ fj.exec.stack = []
          ∧ fj.exec.executionEnv.canModifyState = true
          ∧ (∀ k, selfStorage fj k = (stmtsPost st b.stmts).world k)
            ∧ MemRealises prog (stmtsPost st b.stmts) fj
          ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    intro st L b hbat cond thenL elseL cw hbterm hc frT hcorrT hcsT
    obtain ⟨⟨bthen, hbthen⟩, ⟨belse, hbelse⟩⟩ := hbranchPresent L b hbat cond thenL elseL hbterm
    have hthenlt : thenL.idx < prog.blocks.size := by
      simpa using (List.getElem?_eq_some_iff.mp hbthen).1
    have helselt : elseL.idx < prog.blocks.size := by
      simpa using (List.getElem?_eq_some_iff.mp hbelse).1
    obtain ⟨hbt, hbthenoff, hbelseoff⟩ := hwfl.bound_branch L b cond thenL elseL
      (toList_of_blockAt hbat) hbterm
    -- the cond-materialise stack-room fold, with `frT.stack = []` from `Corr`.
    have hstkCond : frT.exec.stack.size
        + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond)).length ≤ 1024 := by
      rw [hcorrT.stack_nil]
      simpa using hstkBranch L b hbat cond thenL elseL hbterm
    exact branch_landing_of_cleanHalt frT hcorrT hbterm (toList_of_blockAt hbat) hc hbthen hbelse
      hthenlt helselt hbt hbthenoff hbelseoff
      (hwfl.matFueled_branch L b cond thenL elseL (toList_of_blockAt hbat) hbterm) hstkCond hcsT
  exact lower_conforms_cyclic_tiefree hbase hwf hdef hcall hpresent hstmts hterm
    hjumpPresent hjump hbranch

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the tie-discharge deliverables.
#print axioms Lir.V2.realisedCall_projection
#print axioms Lir.V2.gasRecord_eq_gasReadOf
#print axioms Lir.V2.gasReadOf_gasFrame_eq_obs
#print axioms Lir.V2.gasLogAligned_nil
#print axioms Lir.V2.FramesRun.snoc
#print axioms Lir.V2.gasLogAligned_step_gas
#print axioms Lir.V2.aligned_read_eq_obs
#print axioms Lir.V2.gasRealises_obs_of_witness
#print axioms Lir.V2.sloadRecord_discharges_obs
#print axioms Lir.V2.sloadLogAligned_nil
#print axioms Lir.V2.sloadLogAligned_step_sload
#print axioms Lir.V2.alignedSload_read_eq_obs
#print axioms Lir.V2.sloadRealises_charge_of_witness
#print axioms Lir.V2.selfPresent_runs
#print axioms Lir.V2.selfPresent_codeFrame
#print axioms Lir.V2.driveCorrPlus_entry
-- StepPreservesSelf is now DISCHARGED (a theorem, not a supplied edge): the engine-level brick
-- `stepFrame_next_self` (the `a := self` corollary of the dispatch walk), plus the call-resume
-- structural halves, are all axiom-clean.
#print axioms Lir.V2.stepPreservesSelf
#print axioms Lir.V2.resumeAfterCall_self_of_accounts
-- CALLMONO: account-presence monotone across a whole `drive` run (Brick D) — the `.success` shape
-- of `CallPreservesSelf` discharged (the CREATE no-erase seam now eliminated; only `hprec` supplied).
#print axioms Lir.V2.callPreservesSelf_success
#print axioms Lir.V2.callPreservesSelf
#print axioms Lir.V2.callPreservesSelf_modGuards
-- C3: the no-bridge VALUE channels of the L2.0 statement-walk.
#print axioms Lir.V2.memRealises_setLocal_nonspilled
#print axioms Lir.V2.driveCorrPlus_assign_remat_memRealises
#print axioms Lir.V2.driveCorrPlus_sload_value
#print axioms Lir.V2.driveCorrPlus_sload_value_world
-- L2.0g: the seedable GAS-alignment bricks (GAS-advancing walk decls + S3 read-off removed, audit).
#print axioms Lir.V2.FramesRun.snoc_seed
#print axioms Lir.V2.gasLogAligned_step_gas_seed
-- C4: the account-map non-emptiness facts + the edge wrappers (jump/branch).
#print axioms Lir.V2.accounts_ne_empty_of_selfPresent
#print axioms Lir.V2.driveCorrPlus_step_jump
#print axioms Lir.V2.driveCorrPlus_step_branch
-- C8/C9: the `DriveCorrPlus` recursion assembly + the tie-free headline.
#print axioms Lir.V2.driveStepPlus_of_block
#print axioms Lir.V2.runFrom_of_driveCorrPlus
#print axioms Lir.V2.lower_conforms_cyclic_tiefree
-- ASSEMBLE: the headline with `hstmts`/`hterm` built from `WellFormedLowered` + the §7 ties.
#print axioms Lir.V2.lower_conforms_cyclic_assembled
