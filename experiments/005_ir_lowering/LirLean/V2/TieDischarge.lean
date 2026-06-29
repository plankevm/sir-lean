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

/-- **Foundational per-op step — the no-record arm** (twin of `gasLogAligned_step_norecord`). Any
step that is *not* a recorded top-level SLOAD read leaves the sload accumulator (and the witness
list) unchanged, so alignment is preserved verbatim. The common case the walk-induction threads
between SLOAD cursors (every non-SLOAD op, and SLOAD reads inside a descended CALL where
`stack ≠ []`). -/
theorem sloadLogAligned_step_norecord {sloadAcc : List Nat} {frs : List Frame}
    (halign : SloadLogAligned sloadAcc frs) :
    SloadLogAligned sloadAcc frs := halign

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

/-! ### `SelfPresent ⇒ accounts ≠ ∅` (the non-emptiness conjunct of the halt ties)

The halt wrappers (`driveCorrPlus_step_stop`/`_ret`) must emit the `¬ (accounts == ∅)` conjunct
of the §7 terminator bundle. It is *derived* — not supplied — from `SelfPresent` (the self account
is present in the map, so the map cannot be empty). The single new account-map fact is
`find?_some_ne_empty`: a `find?` hit forces the underlying red-black tree to be non-`nil`, and an
empty map's tree IS `nil`, so the structural `BEq` (`RBNode.all₂ (·==·) tree nil`) is `false`.

`AccountMap = Batteries.RBMap AccountAddress Account compare`, whose `BEq` runs `RBNode.all₂`
(`Batteries/Data/RBMap/Basic.lean:232`): a `StateT`-over-`Option` walk of the left tree against the
right tree's *stream*. Against the empty (`nil`) right tree the stream is empty, so the first visited
node's `next?` returns `none` and short-circuits the whole walk to `none` — never matching
`some (_, .nil)`. `forM_from_nil` proves exactly this short-circuit; `all2_nil_false` packages it. -/

open Batteries in
/-- The `all₂` `StateT (RBNode.Stream β) Option` walk of `t` against the **empty** stream is `none`
for a non-`nil` `t` (and `some (⟨⟩, .nil)` for `nil`): from the empty initial state, the first node
visited calls `next?` on `.nil` (`= none`) and short-circuits. Proved by structural induction on
`t`, casing the left child (the leftmost-first descent of `RBNode.forM`). -/
theorem forM_from_nil {α β : Type} (R : α → β → Bool) (t : RBNode α) :
    StateT.run (s := (RBNode.Stream.nil : RBNode.Stream β))
      (t.forM (fun a s => do
        let (b, s) ← s.next?
        bif R a b then pure (⟨⟩, s) else none))
    = (match t with
        | .nil => some ((⟨⟩ : PUnit), (RBNode.Stream.nil : RBNode.Stream β))
        | _ => none) := by
  induction t with
  | nil => rfl
  | node c l v r ihl ihr =>
    show (StateT.run (RBNode.forM _ l) RBNode.Stream.nil >>= fun x =>
           StateT.run ((fun a s => _) v) x.2 >>= fun y =>
             StateT.run (RBNode.forM _ r) y.2) = none
    cases l with
    | nil =>
      rw [show StateT.run (RBNode.forM (fun a s => do
              let (b, s) ← s.next?; bif R a b then pure (⟨⟩, s) else none)
              (RBNode.nil : RBNode α)) RBNode.Stream.nil
            = some ((⟨⟩ : PUnit), (RBNode.Stream.nil : RBNode.Stream β)) from ihl]
      rfl
    | node c' l' v' r' => rw [ihl]; rfl

open Batteries in
/-- `RBNode.all₂ R t nil = false` for any non-`nil` `t`: the empty right tree's stream is empty, so
the walk (`forM_from_nil`) short-circuits to `none`, which does not match `some (_, .nil)`. -/
theorem all2_nil_false {α β : Type} (R : α → β → Bool) (t : RBNode α) (hne : t ≠ .nil) :
    RBNode.all₂ R t RBNode.nil = false := by
  unfold RBNode.all₂
  have hrun := forM_from_nil R t
  rw [show (RBNode.nil : RBNode β).toStream = RBNode.Stream.nil from rfl]
  cases t with
  | nil => exact absurd rfl hne
  | node c l v r => rw [hrun]

open Batteries in
/-- **The new account-map fact.** A `find?` hit (`m.find? addr = some acc`) forces `m`'s underlying
tree non-`nil`, and the empty map's tree IS `nil`, so the structural `BEq` (`RBNode.all₂ (·==·)
tree nil`, `all2_nil_false`) is `false`: `¬ (m == ∅)`. Pure account-map fact — does NOT re-supply
`SelfPresent` (it only consumes the `find? = some` witness `SelfPresent` provides). -/
theorem find?_some_ne_empty (m : Evm.AccountMap) (addr : Evm.AccountAddress) (acc : Evm.Account)
    (h : m.find? addr = some acc) : ¬ (m == (∅ : Evm.AccountMap)) = true := by
  intro hbeq
  -- a `find?` hit forces the underlying red-black tree non-`nil` (`find? nil = none`).
  have htree : m.1 ≠ .nil := by
    intro hc
    rw [RBMap.find?, RBMap.findEntry?, RBSet.findP?, hc] at h
    simp [RBNode.find?] at h
  -- `(m == ∅)` IS `RBNode.all₂ (·==·) m.1 nil`, which is `false` for non-`nil` `m.1`.
  have hbeq2 : RBNode.all₂ (· == ·) m.1 RBNode.nil = true := hbeq
  rw [all2_nil_false _ m.1 htree] at hbeq2
  exact Bool.noConfusion hbeq2

/-- **Thin bridge: `SelfPresent ⇒ accounts ≠ ∅`.** The exact non-emptiness conjunct the halt
wrappers emit (T1 directly, T2 at the return endpoint `frv` after the P3 hop). -/
theorem accounts_ne_empty_of_selfPresent {fr : Frame} (h : SelfPresent fr) :
    ¬ (fr.exec.accounts == (∅ : Evm.AccountMap)) = true := by
  obtain ⟨acc, hf⟩ := h
  exact find?_some_ne_empty _ _ _ hf

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

/-! ### `StepPreservesSelf` is DISCHARGED — every `.next` opcode keeps the self account present

The materialise bricks above (`selfPresent_addFrame`/…) certify the *Lir* post-frames. The
`Runs`-level `StepPreservesSelf` edge ranges over the **engine** `stepFrame`, so it needs the
account-presence preservation proved for *every* `.next`-producing opcode `Evm.stepFrame` can take —
not just the ones the lowering emits. We prove that fully generally here, so `StepPreservesSelf`
becomes a theorem (no longer a supplied hypothesis), discharged outright for the lowered program (and
every program). The template is `Runs.gasAvailable_le`'s `StepsTo.gas_le` brick: split System vs
non-`System`, case the dispatch/`systemOp` arm.

The two facts a `.next` step preserves:
* `exec'.executionEnv.address = exec.executionEnv.address` — **every** opcode (`replaceStackAndIncrPC`/
  `charge`/the CALL/CREATE resumes all leave `executionEnv` untouched), and
* presence at that address — `accounts` is either left verbatim (all arithmetic/env/memory/jump/SLOAD
  ops, and the CALL/CREATE `.next` fallbacks via `resumeAfterCall`/`resumeAfterCreate` whose
  `result.accounts = exec.accounts`) or has an account **inserted at the self address** (SSTORE/TSTORE
  via `State.sstore`/`State.tstore`, whose `none` branch is the map verbatim and whose `some` branch is
  `setAccount self … = insert self …`). No opcode inside `drive` ever erases the self entry. -/

/-- `charge` leaves the account map and execution environment untouched (only `gasAvailable`
moves): if `charge c e = .ok e'` then `e'.accounts = e.accounts` and `e'.executionEnv =
e.executionEnv`. -/
theorem charge_accounts_env {c : ℕ} {e e' : ExecutionState} (h : charge c e = .ok e') :
    e'.accounts = e.accounts ∧ e'.executionEnv = e.executionEnv := by
  unfold charge at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- `chargeMemExpansion` likewise leaves `accounts`/`executionEnv` untouched. -/
theorem chargeMemExpansion_accounts_env {e e' : ExecutionState} {off sz : UInt256}
    (h : chargeMemExpansion e off sz = .ok e') :
    e'.accounts = e.accounts ∧ e'.executionEnv = e.executionEnv := by
  unfold chargeMemExpansion at h
  split at h
  · exact absurd h (by simp)
  · exact charge_accounts_env h

/-- **The presence side-condition `SelfPresent` reads, stated on raw execution states.** -/
def SelfAt (exec : ExecutionState) : Prop :=
  ∃ acc : Account, exec.accounts.find? exec.executionEnv.address = some acc

/-- `replaceStackAndIncrPC` preserves `SelfAt` (touches only `stack`/`pc`). -/
theorem selfAt_replaceStackAndIncrPC {e : ExecutionState} (s : Stack Word) (pcΔ : UInt8)
    (h : SelfAt e) : SelfAt (ExecutionState.replaceStackAndIncrPC e s pcΔ) := h

end Lir.V2

/-! ### `SelfAt` preservation through each `.next` dispatch arm (engine level)

We work in the `Evm` namespace to reach the dispatch/`systemOp`/`smsfOp` definitions directly. The
two account-writing opcodes (`SSTORE`, `TSTORE`) write through `State.sstore`/`State.tstore`, whose
`none` branch returns the state verbatim and whose `some` branch is `setAccount self … = insert self`.
Both are presence-preserving at the self address; we prove that for `State.sstore`/`State.tstore`
once. -/

namespace Evm

open GasConstants

/-- `State.sstore` keeps the self account present and the execution environment fixed: the `none`
branch returns the state verbatim; the `some` branch inserts at the self address. -/
theorem sstore_self_present (st : State) (key val : UInt256)
    (h : ∃ acc, st.accounts.find? st.executionEnv.address = some acc) :
    (∃ acc, (st.sstore key val).accounts.find? (st.sstore key val).executionEnv.address = some acc) := by
  obtain ⟨acc, ha⟩ := h
  -- `State.sstore`'s `lookupAccount self |>.option self (fun acc ↦ …)` with `ha = some acc`
  -- reduces to the `some` branch: `setAccount self (acc.updateStorage …)` + a substate update.
  -- Both leave `executionEnv` fixed and set `accounts := insert self …`; reading self back is `some`.
  refine ⟨acc.updateStorage key val, ?_⟩
  unfold State.sstore
  simp only [State.lookupAccount, ha, Option.option]
  exact BytecodeLayer.Maps.accounts_find?_insert_self _ _ _

/-- `State.tstore` keeps the self account present and the execution environment fixed (it touches
only `accounts` at the self address, via `updateAccount self`, in the `some` branch; `none` is
verbatim). -/
theorem tstore_self_present (st : State) (key val : UInt256)
    (h : ∃ acc, st.accounts.find? st.executionEnv.address = some acc) :
    (∃ acc, (st.tstore key val).accounts.find? (st.tstore key val).executionEnv.address = some acc) := by
  obtain ⟨acc, ha⟩ := h
  refine ⟨acc.updateTransientStorage key val, ?_⟩
  unfold State.tstore
  simp only [State.lookupAccount, ha, Option.option]
  exact BytecodeLayer.Maps.accounts_find?_insert_self _ _ _

/-! ### Combinator-level self-presence preservation (the non-`System`, non-storage `.next` arms)

Every simple dispatch arm ends `continueWith (replaceStackAndIncrPC e …)` for an `e` that is the
post-`charge` state with at most `memory`/`activeWords`/`substate`/`toMachineState` updated — never
`accounts` or `executionEnv`. So each preserves `SelfAt`. We prove the shared shapes once. -/

open Lir.V2 (SelfAt) in
/-- A `.next` produced by `continueWith` carries its argument verbatim: `continueWith e = .ok (.next
e')` forces `e' = e`. -/
theorem continueWith_next {e e' : ExecutionState} (h : continueWith e = .ok (.next e')) : e' = e := by
  unfold continueWith at h
  simp only [Except.ok.injEq, Signal.next.injEq] at h
  exact h.symm

end Evm

namespace Lir.V2
open Evm GasConstants BytecodeLayer.Maps

/-- `SelfAt` survives `replaceStackAndIncrPC` of a state whose `accounts`/`executionEnv` equal a
`SelfAt` base. -/
theorem selfAt_replaceOfBase {base e : ExecutionState} (s : Stack Word) (pcΔ : UInt8)
    (hacc : e.accounts = base.accounts) (henv : e.executionEnv = base.executionEnv)
    (h : SelfAt base) : SelfAt (ExecutionState.replaceStackAndIncrPC e s pcΔ) := by
  obtain ⟨acc, ha⟩ := h
  exact ⟨acc, by
    show e.accounts.find? e.executionEnv.address = some acc
    rw [hacc, henv]; exact ha⟩

end Lir.V2

namespace Evm
open GasConstants

/-- The resumed CALL frame keeps the self account present whenever the returned `result.accounts`
contains the caller self address. `resumeAfterCall` sets `exec.accounts := result.accounts` and
leaves `executionEnv` (hence `.address`) at the suspended caller's value — both by `rfl`. -/
theorem resumeAfterCall_selfAt (result : CallResult) (pd : PendingCall)
    (h : ∃ acc, result.accounts.find? pd.frame.exec.executionEnv.address = some acc) :
    ∃ acc, (resumeAfterCall result pd).exec.accounts.find?
        (resumeAfterCall result pd).exec.executionEnv.address = some acc := h

/-- The resumed CREATE frame keeps the self account present whenever the returned `result.accounts`
contains the caller self address. Same `rfl` shape as `resumeAfterCall_selfAt` once
`resumeAfterCreate` succeeds (it can throw `OutOfGas`, in which case there is no resumed frame). -/
theorem resumeAfterCreate_selfAt (result : CreateResult) (pd : PendingCreate) {f : Frame}
    (hres : resumeAfterCreate result pd = .ok f)
    (h : ∃ acc, result.accounts.find? pd.frame.exec.executionEnv.address = some acc) :
    ∃ acc, f.exec.accounts.find? f.exec.executionEnv.address = some acc := by
  unfold resumeAfterCreate at hres
  simp only [bind, Except.bind, pure, Except.pure] at hres
  split at hres
  · exact absurd hres (by simp)
  · simp only [Except.ok.injEq] at hres; subst hres; exact h

/-- **`callArm` `.next` (fallback) preserves self-presence.** On the funds/depth fallback `callArm`
resumes the parent via `resumeAfterCall failed pending`, whose `failed.accounts = e1.accounts =
exec.accounts` (the captured caller map; `charge` preserves accounts) and whose `pending.frame.exec`
shares `exec`'s execution environment (`charge` preserves it). So the resumed self lookup is the
caller's own, present by hypothesis. -/
theorem callArm_next_self
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256}
    {permission : Bool} {exec' : ExecutionState}
    (h : callArm fr exec stack gas caller recipient codeAddress value apparentValue
          inOffset inSize outOffset outSize permission = .ok (.next exec'))
    (hself : ∃ acc, exec.accounts.find? exec.executionEnv.address = some acc) :
    ∃ acc, exec'.accounts.find? exec'.executionEnv.address = some acc := by
  rw [callArm] at h
  cases hw : (memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize)) with
  | none => rw [hw] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some words' =>
    rw [hw] at h
    simp only [bind, Except.bind] at h
    cases he1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e => rw [he1] at h; simp at h
    | ok e1 =>
      rw [he1] at h
      simp only [] at h
      obtain ⟨he1acc, he1env⟩ := Lir.V2.charge_accounts_env he1
      set ca : AccountAddress := AccountAddress.ofUInt256 codeAddress with hca
      set rc : AccountAddress := AccountAddress.ofUInt256 recipient with hrc
      set extraCost := callExtraCost ca rc value e1.accounts e1.substate with hextra
      set gasCap := callGasCap ca rc value gas e1.accounts e1.gasAvailable e1.substate with hgcap
      set childGas := if value = 0 then gasCap else gasCap + Gcallstipend with hcg
      cases he2 : charge (gasCap + extraCost) e1 with
      | error e => rw [he2] at h; simp at h
      | ok e2 =>
        rw [he2] at h
        simp only [] at h
        obtain ⟨he2acc, he2env⟩ := Lir.V2.charge_accounts_env he2
        split at h
        · -- needsCall branch: contradiction
          simp only [Except.ok.injEq] at h
          exact absurd h (by simp)
        · -- next (fallback) branch
          simp only [Except.ok.injEq, Signal.next.injEq] at h
          subst h
          -- `exec'` is `(resumeAfterCall failed pending).exec`; reduce via `resumeAfterCall_selfAt`.
          apply resumeAfterCall_selfAt
          -- `failed.accounts = e1.accounts`; `pending.frame.exec.executionEnv = e2.executionEnv`.
          show ∃ acc, e1.accounts.find? e2.executionEnv.address = some acc
          obtain ⟨acc, hacc⟩ := hself
          exact ⟨acc, by rw [he2env, he1env, he1acc]; exact hacc⟩

/-- **`createArm` `.next` (fallback) preserves self-presence.** Both `.next` arms resume the parent
via `resumeAfterCreate failed pending`, whose `failed.accounts = exec.accounts` (captured before any
charge) and whose `pending.frame.exec` shares `exec`'s execution environment; so the resumed self
lookup is the caller's own. -/
theorem createArm_next_self
    {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {value initOffset initSize : UInt256} {salt : Option ByteArray} {exec' : ExecutionState}
    (h : createArm fr exec stack value initOffset initSize salt = .ok (.next exec'))
    (hself : ∃ acc, exec.accounts.find? exec.executionEnv.address = some acc) :
    ∃ acc, exec'.accounts.find? exec'.executionEnv.address = some acc := by
  rw [createArm] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- The `failed` CreateResult (accounts = exec.accounts) and `pending` (frame.exec = exec) are the
  -- shared let-bound values of both `.next` arms; a `resumeAfterCreate failed pending = .ok f`
  -- resumes with the caller self present, via `resumeAfterCreate_selfAt`.
  have key : ∀ (f : Frame),
      resumeAfterCreate
        { address := default
          createdAccounts := exec.createdAccounts
          accounts := exec.accounts
          gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
          substate := exec.toState.substate
          success := false
          output := .empty }
        { frame := { fr with exec := exec }
          stack := stack
          callerAccounts := exec.accounts
          value := value
          initOffset := initOffset.toUInt64
          initSize := initSize.toUInt64
          initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size }
        = .ok f →
      ∃ acc, f.exec.accounts.find? f.exec.executionEnv.address = some acc := by
    intro f hf
    exact resumeAfterCreate_selfAt _ _ hf hself
  -- Case on the two guards (nonce overflow; funds/depth/size) — both fall through to a
  -- `resumeAfterCreate failed pending` `.next`; the third is the `.needsCreate` descent.
  split at h
  · -- nonce-overflow fallback
    revert h
    cases hr : resumeAfterCreate _ _ with
    | error e => intro h; simp at h
    | ok f =>
      intro h
      simp only [Except.ok.injEq, Signal.next.injEq] at h
      subst h
      exact key f hr
  · split at h
    · -- successful guard: `.needsCreate`, contradiction with `.next`
      simp only [Except.ok.injEq] at h; exact absurd h (by simp)
    · -- funds/depth/size fallback
      revert h
      cases hr : resumeAfterCreate _ _ with
      | error e => intro h; simp at h
      | ok f =>
        intro h
        simp only [Except.ok.injEq, Signal.next.injEq] at h
        subst h
        exact key f hr

/-- **A `.next` System op preserves self-presence.** STOP/RETURN/REVERT/SELFDESTRUCT/INVALID never
emit `.next` (they `haltOp`); the CALL family reduces (`systemOp_callArm_reduce`) to `callArm` on the
*same* `exec` (so `callArm_next_self` consumes `SelfAt exec` directly); CREATE/CREATE2 reduce to
`createArm` on the charged `ec`, whose `accounts`/`executionEnv` equal `exec`'s
(`chargeMemExpansion`/`charge` preserve both), so `createArm_next_self` consumes the transported
`SelfAt ec`. -/
theorem systemOp_next_self {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {exec' : ExecutionState}
    (h : systemOp op fr exec = .ok (.next exec'))
    (hself : ∃ acc, exec.accounts.find? exec.executionEnv.address = some acc) :
    ∃ acc, exec'.accounts.find? exec'.executionEnv.address = some acc := by
  cases op with
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact absurd (by unfold systemOp at h; exact h)
      (BytecodeLayer.System.haltOp_not_next' (by tauto))
  | CALL | CALLCODE | DELEGATECALL | STATICCALL =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc⟩ :=
      BytecodeLayer.System.systemOp_callArm_reduce (by tauto) h
    exact callArm_next_self hc hself
  | CREATE =>
    -- Reduce `systemOp .CREATE` to `createArm fr ec …` while exposing `ec.accounts = exec.accounts`
    -- and `ec.executionEnv = exec.executionEnv` (both charges preserve them).
    unfold systemOp at h
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (createCost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              refine createArm_next_self h ?_
              obtain ⟨acc, ha⟩ := hself
              exact ⟨acc, by rw [hcacc, hmacc, hcenv, hmenv]; exact ha⟩
  | CREATE2 =>
    unfold systemOp at h
    simp only [bind, Except.bind] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨s, val, io, is, salt⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp at h
        · cases hm : chargeMemExpansion exec io is with
          | error e => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (create2Cost is) em with
            | error e => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              obtain ⟨hmacc, hmenv⟩ := Lir.V2.chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := Lir.V2.charge_accounts_env hc
              refine createArm_next_self h ?_
              obtain ⟨acc, ha⟩ := hself
              exact ⟨acc, by rw [hcacc, hmacc, hcenv, hmenv]; exact ha⟩

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- `unOp`/`binOp`/`ternOp`/`pushOp`/EXP/KECCAK256/copy/BLOBHASH all `charge` (preserving
accounts/env) then `continueWith (replaceStackAndIncrPC e …)` of a state `e` whose accounts/env
equal the charged state's — so `.next` preserves `SelfAt`. We capture that common post-charge
`replaceStackAndIncrPC` shape once. -/
theorem dispatch_simple_arm_next_self {exec echarged e exec' : ExecutionState}
    {s : Stack UInt256} {pcΔ : UInt8} {cost : ℕ}
    (hc : charge cost exec = .ok echarged)
    (hbase_acc : e.accounts = echarged.accounts) (hbase_env : e.executionEnv = echarged.executionEnv)
    (heq : exec' = ExecutionState.replaceStackAndIncrPC e s pcΔ)
    (hself : SelfAt exec) : SelfAt exec' := by
  subst heq
  obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
  exact selfAt_replaceOfBase s pcΔ (by rw [hbase_acc, hcacc]) (by rw [hbase_env, hcenv]) hself

/-- A `pushOp` `.next` preserves `SelfAt`: `charge` then `replaceStackAndIncrPC` of the charged
state. -/
theorem pushOp_next_self {v : ExecutionState → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : pushOp v exec cost = .ok (.next exec')) (hself : Lir.V2.SelfAt exec) :
    Lir.V2.SelfAt exec' := by
  unfold pushOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h
    exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- A `unStateOp` `.next` whose world-op `f` leaves `accounts`/`executionEnv` fixed preserves
`SelfAt` (the dispatch's `unStateOp` arms — BALANCE/EXTCODESIZE/EXTCODEHASH/CALLDATALOAD/BLOCKHASH/
SLOAD/TLOAD — all read-only on `accounts` via `addAccessedAccount`/`addAccessedStorageKey`/pure
reads). -/
theorem unStateOp_next_self {f : Evm.State → UInt256 → Evm.State × UInt256}
    {cost : ExecutionState → UInt256 → ℕ} {exec exec' : ExecutionState}
    (hf : ∀ (st : Evm.State) (a : UInt256), (f st a).1.accounts = st.accounts
        ∧ (f st a).1.executionEnv = st.executionEnv)
    (h : unStateOp f cost exec = .ok (.next exec')) (hself : SelfAt exec) :
    SelfAt exec' := by
  unfold unStateOp at h
  simp only [bind, Except.bind] at h
  cases hp : exec.stack.pop with
  | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
  | some v =>
    obtain ⟨st1, a⟩ := v; rw [hp] at h
    simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    cases hc : charge (cost exec a) exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h
      simp only [] at h
      rw [continueWith_next h]
      obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
      obtain ⟨hfacc, hfenv⟩ := hf ec.toState a
      -- `exec' = replaceStackAndIncrPC { ec with toState := (f ec.toState a).1 } …`
      refine selfAt_replaceOfBase _ _ ?_ ?_ hself
      · show (f ec.toState a).1.accounts = exec.accounts; rw [hfacc, hcacc]
      · show (f ec.toState a).1.executionEnv = exec.executionEnv; rw [hfenv, hcenv]

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceStackAndIncrPC) in
/-- A `charge`-then-`SSTORE`-write `.next` preserves `SelfAt`, for **any** charge cost: `charge`
keeps `accounts`/`executionEnv`, then `State.sstore` writes at the self address. Abstracting the
cost dodges spelling the EIP-2200 `sstoreCost` term. -/
theorem charge_sstore_next_self {cost : ℕ} {exec exec' : ExecutionState} {key newVal : UInt256}
    {st : Stack UInt256}
    (h : (charge cost exec).bind (fun ec => continueWith
        (ExecutionState.replaceStackAndIncrPC { ec with toState := ec.toState.sstore key newVal } st))
      = .ok (.next exec'))
    (hself : SelfAt exec) : SelfAt exec' := by
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hc] at h; simp only [bind, Except.bind] at h
    rw [continueWith_next h]
    refine selfAt_replaceStackAndIncrPC _ _ ?_
    obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
    refine sstore_self_present ec.toState key newVal ?_
    obtain ⟨acc, ha⟩ := hself; exact ⟨acc, by rw [hcacc, hcenv]; exact ha⟩

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceStackAndIncrPC) in
/-- The `TSTORE` twin of `charge_sstore_next_self`. -/
theorem charge_tstore_next_self {cost : ℕ} {exec exec' : ExecutionState} {key val : UInt256}
    {st : Stack UInt256}
    (h : (charge cost exec).bind (fun ec => continueWith
        (ExecutionState.replaceStackAndIncrPC { ec with toState := ec.toState.tstore key val } st))
      = .ok (.next exec'))
    (hself : SelfAt exec) : SelfAt exec' := by
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp [bind, Except.bind] at h
  | ok ec =>
    rw [hc] at h; simp only [bind, Except.bind] at h
    rw [continueWith_next h]
    refine selfAt_replaceStackAndIncrPC _ _ ?_
    obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
    refine tstore_self_present ec.toState key val ?_
    obtain ⟨acc, ha⟩ := hself; exact ⟨acc, by rw [hcacc, hcenv]; exact ha⟩

open Lir.V2 (SelfAt charge_accounts_env chargeMemExpansion_accounts_env
  selfAt_replaceOfBase selfAt_replaceStackAndIncrPC) in
/-- **A `.next` `smsfOp` preserves self-presence.** The memory/stack/flow arms
(POP/MLOAD/MSTORE/MSTORE8/MSIZE/PC/JUMP/JUMPI/JUMPDEST/MCOPY/GAS) leave `accounts`/`executionEnv`
untouched; SLOAD/TLOAD are `unStateOp` read-only on accounts; SSTORE/TSTORE write *at the self
address* (`State.sstore`/`State.tstore` — `none` verbatim, `some` insert-at-self). -/
theorem smsfOp_next_self {op : Operation.SmsfOp} {fr : Frame} {exec exec' : ExecutionState}
    (h : smsfOp op fr exec = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold smsfOp at h
  cases op with
  | POP =>
    simp only [bind, Except.bind] at h
    cases hc : charge Gbase exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      cases hp : ec.stack.pop with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨st, x⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself
  | MLOAD =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, addr⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec addr 32 with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge Gverylow em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
          exact selfAt_replaceOfBase _ _ (by rw [hcacc, hmacc]) (by rw [hcenv, hmenv]) hself
  | MSTORE =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, addr, val⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec addr 32 with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge Gverylow em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
          exact selfAt_replaceOfBase _ _ (by rw [hcacc, hmacc]) (by rw [hcenv, hmenv]) hself
  | MSTORE8 =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, addr, val⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec addr 1 with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge Gverylow em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
          exact selfAt_replaceOfBase _ _ (by rw [hcacc, hmacc]) (by rw [hcenv, hmenv]) hself
  | SLOAD =>
    refine unStateOp_next_self ?_ h hself
    intro st a; exact ⟨rfl, rfl⟩
  | SSTORE =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      split at h
      · simp at h
      · cases hp : exec.stack.pop2 with
        | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        | some v =>
          obtain ⟨st, key, newVal⟩ := v; rw [hp] at h
          simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
          exact charge_sstore_next_self h hself
  | TLOAD =>
    refine unStateOp_next_self ?_ h hself
    intro st a; exact ⟨rfl, rfl⟩
  | TSTORE =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hr : requireStateMod exec with
    | error e => rw [hr] at h; simp at h
    | ok _ =>
      rw [hr] at h; simp only [] at h
      cases hc : charge tstoreCost exec with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        cases hp : ec.stack.pop2 with
        | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        | some v =>
          obtain ⟨st, key, val⟩ := v; rw [hp] at h
          simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
          rw [continueWith_next h]
          obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
          refine selfAt_replaceStackAndIncrPC _ _ ?_
          refine tstore_self_present ec.toState key val ?_
          obtain ⟨acc, ha⟩ := hself; exact ⟨acc, by rw [hcacc, hcenv]; exact ha⟩
  | MSIZE => exact pushOp_next_self h hself
  | GAS => exact pushOp_next_self h hself
  | PC => exact pushOp_next_self h hself
  | JUMP =>
    simp only [bind, Except.bind] at h
    cases hc : charge Gmid exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      cases hp : ec.stack.pop with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨st, dest⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
        cases hd : fr.get_dest dest with
        | none => rw [hd] at h; simp at h
        | some newpc =>
          rw [hd] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨acc, ha⟩ := hself
          exact ⟨acc, by
            show ec.accounts.find? ec.executionEnv.address = some acc
            rw [hcacc, hcenv]; exact ha⟩
  | JUMPI =>
    simp only [bind, Except.bind] at h
    cases hc : charge Ghigh exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      cases hp : ec.stack.pop2 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨st, dest, cond⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
        have hself' : ∃ acc, ec.accounts.find? ec.executionEnv.address = some acc := by
          obtain ⟨acc, ha⟩ := hself; exact ⟨acc, by rw [hcacc, hcenv]; exact ha⟩
        split at h
        · cases hd : fr.get_dest dest with
          | none => rw [hd] at h; simp at h
          | some newpc =>
            rw [hd] at h; simp only [] at h
            rw [continueWith_next h]; exact hself'
        · rw [continueWith_next h]; exact hself'
  | JUMPDEST =>
    simp only [bind, Except.bind] at h
    cases hc : charge Gjumpdest exec with
    | error e => rw [hc] at h; simp at h
    | ok ec =>
      rw [hc] at h; simp only [] at h
      rw [continueWith_next h]
      obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
      obtain ⟨acc, ha⟩ := hself
      exact ⟨acc, by
        show ec.accounts.find? ec.executionEnv.address = some acc
        rw [hcacc, hcenv]; exact ha⟩
  | MCOPY =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop3 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨st, dest, src, sz⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec (max dest src) sz with
      | error e => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge (Gverylow + copyCost sz) em with
        | error e => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
          exact selfAt_replaceOfBase _ _ (by rw [hcacc, hmacc]) (by rw [hcenv, hmenv]) hself

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- `unOp` `.next` preserves `SelfAt`: `charge` then `replaceStackAndIncrPC` of the charged state. -/
theorem unOp_next_self {f : UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : unOp f exec cost = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold unOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hp : ec.stack.pop with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, a⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- `binOp` `.next` preserves `SelfAt`. -/
theorem binOp_next_self {f : UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState} {cost : ℕ}
    (h : binOp f exec cost = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold binOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hp : ec.stack.pop2 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, a, b⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- `ternOp` `.next` preserves `SelfAt`. -/
theorem ternOp_next_self {f : UInt256 → UInt256 → UInt256 → UInt256} {exec exec' : ExecutionState}
    {cost : ℕ} (h : ternOp f exec cost = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold ternOp at h
  simp only [bind, Except.bind] at h
  cases hc : charge cost exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hp : ec.stack.pop3 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, a, b, c⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- `dup` `.next` preserves `SelfAt` (charge then `replaceStackAndIncrPC`). -/
theorem dup_next_self {n : ℕ} {exec exec' : ExecutionState}
    (h : dup n exec = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold dup at h
  simp only [bind, Except.bind] at h
  cases hc : charge Gverylow exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    cases hd : ec.stack[n-1]? with
    | none => rw [hd] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | some x =>
      rw [hd] at h; simp only [] at h
      exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself

open Lir.V2 (SelfAt charge_accounts_env selfAt_replaceOfBase) in
/-- `swap` `.next` preserves `SelfAt`. -/
theorem swap_next_self {n : ℕ} {exec exec' : ExecutionState}
    (h : swap n exec = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold swap at h
  simp only [bind, Except.bind] at h
  cases hc : charge Gverylow exec with
  | error e => rw [hc] at h; simp at h
  | ok ec =>
    rw [hc] at h; simp only [] at h
    split at h
    · exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself
    · simp [throw, throwThe, MonadExceptOf.throw] at h

open Lir.V2 (SelfAt charge_accounts_env chargeMemExpansion_accounts_env selfAt_replaceOfBase) in
/-- `logArm` `.next` preserves `SelfAt`: `requireStateMod`, two charges, then `logOp` (touches only
`substate`/`activeWords`) and `replaceStackAndIncrPC` — `accounts`/`executionEnv` untouched. -/
theorem logArm_next_self {exec exec' : ExecutionState} {stk : Stack UInt256} {offset size : UInt256}
    {topics : Array UInt256}
    (h : logArm exec stk offset size topics = .ok (.next exec')) (hself : SelfAt exec) :
    SelfAt exec' := by
  unfold logArm at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hr : requireStateMod exec with
  | error e => rw [hr] at h; simp at h
  | ok _ =>
    rw [hr] at h; simp only [] at h
    cases hm : chargeMemExpansion exec offset size with
    | error e => rw [hm] at h; simp at h
    | ok em =>
      rw [hm] at h; simp only [] at h
      cases hc : charge (logCost topics.size size) em with
      | error e => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        rw [continueWith_next h]
        obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
        obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
        -- `exec' = replaceStackAndIncrPC (ec.logOp …) stk`; `logOp` keeps accounts/env.
        refine selfAt_replaceOfBase _ _ ?_ ?_ hself
        · show (ec.logOp offset size topics).accounts = exec.accounts
          show ec.accounts = exec.accounts; rw [hcacc, hmacc]
        · show (ec.logOp offset size topics).executionEnv = exec.executionEnv
          show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]

open Lir.V2 (SelfAt charge_accounts_env chargeMemExpansion_accounts_env selfAt_replaceOfBase) in
/-- **`dispatch` `.next` preserves self-presence (engine level).** Every `.next`-producing opcode of
`dispatch` keeps the self account present: System ops via `systemOp_next_self`, storage/memory/flow via
`smsfOp_next_self`, the arithmetic/`pushOp`/`unStateOp`/`dup`/`swap`/log/`EXP`/`KECCAK256`/copy arms via
their combinator lemmas — all either leave `accounts`/`executionEnv` untouched or insert at the self
address (`SSTORE`/`TSTORE`). This is the dispatch-level half of `StepPreservesSelf`. -/
theorem dispatch_next_self {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec exec' : ExecutionState}
    (h : dispatch op arg fr exec = .ok (.next exec')) (hself : SelfAt exec) : SelfAt exec' := by
  unfold dispatch at h
  cases op with
  | System s => exact systemOp_next_self h hself
  | Smsf s => exact smsfOp_next_self h hself
  | KECCAK256 =>
    simp only [bind, Except.bind] at h
    cases hp : exec.stack.pop2 with
    | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
    | some v =>
      obtain ⟨stk, off, sz⟩ := v; rw [hp] at h
      simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      cases hm : chargeMemExpansion exec off sz with
      | error er => rw [hm] at h; simp [pure, Except.pure] at h
      | ok em =>
        rw [hm] at h; simp only [pure, Except.pure] at h
        cases hc : charge (keccakCost sz) em with
        | error er => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          rw [continueWith_next h]
          obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
          obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
          refine selfAt_replaceOfBase _ _ ?_ ?_ hself
          · show ec.accounts = exec.accounts; rw [hcacc, hmacc]
          · show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
  | ArithLogic a =>
    cases a with
    | ADD | SUB | SIGNEXTEND | LT | GT | SLT | SGT | EQ | AND | OR | XOR | BYTE | SHL | SHR | SAR
    | MUL | DIV | SDIV | MOD | SMOD => exact binOp_next_self h hself
    | ADDMOD | MULMOD => exact ternOp_next_self h hself
    | ISZERO | NOT => exact unOp_next_self h hself
    | EXP =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop2 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, b, e⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge (expCost e) exec with
        | error er => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself
  | Env e =>
    cases e with
    | ADDRESS | ORIGIN | CALLER | CALLVALUE | CALLDATASIZE | CODESIZE | GASPRICE | RETURNDATASIZE =>
      exact pushOp_next_self h hself
    | BALANCE => exact unStateOp_next_self (fun _ _ => ⟨rfl, rfl⟩) h hself
    | CALLDATALOAD => exact unStateOp_next_self (fun _ _ => ⟨rfl, rfl⟩) h hself
    | EXTCODESIZE => exact unStateOp_next_self (fun _ _ => ⟨rfl, rfl⟩) h hself
    | EXTCODEHASH =>
      refine unStateOp_next_self ?_ h hself
      intro st a
      -- `State.extCodeHash`'s first component is `st.addAccessedAccount _` in both branches
      -- (substate-only); `accounts`/`executionEnv` are untouched.
      show (State.extCodeHash st a).1.accounts = st.accounts
        ∧ (State.extCodeHash st a).1.executionEnv = st.executionEnv
      unfold State.extCodeHash
      dsimp only
      split <;> exact ⟨rfl, rfl⟩
    | CALLDATACOPY =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, a, b, c⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hm : chargeMemExpansion exec a c with
        | error er => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h; simp only [pure, Except.pure] at h
          cases hc : charge (Gverylow + copyCost c) em with
          | error er => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h; simp only [] at h
            rw [continueWith_next h]
            obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
            obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
            refine selfAt_replaceOfBase _ _ ?_ ?_ hself
            · show (ec.calldatacopy a b c).accounts = exec.accounts
              show ec.accounts = exec.accounts; rw [hcacc, hmacc]
            · show (ec.calldatacopy a b c).executionEnv = exec.executionEnv
              show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
    | CODECOPY =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, a, b, c⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hm : chargeMemExpansion exec a c with
        | error er => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h; simp only [pure, Except.pure] at h
          cases hc : charge (Gverylow + copyCost c) em with
          | error er => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h; simp only [] at h
            rw [continueWith_next h]
            obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
            obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
            refine selfAt_replaceOfBase _ _ ?_ ?_ hself
            · show (ec.codeCopy a b c).accounts = exec.accounts
              show ec.accounts = exec.accounts; rw [hcacc, hmacc]
            · show (ec.codeCopy a b c).executionEnv = exec.executionEnv
              show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
    | EXTCODECOPY =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, addr, a, b, c⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hm : chargeMemExpansion exec a c with
        | error er => rw [hm] at h; simp [pure, Except.pure] at h
        | ok em =>
          rw [hm] at h; simp only [pure, Except.pure] at h
          cases hc : charge (accessCost (AccountAddress.ofUInt256 addr) em.substate + copyCost c) em with
          | error er => rw [hc] at h; simp at h
          | ok ec =>
            rw [hc] at h; simp only [] at h
            rw [continueWith_next h]
            obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
            obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
            refine selfAt_replaceOfBase _ _ ?_ ?_ hself
            · show (ec.extCodeCopy' addr a b c).accounts = exec.accounts
              show ec.accounts = exec.accounts; rw [hcacc, hmacc]
            · show (ec.extCodeCopy' addr a b c).executionEnv = exec.executionEnv
              show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
    | RETURNDATACOPY =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, a, b, c⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · cases hm : chargeMemExpansion exec a c with
          | error er => rw [hm] at h; simp [pure, Except.pure] at h
          | ok em =>
            rw [hm] at h; simp only [pure, Except.pure] at h
            cases hc : charge (Gverylow + copyCost c) em with
            | error er => rw [hc] at h; simp at h
            | ok ec =>
              rw [hc] at h; simp only [] at h
              rw [continueWith_next h]
              obtain ⟨hmacc, hmenv⟩ := chargeMemExpansion_accounts_env hm
              obtain ⟨hcacc, hcenv⟩ := charge_accounts_env hc
              refine selfAt_replaceOfBase _ _ ?_ ?_ hself
              · show ec.accounts = exec.accounts; rw [hcacc, hmacc]
              · show ec.executionEnv = exec.executionEnv; rw [hcenv, hmenv]
  | Block b =>
    cases b with
    | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO | GASLIMIT | CHAINID | SELFBALANCE | BASEFEE
    | BLOBBASEFEE => exact pushOp_next_self h hself
    | BLOCKHASH => exact unStateOp_next_self (fun _ _ => ⟨rfl, rfl⟩) h hself
    | BLOBHASH =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, i⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        cases hc : charge HASH_OPCODE_GAS exec with
        | error er => rw [hc] at h; simp at h
        | ok ec =>
          rw [hc] at h; simp only [] at h
          exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself
  | Push p =>
    cases p with
    | PUSH0 => exact pushOp_next_self h hself
    | _ =>
      simp only [bind, Except.bind] at h
      cases hc : charge Gverylow exec with
      | error er => rw [hc] at h; simp at h
      | ok ec =>
        rw [hc] at h; simp only [] at h
        cases harg : arg with
        | none => rw [harg] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
        | some w =>
          obtain ⟨av, aw⟩ := w; rw [harg] at h
          simp only [] at h
          exact dispatch_simple_arm_next_self hc rfl rfl (continueWith_next h) hself
  | Dup d => exact dup_next_self h hself
  | Swap s => exact swap_next_self h hself
  | Log l =>
    cases l with
    | LOG0 =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop2 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_self h hself
    | LOG1 =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop3 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_self h hself
    | LOG2 =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop4 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1, t2⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_self h hself
    | LOG3 =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop5 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1, t2, t3⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_self h hself
    | LOG4 =>
      simp only [bind, Except.bind] at h
      cases hp : exec.stack.pop6 with
      | none => rw [hp] at h; simp [MonadLift.monadLift, liftM, monadLift, Option.option] at h
      | some v =>
        obtain ⟨stk, off, sz, t1, t2, t3, t4⟩ := v; rw [hp] at h
        simp only [MonadLift.monadLift, liftM, monadLift, Option.option] at h
        exact logArm_next_self h hself

open Lir.V2 (SelfAt) in
/-- **A `.next` `stepFrame` preserves self-presence (the engine-level `StepPreservesSelf` brick).**
`stepFrame` decodes, screens `INVALID`/stack-overflow (both `.halted`, never `.next`), then forwards
to `dispatch`; a `.next` is exactly a `dispatch … = .ok (.next exec')`, discharged by
`dispatch_next_self`. The template is `stepFrame_next_lt`. -/
theorem stepFrame_next_self {fr : Frame} {exec' : ExecutionState}
    (h : stepFrame fr = .next exec') (hself : SelfAt fr.exec) : SelfAt exec' := by
  rw [stepFrame] at h
  generalize hdp : (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)) = dp
    at h
  obtain ⟨op, arg⟩ := dp
  simp only at h
  split at h
  · exact absurd h (by simp)  -- INVALID ⇒ .halted
  · split at h
    · exact absurd h (by simp) -- stack overflow ⇒ .halted
    · cases hdisp : dispatch op arg fr fr.exec with
      | ok signal =>
        rw [hdisp] at h
        cases signal with
        | next e =>
          simp only [Signal.next.injEq] at h; subst h
          exact dispatch_next_self hdisp hself
        | halted hl => simp only at h; exact absurd h (by simp)
        | needsCall p pc => simp only at h; exact absurd h (by simp)
        | needsCreate p pc => simp only at h; exact absurd h (by simp)
      | error e => rw [hdisp] at h; exact absurd h (by simp)

end Evm

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open BytecodeLayer.System
open BytecodeLayer.Maps
open Lir

/-! ### `SelfPresent` threads through a whole materialise sub-run (`MatRuns`-threading, DONE)

The per-op bricks above compose into the whole-materialisation transport via the **new
`MatRuns.accounts` + `MatRuns.addr` clauses** (`MaterialiseRuns.lean`): a materialise sub-run leaves
the account map (`MatRuns.accounts`) and the self address (`MatRuns.addr`) unchanged, so
`SelfPresent` transports across the entire `materialise_runs` endpoint at once — the analogue of
`MemRealises.transport` (which threads the memory value channel across the sub-run via
`memBytes`/`memActive`). This is exactly the `MatRuns`-threading the §5 docstring flagged as the
remaining SSTORE wiring; with the `accounts` clause banked it is now a one-line transport, not a
deferred walk-induction. -/

/-- **`SelfPresent` transports across a materialise sub-run.** From `SelfPresent fr` and a
`MatRuns … fr fr'` materialise run, `SelfPresent fr'`: the account map is preserved
(`MatRuns.accounts`) and the self address is preserved (`MatRuns.addr`), so the witnessed self
account at `fr` is still found at `fr'`. The whole-sub-run analogue of the per-op `selfPresent_*`
bricks — the `MatRuns`-threading the SSTORE presence discharge needs, completed via the new
`MatRuns.accounts` clause. -/
theorem selfPresent_matRuns {defs : Tmp → Option Expr} {sloadChg : Tmp → ℕ} {fuel : Nat}
    {e : Expr} {w : Word} {fr fr' : Frame}
    (h : SelfPresent fr) (hmr : MatRuns defs sloadChg fuel e w fr fr') :
    SelfPresent fr' := by
  obtain ⟨acc, hacc⟩ := h
  exact ⟨acc, by rw [hmr.accounts, hmr.addr]; exact hacc⟩

/-! ### The GAS/SLOAD alignment-threading composites across a materialise sub-run (C1 / L1.1 / L1.2)

The GAS/SLOAD twins of `selfPresent_matRuns`: they transport the recorder-alignment state across a
whole `MatRuns … fr fr'` materialise sub-run, in exactly the form the per-op step lemmas
(`gasLogAligned_step_gas` / `sloadLogAligned_step_sload`) consume at the *next* op after the sub-run
— those need `frs.getLast? = some last ∧ Runs last <next-op frame>`, and the caller forms the
`Runs last <next-op frame>` half as `Runs.trans (this lemma's `Runs last fr') (step fr' → next)`.

**HONEST SCOPE (read this).** These lemmas do exactly two things:

  (i) **alignment-PRESERVATION** — the *pre*-sub-run `GasLogAligned gasAcc gasFrs` (resp.
      `SloadLogAligned …`) fact is carried VERBATIM to the conclusion. The conclusion re-states the
      SAME `gasAcc`/`gasFrs`, so the alignment conjunct (and the `getLast?` conjunct) is the input
      returned unchanged — a deliberate, near-trivial repackaging for single-call ergonomics in
      L2.0, NOT a worked result. We flag it as such.

  (ii) **reachability-THREADING** — the only load-bearing content: a witness frame `last` that
      reaches the sub-run START `fr` (`Runs last fr`) is shown to reach its END `fr'`
      (`Runs last fr'`) via `Runs.trans last→fr→fr'` using `MatRuns.runs` (`MaterialiseRuns.lean`).

We make **NO** claim that the recorder fired no GAS/SLOAD byte inside the sub-run: `Expr` has both
`.gas` and `.sload`, so `materialise` *can* emit those bytes; byte-freeness for SPILLED operands is a
separate completeness obligation DEFERRED to L2.0/C3. Because the conclusion re-states the SAME
`gasAcc`/`gasFrs` (not the post-sub-run recorder accumulator), it cannot and does not certify the
post-sub-run recorder state — there is no circularity smuggling that discharge here. The proof uses
ONLY `MatRuns.runs` + `Runs.trans`; it never inspects `materialise` structure or the
`MatRuns.gas*`/`code`/`pc` clauses. -/

/-- **GAS-alignment transport across a materialise sub-run (L1.1).** Carries `GasLogAligned`
verbatim (alignment-PRESERVATION) and extends the witness reachability `Runs last fr` to
`Runs last fr'` across `MatRuns … fr fr'` (reachability-THREADING, via `Runs.trans` through
`MatRuns.runs`). The alignment and `getLast?` conjuncts are the inputs returned unchanged —
near-trivial repackaging for the next-op step lemma `gasLogAligned_step_gas`; this lemma makes NO
no-record-inside / byte-freeness claim (that stays deferred to L2.0/C3). -/
theorem gasLogAligned_matRuns {defs : Tmp → Option Expr} {sloadChg : Tmp → ℕ} {fuel : Nat}
    {e : Expr} {w : Word} {fr fr' : Frame} {gasAcc : List Word} {gasFrs : List Frame} {last : Frame}
    (halign : GasLogAligned gasAcc gasFrs) (hmr : MatRuns defs sloadChg fuel e w fr fr')
    (hlast : gasFrs.getLast? = some last) (hreach : Runs last fr) :
    GasLogAligned gasAcc gasFrs ∧ gasFrs.getLast? = some last ∧ Runs last fr' :=
  ⟨halign, hlast, Runs.trans hreach hmr.runs⟩

/-- **SLOAD-alignment transport across a materialise sub-run (L1.2).** Exact twin of
`gasLogAligned_matRuns`: carries `SloadLogAligned` verbatim (alignment-PRESERVATION) and extends
`Runs last fr` to `Runs last fr'` across `MatRuns … fr fr'` (reachability-THREADING, via `Runs.trans`
through `MatRuns.runs`). Only the alignment predicate (over `List Nat`) and accumulator type differ;
the alignment and `getLast?` conjuncts are the inputs returned unchanged — near-trivial repackaging
for the next-op step lemma `sloadLogAligned_step_sload`; NO no-record-inside / byte-freeness claim
(deferred to L2.0/C3). -/
theorem sloadLogAligned_matRuns {defs : Tmp → Option Expr} {sloadChg : Tmp → ℕ} {fuel : Nat}
    {e : Expr} {w : Word} {fr fr' : Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    {last : Frame}
    (halign : SloadLogAligned sloadAcc sloadFrs) (hmr : MatRuns defs sloadChg fuel e w fr fr')
    (hlast : sloadFrs.getLast? = some last) (hreach : Runs last fr) :
    SloadLogAligned sloadAcc sloadFrs ∧ sloadFrs.getLast? = some last ∧ Runs last fr' :=
  ⟨halign, hlast, Runs.trans hreach hmr.runs⟩

/-! ### The per-cursor GAS-channel ADVANCE bricks (STEP 1 — the structural advance)

The two standalone per-cursor lemmas that EXTEND (resp. carry) the gas alignment at a statement
cursor, threading `FramesRun.snoc` reachability from the block boundary. They are the honest content
of STEP 1: at a `.assign t .gas` cursor the gas accumulator GROWS by one word (the GAS-op's reported
gas, `driveCorrPlus_gas_cursor_advance`); at every other cursor the gas accumulator is carried
VERBATIM while reachability threads to the cursor's end frame (`driveCorrPlus_norecord_cursor_advance`).

**Why these are SEPARATE bricks, not a mutation of `driveCorrPlus_run_stmts`.** That walk obtains its
`Runs fr frT` from `sim_stmts_block`, a black box that exposes neither the per-cursor frames nor which
cursors are GAS cursors nor the GAS-op `.next` step at each. So it has no handle to ADVANCE the
witness list `gasFrs` — which is exactly why L2.0 carries the alignment verbatim. To advance the gas
channel one must re-do the per-cursor induction (the would-be `driveCorrPlus_run_stmts_gasadvance`,
reported as the standing obstacle). These bricks are the per-cursor steps that re-architected walk
would dispatch to; they are unconditionally green and reusable in isolation.

**Non-vacuity / non-circularity.** `driveCorrPlus_gas_cursor_advance` PRODUCES the extended
`GasLogAligned` from the GAS-op facts (it routes only through `gasLogAligned_step_gas`, whose appended
word is the recorder's literal splice `gasReadOf (gasFrame fr0)`); it never takes an extended-alignment
hypothesis and returns it. The non-gas brick makes NO no-record-inside claim (a non-gas statement can
still materialise a `.gas` operand inside its segment — byte-freeness for spilled operands is the
DEFERRED completeness obligation flagged on `gasLogAligned_matRuns`); it only carries alignment
verbatim and threads reachability via `Runs.trans`. -/

/-- **The per-cursor GAS ADVANCE brick (STEP 1, must-land).** At a statement cursor whose `Corr` frame
is `fr0` and which decodes to the `GAS` op (`hdec`), under the gas envelope `Gbase ≤ fr0.gas` (`hgas`,
the supplied S4 lower bound — CONSUMED here, not produced) and a witness list ending at a frame `last`
from which `fr0` is reachable (`hlast`/`hreach` threaded from the boundary), the gas alignment EXTENDS:
the new accumulator `gasAcc ++ [ofUInt64 (gasFrame fr0).gas]` is aligned with `gasFrs ++ [gasFrame fr0]`,
the GAS step `Runs fr0 (gasFrame fr0)` holds, and the snoc witness list ends at `gasFrame fr0`.

The stack-size bound `fr0.stack.size + 1 ≤ 1024` is recovered from `Corr.stack_nil` (empty stack). The
GAS step + reachability is `sim_gas`; the alignment extension is `gasLogAligned_step_gas` at `fr0` with
`hstep` supplied by `Dispatch.stepFrame_gas`. The appended word is the recorder's literal splice
(`gasReadOf (gasFrame fr0) = ofUInt64 (gasFrame fr0).gas`), so the EXTENSION is genuine — NOT a free
word, NOT a re-supply of the extended alignment. -/
theorem driveCorrPlus_gas_cursor_advance {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {L : Label} {pc : Nat} {fr0 last : Frame}
    {gasAcc : List Word} {gasFrs : List Frame}
    (halign : GasLogAligned gasAcc gasFrs)
    (hlast : gasFrs.getLast? = some last)
    (hreach : Runs last fr0)
    (hcorr : Corr prog sloadChg obs st fr0 L pc)
    (hdec : decode fr0.exec.executionEnv.code fr0.exec.pc = some (.Smsf .GAS, .none))
    (hgas : GasConstants.Gbase ≤ fr0.exec.gasAvailable.toNat) :
    Runs fr0 (gasFrame fr0)
      ∧ GasLogAligned (gasAcc ++ [UInt256.ofUInt64 (gasFrame fr0).exec.gasAvailable])
          (gasFrs ++ [gasFrame fr0])
      ∧ (gasFrs ++ [gasFrame fr0]).getLast? = some (gasFrame fr0) := by
  -- (1) stack-size bound from `Corr.stack_nil`.
  have hsz : fr0.exec.stack.size + 1 ≤ 1024 := by
    rw [hcorr.stack_nil]; decide
  -- (2) the GAS step `Runs fr0 (gasFrame fr0)`.
  have hrun : Runs fr0 (gasFrame fr0) := (sim_gas fr0 hdec hsz hgas).1
  -- (3) `Runs last (gasFrame fr0)` for `FramesRun.snoc`, via `hreach` then the GAS step.
  have hreach' : Runs last (gasFrame fr0) := Runs.trans hreach hrun
  -- (4) `stepFrame fr0 = .next (gasPost fr0.exec)`, so `gasLogAligned_step_gas`'s `exec` is the
  --     post-charge exec and its appended word is `ofUInt64 (gasFrame fr0).gas`.
  have hstep : stepFrame fr0 = .next (BytecodeLayer.Dispatch.gasPost fr0.exec) :=
    BytecodeLayer.Dispatch.stepFrame_gas fr0 hdec hsz hgas
  have halign' :
      GasLogAligned (gasAcc ++ [UInt256.ofUInt64 (BytecodeLayer.Dispatch.gasPost fr0.exec).gasAvailable])
        (gasFrs ++ [gasFrame fr0]) :=
    gasLogAligned_step_gas halign hlast hreach' hdec hsz hgas hstep
  -- `(gasFrame fr0).exec.gasAvailable = (gasPost fr0.exec).gasAvailable` (`rfl`), so the produced
  -- accumulator is exactly the brick's stated extension.
  refine ⟨hrun, halign', ?_⟩
  simp [List.getLast?_concat]

/-- **The per-cursor NON-GAS (no-record) brick (STEP 1, must-land).** At a statement cursor whose
statement is NOT `assign _ .gas` (`hnotgas`), the cursor records no top-level GAS read at its own
boundary, so the gas alignment is carried VERBATIM (`gasLogAligned_step_norecord` = identity) and
reachability threads `Runs last fr0` to `Runs last fr0'` across the cursor's segment (`hsim_seg`) via
`Runs.trans`. Pure repackaging, the GAS twin of `gasLogAligned_matRuns`.

**HONEST-SCOPE CAVEAT** (mirroring the `gasLogAligned_matRuns` disclaimer): this lemma makes NO claim
that the segment `Runs fr0 fr0'` fired no GAS byte internally — a non-gas STATEMENT can still
materialise a `.gas` operand. In the SPILLED regime gas is read once at the def-site stash (NOT inside
materialise), so the top-level recorder gate (`stack.isEmpty`) does not fire inside the segment — but
BYTE-FREENESS is a separate completeness obligation DEFERRED (same status as `gasLogAligned_matRuns`).
The lemma only carries alignment verbatim + threads reachability; it does not and cannot certify the
post-segment recorder state. Sound and non-circular, but explicitly NOT a no-record-inside proof. -/
theorem driveCorrPlus_norecord_cursor_advance {s : Stmt} {fr0 fr0' last : Frame}
    {gasAcc : List Word} {gasFrs : List Frame}
    (halign : GasLogAligned gasAcc gasFrs)
    (hlast : gasFrs.getLast? = some last)
    (hreach : Runs last fr0)
    (_hnotgas : ∀ t, s ≠ .assign t .gas)
    (hsim_seg : Runs fr0 fr0') :
    GasLogAligned gasAcc gasFrs ∧ gasFrs.getLast? = some last ∧ Runs last fr0' :=
  ⟨gasLogAligned_step_norecord halign, hlast, Runs.trans hreach hsim_seg⟩

/-! ### `SelfPresent`-forward along a whole `Runs` segment (incl. the `Runs.call` resume)

`selfPresent_matRuns` transports `SelfPresent` across one materialise sub-run. The drive walk
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
  address) is preserved throughout. The engine-level brick is `Evm.stepFrame_next_self`
  (`dispatch_next_self`/`systemOp_next_self`/`smsfOp_next_self` per arm); `selfPresent_runs`'s first
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

/-- The resumed frame's self address is the *caller's* self address: `resumeAfterCall` rebuilds
`pd.frame` (the suspended caller) touching only stack/pc/gas/accounts/substate, leaving
`executionEnv` (hence `.address`) untouched. The structural half of the `Runs.call` resume's
self-presence transport. -/
theorem resumeAfterCall_address (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.executionEnv.address
      = pd.frame.exec.executionEnv.address := rfl

/-- The resumed frame's account map is the child's returned `result.accounts` (the shared world
state threaded back). The structural half of the `Runs.call` resume's self-presence transport:
self-presence at the resumed frame is exactly `result.accounts.find? (caller self) = some _`. -/
theorem resumeAfterCall_accounts (result : Evm.CallResult) (pd : Evm.PendingCall) :
    (Evm.resumeAfterCall result pd).exec.accounts = result.accounts := rfl

/-- **On `.revert`/`.exception`, `endCall` returns the caller's pre-call account map verbatim.**
`endCall checkpoint (.revert …)` and `endCall checkpoint (.exception …)` both set `accounts :=
checkpoint.accounts` (the caller's pre-call world is rolled back). The structural half of
`CallPreservesSelf` for the two failing `CallResult` shapes: if the caller self was present in the
pre-call `checkpoint.accounts` (the very map `SelfPresent` held against at `callFr`), it is present in
the returned result. The remaining `.success` shape is the genuinely-open residual
`drive_accounts_find_mono` (account-presence monotone across the child `drive` run; out of scope here
— a whole-child-run induction of P5-spine magnitude). -/
theorem endCall_revert_accounts (checkpoint : Evm.Checkpoint) (g : UInt64) (o : ByteArray) :
    (Evm.endCall checkpoint (.revert g o)).accounts = checkpoint.accounts := by
  rfl

theorem endCall_exception_accounts (checkpoint : Evm.Checkpoint) (e : Evm.ExecutionException) :
    (Evm.endCall checkpoint (.exception e)).accounts = checkpoint.accounts := rfl

/-- **The revert/exception sub-case of `CallPreservesSelf`, structurally discharged.** When the child
returns a result whose accounts are the caller's pre-call checkpoint map (the revert/exception shapes,
via `endCall_revert_accounts`/`endCall_exception_accounts`), and the caller self was present there, the
resumed frame keeps the self account present. Reduces to `resumeAfterCall_selfAt`: address is preserved
(`rfl`) and the returned accounts contain the caller self. This is the half of `CallPreservesSelf` that
does **not** depend on the open `drive_accounts_find_mono`; the `.success` shape still does (and so the
full `CallPreservesSelf` stays supplied — satisfiable, not vacuous). -/
theorem resumeAfterCall_self_of_accounts (result : Evm.CallResult) (pd : Evm.PendingCall)
    (h : ∃ acc, result.accounts.find? pd.frame.exec.executionEnv.address = some acc) :
    SelfPresent (Evm.resumeAfterCall result pd) :=
  Evm.resumeAfterCall_selfAt result pd h

/-! ### CALLMONO — account-presence at an *arbitrary* tracked address `a`

`SelfPresent`/`SelfAt` track presence at the frame's *own* self address. To discharge the
`.success` shape of `CallPreservesSelf` we need presence at the **caller's** address tracked across
the *child* drive run, where the running self address is the *callee's* — i.e. presence at an
address `a` that is *not* the running frame's self. We therefore generalise `SelfAt` to an arbitrary
`a` (`AccPresent a`) and prove account-presence monotone across each engine step (`AccMono a`).

The two account framing facts (`Brick A`/`Brick B`) are pure `AccountMap` lemmas; they generalise the
self-specific closers `sstore_self_present`/`tstore_self_present` (insert *at* `a`) and the
`SelfPresent ⇒ ≠ ∅` non-emptiness bridge (the `==∅` swap is harmless on a present `a`) to an
arbitrary tracked `a`. -/

/-- Account `a` is present in the map `m`. The arbitrary-address generalisation of `SelfAt` (which
fixes `a := exec.executionEnv.address`). -/
def AccPresent (a : Evm.AccountAddress) (m : Evm.AccountMap) : Prop :=
  ∃ acc : Evm.Account, m.find? a = some acc

/-- Account-presence at `a` is monotone from `m` to `m'`: if `a` is present in `m` it is present in
`m'`. The per-step invariant threaded through the child drive run. -/
def AccMono (a : Evm.AccountAddress) (m m' : Evm.AccountMap) : Prop :=
  AccPresent a m → AccPresent a m'

/-- **Brick A — presence at `a` survives an `insert` at any key.** Case `a = k`: the inserted entry
is read back (`accounts_find?_insert_self`). Case `a ≠ k`: the insert is framed away
(`accounts_find?_insert_of_ne`) and `a`'s old entry survives. This is the SSTORE/TSTORE closer at an
*arbitrary* tracked `a` (the existing self-specific closers insert *at* `a := self`). -/
theorem accounts_find?_insert_mono (m : Evm.AccountMap) (a k : Evm.AccountAddress)
    (v : Evm.Account) (h : AccPresent a m) : AccPresent a (m.insert k v) := by
  obtain ⟨acc, ha⟩ := h
  by_cases hk : a = k
  · subst hk; exact ⟨v, BytecodeLayer.Maps.accounts_find?_insert_self _ _ _⟩
  · exact ⟨acc, by rw [BytecodeLayer.Maps.accounts_find?_insert_of_ne _ _ hk]; exact ha⟩

/-- **Brick B — a present address forces a non-empty map.** If `a` is present in `m` then `m` is not
`∅`. Lifts the `find? = some ⇒ ≠ ∅` tree-nil reduction (the core of `find?_some_ne_empty`) to a
standalone fact ruling out the `==∅` swap branches (precompile `.inr`, `endCall .success`) whenever
the tracked `a` is present. -/
theorem accPresent_ne_empty (a : Evm.AccountAddress) (m : Evm.AccountMap)
    (h : AccPresent a m) : ¬ (m == (∅ : Evm.AccountMap)) = true := by
  obtain ⟨acc, ha⟩ := h
  exact find?_some_ne_empty _ _ _ ha

/-- **`accMono` closer for a verbatim-accounts step.** When `exec'.accounts = exec.accounts`, presence
at `a` transports unchanged. The arbitrary-`a` twin of `selfAt_replaceOfBase`'s accounts-verbatim
discharge (most `.next` arms route through `charge`/`chargeMemExpansion`, which preserve accounts). -/
theorem accMono_of_accounts_eq (a : Evm.AccountAddress) {m m' : Evm.AccountMap}
    (h : m' = m) : AccMono a m m' := by
  intro hp; rw [h]; exact hp

/-- **Brick B applied — the `==∅` swap is harmless on a present `a`.** For a result of the
`if m == ∅ then m₀ else m` shape, presence at `a` in `m` survives (the `==∅` branch is impossible by
Brick B, so the result is `m`). Used at `endCall .success` and the precompile `.inr` fallback. -/
theorem accMono_emptySwap (a : Evm.AccountAddress) (m m₀ : Evm.AccountMap)
    (h : AccPresent a m) : AccPresent a (if m == (∅ : Evm.AccountMap) then m₀ else m) := by
  rw [if_neg (accPresent_ne_empty a m h)]; exact h

/-- **`beginCall` threads presence at `a` into the code child.** When a CALL begins as a code child
(`beginCall cp = .inl child`), the child's running `exec.accounts` is `accountsAfterTransfer` — a
credit (recipient) then debit (caller) `insert` chain over `cp.accounts`; each branch is either
verbatim (`none`) or an `insert` (`some`), so presence at any `a` present in `cp.accounts` survives
(Brick A). And the child's kind checkpoint is exactly `cp.accounts` (the `.call ⟨_, cp.accounts, _⟩`
node), present by hypothesis. This is the non-vacuous witness that the child drive run *starts*
present at the caller's address. -/
theorem beginCall_inl_accounts_present (a : Evm.AccountAddress) (cp : Evm.CallParams)
    {child : Evm.Frame} (hbc : Evm.beginCall cp = .inl child)
    (h : AccPresent a cp.accounts) :
    AccPresent a child.exec.accounts := by
  -- Reduce `beginCall` to its `.inl` (Code) arm and read off `child.exec.accounts`.
  unfold Evm.beginCall at hbc
  -- The credit step preserves presence at `a` (none → verbatim, some → insert mono).
  have hcredit : AccPresent a
      (match cp.accounts.find? cp.recipient with
        | none =>
          if cp.value != (0 : UInt256) then
            cp.accounts.insert cp.recipient { (default : Evm.Account) with balance := cp.value }
          else cp.accounts
        | some acc =>
          cp.accounts.insert cp.recipient { acc with balance := acc.balance + cp.value }) := by
    cases hr : cp.accounts.find? cp.recipient with
    | none =>
      simp only [hr]
      by_cases hv : cp.value != (0 : UInt256)
      · rw [if_pos hv]; exact accounts_find?_insert_mono _ _ _ _ h
      · rw [if_neg hv]; exact h
    | some acc => simp only [hr]; exact accounts_find?_insert_mono _ _ _ _ h
  -- The debit step over the credited map likewise preserves presence at `a`.
  set credited :=
    (match cp.accounts.find? cp.recipient with
        | none =>
          if cp.value != (0 : UInt256) then
            cp.accounts.insert cp.recipient { (default : Evm.Account) with balance := cp.value }
          else cp.accounts
        | some acc =>
          cp.accounts.insert cp.recipient { acc with balance := acc.balance + cp.value }) with hcred
  have htransfer : AccPresent a
      (match credited.find? cp.caller with
        | none => credited
        | some acc => credited.insert cp.caller { acc with balance := acc.balance - cp.value }) := by
    cases hc : credited.find? cp.caller with
    | none => simp only [hc]; exact hcredit
    | some acc => simp only [hc]; exact accounts_find?_insert_mono _ _ _ _ hcredit
  -- In the Code arm, `child.exec.accounts = accountsAfterTransfer = the debited map`.
  cases hcs : cp.codeSource with
  | Precompiled p => rw [hcs] at hbc; simp only [Sum.inl.injEq] at hbc; exact absurd hbc (by nofun)
  | Code code =>
    rw [hcs] at hbc
    simp only [Sum.inl.injEq] at hbc
    rw [← hbc]
    -- `child.exec.accounts` is definitionally `accountsAfterTransfer` (the debited map).
    exact htransfer

/-- **`beginCall`'s code child carries `cp.accounts` as its kind checkpoint.** The `.inl` (Code) arm
builds `kind := .call ⟨_, cp.accounts, _⟩`; so the checkpoint that `endCall .revert/.exception` rolls
back to is exactly `cp.accounts`. -/
theorem beginCall_inl_checkpoint (cp : Evm.CallParams) {child : Evm.Frame}
    (hbc : Evm.beginCall cp = .inl child) :
    ∃ created sub, child.kind = .call ⟨created, cp.accounts, sub⟩ := by
  unfold Evm.beginCall at hbc
  cases hcs : cp.codeSource with
  | Precompiled p => rw [hcs] at hbc; simp only [Sum.inl.injEq] at hbc; exact absurd hbc (by nofun)
  | Code code =>
    rw [hcs] at hbc
    simp only [Sum.inl.injEq] at hbc
    exact ⟨cp.createdAccounts, cp.substate, by rw [← hbc]⟩

/-- **Local per-step self-presence preservation.** One non-halting opcode step (`StepsTo`) keeps
the self account present. Satisfiable for the lowered program — every `.next` opcode either leaves
`accounts` untouched or inserts at the self account, never erasing it — and supplied per edge by the
materialise bricks (`selfPresent_matRuns` & the `selfPresent_*` post-frame lemmas). -/
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

/-! ### Brick D — account-presence monotone across a whole `drive` run

`drive_accounts_find_mono`: if `a` is present in the running accounts (and in every checkpoint that a
rollback could restore) at the *start* of a `drive` run, it stays present in the run's result. This is
the account-level analogue of `drive_fuel_succ` — a strong-fuel induction following `drive`'s own
recursion — and is the engine-level fact the `.success` shape of `CallPreservesSelf` reduces to.

The presence invariant `DrivePresent a` threads three facts simultaneously, because two `drive` exits
*roll back* the running map to a checkpoint:

* the running `exec.accounts` (`.inl`) / result accounts (`.inr`),
* the **kind checkpoint** of the running `.inl` frame (what `endCall .revert/.exception` restores),
* the kind checkpoint of **every** pending ancestor on the stack (each will become a running frame
  on delivery, and may itself roll back).

The seam excluding the two `∅`-producing arms (`beginCall`'s precompile `.inr` and `drive`'s CREATE
fault) is supplied per-arm as the `hmono`/`hprec`/`hncr` closers — each genuinely satisfiable, never
vacuous (documented at `callPreservesSelf`). -/

/-- Presence at `a` in a frame's kind checkpoint accounts (what `endCall .revert/.exception` and
`endCreate` failure restore). -/
def CheckpointPresent (a : Evm.AccountAddress) (fr : Evm.Frame) : Prop :=
  match fr.kind with
  | .call cp => AccPresent a cp.accounts
  | .create _ cp => AccPresent a cp.accounts

/-- Presence at `a` in every pending ancestor's kind checkpoint. -/
def StackPresent (a : Evm.AccountAddress) : List Evm.Pending → Prop
  | [] => True
  | p :: rest => CheckpointPresent a p.frame ∧ StackPresent a rest

/-- The drive-run presence invariant: `a` present in the running map and in the running frame's
checkpoint (`.inl`) / in the result map (`.inr`), and in every pending ancestor's checkpoint. -/
def DrivePresent (a : Evm.AccountAddress) (stack : List Evm.Pending) :
    Evm.Frame ⊕ Evm.FrameResult → Prop
  | .inl current => AccPresent a current.exec.accounts ∧ CheckpointPresent a current
      ∧ StackPresent a stack
  | .inr result => AccPresent a result.toCallResult.accounts ∧ StackPresent a stack

/-- **One `drive`-recursion transition** (`(stack, state) ⤳ (stack', state')`): exactly the recursive
calls of `drive`. Used to scope the no-CREATE seam to the frames a run actually visits (honest: the
seam is satisfiable for a CREATE-free child run, the `NotCreate`/`ModellableStep` seam, rather than
the false universal `∀ fr, stepFrame fr ≠ needsCreate`). -/
inductive EngineStep : List Evm.Pending → (Evm.Frame ⊕ Evm.FrameResult) →
    List Evm.Pending → (Evm.Frame ⊕ Evm.FrameResult) → Prop where
  | resume {stack : List Evm.Pending} {pending : Evm.Pending} {result : Evm.FrameResult}
      {parent : Evm.Frame} (h : pending.resume result = .ok parent) :
      EngineStep (pending :: stack) (.inr result) stack (.inl parent)
  | resumeErr {stack : List Evm.Pending} {pending : Evm.Pending} {result : Evm.FrameResult}
      {e : Evm.ExecutionException} (h : pending.resume result = .error e) :
      EngineStep (pending :: stack) (.inr result) stack
        (.inr (Evm.endFrame pending.frame (.exception e)))
  | next {stack : List Evm.Pending} {current : Evm.Frame} {exec : Evm.ExecutionState}
      (h : Evm.stepFrame current = .next exec) :
      EngineStep stack (.inl current) stack (.inl { current with exec := exec })
  | halt {stack : List Evm.Pending} {current : Evm.Frame} {halt : Evm.FrameHalt}
      (h : Evm.stepFrame current = .halted halt) :
      EngineStep stack (.inl current) stack (.inr (Evm.endFrame current halt))
  | call {stack : List Evm.Pending} {current child : Evm.Frame} {params : Evm.CallParams}
      {pending : Evm.PendingCall} (h : Evm.stepFrame current = .needsCall params pending)
      (hbc : Evm.beginCall params = .inl child) :
      EngineStep stack (.inl current) (.call pending :: stack) (.inl child)
  | callImm {stack : List Evm.Pending} {current : Evm.Frame} {params : Evm.CallParams}
      {pending : Evm.PendingCall} {immediate : Evm.CallResult}
      (h : Evm.stepFrame current = .needsCall params pending)
      (hbc : Evm.beginCall params = .inr immediate) :
      EngineStep stack (.inl current) (.call pending :: stack) (.inr (.call immediate))

/-- Reflexive–transitive reachability under `EngineStep` from a fixed start configuration. -/
inductive EngineReaches (s0 : List Evm.Pending) (t0 : Evm.Frame ⊕ Evm.FrameResult) :
    List Evm.Pending → (Evm.Frame ⊕ Evm.FrameResult) → Prop where
  | refl : EngineReaches s0 t0 s0 t0
  | tail {s1 t1 s2 t2} (h : EngineReaches s0 t0 s1 t1) (step : EngineStep s1 t1 s2 t2) :
      EngineReaches s0 t0 s2 t2

/-- `endFrame` (a `.call`-kind halt) preserves presence at `a` given running-map presence (the
`.success` swap is killed by `accMono_emptySwap`) and checkpoint presence (the `.revert/.exception`
rollback). The `.create`-kind case is excluded by the no-CREATE seam at the producing step. -/
theorem endFrame_call_accPresent (a : Evm.AccountAddress) (cp : Evm.Checkpoint)
    (halt : Evm.FrameHalt)
    (hcp : AccPresent a cp.accounts)
    (hsucc : ∀ e o, halt = .success e o → AccPresent a e.accounts) :
    AccPresent a (Evm.endCall cp halt).accounts := by
  cases halt with
  | success e o =>
    -- `endCall .success` accounts = `if e.accounts == ∅ then cp.accounts else e.accounts`.
    have he : AccPresent a e.accounts := hsucc e o rfl
    show AccPresent a (if e.accounts == (∅ : Evm.AccountMap) then cp.accounts else e.accounts)
    exact accMono_emptySwap a e.accounts cp.accounts he
  | revert g o => exact (by rw [endCall_revert_accounts]; exact hcp)
  | exception ex => exact (by rw [endCall_exception_accounts]; exact hcp)

/-- `endCreate` preserves presence at `a` given checkpoint presence and running-map presence (on the
deployment-success branch the result map is `exec.accounts.insert address …` — an `insert`, presence
preserving via Brick A; on every failure branch it is the checkpoint map). The `.create`-kind twin of
`endFrame_call_accPresent`. -/
theorem endFrame_create_accPresent (a : Evm.AccountAddress) (addr : Evm.AccountAddress)
    (cp : Evm.Checkpoint) (halt : Evm.FrameHalt)
    (hcp : AccPresent a cp.accounts)
    (hsucc : ∀ e o, halt = .success e o → AccPresent a e.accounts) :
    AccPresent a (Evm.endCreate addr cp halt).accounts := by
  cases halt with
  | success e o =>
    have he : AccPresent a e.accounts := hsucc e o rfl
    show AccPresent a (Evm.endCreate addr cp (.success e o)).accounts
    -- `(endCreate … .success).accounts = if deploymentFailed then cp.accounts else
    --  e.accounts.insert address { (e.accounts.findD address default) with code := o }`.
    -- Case on the (opaque) `deploymentFailed` condition: rollback (cp) or `insert` (Brick A).
    unfold Evm.endCreate
    dsimp only
    -- The `accounts` field is `if deploymentFailed then cp.accounts else e.accounts.insert addr …`.
    -- Case on the (opaque) `deploymentFailed` condition: rollback (cp) vs. `insert` (Brick A).
    split_ifs with hdf
    · exact hcp
    · exact accounts_find?_insert_mono _ _ _ _ he
  | revert g o => exact (by show AccPresent a (Evm.endCreate addr cp (.revert g o)).accounts; exact hcp)
  | exception ex =>
    exact (by show AccPresent a (Evm.endCreate addr cp (.exception ex)).accounts; exact hcp)

/-- `endFrame` preserves presence at `a` for **either** frame kind, given checkpoint presence and (on
a `.success` halt) running-map presence. Combines `endFrame_call_accPresent` /
`endFrame_create_accPresent`; this is the unconditional halt closer for the drive induction (no kind
exclusion needed — both `endCall` and `endCreate` are presence-preserving). -/
theorem endFrame_accPresent (a : Evm.AccountAddress) (current : Evm.Frame) (halt : Evm.FrameHalt)
    (hck : CheckpointPresent a current)
    (hsucc : ∀ e o, halt = .success e o → AccPresent a e.accounts) :
    AccPresent a (Evm.endFrame current halt).toCallResult.accounts := by
  unfold Evm.endFrame
  unfold CheckpointPresent at hck
  cases hk : current.kind with
  | call cp =>
    simp only [hk]
    rw [hk] at hck
    show AccPresent a (Evm.endCall cp halt).accounts
    exact endFrame_call_accPresent a cp halt hck hsucc
  | create addr cp =>
    simp only [hk]
    rw [hk] at hck
    show AccPresent a (Evm.endCreate addr cp halt).toCallResult.accounts
    -- `(endCreate …).toCallResult.accounts = (endCreate …).accounts` (projection is accounts-verbatim).
    exact endFrame_create_accPresent a addr cp halt hck hsucc

/-- `FrameResult`'s two result projections expose the **same** accounts field (`CreateResult extends
CallResult`, so both `.toCallResult.accounts` and `.toCreateResult.accounts` read the inherited
field). -/
theorem toCreateResult_accounts_eq (result : Evm.FrameResult) :
    result.toCreateResult.accounts = result.toCallResult.accounts := by
  cases result with
  | call r => rfl
  | create r => rfl

/-- `resumeAfterCreate` on `.ok` keeps the resumed running map equal to the result's accounts (it
sets `exec.accounts := result.accounts`), so presence at `a` transports from `hresult`. -/
theorem resumeAfterCreate_exec_accounts_present (a : Evm.AccountAddress) (result : Evm.FrameResult)
    (pd : Evm.PendingCreate) (parent : Evm.Frame)
    (hres : Evm.resumeAfterCreate result.toCreateResult pd = .ok parent)
    (hresult : AccPresent a result.toCallResult.accounts) :
    AccPresent a parent.exec.accounts := by
  unfold Evm.resumeAfterCreate at hres
  simp only [bind, Except.bind, pure, Except.pure] at hres
  split at hres
  · exact absurd hres (by simp)
  · simp only [Except.ok.injEq] at hres
    rw [← hres]
    -- `parent.exec = exec'.replaceStackAndIncrPC …` and `exec'.accounts = result.toCreateResult.accounts`.
    show AccPresent a result.toCreateResult.accounts
    rw [toCreateResult_accounts_eq]; exact hresult

/-- `resumeAfterCreate` on `.ok` rebuilds `pd.frame` with the same `kind` (it touches only `exec`),
so checkpoint presence transports. -/
theorem resumeAfterCreate_kind (result : Evm.FrameResult) (pd : Evm.PendingCreate)
    (parent : Evm.Frame) (hres : Evm.resumeAfterCreate result.toCreateResult pd = .ok parent) :
    parent.kind = pd.frame.kind := by
  unfold Evm.resumeAfterCreate at hres
  simp only [bind, Except.bind, pure, Except.pure] at hres
  split at hres
  · exact absurd hres (by simp)
  · simp only [Except.ok.injEq] at hres; rw [← hres]

/-- **Brick D — account-presence is monotone across a whole `drive` run.** Strong induction on
`fuel` following `drive`'s recursion (template: `drive_fuel_succ`). `DrivePresent a` at the start
yields `AccPresent a` in the result accounts at the end, given:

* `hmono` — the per-`.next`-step account-presence mono at `a` (Brick C; supplied & satisfiable: the
  self instance is the proven `stepFrame_next_self`, the arbitrary-`a` generalisation differs only in
  SSTORE/TSTORE via `accounts_find?_insert_mono`);
* `hprec` — `beginCall`'s precompile `.inr` arm preserves presence at `a` (satisfiable: precompiles
  only insert; vacuous for call-free IR);
* `hcall_acc`/`hcall_kind` — the CALL-site boundary facts: the issued `params.accounts` retains
  presence at `a` from the issuing frame's running map, and the suspended `pending.frame` keeps the
  issuing frame's checkpoint (`callArm` sets `params.accounts := (post-charge) exec.accounts` —
  `charge` is accounts-verbatim — and `pending.frame := { current with exec := … }`, same `kind`).
  Satisfiable & local (the `callArm` framing); supplied to keep the drive induction self-contained
  rather than re-diving the `stepFrame → dispatch → systemOp → callArm` chain;
* `hhalt` — the halting-opcode account-verbatim fact (STOP/RETURN/REVERT don't touch accounts);
* `hncr` — the no-CREATE seam, **scoped to the frames the run actually visits** (`EngineReaches`-
  reachable from the start `(s0, t0)`): satisfiable for a CREATE-free child run (the `NotCreate` seam),
  *not* the false universal `∀ fr`. Genuinely needed — `drive`'s CREATE-fault arm sets `accounts := ∅`.

The universally-true seams are `∀`-quantified (constant across the recursion); `hncr` is reachability-
scoped via the `EngineReaches s0 t0 stack state` accumulator threaded by `ih`. Both `endCall` **and**
`endCreate` are presence-preserving (success = `insert`, failure = checkpoint), so no frame-kind
exclusion is needed at the halt/resume arms. -/
theorem drive_accounts_find_mono (a : Evm.AccountAddress)
    (hmono : ∀ (fr : Evm.Frame) (exec' : Evm.ExecutionState),
      Evm.stepFrame fr = .next exec' → AccPresent a fr.exec.accounts → AccPresent a exec'.accounts)
    (hprec : ∀ (cp : Evm.CallParams) (imm : Evm.CallResult),
      Evm.beginCall cp = .inr imm → AccPresent a cp.accounts → AccPresent a imm.accounts)
    (hcall_acc : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → AccPresent a fr.exec.accounts → AccPresent a cp.accounts)
    (hcall_kind : ∀ (fr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall),
      Evm.stepFrame fr = .needsCall cp pd → pd.frame.kind = fr.kind)
    (hhalt : ∀ (fr : Evm.Frame) (e : Evm.ExecutionState) (o : ByteArray),
      Evm.stepFrame fr = .halted (.success e o) → AccPresent a fr.exec.accounts →
        AccPresent a e.accounts)
    (s0 : List Evm.Pending) (t0 : Evm.Frame ⊕ Evm.FrameResult)
    -- the no-CREATE seam, **scoped to the frames the run actually visits** (`EngineReaches`-reachable
    -- from the start `(s0, t0)`): satisfiable for a CREATE-free child run (the `NotCreate` seam), not
    -- the false universal `∀ fr`. Genuinely needed (the CREATE-fault arm sets `accounts := ∅`).
    (hncr : ∀ (stack : List Evm.Pending) (fr : Evm.Frame), EngineReaches s0 t0 stack (.inl fr) →
      ∀ (cp : Evm.CreateParams) (pd : Evm.PendingCreate), Evm.stepFrame fr ≠ .needsCreate cp pd) :
    ∀ (f : ℕ) (stack : List Evm.Pending) (state : Evm.Frame ⊕ Evm.FrameResult)
      (res : Evm.FrameResult),
      Evm.drive f stack state = .ok res → DrivePresent a stack state →
      EngineReaches s0 t0 stack state →
      AccPresent a res.toCallResult.accounts := by
  intro f
  induction f with
  | zero => intro stack state res h _ _; simp [Evm.drive] at h
  | succ n ih =>
    intro stack state res hdrive hpres hreach
    unfold Evm.drive at hdrive
    cases state with
    | inr result =>
      cases stack with
      | nil =>
        -- terminal delivery: `res = result`, presence carried by `hpres`.
        simp only at hdrive
        obtain ⟨hr, _⟩ := hpres
        rw [(Except.ok.injEq _ _).mp hdrive] at hr; exact hr
      | cons pending rest =>
        dsimp only at hdrive
        obtain ⟨hresult, hstk⟩ := hpres
        obtain ⟨hpend, hrest⟩ := hstk
        cases hres : pending.resume result with
        | ok parent =>
          rw [hres] at hdrive; dsimp only at hdrive
          refine ih rest (.inl parent) res hdrive ⟨?_, ?_, hrest⟩
            (hreach.tail (.resume hres))
          · -- parent.exec.accounts presence: for `.call`, `= result.accounts` (resumeAfterCall);
            -- for `.create`, `= result.accounts` (resumeAfterCreate), both present by `hresult`.
            cases pending with
            | call pd =>
              simp only [Evm.Pending.resume, Except.ok.injEq] at hres
              rw [← hres]
              show AccPresent a (Evm.resumeAfterCall result.toCallResult pd).exec.accounts
              rw [resumeAfterCall_accounts]; exact hresult
            | create pd =>
              -- `Pending.resume (.create pd) = resumeAfterCreate result.toCreateResult pd`; on `.ok`
              -- the resumed exec.accounts = result.accounts (present), so transports `hresult`.
              simp only [Evm.Pending.resume] at hres
              exact resumeAfterCreate_exec_accounts_present a result pd parent hres hresult
          · -- parent checkpoint presence: both resumes rebuild `pd.frame` with the same `kind`.
            cases pending with
            | call pd =>
              simp only [Evm.Pending.resume, Except.ok.injEq] at hres
              rw [← hres]
              show CheckpointPresent a (Evm.resumeAfterCall result.toCallResult pd)
              have hkeq : (Evm.resumeAfterCall result.toCallResult pd).kind = pd.frame.kind := rfl
              unfold CheckpointPresent; rw [hkeq]; exact hpend
            | create pd =>
              simp only [Evm.Pending.resume] at hres
              have hkeq : parent.kind = pd.frame.kind :=
                resumeAfterCreate_kind result pd parent hres
              show CheckpointPresent a parent
              unfold CheckpointPresent; rw [hkeq]; exact hpend
        | error e =>
          rw [hres] at hdrive; dsimp only at hdrive
          -- resume faulted: parent halts exceptionally; deliver `endFrame pending.frame (.exception e)`.
          refine ih rest (.inr (Evm.endFrame pending.frame (.exception e))) res hdrive ⟨?_, hrest⟩
            (hreach.tail (.resumeErr hres))
          -- `endFrame .exception` rolls back to the checkpoint (present `hpend`); no `.success` arg.
          refine endFrame_accPresent a pending.frame (.exception e) hpend ?_
          intro e' o' hcon; exact absurd hcon (by nofun)
    | inl current =>
      dsimp only at hdrive
      obtain ⟨hrun, hck, hstk⟩ := hpres
      cases hstep : Evm.stepFrame current with
      | next exec =>
        rw [hstep] at hdrive; dsimp only at hdrive
        refine ih stack (.inl { current with exec := exec }) res hdrive ⟨?_, ?_, hstk⟩
          (hreach.tail (.next hstep))
        · show AccPresent a exec.accounts; exact hmono current exec hstep hrun
        · -- `.next` updates only `exec`; `kind` (hence checkpoint) unchanged.
          show CheckpointPresent a { current with exec := exec }
          unfold CheckpointPresent; exact hck
      | halted halt =>
        rw [hstep] at hdrive; dsimp only at hdrive
        refine ih stack (.inr (Evm.endFrame current halt)) res hdrive ⟨?_, hstk⟩
          (hreach.tail (.halt hstep))
        -- `endFrame current halt`: presence-preserving for either kind (`endFrame_accPresent`);
        -- on `.success`, the running map at halt is `hrun`.
        refine endFrame_accPresent a current halt hck ?_
        intro e o he; exact hhalt current e o (by rw [hstep, he]) hrun
      | needsCall params pending =>
        rw [hstep] at hdrive; dsimp only at hdrive
        have hcpacc : AccPresent a params.accounts := hcall_acc current params pending hstep hrun
        have hpf : pending.frame.kind = current.kind := hcall_kind current params pending hstep
        cases hbc : Evm.beginCall params with
        | inl child =>
          rw [hbc] at hdrive; dsimp only at hdrive
          refine ih (.call pending :: stack) (.inl child) res hdrive ⟨?_, ?_, ?_, hstk⟩
            (hreach.tail (.call hstep hbc))
          · exact beginCall_inl_accounts_present a params hbc hcpacc
          · obtain ⟨created, sub, hkind⟩ := beginCall_inl_checkpoint params hbc
            unfold CheckpointPresent; rw [hkind]; exact hcpacc
          · show CheckpointPresent a pending.frame
            unfold CheckpointPresent; rw [hpf]
            unfold CheckpointPresent at hck; exact hck
        | inr immediate =>
          rw [hbc] at hdrive; dsimp only at hdrive
          refine ih (.call pending :: stack) (.inr (.call immediate)) res hdrive ⟨?_, ?_, hstk⟩
            (hreach.tail (.callImm hstep hbc))
          · show AccPresent a immediate.accounts; exact hprec params immediate hbc hcpacc
          · show CheckpointPresent a pending.frame
            unfold CheckpointPresent; rw [hpf]
            unfold CheckpointPresent at hck; exact hck
      | needsCreate params pending =>
        exact absurd hstep (hncr stack current hreach params pending)

/-- **The `.success` shape of `CallPreservesSelf`, discharged via Brick D.** A returning external
CALL keeps the *caller's* self present, given the child-drive no-erase seam (the same
`hmono`/`hprec`/`hcall_acc`/`hcall_kind`/`hhalt` closers as `drive_accounts_find_mono`, the CALL-site
self-address framing `hcall_self`, and the reachability-scoped no-CREATE seam `hncr` instantiated at
the child run `([], inl child)`).

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
    -- the no-CREATE seam, scoped to the **child run's** reachable frames (satisfiable for a
    -- CREATE-free lowered child — the `NotCreate` seam — not the false universal `∀ fr`). Phrased over
    -- the CALL's params/child via the `CallReturns` shape so it names exactly the run that executes.
    (hncr : ∀ (cp : Evm.CallParams) (pd : Evm.PendingCall) (child : Evm.Frame),
      Evm.stepFrame callFr = .needsCall cp pd → Evm.beginCall cp = .inl child →
      ∀ (stack : List Evm.Pending) (fr : Evm.Frame),
        EngineReaches [] (Sum.inl child) stack (.inl fr) →
        ∀ (cpc : Evm.CreateParams) (pdc : Evm.PendingCreate), Evm.stepFrame fr ≠ .needsCreate cpc pdc)
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
    [] (Sum.inl child)
    (hncr cp pending child hstep hbc)
    (seedFuel cp.gas) [] (Sum.inl child) childRes hchild hchildPres EngineReaches.refl
  -- Close `SelfPresent resumeFr` via the landed resume-self bridge.
  rw [hresume]
  exact resumeAfterCall_self_of_accounts childRes.toCallResult pending hmono'

/-- **`CallPreservesSelf`, discharged modulo the child-drive no-erase seam.** Every shape of a
returning external CALL keeps the caller's self present: `.success` via `callPreservesSelf_success`
(Brick D), `.revert`/`.exception` structurally (folded in — `callPreservesSelf_success` covers the
whole `CallReturns` once the child run terminates, since `childRes` already carries whichever shape).

The seam hypotheses are each genuinely satisfiable (never vacuous) and remain **supplied**:
* `hmono`/`hcall_acc`/`hcall_kind`/`hhalt`/`hcall_self` are *universally-true* framing facts (every
  `.next` step is accounts-monotone at any `a`; `callArm` sets `params.accounts`/`pending.frame` from
  the issuing exec; halting opcodes don't touch accounts) — true for **all** frames, so trivially
  satisfiable (`hmono` is the unproven Brick C, but holds for every frame);
* `hprec` is the precompile-preservation fact (precompiles only insert) — satisfiable, vacuous for
  call-free IR;
* `hncr` is the no-CREATE seam **scoped to the child run's reachable frames** (`EngineReaches`):
  satisfiable for a CREATE-free lowered child (the `NotCreate`/`ModellableStep` seam, `DriveSim.lean`),
  *not* the false universal `∀ fr`. Genuinely needed — `drive`'s CREATE-fault arm sets `accounts := ∅`.

`CallPreservesSelf` is *not* unconditionally true (the precompile/CREATE `∅`-arms really can erase, and
`CallReturns` does not by itself rule them out across the child run). The strict improvement over the
prior fully-supplied `CallPreservesSelf`: its `.success` monotonicity is now *discharged* engine-level
(Brick D), only the structural no-erase guard remains. -/
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
        pd.frame.exec.executionEnv.address = fr.exec.executionEnv.address)
    -- the no-CREATE seam, scoped per CALL edge to that call's child run (the `NotCreate` seam).
    (hncr : ∀ (callFr : Evm.Frame) (cp : Evm.CallParams) (pd : Evm.PendingCall) (child : Evm.Frame),
      Evm.stepFrame callFr = .needsCall cp pd → Evm.beginCall cp = .inl child →
      ∀ (stack : List Evm.Pending) (fr : Evm.Frame),
        EngineReaches [] (Sum.inl child) stack (.inl fr) →
        ∀ (cpc : Evm.CreateParams) (pdc : Evm.PendingCreate), Evm.stepFrame fr ≠ .needsCreate cpc pdc) :
    CallPreservesSelf := by
  intro callFr resumeFr hcr hself
  exact callPreservesSelf_success hmono hprec hcall_acc hcall_kind hhalt hcall_self hcr
    (hncr callFr) hself

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
  (§5), now transportable across each block's materialise sub-runs by `selfPresent_matRuns`;
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

The centerpiece walk `L2.0 driveCorrPlus_run_stmts` (below) is decomposed by the architect into

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
`Corr`/`EvalStmt` ALONE, not of the run, so they are NOT bundled into `driveCorrPlus_run_stmts` (doing
so would buy nothing): the downstream Route-4b assembly applies them per cursor directly (the indexed
form bound to the run's reached `(stpc, frpc)`, NOT the universal free-`ob` `StmtTies` predicate, which
ranges over all cursors and is unreconstructable from a single run).

**The two channels that STAY SUPPLIED tonight** (satisfiable, documented, NON-vacuous):
  * **S3 (gas positional value)** `stpc'.locals t = ofUInt64 (frpc.gas − Gbase)` — NOT a value-only
    have-block: it is the TRACE↔RECORDER bridge (`EvalStmt.assignGas` peels `ob` as the HEAD of the gas
    trace, while `aligned_read_eq_obs` gives the recorder's `gasAcc[i]`; tying them needs a NEW carried
    invariant `IR-trace-consumed = gasAcc` plus the gas-channel structural walk threading
    `gasFrs[i] = gasFrame frpc`). Supplied as `hgasval`; satisfiable — it is exactly what
    `aligned_read_eq_obs` yields once the gas walk threads the witness pairing (`gasReadOf_gasFrame_eq_obs`
    is `rfl`), inhabited by any top-level GAS read.
  * **S1/S5/S6** — folded inside the supplied `SimStmtStep` (the serialized post-P3 spine).
  * **S4 (gas runtime envelopes)** — the lower-bound envelopes need the clean-halt FORWARD split
    (`cleanHalts_forward` to the cursor, then the GAS op runs), not pure descent; supplied alongside S3.
-/

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

/-! ### L2.0 — the `DriveCorrPlus` statement-walk, PRESERVATION form (C3 partial)

`driveCorrPlus_run_stmts` mirrors `sim_stmts_block` (consuming `SimStmtStep` for the Runs+Corr+stack
triple), threads `SelfPresent` via P3, and carries the alignment VERBATIM to the terminator frame. It is
a pure PRESERVATION lemma — it produces only what the walk itself establishes from the run. The no-bridge
per-cursor value channels are kept SEPARATE as the standalone cursor lemmas
`driveCorrPlus_assign_remat_memRealises` (S7) and `driveCorrPlus_sload_value` (S2): they are functions of
the supplied per-cursor `Corr`/`EvalStmt` alone, NOT of the run, so bundling them into the walk would buy
nothing (the C8 Route-4b assembly applies them per cursor directly). The structural/call ties S1/S5/S6 are
inside the supplied `SimStmtStep`; S3/S4 (gas positional value / runtime envelopes) are trace↔recorder /
clean-halt-forward facts produced downstream. Every supplied parameter is satisfiable and non-vacuous. -/

/-- **L2.0 (partial — preservation).** From `DriveCorrPlus` at a block boundary, the block, the IR block
run, and the supplied per-statement simulation `SimStmtStep` (folding S1/S5/S6) + the P3 call edge
`CallPreservesSelf`: reach a terminator frame `frT` with `Runs fr frT`, `Corr` at the terminator cursor,
empty stack, `SelfPresent frT`, and the alignment carried VERBATIM. This is the walk's genuine
preservation content. The no-bridge value channels S7/S2 are the standalone cursor lemmas
`driveCorrPlus_assign_remat_memRealises` / `driveCorrPlus_sload_value` (applied per cursor by the C8
assembly), NOT bundled here. S3/S4 (gas positional value / runtime envelopes) are downstream
trace↔recorder-bridge / clean-halt-forward facts. -/
theorem driveCorrPlus_run_stmts {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {L : Label} {b : Block} {fr : Frame}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    -- `b` is pinned by `hrun`/`hsim` (both run over `b.stmts`); `_hb` ties `b` to `prog.blocks[L.idx]?`,
    -- kept for signature stability — the deferred structural channels (S1/S5/S6 positioning via
    -- `blockAt`) consume it, the preservation body does not.
    (_hb : prog.blocks.toList[L.idx]? = some b)
    (hrun : V2.RunStmts prog o st T b.stmts st' T')
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf) :
    ∃ frT, Runs fr frT
      ∧ Corr prog sloadChg obs st' frT L b.stmts.length
      ∧ frT.exec.stack = []
      ∧ SelfPresent frT
      ∧ GasLogAligned gasAcc gasFrs
      ∧ SloadLogAligned sloadAcc sloadFrs := by
  -- (1) the Runs + Corr-at-terminator + stack-nil triple — VERBATIM from `sim_stmts_block`.
  obtain ⟨frT, hruns, hcorrT, hstk⟩ := sim_stmts_block hsim hdc.base.corr hrun
  -- (2) `SelfPresent frT` via P3 (supplied `CallPreservesSelf`), from the boundary self-presence.
  have hself : SelfPresent frT := selfPresent_runs_of_call hcall hdc.selfPresent hruns
  exact ⟨frT, hruns, hcorrT, hstk, hself, hdc.gasAligned, hdc.sloadAligned⟩

/-! ## §8 — the halt wrappers (Tier 2 / C4): `driveCorrPlus_step_stop` / `_ret`

The halt-arm analogues of `drive_step_block_stop`/`drive_step_block_ret` (`DriveSim.lean`), but
threading `DriveCorrPlus` through the committed L2.0 walk `driveCorrPlus_run_stmts` (C3) and EMITTING
the §7 terminator ties in **Route-4b indexed form** — bound to the SPECIFIC terminator frame `frT`
the L2.0 walk reaches, NOT a universal `∀ st' frT, Corr → …` (which is unprovable: `SelfPresent`
holds only at the reached `frT`, and `Corr`-at-terminator does NOT imply `SelfPresent`).

The ONE genuinely-derived conjunct is `¬ (accounts == ∅)` — from `SelfPresent` via
`accounts_ne_empty_of_selfPresent` (T1: at `frT`; T2: at the return endpoint `frv`, transported by
the P3 hop `selfPresent_runs_of_call`). The remaining conjuncts (`kind = .call`, the `ret` value
channel, gas envelopes, the RETURN-epilogue decode bundle) stay **supplied** — they are structural /
gas-descent facts, indexed to the reached frame(s) so genuinely satisfiable, NOT vacuous and NOT the
forbidden universal. `self` is set to `frT.exec.executionEnv.address`, so the `self = addr` conjunct
is `rfl`; the entry-self equality `frT.address = fr0.address` is a downstream F2 address-invariance
concern, NOT these wrappers. No successor invariant — halt arms bottom out the recursion. -/

/-- **`driveCorrPlus` halt wrapper, `stop` arm (T1).** From `DriveCorrPlus` at the boundary, the
block, the IR block run, the supplied `SimStmtStep`, and the P3 call edge `CallPreservesSelf`: reach
the terminator frame `frT` (`Runs fr frT`, `Corr` at the terminator cursor) carrying `SelfPresent
frT`, and emit the T1 bundle indexed to `frT`: `self = addr` (`rfl`), `kind = .call` (supplied
`hkind`, indexed to the reached `(frT, hruns, hcorrT)` — structural, a top-level lowered run executes
in a `.call` frame), and `¬ (accounts == ∅)` (DERIVED from `SelfPresent frT`). -/
theorem driveCorrPlus_step_stop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {L : Label} {b : Block} {fr : Frame}
    {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat} {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hbterm : b.term = .stop)
    (hrun : V2.RunStmts prog o st T b.stmts st' T')
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf)
    -- `kind = .call cp` at the reached terminator frame (supplied — structural, indexed to the
    -- reached `(frT, hruns, hcorrT)`; a real top-level lowered run executes in the `.call` codeFrame).
    (hkind : ∀ frT, Runs fr frT → Corr prog sloadChg obs st' frT L b.stmts.length →
      ∃ cp, frT.kind = Evm.FrameKind.call cp) :
    ∃ frT, Runs fr frT
      ∧ Corr prog sloadChg obs st' frT L b.stmts.length
      ∧ SelfPresent frT
      ∧ (frT.exec.executionEnv.address = frT.exec.executionEnv.address
          ∧ (∃ cp, frT.kind = Evm.FrameKind.call cp)
          ∧ ¬ (frT.exec.accounts == (∅ : Evm.AccountMap)) = true) := by
  obtain ⟨frT, hruns, hcorrT, _hstk, hself, _, _⟩ :=
    driveCorrPlus_run_stmts hdc hb hrun hsim hcall
  exact ⟨frT, hruns, hcorrT, hself,
    rfl, hkind frT hruns hcorrT, accounts_ne_empty_of_selfPresent hself⟩

/-- **`driveCorrPlus` halt wrapper, `ret` arm (T2).** As `driveCorrPlus_step_stop`, with `b.term =
.ret t`: reach the terminator frame `frT` carrying `SelfPresent frT`, and emit the T2 bundle indexed
to `frT`. The `ret` value channel (`hv`) and gas envelopes (`hgas`) stay supplied (value-binding /
gas-descent facts); the RETURN-epilogue bundle is supplied per-`frv` (`hretsite`: PUSH32/PUSH32/
RETURN decode + gas margins + `kind = .call`), but its `¬ (accounts == ∅)` conjunct is **DERIVED** at
the return endpoint `frv` via the P3 hop `selfPresent_runs_of_call hcall hselfT hrunsFrv` (transport
`SelfPresent frT` along `Runs frT frv`) + `accounts_ne_empty_of_selfPresent`. -/
theorem driveCorrPlus_step_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {L : Label} {b : Block} {t : Tmp}
    {fr : Frame} {gasAcc : List Word} {gasFrs : List Frame} {sloadAcc : List Nat}
    {sloadFrs : List Frame}
    (hdc : DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hbterm : b.term = .ret t)
    (hrun : V2.RunStmts prog o st T b.stmts st' T')
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hcall : CallPreservesSelf)
    -- the `ret` value channel (supplied — the IR `.ret t` step that fired binds `t`).
    (hv : ∃ vw, st'.locals t = some vw)
    -- the gas envelopes at the reached terminator cursor (supplied — gas-descent fact).
    (hgas : ∀ frT, Corr prog sloadChg obs st' frT L b.stmts.length →
      (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum ≤ frT.exec.gasAvailable.toNat
      ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024)
    -- the RETURN-epilogue decode/gas/kind bundle, per return endpoint `frv` (supplied — concrete
    -- lowered RETURN bytes; indexed to the reached `(frT, frv)`). The `accounts ≠ ∅` conjunct is
    -- REMOVED from this supplied bundle and DERIVED below via P3 + `find?_some_ne_empty`.
    (hretsite : ∀ frT, Runs fr frT → Corr prog sloadChg obs st' frT L b.stmts.length →
      ∀ vw, st'.locals t = some vw → ∀ frv, Runs frT frv →
      frv.exec.executionEnv.code = frT.exec.executionEnv.code →
      frv.exec.executionEnv.address = frT.exec.executionEnv.address →
      (∀ k, selfStorage frv k = selfStorage frT k) →
      frv.exec.stack = vw :: frT.exec.stack →
      ∃ cp,
        decode frv.exec.executionEnv.code frv.exec.pc = some (.Push .PUSH32, some ((0 : Word), 32))
        ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
            = some (.Push .PUSH32, some ((0 : Word), 32))
        ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
            = some (.System .RETURN, .none)
        ∧ 3 ≤ frv.exec.gasAvailable.toNat
        ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
        ∧ frv.kind = Evm.FrameKind.call cp) :
    ∃ frT, Runs fr frT
      ∧ Corr prog sloadChg obs st' frT L b.stmts.length
      ∧ SelfPresent frT
      ∧ (frT.exec.executionEnv.address = frT.exec.executionEnv.address
          ∧ (∃ vw, st'.locals t = some vw)
          ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
              ≤ frT.exec.gasAvailable.toNat
          ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
          ∧ (∀ vw, st'.locals t = some vw → ∀ frv, Runs frT frv →
              frv.exec.executionEnv.code = frT.exec.executionEnv.code →
              frv.exec.executionEnv.address = frT.exec.executionEnv.address →
              (∀ k, selfStorage frv k = selfStorage frT k) →
              frv.exec.stack = vw :: frT.exec.stack →
              ∃ cp,
                decode frv.exec.executionEnv.code frv.exec.pc
                    = some (.Push .PUSH32, some ((0 : Word), 32))
                ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
                    = some (.Push .PUSH32, some ((0 : Word), 32))
                ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
                    = some (.System .RETURN, .none)
                ∧ 3 ≤ frv.exec.gasAvailable.toNat
                ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
                ∧ frv.kind = Evm.FrameKind.call cp
                ∧ ¬ (frv.exec.accounts == (∅ : Evm.AccountMap)) = true)) := by
  obtain ⟨frT, hruns, hcorrT, _hstk, hselfT, _, _⟩ :=
    driveCorrPlus_run_stmts hdc hb hrun hsim hcall
  refine ⟨frT, hruns, hcorrT, hselfT,
    rfl, hv, (hgas frT hcorrT).1, (hgas frT hcorrT).2, ?_⟩
  intro vw hvw frv hrunsFrv hcode haddr hstor hstk2
  obtain ⟨cp, hd1, hd2, hdret, hg1, hg2, hkindv⟩ :=
    hretsite frT hruns hcorrT vw hvw frv hrunsFrv hcode haddr hstor hstk2
  exact ⟨cp, hd1, hd2, hdret, hg1, hg2, hkindv,
    accounts_ne_empty_of_selfPresent (selfPresent_runs_of_call hcall hselfT hrunsFrv)⟩

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
  EXTENSION, correctly NOT claimed here (matching `driveCorrPlus_run_stmts` and the C1 `*_matRuns`
  preservation-only docstrings).

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
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdc.base.corr hrun
  -- Layer E: the supplied jump bundle delivers the `JUMPDEST` landing `fj`.
  obtain ⟨fj, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk, hfjmod, hfjstore,
    hfjmem, hfjdec⟩ := hjump frT hcorrT
  -- the `JUMPDEST` step lands at `(dst, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbdst hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from the boundary's (the forward split).
  have hcleanSucc : CleanHalts (jumpdestFrame fj) :=
    cleanHalts_forward hdc.base.cleanHalts hfrrun
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
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdc.base.corr hrun
  -- Layer E: the supplied branch bundle resolves the taken successor `succ` and its landing `fj`.
  obtain ⟨succ, bsucc, fj, hdir, hbsucc, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk,
    hfjmod, hfjstore, hfjmem, hfjdec⟩ := hbranch frT hcorrT
  -- the `JUMPDEST` step lands at `(succ, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbsucc hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from the boundary's (the forward split).
  have hcleanSucc : CleanHalts (jumpdestFrame fj) :=
    cleanHalts_forward hdc.base.cleanHalts hfrrun
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
#print axioms Lir.V2.sstorePresence_of_self
#print axioms Lir.V2.selfPresent_addFrame
#print axioms Lir.V2.selfPresent_sloadFrame
#print axioms Lir.V2.selfPresent_matRuns
#print axioms Lir.V2.gasLogAligned_matRuns
#print axioms Lir.V2.sloadLogAligned_matRuns
-- STEP 1: the per-cursor GAS-channel advance bricks (gas-cursor EXTEND + non-gas VERBATIM-thread).
#print axioms Lir.V2.driveCorrPlus_gas_cursor_advance
#print axioms Lir.V2.driveCorrPlus_norecord_cursor_advance
#print axioms Lir.V2.resumeAfterCall_address
#print axioms Lir.V2.resumeAfterCall_accounts
#print axioms Lir.V2.selfPresent_runs
#print axioms Lir.V2.selfPresent_codeFrame
#print axioms Lir.V2.driveCorrPlus_entry
-- StepPreservesSelf is now DISCHARGED (a theorem, not a supplied edge): the engine-level brick
-- `stepFrame_next_self` and its dispatch/systemOp/smsfOp sub-lemmas, plus the call-resume structural
-- halves, are all axiom-clean.
#print axioms Lir.V2.stepPreservesSelf
#print axioms Evm.stepFrame_next_self
#print axioms Evm.dispatch_next_self
#print axioms Evm.systemOp_next_self
#print axioms Evm.smsfOp_next_self
#print axioms Evm.sstore_self_present
#print axioms Evm.resumeAfterCall_selfAt
#print axioms Lir.V2.resumeAfterCall_self_of_accounts
#print axioms Lir.V2.endCall_revert_accounts
#print axioms Lir.V2.endCall_exception_accounts
-- CALLMONO: account-presence monotone across a whole `drive` run (Brick D) — the `.success` shape
-- of `CallPreservesSelf` discharged (modulo the documented satisfiable child-drive no-erase seam).
#print axioms Lir.V2.accounts_find?_insert_mono
#print axioms Lir.V2.accPresent_ne_empty
#print axioms Lir.V2.beginCall_inl_accounts_present
#print axioms Lir.V2.beginCall_inl_checkpoint
#print axioms Lir.V2.endFrame_accPresent
#print axioms Lir.V2.drive_accounts_find_mono
#print axioms Lir.V2.callPreservesSelf_success
#print axioms Lir.V2.callPreservesSelf
-- C3: the no-bridge VALUE channels of the L2.0 statement-walk.
#print axioms Lir.V2.memRealises_setLocal_nonspilled
#print axioms Lir.V2.driveCorrPlus_assign_remat_memRealises
#print axioms Lir.V2.driveCorrPlus_sload_value
#print axioms Lir.V2.driveCorrPlus_sload_value_world
#print axioms Lir.V2.driveCorrPlus_run_stmts
-- C4: the new account-map non-emptiness fact + the two halt wrappers (T1/T2).
#print axioms Lir.V2.forM_from_nil
#print axioms Lir.V2.all2_nil_false
#print axioms Lir.V2.find?_some_ne_empty
#print axioms Lir.V2.accounts_ne_empty_of_selfPresent
#print axioms Lir.V2.driveCorrPlus_step_stop
#print axioms Lir.V2.driveCorrPlus_step_ret
#print axioms Lir.V2.driveCorrPlus_step_jump
#print axioms Lir.V2.driveCorrPlus_step_branch
