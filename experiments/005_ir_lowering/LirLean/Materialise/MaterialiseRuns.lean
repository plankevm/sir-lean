import LirLean.Frame.Match
import LirLean.Materialise.MaterialiseGas
import LirLean.Materialise.DefsSound
import BytecodeLayer.Hoare.MemAlgebra

/-!
# LirLean — materialise endpoint bundles + realisability side-conditions (Layer **B1** carriers)

The value-channel LINCHPIN itself — running the lowered push-sequence of an expression
reproduces, on the bytecode stack, the value the IR's `evalExpr` computes — is the
fold-based `Lir.materialise_runsC` (`Materialise/MatFoldChannel.lean`), proved
fuel-free over the total byte cache `matCache`. This module carries what that proof (and
the per-statement sims) consume from the B1 layer:

* the **frame-accessor reductions** for the materialise post-frames (`pushFrameW_*`,
  `addFrame_*`, `ltFrame_*`, `sloadFrame_*`, `gasFrame_*`);
* the **stash-endpoint bundle** `StashRuns` (the def-site `PUSH slot ; MSTORE` epilogue);
* the small byte-arithmetic facts (`emitImm_length`, `push32_pcΔ`) and the pure-fragment
  obs-irrelevance `evalExpr_obs_irrel`;
* the live realisability side-conditions: `StorageAgree` (the `M3` storage lens) and
  `MemRealises` (the memory value channel for spilled tmps), with their `.transport`s and
  the memory-coverage bricks (`M_32_eq_self_of_covered`,
  `memoryExpansionWords?_ofNat_32_of_covered`);
* the RETIRED `SloadRealises`/`GasRealises` universals (regression-witness subjects only).

## The two non-pure leaves are spilled (unreachable here)

**`.gas`** (Phase B) and **`.sload`** (Phase C) are routed to memory slots by `defsOf`
(`Loc.slot (slotOf t)`): the value (and, for sload, its cold/warm warmth charge) is read once
at the `assign` def-site stash (`[GAS]`/`materialise k ++ [SLOAD]`, then `PUSH slot ; MSTORE`) and
reused via `MLOAD`. So a *bare* `.gas`/`.sload k` is never materialised by this recursion — those
arms are unreachable (`e ≠ .gas`, `∀ k, e ≠ .sload k`, both preserved across the `.tmp` recursion
by `defsOf_ne_gas`/`defsOf_ne_sload`). The def-site stash runs (with the value tied by
`MemRealises` and, for sload, the warmth via the positional `SloadLogAligned`) live in
`sim_assign_gas`/`sim_assign_sload` (`SimStmt.lean`), NOT here. The former `GasRealises`/
`SloadRealises` universals were deleted with `HonestGasTie.lean`'s regression witnesses (the
unsatisfiability lesson is recorded in `RealisabilitySpec.lean`'s header + `docs/gas-decision.md`).

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `Match.lean`);
nothing here touches `Spec/Semantics.lean` / `Law.lean` (the frame-free spine).
-/

namespace Lir

open Lir.Frame
open BytecodeLayer.Exec
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## Frame-accessor reductions for the materialise post-frames

Each `sim_*` post-frame (`pushFrameW` / `addFrame` / `ltFrame` / `sloadFrame`) leaves
the `executionEnv` (hence `code`, `address`, `canModifyState`) untouched — only
`stack`, `pc`, `gasAvailable` (and, for SLOAD, the accessed-key substate, never a
storage *value*) change. These `rfl` lemmas expose exactly the clauses B1's invariant
threads. -/

@[simp] theorem pushFrameW_code (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

/-! Every materialise post-frame is `{ fr with exec := … }`, so the frame's
`validJumps` field (set once at frame creation from the code) is preserved verbatim. -/

@[simp] theorem pushFrameW_validJumps (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).validJumps = fr.validJumps := rfl

@[simp] theorem addFrame_validJumps (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).validJumps = fr.validJumps := rfl

@[simp] theorem ltFrame_validJumps (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).validJumps = fr.validJumps := rfl

@[simp] theorem sloadFrame_validJumps (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).validJumps = fr.validJumps := rfl

@[simp] theorem gasFrame_validJumps (fr : Frame) :
    (gasFrame fr).validJumps = fr.validJumps := rfl

@[simp] theorem pushFrameW_addr (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem pushFrameW_selfStorage (fr : Frame) (w : Word) (width : UInt8) (k : Word) :
    selfStorage (pushFrameW fr w width) k = selfStorage fr k := rfl

@[simp] theorem pushFrameW_pc (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.pc = fr.exec.pc + (width + 1).toUInt32 := rfl

@[simp] theorem addFrame_code (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem addFrame_addr (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem addFrame_selfStorage (fr : Frame) (a b : Word) (rest : Stack Word) (k : Word) :
    selfStorage (addFrame fr a b rest) k = selfStorage fr k := rfl

@[simp] theorem addFrame_pc (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem ltFrame_code (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem ltFrame_addr (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem ltFrame_selfStorage (fr : Frame) (a b : Word) (rest : Stack Word) (k : Word) :
    selfStorage (ltFrame fr a b rest) k = selfStorage fr k := rfl

@[simp] theorem ltFrame_pc (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem sloadFrame_code (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem sloadFrame_addr (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem sloadFrame_selfStorage (fr : Frame) (key : Word) (rest : Stack Word) (k : Word) :
    selfStorage (sloadFrame fr key rest) k = selfStorage fr k := rfl

@[simp] theorem sloadFrame_pc (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.pc = fr.exec.pc + 1 := rfl

/-- `sloadFrame`'s stack is `rest` with the self-storage cell at `key` pushed (the
value `sloadFrame_storage_self` exposes through the `M3` lens). -/
@[simp] theorem sloadFrame_stack (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.stack = rest.push (selfStorage fr key) := rfl

/-- `SLOAD` charges exactly `sloadCost warm` at `fr` (`warm` the runtime warmth from
`fr`'s accessed-storage-key substate). This is the runtime cost the B2 resolver
`sloadChg k` must equal at the internal SLOAD frame. -/
@[simp] theorem sloadFrame_gas (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.gasAvailable
      = fr.exec.gasAvailable - UInt64.ofNat (Evm.sloadCost
          (fr.exec.substate.accessedStorageKeys.contains (fr.exec.executionEnv.address, key))) :=
  rfl

/-! ### `gasFrame` accessor reductions

`gasFrame fr` (the `GAS` post-frame) leaves `executionEnv` (code/address) and the
account storage untouched; it charges `Gbase`, pushes `ofUInt64` of the *post-charge*
gas, and advances pc by one. These `rfl` lemmas expose exactly those clauses. -/

@[simp] theorem gasFrame_code (fr : Frame) :
    (gasFrame fr).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem gasFrame_addr (fr : Frame) :
    (gasFrame fr).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem gasFrame_selfStorage (fr : Frame) (k : Word) :
    selfStorage (gasFrame fr) k = selfStorage fr k := rfl

@[simp] theorem gasFrame_pc (fr : Frame) :
    (gasFrame fr).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem gasFrame_stack (fr : Frame) :
    (gasFrame fr).exec.stack
      = fr.exec.stack.push (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase)) :=
  rfl

@[simp] theorem gasFrame_gas (fr : Frame) :
    (gasFrame fr).exec.gasAvailable = fr.exec.gasAvailable - UInt64.ofNat Gbase := rfl

/-! ### `toMachineState.memory` / `activeWords` reductions for the pure post-frames

Every materialise post-frame (`pushFrameW` / `addFrame` / `ltFrame` / `sloadFrame` /
`gasFrame`) is built by `replaceStackAndIncrPC` (plus a gas charge and, for SLOAD, an
account/substate update) — none of which touch the `MachineState` `memory` bytes or the
`activeWords` count. These `rfl` lemmas thread the memory value-channel transport:
bytes are *unchanged* and `activeWords` is *unchanged* (hence trivially nondecreasing). -/

@[simp] theorem pushFrameW_memory (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem pushFrameW_activeWords (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem addFrame_memory (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem addFrame_activeWords (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem ltFrame_memory (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem ltFrame_activeWords (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem sloadFrame_memory (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem sloadFrame_activeWords (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem gasFrame_memory (fr : Frame) :
    (gasFrame fr).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem gasFrame_activeWords (fr : Frame) :
    (gasFrame fr).exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords := rfl

/-! ## The stash-endpoint bundle (`StashRuns`)

`StashRuns fr endFr slot v pcΔ rest` packages everything a def-site **stash** run delivers about
the endpoint `endFr` reached from `fr` by running a `… ; PUSH32 slot ; MSTORE` stash (writing `v`
at `slot`): the run, the **honest** memory channel (`.memory` bytes + `.activeWords`, equal to the
`mstore slot v` write — NOT the full `toMachineState`, whose gas the push/charges drop is a field a
real run never preserves), the pc advanced by `pcΔ`, the frame pins (code / valid-jumps / address /
can-modify / accounts / self-storage), and the working stack left at `rest`. The stash-tail forward
lemmas (`stash_tail_runs`/`_covered`/`_gas`/`_sload`) produce it; `sim_assign_gas`/`sim_assign_sload`
and the §7 `CallRealises` call tie consume it. Named so a clause reorder does not ripple
across the destructurings. -/
structure StashRuns (fr endFr : Frame) (slot : Nat) (v : Word) (pcΔ : Nat) (rest : Stack Word) :
    Prop where
  runs        : Runs fr endFr
  memory      : endFr.exec.toMachineState.memory
                  = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).memory
  activeWords : endFr.exec.toMachineState.activeWords
                  = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).activeWords
  pc          : endFr.exec.pc = fr.exec.pc + UInt32.ofNat pcΔ
  code        : endFr.exec.executionEnv.code = fr.exec.executionEnv.code
  validJumps  : endFr.validJumps = fr.validJumps
  addr        : endFr.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod      : endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  accounts    : endFr.exec.accounts = fr.exec.accounts
  storage     : ∀ k, selfStorage endFr k = selfStorage fr k
  stack       : endFr.exec.stack = rest

/-! ## Small arithmetic facts -/

/-- `(emitImm w).length = 33` (a `PUSH32` opcode byte + 32 immediate bytes). -/
theorem emitImm_length (w : Word) : (emitImm w).length = 33 := by
  simp [emitImm, BytecodeLayer.Exec.wordBytesBE]

/-- `(32 + 1 : UInt8).toUInt32 = UInt32.ofNat 33`. -/
theorem push32_pcΔ : ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 := by decide

/-! ## `evalExpr` obs-irrelevance on the pure fragment

`Lir.evalExpr` reads its `obs` argument **only** in the `.gas` arm. So for any
non-`gas` expression the supplied gas value is irrelevant — this is what lets B1's
`.tmp t` recursion bridge `DefsSound`'s `evalExpr st 0 e'` to the `obs`-threaded value
the rest of the induction carries. -/
theorem evalExpr_obs_irrel (st : Lir.IRState) (obs obs' : Word) :
    ∀ {e : Expr}, e ≠ .gas → Lir.evalExpr st obs e = Lir.evalExpr st obs' e
  | .imm _,   _ => rfl
  | .tmp _,   _ => rfl
  | .add _ _, _ => rfl
  | .lt _ _,  _ => rfl
  | .sload _, _ => rfl
  | .gas,     h => absurd rfl h

/-! ## The realisability side-conditions (storage lens; the retired SLOAD/GAS universals)

**Phase B/C**: gas AND sload are now **spilled** — a bare `Expr.gas` / `Expr.sload _` is never
materialised (uses go through `.slot`/MLOAD; the def-site stash is run by `sim_assign_gas` /
`sim_assign_sload`). So the `.gas` and `.sload` arms of `materialise_runsC` are **unreachable**,
discharged by `e ≠ .gas` and `∀ k, e ≠ .sload k` (both preserved across the `.tmp` recursion by
`defsOf_ne_gas`/`defsOf_ne_sload`). The two former realisability universals are retired:

* **`SloadRealises`** (RETIRED, Phase C) — the old `∀ g`-universal forcing `sloadChg k` to equal
  the runtime `sloadCost` warmth at every same-address frame. Unsatisfiable on any cold-then-warm
  same-key re-read (2100 ≠ 100). No longer carried: the SLOAD value lives in the slot (tied by
  `MemRealises`), and the warmth cost is the single cold/warm def-site read (the positional
  `SloadLogAligned` selection). Survives only as the `Drive/SelfPresent.lean` regression witness
  (`sloadRealises_charge_of_witness`); the `HonestGasTie.lean` unsatisfiability witness is deleted
  (lesson in `RealisabilitySpec.lean`'s header + `docs/gas-decision.md`).

* **`GasRealises`** (RETIRED, Phase B) — the analogous `∀ g`-gas-value universal; same story.

* **`StorageAgree`** — the still-live `M3` storage correspondence `selfStorage fr key = st.world
  key`. Preserved across the whole materialisation by `MatRunsC.storage` (every post-frame leaves
  the self account's storage *values* untouched), threading as a plain per-frame fact. It ties the
  storage lens to `evalExpr`'s world read (consumed by the `sstore` value/key materialise calls). -/

/-- The OLD B2 SLOAD-cost resolver realisability universal: at every frame `g` sharing `fr`'s
self-address, `sloadChg k` is the actual `sloadCost` warmth-charge for the bound key
`st.locals k`.

**RETIRED FROM THE CONFORMANCE SPINE (Phase C).** This `∀ g`-universal is unsatisfiable for any
genuine ≥2-read run of the same key: after the first cold→warm access `accessedStorageKeys.contains`
flips, so the warmth-charge for the *same* key changes (2100 → 100), and the universal forces the
single resolver value `sloadChg k` to equal *both* charges — it cannot hold. It is **no longer
carried by `Corr`/`materialise_runsC`/the headlines**: sload is spilled to memory, so the SLOAD
value lives in the slot (tied by `MemRealises`, the honest positional one-read value supplied at
the `assign` def-site by `sim_assign_sload`), and the warmth charge is the single cold/warm read at
that def-site (the positional `SloadLogAligned` selection via `sloadRealises_charge_of_witness`, not
this universal). This def survives ONLY as the subject of the positional discharge
`Drive/SelfPresent.lean` (`sloadRealises_charge_of_witness`); its unsatisfiability witness
(`sloadRealises_universal_unsatisfiable`) is deleted with `HonestGasTie.lean` (lesson in
`RealisabilitySpec.lean`'s header + `docs/gas-decision.md`). The honest replacement is the positional
SLOAD twin `SloadLogAligned` (`Drive/SelfPresent.lean`), satisfiable by a real cold-then-warm run. -/
def SloadRealises (sloadChg : Tmp → ℕ) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ (g : Frame) (k : Tmp) (key : Word),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    st.locals k = some key →
    sloadChg k
      = Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
          (g.exec.executionEnv.address, key))

/-- The OLD `GAS` value realisability universal: at every frame `g` sharing `fr`'s self-address,
the supplied gas word `obs` is `ofUInt64` of the post-`Gbase` gas `g` reports.

**RETIRED FROM THE CONFORMANCE SPINE (Phase B).** This `∀ g`-universal is unsatisfiable for any
genuine ≥2-distinct-read run (a real EVM run's gas strictly descends, so two same-address GAS reads
report two distinct words, and the universal forces `obs` to equal both). It is **no longer carried
by `Corr`/`materialise_runsC`/the headlines**: gas is spilled to memory, so its value lives in the
slot and is tied by `MemRealises` (the honest positional one-read value supplied at the `assign`
def-site, `sim_assign_gas`). This def survives ONLY as the subject of the positional discharge
`Drive/SelfPresent.lean` (`gasRealises_obs_of_witness`); its unsatisfiability witness
(`gasRealises_universal_unsatisfiable`) is deleted with `HonestGasTie.lean` (lesson in
`RealisabilitySpec.lean`'s header + `docs/gas-decision.md`). The honest replacement is the positional
`GasLogAligned` (`Drive/SelfPresent.lean`), satisfiable by a real descending-gas run. -/
def GasRealises (obs : Word) (fr : Frame) : Prop :=
  ∀ (g : Frame),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    obs = UInt256.ofUInt64 (g.exec.gasAvailable - UInt64.ofNat Gbase)

/-- The `M3` storage correspondence: the self account's stored value at `key` (through
the observable lens) equals the IR world. Threaded as a plain per-frame fact —
preserved across the materialisation by `MatRunsC.storage`. -/
def StorageAgree (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ key, selfStorage fr key = st.world key

/-! ### Transport of the storage side-condition across a sub-frame

`StorageAgree` transports through the self-storage equality `MatRunsC.storage` provides — the
clause the `add`/`lt`/`sstore` recursion needs to pass the storage tie to its second/inner
operand. (The `SloadRealises`/`GasRealises` `.transport` lemmas are retired with their
universals: gas and sload are spilled, so neither is carried by `Corr`/`materialise_runsC`
anymore — Phase B/C.) -/

theorem StorageAgree.transport {st : Lir.IRState} {fr fr' : Frame}
    (h : StorageAgree st fr)
    (hstor : ∀ k, selfStorage fr' k = selfStorage fr k) :
    StorageAgree st fr' :=
  fun key => by rw [hstor key]; exact h key

/-! ## The memory value-channel realisability — `MemRealises`

The memory analogue of `SloadRealises`/`GasRealises`/`StorageAgree`: the bytecode's memory
**realises** the IR's bound call-result locals. For every call-result tmp `t` (registered as
`.slot slot` in `defsOf`) that the IR currently holds a value `v` for, the running frame
carries, at byte offset `slot`:

* **coverage** — `slot + 32 ≤ memory.size` (the 32-byte window is allocated),
  `slot + 32 ≤ activeWords.toNat * 32` (the window is active, i.e. within the
  memory-expansion frontier), and `slot + 63 < 2 ^ 64` (a realistic, non-truncating
  memory offset — `slotOf t = t.id * 32` always is); and
* **value** — `(…mload slot).1 = v` (the readback returns the bound flag).

Coverage travels *with* the value because `MLOAD` is not a pure read — it grows `activeWords`
(memory expansion), which can retroactively un-zero an *uncovered* read. A bound call-result
slot is always covered (the binding MSTORE allocated its bytes and grew `activeWords` over it),
so the coverage is honest and the value survives the materialise sub-runs (`MemRealises.transport`).

The active clause is stated as `slot + 32 ≤ activeWords.toNat * 32` (rather than the weaker
`slot < activeWords.toNat * 32`): for a 32-aligned slot this is exactly "MLOAD at `slot` does
*not* expand memory" (`memoryExpansionWords? activeWords slot 32 = some activeWords`), which is
what pins the readback's gas charge to the abstract two-step MLOAD charge
— the memory analogue of `SloadRealises` resolving the SLOAD warmth cost. -/
def MemRealises (prog : Program) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ t slot v, defsOf prog t = some (.slot slot) → st.locals t = some v →
    (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.memory.size
    ∧ (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.activeWords.toNat * 32
    ∧ slot + 63 < 2 ^ 64
    ∧ (fr.exec.toMachineState.mload (UInt256.ofNat slot)).1 = v

/-- A **covered** `lookupMemory`/`mload` read depends on the machine state only through the
memory bytes — *not* through `activeWords`, as long as both states keep the slot covered.
(`mload_congr` needs `activeWords` *equal*; this is the weaker fact a nondecreasing
`activeWords` supports, which is what `MatRunsC.memActive` carries.) When `slot + 32 ≤
memory.size` and `slot + 32 ≤ activeWords.toNat * 32` on both sides and the bytes agree, the
`lookupMemory` guard is false on both and the read is the same function of the (equal) bytes. -/
theorem mload_covered_congr {m m' : MachineState} (slot : UInt256)
    (hmem : m.memory = m'.memory)
    (hcm  : slot.toNat + 32 ≤ m.memory.size)
    (ham  : slot.toNat + 32 ≤ m.activeWords.toNat * 32)
    (hcm' : slot.toNat + 32 ≤ m'.memory.size)
    (ham' : slot.toNat + 32 ≤ m'.activeWords.toNat * 32) :
    (m.mload slot).1 = (m'.mload slot).1 := by
  show m.lookupMemory slot = m'.lookupMemory slot
  unfold MachineState.lookupMemory
  have hg  : ¬ (slot.toNat ≥ m.memory.size ∨ slot.toNat ≥ m.activeWords.toNat * 32) := by
    push_neg; exact ⟨by omega, by omega⟩
  have hg' : ¬ (slot.toNat ≥ m'.memory.size ∨ slot.toNat ≥ m'.activeWords.toNat * 32) := by
    push_neg; exact ⟨by omega, by omega⟩
  rw [if_neg hg, if_neg hg', hmem]

/-- **Transport of `MemRealises` across a materialise sub-run.** Given the memory `bytes`
unchanged (`MatRunsC.memBytes`) and `activeWords` nondecreasing (`MatRunsC.memActive`),
`MemRealises` carries from `fr` to `fr'`: equal bytes ⇒ equal `.size` ⇒ in-bounds preserved;
nondecreasing `activeWords` ⇒ active preserved; covered + equal bytes ⇒ the readback value is
preserved (`mload_covered_congr`). -/
theorem MemRealises.transport {prog : Program} {st : Lir.IRState} {fr fr' : Frame}
    (h : MemRealises prog st fr)
    (hmem : fr'.exec.toMachineState.memory = fr.exec.toMachineState.memory)
    (hact : fr.exec.toMachineState.activeWords.toNat ≤ fr'.exec.toMachineState.activeWords.toNat) :
    MemRealises prog st fr' := by
  intro t slot v hdef hloc
  obtain ⟨hcm, ham, hreal, hval⟩ := h t slot v hdef hloc
  have hsize : fr'.exec.toMachineState.memory.size = fr.exec.toMachineState.memory.size := by
    rw [hmem]
  have hcm' : (UInt256.ofNat slot).toNat + 32 ≤ fr'.exec.toMachineState.memory.size := by
    rw [hsize]; exact hcm
  have ham' : (UInt256.ofNat slot).toNat + 32 ≤ fr'.exec.toMachineState.activeWords.toNat * 32 := by
    have : fr.exec.toMachineState.activeWords.toNat * 32
        ≤ fr'.exec.toMachineState.activeWords.toNat * 32 := Nat.mul_le_mul_right 32 hact
    omega
  refine ⟨hcm', ham', hreal, ?_⟩
  rw [mload_covered_congr (UInt256.ofNat slot) hmem hcm' ham' hcm ham]
  exact hval

/-- **A covered 32-byte access does not expand memory.** When the slot is already active
(`slot + 32 ≤ activeWords.toNat * 32`) and a realistic offset (`slot + 63 < 2 ^ 64`), the
`M`-bookkeeping for a 32-byte access at `slot` returns `activeWords` unchanged: the access
frontier `(slot + 63) / 32` is already below `activeWords`. This is the zero-memory-expansion
fact that pins the call-result readback's gas charge to the abstract `[Gverylow, Gverylow]`. -/
theorem M_32_eq_self_of_covered (aw : UInt64) (addr : UInt256)
    (hcov : addr.toNat + 32 ≤ aw.toNat * 32) (haddr : addr.toNat + 63 < 2 ^ 64) :
    MachineState.M aw addr.toUInt64 32 = aw := by
  rw [BytecodeLayer.Hoare.MemAlgebra.M_32]
  set x : UInt64 := (addr.toUInt64 + 32 + 31) / 32 with hx
  have hau : addr.toUInt64.toNat = addr.toNat := by
    rw [BytecodeLayer.Hoare.MemAlgebra.toUInt64_toNat, Nat.mod_eq_of_lt (by omega)]
  have hxval : x.toNat = (addr.toNat + 63) / 32 := by
    rw [hx, UInt64.toNat_div]
    simp only [UInt64.toNat_add, hau, show (32:UInt64).toNat = 32 from rfl,
      show (31:UInt64).toNat = 31 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hlen : x.toNat ≤ aw.toNat := by rw [hxval]; omega
  -- `max aw x = aw` since `x ≤ aw` (case-split on the `if` that `Max.max` unfolds to).
  show (if aw ≤ x then x else aw) = aw
  by_cases hc : aw ≤ x
  · rw [if_pos hc]
    rw [UInt64.le_iff_toNat_le] at hc
    apply UInt64.toNat_inj.mp; omega
  · rw [if_neg hc]

/-- `UInt256.ofNat slot` has zero high limbs when `slot < 2 ^ 64`, so its `toUInt64?`
truncation check succeeds: `(UInt256.ofNat slot).toUInt64? = some (UInt256.ofNat slot).toUInt64`.
The call-result slots (`slotOf t = t.id * 32`) are always sub-`2 ^ 64`. -/
theorem toUInt64?_ofNat_of_lt {slot : Nat} (h : slot < 2 ^ 64) :
    (UInt256.ofNat slot).toUInt64? = some (UInt256.ofNat slot).toUInt64 := by
  unfold UInt256.toUInt64?
  have hz : ∀ k, 64 ≤ k → (UInt32.ofNat (slot >>> k)) = 0 := by
    intro k hk
    have : slot >>> k = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_eq_of_lt
      exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hk)
    rw [this]; rfl
  show (if (UInt256.ofNat slot).l2 == 0 && (UInt256.ofNat slot).l3 == 0
        && (UInt256.ofNat slot).l4 == 0 && (UInt256.ofNat slot).l5 == 0
        && (UInt256.ofNat slot).l6 == 0 && (UInt256.ofNat slot).l7 == 0 then _ else _) = _
  rw [show (UInt256.ofNat slot).l2 = UInt32.ofNat (slot >>> 64) from rfl,
      show (UInt256.ofNat slot).l3 = UInt32.ofNat (slot >>> 96) from rfl,
      show (UInt256.ofNat slot).l4 = UInt32.ofNat (slot >>> 128) from rfl,
      show (UInt256.ofNat slot).l5 = UInt32.ofNat (slot >>> 160) from rfl,
      show (UInt256.ofNat slot).l6 = UInt32.ofNat (slot >>> 192) from rfl,
      show (UInt256.ofNat slot).l7 = UInt32.ofNat (slot >>> 224) from rfl,
      hz 64 (by omega), hz 96 (by omega), hz 128 (by omega), hz 160 (by omega),
      hz 192 (by omega), hz 224 (by omega)]
  simp

/-- **A covered, realistic 32-byte `MLOAD`/`MSTORE` does not expand memory.** Under coverage
(`slot + 32 ≤ activeWords.toNat * 32`) and a realistic offset (`slot + 63 < 2 ^ 64`),
`memoryExpansionWords?` at offset `slot`, size 32, returns `activeWords` unchanged — the
expansion frontier is already covered, so no `Cₘ` charge is incurred. -/
theorem memoryExpansionWords?_ofNat_32_of_covered (aw : UInt64) {slot : Nat}
    (hcov : (UInt256.ofNat slot).toNat + 32 ≤ aw.toNat * 32)
    (hreal : slot + 63 < 2 ^ 64) :
    memoryExpansionWords? aw (UInt256.ofNat slot) 32 = some aw := by
  -- `slot < 2^64 < 2^256`, so `ofNat` does not truncate: `(ofNat slot).toNat = slot`.
  have h256 : (2 : ℕ) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hofNat : (UInt256.ofNat slot).toNat = slot := by
    rw [BytecodeLayer.Hoare.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hreal' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by rw [hofNat]; exact hreal
  have haddr64 : (UInt256.ofNat slot).toUInt64.toNat = (UInt256.ofNat slot).toNat := by
    rw [BytecodeLayer.Hoare.MemAlgebra.toUInt64_toNat, Nat.mod_eq_of_lt (by omega)]
  -- the two overflow guards are false (slot is realistic), so the `else` branch fires.
  have hg1 : ¬ (UInt256.ofNat slot).toUInt64 > (0xffffffffffffffff : UInt64) - 32 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt,
        show ((0xffffffffffffffff : UInt64) - 32).toNat = 0xffffffffffffffff - 32 from by decide,
        haddr64]
    omega
  have hg2 : ¬ (UInt256.ofNat slot).toUInt64 + 32 > (0xffffffffffffffff : UInt64) - 31 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt,
        show ((0xffffffffffffffff : UInt64) - 31).toNat = 0xffffffffffffffff - 31 from by decide,
        UInt64.toNat_add, haddr64, show (32 : UInt64).toNat = 32 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    omega
  unfold memoryExpansionWords?
  rw [if_neg (by decide)]
  rw [toUInt64?_ofNat_of_lt (by omega)]
  rw [show UInt256.toUInt64? (32 : Word) = some (32 : UInt64) from by decide]
  simp only [bind, Option.bind]
  rw [if_neg (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    exact ⟨hg1, hg2⟩)]
  rw [M_32_eq_self_of_covered aw (UInt256.ofNat slot) hcov hreal']
end Lir
