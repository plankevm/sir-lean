import LirLean.Frame.Match
import LirLean.Materialise.MaterialiseGas
import LirLean.Materialise.DefsSound
import BytecodeLayer.Exec.Memory

/-!
# LirLean — materialisation value-channel adapters

This module retains the IR-indexed materialisation side conditions:

* `evalExpr_obs_irrel` for the pure expression fragment;
* `StorageAgree` for the IR-state storage lens;
* `MemRealises` for the IR temporary-to-memory channel;
* the legacy `GasRealises` predicate still reached by the current correspondence proofs.

The EVM-only frame, stash, and memory facts are re-exported for these adapters.
-/

namespace Lir

export BytecodeLayer.Exec
  (pushFrameW_code pushFrameW_validJumps addFrame_validJumps ltFrame_validJumps
   sloadFrame_validJumps gasFrame_validJumps pushFrameW_addr pushFrameW_selfStorage
   pushFrameW_pc addFrame_code addFrame_addr addFrame_selfStorage addFrame_pc ltFrame_code
   ltFrame_addr ltFrame_selfStorage ltFrame_pc sloadFrame_code sloadFrame_addr
   sloadFrame_selfStorage sloadFrame_pc sloadFrame_stack sloadFrame_gas gasFrame_code
   gasFrame_addr gasFrame_selfStorage gasFrame_pc gasFrame_stack gasFrame_gas pushFrameW_memory
   pushFrameW_activeWords addFrame_memory addFrame_activeWords ltFrame_memory ltFrame_activeWords
   sloadFrame_memory sloadFrame_activeWords gasFrame_memory gasFrame_activeWords StashRuns
   mload_covered_congr M_32_eq_self_of_covered toUInt64?_ofNat_of_lt
   memoryExpansionWords?_ofNat_32_of_covered push32_pcΔ)

open BytecodeLayer.Exec
open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## Small arithmetic facts -/

/-- `(emitImm w).length = 33` (a `PUSH32` opcode byte + 32 immediate bytes). -/
theorem emitImm_length (w : Word) : (emitImm w).length = 33 := by
  simp [emitImm, BytecodeLayer.Exec.wordBytesBE]

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

**Phase B/C**: gas and sload are now **spilled** — a bare `Expr.gas` / `Expr.sload _` is never
materialised (uses go through `.slot`/MLOAD; the def-site stash is run by `sim_assign_gas` /
`sim_assign_sload`). So the `.gas` and `.sload` arms of `materialise_runsC` are **unreachable**,
discharged by `e ≠ .gas` and `∀ k, e ≠ .sload k` (both preserved across the `.tmp` recursion by
`defsOf_ne_gas`/`defsOf_ne_sload`). The two former realisability universals are retired:

* The retired SLOAD warmth universal and recorder stream are gone. The SLOAD value lives in the
  slot and is tied by `MemRealises`; its gas effect is already reflected by the EVM run.

* **`GasRealises`** (RETIRED, Phase B) — the analogous `∀ g`-gas-value universal; same story.

* **`StorageAgree`** — the still-live `M3` storage correspondence `selfStorage fr key = st.world
  key`. Preserved across the whole materialisation by `MatRunsC.storage` (every post-frame leaves
  the self account's storage *values* untouched), threading as a plain per-frame fact. It ties the
  storage lens to `evalExpr`'s world read (consumed by the `sstore` value/key materialise calls). -/

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
operand. The retired GAS/SLOAD transport lemmas are unnecessary because both values are spilled. -/

theorem StorageAgree.transport {st : Lir.IRState} {fr fr' : Frame}
    (h : StorageAgree st fr)
    (hstor : ∀ k, selfStorage fr' k = selfStorage fr k) :
    StorageAgree st fr' :=
  fun key => by rw [hstor key]; exact h key

/-! ## The memory value-channel realisability — `MemRealises`

The bytecode's memory **realises** the IR's bound spilled locals. For every tmp `t` registered as
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
what pins the readback's gas charge to the abstract two-step MLOAD charge. -/
def MemRealises (prog : Program) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ t slot v, defsOf prog t = some (.slot slot) → st.locals t = some v →
    (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.memory.size
    ∧ (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.activeWords.toNat * 32
    ∧ slot + 63 < 2 ^ 64
    ∧ (fr.exec.toMachineState.mload (UInt256.ofNat slot)).1 = v


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

end Lir
