import BytecodeLayer.Exec.Frame
import BytecodeLayer.Hoare.MemAlgebra

namespace BytecodeLayer.Exec

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-- The program-counter increment of a `PUSH32` instruction. -/
theorem push32_pcΔ : ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 := by decide

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

end BytecodeLayer.Exec
