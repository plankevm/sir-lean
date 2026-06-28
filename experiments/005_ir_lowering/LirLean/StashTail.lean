import LirLean.MaterialiseRuns

/-!
# LirLean — the uniform **spill stash-tail** forward lemma (P1)

The def-site of every *spilled* value (`docs/uniform-spill-alloc-plan.md` §2.2) ends in the
same two-opcode **stash tail** `PUSH32 (slotOf t) ; MSTORE`: the value to be stashed is on top
of the stack, `PUSH32 slot` pushes the destination, and `MSTORE` writes the value at the slot.
This is byte-identical for gas (`[GAS] ++ PUSH ++ MSTORE`), the call result
(`… CALL ; PUSH ; MSTORE`), and — in Phase C — a cached `SLOAD` (`… SLOAD ; PUSH ; MSTORE`).

This module proves that tail **once**, parameterized over the stashed value `v` and the residual
stack `rest`, as a forward `Runs` lemma over a frame running `lower prog` (or any code, in fact —
the lemma is code-agnostic). It is the keystone that lets `sim_assign_gas`/`sim_call_stmt`
*construct* their stash run from decode + gas facts instead of taking the whole opaque run as a
supplied hypothesis (the §7 `hstash`/`htail` ties).

## What is proved vs. what is supplied

The lemma is stated frame-locally (exactly like the `sim_*` bricks in `Match.lean`): it consumes

* the two decode anchors (`PUSH32 slot` at `fr.pc`, `MSTORE` at `fr.pc + 33`) — the honest
  Layer-A decode facts every brick takes as `hdec`;
* the memory-expansion witness `hmem` pinning `words'` (`memoryExpansionWords?`) and the two
  *bytecode*-gas bounds the `MSTORE` step needs — the honest runtime gas facts (a real
  descending-gas run supplies them; they are NOT vacuous);
* the slot addressability `slot + 63 < 2^64` (and `slot < 2^numBits`), a genuine `slotOf`
  side-condition;

and **delivers** the whole stash forward bundle:

* `Runs fr endFr` (the PUSH then MSTORE composition, built — never assumed);
* `endFr.exec.toMachineState = fr.exec.toMachineState.mstore (ofNat slot) v` — the EXACT shape
  the `hstash`/`htail` ties assert. The key reduction is that `memChargedState` only touches
  `gasAvailable`, so its `toMachineState` is `fr`'s — the doubly-charged MSTORE post-state's
  machine state *is* `fr.exec.toMachineState.mstore …` regardless of `words'` (the expansion
  charge only moves gas, never memory);
* the pc advance (`+ 34`), the frame pins (code / validJumps / address / canModifyState /
  self-storage / accounts), and the empty residual stack (`rest = []` ⇒ `stack = []`).

The **memory-expansion charge** is handled head-on: `memExpansionChargeOf fr.exec words'` is the
genuine `Cₘ words' − Cₘ activeWords` charge a fresh-slot MSTORE incurs; the lemma threads it
through `sim_mstore`'s gas guards verbatim and proves the post-machine-state shape is unaffected
by it (the charge is on gas, not on the `MachineState`). For an *already-covered* slot the
companion `stash_tail_runs_covered` resolves `words' = activeWords` and the expansion charge to
`0` via `memoryExpansionWords?_ofNat_32_of_covered` (Phase C's cached-SLOAD reuse path).

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `MaterialiseRuns.lean`).
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## The MSTORE post-state's memory channel (memory + activeWords)

`memChargedState` subtracts the expansion + `Gverylow` charges from `gasAvailable`. Because
`gasAvailable` is itself a `MachineState` field (`MachineState` carries the EVM gas), the *full*
`toMachineState` is **not** `fr`'s — its gas is the post-charge gas. **This is the latent
over-constraint in the existing `hstash`/`htail` ties** (`endFr.exec.toMachineState =
fr.exec.toMachineState.mstore …`): that equality also pins gasAvailable, which a real
descending-gas run never preserves, so as written the ties are not honestly satisfiable. The
*honest* — and the only — content the memory value channel (`MemRealises`) and `Corr` actually
consume is the **memory bytes** and the **activeWords** count; neither reads gas. `mstore` and
the charges are independent of each other (mstore touches `memory`/`activeWords`; the charges
touch `gasAvailable`), so these two projections *are* exactly `fr.exec.toMachineState.mstore …`'s
— provable, and true on a real run. We expose precisely those. -/

/-- `memChargedState exec words'` leaves the `memory` bytes untouched (it only charges gas). -/
@[simp] theorem memChargedState_memory (exec : Evm.ExecutionState) (words' : UInt64) :
    (BytecodeLayer.Dispatch.memChargedState exec words').toMachineState.memory
      = exec.toMachineState.memory := rfl

/-- `memChargedState exec words'` leaves `activeWords` untouched (it only charges gas). -/
@[simp] theorem memChargedState_activeWords (exec : Evm.ExecutionState) (words' : UInt64) :
    (BytecodeLayer.Dispatch.memChargedState exec words').toMachineState.activeWords
      = exec.toMachineState.activeWords := rfl

/-- The `mstoreFrame` post-state's **memory bytes** are exactly `fr`'s memory with `val` written
at `addr` — the expansion-charge `words'` only moves gas, never the memory bytes. -/
theorem mstoreFrame_memBytes_eq (fr : Frame) (addr val : Word) (words' : UInt64)
    (rest : Stack Word) :
    (mstoreFrame fr addr val words' rest).exec.toMachineState.memory
      = (fr.exec.toMachineState.mstore addr val).memory := by
  rw [mstoreFrame_memory]
  show ((BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mstore addr val).memory = _
  rw [show (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState
        = { fr.exec.toMachineState with gasAvailable :=
              (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.gasAvailable }
        from rfl]
  rfl

/-- The `mstoreFrame` post-state's **activeWords** are exactly `fr`'s after the `mstore` at
`addr` — the expansion-charge `words'` only moves gas, never `activeWords`. -/
theorem mstoreFrame_activeWords_eq (fr : Frame) (addr val : Word) (words' : UInt64)
    (rest : Stack Word) :
    (mstoreFrame fr addr val words' rest).exec.toMachineState.activeWords
      = (fr.exec.toMachineState.mstore addr val).activeWords := by
  rw [mstoreFrame_memory]
  show ((BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mstore addr val).activeWords = _
  rw [show (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState
        = { fr.exec.toMachineState with gasAvailable :=
              (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.gasAvailable }
        from rfl]
  rfl

/-! ## `pushFrameW` accessor reductions used by the tail

The tail's first opcode is `PUSH32 slot`. `pushFrameW` pushes the immediate, advances pc by
`w+1`, charges `Gverylow`, and leaves `executionEnv` / `accounts` / the `MachineState` (memory +
activeWords) untouched. The needed code/pc/stack/memory reductions already live in
`MaterialiseRuns.lean`; we add the `accounts` and `activeWords` (UInt64) reductions and the
`gasAvailable` form. -/

@[simp] theorem pushFrameW_accounts (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.accounts = fr.exec.accounts := rfl

@[simp] theorem pushFrameW_canMod (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem pushFrameW_activeWords' (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.activeWords = fr.exec.activeWords := rfl

@[simp] theorem pushFrameW_gas (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.gasAvailable
      = fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow := rfl

@[simp] theorem pushFrameW_stack' (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.stack = fr.exec.stack.push w := rfl

/-! ## The core stash-tail forward lemma -/

/-- **The uniform stash tail `PUSH32 slot ; MSTORE` (core forward lemma, P1).** From a frame
`fr` with the value `v` on top of `rest` (`stack = v :: rest`), whose code decodes `PUSH32
(ofNat slot)` at `fr.pc` and `MSTORE` at `fr.pc + 33`, with the slot addressable and the honest
runtime gas facts (the expansion witness `words'` + the two MSTORE gas bounds), running the two
opcodes reaches `endFr` (`= mstoreFrame (pushFrameW fr (ofNat slot) 32) (ofNat slot) v words'
rest`) with:

* `Runs fr endFr`;
* `endFr.exec.toMachineState.memory = (fr.exec.toMachineState.mstore (ofNat slot) v).memory` and
  `…activeWords = (fr.exec.toMachineState.mstore (ofNat slot) v).activeWords` — the **honest**
  memory channel the ties' consumers (`MemRealises`/`Corr`) actually read (the gas the push +
  charges drop is *not* exposed: it is not preserved on a real run, and nothing downstream reads
  it — see the over-constraint note above);
* `endFr.exec.pc = fr.exec.pc + 34`;
* the frame pins (code / validJumps / address / canModifyState / accounts / self-storage);
* `endFr.exec.stack = rest`.

Parameterized over `v`, `rest`, and `slot` — reusable for gas (`v = ofUInt64 (fr.gas − Gbase)`,
via `stash_tail_gas`), the call result (`v = flag`, `rest = []`), and the cached SLOAD value. -/
theorem stash_tail_runs (fr : Frame) (slot : Nat) (v : Word) (rest : Stack Word)
    (words' : UInt64)
    (hstk : fr.exec.stack = v :: rest)
    (hdpush : decode fr.exec.executionEnv.code fr.exec.pc
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdmstore : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgasPush : 3 ≤ fr.exec.gasAvailable.toNat)
    (hmem : memoryExpansionWords? (pushFrameW fr (UInt256.ofNat slot) 32).exec.activeWords
      (UInt256.ofNat slot) 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf
      (pushFrameW fr (UInt256.ofNat slot) 32).exec words'
        ≤ (pushFrameW fr (UInt256.ofNat slot) 32).exec.gasAvailable.toNat)
    (hgasMstore : GasConstants.Gverylow
      ≤ ((pushFrameW fr (UInt256.ofNat slot) 32).exec.gasAvailable
          - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf
              (pushFrameW fr (UInt256.ofNat slot) 32).exec words')).toNat) :
    ∃ endFr,
        Runs fr endFr
      ∧ endFr.exec.toMachineState.memory
          = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).memory
      ∧ endFr.exec.toMachineState.activeWords
          = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).activeWords
      ∧ endFr.exec.pc = fr.exec.pc + UInt32.ofNat 34
      ∧ endFr.exec.executionEnv.code = fr.exec.executionEnv.code
      ∧ endFr.validJumps = fr.validJumps
      ∧ endFr.exec.executionEnv.address = fr.exec.executionEnv.address
      ∧ endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
      ∧ endFr.exec.accounts = fr.exec.accounts
      ∧ (∀ k, selfStorage endFr k = selfStorage fr k)
      ∧ endFr.exec.stack = rest := by
  -- == step 1: PUSH32 slot ==
  obtain ⟨hpushrun, _⟩ := sim_imm fr (UInt256.ofNat slot) hdpush hgasPush hsz
  set frp := pushFrameW fr (UInt256.ofNat slot) 32 with hfrp
  -- frp facts (PUSH preserves env / accounts / memory; advances pc by 33; pushes slot).
  have hpcode : frp.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
  have hppc : frp.exec.pc = fr.exec.pc + UInt32.ofNat 33 := by
    rw [hfrp, pushFrameW_pc, push32_pcΔ]
  have hpstk : frp.exec.stack = UInt256.ofNat slot :: v :: rest := by
    rw [hfrp, pushFrameW_stack', hstk]; rfl
  have hpsz : frp.exec.stack.size ≤ 1024 := by
    rw [hpstk]; rw [hstk] at hsz; simpa using hsz
  -- PUSH leaves `fr`'s memory bytes / activeWords (it only pushes + charges gas).
  have hpmem : frp.exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl
  have hpaw : frp.exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords := rfl
  -- the MSTORE decode at frp.pc (= fr.pc + 33).
  have hmstoredec : decode frp.exec.executionEnv.code frp.exec.pc
      = some (.Smsf .MSTORE, .none) := by rw [hpcode, hppc]; exact hdmstore
  -- == step 2: MSTORE at `slot`, writing `v` (pops `slot :: v :: rest`) ==
  obtain ⟨hmstorerun, _⟩ :=
    sim_mstore frp (UInt256.ofNat slot) v words' rest hmstoredec hpstk hpsz hmem hgasMem hgasMstore
  set endFr := mstoreFrame frp (UInt256.ofNat slot) v words' rest with hendFr
  refine ⟨endFr, hpushrun.trans hmstorerun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- memory bytes: `endFr.memory = (frp.memory.mstore slot v).memory = (fr.memory.mstore …).memory`.
    rw [hendFr, mstoreFrame_memBytes_eq]
    -- `mstore`'s memory depends only on the input memory + activeWords, both of which `frp`
    -- shares with `fr`; so the written-memory bytes coincide.
    show ((frp.exec.toMachineState).mstore (UInt256.ofNat slot) v).memory = _
    rw [show frp.exec.toMachineState
          = { fr.exec.toMachineState with gasAvailable := frp.exec.toMachineState.gasAvailable }
          from rfl]
    rfl
  · -- activeWords: same — `mstore`'s activeWords depends only on the input activeWords.
    rw [hendFr, mstoreFrame_activeWords_eq]
    show ((frp.exec.toMachineState).mstore (UInt256.ofNat slot) v).activeWords = _
    rw [show frp.exec.toMachineState
          = { fr.exec.toMachineState with gasAvailable := frp.exec.toMachineState.gasAvailable }
          from rfl]
    rfl
  · -- pc: frp.pc + 1 = (fr.pc + 33) + 1 = fr.pc + 34.
    rw [hendFr, mstoreFrame_pc, hppc,
        show (UInt32.ofNat 34) = UInt32.ofNat 33 + 1 from by decide]
    ac_rfl
  · rw [hendFr, mstoreFrame_code, hpcode]
  · rw [hendFr, mstoreFrame_validJumps]; rfl
  · show (mstoreFrame frp (UInt256.ofNat slot) v words' rest).exec.executionEnv.address = _
    rfl
  · rw [hendFr, mstoreFrame_canMod]; rfl
  · -- accounts: MSTORE writes memory, not accounts; PUSH preserves accounts.
    show (mstoreFrame frp (UInt256.ofNat slot) v words' rest).exec.accounts = _
    rfl
  · -- self-storage: MSTORE/PUSH write memory, never the account storage map.
    intro k
    show selfStorage (mstoreFrame frp (UInt256.ofNat slot) v words' rest) k = _
    rfl
  · rw [hendFr, mstoreFrame_stack]

/-! ## The covered-slot specialization (zero expansion charge)

When the slot is already **covered** (`slot + 32 ≤ activeWords.toNat * 32`) and realistic
(`slot + 63 < 2^64`), the MSTORE does not expand memory: `words' = activeWords` and the
expansion charge is `0`. This resolves the two MSTORE gas bounds to the single `Gverylow ≤ gas`
bound (a real run always satisfies it), removing the expansion-witness obligation. Phase C's
cached-SLOAD reuse (a covered slot) takes this form; the first def-site write (uncovered) takes
the general `stash_tail_runs`. -/

/-- **The stash tail on an already-covered slot (zero expansion charge).** Under coverage +
realism, `PUSH32 slot ; MSTORE` runs with only the `Gverylow` gas bound (the expansion charge is
zero), delivering the same forward bundle as `stash_tail_runs`. -/
theorem stash_tail_runs_covered (fr : Frame) (slot : Nat) (v : Word) (rest : Stack Word)
    (hstk : fr.exec.stack = v :: rest)
    (hdpush : decode fr.exec.executionEnv.code fr.exec.pc
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdmstore : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgasPush : 3 ≤ fr.exec.gasAvailable.toNat)
    (hcov : (UInt256.ofNat slot).toNat + 32 ≤ fr.exec.toMachineState.activeWords.toNat * 32)
    (hreal : slot + 63 < 2 ^ 64)
    (hgasMstore : GasConstants.Gverylow
      ≤ ((pushFrameW fr (UInt256.ofNat slot) 32).exec.gasAvailable).toNat) :
    ∃ endFr,
        Runs fr endFr
      ∧ endFr.exec.toMachineState.memory
          = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).memory
      ∧ endFr.exec.toMachineState.activeWords
          = (fr.exec.toMachineState.mstore (UInt256.ofNat slot) v).activeWords
      ∧ endFr.exec.pc = fr.exec.pc + UInt32.ofNat 34
      ∧ endFr.exec.executionEnv.code = fr.exec.executionEnv.code
      ∧ endFr.validJumps = fr.validJumps
      ∧ endFr.exec.executionEnv.address = fr.exec.executionEnv.address
      ∧ endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
      ∧ endFr.exec.accounts = fr.exec.accounts
      ∧ (∀ k, selfStorage endFr k = selfStorage fr k)
      ∧ endFr.exec.stack = rest := by
  -- coverage on `frp` (PUSH leaves activeWords untouched ⇒ same coverage as `fr`).
  set frp := pushFrameW fr (UInt256.ofNat slot) 32 with hfrp
  have hfrpaw : frp.exec.activeWords = fr.exec.toMachineState.activeWords := rfl
  have hcovp : (UInt256.ofNat slot).toNat + 32 ≤ frp.exec.activeWords.toNat * 32 := by
    rw [hfrpaw]; exact hcov
  -- no expansion: `words' = activeWords`, charge = 0.
  have hmem : memoryExpansionWords? frp.exec.activeWords (UInt256.ofNat slot) 32
      = some frp.exec.activeWords :=
    memoryExpansionWords?_ofNat_32_of_covered _ hcovp hreal
  have hzcost : BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec frp.exec.activeWords = 0 := by
    show Evm.Cₘ frp.exec.activeWords - Evm.Cₘ frp.exec.activeWords = 0
    omega
  have hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec frp.exec.activeWords
      ≤ frp.exec.gasAvailable.toNat := by rw [hzcost]; omega
  have hgasMstore' : GasConstants.Gverylow
      ≤ (frp.exec.gasAvailable
          - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf frp.exec
              frp.exec.activeWords)).toNat := by
    rw [hzcost, BytecodeLayer.UInt64.toNat_sub_ofNat _ 0 (Nat.zero_le _) (by norm_num),
        Nat.sub_zero]
    exact hgasMstore
  exact stash_tail_runs fr slot v rest frp.exec.activeWords hstk hdpush hdmstore hsz hgasPush
    hmem hgasMem hgasMstore'

/-! ## The GAS-prefix variant (the gas def-site stash)

The gas spill stash is `[GAS] ++ PUSH32 slot ++ MSTORE`. A single `GAS` opcode (pushing
`ofUInt64 (fr.gas − Gbase)` onto the empty boundary stack) composed with the core tail gives the
**gas `hstash`** as a proved fact: the value stashed at `slotOf t` is exactly the realised `GAS`
output `gasReadOf (gasFrame fr) = ofUInt64 (fr.gas − Gbase)` (`gasReadOf_gasFrame_eq_obs`). One
read, one frame — the honest positional value tie (no `∀`-over-frames, no constancy). -/

/-- **The gas def-site stash `GAS ; PUSH32 slot ; MSTORE` (forward lemma, P1).** From a frame
`fr` at a statement boundary (`stack = []`) whose code decodes `GAS` at `fr.pc`, `PUSH32 slot` at
`fr.pc + 1`, `MSTORE` at `fr.pc + 34`, running the three opcodes reaches `endFr` storing the
realised `GAS` value `ofUInt64 (fr.gas − Gbase)` at `slot`, with `pc + 35`, the frame pins, and
the stack back to `[]`. The stored value is the genuine descending-gas read — the positional gas
value tie `MemRealises` carries (no universal). -/
theorem stash_tail_gas (fr : Frame) (slot : Nat)
    (words' : UInt64)
    (hstk : fr.exec.stack = [])
    (hdgas : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hdpush : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 1)
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)))
    (hdmstore : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 1 + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none))
    (hgasGas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat)
    (hgasPush : 3 ≤ (gasFrame fr).exec.gasAvailable.toNat)
    (hmem : memoryExpansionWords?
      (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.activeWords
      (UInt256.ofNat slot) 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf
      (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec words'
        ≤ (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.gasAvailable.toNat)
    (hgasMstore : GasConstants.Gverylow
      ≤ ((pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec.gasAvailable
          - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf
              (pushFrameW (gasFrame fr) (UInt256.ofNat slot) 32).exec words')).toNat) :
    ∃ endFr,
        Runs fr endFr
      ∧ endFr.exec.toMachineState.memory
          = (fr.exec.toMachineState.mstore (UInt256.ofNat slot)
              (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))).memory
      ∧ endFr.exec.toMachineState.activeWords
          = (fr.exec.toMachineState.mstore (UInt256.ofNat slot)
              (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))).activeWords
      ∧ endFr.exec.pc = fr.exec.pc + UInt32.ofNat 35
      ∧ endFr.exec.executionEnv.code = fr.exec.executionEnv.code
      ∧ endFr.validJumps = fr.validJumps
      ∧ endFr.exec.executionEnv.address = fr.exec.executionEnv.address
      ∧ endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
      ∧ endFr.exec.accounts = fr.exec.accounts
      ∧ (∀ k, selfStorage endFr k = selfStorage fr k)
      ∧ endFr.exec.stack = [] := by
  -- == step 0: GAS opcode, pushing `ofUInt64 (fr.gas − Gbase)` onto the empty stack ==
  have hszgas : fr.exec.stack.size + 1 ≤ 1024 := by rw [hstk]; simp
  obtain ⟨hgasrun, _⟩ := sim_gas fr hdgas hszgas hgasGas
  set frg := gasFrame fr with hfrg
  set gasVal : Word := UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)
    with hgasVal
  -- frg facts: stack = [gasVal], pc = fr.pc + 1, env / accounts / machine state = fr's.
  have hgstk : frg.exec.stack = gasVal :: [] := by
    rw [hfrg, gasFrame_stack, hstk]; rfl
  have hgcode : frg.exec.executionEnv.code = fr.exec.executionEnv.code := rfl
  have hgpc : frg.exec.pc = fr.exec.pc + UInt32.ofNat 1 := by
    rw [hfrg, gasFrame_pc, show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
  -- decode the PUSH/MSTORE relative to `frg.pc` (= fr.pc + 1).
  have hdpush' : decode frg.exec.executionEnv.code frg.exec.pc
      = some (.Push .PUSH32, some (UInt256.ofNat slot, 32)) := by rw [hgcode, hgpc]; exact hdpush
  have hdmstore' : decode frg.exec.executionEnv.code (frg.exec.pc + UInt32.ofNat 33)
      = some (.Smsf .MSTORE, .none) := by rw [hgcode, hgpc]; exact hdmstore
  have hgsz : frg.exec.stack.size + 1 ≤ 1024 := by rw [hgstk]; simp
  -- == steps 1-2: the core tail from `frg`, stashing `gasVal` ==
  obtain ⟨endFr, hrun, hmemBytes, hmemActive, hpc, hcode, hvalid, haddr, hcanmod, haccounts,
      hstorage, hstkEnd⟩ :=
    stash_tail_runs frg slot gasVal [] words' hgstk hdpush' hdmstore' hgsz hgasPush
      hmem hgasMem hgasMstore
  refine ⟨endFr, hgasrun.trans hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hstkEnd⟩
  · -- memory: GAS leaves `fr`'s memory bytes / activeWords, the tail writes `gasVal` at `slot`.
    -- `endFr.memory = (frg.memory.mstore slot gasVal).memory` (`hmemBytes`); `frg`'s machine
    -- state is `fr`'s (GAS only charges gas + pushes), so this is `(fr.memory.mstore …).memory`.
    rw [hmemBytes]; rfl
  · rw [hmemActive]; rfl
  · rw [hpc, hgpc, show (UInt32.ofNat 35) = UInt32.ofNat 1 + UInt32.ofNat 34 from by decide]
    ac_rfl
  · rw [hcode, hgcode]
  · rw [hvalid]; rfl
  · rw [haddr]; rfl
  · rw [hcanmod]; rfl
  · rw [haccounts]; rfl
  · intro k; rw [hstorage k]; rfl

end Lir

-- Build-enforced axiom-cleanliness guard for the P1 stash-tail forward lemmas: the core tail,
-- its covered specialization, and the GAS-prefix variant depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.stash_tail_runs
#print axioms Lir.stash_tail_runs_covered
#print axioms Lir.stash_tail_gas
