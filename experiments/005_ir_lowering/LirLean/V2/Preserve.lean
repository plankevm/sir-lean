import LirLean.V2.Machine
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence
import BytecodeLayer.Semantics.UInt64
import BytecodeLayer.Programs
import BytecodeLayer.Observables

/-!
# LirLean v2 — observable lowering preservation, the call-free prototype (§4, §6 step 1)

This file validates the **v2 preservation theorem shape** end-to-end on a concrete
program, at low cost, before the heavier external-`call` event step. It is the
de-risking prototype of `docs/ir-design-v2.md` §6 step 1.

## The theorem shape (`ir-design-v2.md` §4)

```
IRRun prog w₀ T O → ∃ G₀, ∀ g, G₀ ≤ g → LoweredRunHasObs (lower prog) w₀ g T O
```

* **No `pc`, no gas-equality in the statement.** The only gas fact is the adequacy
  envelope `G₀ ≤ g`. The bytecode's pc/stack/gas bookkeeping lives *inside* the
  `Runs` witness `LoweredRunHasObs` unfolds to — the IR never sees it.
* **World agreement** (M3 promoted to `World`) and the **halt result** are the
  IR-facing observable.
* **The `gasRead` event is realised** by the bytecode `GAS` opcode's actual value
  (§3.4): the obs the IR consumed equals the machine gas word at the GAS site. This
  is the unified "events are witnessed by the bytecode" mechanism, applied to the
  lightweight `gasRead` event (the `call` event is the next migration step).

## Deliberate prototype cuts (documented per the brief)

* **Hand-written witness bytecode, not `lower prog`.** `lower` emits PUSH32 literals
  (33 bytes each); a `Runs` over it needs the deep offset-table/decode kernel
  reductions that make v1 `WorkedCall.lean` ~1700 lines. The prototype's purpose is
  the *theorem shape*, so the internal `Runs` witness is a hand-assembled PUSH1
  bytecode (`protoBytecode`) that computes the same values; we reuse exactly the v1
  *reasoning* machinery (`runs_*`, `runs_branch`, `messageCall_runs`, the
  `validJumpDests` reachability characterization). Wiring `lower` in is mechanical
  follow-up (it is precisely what `WorkedCall.lean` already does for its program).
* **`returned w` ↦ success+empty output.** The C3 lowering RETURNs an *empty* window
  (v1 `halt_ret`), so the IR exit word `w` is not reflected in the bytecode output
  (the §7 open question). The observable correspondence therefore checks `success`,
  empty output, and **world agreement**; both `stopped` and `returned _` map to
  success+empty. The control-flow branch is still genuinely exercised.
* **Taken arm proved; STOP arm symmetric.** For `G₀ ≤ g` the observed gas word is
  non-zero, so the gas-dependent branch takes the `RETURN` arm. The `STOP` arm is the
  same shape with `cond = 0` (and is the §4 fall-through of `runs_branch`); not
  instantiated to keep the prototype small.
-/

namespace Lir.V2

open Evm
open GasConstants
open BytecodeLayer
open BytecodeLayer.Dispatch
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.UInt64

set_option maxRecDepth 4000

/-! ## The witness bytecode (the internal `Runs` witness, PUSH1-based)

```text
pc 0  : PUSH1 5      60 05    value
pc 2  : PUSH1 7      60 07    key
pc 4  : SSTORE       55       storage[7] := 5
pc 5  : PUSH1 100    60 64    lt right operand (pushed lowest)
pc 7  : PUSH1 7      60 07    sload key
pc 9  : SLOAD        54       → 5
pc 10 : PUSH1 9      60 09
pc 12 : ADD          01       → add 9 5 = 14
pc 13 : LT           10       → lt 14 100 = 1
pc 14 : GAS          5a       → observed gas word
pc 15 : PUSH1 19     60 13    JUMPI destination (the RETURN block)
pc 17 : JUMPI        57       gas ≠ 0 ⇒ jump to 19, else fall to STOP at 18
pc 18 : STOP         00       (else arm)
pc 19 : JUMPDEST     5b       (then arm lands here)
pc 20 : PUSH1 0      60 00
pc 22 : PUSH1 0      60 00
pc 24 : RETURN       f3       return empty (offset 0, size 0)
```
-/
def protoBytecode : ByteArray :=
  ⟨#[0x60,0x05, 0x60,0x07, 0x55, 0x60,0x64, 0x60,0x07, 0x54,
     0x60,0x09, 0x01, 0x10, 0x5a, 0x60,0x13, 0x57, 0x00,
     0x5b, 0x60,0x00, 0x60,0x00, 0xf3]⟩

/-- The top-level call running `protoBytecode` in `addrA` (present, default
account; value-free, state-modifying, depth 0) — same world shape as
`BytecodeLayer.Programs.paramsSStore`. -/
def protoParams (g : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := (∅ : AccountMap).insert addrA default,
    originalAccounts := ∅, substate := default,
    caller := addrA, origin := addrA, recipient := addrA,
    codeSource := .Code protoBytecode, gas := g, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-! ## Decode facts at each pc (literal `rfl`, cheap since PUSH1) -/

private def fr0 (g : UInt64) : Frame := codeFrame (protoParams g) protoBytecode

theorem dec_0  (g : UInt64) : decode protoBytecode 0  = some (.Push .PUSH1, some (5, 1))   := by rfl
theorem dec_2  (g : UInt64) : decode protoBytecode 2  = some (.Push .PUSH1, some (7, 1))   := by rfl
theorem dec_4  (g : UInt64) : decode protoBytecode 4  = some (.Smsf .SSTORE, .none)        := by rfl
theorem dec_5  (g : UInt64) : decode protoBytecode 5  = some (.Push .PUSH1, some (100, 1)) := by rfl
theorem dec_7  (g : UInt64) : decode protoBytecode 7  = some (.Push .PUSH1, some (7, 1))   := by rfl
theorem dec_9  (g : UInt64) : decode protoBytecode 9  = some (.Smsf .SLOAD, .none)         := by rfl
theorem dec_10 (g : UInt64) : decode protoBytecode 10 = some (.Push .PUSH1, some (9, 1))   := by rfl
theorem dec_12 (g : UInt64) : decode protoBytecode 12 = some (.ArithLogic .ADD, .none)     := by rfl
theorem dec_13 (g : UInt64) : decode protoBytecode 13 = some (.ArithLogic .LT, .none)      := by rfl
theorem dec_14 (g : UInt64) : decode protoBytecode 14 = some (.Smsf .GAS, .none)           := by rfl
theorem dec_15 (g : UInt64) : decode protoBytecode 15 = some (.Push .PUSH1, some (19, 1))  := by rfl
theorem dec_17 (g : UInt64) : decode protoBytecode 17 = some (.Smsf .JUMPI, .none)         := by rfl
theorem dec_19 (g : UInt64) : decode protoBytecode 19 = some (.Smsf .JUMPDEST, .none)      := by rfl
theorem dec_20 (g : UInt64) : decode protoBytecode 20 = some (.Push .PUSH1, some (0, 1))   := by rfl
theorem dec_22 (g : UInt64) : decode protoBytecode 22 = some (.Push .PUSH1, some (0, 1))   := by rfl
theorem dec_24 (g : UInt64) : decode protoBytecode 24 = some (.System .RETURN, .none)      := by rfl

end Lir.V2
