import Evm

/-!
# The example programs and world

This is the **data** experiment 003 proves things about — the handwritten
bytecode contracts, the addresses they live at, and the `messageCall` entry
points (`CallParams`) that run them. Nothing here is a theorem or a proof; it is
the concrete material the specs in `Spec.lean` quantify over.

Each program is raw EVM bytecode (`ByteArray` of opcode bytes). The comment above
each one is its disassembly.

Read together with `Spec.lean` (what we prove) and `Observables.lean` (the lens
we observe results through).
-/

namespace BytecodeLayer
open Evm

/-! ## Addresses -/

/-- The single self-account used by the call-free programs, `0xC0FFEE`. -/
def addrA : AccountAddress := AccountAddress.ofNat 0xC0FFEE

/-- The caller contract's address, `0xCA11E2`. -/
def addrCaller : AccountAddress := AccountAddress.ofNat 0xCA11E2

/-- The callee contract's address, `0xCA11EE` (= `13242862`). -/
def addrCallee : AccountAddress := AccountAddress.ofNat 0xCA11EE

/-! ## Call-free programs (M1) -/

/-- The single-`STOP` program. -/
def stopProgram : ByteArray := ⟨#[0x00]⟩

/-- `PUSH1 0x05 ; STOP`. -/
def pushStopProgram : ByteArray := ⟨#[0x60, 0x05, 0x00]⟩

/-- `PUSH1 0x05 ; PUSH1 0x07 ; SSTORE ; STOP` — store `5` at slot `7`, then stop. -/
def sstoreProgram : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x07, 0x55, 0x00]⟩

/-- `PUSH1 5 ; PUSH1 7 ; SSTORE ; PUSH1 0x0B ; PUSH1 9 ; SSTORE ; STOP` — two
cold writes (`7 ↦ 5`, then `9 ↦ 11`). -/
def seqProgram : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x07, 0x55, 0x60, 0x0B, 0x60, 0x09, 0x55, 0x00]⟩

/-- `PUSH1 0 ; PUSH1 0 ; RETURN` — return empty output (offset 0, size 0). The
zero-size `RETURN` charges no memory gas, so the program's exact cost is `6`. -/
def returnProgram : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0xF3]⟩

/-! ## The external-call programs (M2) -/

/-- caller: `PUSH1 0 ×5 ; PUSH3 0xCA11EE ; PUSH4 0xFFFFFFFF ; CALL ; STOP`.
Pushes the seven CALL args (value-free, zero-memory; the gas arg `0xFFFFFFFF` is
large, so the 63/64 cap always binds, never the literal), forwards a `CALL` to
the callee, then stops. -/
def callerProg : ByteArray :=
  ⟨#[0x60,0x00, 0x60,0x00, 0x60,0x00, 0x60,0x00, 0x60,0x00,
     0x62,0xCA,0x11,0xEE, 0x63,0xFF,0xFF,0xFF,0xFF, 0xF1, 0x00]⟩

/-- callee: `PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP` — stores `5` at slot `7`. Its cold
first-write cost is `22106`. -/
def calleeProg : ByteArray := ⟨#[0x60,0x05, 0x60,0x07, 0x55, 0x00]⟩

def callerAccount : Account := { (default : Account) with code := callerProg }
def calleeAccount : Account := { (default : Account) with code := calleeProg }

/-- The world for the call example: caller and callee accounts, each with its code. -/
def accts : AccountMap :=
  ((∅ : AccountMap).insert addrCaller callerAccount).insert addrCallee calleeAccount

/-! ## Message-call entry points

The `CallParams` that run each program as a top-level `messageCall p`. `gas := g`
is the only thing that varies; everything else fixes the world, the code source,
and a value-free, calldata-free, state-modifying call at depth 0.
-/

/-- Run `sstoreProgram` in `addrA` (present with a default account). -/
def paramsSStore (g : UInt64) : CallParams :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := #[]
    accounts := (∅ : AccountMap).insert addrA default
    originalAccounts := ∅
    substate := default
    caller := addrA
    origin := addrA
    recipient := addrA
    codeSource := .Code sstoreProgram
    gas := g
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 0
    canModifyState := true }

/-- Run `seqProgram` in `addrA`. -/
def paramsSeq (g : UInt64) : CallParams :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := #[]
    accounts := (∅ : AccountMap).insert addrA default
    originalAccounts := ∅
    substate := default
    caller := addrA
    origin := addrA
    recipient := addrA
    codeSource := .Code seqProgram
    gas := g
    gasPrice := 0
    value := 0
    apparentValue := 0
    calldata := .empty
    depth := 0
    blockHeader := default
    chainId := 0
    canModifyState := true }

/-- Top-level message-call into the caller contract (which forwards a `CALL` to
the callee). The whole external-call story runs from here. -/
def callerParams (g : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := accts, originalAccounts := ∅, substate := default,
    caller := addrCaller, origin := addrCaller, recipient := addrCaller,
    codeSource := .Code callerProg, gas := g, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

end BytecodeLayer
