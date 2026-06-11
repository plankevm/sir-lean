import ToyExternalCall.IR

/-!
# The metered (gas-exact) semantics — internal proof artifact

This is **not** the IR's specification; the specification is the gasless
semantics in `IR.lean`. The metered semantics instruments every IR action
with exactly the gas accounting of its lowered bytecode, one action per
lowered opcode, mirroring one `EVM.X` iteration each: fuel check (`tick`),
`EVM.Z`'s two-stage gas accounting (`chargeMem`/`requireGas`), `EVM.step`'s
fuel guard (`stepGuard`), then the effect.

It exists for one purpose: the lowering proof. Against the metered
semantics, the bytecode simulation is an on-the-nose equality for *every*
gas level (`Preservation.lowering_correct`), with no "enough gas" side
conditions; the gasless specification is then recovered by erasing gas on
the IR side only (`GasErasure.lean`), never touching the bytecode proofs.

The cost formulas here (`wordTouchCost`, `callTouchCost`, `EVM.Ccall`, …)
are *defined* to be the lowering's costs; the content of the preservation
theorem is that these formulas are what the EVM actually charges, plus all
the decode/stack/pc/loop/halting correctness.

External calls go through a `CallOracle` parameter — internal plumbing that
lets the per-opcode lemmas be stated once. The canonical instantiation
`evmCallOracle` is `EVM.call` itself; `CallSound.lean` proves it satisfies
`CallOracleSound` (i.e. `EVM.call` neither reads nor garbles the frame
fields), which discharges the hypothesis from every downstream theorem.
-/

namespace ToyExternalCall

open EvmYul

namespace Exec

def chargeGas (c : Nat) (s : Exec) : Exec :=
  { s with evm := { s.evm with gasAvailable := s.evm.gasAvailable - UInt256.ofNat c } }

end Exec

/-! ## Gas-exact micro actions -/

/-- First half of `EVM.Z`'s gas accounting: charge the memory-expansion
cost `c₁`. -/
def chargeMem (c₁ : Nat) (s : Exec) : Except EVM.ExecutionException Exec :=
  if s.evm.gasAvailable.toNat < c₁ then .error .OutOfGass
  else .ok (s.chargeGas c₁)

/-- Second half of `EVM.Z`'s gas accounting: check (without deducting) the
instruction cost `c₂`. `c₂` must be computed on the state already charged
with `c₁` — this matters for `CALL`, whose cost reads the gas counter. -/
def requireGas (c₂ : Nat) (s : Exec) : Except EVM.ExecutionException Exec :=
  if s.evm.gasAvailable.toNat < c₂ then .error .OutOfGass
  else .ok s

/-- The gas accounting of `EVM.Z` for instructions whose cost `c₂` does not
depend on the state. -/
def payZ (c₁ c₂ : Nat) (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← chargeMem c₁ s
  requireGas c₂ s

/-- The state bookkeeping of `EVM.step` for non-call instructions: bump the
trace length and deduct the instruction cost. -/
def commit (c₂ : Nat) (s : Exec) : Exec :=
  s.bumpExecLength.chargeGas c₂

/-- One non-call opcode of cost `c₂` and memory-expansion cost `c₁`. -/
def opStep (c₁ c₂ : Nat) (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← tick s
  let s ← payZ c₁ c₂ s
  let s ← stepGuard s
  .ok (commit c₂ s)

/-- Memory-expansion cost of an `MLOAD`/`MSTORE` at `addr`
(cf. `EVM.memoryExpansionCost`). -/
def wordTouchCost (evm : EVM.State) (addr : Word) : Nat :=
  EVM.Cₘ (.ofNat (MachineState.M evm.toMachineState.activeWords.toNat addr.toNat 32)) -
    EVM.Cₘ evm.toMachineState.activeWords

/-- Memory-expansion cost of a `CALL` with the given in/out regions
(cf. `EVM.memoryExpansionCost`). -/
def callTouchCost (evm : EVM.State) (inOffset inSize outOffset outSize : Word) : Nat :=
  EVM.Cₘ (.ofNat
    (MachineState.M
      (MachineState.M evm.toMachineState.activeWords.toNat inOffset.toNat inSize.toNat)
      outOffset.toNat outSize.toNat)) -
    EVM.Cₘ evm.toMachineState.activeWords

/-! ## Per-opcode actions -/

/-- `PUSH32` (also `ADD` and `CALLDATALOAD`): no memory expansion, very-low
cost, no machine-state effect beyond the bookkeeping. -/
def pushStep (s : Exec) : Except EVM.ExecutionException Exec :=
  opStep 0 GasConstants.Gverylow s

/-- `MLOAD` at `addr`: returns the loaded word and the state with expanded
memory accounting. -/
def mloadStep (addr : Word) (s : Exec) : Except EVM.ExecutionException (Word × Exec) := do
  let s ← opStep (wordTouchCost s.evm addr) GasConstants.Gverylow s
  let (v, m) := s.evm.toMachineState.mload addr
  .ok (v, s.setMachineState m)

/-- `MSTORE` of `v` at `addr`. -/
def mstoreStep (addr v : Word) (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← opStep (wordTouchCost s.evm addr) GasConstants.Gverylow s
  .ok (s.setMachineState (s.evm.toMachineState.mstore addr v))

/-! ## Operand evaluation and local update -/

/-- Evaluate an operand. A constant costs one `PUSH32`; a local costs a
`PUSH32` followed by an `MLOAD` of its slot (which can expand memory). -/
def evalOperand (s : Exec) : Operand → Except EVM.ExecutionException (Word × Exec)
  | .const v => do
      let s ← pushStep s
      .ok (v, s)
  | .local x => do
      let s ← pushStep s
      mloadStep (localSlot x) s

/-- Write a local: a `PUSH32` of its slot followed by an `MSTORE`. -/
def writeLocal (s : Exec) (x : Local) (v : Word) : Except EVM.ExecutionException Exec := do
  let s ← pushStep s
  mstoreStep (localSlot x) v s

/-! ## External calls -/

/-- Internal plumbing: the per-opcode `EVM.X` lemmas are stated against an
abstract call function with exactly the signature of the `EVM.call`
instance reached by lowered code (`fuel` and `gasCost` are the values
threaded by `EVM.X`/`EVM.step`; the state is the caller's state at the
`CALL` opcode, memory-expansion cost charged, trace bumped, instruction
cost not yet deducted). The only instantiation used by the final theorems
is `evmCallOracle`, i.e. `EVM.call` itself. -/
abbrev CallOracle :=
  Nat → Nat → EVM.State →
  (gas target value inOffset inSize outOffset outSize : Word) →
  Except EVM.ExecutionException (Word × EVM.State)

/-- The canonical call oracle: `EVM.call` itself, with the environment
arguments the `CALL` opcode passes. -/
def evmCallOracle : CallOracle :=
  fun fuel gasCost s gas target value inOffset inSize outOffset outSize =>
    EVM.call fuel gasCost s.executionEnv.blobVersionedHashes
      gas (.ofNat s.executionEnv.codeOwner) target target value value
      inOffset inSize outOffset outSize
      s.executionEnv.perm s

/-- Frame insensitivity of an oracle, stated at the exact point of use: the
oracle computes what `EVM.call` computes, and `EVM.call` passes the frame
fields (`pc`, `stack`, code) through untouched without reading them.
`CallSound.lean` proves `CallOracleSound evmCallOracle`, so this is a
*lemma* about `EVM.call`, not an assumption, in the final theorems. -/
def CallOracleSound (oracle : CallOracle) : Prop :=
  ∀ (fuel gasCost : Nat) (s : EVM.State)
    (gas target value inOffset inSize outOffset outSize : Word)
    (pc : Word) (stack : List Word) (code : ByteArray),
    EVM.call fuel gasCost s.executionEnv.blobVersionedHashes
      gas (.ofNat s.executionEnv.codeOwner) target target value value
      inOffset inSize outOffset outSize
      s.executionEnv.perm
      (injectFrame s pc stack code) =
    (oracle fuel gasCost s gas target value inOffset inSize outOffset outSize).map
      (fun r => (r.1, injectFrame r.2 pc stack code))

/-- `CALL` with the given (already evaluated) arguments, via the oracle.
Returns the success flag. -/
def callStep (oracle : CallOracle)
    (gas target value inOffset inSize outOffset outSize : Word) (s : Exec) :
    Except EVM.ExecutionException (Word × Exec) := do
  let s ← tick s
  let s ← chargeMem (callTouchCost s.evm inOffset inSize outOffset outSize) s
  -- `Ccall` reads the gas counter, so it is computed on the state already
  -- charged with the memory-expansion cost, exactly as `EVM.Z` computes
  -- `C'` after deducting `cost₁`.
  let c₂ :=
    EVM.Ccall (.ofUInt256 target) (.ofUInt256 target) value gas
      s.evm.accountMap s.evm.toMachineState s.evm.substate
  let s ← requireGas c₂ s
  if ¬ s.evm.executionEnv.perm ∧ value ≠ UInt256.ofNat 0 then
    .error .StaticModeViolation
  else do
    let s ← stepGuard s
    let s := s.bumpExecLength
    match oracle (s.fuel - 1) c₂ s.evm gas target value inOffset inSize outOffset outSize with
    | .error e => .error e
    | .ok (flag, evm') => .ok (flag, { s with evm := evm' })

/-! ## Instruction semantics -/

/-- Execute one IR instruction, charging exactly the gas of its lowering. -/
def execInstr (oracle : CallOracle) (s : Exec) : Instr → Except EVM.ExecutionException Exec
  | .inputLoad dst offset => do
      let (off, s) ← evalOperand s offset
      let s ← pushStep s
      writeLocal s dst (EvmYul.State.calldataload s.evm.toState off)
  | .add dst lhs rhs => do
      -- Operands are evaluated right-to-left, matching the order in which
      -- the lowering pushes them (evaluation can expand memory, so the
      -- order is observable in the gas accounting).
      let (vr, s) ← evalOperand s rhs
      let (vl, s) ← evalOperand s lhs
      let s ← pushStep s
      writeLocal s dst (vl + vr)
  | .call dst args => do
      let (outSize, s) ← evalOperand s args.outSize
      let (outOffset, s) ← evalOperand s args.outOffset
      let (inSize, s) ← evalOperand s args.inSize
      let (inOffset, s) ← evalOperand s args.inOffset
      let (value, s) ← evalOperand s args.value
      let (target, s) ← evalOperand s args.target
      let (gas, s) ← evalOperand s args.gas
      let (flag, s) ← callStep oracle gas target value inOffset inSize outOffset outSize s
      writeLocal s dst flag

/-- The final `STOP` appended by the lowering: clears the return-data buffer
and halts. -/
def stopStep (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← opStep 0 GasConstants.Gzero s
  .ok (s.setMachineState (s.evm.toMachineState.setReturnData .empty))

/-- Run a program under the metered semantics. Structural recursion on the
program; the fuel counter only mirrors `EVM.X`'s and is consumed one unit
per lowered opcode. -/
def run (oracle : CallOracle) : Program → Exec → Except EVM.ExecutionException Exec
  | [], s => stopStep s
  | instr :: rest, s =>
      match execInstr oracle s instr with
      | .ok s' => run oracle rest s'
      | .error e => .error e

end ToyExternalCall
