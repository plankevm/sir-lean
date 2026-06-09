import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.State
import EvmYul.EVM.Gas
import EvmYul.EVM.Semantics

/-!
# A toy IR with a gas-exact executable semantics

The IR is a straight-line register language with three instructions:
`inputLoad` (CALLDATALOAD), `add`, and `call` (external EVM CALL).

Design decisions, in response to the obstructions found in the previous
iteration (see `docs/findings.md`):

* **Locals are memory-backed.** The IR state is an `EVM.State` (plus a fuel
  counter); local `x` denotes the 32-byte memory word at `localSlot x`.
  There is no separate locals map, hence no frame invariant relating two
  copies of the same data: if an external call clobbers a local slot, source
  and target see the identical clobbering.

* **The semantics is gas-exact.** Every IR action charges precisely the gas
  the lowered bytecode charges, including memory-expansion costs, and
  mirrors the fuel discipline of `EVM.X`/`EVM.step`. Consequently the
  lowering theorem needs no "enough gas" side conditions.

* **External calls go through an oracle** with the exact signature of the
  relevant `EVM.call` instance. The only assumption of the lowering theorem
  is `CallOracleSound`: the oracle agrees with `EVM.call`, and `EVM.call`
  neither reads nor garbles the frame fields (`pc`, `stack`, code) that
  distinguish an IR state from its lowered counterpart.

The frame fields `pc`, `stack` and `executionEnv.code` of the embedded
`EVM.State` are *don't care* in IR states: the semantics never reads them,
and the lowering theorem overrides them on both ends via `injectFrame`.
-/

namespace ToyExternalCall

open EvmYul

abbrev Word := UInt256
abbrev Address := AccountAddress
abbrev Local := Nat

/-! ## Syntax -/

inductive Operand where
  | local (x : Local)
  | const (value : Word)
  deriving Repr

structure CallArgs where
  gas : Operand
  target : Operand
  value : Operand
  inOffset : Operand
  inSize : Operand
  outOffset : Operand
  outSize : Operand
  deriving Repr

inductive Instr where
  | inputLoad (dst : Local) (offset : Operand)
  | add (dst : Local) (lhs rhs : Operand)
  | call (dst : Local) (args : CallArgs)
  deriving Repr

abbrev Program := List Instr

/-! ## Memory layout

Locals live in a reserved region of EVM memory. The layout is a fact about
the IR's memory model (local reads/writes *are* `MLOAD`/`MSTORE` at these
addresses), not merely a compilation detail.
-/

def localBase : Nat := 1048576

def localSlot (x : Local) : Word :=
  UInt256.ofNat (localBase + 32 * x)

/-! ## States -/

/-- An IR state: an EVM machine state plus the fuel counter threaded through
`EVM.X`. The `pc`, `stack` and `executionEnv.code` fields of `evm` are unused
by the IR semantics. -/
structure Exec where
  evm : EVM.State
  fuel : Nat

/-- Override the frame fields that distinguish an IR state from the state of
its lowered bytecode: program counter, machine stack and executing code. -/
def injectFrame (evm : EVM.State) (pc : Word) (stack : List Word) (code : ByteArray) :
    EVM.State :=
  { evm with
      pc := pc
      stack := stack
      executionEnv := { evm.executionEnv with code := code } }

namespace Exec

def chargeGas (c : Nat) (s : Exec) : Exec :=
  { s with evm := { s.evm with gasAvailable := s.evm.gasAvailable - UInt256.ofNat c } }

def bumpExecLength (s : Exec) : Exec :=
  { s with evm := { s.evm with execLength := s.evm.execLength + 1 } }

def setMachineState (m : MachineState) (s : Exec) : Exec :=
  { s with evm := { s.evm with toMachineState := m } }

end Exec

/-! ## Gas-exact micro actions

Each lowered opcode is executed by `EVM.X` as: fuel check, decode,
`EVM.Z` (memory-expansion cost, instruction cost, validity checks),
`EVM.step` (fuel check, trace bump, instruction-cost deduction, effect).
The IR semantics mirrors this sequence exactly, one action per opcode.
-/

/-- The fuel check and decrement performed by one `EVM.X` iteration. -/
def tick (s : Exec) : Except EVM.ExecutionException Exec :=
  match s.fuel with
  | 0 => .error .OutOfFuel
  | f + 1 => .ok { s with fuel := f }

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

/-- The fuel check performed by `EVM.step` (depth protection; the counter
itself is only consumed by `EVM.X`). -/
def stepGuard (s : Exec) : Except EVM.ExecutionException Exec :=
  match s.fuel with
  | 0 => .error .OutOfFuel
  | _ + 1 => .ok s

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

/-! ## Per-opcode actions

One action per opcode of the lowered code; each mirrors exactly one
iteration of `EVM.X` for that opcode.
-/

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

/-- The call oracle abstracts the execution of the called contract. Its
signature is exactly that of the `EVM.call` instance reached by lowered
code: `fuel` and `gasCost` are the values threaded by `EVM.X`/`EVM.step`,
and the state is the caller's state at the `CALL` opcode (memory-expansion
cost already charged, trace length already bumped, instruction cost not yet
deducted — `EVM.call` deducts it internally). -/
abbrev CallOracle :=
  Nat → Nat → EVM.State →
  (gas target value inOffset inSize outOffset outSize : Word) →
  Except EVM.ExecutionException (Word × EVM.State)

/-- The lowering theorem's only assumption. It says, jointly:

1. the oracle computes exactly what `EVM.call` computes, and
2. `EVM.call` is insensitive to the frame fields (`pc`, `stack`, code):
   they are passed through to the result state untouched and do not
   influence anything else.

The hypothesis is satisfiable by taking the oracle to *be* `EVM.call`;
part 2 is then a provable (if laborious) fact about `EVM.call`, which never
reads those fields. -/
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

/-- Run a program. Structural recursion on the program; the fuel counter
only mirrors `EVM.X`'s and is consumed one unit per lowered opcode. -/
def run (oracle : CallOracle) : Program → Exec → Except EVM.ExecutionException Exec
  | [], s => stopStep s
  | instr :: rest, s =>
      match execInstr oracle s instr with
      | .ok s' => run oracle rest s'
      | .error e => .error e

end ToyExternalCall
