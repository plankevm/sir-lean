import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.State
import EvmYul.EVM.Gas
import EvmYul.EVM.Semantics

/-!
# A toy IR over the EVM state, with a gasless executable semantics

The IR is a straight-line register language with three instructions:
`inputLoad` (CALLDATALOAD), `add`, and `call` (external EVM CALL).

**The specification is the `Gasless` semantics in this file.** Its design:

* **No gas.** The IR does not model gas. The gas counter of the embedded
  EVM state is *dead*: the semantics neither reads it nor lets it influence
  any result. Consequently the IR cannot run out of gas, and the lowering
  theorem (`Correctness.lean`) is a refinement: for every IR run that
  succeeds there is a gas bound `G₀` such that the lowered bytecode,
  funded with any `G ≥ G₀`, produces the same final state up to the
  remaining gas. Under-funded bytecode runs may fail with `OutOfGass`;
  the theorem promises nothing about them — exactly the freedom a
  gas-optimizing compiler needs.

* **External calls are the real thing.** `Gasless.callStep` executes the
  callee's actual bytecode by invoking EVMYulLean's own `EVM.call` — the
  very function the lowered `CALL` opcode reaches — on a *full tank* (gas
  counter set to its maximum, so the 63/64 forwarding cap never bites and
  the callee receives exactly the gas the program asked for). There is no
  call oracle, no assumption about callee behavior: arbitrary bytecode
  runs, reentrancy included, on both sides of the lowering theorem.

* **Locals are memory-backed.** The IR state is an `EVM.State` (plus a
  fuel counter); local `x` denotes the 32-byte memory word at
  `localSlot x`. There is no separate locals map, hence no frame invariant
  relating two copies of the same data.

* **Fuel is a termination device, not a resource.** EVMYulLean's execution
  is fuel-bounded (one unit per opcode, recursion depth for calls); the IR
  mirrors that discipline one unit per *lowered* opcode so that source and
  target run out of fuel at exactly the same point. Fuel never measures
  cost.

The `pc`, `stack` and `executionEnv.code` fields of the embedded
`EVM.State` are *don't care* in IR states — the semantics never reads
them — and the gas counter `gasAvailable` is dead as described above.
`injectFrame` overrides the first three; the lowering theorem quantifies
the gas counter away.
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
by the IR semantics, and `gasAvailable` is dead in the gasless semantics. -/
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

def bumpExecLength (s : Exec) : Exec :=
  { s with evm := { s.evm with execLength := s.evm.execLength + 1 } }

def setMachineState (m : MachineState) (s : Exec) : Exec :=
  { s with evm := { s.evm with toMachineState := m } }

/-- Set the (dead) gas counter. Used only to state the lowering theorem:
the IR semantics itself never reads gas. -/
def withGas (g : Word) (s : Exec) : Exec :=
  { s with evm := { s.evm with gasAvailable := g } }

end Exec

/-- The fuel check and decrement performed by one `EVM.X` iteration. -/
def tick (s : Exec) : Except EVM.ExecutionException Exec :=
  match s.fuel with
  | 0 => .error .OutOfFuel
  | f + 1 => .ok { s with fuel := f }

/-- The fuel check performed by `EVM.step` (depth protection; the counter
itself is only consumed by `EVM.X`). -/
def stepGuard (s : Exec) : Except EVM.ExecutionException Exec :=
  match s.fuel with
  | 0 => .error .OutOfFuel
  | _ + 1 => .ok s

/-! ## The gasless semantics -/

namespace Gasless

/-- One non-call opcode of the lowered code: one unit of fuel, `EVM.step`'s
fuel guard, and the trace-length bump. No gas. -/
def opStep (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← tick s
  let s ← stepGuard s
  .ok s.bumpExecLength

/-- `MLOAD` at `addr`: returns the loaded word; memory accounting
(`activeWords`) expands exactly as the EVM's does. -/
def mloadStep (addr : Word) (s : Exec) : Except EVM.ExecutionException (Word × Exec) := do
  let s ← opStep s
  let (v, m) := s.evm.toMachineState.mload addr
  .ok (v, s.setMachineState m)

/-- `MSTORE` of `v` at `addr`. -/
def mstoreStep (addr v : Word) (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← opStep s
  .ok (s.setMachineState (s.evm.toMachineState.mstore addr v))

/-- Evaluate an operand. A constant is one lowered opcode (`PUSH32`); a
local is a push of its slot followed by an `MLOAD`. Operands are evaluated
right-to-left below, matching the order in which the lowering pushes them;
with gas erased the order is unobservable, but keeping it aligned makes the
erasure proof a literal step-for-step match. -/
def evalOperand (s : Exec) : Operand → Except EVM.ExecutionException (Word × Exec)
  | .const v => do
      let s ← opStep s
      .ok (v, s)
  | .local x => do
      let s ← opStep s
      mloadStep (localSlot x) s

/-- Write a local: a push of its slot followed by an `MSTORE`. -/
def writeLocal (s : Exec) (x : Local) (v : Word) : Except EVM.ExecutionException Exec := do
  let s ← opStep s
  mstoreStep (localSlot x) v s

/-- A full tank: the gas counter at its maximum. The gasless semantics
executes calls on a full tank, so the EVM's 63/64 forwarding cap never
binds and the callee receives exactly the gas the program asked for (for
any gas argument below ~63/64 of 2²⁵⁶). -/
def fullTank (evm : EVM.State) : EVM.State :=
  { evm with gasAvailable := .ofNat (UInt256.size - 1) }

/-- External `CALL`: execute the callee's actual bytecode via EVMYulLean's
own `EVM.call` — the very function the lowered `CALL` opcode reaches — on a
full tank. Arbitrary callee code runs (reentrancy included); the callee's
effects on accounts, storage, logs and the caller's return-data buffer and
output region are exactly the EVM's. The success flag is returned.

The deducted instruction cost is passed as `0` and the resulting gas
counter is garbage; both only touch the dead gas field. -/
def callStep (gas target value inOffset inSize outOffset outSize : Word) (s : Exec) :
    Except EVM.ExecutionException (Word × Exec) := do
  let s ← tick s
  if ¬ s.evm.executionEnv.perm ∧ value ≠ UInt256.ofNat 0 then
    .error .StaticModeViolation
  else do
    let s ← stepGuard s
    let s := s.bumpExecLength
    match EVM.call (s.fuel - 1) 0 s.evm.executionEnv.blobVersionedHashes
        gas (.ofNat s.evm.executionEnv.codeOwner) target target value value
        inOffset inSize outOffset outSize
        s.evm.executionEnv.perm (fullTank s.evm) with
    | .error e => .error e
    | .ok (flag, evm') => .ok (flag, { s with evm := evm' })

/-! ## Instruction semantics -/

/-- Execute one IR instruction. -/
def execInstr (s : Exec) : Instr → Except EVM.ExecutionException Exec
  | .inputLoad dst offset => do
      let (off, s) ← evalOperand s offset
      let s ← opStep s
      writeLocal s dst (EvmYul.State.calldataload s.evm.toState off)
  | .add dst lhs rhs => do
      let (vr, s) ← evalOperand s rhs
      let (vl, s) ← evalOperand s lhs
      let s ← opStep s
      writeLocal s dst (vl + vr)
  | .call dst args => do
      let (outSize, s) ← evalOperand s args.outSize
      let (outOffset, s) ← evalOperand s args.outOffset
      let (inSize, s) ← evalOperand s args.inSize
      let (inOffset, s) ← evalOperand s args.inOffset
      let (value, s) ← evalOperand s args.value
      let (target, s) ← evalOperand s args.target
      let (gas, s) ← evalOperand s args.gas
      let (flag, s) ← callStep gas target value inOffset inSize outOffset outSize s
      writeLocal s dst flag

/-- The final halt (the lowering's terminal `STOP`): clears the return-data
buffer. -/
def stopStep (s : Exec) : Except EVM.ExecutionException Exec := do
  let s ← opStep s
  .ok (s.setMachineState (s.evm.toMachineState.setReturnData .empty))

/-- Run a program. Structural recursion on the program; fuel is consumed
one unit per lowered opcode, mirroring `EVM.X`. The possible errors are
`OutOfFuel` (artifact of the fuel discipline), `StaticModeViolation`, and
a callee's `OutOfFuel` propagated by `EVM.call` — never `OutOfGass`. -/
def run : Program → Exec → Except EVM.ExecutionException Exec
  | [], s => stopStep s
  | instr :: rest, s =>
      match execInstr s instr with
      | .ok s' => run rest s'
      | .error e => .error e

end Gasless

end ToyExternalCall
