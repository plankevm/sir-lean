import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.State

namespace ToyExternalCall

open EvmYul

abbrev Word := UInt256
abbrev Address := AccountAddress
abbrev Local := Nat

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

structure CallRequest where
  gas : Word
  target : Address
  value : Word
  input : ByteArray
  outOffset : Word
  outSize : Word

structure CallResult where
  success : Bool
  returnData : ByteArray
  evm : EVM.State

inductive Instr where
  | inputLoad (dst : Local) (offset : Operand)
  | addConst (dst src : Local) (value : Word)
  | call (dst : Local) (args : CallArgs)
  deriving Repr

abbrev Program := List Instr

structure ToyState where
  evm : EVM.State
  locals : Local → Word
  deriving Inhabited

namespace ToyState

def emptyLocals : Local → Word :=
  fun _ => UInt256.ofNat 0

def readLocal (s : ToyState) (x : Local) : Word :=
  s.locals x

def writeLocal (s : ToyState) (x : Local) (v : Word) : ToyState :=
  { s with locals := fun y => if y = x then v else s.locals y }

def evalOperand (s : ToyState) : Operand → Word
  | .local x => s.readLocal x
  | .const value => value

def callDataLoad (s : ToyState) (offset : Word) : Word :=
  EvmYul.State.calldataload s.evm.toState offset

def callInput (s : ToyState) (inOffset inSize : Word) : ByteArray :=
  s.evm.memory.readWithPadding inOffset.toNat inSize.toNat

def setEvm (s : ToyState) (evm : EVM.State) : ToyState :=
  { s with evm := evm }

def setReturnData (s : ToyState) (returnData : ByteArray) : ToyState :=
  { s with evm := { s.evm with returnData := returnData } }

def evalCallRequest (s : ToyState) (args : CallArgs) : CallRequest :=
  let inOffset := s.evalOperand args.inOffset
  let inSize := s.evalOperand args.inSize
  { gas := s.evalOperand args.gas
    target := AccountAddress.ofUInt256 (s.evalOperand args.target)
    value := s.evalOperand args.value
    input := s.callInput inOffset inSize
    outOffset := s.evalOperand args.outOffset
    outSize := s.evalOperand args.outSize }

end ToyState

abbrev CallOracle :=
  ToyState → CallRequest → Except EVM.ExecutionException CallResult

inductive StepResult where
  | ok (state : ToyState)
  | exceptional (state : ToyState) (error : EVM.ExecutionException)

inductive RunResult where
  | ok (state : ToyState)
  | exceptional (state : ToyState) (error : EVM.ExecutionException)
  | outOfFuel (state : ToyState)

def successWord (success : Bool) : Word :=
  if success then UInt256.ofNat 1 else UInt256.ofNat 0

def evalInstr (oracle : CallOracle) (s : ToyState) : Instr → StepResult
  | .inputLoad dst offset =>
      .ok (s.writeLocal dst (s.callDataLoad (s.evalOperand offset)))
  | .addConst dst src value =>
      .ok (s.writeLocal dst (s.readLocal src + value))
  | .call dst args =>
      match oracle s (s.evalCallRequest args) with
      | .ok result =>
          .ok (((s.setEvm result.evm).setReturnData result.returnData).writeLocal dst
            (successWord result.success))
      | .error error =>
          .exceptional s error

def run (oracle : CallOracle) : Nat → ToyState → Program → RunResult
  | 0, s, _ => .outOfFuel s
  | _fuel, s, [] => .ok s
  | fuel + 1, s, instr :: rest =>
      match evalInstr oracle s instr with
      | .ok s' => run oracle fuel s' rest
      | .exceptional s' error => .exceptional s' error

def canonicalProgram (callArgs : CallArgs) (constant : Word) : Program :=
  [ .inputLoad 0 (.const (UInt256.ofNat 0))
  , .addConst 1 0 constant
  , .call 2 { callArgs with target := .local 1 }
  ]

def canonicalZeroValueCallArgs (gas inOffset inSize outOffset outSize : Word) : CallArgs :=
  { gas := .const gas
    target := .const (UInt256.ofNat 0)
    value := .const (UInt256.ofNat 0)
    inOffset := .const inOffset
    inSize := .const inSize
    outOffset := .const outOffset
    outSize := .const outSize }

end ToyExternalCall
