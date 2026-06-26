import EvmYul.Operations

import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.PrimOps
import EvmYul.EVM.StateOps
import EvmYul.Wheels

import EvmYul.UInt256
import EvmYul.StateOps
import EvmYul.SharedStateOps
import EvmYul.MachineStateOps

import EvmYul.SpongeHash.Keccak256

--

import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256
import EvmYul.MachineState

--

namespace EvmYul

section Semantics

open Stack

/--
`Transformer` is the primop-evaluating semantic function type for the EVM.

`EVM.State → EVM.State` because the arguments are already contained in `EVM.State.stack`,
in the `EVM.Exception` error monad.
-/
private abbrev Transformer : Type := EVM.Transformer

private def dispatchInvalid : Transformer := λ _ ↦ .error .InvalidInstruction

private def dispatchUnary : Primop.Unary → Transformer := EVM.execUnOp

private def dispatchBinary : Primop.Binary → Transformer := EVM.execBinOp

private def dispatchTernary : Primop.Ternary → Transformer := EVM.execTriOp

private def dispatchQuartiary : Primop.Quaternary → Transformer := EVM.execQuadOp

private def dispatchExecutionEnvOp (op : ExecutionEnv → UInt256) : Transformer :=
  EVM.executionEnvOp op

private def dispatchUnaryExecutionEnvOp (op : ExecutionEnv → UInt256 → UInt256) : Transformer :=
  EVM.unaryExecutionEnvOp op

private def dispatchMachineStateOp (op : MachineState → UInt256) : Transformer :=
  EVM.machineStateOp op

private def dispatchUnaryStateOp (op : State → UInt256 → State × UInt256) : Transformer :=
  EVM.unaryStateOp op

private def dispatchTernaryCopyOp
 (op : SharedState → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer
:=
  EVM.ternaryCopyOp op

private def dispatchQuaternaryCopyOp
 (op : SharedState → UInt256 → UInt256 → UInt256 → UInt256 → SharedState) :
  Transformer
:=
  EVM.quaternaryCopyOp op

private def dispatchBinaryMachineStateOp
 (op : MachineState → UInt256 → UInt256 → MachineState) :
  Transformer
:=
  EVM.binaryMachineStateOp op

private def dispatchTernaryMachineStateOp
 (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
  Transformer
:=
  EVM.ternaryMachineStateOp op

private def dispatchBinaryMachineStateOp'
 (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
  Transformer
:=
  EVM.binaryMachineStateOp' op

private def dispatchBinaryStateOp
 (op : State → UInt256 → UInt256 → State) :
  Transformer
:=
  EVM.binaryStateOp op

private def dispatchStateOp (op : State → UInt256) : Transformer := EVM.stateOp op

private def dispatchLog0 : Transformer := EVM.log0Op

private def dispatchLog1 : Transformer := EVM.log1Op

private def dispatchLog2 : Transformer := EVM.log2Op

private def dispatchLog3 : Transformer := EVM.log3Op

private def dispatchLog4 : Transformer := EVM.log4Op

private def L (n : ℕ) := n - n / 64

def dup (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

def step (op : Operation) (arg : Option (UInt256 × Nat) := .none) : Transformer := Id.run do
  let _ : Id Unit := -- For debug logging
    dbg_trace op.pretty; pure ()
  match op with
    -- TODO: Revisit STOP, this is likely not the best way to do it.
    | .STOP =>
      λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
    | .ADD =>
      dispatchBinary UInt256.add
    | .MUL =>
      dispatchBinary UInt256.mul
    | .SUB =>
      dispatchBinary UInt256.sub
    | .DIV =>
      dispatchBinary UInt256.div
    | .SDIV =>
      dispatchBinary UInt256.sdiv
    | .MOD =>
      dispatchBinary UInt256.mod
    | .SMOD =>
      dispatchBinary UInt256.smod
    | .ADDMOD =>
      dispatchTernary UInt256.addMod
    | .MULMOD =>
      dispatchTernary UInt256.mulMod
    | .EXP =>
      dispatchBinary UInt256.exp
    | .SIGNEXTEND =>
      dispatchBinary UInt256.signextend
    | .LT =>
      dispatchBinary UInt256.lt
    | .GT =>
      dispatchBinary UInt256.gt
    | .SLT =>
      dispatchBinary UInt256.slt
    | .SGT =>
      dispatchBinary UInt256.sgt
    | .EQ =>
      dispatchBinary UInt256.eq
    | .ISZERO =>
      dispatchUnary UInt256.isZero
    | .AND =>
      dispatchBinary UInt256.land
    | .OR =>
      dispatchBinary UInt256.lor
    | .XOR =>
      dispatchBinary UInt256.xor
    | .NOT =>
      dispatchUnary UInt256.lnot
    | .BYTE =>
      dispatchBinary UInt256.byteAt
    | .SHL =>
      dispatchBinary (flip UInt256.shiftLeft)
    | .SHR =>
      dispatchBinary (flip UInt256.shiftRight)
    | .SAR =>
      dispatchBinary UInt256.sar

    | .KECCAK256 =>
      dispatchBinaryMachineStateOp' MachineState.keccak256

    | .ADDRESS =>
      dispatchExecutionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | .BALANCE =>
      dispatchUnaryStateOp EvmYul.State.balance
    | .ORIGIN =>
      dispatchExecutionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | .CALLER =>
      dispatchExecutionEnvOp (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | .CALLVALUE =>
      dispatchExecutionEnvOp ExecutionEnv.weiValue
    | .CALLDATALOAD =>
      dispatchUnaryStateOp (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | .CALLDATASIZE =>
      dispatchExecutionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
    | .CALLDATACOPY =>
      dispatchTernaryCopyOp .calldatacopy
    | .CODESIZE =>
      dispatchExecutionEnvOp (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | .CODECOPY =>
      dispatchTernaryCopyOp .codeCopy
    | .GASPRICE =>
      dispatchExecutionEnvOp (.ofNat ∘ ExecutionEnv.gasPrice)
    | .EXTCODESIZE =>
      dispatchUnaryStateOp EvmYul.State.extCodeSize
    | .EXTCODECOPY =>
      dispatchQuaternaryCopyOp EvmYul.SharedState.extCodeCopy'
    | .RETURNDATASIZE =>
      dispatchMachineStateOp EvmYul.MachineState.returndatasize
    | .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error .StackUnderflow
    | .EXTCODEHASH => dispatchUnaryStateOp EvmYul.State.extCodeHash

    | .BLOCKHASH => dispatchUnaryStateOp (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | .COINBASE => dispatchStateOp (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | .TIMESTAMP =>
      dispatchStateOp EvmYul.State.timeStamp
    | .NUMBER => dispatchStateOp EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | .PREVRANDAO => dispatchExecutionEnvOp EvmYul.prevRandao
    | .GASLIMIT => dispatchStateOp EvmYul.State.gasLimit
    | .CHAINID => dispatchStateOp EvmYul.State.chainId
    | .SELFBALANCE => dispatchStateOp EvmYul.State.selfbalance
    | .BASEFEE => dispatchExecutionEnvOp EvmYul.basefee
    | .BLOBHASH => dispatchUnaryExecutionEnvOp blobhash
    | .BLOBBASEFEE => dispatchExecutionEnvOp EvmYul.ExecutionEnv.getBlobGasprice

    | .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow

    | .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ => Id.run do
          let (v, mState') := evmState.toMachineState.mload μ₀
          let evmState' := {evmState with toMachineState := mState'}
          .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow
    | .MSTORE =>
      dispatchBinaryMachineStateOp MachineState.mstore
    | .MSTORE8 => dispatchBinaryMachineStateOp MachineState.mstore8
    | .SLOAD =>
      dispatchUnaryStateOp EvmYul.State.sload
    | .SSTORE =>
      dispatchBinaryStateOp EvmYul.State.sstore
    | .TLOAD => dispatchUnaryStateOp EvmYul.State.tload
    | .TSTORE => dispatchBinaryStateOp EvmYul.State.tstore
    | .MSIZE => dispatchMachineStateOp MachineState.msize
    | .GAS =>
      dispatchMachineStateOp MachineState.gas
    | .MCOPY => dispatchTernaryMachineStateOp MachineState.mcopy

    | .LOG0 => dispatchLog0
    | .LOG1 => dispatchLog1
    | .LOG2 => dispatchLog2
    | .LOG3 => dispatchLog3
    | .LOG4 => dispatchLog4
    | .RETURN => dispatchBinaryMachineStateOp MachineState.evmReturn
    | .REVERT => dispatchBinaryMachineStateOp MachineState.evmRevert
    | .SELFDESTRUCT =>
      λ evmState ↦
        match evmState.stack.pop with
          | some ⟨ s , μ₁ ⟩ =>
            let Iₐ := evmState.executionEnv.codeOwner
            let r : AccountAddress := AccountAddress.ofUInt256 μ₁
            if evmState.createdAccounts.contains Iₐ then
              -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
              let A' : Substate :=
                { evmState.substate with
                    selfDestructSet :=
                      evmState.substate.selfDestructSet.insert Iₐ
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none =>
                    dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                          evmState.accountMap.insert r {σ_r with balance := ⟨0⟩}
                            |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
            else
              /- When SELFDESTRUCT is executed in a transaction that is not the
                same as the contract calling SELFDESTRUCT was created:
              -/
              let A' : Substate :=
                { evmState.substate with
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- Note that if the target is the same as the contract
                          -- calling SELFDESTRUCT there is no net change in balances.
                          -- Unlike the prior specification, Ether will not be burnt in this case.
                          evmState.accountMap
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow
    | .INVALID => dispatchInvalid
    | .Push .PUSH0 => λ evmState =>
        .ok <|
          evmState.replaceStackAndIncrPC (evmState.stack.push ⟨0⟩)
    | .Push _ => λ evmState => do
        let some (arg, argWidth) := arg | .error .StackUnderflow
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
    | .JUMP => λ evmState => do
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            let newPc := μ₀
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .JUMPI => λ evmState => do
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            let newPc := if μ₁ != ⟨0⟩ then μ₀ else evmState.pc + ⟨1⟩
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .PC => λ evmState =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
    | .JUMPDEST => λ evmState => do
        .ok <| evmState.incrPC
    | .DUP1 => dup 1
    | .DUP2 => dup 2
    | .DUP3 => dup 3
    | .DUP4 => dup 4
    | .DUP5 => dup 5
    | .DUP6 => dup 6
    | .DUP7 => dup 7
    | .DUP8 => dup 8
    | .DUP9 => dup 9
    | .DUP10 => dup 10
    | .DUP11 => dup 11
    | .DUP12 => dup 12
    | .DUP13 => dup 13
    | .DUP14 => dup 14
    | .DUP15 => dup 15
    | .DUP16 => dup 16
    | .SWAP1 => swap 1
    | .SWAP2 => swap 2
    | .SWAP3 => swap 3
    | .SWAP4 => swap 4
    | .SWAP5 => swap 5
    | .SWAP6 => swap 6
    | .SWAP7 => swap 7
    | .SWAP8 => swap 8
    | .SWAP9 => swap 9
    | .SWAP10 => swap 10
    | .SWAP11 => swap 11
    | .SWAP12 => swap 12
    | .SWAP13 => swap 13
    | .SWAP14 => swap 14
    | .SWAP15 => swap 15
    | .SWAP16 => swap 16
    | _ => λ _ ↦ default

end Semantics

end EvmYul
