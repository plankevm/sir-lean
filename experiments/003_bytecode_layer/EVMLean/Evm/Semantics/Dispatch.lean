import Evm.Instr
import Evm.Semantics.Decode
import Evm.Semantics.Frame
import Evm.Semantics.PrimOps
import Evm.Semantics.Smsf
import Evm.Semantics.System

namespace Evm

open GasConstants

def dispatch (op : Operation) (arg : Option (UInt256 × UInt8)) (fr : Frame)
    (exec : ExecutionState) : Step :=
  match op with
    | .System s => systemOp s fr exec

    | .ADD => binOp UInt256.add exec
    | .MUL => binOp UInt256.mul exec Glow
    | .SUB => binOp UInt256.sub exec
    | .DIV => binOp UInt256.div exec Glow
    | .SDIV => binOp UInt256.sdiv exec Glow
    | .MOD => binOp UInt256.mod exec Glow
    | .SMOD => binOp UInt256.smod exec Glow
    | .ADDMOD => ternOp UInt256.addMod exec Gmid
    | .MULMOD => ternOp UInt256.mulMod exec Gmid
    | .EXP => do
      let (stack, base, exponent) ← exec.stack.pop2
      let exec ← charge (expCost exponent) exec
      continueWith <| exec.replaceStackAndIncrPC (stack.push (UInt256.exp base exponent))
    | .SIGNEXTEND => binOp UInt256.signextend exec Glow
    | .LT => binOp UInt256.lt exec
    | .GT => binOp UInt256.gt exec
    | .SLT => binOp UInt256.slt exec
    | .SGT => binOp UInt256.sgt exec
    | .EQ => binOp UInt256.eq exec
    | .ISZERO => unOp UInt256.isZero exec
    | .AND => binOp UInt256.land exec
    | .OR => binOp UInt256.lor exec
    | .XOR => binOp UInt256.xor exec
    | .NOT => unOp UInt256.lnot exec
    | .BYTE => binOp UInt256.byteAt exec
    | .SHL => binOp (flip UInt256.shiftLeft) exec
    | .SHR => binOp (flip UInt256.shiftRight) exec
    | .SAR => binOp UInt256.sar exec

    | .KECCAK256 => do
      let (stack, offset, size) ← exec.stack.pop2
      let exec ← chargeMemExpansion exec offset size
      let exec ← charge (keccakCost size) exec
      let (v, machine') := exec.toMachineState.keccak256 offset size
      continueWith <| ExecutionState.replaceStackAndIncrPC { exec with toMachineState := machine' } (stack.push v)

    | .ADDRESS => pushOp (λ s ↦ .ofNat s.executionEnv.address.val) exec
    | .BALANCE => unStateOp Evm.State.balance (λ s a ↦ accessCost (AccountAddress.ofUInt256 a) s.substate) exec
    | .ORIGIN => pushOp (λ s ↦ .ofNat s.executionEnv.origin.val) exec
    | .CALLER => pushOp (λ s ↦ .ofNat s.executionEnv.caller.val) exec
    | .CALLVALUE => pushOp (λ s ↦ s.executionEnv.value) exec
    | .CALLDATALOAD => unStateOp (λ s v ↦ (s, Evm.State.calldataload s v)) (λ _ _ ↦ Gverylow) exec
    | .CALLDATASIZE => pushOp (λ s ↦ .ofNat s.executionEnv.calldata.size) exec
    | .CODESIZE => pushOp (λ s ↦ .ofNat s.executionEnv.code.size) exec
    | .GASPRICE => pushOp (λ s ↦ .ofNat s.executionEnv.gasPrice) exec
    | .EXTCODESIZE => unStateOp Evm.State.extCodeSize (λ s a ↦ accessCost (AccountAddress.ofUInt256 a) s.substate) exec
    | .EXTCODEHASH => unStateOp Evm.State.extCodeHash (λ s a ↦ accessCost (AccountAddress.ofUInt256 a) s.substate) exec
    | .RETURNDATASIZE => pushOp (λ s ↦ .ofNat s.returnData.size) exec

    | .CALLDATACOPY => do
      let (stack, mstart, dstart, size) ← exec.stack.pop3
      let exec ← chargeMemExpansion exec mstart size
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        (exec.calldatacopy mstart dstart size) stack
    | .CODECOPY => do
      let (stack, mstart, cstart, size) ← exec.stack.pop3
      let exec ← chargeMemExpansion exec mstart size
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        (exec.codeCopy mstart cstart size) stack
    | .EXTCODECOPY => do
      let (stack, addr, mstart, cstart, size) ← exec.stack.pop4
      let exec ← chargeMemExpansion exec mstart size
      let exec ← charge (accessCost (AccountAddress.ofUInt256 addr) exec.substate + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        (exec.extCodeCopy' addr mstart cstart size) stack
    | .RETURNDATACOPY => do
      let (stack, mstart, rstart, size) ← exec.stack.pop3
      if rstart.toNat + size.toNat > exec.returnData.size then throw .InvalidMemoryAccess
      let exec ← chargeMemExpansion exec mstart size
      let exec ← charge (Gverylow + copyCost size) exec
      continueWith <| ExecutionState.replaceStackAndIncrPC
        { exec with toMachineState := exec.toMachineState.returndatacopy mstart rstart size } stack

    | .BLOCKHASH => unStateOp (λ s v ↦ (s, Evm.State.blockHash s v)) (λ _ _ ↦ Gblockhash) exec
    | .COINBASE => pushOp (λ s ↦ .ofNat (Evm.State.coinBase s.toState).val) exec
    | .TIMESTAMP => pushOp (λ s ↦ Evm.State.timeStamp s.toState) exec
    | .NUMBER => pushOp (λ s ↦ Evm.State.number s.toState) exec
    | .PREVRANDAO => pushOp (λ s ↦ Evm.prevRandao s.executionEnv) exec
    | .GASLIMIT => pushOp (λ s ↦ Evm.State.gasLimit s.toState) exec
    | .CHAINID => pushOp (λ s ↦ Evm.State.chainId s.toState) exec
    | .SELFBALANCE => pushOp (λ s ↦ Evm.State.selfbalance s.toState) exec Glow
    | .BASEFEE => pushOp (λ s ↦ Evm.basefee s.executionEnv) exec
    | .BLOBHASH => do
      let (stack, i) ← exec.stack.pop
      let exec ← charge HASH_OPCODE_GAS exec
      continueWith <| exec.replaceStackAndIncrPC (stack.push (blobhash exec.executionEnv i))
    | .BLOBBASEFEE => pushOp (λ s ↦ s.executionEnv.getBlobGasprice) exec
    | .Smsf s => smsfOp s fr exec
    | .LOG0 => do
      let (stack, offset, size) ← exec.stack.pop2
      logArm exec stack offset size #[]
    | .LOG1 => do
      let (stack, offset, size, t₁) ← exec.stack.pop3
      logArm exec stack offset size #[t₁]
    | .LOG2 => do
      let (stack, offset, size, t₁, t₂) ← exec.stack.pop4
      logArm exec stack offset size #[t₁, t₂]
    | .LOG3 => do
      let (stack, offset, size, t₁, t₂, t₃) ← exec.stack.pop5
      logArm exec stack offset size #[t₁, t₂, t₃]
    | .LOG4 => do
      let (stack, offset, size, t₁, t₂, t₃, t₄) ← exec.stack.pop6
      logArm exec stack offset size #[t₁, t₂, t₃, t₄]
    | .Push .PUSH0 => pushOp (fun _ => 0) exec
    | .Push _ => do
      let exec ← charge Gverylow exec
      let some (argVal, argWidth) := arg | throw .StackUnderflow
      continueWith <| exec.replaceStackAndIncrPC (exec.stack.push argVal) (pcΔ := argWidth + 1)
    | .Dup d => dup (dupIndex d) exec
    | .Swap s => swap (swapIndex s) exec

def stepFrame (fr : Frame) : Signal :=
  let exec := fr.exec
  let (op, arg) := decode exec.executionEnv.code exec.pc |>.getD (.STOP, .none)
  if op = .INVALID then
    .halted (.exception .InvalidInstruction)
  else
    let δ := stackPopCount op
    let α := stackPushCount op
    if exec.stack.size - δ + α > 1024 then
      .halted (.exception .StackOverflow)
    else
      match dispatch op arg fr exec with
        | .ok signal => signal
        | .error e => .halted (.exception e)

end Evm
