import ToyExternalCall.EVMBridgeSpec

namespace ToyExternalCall

open EvmYul

namespace EVMBytecode

theorem parse_serialize_stop :
    EVM.parseInstr (EVM.serializeInstr (.STOP : Operation .EVM)) = some .STOP := by
  rfl

theorem parse_serialize_add :
    EVM.parseInstr (EVM.serializeInstr (.ADD : Operation .EVM)) = some .ADD := by
  rfl

theorem parse_serialize_calldataload :
    EVM.parseInstr (EVM.serializeInstr (.CALLDATALOAD : Operation .EVM)) =
      some .CALLDATALOAD := by
  rfl

theorem parse_serialize_mload :
    EVM.parseInstr (EVM.serializeInstr (.MLOAD : Operation .EVM)) = some .MLOAD := by
  rfl

theorem parse_serialize_mstore :
    EVM.parseInstr (EVM.serializeInstr (.MSTORE : Operation .EVM)) = some .MSTORE := by
  rfl

theorem parse_serialize_call :
    EVM.parseInstr (EVM.serializeInstr (.CALL : Operation .EVM)) = some .CALL := by
  rfl

theorem parse_serialize_push32 :
    EVM.parseInstr (EVM.serializeInstr (.PUSH32 : Operation .EVM)) = some .PUSH32 := by
  rfl

theorem decode_stop :
    EVM.decode (Bytecode.op .STOP) (UInt256.ofNat 0) = some (.STOP, none) := by
  rfl

theorem decode_add :
    EVM.decode (Bytecode.op .ADD) (UInt256.ofNat 0) = some (.ADD, none) := by
  rfl

theorem decode_calldataload :
    EVM.decode (Bytecode.op .CALLDATALOAD) (UInt256.ofNat 0) =
      some (.CALLDATALOAD, none) := by
  rfl

theorem decode_mload :
    EVM.decode (Bytecode.op .MLOAD) (UInt256.ofNat 0) = some (.MLOAD, none) := by
  rfl

theorem decode_mstore :
    EVM.decode (Bytecode.op .MSTORE) (UInt256.ofNat 0) = some (.MSTORE, none) := by
  rfl

theorem decode_call :
    EVM.decode (Bytecode.op .CALL) (UInt256.ofNat 0) = some (.CALL, none) := by
  rfl

end EVMBytecode

end ToyExternalCall
