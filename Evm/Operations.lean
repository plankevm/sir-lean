import Evm.UInt256
import Evm.Machine.MachineState

import Mathlib.Data.Finmap

namespace Evm

namespace Operation

section Operation

inductive ArithLogicOp where
  | protected ADD
  | protected MUL
  | protected SUB
  | protected DIV
  | protected SDIV
  | protected MOD
  | protected SMOD
  | protected ADDMOD
  | protected MULMOD
  | protected EXP
  | protected SIGNEXTEND
  | protected LT
  | protected GT
  | protected SLT
  | protected SGT
  | protected EQ
  | protected ISZERO
  | protected AND
  | protected OR
  | protected XOR
  | protected NOT
  | protected BYTE
  | protected SHL
  | protected SHR
  | protected SAR
  deriving DecidableEq, Repr

inductive EnvOp where
  | protected ADDRESS
  | protected BALANCE
  | protected ORIGIN
  | protected CALLER
  | protected CALLVALUE
  | protected CALLDATALOAD
  | protected CALLDATASIZE
  | protected CALLDATACOPY
  | protected GASPRICE
  | protected CODESIZE
  | protected CODECOPY
  | protected EXTCODESIZE
  | protected EXTCODECOPY
  | protected RETURNDATASIZE
  | protected RETURNDATACOPY
  | protected EXTCODEHASH
  deriving DecidableEq, Repr

inductive BlockOp where
  | protected BLOCKHASH
  | protected COINBASE
  | protected TIMESTAMP
  | protected NUMBER
  | protected PREVRANDAO
  | protected GASLIMIT
  | protected CHAINID
  | protected SELFBALANCE
  | protected BASEFEE
  | protected BLOBHASH
  | protected BLOBBASEFEE
  deriving DecidableEq, Repr

inductive SmsfOp where
  | protected POP
  | protected MLOAD
  | protected MSTORE
  | protected SLOAD
  | protected SSTORE
  | protected MSTORE8
  | protected JUMP
  | protected JUMPI
  | protected PC
  | protected MSIZE
  | protected GAS
  | protected JUMPDEST
  | protected TLOAD
  | protected TSTORE
  | protected MCOPY
  deriving DecidableEq, Repr

inductive PushOp where
  | protected PUSH0
  | protected PUSH1
  | protected PUSH2
  | protected PUSH3
  | protected PUSH4
  | protected PUSH5
  | protected PUSH6
  | protected PUSH7
  | protected PUSH8
  | protected PUSH9
  | protected PUSH10
  | protected PUSH11
  | protected PUSH12
  | protected PUSH13
  | protected PUSH14
  | protected PUSH15
  | protected PUSH16
  | protected PUSH17
  | protected PUSH18
  | protected PUSH19
  | protected PUSH20
  | protected PUSH21
  | protected PUSH22
  | protected PUSH23
  | protected PUSH24
  | protected PUSH25
  | protected PUSH26
  | protected PUSH27
  | protected PUSH28
  | protected PUSH29
  | protected PUSH30
  | protected PUSH31
  | protected PUSH32
  deriving DecidableEq, Repr

inductive DupOp where
  | protected DUP1
  | protected DUP2
  | protected DUP3
  | protected DUP4
  | protected DUP5
  | protected DUP6
  | protected DUP7
  | protected DUP8
  | protected DUP9
  | protected DUP10
  | protected DUP11
  | protected DUP12
  | protected DUP13
  | protected DUP14
  | protected DUP15
  | protected DUP16
  deriving DecidableEq, Repr

inductive SwapOp where
  | protected SWAP1
  | protected SWAP2
  | protected SWAP3
  | protected SWAP4
  | protected SWAP5
  | protected SWAP6
  | protected SWAP7
  | protected SWAP8
  | protected SWAP9
  | protected SWAP10
  | protected SWAP11
  | protected SWAP12
  | protected SWAP13
  | protected SWAP14
  | protected SWAP15
  | protected SWAP16
  deriving DecidableEq, Repr

inductive LogOp where
  | protected LOG0
  | protected LOG1
  | protected LOG2
  | protected LOG3
  | protected LOG4
  deriving DecidableEq, Repr

inductive SystemOp where
  | protected STOP
  | protected CREATE
  | protected CALL
  | protected CALLCODE
  | protected RETURN
  | protected DELEGATECALL
  | protected CREATE2
  | protected STATICCALL
  | protected REVERT
  | protected INVALID
  | protected SELFDESTRUCT
  deriving DecidableEq, Repr

end Operation

end Operation

open Operation

inductive Operation where
  | protected ArithLogic (op : ArithLogicOp)
  | protected KECCAK256
  | protected Env (op : EnvOp)
  | protected Block (op : BlockOp)
  | protected Smsf (op : SmsfOp)
  | protected Push (op : PushOp)
  | protected Dup (op : DupOp)
  | protected Swap (op : SwapOp)
  | protected Log (op : LogOp)
  | protected System (op : SystemOp)
  deriving DecidableEq, Repr

namespace Operation

@[match_pattern]
abbrev STOP       : Operation := .System .STOP
abbrev ADD        : Operation := .ArithLogic .ADD
abbrev MUL        : Operation := .ArithLogic .MUL
abbrev SUB        : Operation := .ArithLogic .SUB
abbrev DIV        : Operation := .ArithLogic .DIV
abbrev SDIV       : Operation := .ArithLogic .SDIV
abbrev MOD        : Operation := .ArithLogic .MOD
abbrev SMOD       : Operation := .ArithLogic .SMOD
abbrev ADDMOD     : Operation := .ArithLogic .ADDMOD
abbrev MULMOD     : Operation := .ArithLogic .MULMOD
abbrev EXP        : Operation := .ArithLogic .EXP
abbrev SIGNEXTEND : Operation := .ArithLogic .SIGNEXTEND

abbrev LT     : Operation := .ArithLogic .LT
abbrev GT     : Operation := .ArithLogic .GT
abbrev SLT    : Operation := .ArithLogic .SLT
abbrev SGT    : Operation := .ArithLogic .SGT
abbrev EQ     : Operation := .ArithLogic .EQ
abbrev ISZERO : Operation := .ArithLogic .ISZERO
abbrev AND    : Operation := .ArithLogic .AND
abbrev OR     : Operation := .ArithLogic .OR
abbrev XOR    : Operation := .ArithLogic .XOR
abbrev NOT    : Operation := .ArithLogic .NOT
abbrev BYTE   : Operation := .ArithLogic .BYTE
abbrev SHL    : Operation := .ArithLogic .SHL
abbrev SHR    : Operation := .ArithLogic .SHR
abbrev SAR    : Operation := .ArithLogic .SAR

abbrev ADDRESS        : Operation := .Env .ADDRESS
abbrev BALANCE        : Operation := .Env .BALANCE
abbrev ORIGIN         : Operation := .Env .ORIGIN
abbrev CALLER         : Operation := .Env .CALLER
abbrev CALLVALUE      : Operation := .Env .CALLVALUE
abbrev CALLDATALOAD   : Operation := .Env .CALLDATALOAD
abbrev CALLDATASIZE   : Operation := .Env .CALLDATASIZE
abbrev CALLDATACOPY   : Operation := .Env .CALLDATACOPY
abbrev CODESIZE       : Operation := .Env .CODESIZE
abbrev GASPRICE       : Operation := .Env .GASPRICE
abbrev CODECOPY       : Operation := .Env .CODECOPY
abbrev EXTCODECOPY    : Operation := .Env .EXTCODECOPY
abbrev EXTCODESIZE    : Operation := .Env .EXTCODESIZE
abbrev RETURNDATASIZE : Operation := .Env .RETURNDATASIZE
abbrev RETURNDATACOPY : Operation := .Env .RETURNDATACOPY
abbrev EXTCODEHASH    : Operation := .Env .EXTCODEHASH

abbrev BLOCKHASH   : Operation := .Block .BLOCKHASH
abbrev COINBASE    : Operation := .Block .COINBASE
abbrev TIMESTAMP   : Operation := .Block .TIMESTAMP
abbrev NUMBER      : Operation := .Block .NUMBER
abbrev PREVRANDAO  : Operation := .Block .PREVRANDAO
abbrev GASLIMIT    : Operation := .Block .GASLIMIT
abbrev CHAINID     : Operation := .Block .CHAINID
abbrev SELFBALANCE : Operation := .Block .SELFBALANCE
abbrev BASEFEE     : Operation := .Block .BASEFEE
abbrev BLOBHASH    : Operation := .Block .BLOBHASH
abbrev BLOBBASEFEE : Operation := .Block .BLOBBASEFEE

abbrev POP      : Operation := .Smsf .POP
abbrev MLOAD    : Operation := .Smsf .MLOAD
abbrev MSTORE   : Operation := .Smsf .MSTORE
abbrev SLOAD    : Operation := .Smsf .SLOAD
abbrev SSTORE   : Operation := .Smsf .SSTORE
abbrev MSTORE8  : Operation := .Smsf .MSTORE8
abbrev JUMP     : Operation := .Smsf .JUMP
abbrev JUMPI    : Operation := .Smsf .JUMPI
abbrev PC       : Operation := .Smsf .PC
abbrev MSIZE    : Operation := .Smsf .MSIZE
abbrev GAS      : Operation := .Smsf .GAS
abbrev JUMPDEST : Operation := .Smsf .JUMPDEST
abbrev TLOAD    : Operation := .Smsf .TLOAD
abbrev TSTORE   : Operation := .Smsf .TSTORE
abbrev MCOPY    : Operation := .Smsf .MCOPY

abbrev PUSH0  : Operation := .Push .PUSH0
abbrev PUSH1  : Operation := .Push .PUSH1
abbrev PUSH2  : Operation := .Push .PUSH2
abbrev PUSH3  : Operation := .Push .PUSH3
abbrev PUSH4  : Operation := .Push .PUSH4
abbrev PUSH5  : Operation := .Push .PUSH5
abbrev PUSH6  : Operation := .Push .PUSH6
abbrev PUSH7  : Operation := .Push .PUSH7
abbrev PUSH8  : Operation := .Push .PUSH8
abbrev PUSH9  : Operation := .Push .PUSH9
abbrev PUSH10 : Operation := .Push .PUSH10
abbrev PUSH11 : Operation := .Push .PUSH11
abbrev PUSH12 : Operation := .Push .PUSH12
abbrev PUSH13 : Operation := .Push .PUSH13
abbrev PUSH14 : Operation := .Push .PUSH14
abbrev PUSH15 : Operation := .Push .PUSH15
abbrev PUSH16 : Operation := .Push .PUSH16
abbrev PUSH17 : Operation := .Push .PUSH17
abbrev PUSH18 : Operation := .Push .PUSH18
abbrev PUSH19 : Operation := .Push .PUSH19
abbrev PUSH20 : Operation := .Push .PUSH20
abbrev PUSH21 : Operation := .Push .PUSH21
abbrev PUSH22 : Operation := .Push .PUSH22
abbrev PUSH23 : Operation := .Push .PUSH23
abbrev PUSH24 : Operation := .Push .PUSH24
abbrev PUSH25 : Operation := .Push .PUSH25
abbrev PUSH26 : Operation := .Push .PUSH26
abbrev PUSH27 : Operation := .Push .PUSH27
abbrev PUSH28 : Operation := .Push .PUSH28
abbrev PUSH29 : Operation := .Push .PUSH29
abbrev PUSH30 : Operation := .Push .PUSH30
abbrev PUSH31 : Operation := .Push .PUSH31
abbrev PUSH32 : Operation := .Push .PUSH32

abbrev DUP1  : Operation := .Dup .DUP1
abbrev DUP2  : Operation := .Dup .DUP2
abbrev DUP3  : Operation := .Dup .DUP3
abbrev DUP4  : Operation := .Dup .DUP4
abbrev DUP5  : Operation := .Dup .DUP5
abbrev DUP6  : Operation := .Dup .DUP6
abbrev DUP7  : Operation := .Dup .DUP7
abbrev DUP8  : Operation := .Dup .DUP8
abbrev DUP9  : Operation := .Dup .DUP9
abbrev DUP10 : Operation := .Dup .DUP10
abbrev DUP11 : Operation := .Dup .DUP11
abbrev DUP12 : Operation := .Dup .DUP12
abbrev DUP13 : Operation := .Dup .DUP13
abbrev DUP14 : Operation := .Dup .DUP14
abbrev DUP15 : Operation := .Dup .DUP15
abbrev DUP16 : Operation := .Dup .DUP16

abbrev SWAP1  : Operation := .Swap .SWAP1
abbrev SWAP2  : Operation := .Swap .SWAP2
abbrev SWAP3  : Operation := .Swap .SWAP3
abbrev SWAP4  : Operation := .Swap .SWAP4
abbrev SWAP5  : Operation := .Swap .SWAP5
abbrev SWAP6  : Operation := .Swap .SWAP6
abbrev SWAP7  : Operation := .Swap .SWAP7
abbrev SWAP8  : Operation := .Swap .SWAP8
abbrev SWAP9  : Operation := .Swap .SWAP9
abbrev SWAP10 : Operation := .Swap .SWAP10
abbrev SWAP11 : Operation := .Swap .SWAP11
abbrev SWAP12 : Operation := .Swap .SWAP12
abbrev SWAP13 : Operation := .Swap .SWAP13
abbrev SWAP14 : Operation := .Swap .SWAP14
abbrev SWAP15 : Operation := .Swap .SWAP15
abbrev SWAP16 : Operation := .Swap .SWAP16

abbrev LOG0 : Operation := .Log .LOG0
abbrev LOG1 : Operation := .Log .LOG1
abbrev LOG2 : Operation := .Log .LOG2
abbrev LOG3 : Operation := .Log .LOG3
abbrev LOG4 : Operation := .Log .LOG4

abbrev CREATE       : Operation := .System .CREATE
abbrev CALL         : Operation := .System .CALL
abbrev CALLCODE     : Operation := .System .CALLCODE
abbrev RETURN       : Operation := .System .RETURN
abbrev DELEGATECALL : Operation := .System .DELEGATECALL
abbrev CREATE2      : Operation := .System .CREATE2
abbrev STATICCALL   : Operation := .System .STATICCALL
abbrev REVERT       : Operation := .System .REVERT
abbrev INVALID      : Operation := .System .INVALID
abbrev SELFDESTRUCT : Operation := .System .SELFDESTRUCT

end Operation
