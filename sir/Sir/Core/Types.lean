import Evm.UInt256
import Evm.Wheels

namespace Sir

/-- The value type shared by SIR and the EVM bytecode layer. -/
abbrev Word := Evm.UInt256
abbrev Address := Evm.AccountAddress

structure VarId where
  id : Nat
deriving DecidableEq, Repr

structure BlockId where
  id : Nat
deriving DecidableEq, Repr

end Sir
