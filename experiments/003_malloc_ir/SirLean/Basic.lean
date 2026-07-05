import Init.Data.UInt

namespace Sir

abbrev Word := UInt32

structure VarId where
  id : Nat
deriving DecidableEq, Repr

def VarId.ofNat (n : Nat) : VarId := ⟨n⟩
def VarId.toNat (v : VarId) : Nat := v.id

end Sir
