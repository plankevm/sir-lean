import Sir.Core.Types

namespace Sir

class WorldModel (World : Type) where
  sload : World → Address → Word → Word
  sstore : World → Address → Word → Word → World


class LawfulWorldModel (World : Type) [WorldModel World] : Prop where
  load_store_same :
    ∀ (w : World) (a : Address) (k value : Word),
      let w' := WorldModel.sstore w a k value
      WorldModel.sload w' a k = value

  load_store_otherKey :
    ∀ (w : World) (a : Address) (k k' value : Word),
      k' ≠ k →
        let w' := WorldModel.sstore w a k value
        WorldModel.sload w' a k' = WorldModel.sload w a k'

  load_store_otherAccount :
    ∀ (w₀ : World) (a a' : Address) (key value : Word)
      (otherKey : Word),
      a' ≠ a →
        let w' := WorldModel.sstore w₀ a key value
        WorldModel.sload w' a' otherKey = WorldModel.sload w₀ a' otherKey


end Sir
