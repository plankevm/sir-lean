import CoinductiveSir.Data
import CoinductiveSir.CoFree
import Evm.Wheels
import Evm.Maps.AccountMap

abbrev Address := Evm.AccountAddress
abbrev World := Evm.AccountMap

namespace World

def loadStorage (world : World) (address : Address) (key : Word) : Word :=
  match world.find? address with
  | none => 0
  | some account => account.lookupStorage key

def storeStorage (world : World) (address : Address) (key value : Word) : World :=
  let account := (world.find? address).getD default
  world.insert address (account.updateStorage key value)

end World

structure CallInput where
  target : Address
  gas : Word
  world : World

structure CallResult where
  world' : World
  success : Bool
  output : ByteArray

inductive SirEffect : Type → Type where
  | call (input : CallInput) : SirEffect CallResult
  | gas : SirEffect Word
  | mallocUninit (size : Word) : SirEffect Word
  | mallocZeroed (size : Word) : SirEffect Word

-- helper definitions --
abbrev SirM := CoFree SirEffect
def call (input : CallInput) : SirM CallResult := CoFree.perform (.call input)
def gas : SirM Word := CoFree.perform .gas
def mallocUninit (size : Word) : SirM Word := CoFree.perform (.mallocUninit size)
def mallocZeroed (size : Word) : SirM Word := CoFree.perform (.mallocZeroed size)

inductive IRError where
  | undefinedVariable (var : VarId)
  | invalidBlock (block : BlockId)
  | blockArityMismatch (outputs inputs : Nat)
  deriving DecidableEq, Repr

def eval (p : Program) : Func → SirM (Except IRError Unit) := CoFree.fix (fun eval f => do
  let mut block := f.entry
  repeat do
    
)
