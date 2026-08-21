import Evm.UInt256
import Evm.Wheels
import Evm.Maps.AccountMap

namespace Sir

abbrev Word := Evm.UInt256
abbrev Address := Evm.AccountAddress

structure VarId where
  id : Nat
deriving DecidableEq, Repr

structure BlockId where
  id : Nat
deriving DecidableEq, Repr

structure FunctionId where
  id : Nat
deriving DecidableEq, Repr

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

inductive IRError where
  | undefinedVariable (var : VarId)
  | invalidBlock (block : BlockId)
  | invalidControl
  | blockArityMismatch (outputs inputs : Nat)
  deriving DecidableEq, Repr

structure CallResult where
  world' : World
  success : Bool
  output : ByteArray

structure CallInput where
  target : Address
  gas : Word
  world : World

structure CallRecord where
  input : CallInput
  result : CallResult

structure CallContext where
  self : Address
  caller : Address
  value : Word
  calldata : ByteArray
  isStatic : Bool

inductive FunctionOutcome where
  | returned (rs : Array Word)
  | halted
  deriving DecidableEq, Repr

inductive Event where
  | gas (value : Word)
  | call (call : CallRecord)

inductive Query where
  | gas
  | call (input : CallInput)

def Event.query : Event → Query
  | .gas _ => .gas
  | .call record => .call record.input

abbrev Trace := List Event

def Trace.QueryDivergence (first second : Trace) : Prop :=
  ∃ pre firstEvent firstRest secondEvent secondRest,
    first = pre ++ firstEvent :: firstRest ∧
      second = pre ++ secondEvent :: secondRest ∧
      firstEvent ≠ secondEvent ∧ firstEvent.query = secondEvent.query

inductive ObservableOutcome where
  | gas
  | call (input : CallInput)
  | halt (world : World)

inductive FunctionObservableOutcome where
  | gas
  | call (input : CallInput)
  | halt (world : World)
  | returned (world : World) (values : Array Word)

def ObservableOutcome.functionOutcome : ObservableOutcome → FunctionObservableOutcome
  | .gas => .gas
  | .call input => .call input
  | .halt world => .halt world


end Sir
