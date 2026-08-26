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

structure CallContext where
  self : Address

inductive SirEffect : Type → Type where
  | call (input : CallInput) : SirEffect CallResult
  | gas : SirEffect Word
  | mallocUninit (size : Word) : SirEffect Word
  | mallocZeroed (size : Word) : SirEffect Word
  | mstore32 (offset value : Word) : SirEffect Unit
  | mload32 (offset : Word) : SirEffect Word
  | halt (final : World) : SirEffect Empty
  | unreachable : SirEffect Empty

abbrev SirM := CoFree SirEffect

def call (input : CallInput) : SirM CallResult := CoFree.perform (.call input)
def gas : SirM Word := CoFree.perform .gas
def mallocUninit (size : Word) : SirM Word := CoFree.perform (.mallocUninit size)
def mallocZeroed (size : Word) : SirM Word := CoFree.perform (.mallocZeroed size)
def mstore32 (offset value : Word) : SirM Unit := CoFree.perform (.mstore32 offset value)
def mload32 (offset : Word) : SirM Word := CoFree.perform (.mload32 offset)

inductive IRError where
  | undefinedVariable (var : VarId)
  | invalidFunction (function : FunctionId)
  | invalidBlock (block : BlockId)
  | blockArityMismatch (outputs inputs : Nat)
  deriving DecidableEq, Repr

structure Locals where
  values : VarId → Option Word

namespace Locals

def empty : Locals := ⟨fun _ => none⟩

def lookup (locals : Locals) (var : VarId) : Except IRError Word :=
  match locals.values var with
  | none => .error (.undefinedVariable var)
  | some value => .ok value

def assign (locals : Locals) (var : VarId) (value : Word) : Locals :=
  ⟨fun candidate => if candidate = var then some value else locals.values candidate⟩

def bind (locals : Locals) (identifiers : Array VarId) (values : Array Word) : Except IRError Locals := do
  if identifiers.size != values.size then
    throw (.blockArityMismatch values.size identifiers.size)
  let mut result := locals
  for (identifier, value) in identifiers.zip values do
    result := result.assign identifier value
  return result

end Locals

structure FunctionInput where
  function : Func
  world : World
  arguments : Array Word

structure FunctionResult where
  world : World
  values : Array Word

private abbrev EvalOutput := Except IRError FunctionResult
private abbrev EvalEffects := Recur FunctionInput EvalOutput ⊕ₑ SirEffect
private abbrev EvalM := ExceptT IRError (CoFree EvalEffects)

private def request (effect : SirEffect X) : EvalM X :=
  ExceptT.lift (CoFree.perform (.inr effect))

private def evalExpr (context : CallContext) (world : World) (locals : Locals) :
    Expr → Except IRError Word
  | .constant value => .ok value
  | .var identifier => locals.lookup identifier
  | .add lhs rhs => do return .add (← locals.lookup lhs) (← locals.lookup rhs)
  | .lt lhs rhs => do return .lt (← locals.lookup lhs) (← locals.lookup rhs)
  | .sload key => do return world.loadStorage context.self (← locals.lookup key)

private def transfer (function : Func) (source : Block) (target : BlockId)
    (locals : Locals) : Except IRError (Block × Locals) := do
  let some targetBlock := function.blocks[target.id]? | throw (.invalidBlock target)
  let values ← source.outputs.mapM locals.lookup
  let locals ← locals.bind targetBlock.inputs values
  return (targetBlock, locals)

private instance : MonadLift (Except IRError) EvalM where
  monadLift := MonadExcept.ofExcept

def eval (program : Program) (context : CallContext) :
    FunctionInput → SirM (Except IRError FunctionResult) :=
  CoFree.fix fun eval input => (do
    let mut world := input.world
    let mut locals ← Locals.bind .empty input.function.entry.inputs input.arguments
    let mut block := input.function.entry
    repeat do
      for statement in block.statements do
        match statement with
        | .assign result expression =>
            let value ← evalExpr context world locals expression
            locals := locals.assign result value
        | .sstore keyVariable valueVariable =>
            let key ← locals.lookup keyVariable
            let value ← locals.lookup valueVariable
            world := world.storeStorage context.self key value
        | .gas result =>
            let value ← request .gas
            locals := locals.assign result value
        | .call callData =>
            let target ← locals.lookup callData.callee
            let gasLimit ← locals.lookup callData.gas
            let answer ← request (.call {
              target := .ofUInt256 target,
              gas := gasLimit,
              world
            })
            world := answer.world'
            locals := locals.assign callData.result (.fromBool answer.success)
        | .malloc result sizeVariable =>
            let size ← locals.lookup sizeVariable
            let offset ← request (.mallocZeroed size)
            locals := locals.assign result offset
        | .mallocUninit result sizeVariable =>
            let size ← locals.lookup sizeVariable
            let offset ← request (.mallocUninit size)
            locals := locals.assign result offset
        | .mstore32 offsetVariable valueVariable =>
            let offset ← locals.lookup offsetVariable
            let value ← locals.lookup valueVariable
            request (.mstore32 offset value)
        | .mload32 result offsetVariable =>
            let offset ← locals.lookup offsetVariable
            let value ← request (.mload32 offset)
            locals := locals.assign result value
        | .icall callee inputs outputs =>
            let some function := program.function? callee | throw (.invalidFunction callee)
            let arguments ← (inputs.mapM locals.lookup : Except _ _)
            let result ← ExceptT.mk (eval { function, world, arguments })
            world := result.world
            locals ← locals.bind outputs result.values
      match block.terminator with
      | .halt => nomatch ← request (.halt world)
      | .jump target =>
          (block, locals) ← transfer input.function block target locals
      | .branch condition thenTarget elseTarget =>
          let value ← locals.lookup condition
          let target := if value = 0 then elseTarget else thenTarget
          (block, locals) ← transfer input.function block target locals
      | .iret =>
          let values ← (block.outputs.mapM locals.lookup : Except _ _)
          return { world, values }
    nomatch ← request (.unreachable)
  : EvalM FunctionResult).run
