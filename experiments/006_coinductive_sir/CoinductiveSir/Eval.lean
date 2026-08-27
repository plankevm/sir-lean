import CoinductiveSir.Data
import CoinductiveSir.CoFree
import CoinductiveSir.Memory
import Evm.Wheels
import Evm.Maps.AccountMap


inductive IRError where
  | undefinedVariable (var : VarId)
  | invalidFunction (function : FunctionId)
  | invalidBlock (block : BlockId)
  | blockArityMismatch (outputs inputs : Nat)
  deriving DecidableEq, Repr

inductive ProgramEffect : Type → Type where
  | call (target : U256) (gasLimit : U256) : ProgramEffect Bool
  | gas : ProgramEffect U256
  | mallocUninit (size : U256) : ProgramEffect U256
  | mallocZeroed (size : U256) : ProgramEffect U256
  | mstore32 (offset value : U256) : ProgramEffect Unit
  | mload32 (offset : U256) : ProgramEffect U256
  | sstore (slot value : U256) : ProgramEffect Unit
  | sload (slot : U256) : ProgramEffect U256
  | halt : ProgramEffect Empty
  | failure (error : IRError) : ProgramEffect Empty

abbrev ProgramM := CoFree ProgramEffect

def call (target : U256) (gasLimit : U256) : ProgramM Bool := CoFree.perform (.call target gasLimit)
def gas : ProgramM U256 := CoFree.perform .gas
def mallocUninit (size : U256) : ProgramM U256 := CoFree.perform (.mallocUninit size)
def mallocZeroed (size : U256) : ProgramM U256 := CoFree.perform (.mallocZeroed size)
def mstore32 (offset value : U256) : ProgramM Unit := CoFree.perform (.mstore32 offset value)
def mload32 (offset : U256) : ProgramM U256 := CoFree.perform (.mload32 offset)
def sstore (slot value : U256) : ProgramM Unit := CoFree.perform (.sstore slot value)
def sload (slot : U256) : ProgramM U256 := CoFree.perform (.sload slot)
def halt : ProgramM A := do nomatch ← CoFree.perform .halt
def fail (error : IRError) : ProgramM A := do nomatch ← CoFree.perform (.failure error)

structure Locals where
  values : VarId → Option U256

namespace Locals

def empty : Locals := ⟨fun _ => none⟩

def lookup (locals : Locals) (var : VarId) : Except IRError U256 :=
  match locals.values var with
  | none => .error (.undefinedVariable var)
  | some value => .ok value

def assign (locals : Locals) (var : VarId) (value : U256) : Locals :=
  ⟨fun candidate => if candidate = var then some value else locals.values candidate⟩

def bind (locals : Locals) (identifiers : Array VarId) (values : Array U256) : Except IRError Locals := do
  if identifiers.size != values.size then
    throw (.blockArityMismatch values.size identifiers.size)
  let mut result := locals
  for (identifier, value) in identifiers.zip values do
    result := result.assign identifier value
  return result

private def transfer (locals : Locals) (function : Func) (source : Block) (target : BlockId)
    : Except IRError (Block × Locals) := do
  let some targetBlock := function.blocks[target.id]? | throw (.invalidBlock target)
  let values ← source.outputs.mapM locals.lookup
  let locals ← locals.bind targetBlock.inputs values
  return (targetBlock, locals)

end Locals

def BinOp.eval : BinOp → U256 → U256 → U256
  | .add => .add
  | .lt => .lt

private instance : MonadLift (Except IRError) (CoFree ProgramEffect) where
  monadLift
  | .ok value => pure value
  | .error error => fail error

private def evalExpr (locals : Locals) : Expr → ProgramM U256
  | .constant value => do return value
  | .var identifier => do return (← locals.lookup identifier)
  | .binaryOp op lhs rhs => do
      let lhs ← locals.lookup lhs
      let rhs ← locals.lookup rhs
      return op.eval lhs rhs
  | .sload slot => do sload (← locals.lookup slot)
  | .gas => gas
  | .call args => do
      let target ← locals.lookup args.callee
      let gasLimit ← locals.lookup args.gas
      return .fromBool (← call target gasLimit)
  | .malloc size => do mallocZeroed (← locals.lookup size)
  | .mallocUninit size => do mallocUninit (← locals.lookup size)
  | .mload32 offset => do mload32 (← locals.lookup  offset)


def eval (program : Program) : Func × Array U256 → ProgramM (Array U256) :=
  CoFree.fix fun eval (function, arguments) => do
    let locals ← Locals.bind .empty function.entry.inputs arguments
    CoFree.iter (function.entry, locals)
      fun (block, locals) => do
        let mut locals := locals
        let mut block := block
        for statement in block.statements do
          match statement with
          | .assign result expression =>
              let value ← evalExpr locals expression
              locals := locals.assign result value
          | .sstore slot value =>
              let slot ← locals.lookup slot
              let value ← locals.lookup value
              sstore slot value
          | .mstore32 offsetVariable valueVariable =>
              let offset ← locals.lookup offsetVariable
              let value ← locals.lookup valueVariable
              mstore32 offset value
          | .icall callee inputs outputs =>
              let some function := program.function? callee | fail (.invalidFunction callee)
              let arguments ← (inputs.mapM locals.lookup : Except _ _)
              let result ← eval (function, arguments)
              locals ← locals.bind outputs result
        match block.terminator with
        | .halt => halt
        | .jump target =>
            return .repeat (← locals.transfer function block target)
        | .branch condition thenTarget elseTarget =>
            let value ← locals.lookup condition
            let target := if value = 0 then elseTarget else thenTarget
            return .repeat (← locals.transfer function block target)
        | .iret =>
            return .exit (← (block.outputs.mapM locals.lookup : Except _ _))
