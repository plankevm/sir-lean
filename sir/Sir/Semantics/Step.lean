import Sir.Semantics.World
import Sir.Semantics.State
import Sir.Semantics.Interaction

namespace Sir

private def evalExpr {World : Type} [WorldModel World] (state : ResumePoint World) (expr : Expr) :
    Except IRError (LocalState × Word) := do
  match expr with
  | .constant value => return (state.localState, value)
  | .var var => return (state.localState, ← readVariable state.localState var)
  | .add lhs rhs =>
      let lhsValue ← state.localState lhs
      let rhsValue ← state.localState rhs
      return (state.localState, Evm.UInt256.add lhsValue rhsValue)
  | .lt lhs rhs =>
      let lhsValue ← readVariable state.localState lhs
      let rhsValue ← readVariable state.localState rhs
      return (state.localState, Evm.UInt256.lt lhsValue rhsValue)
  | .sload key =>
      let keyValue ← readVariable state.localState key
      return (state.localState,
        storageLoad state.world state.context.self keyValue)
  | .gas =>
      match state.localState.gas.next with
      | none => throw (.missingEffect .gas)
      | some (value, rest) =>
          return ({ state.localState with gas := rest }, value)

private def stepStatement {World : Type} [WorldModel World] (program : Program) (state : ResumePoint World)
    (statement : Stmt) : Except IRError (StepResult World) := do
  let nextPC ← program.nextPC state.pc
  match statement with
  | .assign result expr =>
      let (localState, value) ← evalExpr state expr
      let localState := { localState with locals := localState.locals.set result value }
      return .continue { state with localState, pc := nextPC }
  | .sstore key value =>
      let keyValue ← readVariable state.localState key
      let valueValue ← readVariable state.localState value
      let world := sstore state.world state.context.self keyValue valueValue
      return .continue { state with world, pc := nextPC }
  | .call call =>
      let callee ← readVariable state.localState call.callee
      let gas ← readVariable state.localState call.gas
      let request : CallRequest := { caller := state.context.self, callee, gas }
      let continuation : CallContinuation World := {
        resume := { state with pc := nextPC }
        resultTarget := call.result
      }
      return .needsCall request continuation
  | .create create =>
      let value ← readVariable state.localState create.value
      let initOffset ← readVariable state.localState create.initOffset
      let initSize ← readVariable state.localState create.initSize
      let salt ← match create.salt with
        | none => pure none
        | some var => some <$> readVariable state.localState var
      let request : CreateRequest := {
        creator := state.context.self
        value
        initOffset
        initSize
        salt
      }
      let continuation : CreateContinuation World := {
        resume := { state with pc := nextPC }
        resultTarget := create.result
      }
      return .needsCreate request continuation

private def stepTerminator {World : Type} [WorldModel World] (program : Program) (state : ResumePoint World)
    (terminator : Terminator) : Except IRError (StepResult World) := do
  match terminator with
  | .ret var => return .halted state (.returned (← readVariable state.localState var))
  | .stop => return .halted state .stopped
  | .jump target => return .continue { state with pc := ← program.blockEntryPC target }
  | .branch condition thenTarget elseTarget =>
      let value ← readVariable state.localState condition
      let target := if value = 0 then elseTarget else thenTarget
      return .continue { state with pc := ← program.blockEntryPC target }

instance {L R : Type} {m : Type → Type} [Monad m] : MonadLift (StateT L m) (StateT (L × R) m) where
  monadLift := fun transform_l (lhs, rhs) => do
    let (res, lhs') ← transform_l lhs
    return (res, lhs', rhs)

instance {L R : Type} {m : Type → Type} [Monad m] : MonadLift (StateT R m) (StateT (L × R) m) where
  monadLift := fun transform_r (lhs, rhs) => do
    let (res, rhs') ← transform_r rhs
    return (res, lhs, rhs')


/-- Execute one IR statement or terminator. Calls and creates suspend before their effects. -/
def step {World : Type} [WorldModel World] (program : Program) : StateT (LocalState × World) IRResult StepResult :=
  sorry


-- step => next, needsCall, needsCreate, halt, error

end Sir
