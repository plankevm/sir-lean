import Sir.Semantics.State

namespace Sir

/-- Deterministic, read-only expression evaluation. -/
def Expr.eval (ctx : CallContext) (state : MachineState) : Expr → Except IRError Word
  | Expr.constant value => .ok value
  | Expr.var id => state.locals.get id
  | Expr.add lhs rhs => do
      let lhsValue ← state.locals.get lhs
      let rhsValue ← state.locals.get rhs
      return Evm.UInt256.add lhsValue rhsValue
  | Expr.lt lhs rhs => do
      let lhsValue ← state.locals.get lhs
      let rhsValue ← state.locals.get rhs
      return Evm.UInt256.lt lhsValue rhsValue
  | Expr.sload key => do
      let keyValue ← state.locals.get key
      return state.world.loadStorage ctx.self keyValue

def eval_assign (ctx : CallContext) (s : MachineState) (result : VarId) (expr : Expr) : Except IRError MachineState :=
  do
    let value ← Expr.eval ctx s expr
    .ok { s with locals := s.locals.set result value }

def eval_sstore (ctx : CallContext) (s : MachineState) (key value : VarId) :
    Except IRError MachineState := do
  let keyValue ← s.locals.get key
  let valueValue ← s.locals.get value
  return { s with world := s.world.storeStorage ctx.self keyValue valueValue }

def eval_call (s : MachineState) (call : Call) (result : CallResult)
  : Except IRError (MachineState × CallRecord) := do
    let callee ← s.locals.get call.callee
    let gas ← s.locals.get call.gas
    let s' := { s with
      locals := s.locals.set call.result (Evm.UInt256.fromBool result.success)
      returnData := result.output
      world := result.world
    }
    .ok (s', { target := .ofUInt256 callee, gas := gas, result := result })
/-- Deterministically compute a terminator's next control state. Target validity is
checked only when a later small step looks up the resulting control state. -/
def Terminator.eval (state : MachineState) : Terminator → Except IRError MachineControl
  | .halt => .ok .halted
  | .jump target => .ok (.blockStart target)
  | .branch condition thenTarget elseTarget => do
      let value ← state.locals.get condition
      return .blockStart (if value = 0 then elseTarget else thenTarget)

end Sir
