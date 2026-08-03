import Sir.Generic.Machine

namespace Sir.Generic

open Sir

abbrev localsFrame : OpFrame where
  Env := Locals
  Src := Array VarId
  Dst := Array VarId
  fetch env src := src.mapM env.lookup
  store env dst values := Locals.bindValues env dst values

def decodeExpr (result : VarId) : Expr → Instr localsFrame
  | .constant value => ⟨Instr.Kind.primitive (.constant value), #[], #[result]⟩
  | .var var => ⟨Instr.Kind.primitive .copy, #[var], #[result]⟩
  | .add lhs rhs => ⟨Instr.Kind.primitive .add, #[lhs, rhs], #[result]⟩
  | .lt lhs rhs => ⟨Instr.Kind.primitive .lt, #[lhs, rhs], #[result]⟩
  | .sload key => ⟨Instr.Kind.primitive .sload, #[key], #[result]⟩

def decodeSirStmt : Stmt → Instr localsFrame
  | .assign result expr => decodeExpr result expr
  | .sstore key value => ⟨Instr.Kind.primitive .sstore, #[key, value], #[]⟩
  | .gas result => ⟨Instr.Kind.primitive .gas, #[], #[result]⟩
  | .call call => ⟨Instr.Kind.primitive .call, #[call.callee, call.gas], #[call.result]⟩
  | .mallocUninit result size =>
      ⟨Instr.Kind.primitive .mallocUninit, #[size], #[result]⟩
  | .mstore32 offset value => ⟨Instr.Kind.primitive .mstore32, #[offset, value], #[]⟩
  | .mload32 result offset => ⟨Instr.Kind.primitive .mload32, #[offset], #[result]⟩
  | .icall callee args dests => ⟨Instr.Kind.icall callee, args, dests⟩

def sirDecode (program : Program) (control : MachineControl) :
    Option (Instr localsFrame × MachineControl) :=
  (program.decodeStmt control).map fun (next, stmt) => (decodeSirStmt stmt, next)

def sirControl (program : Program) (env : Locals) (globals : Globals)
    (control : MachineControl) :
    Option (Trace × Locals × Globals × MachineControl) := do
  let terminator ← program.terminatorAt control
  let state : MachineState := { globals, locals := env, control }
  let .ok ((), state') := (eval_terminator program terminator).run state | none
  some ([], state'.locals, state'.globals, state'.control)

def sirResume (outcome : FunctionOutcome) (env : Locals) (dst : Array VarId)
    (next : MachineControl) : Option (Locals × MachineControl) :=
  match outcome with
  | .returned results =>
      match Locals.bindReturns env dst results with
      | .ok env' => some (env', next)
      | .error _ => none
  | .halted => some (.empty, .halted)

def sirEntry (program : Program) (function : FunctionId) (globals : Globals)
    (args : Array Word) : Option (GenState localsFrame) :=
  (program.callState? function globals args).map fun state =>
    { globals := state.globals, env := state.locals, control := state.control }

def sirDecoder (program : Program) : Decoder localsFrame where
  decode := sirDecode program
  control := sirControl program
  resume := sirResume
  entry := sirEntry program

end Sir.Generic
