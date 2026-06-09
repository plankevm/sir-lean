import EvmYul.EVM.Semantics
import ToyExternalCall.Bytecode

namespace ToyExternalCall

open EvmYul

namespace Correctness

structure LoweredState where
  toy : ToyState
  stack : List Word

inductive LoweredStepResult where
  | ok (state : LoweredState)
  | exceptional (state : LoweredState) (error : EVM.ExecutionException)

def LoweredState.push (state : LoweredState) (value : Word) : LoweredState :=
  { state with stack := value :: state.stack }

def LoweredState.storeLocal (state : LoweredState) (x : Local) (value : Word) : LoweredState :=
  { state with toy := state.toy.writeLocal x value }

def callRequestFromStack
    (state : ToyState)
    (gas targetWord value inOffset inSize outOffset outSize : Word) : CallRequest :=
  { gas := gas
    targetWord := targetWord
    target := AccountAddress.ofUInt256 targetWord
    value := value
    inOffset := inOffset
    inSize := inSize
    input := state.callInput inOffset inSize
    outOffset := outOffset
    outSize := outSize }

@[simp] theorem callRequestFromStack_evalOperands
    (state : ToyState)
    (args : CallArgs) :
    callRequestFromStack state
      (state.evalOperand args.gas)
      (state.evalOperand args.target)
      (state.evalOperand args.value)
      (state.evalOperand args.inOffset)
      (state.evalOperand args.inSize)
      (state.evalOperand args.outOffset)
      (state.evalOperand args.outSize) =
    state.evalCallRequest args := by
  simp [callRequestFromStack, ToyState.evalCallRequest, ToyState.callInput]

def stepLoweredOp (oracle : CallOracle) (state : LoweredState) :
    Bytecode.Op → LoweredStepResult
  | .push value =>
      .ok (state.push value)
  | .loadLocal x =>
      .ok (state.push (state.toy.readLocal x))
  | .storeLocal x =>
      match state.stack with
      | value :: stack =>
          .ok { state.storeLocal x value with stack := stack }
      | [] =>
          .exceptional state .StackUnderflow
  | .calldataload =>
      match state.stack with
      | offset :: stack =>
          .ok { toy := state.toy, stack := state.toy.callDataLoad offset :: stack }
      | [] =>
          .exceptional state .StackUnderflow
  | .add =>
      match state.stack with
      | lhs :: rhs :: stack =>
          .ok { toy := state.toy, stack := (lhs + rhs) :: stack }
      | _ =>
          .exceptional state .StackUnderflow
  | .call =>
      match state.stack with
      | gas :: targetWord :: value :: inOffset :: inSize :: outOffset :: outSize :: stack =>
          let request :=
            callRequestFromStack state.toy gas targetWord value inOffset inSize outOffset outSize
          match oracle state.toy request with
          | .ok result =>
              .ok
                { toy := (state.toy.setEvm result.evm).setReturnData result.returnData
                  stack := result.successFlag :: stack }
          | .error error =>
              .exceptional state error
      | _ =>
          .exceptional state .StackUnderflow
  | .stop =>
      .ok state

def runLoweredOps (oracle : CallOracle) (state : LoweredState) :
    List Bytecode.Op → RunResult
  | [] => .ok state.toy
  | .stop :: _ => .ok state.toy
  | op :: rest =>
      match stepLoweredOp oracle state op with
      | .ok state' => runLoweredOps oracle state' rest
      | .exceptional state' error => .exceptional state'.toy error

theorem compileOperandOps_correct_append
    (oracle : CallOracle)
    (state : ToyState)
    (operand : Operand)
    (stack : List Word)
    (ops : List Bytecode.Op) :
    runLoweredOps oracle { toy := state, stack := stack }
        (Bytecode.compileOperandOps operand ++ ops) =
      runLoweredOps oracle
        { toy := state, stack := state.evalOperand operand :: stack } ops := by
  cases operand <;>
    simp [Bytecode.compileOperandOps, runLoweredOps, stepLoweredOp, LoweredState.push,
      ToyState.evalOperand, ToyState.readLocal]

theorem compileInstrOps_correct_append
    (oracle : CallOracle)
    (state : ToyState)
    (instr : Instr)
    (ops : List Bytecode.Op) :
    runLoweredOps oracle { toy := state, stack := [] }
        (Bytecode.compileInstrOps instr ++ ops) =
      match evalInstr oracle state instr with
      | .ok state' => runLoweredOps oracle { toy := state', stack := [] } ops
      | .exceptional state' error => .exceptional state' error := by
  cases instr with
  | inputLoad dst offset =>
      simp [Bytecode.compileInstrOps]
      rw [compileOperandOps_correct_append]
      simp [runLoweredOps, stepLoweredOp, LoweredState.storeLocal, ToyState.writeLocal,
        ToyState.callDataLoad, evalInstr]
  | add dst lhs rhs =>
      simp [Bytecode.compileInstrOps, Bytecode.compileAddOps]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      simp [runLoweredOps, stepLoweredOp, LoweredState.storeLocal, ToyState.writeLocal,
        evalInstr]
  | call dst args =>
      simp [Bytecode.compileInstrOps, Bytecode.compileCallOps]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      rw [compileOperandOps_correct_append]
      simp [runLoweredOps, stepLoweredOp, callRequestFromStack_evalOperands]
      cases h : oracle state (state.evalCallRequest args) <;>
        simp [h, LoweredState.storeLocal, ToyState.writeLocal, ToyState.setEvm,
          ToyState.setReturnData, evalInstr]

theorem lowerOps_preserve_semantics
    (oracle : CallOracle)
    (program : Program)
    (initial : ToyState) :
    runLoweredOps oracle { toy := initial, stack := [] } (Bytecode.lowerOps program) = run oracle (program.length + 1) initial program := by
  induction program generalizing initial with
  | nil =>
      simp [Bytecode.lowerOps, runLoweredOps, run]
  | cons instr rest ih =>
      simp [Bytecode.lowerOps, run, List.length_cons]
      rw [compileInstrOps_correct_append]
      cases h : evalInstr oracle initial instr with
      | ok state' =>
          simp
          exact ih state'
      | exceptional state' error =>
          simp

end Correctness

end ToyExternalCall
