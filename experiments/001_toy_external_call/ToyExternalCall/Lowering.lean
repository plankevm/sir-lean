import ToyExternalCall.IR
import EvmYul.EVM.Semantics

namespace ToyExternalCall

open EvmYul

abbrev EvmInstr := Operation .EVM × Option (Word × Nat)

def evmOp (op : Operation .EVM) : EvmInstr :=
  (op, none)

def push32 (value : Word) : EvmInstr :=
  (Operation.PUSH32, some (value, 32))

def execLoweredInstr (fuel gasCost : Nat) (instr : EvmInstr) :
    EVM.State → Except EVM.ExecutionException EVM.State :=
  if instr.1 = Operation.CALL then
    EVM.step fuel gasCost (some instr)
  else
    EvmYul.step (τ := .EVM) instr.1 instr.2

def runEvmTrace (fuel gasCost : Nat) : List EvmInstr → EVM.State →
    Except EVM.ExecutionException EVM.State
  | [], s => .ok s
  | [instr], s => execLoweredInstr fuel gasCost instr s
  | instr :: rest, s =>
      match execLoweredInstr fuel gasCost instr s with
      | .ok s' => runEvmTrace fuel gasCost rest s'
      | .error error => .error error

def lowerInputLoad (offset : Word) : List EvmInstr :=
  [ push32 offset
  , evmOp Operation.CALLDATALOAD
  ]

def lowerAddConst (constant : Word) : List EvmInstr :=
  [ push32 constant
  , evmOp Operation.ADD
  ]

def lowerCallEvaluated (req : CallRequest) : List EvmInstr :=
  [ push32 req.outSize
  , push32 req.outOffset
  , push32 req.inSize
  , push32 req.inOffset
  , push32 req.value
  , evmOp Operation.DUP6
  , push32 req.gas
  , evmOp Operation.CALL
  ]

def lowerCanonicalTrace (args : CallArgs) (constant : Word) (s : ToyState) : List EvmInstr :=
  lowerInputLoad (UInt256.ofNat 0)
    ++ lowerAddConst constant
    ++ lowerCallEvaluated ((s.writeLocal 1 (constant + s.callDataLoad (UInt256.ofNat 0))).evalCallRequest
      { args with target := .local 1 })

def callStack (req : CallRequest) : List Word :=
  [ req.gas
  , req.targetWord
  , req.value
  , req.inOffset
  , req.inSize
  , req.outOffset
  , req.outSize
  ]

def evmStepCallOracle (fuel gasCost : Nat) : CallOracle :=
  fun s req =>
    match execLoweredInstr fuel gasCost (evmOp Operation.CALL) { s.evm with stack := callStack req } with
    | .ok evm' =>
        match evm'.stack.head? with
        | some flag =>
            .ok { successFlag := flag, returnData := evm'.returnData, evm := evm' }
        | none => .error .StackUnderflow
    | .error error => .error error

def stackTop (result : Except EVM.ExecutionException EVM.State) : Option Word :=
  match result with
  | .ok s => s.stack.head?
  | .error _ => none

def stackSecond (result : Except EVM.ExecutionException EVM.State) : Option Word :=
  match result with
  | .ok s => s.stack.tail.head?
  | .error _ => none

def machineObsRel (toy : ToyState) (evm : EVM.State) : Prop :=
  toy.evm.toState = evm.toState ∧
  toy.evm.toMachineState = evm.toMachineState

@[simp]
theorem evm_push32_sem (s : EVM.State) (value : Word) :
    EvmYul.step Operation.PUSH32 (some (value, 32)) s =
      .ok (s.replaceStackAndIncrPC (s.stack.push value) (pcΔ := 33)) := by
  rfl

@[simp]
theorem evm_calldataload_sem (s : EVM.State) (offset : Word) (rest : List Word) :
    (EvmYul.step (τ := .EVM) Operation.CALLDATALOAD none) { s with stack := offset :: rest } =
      .ok ({ s with toState := s.toState }.replaceStackAndIncrPC
        (Stack.push rest (EvmYul.State.calldataload s.toState offset))) := by
  rfl

@[simp]
theorem evm_add_sem (s : EVM.State) (x y : Word) (rest : List Word) :
    (EvmYul.step (τ := .EVM) Operation.ADD none) { s with stack := x :: y :: rest } =
      .ok (s.replaceStackAndIncrPC (Stack.push rest (x + y))) := by
  rfl

@[simp]
theorem evm_calldataload_ctor_top
    (shared : SharedState .EVM) (pc : Word) (execLength : Nat) (offset : Word) (rest : List Word) :
    stackTop ((EvmYul.step (τ := .EVM) Operation.CALLDATALOAD none)
      { toSharedState := shared, pc := pc, stack := offset :: rest, execLength := execLength }) =
      some (EvmYul.State.calldataload shared.toState offset) := by
  rfl

@[simp]
theorem evm_add_ctor_top
    (shared : SharedState .EVM) (pc : Word) (execLength : Nat) (x y : Word) (rest : List Word) :
    stackTop ((EvmYul.step (τ := .EVM) Operation.ADD none)
      { toSharedState := shared, pc := pc, stack := x :: y :: rest, execLength := execLength }) =
      some (x + y) := by
  rfl

theorem lower_inputLoad_top (s : ToyState) (offset : Word) :
    stackTop (runEvmTrace 10 0 (lowerInputLoad offset) { s.evm with stack := [] }) =
      some (s.callDataLoad offset) := by
  simp only [stackTop, runEvmTrace, execLoweredInstr, lowerInputLoad, push32, evmOp,
    Operation.PUSH32, Operation.CALLDATALOAD, Operation.CALL, reduceCtorEq, ↓reduceIte,
    evm_push32_sem]
  simp only [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, Stack.push]
  change stackTop ((EvmYul.step (τ := .EVM) Operation.CALLDATALOAD none)
    { toSharedState := s.evm.toSharedState
      pc := s.evm.pc + UInt256.ofNat 33
      stack := [offset]
      execLength := s.evm.execLength }) = some (s.callDataLoad offset)
  rw [evm_calldataload_ctor_top]
  simp [ToyState.callDataLoad]

theorem lower_addConst_top (s : ToyState) (src constant : Word) :
    stackTop (runEvmTrace 10 0 (lowerAddConst constant) { s.evm with stack := [src] }) =
      some (constant + src) := by
  simp only [stackTop, runEvmTrace, execLoweredInstr, lowerAddConst, push32, evmOp,
    Operation.PUSH32, Operation.ADD, Operation.CALL, reduceCtorEq, ↓reduceIte, evm_push32_sem]
  simp only [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, Stack.push]
  change stackTop ((EvmYul.step (τ := .EVM) Operation.ADD none)
    { toSharedState := s.evm.toSharedState
      pc := s.evm.pc + UInt256.ofNat 33
      stack := [constant, src]
      execLength := s.evm.execLength }) = some (constant + src)
  rw [evm_add_ctor_top]

def toyStepLocal (result : StepResult) (dst : Local) : Option Word :=
  match result with
  | .ok s => some (s.readLocal dst)
  | .exceptional _ _ => none

theorem toy_inputLoad_preserved_by_lowering (s : ToyState) (dst : Local) (offset : Word) :
    toyStepLocal (evalInstr (evmStepCallOracle 10 0) s (.inputLoad dst (.const offset))) dst =
      stackTop (runEvmTrace 10 0 (lowerInputLoad offset) { s.evm with stack := [] }) := by
  rw [lower_inputLoad_top]
  simp [toyStepLocal, evalInstr, ToyState.readLocal, ToyState.writeLocal, ToyState.callDataLoad,
    ToyState.evalOperand]

theorem toy_addConst_preserved_by_lowering (s : ToyState) (dst srcLocal : Local) (constant : Word) :
    toyStepLocal (evalInstr (evmStepCallOracle 10 0) s (.addConst dst srcLocal constant)) dst =
      stackTop (runEvmTrace 10 0 (lowerAddConst constant) { s.evm with stack := [s.readLocal srcLocal] }) := by
  rw [lower_addConst_top]
  simp [toyStepLocal, evalInstr, ToyState.readLocal, ToyState.writeLocal]

theorem toy_call_preserved_by_evm_step_oracle
    (s : ToyState) (dst : Local) (args : CallArgs) (fuel gasCost : Nat) :
    toyStepLocal (evalInstr (evmStepCallOracle fuel gasCost) s (.call dst args)) dst =
      stackTop (execLoweredInstr fuel gasCost (evmOp Operation.CALL)
        { s.evm with stack := callStack (s.evalCallRequest args) }) := by
  generalize h :
    execLoweredInstr fuel gasCost (evmOp Operation.CALL)
      { s.evm with stack := callStack (s.evalCallRequest args) } = result
  cases result with
  | error error =>
      simp [toyStepLocal, stackTop, evalInstr, evmStepCallOracle, h]
  | ok evm' =>
      cases htop : evm'.stack.head? with
      | none =>
          simp [toyStepLocal, stackTop, evalInstr, evmStepCallOracle, h, htop]
      | some flag =>
          simp [toyStepLocal, stackTop, evalInstr, evmStepCallOracle, h, htop,
            ToyState.readLocal, ToyState.writeLocal]

theorem toy_call_preserves_machine_obs_by_evm_step_oracle
    (s : ToyState) (dst : Local) (args : CallArgs) (fuel gasCost : Nat) :
    match evalInstr (evmStepCallOracle fuel gasCost) s (.call dst args),
        execLoweredInstr fuel gasCost (evmOp Operation.CALL)
          { s.evm with stack := callStack (s.evalCallRequest args) } with
    | .ok toy', .ok evm' => machineObsRel toy' evm'
    | _, _ => True := by
  generalize h :
    execLoweredInstr fuel gasCost (evmOp Operation.CALL)
      { s.evm with stack := callStack (s.evalCallRequest args) } = result
  cases result with
  | error error =>
      simp [evalInstr, evmStepCallOracle, h]
  | ok evm' =>
      cases htop : evm'.stack.head? with
      | none =>
          simp [evalInstr, evmStepCallOracle, h, htop]
      | some flag =>
          simp [evalInstr, evmStepCallOracle, h, htop, machineObsRel, ToyState.setEvm,
            ToyState.setReturnData, ToyState.writeLocal]

end ToyExternalCall
