import Sir.Machine.Spec.Memory

namespace Sir.Machine

open Sir

inductive Operation where
  | constant (value : Word)
  | copy
  | add
  | lt
  | sload
  | sstore
  | gas
  | call
  | malloc
  | mallocUninit
  | mstore32
  | mload32
deriving DecidableEq, Repr

namespace Operation

def inputCount : Operation → Nat
  | .constant _ | .gas => 0
  | .copy | .sload | .malloc | .mallocUninit | .mload32 => 1
  | .add | .lt | .sstore | .call | .mstore32 => 2

def outputCount : Operation → Nat
  | .sstore | .mstore32 => 0
  | _ => 1

def Oracle : Operation → Type
  | .gas => Word
  | .call => CallResult
  | .malloc => Allocation
  | .mallocUninit => Allocation
  | .mload32 => Vector UInt8 32
  | _ => Unit

def Admissible (policy : MemoryPolicy) :
    (operation : Operation) → Globals → Array Word → operation.Oracle → Prop
  | .malloc, globals, operands, allocation =>
      ∃ size, operands[0]? = some size ∧
        policy.Allows globals.memory size.toNat allocation ∧
        globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = size.toNat ∧
        allocation.bytes = ByteArray.mk (Array.replicate size.toNat 0)
  | .mallocUninit, globals, operands, allocation =>
      ∃ size, operands[0]? = some size ∧
        policy.Allows globals.memory size.toNat allocation ∧
        globals.memory.IsValidNewAlloc allocation ∧
        allocation.size = size.toNat
  | _, _, _, _ => True

inductive Outcome where
  | next (results : Array Word) (globals : Globals) (trace : Trace)
  | halted (globals : Globals) (trace : Trace)

def execute (ctx : CallContext) :
    (operation : Operation) → operation.Oracle → Globals → Array Word →
      Except IRError Outcome
  | .constant value, _, globals, _ => .ok (.next #[value] globals [])
  | .copy, _, globals, operands => do
      let some value := operands[0]? | throw (.blockArityMismatch operands.size 1)
      return .next #[value] globals []
  | .add, _, globals, operands => do
      let some lhs := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some rhs := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[Evm.UInt256.add lhs rhs] globals []
  | .lt, _, globals, operands => do
      let some lhs := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some rhs := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[Evm.UInt256.lt lhs rhs] globals []
  | .sload, _, globals, operands => do
      let some key := operands[0]? | throw (.blockArityMismatch operands.size 1)
      return .next #[globals.world.loadStorage ctx.self key] globals []
  | .sstore, _, globals, operands => do
      let some key := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some value := operands[1]? | throw (.blockArityMismatch operands.size 2)
      return .next #[]
        { globals with world := globals.world.storeStorage ctx.self key value } []
  | .gas, answer, globals, _ =>
      .ok (.next #[answer] globals [Sir.Event.gas answer])
  | .call, result, globals, operands => do
      let some callee := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some gasValue := operands[1]? | throw (.blockArityMismatch operands.size 2)
      let input : CallInput :=
        { target := .ofUInt256 callee, gas := gasValue, world := globals.world }
      let record : CallRecord := { input, result }
      return .next #[Evm.UInt256.fromBool result.success]
        { globals with returnData := result.output, world := result.world' }
          [Sir.Event.call record]
  | .malloc, allocation, globals, operands => do
      let some size := operands[0]? | throw (.blockArityMismatch operands.size 1)
      if allocation.size ≠ size.toNat then
        throw .invalidAlloc
      return .next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } []
  | .mallocUninit, allocation, globals, operands => do
      let some size := operands[0]? | throw (.blockArityMismatch operands.size 1)
      if allocation.size ≠ size.toNat then
        throw .invalidAlloc
      return .next #[allocation.offset]
        { globals with memory := globals.memory.push allocation } []
  | .mstore32, _, globals, operands => do
      let some offset := operands[0]? | throw (.blockArityMismatch operands.size 2)
      let some value := operands[1]? | throw (.blockArityMismatch operands.size 2)
      if globals.memory.InBounds offset.toNat 32 then
        return .next #[]
          { globals with memory := globals.memory.writeBytes offset value.toByteArray } []
      else
        throw .storeOutOfBounds
  | .mload32, assumed, globals, operands => do
      let some offset := operands[0]? | throw (.blockArityMismatch operands.size 1)
      let bytes := globals.memory.readBytes offset ⟨assumed.toArray⟩
      return .next #[.ofNat (Evm.fromByteArrayBigEndian bytes)] globals []

end Operation

end Sir.Machine
