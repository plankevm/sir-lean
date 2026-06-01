# Verity to EVMYulLean Bridge

Verity is useful for Plank because it shows a Lean-native way to keep a high-level language semantics and still execute generated Yul in EVMYulLean. It does not simply identify Verity state with EVM state.

## Dependency and Fork Status

Verity does not vendor EVMYulLean inside the repository. It depends on a pinned fork through Lake:

```lean
require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"7785a9bba344db917e42b7f1033ee8346197bb40"
```

Source: [`forks/verity/lakefile.lean`](../forks/verity/lakefile.lean)

The local `forks/EVMYulLean` checkout is `NethermindEth/EVMYulLean` at commit `047f63070309f436b66c61e276ab3b6d1169265a`. Verity pins `lfglabs-dev/EVMYulLean` at `7785a9bba344db917e42b7f1033ee8346197bb40`.

Consequence: if Plank relies on EVMYulLean, pin the exact dependency and document the trust boundary. The issue is less "EVMYulLean is unusable" and more "the project must decide which fork/revision is the target semantics."

## Abstract Source State

Verity's source contracts run in an abstract state monad:

```lean
abbrev Contract (alpha : Type) := ContractState -> ContractResult alpha
```

Source: [`forks/verity/Verity/Core.lean`](../forks/verity/Verity/Core.lean)

Here `alpha` is the return type of the computation. `Contract Uint256` is a contract computation returning a `Uint256`; `Contract PUnit` is a stateful command returning no meaningful value.

Rollback is part of `Contract.run`:

```lean
def Contract.run {alpha : Type} (c : Contract alpha) (s : ContractState) :
    ContractResult alpha :=
  match c s with
  | ContractResult.success a s' => ContractResult.success a s'
  | ContractResult.revert msg _ => ContractResult.revert msg s
```

Source: [`forks/verity/Verity/Core.lean`](../forks/verity/Verity/Core.lean)

Consequence: Verity has a separate source semantics. It then proves compiler/IR agreement for supported fragments and separately bridges generated Yul/native execution back to observable results.

## Typed IR Details

The typed IR is a GADT indexed by a small type universe. `TVar` stores both an identifier and a static type:

```lean
inductive Ty where
  | uint256
  | address
  | bool
  | unit

structure TVar where
  id : Nat
  ty : Ty

inductive TExpr : Ty -> Type where
  | var (v : TVar) : TExpr v.ty
  | add (lhs rhs : TExpr .uint256) : TExpr .uint256
  | sender : TExpr .address
  | getStorage (slot : Nat) : TExpr .uint256
```

Source: [`forks/verity/Verity/Core/Free/TypedIR.lean`](../forks/verity/Verity/Core/Free/TypedIR.lean)

The important proof consequence is that ill-typed expressions are unrepresentable. You do not need a separate theorem saying `add` only receives `uint256`; the constructor enforces it.

## State Projection to EVMYulLean

Verity bridges flat proof-side Yul state into EVMYulLean account-map state. It projects only observable storage slots:

```lean
def toSharedState (state : YulState) (observableSlots : List Nat) :
    SharedState .Yul :=
  let addr := natToAddress state.thisAddress
  let storage := projectStorage state.storage observableSlots
  let account : Account .Yul :=
    { nonce := 0
      balance := 0
      storage := storage
      code := emptyCode
      tstorage := Batteries.RBMap.empty }
  ...
```

Source: [`forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanStateBridge.lean`](../forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanStateBridge.lean)

Consequence: this is an observable-projection bridge, not full state equality. That is a good early pattern for Plank: prove equality of storage slots, returndata, logs, return values, and relevant memory slices before trying to prove equality of an entire EVM world.

## Native Lowering

Verity lowers generated Yul builtins to EVMYulLean Yul primitive operations:

```lean
def lookupRuntimePrimOp : String -> Option (EvmYul.Operation .Yul)
  | "sload"        => some .SLOAD
  | "sstore"       => some .SSTORE
  | "tload"        => some .TLOAD
  | "tstore"       => some .TSTORE
  | "return"       => some .RETURN
  | "revert"       => some .REVERT
  | "call"         => some .CALL
  | "staticcall"   => some .STATICCALL
  | "delegatecall" => some .DELEGATECALL
  | "callcode"     => some .CALLCODE
  | _              => none
```

Source: [`forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeLowering.lean`](../forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeLowering.lean)

The runtime entry point validates the generated fragment, lowers to an EVMYulLean contract, calls EVMYulLean's dispatcher, then projects the result back to Verity's `YulResult`.

Consequence: Verity proves adapters and observable agreement around EVMYulLean. It does not erase the need for correctness obligations; it makes them local and staged.

## Correctness Obligations

Verity has a real source-to-IR theorem shape. The theorem relates supported source contract semantics to interpretation of generated IR:

```lean
theorem compile_preserves_semantics
    ...
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld))
```

Source: [`forks/verity/Compiler/Proofs/IRGeneration/Contract.lean`](../forks/verity/Compiler/Proofs/IRGeneration/Contract.lean)

The native EVMYulLean side is organized around an observable comparison predicate:

```lean
def nativeResultsMatchOn
    (observableSlots : List Nat)
    (ir : IRResult)
    (native : Except NativeLoweringError YulResult) : Prop :=
  match native with
  | .ok yul =>
      ir.success = yul.success /\
      ir.returnValue = yul.returnValue /\
      (∀ slot, slot ∈ observableSlots →
        ir.finalStorage (IRStorageSlot.ofNat slot) =
          yul.finalStorage (IRStorageSlot.ofNat slot)) /\
      ir.events = yul.events
  | .error _ => False
```

Source: [`forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean`](../forks/verity/Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeHarness.lean)

Consequence: Verity does have a separate abstract semantics, and it connects that semantics to lower layers by explicit result/state matching predicates. The lower layer is not "automatically equivalent" to the source semantics; the bridge theorem has to state which observables match and under what generated-fragment assumptions.

## Pattern to Steal for Plank

For Plank SIR:

1. Define a compact SIR state and executable SIR interpreter.
2. Define a lowering/scheduling relation from SIR locals/blocks to bytecode stack/memory/pc.
3. Build an initial EVMYulLean state for the emitted bytecode.
4. Project final EVMYulLean results back to SIR observables.
5. State theorem obligations over observable result relations first.
