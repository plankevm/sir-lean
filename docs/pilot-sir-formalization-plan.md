# Pilot SIR Formalization Plan

## Pilot Goal

Build the smallest Lean artifact that teaches us how Plank SIR-style semantics should work and how it can later connect to EVMYulLean bytecode execution.

The pilot toy IR has:

- no control flow;
- a small AST, not full Plank SIR CFG yet;
- input/calldata word load;
- add constant;
- external call.

The key reason to include external call early is that `CALL` forces the semantic design to expose the real EVM boundary: call context, world/account state, memory slices, returndata, success/failure, gas assumptions, and rollback. We do not want to build a semantics that works only for arithmetic and then discover later that calls need a different state model.

## Non-goals

Do not formalize full Plank source, HIR, MIR, or full SIR yet.

Do not define a fresh full EVM semantics. The long-term target remains EVMYulLean bytecode execution. See [Semantics choice for Plank](./semantics-choice.md).

Do not prove full arbitrary reentrant EVM call correctness in the first milestone. The first milestone should make the call boundary explicit and prove a constrained call case or a call-summary theorem.

Do not model gas perfectly at first. We should prove under an adequate-gas assumption and record where gas affects observable behavior.

## Proposed Toy IR

Use a typed-enough AST with 256-bit words and explicit call expressions.

```lean
abbrev Word := UInt256
abbrev Address := AccountAddress

inductive Expr where
  | inputLoad  : Word -> Expr
  | addConst   : Expr -> Word -> Expr

structure ExternalCall where
  gas     : Expr
  to      : Expr
  value   : Expr
  inOff   : Expr
  inSize  : Expr
  outOff  : Expr
  outSize : Expr

inductive Program where
  | call : ExternalCall -> Program
```

This is deliberately close to the EVM `CALL` stack arguments:

```text
CALL(gas, to, value, inOffset, inSize, outOffset, outSize)
```

Plank SIR has the corresponding literal EVM operation:

```rust
Call(AllocatedIns<7, 1>) "call"
```

Source: [`forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs`](../forks/plank-monorepo/plankc/sir/crates/data/src/operation/mod.rs)

For the first example, instantiate a program like:

```text
let x = inputLoad 0
let to = x + constant
call(gas = fixedGas, to = to, value = 0, inOff = 0, inSize = 0, outOff = 0, outSize = 0)
```

That gives us calldata, arithmetic, constant emission, and external call while avoiding memory-copy complexity in the first proof.

## Semantic State

The toy state should already have the pieces needed for external calls, even if most fields are simple in the first milestone.

```lean
structure ToyState where
  calldata   : ByteArray
  memory     : ByteArray
  returndata : ByteArray
  accounts   : AccountMap .EVM
  this       : AccountAddress
  caller     : AccountAddress
  origin     : AccountAddress
  callvalue  : UInt256
  depth      : Nat
  static     : Bool
  gas        : UInt256
  logs       : List Event
```

Design decision: this state is not full EVMYulLean state, but it is EVM-shaped enough to define a later relation to EVMYulLean `EVM.State`.

Open question: should `accounts` initially be exactly EVMYulLean's `AccountMap .EVM`, or should the toy semantics use a smaller account model and define a projection relation later?

Recommendation: use EVMYulLean's account/storage types immediately. This avoids an avoidable translation layer for calls and storage, while still keeping the toy interpreter separate from EVMYulLean.

## Result Type

Use a result type that distinguishes success, revert, exceptional halt, and meta-level timeout.

```lean
inductive ToyResult where
  | ok       : ToyState -> UInt256 -> ToyResult
  | revert   : ToyState -> ByteArray -> ToyResult
  | exHalt   : ToyState -> ToyError -> ToyResult
  | outOfFuel : ToyResult
```

Design decision: do not collapse revert and exceptional halt. EVMYulLean separates normal success/revert from exceptions, and SIR should preserve that distinction.

## Interpreter Shape

Use executable, fuel-bounded semantics.

```lean
evalExpr : Nat -> ToyState -> Expr -> Except ToyError UInt256
run      : Nat -> ToyState -> Program -> ToyResult
```

This follows the research recommendation: define a Plank-owned executable IR semantics, then prove relations to EVMYulLean. See [Jargon and semantic styles](./jargon.md).

Design decision: even without control flow, use fuel. It makes the toy interpreter structurally similar to later SIR and EVMYulLean execution and avoids redesign when calls execute nested code.

## External Call Semantics

This is the core pilot decision.

There are three possible levels:

1. **Oracle call semantics**
   The toy interpreter calls an abstract function:

   ```lean
   CallOracle : ToyState -> CallArgs -> CallResult
   ```

   This is fastest and cleanly exposes the call boundary, but it does not prove EVMYulLean `CALL` behavior yet.

2. **Constrained EVM call semantics**
   Prove correspondence for `CALL` under strong restrictions:

   - `value = 0`;
   - `inSize = 0`;
   - `outSize = 0`;
   - adequate gas;
   - depth `< 1024`;
   - non-static or value is zero;
   - callee has empty/STOP code, or callee behavior is summarized.

   This gives a real EVMYulLean bridge early without taking on arbitrary reentrancy.

3. **Full EVMYulLean call semantics**
   Let `CALL` run arbitrary callee bytecode via EVMYulLean's message-call semantics.

   This is the real target but too large for the first pilot.

Recommendation: implement level 1 and prove level 2 for one constrained case. This gives us the architecture and one concrete EVMYulLean theorem without blocking on full call semantics.

## Why Calls Are Hard

EVMYulLean's bytecode `CALL` pops seven stack values:

```lean
-- mu0 - gas
-- mu1 - to
-- mu2 - value
-- mu3 - inOffset
-- mu4 - inSize
-- mu5 - outOffset
-- mu6 - outSize
let (stack, mu0, mu1, mu2, mu3, mu4, mu5, mu6) <- evmState.stack.pop7
```

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

It then delegates to message-call semantics `Theta`, which updates balances, constructs a new execution environment, runs precompile or callee code, handles revert/success, and returns `(createdAccounts, accountMap, gas, substate, success, output)`.

Source: [`forks/EVMYulLean/EvmYul/EVM/Semantics.lean`](../forks/EVMYulLean/EvmYul/EVM/Semantics.lean)

Consequence: even a toy external call must decide how to handle:

- call success flag;
- balance transfer;
- account creation for value transfer;
- callee code execution;
- memory input/output slices;
- returndata update;
- gas forwarding and refund;
- call depth;
- static-call restrictions;
- revert rollback.

## Initial Bytecode Target

The toy program above should compile to bytecode shaped like:

```text
PUSH1 0
CALLDATALOAD
PUSHn constant
ADD
PUSH1 0       -- outSize
PUSH1 0       -- outOffset
PUSH1 0       -- inSize
PUSH1 0       -- inOffset
PUSH1 0       -- value
<to already on stack>
PUSHn gas
CALL
STOP
```

Open question: confirm stack order against Plank's stack scheduler and EVMYulLean `pop7` convention before proving anything. The source comments show `CALL` expects top-of-stack as gas first when popped by `pop7`, but bytecode emission must arrange stack exactly.

Design decision: start with hand-written bytecode for the toy theorem, not the full Plank backend. Once the semantics and theorem shape are right, connect the toy compiler to Plank's stack scheduling/release backend.

## Proof Obligations

### Expression Evaluation

Prove:

```text
evalExpr (inputLoad off) state = word_at_calldata off state.calldata
evalExpr (addConst e k) state = evalExpr e state + k mod 2^256
```

This should match EVM `CALLDATALOAD` and `ADD`.

### Toy Compiler Correctness

For the no-call prefix:

```text
compileExpr e = bytes
state_rel toy evm
evalExpr e toy = v
--------------------------------
run_evm_segment bytes evm = evm'
top evm'.stack = v
state_rel_except_stack toy evm'
```

### Call Boundary Correctness

For oracle semantics:

```text
call_oracle toy args = call_result
evm_call_summary evm args call_result
--------------------------------------
toy_result_rel (runToy toy (call args)) (runEvmCall evm args)
```

For constrained EVMYulLean semantics:

```text
value = 0
inSize = 0
outSize = 0
adequate_gas evm
callee_empty_or_stop accounts to
state_rel toy evm
--------------------------------
EVMYulLean CALL step returns success flag 1
and toy/EVM states remain related on observables
```

### Whole Toy Program

```text
compileToy p = bytecode
initial_rel toy_state evm_state
runToy fuel toy_state p = toy_result
----------------------------------------
exists evm_result,
  runEvm fuel' bytecode evm_state = evm_result
  and result_rel toy_result evm_result
```

For the pilot, this can be specialized to the one concrete toy program rather than generalized over all programs.

## Phased Plan

### Phase 0: Pin Definitions and Assumptions

Deliverable: a short Lean/design note with:

- exact toy syntax;
- exact state fields;
- exact result type;
- chosen call abstraction level;
- EVMYulLean revision targeted;
- assumptions for the constrained call theorem.

### Phase 1: Lean Toy Interpreter

Implement:

- `Expr`;
- `ExternalCall`;
- `Program`;
- `ToyState`;
- `ToyResult`;
- `evalExpr`;
- `run`.

External call initially uses an oracle parameter or typeclass.

### Phase 2: Hand Bytecode and EVMYulLean Harness

Implement a minimal EVMYulLean setup for hand-written bytecode:

- account map with current contract code;
- execution environment with calldata;
- enough gas;
- empty memory;
- caller/recipient addresses;
- depth zero;
- non-static mode.

Run or evaluate simple bytecode:

- `PUSH offset; CALLDATALOAD`;
- `PUSH offset; CALLDATALOAD; PUSH c; ADD`;
- call with zero input/output.

### Phase 3: Prefix Correctness

Prove or at least structure proofs for input load and add constant.

This validates:

- calldata word interpretation;
- word arithmetic convention;
- stack relation for expression compilation.

### Phase 4: External Call Boundary

First theorem: oracle-level call relation.

Second theorem: one constrained EVMYulLean call case:

- no value transfer;
- no input/output data;
- enough gas;
- callee STOP/empty code;
- result success flag matches toy call success;
- returndata/log/account observables match.

### Phase 5: Generalization Toward SIR

Replace toy AST nodes with a tiny SIR subset:

- `SetSmallConst`;
- `CallDataLoad`;
- `Add`;
- `Call`;
- `Stop` or `Return`.

Then connect the toy semantics to the Plank operation universe and eventually to the backend.

## Design Decisions We Need to Make

1. **Lean package location**
   Should this pilot live in this study repo, a new Lean package, or inside Plank's future formalization repo?

2. **Word type**
   Use EVMYulLean `UInt256` from day one, or define a small wrapper?

   Recommendation: use `UInt256`.

3. **Byte representation**
   Use Lean `ByteArray` like EVMYulLean, or lists of bytes?

   Recommendation: use `ByteArray` to reduce bridge friction.

4. **Account model**
   Use EVMYulLean `AccountMap .EVM`, or a toy map?

   Recommendation: use EVMYulLean account types now.

5. **Call semantics**
   Oracle first, constrained EVMYulLean theorem second, or direct full EVMYulLean call?

   Recommendation: oracle plus constrained theorem.

6. **Gas**
   Erase gas, pass gas through, or model enough gas?

   Recommendation: carry gas in state, prove under adequate-gas assumptions, do not prove exact gas costs first.

7. **Memory**
   Include memory from day one?

   Recommendation: yes, but first call case sets `inSize = outSize = 0`.

8. **Return data**
   Include returndata from day one?

   Recommendation: yes. Calls update returndata even when we avoid output copying.

9. **Control flow**
   No control flow in toy AST, but should bytecode end in `STOP` or `RETURN`?

   Recommendation: use `STOP` first for minimality, then add `RETURN` once memory output matters.

10. **Compiler target**
    Hand-written bytecode first or Plank release backend first?

    Recommendation: hand-written bytecode first; backend later.

11. **Theorem generality**
    Prove for all toy programs or one canonical toy program?

    Recommendation: prove expression lemmas generically, prove whole-program theorem for one canonical program first.

12. **External call target**
    Should the callee be empty code, `STOP`, a fixed successful contract, a precompile, or an oracle?

    Recommendation: start with empty/STOP code and zero value/input/output.

13. **Reentrancy**
    Do we model reentrancy now?

    Recommendation: no, but do not design it away. The call oracle/result relation should allow state changes by callee so reentrancy can be introduced later.

14. **State equality vs observables**
    Compare full state or observable projection?

    Recommendation: observable projection: success flag, account/storage changes, returndata, logs, selected memory slices, and halt mode.

## Questions for the Team

1. Is the pilot supposed to live in Lean immediately, or should we first write an executable reference interpreter in Rust/Lean pseudocode?

2. Should the toy IR be an independent teaching IR, or should it literally be a subset of Plank SIR operations from the start?

3. What is the intended external call example?
   Is it `call(to = calldata[0] + k)`, or should calldata supply gas/value/offsets too?

4. Do we care about value-transferring calls in the pilot?
   If yes, balance transfer and account creation enter immediately.

5. Should the first call theorem use an empty/STOP callee, a fixed callee bytecode, or an abstract oracle?

6. Should returndata be observable in the first pilot if `outSize = 0`?

7. Do we want to include memory input/output for `CALL` now, or intentionally set them to zero for milestone one?

8. Are we proving against EVMYulLean `.EVM` bytecode execution directly, or introducing an intermediate assembly/stack-machine semantics first?

9. How close should the toy compiler's bytecode be to Plank's actual stack scheduler output?

10. Is exact gas out of scope for the pilot, or do we need at least a rough gas monotonicity/adequate-gas theorem?

11. What should count as success for the pilot?
    A running Lean interpreter? A theorem about expression compilation? A theorem about constrained `CALL`? A whole-program theorem?

12. Who owns validating that EVMYulLean's `CALL` behavior is current enough for Plank's target fork rules?

## Proposed Success Criteria

The pilot is successful if we have:

1. a Lean toy IR and executable interpreter;
2. a hand-written bytecode target for the canonical toy program;
3. a state relation between toy state and EVMYulLean state;
4. generic lemmas for input load and add constant;
5. a call-boundary relation;
6. one constrained EVMYulLean `CALL` correspondence theorem or, if that proves too large, a precise list of the missing EVMYulLean lemmas needed;
7. a clear next step from toy IR to the actual SIR subset.

