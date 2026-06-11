import ToyExternalCall.Correctness

/-!
# Executable validation: the exported theorems are non-vacuous

This file is an `#eval` sanity harness. It interprets both semantics —
the gasless IR specification (`Gasless.run`) and EVMYulLean's actual
bytecode interpreter (`EVM.X` on `load program s G`) — on concrete
programs and checks that they exhibit exactly the behaviour the exported
theorems (`lowering_correct` / `lowering_observables`) promise, and that
the behaviour the theorems deliberately do *not* promise (under-funded
runs) really does diverge.

It proves nothing; every claim is checked at runtime. Each `#eval` block
throws (failing the build) if a `CHECK` line is violated, so this file
doubles as a regression test. A summary of the concrete evaluated numbers
is at the bottom of the file.

Demonstrated:

1. **Call-free agreement** (`prog1 = [inputLoad 0 0, add 1 (local 0) (const 5)]`):
   the gasless run succeeds, and the lowered bytecode under a generous gas
   budget produces *exactly* the IR's observables and locals; an
   under-funded budget yields `OutOfGass` on the bytecode side while the
   gasless IR still succeeds (the refinement direction). The exact funding
   threshold `G₀` is located by evaluation.

2. **The CALL gas-divergence counterexample** (`progCall`): a callee that
   SSTOREs and halts. The gasless IR forwards exactly the requested gas
   (full tank ⇒ the 63/64 cap never binds) and the callee succeeds
   (flag 1, storage written). The bytecode on a *mid-sized* budget
   completes **successfully** (terminal `STOP`, no `OutOfGass`) but the
   63/64 cap starves the callee: flag 0, storage not written — a
   successful divergent execution, the documented counterexample to any
   "`¬OutOfGass → equal`" strengthening of the theorem. On a large budget
   the divergence disappears and the observables agree again.
-/

namespace ToyExternalCall

namespace Validation

open EvmYul

set_option maxHeartbeats 1000000

/-! ## Generic harness helpers -/

abbrev XResult := Except EVM.ExecutionException (EVM.ExecutionResult EVM.State)

/-- Run the lowered bytecode exactly as the theorems quantify it. -/
def runBytecode (p : Program) (s : Exec) (G : Nat) : XResult :=
  EVM.X s.fuel #[] (load p s G)

def resultTag : XResult → String
  | .ok (.success _ _) => "success"
  | .ok (.revert _ _)  => "revert"
  | .error e           => s!"error {repr e}"

def isOutOfGass : XResult → Bool
  | .error .OutOfGass => true
  | _                 => false

def finalState : XResult → Option EVM.State
  | .ok (.success st _) => some st
  | _                   => none

/-- Remaining gas of a successful bytecode run. -/
def resultGas (r : XResult) : Option Nat :=
  (finalState r).map (·.gasAvailable.toNat)

/-- The 32-byte word at `localSlot x` of a final state's memory: the value
of IR local `x` (locals are memory-backed). -/
def stateLocal (x : Local) (st : EVM.State) : Nat :=
  (st.toMachineState.lookupMemory (localSlot x)).toNat

def resultLocal (x : Local) (r : XResult) : Option Nat :=
  (finalState r).map (stateLocal x)

/-- Structural equality of observables (the `Observables` projections all
carry `BEq`). -/
def obsEq (a b : Observables) : Bool :=
  a.accounts == b.accounts && a.substate == b.substate && a.output == b.output

/-- Do the bytecode run's observables equal the given IR final state's? -/
def obsAgree (r : XResult) (s' : Exec) : Bool :=
  match observe r with
  | some o => obsEq o s'.observables
  | none   => false

/-- A runtime check: prints `CHECK <name>` on success, throws (failing the
build) otherwise. -/
def check (name : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"CHECK {name}"
  else throw <| IO.userError s!"CHECK FAILED: {name}"

/-! ## Concrete initial state

Built from the fork's `Inhabited` instances; the only fields that matter
are a nonempty calldata (so `inputLoad` reads something interesting) and
`perm := true` (non-static context). The gas counter is dead in the IR and
overridden by `load` on the bytecode side; fuel 50 covers every program
below (≤ 15 lowered opcodes plus the callee's nested interpreter stack).
-/

/-- 32-byte big-endian calldata whose word 0 is 37. -/
def calldata37 : ByteArray := (UInt256.ofNat 37).toByteArray

def env0 : ExecutionEnv .EVM :=
  { (default : ExecutionEnv .EVM) with
      calldata := calldata37
      perm := true }

def s0 : Exec :=
  { evm := { (default : EVM.State) with executionEnv := env0 }, fuel := 50 }

/-! ## Part 1: agreement on a call-free program -/

/-- `local0 := calldata[0]; local1 := local0 + 5` — expect 37 and 42. -/
def prog1 : Program :=
  [ .inputLoad 0 (.const (.ofNat 0)),
    .add 1 (.local 0) (.const (.ofNat 5)) ]

/- Gasless IR run of `prog1`, and the lowered bytecode on a generous
budget (10⁷ ≫ the ~2.2M memory-expansion cost of touching `localBase`).
Expected: gasless `.ok` with locals 37/42; bytecode `success` with the
*same* locals and *equal* observables (the conclusion of
`lowering_observables` at this `G`). -/
#eval show IO Unit from do
  let G := 10_000_000
  -- gasless specification side
  let s' ← match Gasless.run prog1 s0 with
    | .ok s' => pure s'
    | .error e => throw <| IO.userError s!"gasless prog1 failed: {repr e}"
  IO.println s!"[1] gasless prog1: ok; local0={stateLocal 0 s'.evm} \
local1={stateLocal 1 s'.evm} fuelLeft={s'.fuel}"
  check "gasless local0 = 37" (stateLocal 0 s'.evm == 37)
  check "gasless local1 = 42" (stateLocal 1 s'.evm == 42)
  -- bytecode side, generous budget
  let r := runBytecode prog1 s0 G
  IO.println s!"[1] bytecode prog1 @ G={G}: {resultTag r}; \
gasLeft={resultGas r} local0={resultLocal 0 r} local1={resultLocal 1 r}"
  check "bytecode success at G=10_000_000" (finalState r).isSome
  check "bytecode local0 = 37" (resultLocal 0 r == some 37)
  check "bytecode local1 = 42" (resultLocal 1 r == some 42)
  check "observables agree (accounts, substate, output)" (obsAgree r s')
  check "output is empty (terminal STOP)"
    (match observe r with | some o => o.output == ByteArray.empty | none => false)

/- The refinement direction: an under-funded bytecode run fails with
`OutOfGass` while the gasless IR (above) succeeds — exactly the case the
theorem promises nothing about. Also locate the exact funding threshold
`G₀` for `prog1` by evaluating one gas unit on either side of it.
Expected: G=1000 ⇒ `OutOfGass`; G=2_195_747 ⇒ `OutOfGass`;
G=2_195_748 ⇒ success with 0 gas left. -/
#eval show IO Unit from do
  let rTiny := runBytecode prog1 s0 1000
  IO.println s!"[1] bytecode prog1 @ G=1000: {resultTag rTiny}"
  check "underfunded run is OutOfGass, observe = none"
    (isOutOfGass rTiny && (observe rTiny).isNone)
  let rBelow := runBytecode prog1 s0 2_195_747
  let rExact := runBytecode prog1 s0 2_195_748
  IO.println s!"[1] bytecode prog1 @ G=2195747: {resultTag rBelow}"
  IO.println s!"[1] bytecode prog1 @ G=2195748: {resultTag rExact}; gasLeft={resultGas rExact}"
  check "G = 2_195_747 is one short (OutOfGass)" (isOutOfGass rBelow)
  check "G = 2_195_748 succeeds with 0 left" (resultGas rExact == some 0)
  -- cross-check: the metered IR semantics (the proof artifact) reproduces
  -- the bytecode's remaining gas on the nose (lowering_exact, evaluated)
  let mt := ToyExternalCall.run evmCallOracle prog1 (s0.withGas (.ofNat 10_000_000))
  let mtGas := match mt with | .ok s' => some s'.evm.gasAvailable.toNat | .error _ => none
  IO.println s!"[1] metered prog1 @ G=10000000: gasLeft={mtGas}"
  check "metered gas = bytecode gas" (mtGas == resultGas (runBytecode prog1 s0 10_000_000))

/-! ## Part 2: the CALL gas-divergence counterexample

Callee at `0xC0FFEE`: `PUSH32 1; PUSH32 0; SSTORE; STOP` — needs
3 + 3 + (2100 cold + 20000 sset) = 22_106 gas, and writes storage slot 0
(an *observable* effect, so success/starvation is visible in the account
map, not just in the flag local).

Caller program: `inputLoad 0 0` first (pre-pays the ~2.2M expansion of the
locals region, so the post-CALL flag store is cheap), then a `call` with
gas operand 200_000 — comfortably above the callee's need — value 0, empty
in/out regions, flag into local 0.
-/

def calleeAddr : AccountAddress := AccountAddress.ofNat 0xC0FFEE

def calleeCode : ByteArray :=
  ⟨⟨Bytecode.codeBytes [.push (.ofNat 1), .push (.ofNat 0)] ++
    [Bytecode.opcode .SSTORE, Bytecode.opcode .STOP]⟩⟩

def accountsC : AccountMap .EVM :=
  (Batteries.RBMap.empty : AccountMap .EVM).insert calleeAddr
    { (default : Account .EVM) with code := calleeCode }

def sC : Exec :=
  { evm := { (default : EVM.State) with executionEnv := env0, accountMap := accountsC }
    fuel := 50 }

def progCall : Program :=
  [ .inputLoad 0 (.const (.ofNat 0)),
    .call 0
      { gas       := .const (.ofNat 200_000)
        target    := .const (.ofNat 0xC0FFEE)
        value     := .const (.ofNat 0)
        inOffset  := .const (.ofNat 0)
        inSize    := .const (.ofNat 0)
        outOffset := .const (.ofNat 0)
        outSize   := .const (.ofNat 0) } ]

/-- Storage slot 0 of the callee in an account map (0 if absent). -/
def calleeSlot0 (m : AccountMap .EVM) : Nat :=
  match m.find? calleeAddr with
  | some acct => (acct.storage.findD (UInt256.ofNat 0) (UInt256.ofNat 0)).toNat
  | none => 0

def resultCalleeSlot0 (r : XResult) : Option Nat :=
  (finalState r).map (fun st => calleeSlot0 st.accountMap)

/- Gasless IR run of `progCall`: the call executes the callee's real
bytecode via `EVM.call` on a full tank, so the callee receives the full
200_000 it asked for. Expected: success flag 1 in local 0, callee storage
slot 0 written to 1. -/
#eval show IO Unit from do
  let s' ← match Gasless.run progCall sC with
    | .ok s' => pure s'
    | .error e => throw <| IO.userError s!"gasless progCall failed: {repr e}"
  IO.println s!"[2] gasless progCall: ok; flag(local0)={stateLocal 0 s'.evm} \
calleeStorage[0]={calleeSlot0 s'.evm.accountMap} fuelLeft={s'.fuel}"
  check "gasless call flag = 1" (stateLocal 0 s'.evm == 1)
  check "gasless callee storage[0] = 1" (calleeSlot0 s'.evm.accountMap == 1)

/- The bytecode side of `progCall` across budgets. The CALL opcode forwards
`min(requested, ⌊63/64 · (remaining − 2600)⌋)`; at the CALL the caller has
spent 2_195_620 (locals expansion + 7 operand pushes), so:

* G = 10_000_000: cap doesn't bind, callee gets its 200_000, succeeds —
  observables equal the gasless IR's (the theorem's `G ≥ G₀` regime).
* G = 2_215_000: remaining−2600 = 16_780, cap forwards 16_518 < 22_106:
  the callee dies of OutOfGass, the *caller does not* — CALL pushes flag 0
  and the run completes via STOP. A successful execution, no visible
  `OutOfGass`, with flag 0 ≠ 1 and storage unwritten: the counterexample
  showing `¬OutOfGass → equal` is false, hence the `∃ G₀` shape.
* G = 2_200_000 sits in the same divergence window (robustness);
* G = 2_220_676 is the *exact* lower edge of the agreement regime: the cap
  forwards exactly 22_106 and the callee finishes with 0 gas. -/
#eval show IO Unit from do
  -- gasless reference for observables comparison
  let s' ← match Gasless.run progCall sC with
    | .ok s' => pure s'
    | .error e => throw <| IO.userError s!"gasless progCall failed: {repr e}"
  -- survey the budgets
  for G in [2_200_000, 2_215_000, 2_220_676, 10_000_000] do
    let r := runBytecode progCall sC G
    IO.println s!"[2] bytecode progCall @ G={G}: {resultTag r}; \
flag={resultLocal 0 r} calleeStorage[0]={resultCalleeSlot0 r} \
gasLeft={resultGas r} obsAgree={obsAgree r s'}"
  -- the divergent-but-successful run
  let rDiv := runBytecode progCall sC 2_215_000
  check "divergent run completes successfully (no OutOfGass)" (finalState rDiv).isSome
  check "divergent run: flag = 0 (callee starved by 63/64 cap)"
    (resultLocal 0 rDiv == some 0)
  check "divergent run: callee storage[0] = 0 (effects reverted)"
    (resultCalleeSlot0 rDiv == some 0)
  check "divergent run: observables differ from gasless IR" (!obsAgree rDiv s')
  check "gasless IR still says flag 1: successful divergence demonstrated"
    (stateLocal 0 s'.evm == 1)
  -- the funded run agrees again
  let rBig := runBytecode progCall sC 10_000_000
  check "funded run: flag = 1" (resultLocal 0 rBig == some 1)
  check "funded run: callee storage[0] = 1" (resultCalleeSlot0 rBig == some 1)
  check "funded run: observables equal the gasless IR's" (obsAgree rBig s')
  -- metered cross-check: the proof-artifact semantics tracks EVM.X even in
  -- the divergent regime (lowering_exact holds at every gas level)
  let mt := ToyExternalCall.run evmCallOracle progCall (sC.withGas (.ofNat 2_215_000))
  let mtGas := match mt with | .ok st => some st.evm.gasAvailable.toNat | .error _ => none
  let mtFlag := match mt with | .ok st => some (stateLocal 0 st.evm) | .error _ => none
  IO.println s!"[2] metered progCall @ G=2215000: gasLeft={mtGas} flag={mtFlag}"
  check "metered gas/flag = bytecode gas/flag in the divergent regime"
    (mtGas == resultGas rDiv && mtFlag == resultLocal 0 rDiv)

/-!
## Summary of evaluated results (recorded from an actual build)

Part 1 — call-free program `prog1 = [inputLoad 0 0, add 1 (local 0) (const 5)]`,
calldata word 0 = 37, fuel 50:

* gasless IR: `.ok`, local0 = 37, local1 = 42, fuel left 39.
* bytecode @ G = 10_000_000: success, gasLeft = 7_804_252 (2_195_748
  consumed, dominated by the 2_195_587 memory expansion to `localBase`),
  local0 = 37, local1 = 42, observables (accounts/substate/output) equal
  the IR's, output empty.
* bytecode @ G = 1000: `error OutOfGass`, `observe = none` — the gasless
  IR still succeeds: refinement, not equivalence.
* exact threshold: G = 2_195_747 ⇒ OutOfGass; G = 2_195_748 ⇒ success with
  gasLeft = 0. So `G₀ = 2_195_748` for this program/state.
* metered IR @ G = 10_000_000: gasLeft = 7_804_252, on the nose equal to
  the bytecode (evaluated instance of `lowering_exact`).

Part 2 — `progCall` (callee `PUSH32 1; PUSH32 0; SSTORE; STOP` at
0xC0FFEE needs 22_106; caller asks CALL to forward 200_000):

* gasless IR: `.ok`, flag(local0) = 1, callee storage[0] = 1, fuel left 35.
* bytecode @ G = 2_200_000: success, flag = 0, storage[0] = 0,
  gasLeft = 21, obsAgree = false  (divergence window)
* bytecode @ G = 2_215_000: success, flag = 0, storage[0] = 0,
  gasLeft = 256, obsAgree = false (divergence window: cap forwards
  16_518 < 22_106; callee dies, caller completes)
* bytecode @ G = 2_220_676: success, flag = 1, storage[0] = 1,
  gasLeft = 344, obsAgree = true  (exact edge: cap forwards exactly the
  22_106 the callee needs — it halts with 0 gas; the caller keeps the
  1/64 holdback of 350 minus 6 for the flag store)
* bytecode @ G = 10_000_000: success, flag = 1, storage[0] = 1,
  gasLeft = 7_779_668, obsAgree = true (funded regime of the theorem)
* metered IR @ G = 2_215_000: gasLeft = 256, flag = 0 — tracks the
  bytecode exactly even on the divergent budget.

The divergent run @ 2_215_000 is the documented counterexample: a
*successful* bytecode execution (no `OutOfGass` anywhere in the result)
whose final state and observables differ from the gasless IR's — which is
why the lowering theorem is `∃ G₀, ∀ G ≥ G₀, …` and cannot be strengthened
to `∀ G, ¬OutOfGass → equal`.
-/

end Validation

end ToyExternalCall
