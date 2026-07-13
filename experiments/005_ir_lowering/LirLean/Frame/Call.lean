import LirLean.Spec.IR
import Evm
import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Dispatch

/-!
# LirLean — the abstract call oracle (`docs/ir-design.md` §5)

The IR's external-CALL accounting is **call-agnostic**: the IR does **not** model
the internals of an external call. It defers the call's *effect* — the post-storage
world, the gas restored to the caller, and the 0/1 success word — to an abstract
`CallOracle`. The IR reasons for **all** oracles; lowering instantiates the oracle
to **exactly what the lowered bytecode's CALL does** (the exp003 black-box
`messageCall` / `CallReturns` resume, projected through exp003's observable
`resumeAfterCall`), so the IR's call effect is *reflexively equal* to the lowered
bytecode's ext-call effect.

This mirrors how vyper-hol models external calls (the call is a black box that
returns a `CallResult`) and matches the gas-oracle altitude precisely: an abstract
oracle (IR reasons for all instantiations) + an `evmCallOracle` instantiation
(defeq / by-construction the lowered call's projection) + a reflexivity headline.

## What the oracle captures (and the one thing it cannot)

`resumeAfterCall result pd` (`EVM/Evm/Semantics/Call.lean`) does three
things the IR cares about:

* sets `exec.accounts := result.accounts` — the **post-storage world**, read
  through the observable `find?/lookupStorage` lens;
* sets `gasAvailable := gasAfterReturn` — the **restored gas**
  (`machineWithOutput.gasAvailable + result.gasRemaining`);
* pushes the **0/1 success word** `x` onto the stack.

The oracle captures the first two as state observations and the third as a word.
The dynamic success word is consumed by the live call stream and bound directly to
the statement's result temporary. The reflexivity headline reflects all three
effects (post-storage, restored gas, and the success word's value).
-/

namespace Lir.Frame

open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## The abstract call oracle

The oracle's input is exactly the data exp003's `resumeAfterCall` reads — the
child's `CallResult` and the suspended `PendingCall` — so the EVM instantiation is
**by construction** the lowered call's projection (each field reduces by `rfl` to
the corresponding `resumeAfterCall` component). The IR is parametric over *all*
`CallOracle`s; lowering picks `evmCallOracle`. -/

/-- An abstract **call oracle**: the IR's view of an external call's *effect*,
projected from the data exp003's `resumeAfterCall` reads (the child's `CallResult`
and the suspended `PendingCall`). Three projections, matching the three things
`resumeAfterCall` does the IR cares about:

* `postStorage result pd addr key` — the storage of account `addr` at `key` in the
  resumed world, through the observable `find?/lookupStorage` lens; for the EVM
  oracle this is `result.accounts`'s lens;
* `restoredGas result pd` — the gas the caller resumes with (`gasAfterReturn`);
* `successWord result pd` — the 0/1 success word the CALL pushes (`x`).

The field types are chosen so `evmCallOracle` instantiates each by *projection*
(definitional) of the bytecode resume. -/
structure CallOracle where
  /-- Post-call storage of `addr` at `key`, through the observable lens. -/
  postStorage : CallResult → PendingCall → AccountAddress → Word → Word
  /-- Gas restored to the caller on resume (`gasAfterReturn`). -/
  restoredGas : CallResult → PendingCall → UInt64
  /-- The 0/1 success word the CALL pushes (`x`). -/
  successWord : CallResult → PendingCall → Word

/-! ## The EVM instantiation — by-construction the lowered CALL

`evmCallOracle` defines each field as the corresponding projection of exp003's
`resumeAfterCall result pd` (`EVM/Evm/Semantics/Call.lean`). Each is therefore
*definitionally* what the lowered bytecode's CALL does to that observable:

* `postStorage` reads `result.accounts` (the map `resumeAfterCall` writes into
  `exec.accounts`) through the observable `find?/lookupStorage` lens;
* `restoredGas` is `(resumeAfterCall result pd).exec.gasAvailable`, i.e.
  `gasAfterReturn`;
* `successWord` is the word `resumeAfterCall` pushes — the head of
  `(resumeAfterCall result pd).exec.stack` (which is `pd.stack.push x = x ::
  pd.stack`), i.e. `x`.

By stating each as a *projection of `resumeAfterCall`*, the reflexivity headline
(`call_reflects_lowered`) is `rfl`-clean: the IR call effect at `evmCallOracle`
*is* the resume frame's observable, by construction. -/

/-- **The concrete EVM external-CALL effect** — one instantiation of `CallOracle`,
each field a projection of exp003's `resumeAfterCall`. By construction the lowered
bytecode's ext-call effect. -/
def evmCallOracle : CallOracle where
  postStorage := fun result pd addr key =>
    (resumeAfterCall result pd).exec.accounts.find? addr |>.option 0 (·.lookupStorage key)
  restoredGas := fun result pd => (resumeAfterCall result pd).exec.gasAvailable
  successWord := fun result pd =>
    -- the word pushed on top of the suspended stack (the head of the resumed
    -- stack, `pd.stack.push x = x :: pd.stack`) — `resumeAfterCall`'s `x`.
    (resumeAfterCall result pd).exec.stack.head?.getD 0

/-- exp003's CALL success flag `x` (verbatim from `resumeAfterCall`): `0` on code
failure / insufficient funds / call-depth limit, else `1`. Named so the oracle's
`successWord` can be pinned to it (`evmCallOracle_successWord_eq_x`). -/
def callSuccessFlag (result : CallResult) (pd : PendingCall) : Word :=
  if !result.success
      || (pd.value > (pd.callerAccounts.find? pd.frame.exec.executionEnv.address |>.elim 0 (·.balance)))
      || (pd.frame.exec.executionEnv.depth == 1024) then 0 else 1

/-- **The EVM oracle's success word is exactly exp003's CALL flag `x`.** The head
of the resumed stack `pd.stack.push x = x :: pd.stack` is `x`, by `rfl`. Pins the
"success word matches `x`" claim of the reflexivity headline to the concrete flag. -/
theorem evmCallOracle_successWord_eq_x (result : CallResult) (pd : PendingCall) :
    evmCallOracle.successWord result pd = callSuccessFlag result pd := rfl

end Lir.Frame
