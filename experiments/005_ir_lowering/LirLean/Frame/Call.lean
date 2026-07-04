import LirLean.Spec.IR
import LirLean.Frame.SmallStep
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
(defeq / by-construction the lowered call's projection) + a reflexivity headline
under `Match` (`Lir.call_reflects_lowered` in `LirLean/Match.lean`).

## What the oracle captures (and the one thing it cannot)

`resumeAfterCall result pd` (exp003 `EVMLean/Evm/Semantics/Call.lean`) does three
things the IR cares about:

* sets `exec.accounts := result.accounts` — the **post-storage world** (read
  through the same observable `find?/lookupStorage` lens as `Match`'s `M3`);
* sets `gasAvailable := gasAfterReturn` — the **restored gas**
  (`machineWithOutput.gasAvailable + result.gasRemaining`);
* pushes the **0/1 success word** `x` onto the stack.

The oracle captures the first two as recompute-friendly *state* effects and the
third as a word. The success word is the ONE value that is genuinely *not*
recomputable from a pure `Expr` (it is dynamic — it depends on the child run), so it
cannot live in `defs`/`locals` as a recompute-on-use value. **The resolution
(`docs/ir-design.md` §5):** give it a dedicated `callResult` slot in `IRState`
(`LirLean/SmallStep.lean`). `IRState.applyCall` writes the oracle's `successWord`
there alongside the storage/gas effects, and `IRState.bindCallResult` reads it
*once* into `locals` at the call's `resultTmp` — after which a use of `resultTmp` is
an ordinary `Expr.tmp` read. This **keeps `Match`'s `M5 stack_nil`**: the slot is
pure IR state, and the lowered CALL's physical flag-on-stack is bridged by the
`successWord` reflexivity (`call_reflects_lowered`), not threaded through `Match`.
The reflexivity headline reflects all three effects (post-storage, restored gas, and
the success word's value). This matches the gas oracle's altitude: a clean
abstraction + a reflexivity equation.
-/

namespace Lir

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
  resumed world, through the observable `find?/lookupStorage` lens (the EVM side of
  `Match`'s `M3`); for the EVM oracle this is `result.accounts`'s lens;
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
`resumeAfterCall result pd` (`EVMLean/Evm/Semantics/Call.lean`). Each is therefore
*definitionally* what the lowered bytecode's CALL does to that observable:

* `postStorage` reads `result.accounts` (the map `resumeAfterCall` writes into
  `exec.accounts`) through the same `find?/lookupStorage` lens as `Match`'s `M3`;
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

/-! ## The IR-level call transformer (`IRState.applyCall`)

`IRState.applyCall oracle result pd` threads the oracle's call effect into the IR
state — storage becomes the oracle's `postStorage` lens (keyed on the self
address). It is parametric over the oracle, so the IR small-step reasons for all
instantiations; under lowering the oracle is `evmCallOracle` and the resulting state
is *reflexively* the resumed frame's observable (`call_reflects_lowered`). The
gas-free v1 state carries no gas counter, so the oracle's `restoredGas` projection
is not applied to the state (it is still reflected at the bytecode boundary by
`call_reflects_lowered`'s `restoredGas = gasAvailable` conjunct).

The success word is the one effect that is **not** recomputable from a pure `Expr`
(it is dynamic — it depends on the child run), so it cannot live in `defs`/`locals`
as a recompute-on-use value. We therefore fold it into the dedicated `callResult`
slot of `IRState` (`LirLean/SmallStep.lean`): `applyCall` writes the oracle's
`successWord` there, and `IRState.bindCallResult` reads it once into `locals` at the
call's `resultTmp` (after which a later use is an ordinary `Expr.tmp` read). This
keeps `Match`'s `M5 stack_nil` intact — the slot is pure IR state, and the lowered
CALL's physical flag-on-stack is bridged by the `successWord` reflexivity, not by
`Match`. `locals` is still untouched by `applyCall` itself (the bind is a separate,
explicit step). -/

/-- Thread the oracle's external-CALL effect into the IR state at self address
`self`: storage follows the oracle's post-call lens, and the `callResult` slot
receives the oracle's 0/1 `successWord` (the one non-recomputable effect — see the
module docstring on `bindCallResult`/`resultTmp`). `locals` is untouched here;
binding the result to `resultTmp` is the separate `IRState.bindCallResult` step. -/
def IRState.applyCall (st : IRState) (oracle : CallOracle)
    (result : CallResult) (pd : PendingCall) (self : AccountAddress) : IRState :=
  { st with
      storage    := fun k => oracle.postStorage result pd self k
      callResult := some (oracle.successWord result pd) }

end Lir
