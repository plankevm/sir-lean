import BytecodeLayer.Refinement

/-!
# DRAFT — the abstract `EVMSpec` interface + the flat instance `flatSpec`

> **STATUS: PARKED DRAFT — deliberately de-aggregated.** This is the reshape of
> the interim `EVMSemantics` (`BytecodeLayer/SharedObservable.lean`) into the
> interface Eduardo sketched, built on the FLAT (`«evm»`) side. It is additive:
> it does not touch `EVMSemantics`/`flatSem`, which remains the CANONICAL
> cross-engine interface (all live refinement/equivalence results go through it).
> This module was removed from the root aggregator on purpose (commit 28e01243,
> Phase-D hygiene) — it builds only via the lakefile glob and has zero importers;
> do not re-import it while it is a draft.
>
> Two items remain before this draft could replace `flatSem`: (a) Eduardo's
> adopt-vs-archive decision on the reshape, and (b) ratification of the Option-B
> State/Result modeling choice (§"The modeling choice" below) — the pick recorded
> there is the draft author's, not yet Eduardo's. Once ratified, `flatSem` can be
> retired in favour of `flatSpec` and the nested side can mirror it.

## What this fixes vs. the interim `EVMSemantics`

`EVMSemantics.run : World → Except E Result` has the **wrong shape**: the
bytecode being run is *buried inside* `World = CallParams` (in `codeSource`), so
the same `code` cannot be seen threading through two engines — it is part of the
opaque world. The agreed interface instead exposes **bytecode and state as
separate arguments**:

```lean
structure EVMSpec where
  State   : Type
  inject  : Input → State
  interp  : Bytecode → State → State
  observe : State → Observables
```

so `interp code (inject i)` makes `code` a visible, shared argument that the same
way across every conforming engine, and conformance is

```lean
Refines S I := ∀ code i, I.observe (I.interp code (I.inject i))
                       = S.observe (S.interp code (S.inject i))
```

## The modeling choice (input-state ≠ result-state) — see open question below

The flat engine is `messageCall : CallParams → Except ExecutionException CallResult`.
`CallParams` BUNDLES the code (`codeSource`) together with the **input** world
(accounts / gas / env / caller / …); `CallResult` is the **post-run** state
(returned accounts, gasRemaining, success, output, logs). Input-state and
result-state are genuinely *different Lean types*. So we have two options:

* **Option A** — one rich `State` covering both the input fields and the result
  fields; `inject` fills the input portion, `interp` runs and fills the result
  portion, `observe` reads the result portion. For the flat engine this means
  inventing a `CallParams ⊎ CallResult`-ish union type and a partial `State` that
  is half-populated before `interp` — artificial, since `messageCall` does not
  thread a single state type through.

* **Option B (CHOSEN here)** — keep `State`/`Result` **distinct**:
  `interp : Bytecode → State → Result`, `observe : Result → Observables`. This is
  a strictly more general `EVMSpec` than the `interp : … → State` sketch, and it
  is the *honest* shape for the flat engine: `State := CallParams` (the input
  world, code-free as far as `interp` cares — `interp` overwrites `codeSource`),
  `Result := Except ExecutionException CallResult` (exactly what `messageCall`
  returns, so `observe := observe_flat` plugs in unchanged), and
  `interp code s := messageCall { s with codeSource := .Code code }`.

We adapt the `EVMSpec` structure to Option B below (an extra `Result : Type`
field, `interp : Bytecode → State → Result`, `observe : Result → Observables`).
The sketch's `interp : Bytecode → State → State` is the special case
`Result := State`.

## `Input` / `Bytecode` / `Observables` for this draft

* `Bytecode := ByteArray` — raw EVM opcode bytes, exactly what `ToExecute.Code`
  wraps. Toolchain-neutral already (`ByteArray` is core), so this is the right
  shared `Bytecode` for both engines.
* `Observables := SharedObservable` — reused verbatim from `SharedObservable.lean`
  (the toolchain-neutral observable both engines compare through), with
  `observe := observe_flat`.
* `Input` — **for this flat draft** we take `Input := CallParams` and
  `inject := id`: the flat input world already *is* a `CallParams`, and threading
  it through unchanged keeps the draft honest about what the flat engine needs.
  The `codeSource` field of the injected `CallParams` is a **don't-care**:
  `interp` overwrites it with the supplied `code`, so it never leaks into the
  observable. *NOTE (later work):* the real shared `Input` must be
  **toolchain-neutral plain data** (like `SharedObservable`), since the nested
  side cannot import `CallParams`; a neutral `Input` + per-engine `inject :
  Input → State` bridges is the eventual shape. Flagged here, not built.
-/

namespace BytecodeLayer
open Evm

/-- **DRAFT** abstract EVM semantics interface (Option B: distinct `State`/`Result`).

An implementation supplies its **own** input-state type `State` and result type
`Result`, an `inject` building its input-state from the shared `Input`, an
`interp` running a `Bytecode` on its input-state to a `Result`, and an `observe`
piping its `Result` into the shared `Observables`. Bytecode and state are
**separate arguments** of `interp`, so the same `code` visibly threads through
every conforming engine — the whole point of the reshape.

`Bytecode`/`Input`/`Observables` are the *shared* (cross-engine) types; `State`
and `Result` are the impl's own. The sketch's `interp : Bytecode → State → State`
is the special case `Result := State`. -/
structure EVMSpec (Input Bytecode Observables : Type) where
  /-- The impl's own input-state representation. -/
  State   : Type
  /-- The impl's own result representation (Option B: may differ from `State`). -/
  Result  : Type
  /-- Build the impl's input-state from the shared inputs. -/
  inject  : Input → State
  /-- Run a bytecode on the impl's input-state, producing its result. -/
  interp  : Bytecode → State → Result
  /-- Pipe the impl's result into the shared observables. -/
  observe : Result → Observables

/-- Conformance of impl `I` to the canonical spec `S`: for every bytecode and
shared input, the two engines produce the **same observable**. With `interp`
taking `code` separately, the same `code` is plainly the shared argument. -/
def Refines {Input Bytecode Observables : Type}
    (S I : EVMSpec Input Bytecode Observables) : Prop :=
  ∀ (code : Bytecode) (i : Input),
    I.observe (I.interp code (I.inject i)) = S.observe (S.interp code (S.inject i))

/-! ## The flat instance `flatSpec`

`State := CallParams` (the flat input world), `Result := Except ExecutionException
CallResult` (what `messageCall` returns), `Bytecode := ByteArray`,
`Observables := SharedObservable`. `inject := id`, `observe := observe_flat`, and
`interp code s` plugs `code` into the code-source and runs `messageCall`. -/

/-- **DRAFT flat (`«evm»`) instance.** Reshapes `flatSem` so the bytecode is a
**separate argument** of `interp` instead of being buried in the world. Note
`interp code s = messageCall { s with codeSource := .Code code }`: the supplied
`code` *overwrites* whatever `s.codeSource` held, so `code` is the only thing the
result's program depends on. `observe := observe_flat` and the observable type is
the shared `SharedObservable`, so this conforms to the same canonical spec the
nested side will. -/
def flatSpec : EVMSpec CallParams ByteArray SharedObservable where
  State   := CallParams
  Result  := Except ExecutionException CallResult
  inject  := id
  interp  := fun code s => messageCall { s with codeSource := .Code code }
  observe := observe_flat

/-! ## Sanity check: the do-nothing fact in the new shape

Re-express `flat_refines_emptyObs` through `flatSpec`. We feed the `stopProgram`
bytecode and `stopParams` as the input; because `flatSpec.interp` overwrites
`codeSource` with `.Code stopProgram` and `stopParams.codeSource` is *already*
`.Code stopProgram`, the injected+interpreted call is literally `messageCall
stopParams`, so the existing `flat_refines_emptyObs` transports verbatim. -/

/-- `flatSpec.interp stopProgram (flatSpec.inject stopParams)` is definitionally
`messageCall stopParams` — overwriting `codeSource` with the value it already
holds is a no-op on this `CallParams`. -/
theorem flatSpec_interp_stopParams :
    flatSpec.interp stopProgram (flatSpec.inject stopParams) = messageCall stopParams := rfl

/-- **DRAFT sanity check.** The do-nothing `STOP` call, run through the new
`flatSpec` shape, observes as the canonical `emptyObs` (its own gas) — i.e.
`flat_refines_emptyObs` survives the reshape unchanged. Inherited definitionally
from `flatSpec_interp_stopParams`. -/
theorem flatSpec_stop_emptyObs :
    (flatSpec.observe (flatSpec.interp stopProgram (flatSpec.inject stopParams))).agrees
      (emptyObs
        (flatSpec.observe (flatSpec.interp stopProgram (flatSpec.inject stopParams))).gas) := by
  -- `flatSpec.observe (flatSpec.interp …) = observe_flat (messageCall stopParams)
  --                                       = observe_flat (flatSem.run stopParams)`
  show (observe_flat (messageCall stopParams)).agrees
        (emptyObs (observe_flat (messageCall stopParams)).gas)
  exact flat_refines_emptyObs

end BytecodeLayer
