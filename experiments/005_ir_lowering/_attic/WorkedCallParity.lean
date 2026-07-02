import LirLean.V2.CallRealises
import LirLean.V2.RunLog
import LirLean.WorkedCall

/-!
# LirLean v2 — with-CALL parity, worked example (`docs/ir-design-v3.md` §3, §7)

This is the **worked-example leaf** for the call realisability bridge. The general
bridge (`callRealises_bridge`, the call analogue of `GasRealises.monotoneGas`) lives
in `LirLean/V2/CallRealises.lean` and is part of the headline import cone. This file
instantiates that bridge to the concrete `workedCall` bytecode scenario
(`LirLean/WorkedCall.lean`) — a *leaf example*, NOT a headline dependency.

It used to live inside `CallRealises.lean`, which forced `LirLean.WorkedCall` into the
headline import chain (`SimStmt → V2/CallRealises → WorkedCall`) even though the
headlines reference only the general `evmV2CallOracle` / `callRealises_bridge`. Splitting
the `workedCall` instance out here removes that over-broad coupling: the four headlines no
longer transitively import the 1752-line offset-coupled `WorkedCall.lean`, so changes to
the concrete byte layout (e.g. spilling sload) touch `WorkedCall` only as a leaf.
-/

namespace Lir.V2

open Evm
open Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare

/-! ## Step 2b — with-CALL parity in v2's gas-free observable form

We reuse the abstract worked call run (`call_IRRun`, `LirLean/V2/Call.lean`) and the worked
bytecode CALL scenario (`LirLean/WorkedCall.lean`). Instantiating the abstract oracle to
`evmV2CallOracle` for the *realised* `workedCall` CALL data, the v2 IR run's `Observable`
equals the lowered bytecode's post-CALL effect: its `world` is the resumed frame's
self-storage lens (the `M3` lens on `resumeAfterCall`) and its `result` returns the CALL
flag `x`. This reaches `workedCall` parity in v2's gas-free observable form: **IR observable
= lowered observable**.

The bytecode CALL data is read off `Lir.WorkedCall.wc_callReturns g` — the genuine, hypothesis-
free `CallReturns (wcCallSite g) (wcResumed g)` (for `g ≥ 50000`). The realised oracle is
`evmV2CallOracle` at that returning call's `(result, pd)`, self `addrCaller` (the caller of
`workedCall`). -/

/-- The realised v2 call oracle for `workedCall`'s single CALL, at gas knob `g`: it is
`evmV2CallOracle` instantiated at the projected child result `(wcChildFrameRes g).toCallResult`
and the pending call `callPending (wcCallSite g) 0xCA11EE 0xFFFFFFFF`, self `addrCaller`. -/
def wcV2Oracle (g : UInt64) : CallOracle :=
  evmV2CallOracle (Lir.WorkedCall.wcChildFrameRes g).toCallResult
    (callPending (Lir.WorkedCall.wcCallSite g) 0xCA11EE 0xFFFFFFFF)
    addrCaller

/-- **With-CALL parity in v2's gas-free observable form (`workedCall`).** For `g ≥ 50000`
and any initial world `w₀` / observed gas `obs`, running the worked v2 call program `callIR`
under the *realised* oracle `wcV2Oracle g` (and consuming the single gas read `obs`)
halts with an `Observable` whose:

* `world` is the resumed bytecode frame's self-storage lens `storageAt (wcResumed g)
  addrCaller` — the lowered CALL's post-storage observable (`Match`'s `M3` lens); and
* `result` is `.returned (callSuccessFlag … )` — the CALL flag `x` the lowered bytecode
  pushes.

Plus three observable pins of the realised scenario: the returned flag is `1` (the genuine
child CALL succeeds — `wcResumed_stack`); the caller's slot `7` survives the CALL at `5`
(`wcResumed_sload7`, the post-storage observable the IR run carries); and the resumed frame's
gas is `g − 46834` (`wcResumed_gas`, needs `g ≥ 50000` — the `callGasCap` cancellation).

This is **IR observable = lowered observable** on the call side: the v2 IR run reads its
whole observable off the realised call oracle, which `callRealises_bridge` ties to the
lowered bytecode CALL's effect. The `∀ O, IRRun … O → O = …` uniqueness shape follows from
`IRRun.det` (`call_IRRun_unique`); we state the produced-observable form here, with the
pins. -/
theorem wc_call_parity_v2 (g : UInt64) (hg : 50000 ≤ g.toNat) (w₀ : World) (obs : Word) :
    let result := (Lir.WorkedCall.wcChildFrameRes g).toCallResult
    let pd := callPending (Lir.WorkedCall.wcCallSite g) 0xCA11EE 0xFFFFFFFF
    IRRun callIR (wcV2Oracle g) w₀ [obs]
      { world := fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key
      , result     := .returned (callSuccessFlag result pd) }
    ∧ callSuccessFlag result pd = 1
    ∧ (fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key) 7 = 5
    ∧ (Lir.WorkedCall.wcResumed g).exec.gasAvailable.toNat = g.toNat - 46834 := by
  intro result pd
  -- The abstract worked run (`call_IRRun`) produces `callObsResult (wcV2Oracle g) w₀ obs`.
  -- We rewrite its two components to the lowered CALL's observable. Both are `rfl`-clean:
  -- `wcResumed g` is *definitionally* `resumeAfterCall result pd` (its very definition), and
  -- `evmCallOracle.postStorage`/`successWord` are *defined* as the corresponding projections
  -- of `resumeAfterCall result pd` (`LirLean/Call.lean`). So the realised oracle's bundle
  -- equals the resumed frame's `storageAt` lens and the CALL flag `x`, by construction.
  have hrun := call_IRRun (wcV2Oracle g) w₀ obs
  -- world: `(wcV2Oracle g 42 obs w₀).1 = fun key => postStorage result pd addrCaller key`
  -- (by `rfl`), and `postStorage result pd addrCaller key = storageAt (resumeAfterCall result
  -- pd) addrCaller key = storageAt (wcResumed g) addrCaller key` (all `rfl`).
  have hw : ((wcV2Oracle g) 42 obs w₀).1
      = (fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key) := rfl
  -- success: `(wcV2Oracle g 42 obs w₀).2 = successWord result pd = callSuccessFlag result pd`,
  -- the `evmCallOracle_successWord_eq_x` reflexivity (`rfl`).
  have hr : ((wcV2Oracle g) 42 obs w₀).2 = callSuccessFlag result pd :=
    evmCallOracle_successWord_eq_x result pd
  -- the genuine child CALL succeeds (`g ≥ 50000`): the lowered CALL pushes `1`, which is the
  -- head of `wcResumed`'s stack `[1]` — exactly the CALL flag `x` (`successWord`/`rfl`).
  have hflag : callSuccessFlag result pd = 1 := by
    rw [← evmCallOracle_successWord_eq_x result pd]
    show (Evm.resumeAfterCall result pd).exec.stack.head?.getD 0 = 1
    show (Lir.WorkedCall.wcResumed g).exec.stack.head?.getD 0 = 1
    rw [Lir.WorkedCall.wcResumed_stack g]; rfl
  -- the concrete observable values: the caller's slot 7 survives the CALL = 5
  -- (`wcResumed_sload7`), and the resumed frame's gas is `g − 46834` (`wcResumed_gas`,
  -- needs `g ≥ 50000`). Both pin the realised scenario.
  have hsload : (fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key) 7 = 5 :=
    Lir.WorkedCall.wcResumed_sload7 g
  have hgas : (Lir.WorkedCall.wcResumed g).exec.gasAvailable.toNat = g.toNat - 46834 :=
    Lir.WorkedCall.wcResumed_gas g hg
  refine ⟨?_, hflag, hsload, hgas⟩
  -- rewrite `callObsResult`'s two fields and discharge with the abstract run
  have hobs : callObsResult (wcV2Oracle g) w₀ obs
      = { world := fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key
        , result := .returned (callSuccessFlag result pd) } := by
    unfold callObsResult
    rw [hw, hr]
  rw [← hobs]; exact hrun

/-! ## Concrete conformance through `observe` + the realised call oracle (`lower_conforms`, specialised)

`wc_call_parity_v2` (above) is `lower_conforms` for the worked program, but it states the IR
observable's `world` *inline* (`storageAt (wcResumed g) addrCaller`). The corollary below
re-expresses that world through the **`observe` bridge** of the *recorded bytecode result*
and under the **realised call oracle** (`realisedCall`, `LirLean/V2/RunLog.lean`), stitching
the three convergence pieces into one statement:

* the **realised oracle** — `realisedCall` read off a `RunLog` whose single recorded
  CALL is the worked call's `CallRecord` (the genuine child result + pending), which is
  `wcV2Oracle g` by `realisedCall_eq_evmV2` (`rfl`-clean);
* the **`observe` bridge** — applied to `wcChildFrameRes g`, the recorded child
  `FrameResult` whose `.toCallResult` is the record's result, and which
  `resumeAfterCall` writes back as the resumed frame's `exec.accounts` — so
  `observe`'s self-storage lens *is* `storageAt (wcResumed g) addrCaller` by
  construction;
* the **IR run** — `IRRun callIR (realisedCall …) …` under the realised oracle, whose
  produced observable is `wc_call_parity_v2`'s.

**Scope (reported).** This is the *world* component of conformance — the IR observable
the realised call oracle actually determines. The `result` field is `observe`'s
restricted `.stopped` (the value-free boundary; see `observe`'s doc), so it is not
claimed here. And the recorded `FrameResult` used is the genuine child result the worked
CALL records (`wcChildFrameRes g`, the datum `realisedCall` is built from), not the
top-level `runWithLog`'s `observable`: evaluating `runWithLog` over the *whole*
`workedCall` program to a closed-form `RunLog` is the deferred general-`lower` step
(threading account-preservation through the ~15 post-CALL frames). The corollary
exercises `observe` + `realisedCall` + `IRRun` together on the concrete worked CALL. -/

/-- The single-record run log for `workedCall`'s one external CALL at gas knob `g`: the
recorded child `FrameResult` projected to a `CallResult`, with the worked pending call,
as the sole `CallRecord`. `observable` is `wcChildFrameRes g` (the recorded child
result); `gas` is left empty (the gas channel is `realisedGas`/`wc_call_parity_v2`'s
single `obs`, exercised separately). `realisedCall` off this log is `wcV2Oracle g`. -/
def wcRunLog (g : UInt64) : RunLog :=
  { observable := Lir.WorkedCall.wcChildFrameRes g
    gas        := []
    sloads     := []
    calls      := [{ result  := (Lir.WorkedCall.wcChildFrameRes g).toCallResult
                     pending := callPending (Lir.WorkedCall.wcCallSite g) 0xCA11EE 0xFFFFFFFF }] }

/-- **`realisedCall (wcRunLog g) addrCaller = wcV2Oracle g`.** The realised call oracle
read off the worked single-record log *is* the worked oracle, `rfl`/`simp`-clean via
`realisedCall_eq_evmV2` (the record's `(result, pending)` are exactly `wcV2Oracle`'s). -/
theorem realisedCall_wcRunLog (g : UInt64) :
    realisedCall (wcRunLog g) addrCaller = wcV2Oracle g :=
  realisedCall_eq_evmV2 (log := wcRunLog g) addrCaller rfl

/-- **Concrete conformance through `observe` (`lower_conforms`, worked-program world
component).** For `g ≥ 50000` and any initial world `w₀` / observed gas `obs`, running
the worked IR program `callIR` under the **realised** call oracle `realisedCall
(wcRunLog g) addrCaller` (and consuming the single gas read `obs`) halts with an
`Observable` whose `world` is exactly `observe addrCaller (wcRunLog g).observable`'s
world — the `observe` bridge of the recorded child bytecode result.

This stitches the recorder's record (`wcRunLog`/`realisedCall`), the realised oracle
(`realisedCall_wcRunLog` ⟶ `wcV2Oracle g`), and the `observe` bridge into one
statement: the concrete IR run under the realised oracle = `observe` of the recorded
bytecode result, on the world component. The two pins of the realised scenario (the
CALL succeeds — flag `1`; the caller's slot `7` survives at `5`) ride along from
`wc_call_parity_v2`. (`result`-field and full top-level-`runWithLog` recovery are the
reported deferrals — see the section/`observe` docs.) -/
theorem wc_observe_conforms (g : UInt64) (hg : 50000 ≤ g.toNat) (w₀ : World) (obs : Word) :
    IRRun callIR (realisedCall (wcRunLog g) addrCaller) w₀ [obs]
      { world  := (observe addrCaller (wcRunLog g).observable).world
      , result := .returned (callSuccessFlag
          (Lir.WorkedCall.wcChildFrameRes g).toCallResult
          (callPending (Lir.WorkedCall.wcCallSite g) 0xCA11EE 0xFFFFFFFF)) }
    ∧ callSuccessFlag (Lir.WorkedCall.wcChildFrameRes g).toCallResult
        (callPending (Lir.WorkedCall.wcCallSite g) 0xCA11EE 0xFFFFFFFF) = 1
    ∧ (observe addrCaller (wcRunLog g).observable).world 7 = 5 := by
  -- `observe`'s world on the recorded child result *is* `wc_call_parity_v2`'s world:
  -- `observe`'s lens reads `(wcChildFrameRes g).toCallResult.accounts`, which is exactly
  -- `(resumeAfterCall … ).exec.accounts = (wcResumed g).exec.accounts` by `resumeAfterCall`,
  -- so it is `storageAt (wcResumed g) addrCaller`, `rfl`-clean.
  have hworld : (observe addrCaller (wcRunLog g).observable).world
      = (fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key) := rfl
  -- the realised oracle off the worked log is `wcV2Oracle g` (`rfl`/`simp`-clean).
  rw [realisedCall_wcRunLog g, hworld]
  -- now it is exactly `wc_call_parity_v2`'s statement (minus the gas/sload pin we don't restate).
  obtain ⟨hrun, hflag, hsload, _hgas⟩ := wc_call_parity_v2 g hg w₀ obs
  exact ⟨hrun, hflag, hsload⟩

-- Build-enforced axiom-cleanliness guards: the worked with-CALL parity theorem and the
-- worked `observe`-bridged conformance depend only on `[propext, Classical.choice, Quot.sound]`.
#print axioms wc_call_parity_v2
#print axioms realisedCall_wcRunLog
#print axioms wc_observe_conforms

end Lir.V2
