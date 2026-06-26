import LirLean.V2.Call
import LirLean.Match
import LirLean.WorkedCall

/-!
# LirLean v2 — the **call realisability bridge** (`docs/ir-design-v3.md` §3, §7)

`LirLean/V2/Oracle.lean` discharged the *gas* oracle's realisability: the abstract
`gasRead` events are *realised* by a witnessing bytecode `Runs`, and the §3.4 law is a
**consequence** of that realisation (`GasRealises.monotoneGas` ⟵ `Runs.gasAvailable_le`),
never an axiom. This module is the **call** analogue: the abstract `V2.CallOracle`
(`LirLean/V2/Machine.lean`) is *realised* by v1's concrete `evmCallOracle`
(`LirLean/Call.lean`), and the bundle the realised oracle yields is shown — by
construction — to equal the lowered bytecode CALL's observable effect.

This file is **bytecode-coupled** (it references `CallResult`/`PendingCall`/`evmCallOracle`
and v1's `Match` facts), so it lives here rather than in the frame-free
`Machine.lean`/`Law.lean`, exactly as `Oracle.lean` is the gas-side bridge.

## What is realised (the §7 interaction model, on the call side)

The abstract `V2.CallOracle` is `Word → Word → World → (World × Word)` — callee, gas-to-
forward, current world ↦ (post-call world, 0/1 success). The realised post-world comes from
the lowered bytecode's `resumeAfterCall`, which depends on chain state the IR lacks; so the
oracle **ignores its `World` argument** and reads the realised bundle off v1's
`evmCallOracle` projections instead:

* the post-call `World` is `evmCallOracle.postStorage result pd self` — the self account's
  post-CALL storage lens, exactly `Match`'s `M3` lens on `resumeAfterCall result pd`;
* the success word is `evmCallOracle.successWord result pd` — which `rfl`-reduces to
  exp003's CALL flag `x` (`callSuccessFlag`), per `evmCallOracle_successWord_eq_x`.

`callRealises_bridge` is the call analogue of `GasRealises.monotoneGas`: under a returning
external CALL (`CallReturns callFr resumeFr`), the realised oracle's `(world', success)`
*is* the lowered CALL's observable — `world'` is the resumed frame's self-storage lens
(`storageAt resumeFr self`, the `M3` lens), and `success` is the CALL flag `x`. It is
`rfl`-clean: `evmV2CallOracle … = (postStorage…, successWord…)` by `rfl`, the storage half
is `call_reflects_lowered`'s `postStorage = storageAt` projection at the self address, and
the success half is `evmCallOracle_successWord_eq_x`.
-/

namespace Lir.V2

open Evm
open Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare

/-! ## Step 2a — instantiating the abstract `V2.CallOracle` to v1's `evmCallOracle`

`evmV2CallOracle result pd self` is the abstract `V2.CallOracle` *realised* by the bytecode
CALL data `(result, pd)` at self address `self`. It ignores the queried `World` argument
(the realised post-world comes from `resumeAfterCall`, the "depends on bytecode state the IR
lacks" point of §7) and returns v1's `evmCallOracle` projections: the post-call self-storage
lens, and the 0/1 success word. `restoredGas` is dropped — v2 has no gas in state, so the
restored-gas field is irrelevant to the gas-free machine (§7). -/

/-- **The realised v2 call oracle.** Instantiates the abstract `V2.CallOracle` to v1's
`evmCallOracle`, parameterised by the bytecode CALL data `(result, pd)` and the self address
`self`. The yielded post-`World` is the self account's post-CALL storage lens
(`evmCallOracle.postStorage result pd self`); the success word is `evmCallOracle.successWord
result pd`. The queried `World` argument is ignored — the realised post-world is fixed by the
bytecode's `resumeAfterCall`, not recomputed from the IR's view. -/
def evmV2CallOracle (result : CallResult) (pd : PendingCall) (self : AccountAddress) :
    CallOracle :=
  fun _callee _gasFwd _world =>
    ( (fun key => evmCallOracle.postStorage result pd self key)
    , evmCallOracle.successWord result pd )

/-! ## Step 2a — the realisability bridge lemma (the call analogue of `monotoneGas`)

Under a returning external CALL, the `(world', success)` bundle `evmV2CallOracle` yields
equals the lowered bytecode CALL's observable effect. -/

/-- **The call realisability bridge.** Given a returning external CALL
(`CallReturns callFr resumeFr`, so `resumeFr = resumeAfterCall result pd` for the projected
child result / pending call), the bundle `evmV2CallOracle result pd self` yields — for *any*
queried callee / gas-to-forward / world — is exactly the lowered CALL's observable effect:

* the post-call `World` is the resumed frame's self-storage lens (`storageAt resumeFr self`,
  the `M3` lens — `Match.call_reflects_lowered`'s `postStorage` projection); and
* the success word is exp003's CALL flag `x` (`callSuccessFlag result pd`, via
  `evmCallOracle_successWord_eq_x`).

By construction / `rfl`-clean: the oracle is `(postStorage…, successWord…)` definitionally,
the storage half is the `call_reflects_lowered` projection at the self address, and the
success half is the `successWord = x` reflexivity. This is the call analogue of
`GasRealises.monotoneGas` — the IR's call effect *is* the lowered bytecode's, by
realisation, never assumed. -/
theorem callRealises_bridge {callFr resumeFr : Frame} (self : AccountAddress)
    (hcall : CallReturns callFr resumeFr)
    (callee gasFwd : Word) (w : World) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (evmV2CallOracle result pd self callee gasFwd w).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmV2CallOracle result pd self callee gasFwd w).2
          = callSuccessFlag result pd := by
  obtain ⟨result, pd, hres, hstore, _hgas, hsucc⟩ := call_reflects_lowered hcall
  refine ⟨result, pd, hres, ?_, ?_⟩
  · -- world' = postStorage self = storageAt resumeFr self, pointwise via `hstore`
    show (fun key => evmCallOracle.postStorage result pd self key)
        = (fun key => storageAt resumeFr self key)
    funext key; exact hstore self key
  · -- success = successWord = callSuccessFlag (by `hsucc`, which is `rfl`)
    show evmCallOracle.successWord result pd = callSuccessFlag result pd
    exact hsucc

/-! ## Step 2b — with-CALL parity in v2's gas-free observable form

We reuse the abstract worked call run (`call_IRRun`, `LirLean/V2/Call.lean`) and the worked
bytecode CALL scenario (`LirLean/WorkedCall.lean`). Instantiating the abstract oracle to
`evmV2CallOracle` for the *realised* `workedCall` CALL data, the v2 IR run's `Observable`
equals the lowered bytecode's post-CALL effect: its `worldDelta` is the resumed frame's
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
under the *realised* oracle `wcV2Oracle g` (and consuming the single `gasRead obs` event)
halts with an `Observable` whose:

* `worldDelta` is the resumed bytecode frame's self-storage lens `storageAt (wcResumed g)
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
    IRRun callIR (wcV2Oracle g) w₀ [Event.gasRead obs]
      { worldDelta := fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key
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
  -- worldDelta: `(wcV2Oracle g 42 obs w₀).1 = fun key => postStorage result pd addrCaller key`
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
      = { worldDelta := fun key => storageAt (Lir.WorkedCall.wcResumed g) addrCaller key
        , result := .returned (callSuccessFlag result pd) } := by
    unfold callObsResult
    rw [hw, hr]
  rw [← hobs]; exact hrun

-- Build-enforced axiom-cleanliness guards: the call realisability bridge and the worked
-- with-CALL parity theorem depend only on `[propext, Classical.choice, Quot.sound]`.
#print axioms callRealises_bridge
#print axioms wc_call_parity_v2

end Lir.V2
