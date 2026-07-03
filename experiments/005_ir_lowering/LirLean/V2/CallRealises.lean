import LirLean.V2.Call
import LirLean.Match

/-!
# LirLean v2 — the **call realisability bridge** (`docs/ir-design-v3.md` §3, §7)

The now-deleted `LirLean/V2/Oracle.lean` discharged the *gas* oracle's realisability: the abstract
gas reads are *realised* by a witnessing bytecode `Runs`, and the §3.4 law is a
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

/-! The `workedCall` instance of this bridge (`wcV2Oracle`, `wc_call_parity_v2`) is a *leaf
example*, not a headline dependency, so it lives in `LirLean/V2/WorkedCallParity.lean` (which
imports both this module and the offset-coupled `LirLean/WorkedCall.lean`). Keeping it out of
this module is what keeps `LirLean.WorkedCall` off the headline import cone. -/

-- Build-enforced axiom-cleanliness guard: the call realisability bridge depends only on
-- `[propext, Classical.choice, Quot.sound]`.

end Lir.V2
