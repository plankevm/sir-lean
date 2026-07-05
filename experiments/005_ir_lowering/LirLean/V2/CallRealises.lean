import LirLean.V2.Call
import LirLean.Frame.Match

/-!
# LirLean v2 — the **call realisability bridge** (`docs/ir-design-v3.md` §3, §7)

The now-deleted `LirLean/V2/Oracle.lean` discharged the *gas* stream's realisability: the abstract
gas reads are *realised* by a witnessing bytecode `Runs`, and the §3.4 law is a
**consequence** of that realisation (`GasRealises.monotoneGas` ⟵ `Runs.gasAvailable_le`),
never an axiom. This module is the **call** analogue: an abstract `V2.CallStream` entry
(`LirLean/V2/Machine.lean`) is *realised* by v1's concrete `evmCallOracle`
(`LirLean/Call.lean`), and the `(world', success)` entry is shown — by construction — to
equal the lowered bytecode CALL's observable effect.

This file is **bytecode-coupled** (it references `CallResult`/`PendingCall`/`evmCallOracle`
and v1's `Match` facts), so it lives here rather than in the frame-free
`Machine.lean`/`Law.lean`, exactly as `Oracle.lean` is the gas-side bridge.

## What is realised (the §7 interaction model, on the call side)

A `V2.CallStream` entry is a `(World × Word)` — (post-call world, 0/1 success). The realised
post-world comes from the lowered bytecode's `resumeAfterCall`, which depends on chain state
the IR lacks; so the realised entry reads off v1's `evmCallOracle` projections:

* the post-call `World` is `evmCallOracle.postStorage result pd self` — the self account's
  post-CALL storage lens, exactly `Match`'s `M3` lens on `resumeAfterCall result pd`;
* the success word is `evmCallOracle.successWord result pd` — which `rfl`-reduces to
  exp003's CALL flag `x` (`callSuccessFlag`), per `evmCallOracle_successWord_eq_x`.

`callRealises_bridge` is the call analogue of `GasRealises.monotoneGas`: under a returning
external CALL (`CallReturns callFr resumeFr`), the realised entry's `(world', success)`
*is* the lowered CALL's observable — `world'` is the resumed frame's self-storage lens
(`storageAt resumeFr self`, the `M3` lens), and `success` is the CALL flag `x`. It is
`rfl`-clean: `evmV2CallEntry … = (postStorage…, successWord…)` by `rfl`, the storage half
is `call_reflects_lowered`'s `postStorage = storageAt` projection at the self address, and
the success half is `evmCallOracle_successWord_eq_x`.
-/

namespace Lir.V2

open Evm
open Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare

/-! ## Step 2a — the realised `V2.CallStream` entry off v1's `evmCallOracle`

`evmV2CallEntry result pd self` is a single `V2.CallStream` entry *realised* by the bytecode
CALL data `(result, pd)` at self address `self`: the post-call self-storage lens paired with
the 0/1 success word. `restoredGas` is dropped — v2 has no gas in state, so the restored-gas
field is irrelevant to the gas-free machine (§7). -/

/-- **The realised v2 call-stream entry.** The `(World × Word)` a recorded bytecode CALL
`(result, pd)` at self address `self` contributes to the consumed call stream: the post-call
self-storage lens (`evmCallOracle.postStorage result pd self`) paired with the success word
(`evmCallOracle.successWord result pd`). Positional — the entry is fixed by the bytecode's
`resumeAfterCall`, indexed by the record, NOT a function of the call's IR-visible inputs. -/
def evmV2CallEntry (result : CallResult) (pd : PendingCall) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCallOracle.postStorage result pd self key)
  , evmCallOracle.successWord result pd )

/-! ## Step 2a — the realisability bridge lemma (the call analogue of `monotoneGas`)

Under a returning external CALL, the `(world', success)` entry `evmV2CallEntry` names
equals the lowered bytecode CALL's observable effect. -/

/-- **The call realisability bridge.** Given a returning external CALL
(`CallReturns callFr resumeFr`, so `resumeFr = resumeAfterCall result pd` for the projected
child result / pending call), the entry `evmV2CallEntry result pd self` is exactly the
lowered CALL's observable effect:

* its `.1` (post-call `World`) is the resumed frame's self-storage lens
  (`storageAt resumeFr self`, the `M3` lens — `Match.call_reflects_lowered`'s `postStorage`
  projection); and
* its `.2` (success word) is exp003's CALL flag `x` (`callSuccessFlag result pd`, via
  `evmCallOracle_successWord_eq_x`).

By construction / `rfl`-clean: the entry is `(postStorage…, successWord…)` definitionally,
the storage half is the `call_reflects_lowered` projection at the self address, and the
success half is the `successWord = x` reflexivity. This is the call analogue of
`GasRealises.monotoneGas` — the IR's call effect *is* the lowered bytecode's, by
realisation, never assumed. -/
theorem callRealises_bridge {callFr resumeFr : Frame} (self : AccountAddress)
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (evmV2CallEntry result pd self).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmV2CallEntry result pd self).2
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

/-! ## Step 6 — the realised `V2.CreateStream` entry off v1's `evmCreateOracle`

The CREATE twin of `evmV2CallEntry`/`callRealises_bridge`. A `V2.CreateStream` entry is a
`(World × Word)` — (post-create world, deployed-address-or-0 word). The realised entry reads
off v1's `evmCreateOracle` projections: the post-create `World` is the self account's storage
lens, and the pushed word is `createAddrOrZero` (the CREATE analogue of `callSuccessFlag`).
The bridge is off `create_reflects_lowered` (the R3 non-`rfl` storage side, discharged in
`Frame/Match.lean`), exactly as the call bridge is off `call_reflects_lowered`. -/

/-- **The realised v2 create-stream entry** (twin of `evmV2CallEntry`). The `(World × Word)` a
recorded bytecode CREATE `(result, pd)` at self address `self` contributes to the consumed
create stream: the post-create self-storage lens (`evmCreateOracle.postStorage result pd self`)
paired with the deployed-address-or-`0` word (`evmCreateOracle.addressWord result pd`).
Positional — the entry is fixed by the bytecode's `resumeAfterCreate` data, indexed by the
record, NOT a function of the create's IR-visible inputs. -/
def evmV2CreateEntry (result : CreateResult) (pd : PendingCreate) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCreateOracle.postStorage result pd self key)
  , evmCreateOracle.addressWord result pd )

/-- **The create realisability bridge** (twin of `callRealises_bridge`). Given a returning,
successfully-resumed CREATE (`CreateReturns createFr resumeFr`, so `resumeAfterCreate result pd
= .ok resumeFr` for the projected child result / pending create), the entry `evmV2CreateEntry
result pd self` is exactly the lowered CREATE's observable effect:

* its `.1` (post-create `World`) is the resumed frame's self-storage lens
  (`storageAt resumeFr self`, the `M3` lens — `Match.create_reflects_lowered`'s `postStorage`
  projection, via the 63/64-guarded `accounts := result.accounts` unfold, R3); and
* its `.2` (pushed word) is the deployed-address-or-`0` (`createAddrOrZero result pd`, via
  `evmCreateOracle_addressWord_eq`).

The CREATE analogue of `callRealises_bridge`: the IR's create effect *is* the lowered
bytecode's, by realisation, never assumed. The storage half rides `create_reflects_lowered`'s
short unfold (the create-specific cost CALL got for free); the address half is `rfl`-clean. -/
theorem createRealises_bridge {createFr resumeFr : Frame} (self : AccountAddress)
    (hc : CreateReturns createFr resumeFr) :
    ∃ result pd, resumeAfterCreate result pd = .ok resumeFr
      ∧ (evmV2CreateEntry result pd self).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmV2CreateEntry result pd self).2
          = createAddrOrZero result pd := by
  obtain ⟨result, pd, hres, hstore, haddr⟩ := create_reflects_lowered hc
  refine ⟨result, pd, hres, ?_, ?_⟩
  · -- world' = postStorage self = storageAt resumeFr self, pointwise via `hstore`
    show (fun key => evmCreateOracle.postStorage result pd self key)
        = (fun key => storageAt resumeFr self key)
    funext key; exact hstore self key
  · -- pushed word = addressWord = createAddrOrZero (by `haddr`, which is `rfl`)
    show evmCreateOracle.addressWord result pd = createAddrOrZero result pd
    exact haddr

/-! The `workedCall` instance of this bridge (`wcV2Oracle`, `wc_call_parity_v2`) is a *leaf
example*, not a headline dependency, so it lives in `LirLean/V2/WorkedCallParity.lean` (which
imports both this module and the offset-coupled `LirLean/WorkedCall.lean`). Keeping it out of
this module is what keeps `LirLean.WorkedCall` off the headline import cone. -/

-- Build-enforced axiom-cleanliness guard: the call realisability bridge depends only on
-- `[propext, Classical.choice, Quot.sound]`.

end Lir.V2
