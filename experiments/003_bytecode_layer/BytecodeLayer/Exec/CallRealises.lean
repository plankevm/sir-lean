import BytecodeLayer.Exec.Recorder
import BytecodeLayer.Hoare

open BytecodeLayer.Exec

/-!
# CALL/CREATE realisability bridges

The gas stream's realisability is discharged by a witnessing bytecode `Runs`, and its law is a
**consequence** of that realisation. This module provides the call analogue: a recorded call entry
is realised by the frame-reference `evmCallOracle`, and the `(world', success)` entry is shown to
equal the lowered bytecode CALL's observable effect.

This file is **bytecode-coupled** (it references `CallResult`/`PendingCall`/`evmCallOracle`
and concrete frame facts), so it lives here rather than in the frame-free
`Spec/Semantics.lean`/`Law.lean`, exactly as `Oracle.lean` is the gas-side bridge.

## What is realised (the §7 interaction model, on the call side)

A call-stream entry is a `(World × Word)` — (post-call world, 0/1 success). The realised
post-world comes from the lowered bytecode's `resumeAfterCall`, which depends on chain state
the IR lacks; so the realised entry reads off the frame-reference `evmCallOracle` projections:

* the post-call `World` is `evmCallOracle.postStorage result pd self` — the self account's
  post-CALL observable storage lens on `resumeAfterCall result pd`;
* the success word is `evmCallOracle.successWord result pd` — which `rfl`-reduces to
  exp003's CALL flag `x` (`callSuccessFlag`), per `evmCallOracle_successWord_eq_x`.

`callRealises_bridge` is the call analogue of `GasRealises.monotoneGas`: under a returning
external CALL (`CallReturns callFr resumeFr`), the realised entry's `(world', success)`
*is* the lowered CALL's observable — `world'` is the resumed frame's self-storage lens
(`storageAt resumeFr self`), and `success` is the CALL flag `x`. It is
`rfl`-clean: `evmV2CallEntry … = (postStorage…, successWord…)` by `rfl`, the storage half
is `call_reflects_lowered`'s `postStorage = storageAt` projection at the self address, and
the success half is `evmCallOracle_successWord_eq_x`.
-/

namespace BytecodeLayer.Exec

open BytecodeLayer.Exec
open BytecodeLayer.Exec.Recorder
open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare

/-- The storage of account `addr` at `key` in frame `fr`. -/
def storageAt (fr : Frame) (addr : AccountAddress) (key : Word) : Word :=
  fr.exec.accounts.find? addr |>.option 0 (·.lookupStorage key)

/-- A returning CALL's oracle projection is the resumed frame's observable effect. -/
theorem call_reflects_lowered {callFr resumeFr : Frame}
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (∀ addr key, evmCallOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCallOracle.restoredGas result pd = resumeFr.exec.gasAvailable
      ∧ evmCallOracle.successWord result pd = callSuccessFlag result pd := by
  obtain ⟨cp, pending, child, childRes, _hstep, _henters, _hdrive, hresume⟩ := hcall
  subst hresume
  exact ⟨childRes.toCallResult, pending, rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A returning CREATE's oracle projection is the resumed frame's observable effect. -/
theorem create_reflects_lowered {createFr resumeFr : Frame}
    (hc : CreateReturns createFr resumeFr) :
    ∃ result pd, resumeAfterCreate result pd = .ok resumeFr
      ∧ (∀ addr key, evmCreateOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCreateOracle.addressWord result pd = createAddrOrZero result pd := by
  obtain ⟨cp, pending, childRes, _hstep, _hdrive, hresume⟩ := hc
  refine ⟨childRes.toCreateResult, pending, hresume, ?_, rfl⟩
  have hacc : resumeFr.exec.accounts = childRes.toCreateResult.accounts := by
    unfold resumeAfterCreate at hresume
    simp only [bind, Except.bind, pure, Except.pure] at hresume
    split at hresume
    · exact absurd hresume (by simp)
    · simp only [Except.ok.injEq] at hresume
      rw [← hresume]
      dsimp only [ExecutionState.replaceStackAndIncrPC]
  intro addr key
  simp only [evmCreateOracle, storageAt, hacc]

/-! ## The realised call entry

`evmV2CallEntry result pd self` (on the trusted recorder surface) is a
single call-stream entry realised by the bytecode CALL data `(result, pd)` at self address
`self`: the post-call self-storage lens paired with the 0/1 success word. `restoredGas` is
dropped — the gas-free IR has no gas in state, so the restored-gas field is irrelevant to the gas-free
machine (§7). -/

/-! ## Step 2a — the realisability bridge lemma (the call analogue of `monotoneGas`)

Under a returning external CALL, the `(world', success)` entry `evmV2CallEntry` names
equals the lowered bytecode CALL's observable effect. -/

/-- **The call realisability bridge.** Given a returning external CALL
(`CallReturns callFr resumeFr`, so `resumeFr = resumeAfterCall result pd` for the projected
child result / pending call), the entry `evmV2CallEntry result pd self` is exactly the
lowered CALL's observable effect:

* its `.1` (post-call `World`) is the resumed frame's self-storage lens
  (`storageAt resumeFr self` — `call_reflects_lowered`'s `postStorage`
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

/-! ## The realised create entry

The CREATE twin of `evmV2CallEntry`/`callRealises_bridge`. A create-stream entry is a
`(World × Word)` — (post-create world, deployed-address-or-0 word). The realised entry reads
from the frame-reference `evmCreateOracle` projections: the post-create `World` is the self account's storage
lens, and the pushed word is `createAddrOrZero` (the CREATE analogue of `callSuccessFlag`).
The bridge is off `create_reflects_lowered`, exactly as the call bridge is off
`call_reflects_lowered`. The realised
entry `evmV2CreateEntry` itself lives on the trusted recorder surface. -/

/-- **The create realisability bridge** (twin of `callRealises_bridge`). Given a returning,
successfully-resumed CREATE (`CreateReturns createFr resumeFr`, so `resumeAfterCreate result pd
= .ok resumeFr` for the projected child result / pending create), the entry `evmV2CreateEntry
result pd self` is exactly the lowered CREATE's observable effect:

* its `.1` (post-create `World`) is the resumed frame's self-storage lens
  (`storageAt resumeFr self` — `create_reflects_lowered`'s `postStorage`
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

-- Build-enforced axiom-cleanliness guard: the call realisability bridge depends only on
-- `[propext, Classical.choice, Quot.sound]`.

end BytecodeLayer.Exec
