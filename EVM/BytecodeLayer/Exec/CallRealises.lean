import BytecodeLayer.Exec.Recorder
import BytecodeLayer.Hoare

open BytecodeLayer.Exec

/-!
# CALL and CREATE recorder bridges

Recorded CALL and CREATE entries are projected from their resume data. The bridge
theorems identify those entries with the resumed frame's self-storage lens and the
word pushed by the corresponding opcode.
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
theorem call_reflects_oracle {callFr resumeFr : Frame}
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (∀ addr key, evmCallOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCallOracle.restoredGas result pd = resumeFr.exec.gasAvailable
      ∧ evmCallOracle.successWord result pd = callSuccessFlag result pd := by
  obtain ⟨cp, pending, child, childRes, _hstep, _henters, _hdrive, hresume⟩ := hcall
  subst hresume
  exact ⟨childRes.toCallResult, pending, rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A returning CREATE's oracle projection is the resumed frame's observable effect. -/
theorem create_reflects_oracle {createFr resumeFr : Frame}
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

/-! ## Recorded CALL entry -/

/-- Given a returning external CALL, its recorded entry contains:

* its `.1` (post-call `World`) is the resumed frame's self-storage lens
  (`storageAt resumeFr self` — `call_reflects_oracle`'s `postStorage`
  projection); and
* its `.2` (success word) is the CALL flag (`callSuccessFlag result pd`, via
  `evmCallOracle_successWord_eq_x`).
-/
theorem callRealises_bridge {callFr resumeFr : Frame} (self : AccountAddress)
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (evmCallEntry result pd self).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmCallEntry result pd self).2
          = callSuccessFlag result pd := by
  obtain ⟨result, pd, hres, hstore, _hgas, hsucc⟩ := call_reflects_oracle hcall
  refine ⟨result, pd, hres, ?_, ?_⟩
  · -- world' = postStorage self = storageAt resumeFr self, pointwise via `hstore`
    show (fun key => evmCallOracle.postStorage result pd self key)
        = (fun key => storageAt resumeFr self key)
    funext key; exact hstore self key
  · -- success = successWord = callSuccessFlag (by `hsucc`, which is `rfl`)
    show evmCallOracle.successWord result pd = callSuccessFlag result pd
    exact hsucc

/-! ## The realised create entry

The CREATE twin of `evmCallEntry`/`callRealises_bridge`. A create-stream entry is a
`(World × Word)` — (post-create world, deployed-address-or-0 word). The realised entry reads
from the frame-reference `evmCreateOracle` projections: the post-create `World` is the self account's storage
lens, and the pushed word is `createAddrOrZero` (the CREATE analogue of `callSuccessFlag`).
The bridge uses `create_reflects_oracle` in the same way the CALL bridge uses
`call_reflects_oracle`. -/

/-- Given a returning, successfully resumed CREATE, its recorded entry contains:

* its `.1` (post-create `World`) is the resumed frame's self-storage lens; and
* its `.2` (pushed word) is the deployed-address-or-`0` (`createAddrOrZero result pd`, via
  `evmCreateOracle_addressWord_eq`).
-/
theorem createRealises_bridge {createFr resumeFr : Frame} (self : AccountAddress)
    (hc : CreateReturns createFr resumeFr) :
    ∃ result pd, resumeAfterCreate result pd = .ok resumeFr
      ∧ (evmCreateEntry result pd self).1
          = (fun key => storageAt resumeFr self key)
      ∧ (evmCreateEntry result pd self).2
          = createAddrOrZero result pd := by
  obtain ⟨result, pd, hres, hstore, haddr⟩ := create_reflects_oracle hc
  refine ⟨result, pd, hres, ?_, ?_⟩
  · -- world' = postStorage self = storageAt resumeFr self, pointwise via `hstore`
    show (fun key => evmCreateOracle.postStorage result pd self key)
        = (fun key => storageAt resumeFr self key)
    funext key; exact hstore self key
  · -- pushed word = addressWord = createAddrOrZero (by `haddr`, which is `rfl`)
    show evmCreateOracle.addressWord result pd = createAddrOrZero result pd
    exact haddr

end BytecodeLayer.Exec
