import BytecodeLayer.Exec.CallRealises
import BytecodeLayer.Exec.Recorder

namespace BytecodeLayer.Exec

open Evm
open BytecodeLayer.Exec.Recorder

/-- A successful call-frame halt exposes the frame's committed storage. -/
theorem resultStorageAt_endFrame_success (fr : Frame) (hexec : Evm.ExecutionState)
    (output : ByteArray) (self : AccountAddress) (key : Word) (cp : Evm.Checkpoint)
    (hkind : fr.kind = .call cp)
    (hacc_eq : hexec.accounts = fr.exec.accounts)
    (hne : ¬ (fr.exec.accounts == ∅) = true) :
    resultStorageAt (endFrame fr (.success hexec output)) self key
      = storageAt fr self key := by
  show ((endFrame fr (.success hexec output)).toCallResult.accounts.find? self
          |>.option 0 (·.lookupStorage key))
        = (fr.exec.accounts.find? self |>.option 0 (·.lookupStorage key))
  have hacc : (endFrame fr (.success hexec output)).toCallResult.accounts
      = fr.exec.accounts := by
    unfold Evm.endFrame
    rw [hkind]
    show (Evm.endCall cp (.success hexec output)).accounts = fr.exec.accounts
    have hne' : (hexec.accounts == ∅) = false := by
      cases h : (hexec.accounts == ∅) with
      | false => rfl
      | true => rw [hacc_eq] at h; exact absurd h hne
    show (if (hexec.accounts == ∅) = true then cp.accounts else hexec.accounts)
      = fr.exec.accounts
    rw [hne', if_neg (by simp), hacc_eq]
  rw [hacc]

/-- A successful call-frame halt exposes the halt's output unchanged. -/
theorem resultOutput_endFrame_success (fr : Frame) (hexec : Evm.ExecutionState)
    (output : ByteArray) (cp : Evm.Checkpoint) (hkind : fr.kind = .call cp) :
    (endFrame fr (.success hexec output)).toCallResult.output = output := by
  unfold Evm.endFrame
  rw [hkind]
  rfl

end BytecodeLayer.Exec
