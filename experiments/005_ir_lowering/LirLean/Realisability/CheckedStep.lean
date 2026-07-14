import LirLean.Realisability.SegmentedEval
import BytecodeLayer.Exec.CheckedStep

namespace Lir

export BytecodeLayer.Exec.Recorder
  (two_pow_32_le_usize_size zeroes_cast zeroes_cast_sub zeroes_ofNat32_sub
   readWithoutPadding_size_le readWithPaddingK readWithPadding_eq_K writeK write_eq_K
   writeBytesK writeBytes_eq_K toByteArrayK toByteArray_eq_K writeWordK writeWord_eq_K
   lookupMemoryK lookupMemory_eq_K mloadK mload_eq_K mstoreK mstore_eq_K mstoreChk
   mstoreChk_sound smsfOpChk smsfOpChk_sound callArmChk callArmChk_sound systemOpChk
   systemOpChk_sound dispatchChk dispatchChk_sound stepFrameChk stepFrameChk_sound
   nextLogOnSig nextLog_inl nextLogChk nextLogChk_sound stepsLogChk stepsLogChk_sound
   nextCCOnSig nextCC_eq_onSig nextCCChk nextCCChk_sound stepsCCChk stepsCCChk_sound)

end Lir
