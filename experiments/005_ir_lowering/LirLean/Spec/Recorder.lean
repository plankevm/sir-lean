import LirLean.Spec.Semantics
import BytecodeLayer.Exec.Recorder

namespace Lir

export BytecodeLayer.Exec.Recorder
  (evmV2CallEntry evmV2CreateEntry CallRecord CreateRecord RunLog isGasOp isSloadOp
   isCreate2Op isCallOp softFailCallRecord callSuccessFlag_softFailCallRecord
   softFailCreateRecord createAddrOrZero_softFailCreateRecord sloadWarmthOf recordCall
   recordCreate driveLog runWithLog callsCodeOk realisedGas realisedSload callStreamOf realisedCall
   createStreamOf realisedCreate resultStorageAt observe observe_result)

namespace RunLog

abbrev clean := BytecodeLayer.Exec.Recorder.RunLog.clean
abbrev cleanb := BytecodeLayer.Exec.Recorder.RunLog.cleanb

end RunLog

end Lir
