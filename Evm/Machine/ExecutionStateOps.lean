import Mathlib.Data.List.Intervals

import Evm.UInt256
import Evm.Machine.ExecutionState
import Evm.State.AccountOps
import Evm.StateOps
import Evm.Machine.MachineStateOps
import Evm.Machine.MachineState
import Evm.Operations

namespace Evm



namespace ExecutionState

section Instructions

def incrPC (I : ExecutionState) (pcΔ : ℕ := 1) : ExecutionState :=
  { I with pc := I.pc + .ofNat pcΔ }

def replaceStackAndIncrPC (state : ExecutionState) (stack : Stack UInt256) (pcΔ : UInt8 := 1) : ExecutionState :=
  { state with stack := stack, pc := state.pc + pcΔ.toUInt32 }

end Instructions

section Memory

def calldatacopy (self : ExecutionState) (mstart datastart size : UInt256) : ExecutionState :=
  { self with
    memory := self.executionEnv.calldata.write datastart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      MachineState.M self.activeWords mstart.toUInt64 size.toUInt64
  }

def codeCopy (self : ExecutionState) (mstart cstart size : UInt256) : ExecutionState :=
  { self with
    memory := self.executionEnv.code.write cstart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      MachineState.M self.activeWords mstart.toUInt64 size.toUInt64
  }

def extCodeCopy' (self : ExecutionState) (acc mstart cstart size : UInt256) : ExecutionState :=
  let mstartNat := mstart.toNat
  let cstart := cstart.toNat
  let sizeNat := size.toNat
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.lookupAccount addr |>.option .empty (·.code)
  { self with
    memory := b.write cstart self.memory mstartNat sizeNat
    substate := .addAccessedAccount self.substate addr
    activeWords :=
      MachineState.M self.activeWords mstart.toUInt64 size.toUInt64
  }

end Memory

def logOp (offset size : UInt256) (topics : Array UInt256) (self : ExecutionState) : ExecutionState :=
  let address := self.executionEnv.address
  let mem := self.memory.readWithPadding offset.toNat size.toNat
  { self with
    substate.logSeries := self.substate.logSeries.push ⟨address, topics, mem⟩
    activeWords := MachineState.M self.activeWords offset.toUInt64 size.toUInt64
  }

def liftMState {m} [Monad m] (f : Evm.State → m (Evm.State)) : ExecutionState → m ExecutionState :=
  λ s ↦ do pure { s with toState := ← f s.toState }

instance {m} [Monad m] : CoeFun (Evm.State → m (Evm.State)) (λ _ ↦ ExecutionState → m ExecutionState) := ⟨liftMState⟩

def liftState (f : Evm.State → Evm.State) : ExecutionState → ExecutionState :=
  liftMState (m := Id) f

instance : CoeFun (Evm.State → Evm.State) (λ _ ↦ ExecutionState → ExecutionState) := ⟨liftState⟩

def initialiseAccount (addr : AccountAddress) : ExecutionState → ExecutionState :=
  Evm.State.initialiseAccount addr

def updateAccount (addr : AccountAddress) (act : Account) : ExecutionState → ExecutionState :=
  Evm.State.updateAccount addr act

end ExecutionState



end Evm
