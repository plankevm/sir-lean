import Batteries.Data.RBMap

import Evm.Machine.MachineState

import Evm.Crypto.Keccak256

namespace Evm

def writeBytes
  (source : ByteArray)
  (sourceAddr : ℕ)
  (self : MachineState)
  (destAddr len : ℕ)
 : MachineState :=
  { self with
      memory := source.write sourceAddr self.memory destAddr len
  }

namespace MachineState

open Batteries (RBMap)

def M (s f l : UInt64) : UInt64 :=
  match l with
  | 0 => s
  | l =>
    max s ((f + l + 31) / 32)

def writeWord (self : MachineState) (addr val : UInt256) : MachineState :=
  let numOctets := 32
  let source : ByteArray := val.toByteArray
  writeBytes source 0 self addr.toNat numOctets

def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr.toNat ≥ self.activeWords.toNat * 32 then 0 else
    let bytes := self.memory.readWithPadding addr.toNat 32
    let val := fromByteArrayBigEndian bytes
    .ofNat val

def msize (self : MachineState) : UInt256 :=
  UInt256.ofUInt64 self.activeWords * 32

def mload (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  let val := self.lookupMemory spos
  let self :=
    { self with
      activeWords := MachineState.M self.activeWords spos.toUInt64 32
    }
  (val, self)

def mstore (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := self.writeWord spos sval
  { self with
    activeWords := MachineState.M self.activeWords spos.toUInt64 32
  }

def mstore8 (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := writeBytes ⟨#[UInt8.ofNat sval.toNat]⟩ 0 self spos.toNat 1
  { self with
    activeWords := MachineState.M self.activeWords spos.toUInt64 1
  }

def mcopy (self : MachineState) (writeStart readStart s : UInt256) : MachineState :=
  let self := writeBytes self.memory readStart.toNat self writeStart.toNat s.toNat
  { self with
    activeWords :=
      MachineState.M self.activeWords (max writeStart.toUInt64 readStart.toUInt64) s.toUInt64
  }

def returndatacopy (self : MachineState) (mstart rstart size : UInt256) : MachineState :=
  let self := writeBytes self.returnData rstart.toNat self mstart.toNat size.toNat
  { self with
    activeWords :=
      MachineState.M self.activeWords mstart.toUInt64 size.toUInt64
  }

def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  let bytes := self.memory.readWithPadding mstart.toNat s.toNat
  let kec := ffi.KEC bytes
  let newMachineState :=
    { self with activeWords := M self.activeWords mstart.toUInt64 s.toUInt64 }
  (.ofNat (fromByteArrayBigEndian kec), newMachineState)

end MachineState

end Evm
