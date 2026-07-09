import LirLean.Spec.Semantics
import LirLean.Frame.Call
import LirLean.Frame.Create

namespace Lir.V2

open Evm
open Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare

def evmV2CallEntry (result : CallResult) (pd : PendingCall) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCallOracle.postStorage result pd self key)
  , evmCallOracle.successWord result pd )

def evmV2CreateEntry (result : CreateResult) (pd : PendingCreate) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCreateOracle.postStorage result pd self key)
  , evmCreateOracle.addressWord result pd )

end Lir.V2
