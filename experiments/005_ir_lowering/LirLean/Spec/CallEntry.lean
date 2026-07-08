import LirLean.Spec.Semantics
import LirLean.Frame.Call
import LirLean.Frame.Create

/-!
# LirLean spec surface — the realised oracle-stream entries

The **statement vocabulary** for the recorder's realised call/create streams: the single
`(World × Word)` entry a recorded bytecode CALL/CREATE contributes to the consumed
`CallStream`/`CreateStream`. Hoisted out of `LirLean/V2/CallRealises.lean` (which keeps only the
realisability *bridge proofs* `callRealises_bridge`/`createRealises_bridge`) so the trusted
surface — in particular `Spec/Recorder.lean`'s `realisedCall`/`realisedCreate` — can name what
it realises without importing the proof module. Both defs are sorry-free.

These are bytecode-coupled (they read v1's `evmCallOracle`/`evmCreateOracle`, `CallResult`,
`PendingCall`), so they live here rather than in the frame-free `Spec/Semantics.lean`, exactly
as the deleted `Oracle.lean` was the gas-side bridge's home.
-/

namespace Lir.V2

open Evm
open Lir
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare

/-- **The realised v2 call-stream entry.** The `(World × Word)` a recorded bytecode CALL
`(result, pd)` at self address `self` contributes to the consumed call stream: the post-call
self-storage lens (`evmCallOracle.postStorage result pd self`) paired with the success word
(`evmCallOracle.successWord result pd`). Positional — the entry is fixed by the bytecode's
`resumeAfterCall`, indexed by the record, NOT a function of the call's IR-visible inputs. -/
def evmV2CallEntry (result : CallResult) (pd : PendingCall) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCallOracle.postStorage result pd self key)
  , evmCallOracle.successWord result pd )

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

end Lir.V2
