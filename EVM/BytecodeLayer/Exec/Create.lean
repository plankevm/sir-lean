import BytecodeLayer.Exec.Observable
import Evm
import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Dispatch

/-!
# Abstract CREATE effects

`CreateOracle` exposes post-create storage and the deployed-address-or-zero word.
`evmCreateOracle` is the concrete instance obtained from the data consumed by
`resumeAfterCreate`.
-/

namespace BytecodeLayer.Exec

open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## Oracle interface -/

/-- An abstract view of a contract creation's effect. Its projections match the
observable parts of `resumeAfterCreate`:

* `postStorage result pd addr key` — the storage of account `addr` at `key` in the
  resumed world, through the observable `find?/lookupStorage` lens; for the EVM
  oracle this is `result.accounts`'s lens;
* `addressWord result pd` — the deployed contract address (or `0` on soft-failure) the
  CREATE pushes.

`evmCreateOracle` instantiates both fields directly from `CreateResult` and
`PendingCreate`. -/
structure CreateOracle where
  /-- Post-create storage of `addr` at `key`, through the observable lens. -/
  postStorage : CreateResult → PendingCreate → AccountAddress → Word → Word
  /-- The deployed-address-or-`0` word the CREATE pushes. -/
  addressWord : CreateResult → PendingCreate → Word

/-- The value pushed after CREATE: `0` on soft failure, otherwise the deployed
address. -/
def createAddrOrZero (result : CreateResult) (pd : PendingCreate) : Word :=
  let balance :=
    pd.callerAccounts.find? pd.frame.exec.executionEnv.address |>.option 0 (·.balance)
  if result.success = false ∨ pd.frame.exec.executionEnv.depth = 1024
      ∨ pd.value > balance ∨ pd.initCodeSize > 49152
  then 0 else .ofNat result.address

/-! ## Concrete EVM instance

The resume can return `.error` at the 63/64 retention guard, so the oracle projects
the exact values it writes from `CreateResult` and `PendingCreate`:

* `postStorage` reads `result.accounts` (the map `resumeAfterCreate` writes into
  `exec.accounts`) through the observable `find?/lookupStorage` lens;
* `addressWord` is `createAddrOrZero` — the word `resumeAfterCreate` pushes
  on a successful resume.
-/

/-- The concrete CREATE effect projected from the resume data. -/
def evmCreateOracle : CreateOracle where
  postStorage := fun result _pd addr key =>
    result.accounts.find? addr |>.option 0 (·.lookupStorage key)
  addressWord := createAddrOrZero

/-- The concrete oracle's address word is `createAddrOrZero`. -/
theorem evmCreateOracle_addressWord_eq (result : CreateResult) (pd : PendingCreate) :
    evmCreateOracle.addressWord result pd = createAddrOrZero result pd := rfl

end BytecodeLayer.Exec
