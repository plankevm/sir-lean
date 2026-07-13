import LirLean.Spec.IR
import Evm
import BytecodeLayer.Hoare
import BytecodeLayer.Semantics.Dispatch

/-!
# LirLean — the abstract create oracle (CREATE/CREATE2)

The CREATE analogue of `Frame/Call.lean`. The IR's CREATE accounting is
**create-agnostic**: the IR does **not** model contract creation internals. It defers
the create's *effect* — the post-storage world (through the self lens) and the
deployed-address-or-`0` word the opcode pushes — to an abstract `CreateOracle`. The IR
reasons for **all** oracles; lowering instantiates the oracle to **exactly what the
lowered bytecode's CREATE does** (exp003's `resumeAfterCreate`, projected through the
observable lens), so the IR's create effect is *reflexively equal* to the lowered
bytecode's.

This mirrors `Frame/Call.lean` field-for-field. Two altitude differences from CALL, both
handled here:

* `resumeAfterCreate` (`EVM/Evm/Semantics/Create.lean:153`) returns
  `Except _ Frame` (it can throw on the 63/64 retention guard), whereas
  `resumeAfterCall` is total. So the oracle's projections read off the `CreateResult` /
  `PendingCreate` **data** that `resumeAfterCreate` writes (`accounts := result.accounts`,
  the `pushedValue` `let`-block) — keeping the oracle **total** while staying
  projection-faithful to what the resume does.
* CALL pushes a 0/1 success flag; CREATE pushes the deployed **address or 0**
  (`createAddrOrZero`, exactly `resumeAfterCreate`'s `pushedValue`).

The empty-init-code first cut (`offset = length = 0`, value `0`) collapses the
init-code failure surface (no init-code OOG/REVERT, EIP-170, EIP-3541, deposit);
richer init code is future work (`docs/ir-design.md`).
-/

namespace Lir.Frame

open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## The abstract create oracle

The oracle's input is the data exp003's `resumeAfterCreate` reads — the child's
`CreateResult` and the suspended `PendingCreate` — so the EVM instantiation is **by
construction** the lowered create's projection (each field reduces by `rfl` to the
corresponding `resumeAfterCreate` component). The IR is parametric over *all*
`CreateOracle`s; lowering picks `evmCreateOracle`. -/

/-- An abstract **create oracle**: the IR's view of a contract creation's *effect*,
projected from the data exp003's `resumeAfterCreate` reads (the child's `CreateResult`
and the suspended `PendingCreate`). Two projections, matching the two things
`resumeAfterCreate` does the IR cares about:

* `postStorage result pd addr key` — the storage of account `addr` at `key` in the
  resumed world, through the observable `find?/lookupStorage` lens; for the EVM
  oracle this is `result.accounts`'s lens;
* `addressWord result pd` — the deployed contract address (or `0` on soft-failure) the
  CREATE pushes.

The field types are chosen so `evmCreateOracle` instantiates each by *projection*
(definitional) of the bytecode resume. The gas-restored field is dropped — the gas-free
IR has no gas in state (cf. `Frame/Call.lean`'s `restoredGas`). -/
structure CreateOracle where
  /-- Post-create storage of `addr` at `key`, through the observable lens. -/
  postStorage : CreateResult → PendingCreate → AccountAddress → Word → Word
  /-- The deployed-address-or-`0` word the CREATE pushes. -/
  addressWord : CreateResult → PendingCreate → Word

/-- exp003's CREATE pushed value (verbatim from `resumeAfterCreate`'s `pushedValue`
`let`-block, `Create.lean:159-162`): `0` on soft-failure (child failed / call-depth
limit / insufficient balance / init-code over the EIP-3860 cap), else the deployed
address `.ofNat result.address`. Named so the oracle's `addressWord` can be pinned to
it (`evmCreateOracle_addressWord_eq`). -/
def createAddrOrZero (result : CreateResult) (pd : PendingCreate) : Word :=
  let balance :=
    pd.callerAccounts.find? pd.frame.exec.executionEnv.address |>.option 0 (·.balance)
  if result.success = false ∨ pd.frame.exec.executionEnv.depth = 1024
      ∨ pd.value > balance ∨ pd.initCodeSize > 49152
  then 0 else .ofNat result.address

/-! ## The EVM instantiation — by-construction the lowered CREATE

`evmCreateOracle` defines each field as the corresponding projection of exp003's
`resumeAfterCreate result pd` data (`EVM/Evm/Semantics/Create.lean`):

* `postStorage` reads `result.accounts` (the map `resumeAfterCreate` writes into
  `exec.accounts`, `Create.lean:168`) through the observable
  `find?/lookupStorage` lens;
* `addressWord` is `createAddrOrZero` — the word `resumeAfterCreate` pushes
  (`pushedValue`, `Create.lean:159-162,174`).

By stating each as a *projection of the resume data*, the reflexivity headline (the
CREATE analogue of `call_reflects_lowered`) is `rfl`-clean. -/

/-- **The concrete EVM contract-creation effect** — one instantiation of `CreateOracle`,
each field a projection of exp003's `resumeAfterCreate` data. By construction the lowered
bytecode's CREATE effect. -/
def evmCreateOracle : CreateOracle where
  postStorage := fun result _pd addr key =>
    result.accounts.find? addr |>.option 0 (·.lookupStorage key)
  addressWord := createAddrOrZero

/-- **The EVM oracle's address word is exactly exp003's CREATE pushed value.** Pins the
"address word matches `pushedValue`" claim of the reflexivity headline to the concrete
formula, by `rfl`. -/
theorem evmCreateOracle_addressWord_eq (result : CreateResult) (pd : PendingCreate) :
    evmCreateOracle.addressWord result pd = createAddrOrZero result pd := rfl

end Lir.Frame
