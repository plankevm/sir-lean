import Evm

/-!
# `beginCall` entry characterization for code calls (reusable brick)

`beginCall` (leanevm) decides what running a `CallParams` produces *before* code
execution: a precompile result, or — for a `.Code` call — the initial `Frame` the
driver descends into. This file pins that initial frame as named definitions
(`codeEnv`, `codeAccounts`, `codeFrame`) and proves `beginCall` equals it
(`beginCall_code`) for any `.Code` call.

It is the **single bridge** that unfolds `beginCall`: capstone proofs obtain the
initial frame through `beginCall_code` (composed with `messageCall_eq_drive`)
instead of unfolding `beginCall` themselves. Low-level by design (it mentions
`Frame`, `ExecutionEnv`); an internal brick, never an exported statement.
-/

namespace BytecodeLayer
open Evm

/-- The account map after `beginCall`'s value credit (to the recipient) and debit
(from the caller) — mirrors `beginCall`'s `accountsAfterTransfer`. -/
def codeAccounts (params : CallParams) : AccountMap :=
  let accountsAfterCredit :=
    match params.accounts.find? params.recipient with
      | none =>
        if params.value != (0 : UInt256) then
          params.accounts.insert params.recipient { (default : Account) with balance := params.value }
        else
          params.accounts
      | some acc =>
        params.accounts.insert params.recipient { acc with balance := acc.balance + params.value }
  match accountsAfterCredit.find? params.caller with
    | none => accountsAfterCredit
    | some acc =>
      accountsAfterCredit.insert params.caller { acc with balance := acc.balance - params.value }

/-- The execution env `beginCall` builds for a `.Code code` call. -/
def codeEnv (params : CallParams) (code : ByteArray) : ExecutionEnv :=
  { address := params.recipient
    origin    := params.origin
    gasPrice  := params.gasPrice.toNat
    calldata  := params.calldata
    caller    := params.caller
    value  := params.apparentValue
    depth     := params.depth
    canModifyState      := params.canModifyState
    code      := code
    blockHeader := params.blockHeader
    blobVersionedHashes := params.blobVersionedHashes
    chainId   := params.chainId }

/-- The initial frame `beginCall` produces for a `.Code code` call. -/
def codeFrame (params : CallParams) (code : ByteArray) : Frame :=
  { kind := .call ⟨params.createdAccounts, params.accounts, params.substate⟩
    validJumps := validJumpDests code 0
    exec :=
      { (default : ExecutionState) with
          accounts := codeAccounts params
          originalAccounts := params.originalAccounts
          executionEnv := codeEnv params code
          substate := params.substate
          createdAccounts := params.createdAccounts
          gasAvailable := params.gas
          blocks := params.blocks
          genesisBlockHeader := params.genesisBlockHeader } }

/-- **`beginCall` on a code call.** For any `params` whose code source is
`.Code code`, `beginCall` returns `.inl (codeFrame params code)` — the driver
descends into the initial frame. The one place `beginCall` is unfolded. -/
theorem beginCall_code (params : CallParams) (code : ByteArray)
    (hc : params.codeSource = .Code code) :
    beginCall params = .inl (codeFrame params code) := by
  unfold beginCall codeFrame codeEnv codeAccounts
  rw [hc]
  rfl

end BytecodeLayer
