# exp005 / EVMLean backlog

Low-priority cleanups and tech debt surfaced during the conformance work. Not blocking; record-and-defer.

## CREATE address-derivation dead branch (EVMLean `beginCreate`)

`EVMLean/Evm/Semantics/Create.lean:beginCreate` returns `.error` on exactly one
path: `contractAddressBytes … = none` (the address-preimage encoder).
- For CREATE that is `Rlp.encode [sender, nonce]` returning `none`; for CREATE2
  the preimage is `.some`-wrapped (never fails).
- `Rlp.encode` of a 20-byte address + ≤32-byte nonce is **always `some`** — the
  `none` is a totality artifact of the `Option`-typed encoder, so the `.error`
  branch (and, in the drive loop, its account-map fallback) is **dead code**.

**Planned fix (in progress / scheduled):** define a *total* address-preimage
function on top of the `Option`-based `Rlp.encode` — prove
`Rlp.encode` is always `some` for inputs within RLP's length bounds, expose a
non-`Option` `contractAddressBytes`/`beginCreate`, and **remove the dead branch**
entirely (which also removes the corresponding CREATE-fault case from
`drive_accounts_find_mono`). Sequenced after the in-flight 005 charge-fold
workflow to avoid touching the upstream 003 reference + `TieDischarge.lean`
(`drive_accounts_find_mono`) while a 005 workflow is mid-build.

## `StackUnderflow` exception-tag misnomer (EVMYulLean + EVMLean)

A `none`-`Option` lifted into the exception monad (via `←` in a `do`-block, or
the `let some x := … | .error .StackUnderflow` pattern) becomes
`.error .StackUnderflow` — from the generic instance
`MonadLift Option (Except ExecutionException) := none ↦ .StackUnderflow`
(EVMYulLean `EvmYul/EVM/Semantics.lean:136`).

The tag is `StackUnderflow` because the most common source of a `none`-`Option`
in EVM stepping is a stack pop that underflowed — it is a **generic default, not
a semantic claim**. So an RLP/address-preimage failure mislabels itself as
`StackUnderflow`. Harmless today (the branch is unreachable, so the tag never
surfaces). If that branch ever became reachable and the tag mattered, it should
be a dedicated tag (e.g. `.AddressDerivationFailure`). **Not a priority.**
