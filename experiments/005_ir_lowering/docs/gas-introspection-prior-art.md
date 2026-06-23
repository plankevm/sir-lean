# Gas introspection in prior art: verifereum/vyper-hol vs lfglabs-dev/verity

**Status:** study (2026-06-23). Informs `ir-design-v2.md` §3.4 (the gas-introspection
decision: *keep introspection, don't model opcode gas costs*). Findings below are
source-grounded (both repos cloned & read), not README-level.

## The question

Both projects are verified high-level→EVM pipelines. How does each treat **gas**, and
specifically **gas introspection** (a program reading remaining gas — `gasleft()` /
`msg.gas` / the `GAS` opcode — and branching on it)? Counter, abstract value,
oracle/event, or absent? And what is proved?

## Verity (Lean 4: EDSL → CompilationModel → IR → Yul)

| Aspect | Finding |
|---|---|
| Gas in verified layers | **None.** EDSL/IR/CompilationModel carry no gas; `Compiler/IR.lean` has zero `gas` tokens; the `Env` has no gas field. |
| Introspection | **Unsupported.** No `gasleft()`/`gas()` reader in the modeled EDSL. The only gas operand is forwarded-gas to `call`/`staticcall`/`delegatecall`, and it **must be a compile-time constant** (non-constant rejected at macro time). Those low-level calls evaluate to `none` and are excluded from the verified fragment. |
| Representation | Absent. Gas pinned to `0` in the EVMYulLean bridge (`gasAvailable := ⟨0⟩`) and never charged. (A separate *unverified* `gas-report` static tool has per-opcode costs, outside the proof tree.) |
| What's proved | A purely observable equivalence over **four observables: success, return value, observable storage slots, events** — no gas term. |
| Reconciliation | **Sidesteps gas by targeting Yul**; gas deferred to trusted `solc`. Stated outright: *"gas is not modeled"*, *"semantic correctness does not imply gas-safety."* |
| Calls | Return values via a `callOracle` env field (an oracle, not an event). |

## vyper-hol (HOL4: Vyper AST → Venom → EVM via `verifereum`)

| Aspect | Finding |
|---|---|
| Gas at Vyper (high) level | **None as a dynamic quantity.** Only static `gas_price`/`gas_limit` (block limit) in the txn record; no `gas_left`/`gasUsed` counter. Interpreter totality proved by a **syntactic** measure, *not* a fuel/gas clock (README: gas is "invisible at the Vyper source level"). |
| Gas at EVM (low) level | **Full, sound model.** `verifereum` has a decremented `gasUsed` counter, per-opcode `static_gas` + dynamic costs, `OutOfGas`, `get_gas_left = gasLimit − gasUsed`, and the `GAS` opcode. Capstone theorem `decreases_gas` proves monotonicity/boundedness over **every** opcode. |
| Introspection | **Deliberately rejected at the Vyper level.** The AST has `MsgGas`, but the type checker excludes it (`item ≠ MsgGas`), the interpreter has no evaluation rule (falls to `TypeError`), and the test harness skips programs using `msg.gas`. Tracked as future work (**issue #98**). The compiler *can* lower `MsgGas → GAS`, but no well-typed program reaches that path. (`block.gaslimit` is supported, but that's the static limit, not gas-left.) |
| What's proved | (1) Vyper-level **totality independent of gas**; (2) EVM-level gas monotonicity (`decreases_gas`); (3) compiler correctness **modulo a single top-level "enough gas" existential**: `codegen_fn_correct = ∃ gas_needed, ∀ es, gasLimit ≥ gas_needed ⇒ (EVM result corresponds to Venom result)`. |
| Reconciliation | High level is gas-free; all accounting lives in `verifereum`. **`OutOfGas` is the one exception "undischargeable in general" — quarantined to a top-level `gas_sufficient` hypothesis**; every other EVM exception (stack/jumpdest/…) is discharged by construction. External-call gas sufficiency is reused from `verifereum`'s proofs. |

## The common pattern (two independent projects agree)

1. **The high-level / source / IR semantics is gas-free.** Neither threads opcode gas
   costs through high-level reasoning. Gas lives only in the lowest (EVM/bytecode) layer
   — or, for Verity, below the trust boundary entirely.
2. **Gas introspection is NOT supported in either.** Both consciously exclude reading
   gas-left (Verity: constant-only call gas + unmodeled low-level calls; vyper-hol:
   `MsgGas` rejected, issue #98). It is *future work* in both.
3. **Gas is reconciled by a single "enough gas" envelope, not per-operation tracking.**
   vyper-hol's `∃ gas_needed, ∀ gasLimit ≥ gas_needed ⇒ correspondence` is the cleanest
   statement of it; Verity defers the whole concern to `solc`.

## What this means for our C-v2 design

**Strong validation of two v2 choices:**

- **Gas-free functional semantics + observable preservation.** Both projects do exactly
  this. Verity's four observables (success / return / storage / events) are essentially
  our `Observable` (worldDelta + halt result + the event trace). Confirms `Match.M4`
  (gas-equality) should be deleted, not preserved.
- **The "enough gas" envelope.** vyper-hol's `codegen_fn_correct` is, almost verbatim,
  our v2 preservation shape `∃ G₀, ∀ g ≥ G₀, (lowered run reproduces the IR observable)`.
  And their handling — *every machine exception discharged by construction except OOG,
  which is the one top-level hypothesis* — is precisely our "pc/stack/code are internal
  to the `Runs` witness; gas is the single caller-local adequacy side-condition." We
  arrived at the state-of-the-art shape independently.

**Where we are in genuinely new territory:**

- **Keeping gas introspection is novel.** *Neither* project supports it — both list it as
  future work. Our event-model treatment of `Expr.gas` (a `gasRead` event the run
  supplies; introspection **without** opcode-cost accounting) is not copied from either;
  it is our answer to the exact question they both deferred. So there is **no prior-art
  template** to lean on for this part — it is a contribution, and a risk.
- **Why the event model is the right shape for it anyway.** vyper-hol shows the *only*
  place gas is genuinely defined is `gasLimit − gasUsed` at the EVM layer — i.e. it is a
  function of accumulated opcode cost. If (per Eduardo) we refuse to model that cost, then
  the gas value is, from the IR's vantage, *unpredictable* — we can only **observe** it,
  never compute it. That is exactly what an event encodes: the run supplies the value; the
  IR asserts nothing about how it arose. Soundness consequence to state honestly:
  - We **can** prove properties that hold *for all* observed gas values (robustness), and
    properties that carry the *witnessed* value through (the preservation gives us the
    real `GAS` result at each read).
  - We **cannot** predict gas-dependent control flow without modeling costs (e.g. "this
    branch is taken because gas > X" is not derivable) — but that is precisely the
    modeling Eduardo rules out, so it is a non-goal, not a gap. This is the project's
    "earn gas-freedom, don't assume it" honesty constraint, realized structurally.

**Net:** the gas-free + enough-gas-envelope spine of v2 is the validated consensus
design; the gas-introspection-as-event layer is our own extension into what both prior
projects left as future work. Worth flagging in the eventual report as a genuine
contribution rather than a port.
