# LirLean v2 — observable-level lowering preservation (gas/pc-free IR, calls as events)

**Status:** PLANNING (2026-06-23). Supersedes the `ir-design.md` §3/§6 semantics &
preservation strategy. The v1 `wc_preserves` (fully hypothesis-free, axiom-clean) stays
as the reference "old boundary" until v2 reaches parity.

**Driver (Eduardo, 2026-06-23):** the IR semantics should *not* be gas-aware or
call-aware. Calls are "whatever the bytecode does" — reflexively the same, **not an
oracle**. Lowering-preservation should be stated **mostly at the observable level** and
must **not** prove preservation of gas, program counter, or other low-level machine
state.

---

## 1. What couples v1 (the rot we are removing)

The v1 *datatypes* (`LirLean/IR.lean`) are mostly fine; the coupling is in the semantics
(`SmallStep.lean`) and the `Match` invariant (`Match.lean`):

- `IRState.gas : UInt64` exists **only** so `Match` clause `M4` can assert
  `IR.gas = fr.exec.gasAvailable`. The IR gas charges (`gVerylow`, `gBase`, `matCost`,
  …) are literally "the same constants the lowered opcodes charge." → **the IR semantics
  is defined by the bytecode's gas accounting.**
- `Match` carries `M1` (pc = `pcOf prog L pc`) and `M4` (gas equality) — the two
  low-level invariants we explicitly do not want preserved.
- `CallSpec.gasFwd : Tmp` bakes the 63/64 gas-forwarding (a pure lowering detail) into
  the IR call type.
- No abstract `IRStep` relation was ever built — v1's simulation was assembled
  concretely against `workedCall`, so the IR has no standalone semantics to point IR-level
  reasoning at.

## 2. Principle (prior art)

- **Verity** (lfglabs-dev/verity, a verified compiler in Lean 4): lowers
  EDSL→CompilationModel→IR→**Yul** and proves *statement-level equivalence*. Decisive
  move: the verified lowering stops at a **structured target with no explicit pc and no
  explicit gas**, so pc/gas preservation is never a theorem.
- **Dafny-EVM**: explicitly *separates functional opcode semantics from gas accounting* —
  functional correctness and gas are different proofs.
- **CompCert** (the closest mature analog to Eduardo's instinct): external calls are
  **events in a trace**; compiler correctness is a forward simulation that **preserves the
  trace**. The compiler asserts *nothing* about what an external call does — only that both
  sides emit the same event. This is "the call is reflexively whatever the bytecode does",
  done without an oracle.

**Synthesis = the v2 design:** (a) pick the *observable* boundary (storage delta + halt
result), gas-free and pc-free; (b) functional preservation and gas-adequacy are separate
theorems; (c) external calls are **events/holes threaded in from the run**, not modeled.

## 3. The reformed IR semantics

### 3.1 Abstract, observable machine state — no gas, no pc

```text
World   := observable EVM state the IR can affect/observe
           (C1 scope: per-account storage map; later: balances, code, …)
IRState := { locals : Tmp → Option Word, world : World }
```

`World` is **IR-native**: it never mentions `Frame`, `pc`, or `gasAvailable`. An
abstraction lens relates it to an EVM `Frame`'s observable projection (the existing
`selfStorage`/`storageAt` lenses in `Match.lean` are the seed). The IR datatypes already
only mention `Word`/`Tmp`/`Address`-as-`Word`, so they stay decoupled.

### 3.2 Pure constructs get real observable semantics

`add`, `lt`, `sload`, `sstore`, `assign`, and the `jump`/`branch`/`ret`/`stop`
terminators are defined operationally on `(locals, world)` with **no gas charge and no
pc** — `evalExpr` keeps its current arithmetic (`UInt256.add/lt`, storage lens) minus the
`gas` counter. These are the constructs that earn observable-preservation lemmas.

### 3.3 External calls = events, threaded from the run (the "bail-out")

Drop `CallSpec.gasFwd`. A call carries only what the IR genuinely chooses: `callee`,
`calldata` (C1: empty), and where to bind `success`/returndata.

The IR execution is threaded with a **call transcript**

```text
CallEvent := { callee : Address, calldata : Calldata,
               world' : World, success : Word, returndata : Returndata }
CallTranscript := List CallEvent
```

The `call` step **consumes the next `CallEvent`** — it does *not* compute it. The IR
asserts nothing about `world'/success/returndata`; they are inputs. This is the precise
sense of "the semantics of an external call is whatever the bytecode does": in the
preservation proof each event is *witnessed by the bytecode's actual `messageCall`*
(= one of Track A's `Runs.call` nodes), so the call step matches **by construction**.

> No oracle (nothing axiomatized about calls), no refinement obligation, no gas math at
> the call. A callee that legitimately runs out of gas is just a `CallEvent` with
> `success = 0` — absorbed into "whatever the bytecode does."

### 3.4 `Expr.gas` / gas introspection — DEFERRED (open, see §7)

Gas introspection is the one place the IR reads a low-level quantity. Options recorded
for later; v2's first cut likely **drops `Expr.gas`** and revisits gas-introspection as a
follow-up (Eduardo de-emphasized gas-awareness). If kept: model `gas` as another *event*
(an observed value the run supplies), with the honesty obligation stated as an IR theorem
("output robust across the observed value"), never as a tracked counter.

## 4. The preservation theorem (shape)

```text
Observable := { worldDelta : World,        -- final storage state (observable lens)
                result     : IRHalt }      -- stop / return w  (revert: see §7)

-- IR big-step: program prog, start world w₀, consuming transcript T, yields O
IRRun : Program → World → CallTranscript → Observable → Prop

theorem lower_preserves_obs (prog : Program) (w₀ : World) :
  ∀ {T O}, IRRun prog w₀ T O →
    ∃ G₀, ∀ g, G₀ ≤ g →
      -- the lowered bytecode at gas g halts with the SAME observable O,
      -- making external calls that realise the SAME transcript T
      LoweredRunHasObs (lower prog) w₀ g T O
```

- **Call steps** match because it is the **same `T`** on both sides (CompCert-style
  trace preservation; each `CallEvent` ↔ a `Runs.call` node, Track A's engine).
- **Pure steps** match by the per-construct observable simulation lemmas (the v1
  `runs_add/lt/sload/sstore/...` rules, restated to re-establish *world*, not gas/pc).
- **pc (`M1`) and gas-equality (`M4`) are GONE from the statement.** They survive only
  *inside* the existence-of-`Runs` witness (`LoweredRunHasObs` unfolds to a
  `Runs fr₀ last` whose internal bookkeeping still tracks pc/stack — but the IR never
  sees it).
- **Gas** appears once, as the adequacy envelope `G₀ ≤ g`, covering only the **caller's
  own opcodes** between calls/halt. Same flavour as Track A/B never-OutOfFuel; a separate
  lemma from functional correctness.

`Match`'s five clauses split into two tiers:

| v1 clause | v2 home |
|---|---|
| M1 pc | internal to the `Runs` witness — **not** IR-facing |
| M2 code | internal (decode/layout) |
| M3 storage | **observable** — promoted to `World` agreement (IR-facing) |
| M4 gas-equality | **deleted** — replaced by the `G₀ ≤ g` adequacy side-condition |
| M5 stack-empty | internal to the `Runs` witness |

## 5. What is reused (cost control)

The expensive v1 bytecode-side machinery becomes the **internal witness**, unchanged in
spirit: `decode_lower`, the `Layout`/`pcOf` offset arithmetic, the per-opcode `Runs`
rules, the never-OutOfFuel discharge, and the concrete child-`CallReturns`. What changes
is the **IR-facing surface** (gas-free `IRRun`, `World`, observable `Obs`) and the
**theorem statement** (observables + transcript, not `Match`). The honest-but-large child
work folds into "this `Runs.call` node realises this `CallEvent`."

## 6. Migration plan (de-risk before porting `workedCall`)

0. **Lens + types.** Define `World`, `Observable`, `CallEvent`, and the
   `World ↔ Frame`-observable abstraction lens (seed: `selfStorage`/`storageAt`).
1. **Pure fragment prototype.** Gas-free `IRRun` for the no-call fragment; prove
   `lower_preserves_obs` on the **arithmetic+storage example** (the `ArithStorageExample`
   analog). This validates the gas-free machine + observable theorem shape end-to-end at
   low cost. ← **the de-risking prototype.**
2. **Calls as events.** Add transcript threading; re-derive `workedCall`'s preservation in
   the v2 shape, reusing the v1 `Runs` assembly as the witness for each `CallEvent`.
3. **Branch + multi-call.** `Term.branch` lowering as an observable theorem;
   `wc_preserves_twoCall` analog falls out of transcript concatenation (Track A
   `Runs.call` composition).
4. **(Optional) gas introspection.** Revisit `Expr.gas` per §7.

Keep v1 `wc_preserves` green as reference until step 2 reaches parity.

## 7. Open decisions (need Eduardo)

1. **`World` decoupling depth.** EVM-native (`evmCall` ≈ `rfl`, but couples the `World`
   type to EVM state) vs observable-native record + lens (more decoupled, needs round-trip
   lemmas). *Lean: observable-native + a thin lens.*
2. **Direction of the simulation.** "IR says O ⇒ bytecode (enough gas) does O" (above) vs
   the converse "every bytecode behaviour is an IR behaviour." For a *compiler* the former
   is the useful guarantee; confirm.
3. **calldata / returndata / value.** C1 was value-free & calldata-free. Keep that for v2
   first cut, or generalise the `CallEvent` now?
4. **`Expr.gas`.** Drop for v2 and split gas-introspection to a follow-up experiment, or
   keep via the event model (§3.4)?
5. **Revert/failure as observable.** Does the IR model `REVERT` (an `Observable.result`
   case) or only `stop`/`return`?
6. **Convergence with Phase-2.** `CallEvent`/the call-as-event boundary is a candidate
   piece of the shared `EVMSemantics` interface — both flat (A) and nested (B) realise the
   same `messageCall`-induced events. Worth aligning the `World`/`CallEvent` signatures
   with B4's IR surface so Phase-2a is mechanical.
