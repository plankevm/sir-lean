# LirLean v2 — observable-level lowering preservation (gas/pc-free IR, calls as events)

> **SUPERSEDED (2026-07-03):** superseded by `ir-design-v3.md` (the v1/v2 convergence); plan of record is `target-architecture-2026-07-02.md` + `execution-plan-2026-07-02.md`. The `V2/Mono.lean` two-read monotonicity milestone validated below was deleted in Phase 2 with the rest of the gas-law apparatus (Mono/Oracle/HonestGasTie) — see `gas-decision.md`.

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

### 3.4 `Expr.gas` / gas introspection — KEPT, as an observed-value event

**Decision (Eduardo, 2026-06-23): keep gas introspection, but do NOT model opcode gas
costs.** The IR may *read* gas and branch on it; it must never *account* gas (no
per-opcode charge, no `matCost`, no decremented counter).

This is the **same event mechanism as calls** (§3.3) applied to gas: `Expr.gas`
evaluates to a value drawn from a **gas-read event** the run supplies. The IR consumes
the event and asserts nothing about how the value arose — exactly "introspection without
accounting." So v2's event trace is not just calls; it is the unified sequence of
*things the IR observes but does not model*:

```text
Event := | call (callee : Address) (calldata : Calldata)
                 (world' : World) (success : Word) (returndata : Returndata)
         | gasRead (observed : Word)          -- the value a GAS opcode reports
Trace := List Event
```

`Expr.gas` consumes the next `gasRead`; `Stmt.call` consumes the next `call`. In the
preservation proof each `gasRead` is witnessed by the lowered `GAS` opcode's actual
result (just as each `call` is witnessed by `messageCall`). The project's honesty
constraint (theorems true *under* gas introspection, gas-freedom earned not assumed) is
satisfied structurally: a gas-dependent branch is evaluated against the **actual observed
gas**, so the preserved observable is correct for the real machine value — and a theorem
"observable independent of the `gasRead` value" becomes a *provable IR property*, never an
assumption.

#### The ONE law on the gas oracle: monotonicity (Eduardo, 2026-06-23)

The `gasRead` values are not arbitrary. The IR semantics gives the gas opcode **exactly
one** property to reason with: the sequence of `gasRead` values, in program order, is
**monotone non-increasing** (the EVM `GAS` opcode returns gas *remaining*; the dual
"gas-used non-decreasing" is the same law). The IR may assume *only* this — never any
per-opcode cost. This is the precise middle point between an arbitrary oracle (buys only
"robust over all values") and cost-modeling (rejected):

- **Sound & cheap to discharge.** The real machine satisfies it (cf. vyper-hol's
  `decreases_gas`; on our side it is the same gas-descent fact the never-OutOfFuel fuel
  induction already rides). The lowering obligation "the realized `GAS` sequence is a
  valid monotone instance" is *already-owned machinery*, not new accounting.
- **Holds across calls.** Monotonicity survives an external call between two reads: a
  returning call nets a *debit* on the caller (`before − cost − child_used`); the 63/64
  refund only means the caller wasn't charged for the child's unused gas, it does not
  raise the caller's gas. SSTORE/SELFDESTRUCT gas refunds are end-of-transaction, so they
  never perturb a mid-run reading. **Scope: a single message-call execution** (LirLean's
  scope); revisit only if the IR ever models a callee's own gas.
- **Buys** "sticky" gas-guard reasoning (`if gasleft() < RESERVE then stop` — once gas
  drops below a threshold it stays below). **Does not buy** loop-termination-by-gas or
  predictive branch direction (those need *strict* decrease + a positive per-iteration
  cost lower bound = cost modeling, the non-goal).

**✅ VALIDATED (2026-06-23, `LirLean/V2/Mono.lean`, axiom-clean).** The two-read milestone
proved `lower_preserves_obs_mono` on a "sticky gas guard" (`g1:=gas; …; g2:=gas;
branch (g1<g2) BAD GOOD` — monotonicity forces the "did gas go up" guard to `0`, pinning the
observable). The IR touches the law exactly once to decide the guard; the bytecode side
**discharges** monotonicity (not assumes it) — and it fell out of the exact `subCharges` gas
accounting as a one-line `omega`, confirming "already-owned machinery, no new gas theory."
Refinements this surfaced (now part of the design):
- **The law is `toNat` non-increasing, and only the `later ≤ earlier` direction (+ its
  negation) is determinable.** A *strict*-decrease guard (`g2 < g1`) is NOT determinable
  (the equality case) — that is exactly the loop-termination non-goal, re-confirmed.
- **Determinable guards lower through `GT`, not `LT`.** Two `GAS` reads leave the stack as
  `g2 :: g1`; deciding `g1 < g2` needs `g1` on top, i.e. a `SWAP` or (free, same `binOp`
  path) a `GT`. The lowering uses `GT`. State this operand-order fact for any guard whose
  determinacy needs a specific operand on top.
- **`gasReads` is the gasRead *subsequence*** (it ignores `call`/other events) — the right
  semantics once events interleave; "holds across calls" is precisely a `call` between two
  reads.
- **✅ The general `Runs`-level gas-monotonicity lemma is now PROVED, hypothesis-free,
  axiom-clean** (`BytecodeLayer/Hoare/GasMonotone.lean`, on the `Spec.lean` audit surface):
  `Runs.gasAvailable_le : Runs fr last → last.gasAvailable.toNat ≤ fr.gasAvailable.toNat`,
  with the `.call` net-debit discharged as `CallReturns.gas_le` (no side-condition — a
  `Runs.call` node already bundles the returning child). Supporting:
  `drive_gasRemaining_le_totalGas` (the one genuinely-new fact — exp003 had only the
  *termination* measure, never a gas-conservation bound) + `StepsTo.gas_le`. **§3.4's "holds
  across calls" is now a real proof, not a remark.** The general v2 theorem cites
  `Runs.gasAvailable_le` for any two gas reads on its witness `Runs`, no concrete-program
  assumption, no per-opcode cost — confirming "already-owned machinery, no new gas theory"
  at the general level (every per-transition bound was an existing lemma).

> Note: this means v2 has **no gas counter at all** — neither for accounting (rejected)
> nor for introspection (it's an event). The only surviving gas fact is the caller-local
> adequacy envelope `G₀ ≤ g` of §4, which is about *never running out*, not about *values*.

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
1. **Call-free prototype (arith + storage + gas-read branch). ✅ DONE (2026-06-23,
   `exp005-ir`, axiom-clean, build-enforced).** `LirLean/V2/Machine.lean` (gas-free
   `World`/`IRState`/`evalExpr`/`IRRun`, `Event.gasRead`, `Observable`) +
   `LirLean/V2/Preserve.lean` (`Lir.V2.lower_preserves_obs`: `∃ G₀, ∀ g ≥ G₀`, IR run and
   bytecode agree on the observable, the `GAS` opcode realising the `gasRead`; statement is
   pc-free and gas-equality-free). **Verdict: the shape works** — gas introspection cost
   ZERO gas machinery in the IR; the event-realisability clause fell out as a one-line
   hypothesis (CompCert discipline confirmed); `World`-as-storage-lens reused v1's
   `selfStorage`/`sstoreFrame_storage_self` verbatim. v1 `wc_preserves` untouched & green.
   Documented prototype cuts (mechanical follow-up, not design risk): witness bytecode is
   hand-written PUSH1 not `lower protoIR` (avoids the PUSH32 decode blowup); `returned w` ↦
   success with empty RETURN window; STOP fall-through arm not instantiated; `RunFrom`
   determinism not yet proved (headline states IR-and-bytecode-agree directly).
1b. **Two-read monotonicity. ✅ DONE (`LirLean/V2/Mono.lean`, axiom-clean).** Validated the
   §3.4 monotone-oracle law on a sticky-gas-guard example; bytecode discharges monotonicity.
   *In progress next:* the general `Runs`-level gas-monotonicity-across-`.call` lemma (the
   prerequisite that makes "holds across calls" a real proof, decision-free).
2. **Calls as events.** Add transcript threading; re-derive `workedCall`'s preservation in
   the v2 shape, reusing the v1 `Runs` assembly as the witness for each `CallEvent`.
   *(Blocked on the §7.5 returndata-model decision — held for Eduardo.)*
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
4. ~~`Expr.gas`.~~ **DECIDED (2026-06-23):** keep gas introspection, modeled as a
   `gasRead` event — no opcode-cost accounting, no gas counter (§3.4). The prototype
   (§6 step 1) should include a gas-read + gas-dependent `branch` to exercise the event
   model cheaply, before external-call events.
5. **Revert/failure as observable + the returned word.** *(Sharpened by the prototype —
   needs Eduardo before the `call`-event step, since calls carry returndata.)*
   (a) `IRHalt.returned w` currently carries a word, but the C3 lowering RETURNs an **empty
   window**, so the word is not observed — drop the word from `returned` (match the lowering)
   or make the lowering RETURN it so `output` reflects it? (b) When revert enters, align
   `IRHalt`/`Observable.result` with the EVM `Outcome` (`completed/reverted/exception`) so
   the result is faithful, not a bare success flag. *Default for the first `call`-event cut:
   value-free, empty calldata/returndata (mirrors v1 `workedCall`), revert deferred.*
6. **`evalExpr` gas-trace threading.** The prototype's single `obs` arg works only because
   recompute-on-use ⇒ ≤1 `gasRead` per materialised expression. State that invariant
   explicitly, or thread a sub-trace once an expression can force >1 gas read.
7. **Trace realisability in the theorem.** The headline holds only for the trace whose
   `gasRead` matches the machine `GAS` value. State this as the explicit *realisability
   side-condition* of the events (the `call` analogue: `world'/success/returndata = what
   `messageCall` produces`) so the discipline ports cleanly to the `call` step. Add the
   `RunFrom` determinism lemma to recover the cleaner `∀ O, IRRun … O → …` shape.
8. **Convergence with Phase-2.** `CallEvent`/the call-as-event boundary is a candidate
   piece of the shared `EVMSemantics` interface — both flat (A) and nested (B) realise the
   same `messageCall`-induced events. Worth aligning the `World`/`CallEvent` signatures
   with B4's IR surface so Phase-2a is mechanical.
