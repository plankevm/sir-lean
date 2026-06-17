# File-structure plan — topic tree mirroring leanevm (for upstreaming)

*Status: agreed direction, not yet executed. Pending one sign-off (namespaces, §7).*

## Goal & rationale

Drop the `Reasoning/` vs `Proof/` split. It is an artificial bucket that cuts
through single results: the never-out-of-fuel proof alone is smeared across **8
files in both buckets**, and `StepGas` (Reasoning) and `DescentDrops` (Proof) —
both "stepping drops gas" — are maximally far apart.

leanevm itself shows the target convention: it has **no proof bucket**, the few
lemmas it carries live *next to the definitions they are about* (only
`Machine/Stack.lean` and `UInt256.lean` have theorems), and everything is
one-file-per-concept under `Evm/Semantics/`.

So: reorganize our reasoning into a **parallel topic tree mirroring
`Evm/Semantics/`**, in our package, so it upstreams later as a clean drop-in.
A second payoff falls out: organizing by topic separates the **reusable semantic
facts** (gas / system / precompile / dispatch inversions — useful well beyond
fuel) from the **fuel-specific Interpreter argument** (the measure `μ` + drive
induction). The former belong with their leanevm topic; only the latter is
genuinely Interpreter-specific.

Our Hoare-style framework and the example/spec surface have **no leanevm home**;
they stay an experiment-side layer regardless.

## Target tree

```
BytecodeLayer/
  Semantics/                    ← mirrors leanevm Evm/Semantics/ (reusable, upstreamable)
    UInt256.lean      ← toNat_sub_ofNat (UInt64/256 gas-threading arith)   [from DecodeGas]
    GasConstants?/Gas.lean ← StepGasBasics + StepGas (stepFrame_next_lt) + the cost
                          lower bounds (callExtraCost_ge_*, createCost_ge_2, charge_drop_ge)
    Decode.lean       ← DecodeGas's decode_* program facts
    Precompiles.lean  ← Fuel/PrecompileGas (the 10 *_gas_le + beginCall_inr_gas)
    Dispatch.lean     ← Step + Fuel/DispatchSignalShape (onlyNext + stepFrame→systemOp bridges)
    System.lean       ← Call + Begin + DescentDrops's callArm/createArm/systemOp inversions
                          & reduction lemmas + any System-shaped generic facts pulled out
                          of ExternalCall(Gen)
    Maps.lean         ← Maps
    Interpreter/      ← the fuel-specific measure argument (large → own subdir)
      Drive.lean        ← Drive + DriveGen + Fuel
      NeverOutOfFuel.lean ← μ, mu_bound, boundary theorem
      DescentDrops.lean   ← conjunct assembly + descentDrops_holds + messageCall_never_outOfFuel
  Hoare/                        ← OUR additions, no leanevm home
    Hoare.lean · Behaves.lean · Straightline.lean · Sequence.lean
  ExternalCall.lean   ← ExternalCall + ExternalCallGen, MINUS whatever is generic System shape
  Examples/           ← Programs · ProgramExamples · HoareDemo
  Observables.lean · Spec.lean  (top-level boundary + audit surface, unchanged)
```

## Mapping (new ← old)

| New file | Absorbs (current) | Notes |
|---|---|---|
| `Semantics/UInt256.lean` | `toNat_sub_ofNat` (from `Proof/DecodeGas`) | mirrors leanevm `Evm/UInt256.lean` (its arith-lemma home) |
| `Semantics/Gas.lean` | `Reasoning/StepGasBasics`, `Reasoning/StepGas`, + `callExtraCost_ge_*`/`createCost_ge_2`/`create2Cost_ge_2`/`charge_drop_ge` (from `DescentDrops`) | the per-step gas-burn theorem sits with the cost bounds it feeds |
| `Semantics/Decode.lean` | `decode_*` facts (from `Proof/DecodeGas`) | `DecodeGas.lean` dissolves into UInt256 + Decode |
| `Semantics/Precompiles.lean` | `Proof/Fuel/PrecompileGas` | self-contained; cleanest pilot |
| `Semantics/Dispatch.lean` | `Reasoning/Step`, `Proof/Fuel/DispatchSignalShape` | reunites the two "stepFrame/dispatch signal shape" files |
| `Semantics/System.lean` | `Reasoning/Call`, `Reasoning/Begin`, the `callArm`/`createArm`/`systemOp` inversion+reduction lemmas from `DescentDrops`, + generic bits factored out of ExternalCall | the reusable System-op facts |
| `Semantics/Maps.lean` | `Reasoning/Maps` | mirrors `Evm/Maps/` |
| `Semantics/Interpreter/Drive.lean` | `Reasoning/Drive`, `DriveGen`, `Fuel` | drive vocab + fuel monotonicity |
| `Semantics/Interpreter/NeverOutOfFuel.lean` | `Reasoning/NeverOutOfFuel` | `μ`, `mu_bound`, boundary theorem |
| `Semantics/Interpreter/DescentDrops.lean` | the conjunct-assembly + `descentDrops_holds` + `messageCall_never_outOfFuel` tail of `DescentDrops` | the fuel-specific remainder |
| `Hoare/*` | `Reasoning/Hoare`, `Reasoning/Behaves`, `Proof/Straightline`, `Proof/Sequence` | our compositional layer |
| `ExternalCall.lean` | `Proof/ExternalCall`, `Proof/ExternalCallGen` minus generic System shapes | keep external-call-specific rungs here |
| `Examples/*` | `Programs`, `Proof/ProgramExamples`, `Proof/HoareDemo` | demos / worked programs |
| `Observables.lean`, `Spec.lean` | unchanged | top-level surface |

## The two non-trivial factorings

1. **`DescentDrops.lean` splits in two** (decision 1, agreed). Its `systemOp`
   reduction lemmas + `callArm`/`createArm` inversions are reusable System facts
   → `Semantics/System.lean`. Only the five `descentDrops_conj*` + `descentDrops_holds`
   + `messageCall_never_outOfFuel` are fuel-specific → `Interpreter/DescentDrops.lean`.
   This is the literal "reusable facts vs the fuel argument" cut.

2. **`ExternalCall` factoring** (decision 3, agreed). Keep external-call-specific
   results in `ExternalCall.lean`; but anything in `ExternalCall`/`ExternalCallGen`
   that is a *generic System-shaped fact* (same shape as what lands in
   `Semantics/System.lean`) moves into `System.lean` so the connecting/general
   reasoning lives once. Requires reading both files during the System step to
   identify the generic bits.

## Import DAG (bottom-up build order)

```
UInt256 ─► Gas ─► Decode
              └─► Precompiles ─┐
Maps                           ├─► System ─► Interpreter/{Drive ─► NeverOutOfFuel ─► DescentDrops}
            Dispatch ──────────┘                │
                                                ▼
                              Hoare/* ─► ExternalCall ─► Examples/* ─► Spec
```

## Execution plan (each step builds green, no `sorry`)

1. **Pilot — `Precompiles`** (decision: cleanest, self-contained single-file move).
   Move `Proof/Fuel/PrecompileGas.lean` → `Semantics/Precompiles.lean`, fix the one
   importer (`DescentDrops`). Validates the path/namespace shape before bigger cuts.
2. **Leaf topics** — `UInt256`, `Gas`, `Decode`, `Dispatch`, `Maps` (mechanical
   moves; `DecodeGas` dissolves; `Step`+`DispatchSignalShape` merge).
3. **`System`** — the big reusable-facts gather: `Call`, `Begin`, the `DescentDrops`
   inversions, + the generic bits factored out of `ExternalCall(Gen)`.
4. **`Interpreter/`** — `Drive`/`NeverOutOfFuel`/`DescentDrops`-tail.
5. **`Hoare/`, `ExternalCall`, `Examples/`, top-level** — the rest.
6. Drop the now-empty `Reasoning/` and `Proof/` dirs.

## §7 Namespace convention (agreed principle)

Hard constraints (Eduardo): **no `Proof` anywhere** — not in the file tree, the
module path, or the namespace; and **not one single huge flat namespace**.
Namespaces should be topic-meaningful, need **not** be 1-1 with the module, and a
file may introduce **a few sub-namespaces** where it has a natural internal
cluster — decided case-by-case.

So: `Semantics/` stays in the *path* only; the *namespace* is topic-based under
`BytecodeLayer`, not path-mirroring (matches leanevm, whose files live under
`Evm/Semantics/` but declare `namespace Evm` / `Evm.<X>`).

Proposed per-topic scheme (react/adjust freely; finer sub-namespaces added
per-file as natural):

| Module (path) | Namespace |
|---|---|
| `Semantics/UInt256.lean` | `BytecodeLayer.UInt256` |
| `Semantics/Gas.lean` | `BytecodeLayer.Gas` |
| `Semantics/Decode.lean` | `BytecodeLayer.Decode` |
| `Semantics/Precompiles.lean` | `BytecodeLayer.Precompiles` |
| `Semantics/Dispatch.lean` | `BytecodeLayer.Dispatch` |
| `Semantics/System.lean` | `BytecodeLayer.System` (sub e.g. `…System.CallArm` where natural) |
| `Semantics/Maps.lean` | `BytecodeLayer.Maps` |
| `Semantics/Interpreter/*.lean` | `BytecodeLayer.Interpreter` (shared by the 3 files) |
| `Hoare/*.lean` | `BytecodeLayer.Hoare` (sub e.g. `…Hoare.Runs` where natural) |
| `ExternalCall.lean` | `BytecodeLayer.ExternalCall` |
| `Examples/*.lean` | `BytecodeLayer.Examples` |
| `Observables.lean`, `Spec.lean` | `BytecodeLayer` (clean exported audit-surface names) |

Net effect: drop `.Proof` from the 11 Proof files; the current bare-`BytecodeLayer`
Reasoning files gain a topic sub-namespace. Cross-topic references use `open`.
