# Route B — calls compose into the block spine (memory value channel)

> **P9 status note (2026-07-08).** This plan is historical. The intermediate `Expr.slot`
> encoding and the legacy fuel/materialisation APIs (`materialiseExpr`, `materialise`,
> `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`, `NoSlotSource`) have been deleted;
> current spill/readback policy is represented by `Loc` and `matCache`.

> **Naming note (uniform-spill refactor, 2026-06-28):** the constructor this document
> calls `Expr.callResult` was renamed to **`Expr.slot`** (a generic spill-load) in Phase A
> of `docs/uniform-spill-alloc-plan.md` — the call-result use is now one client of a uniform
> memory-slot mechanism. Read every `Expr.callResult` / `.callResult` *expression* below as
> `Expr.slot` / `.slot`. (The unrelated `IRState.callResult` success-word field is unchanged.)

**Goal.** Make `lower_conforms` genuinely general over **all** `Stmt.call`, deleting
`CallFree`. The call-free theorem (`lower_conforms_acyclic_cfg`, commit `227cf6a`) is the
honest base; this work removes the "call-free" distortion.

**Decision (Eduardo, 2026-06-26): full memory value channel now.** The CALL success flag
is spilled to EVM memory and re-read on use. This is the only mechanism that makes
`resultTmp = some t` calls *compose* (`stack = []` at the boundary) **and** *correct*
(a later use materialises the true flag, not the `PUSH32 0` stub). Fire-and-forget
(`resultTmp = none`) is the degenerate POP case of the same scheme.

The memory channel is **bytecode-side only**: the IR (`Lir.IRState`) is **not** extended.
Memory is unobservable, so it never appears in the storage-conformance statement —
exactly as gas/calls are "observed but not modelled". `MemAgree` (a new `Corr` clause)
ties the bytecode's memory at result slots to the IR's bound locals, the same way
`StorageAgree` ties frame storage to `st.world`.

Build: `lake build` in `experiments/005_ir_lowering`. Baseline green = 1153 jobs,
axioms `[propext, Classical.choice, Quot.sound]`. **Always green, no `sorry`, no new
axioms** after every phase. Worktree `evm-semantics-wt/ir-lowering`, branch
`ir-convergence`; `main` untouched.

---

## Concrete definitions (the contract every phase implements against)

### Opcode bytes (`Lowering.lean`, `namespace Byte`)
```
def pop    : UInt8 := 0x50
def mload  : UInt8 := 0x51
def mstore : UInt8 := 0x52
```
All three are already implemented in the exp003 EVM layer:
- decode/serialize: `003_bytecode_layer/EVMLean/Evm/Instr.lean:66-69,276-279,515-517`
- dispatch/step: `…/Semantics/Smsf.lean:11-32` (`.POP`/`.MLOAD`/`.MSTORE`)
- memory model: `…/Machine/MachineState.lean:25` (`memory : ByteArray`),
  `…/Machine/MachineStateOps.lean:43-55` (`mload`/`mstore`)

### Result-tmp memory slots
```
/-- Private memory slot for a call-result tmp. Unique per tmp id; SSA single-binding
    ⇒ write-once. Base offset keeps slots clear of the (zero-size) CALL windows. -/
def slotOf (t : Tmp) : Nat := t.id * 32
```
(Final base TBD in Phase 0 — `t.id * 32` is fine because CALL uses zero-size memory
windows, so even slot 0 is untouched by the call itself.)

### Rematerialisation of a call result — `Expr.callResult`
Add a constructor to `Expr` (IR.lean) used **only** by `defsOf`/`materialiseExpr` as a
lowering marker; it is never produced by a source program and never evaluated by the IR.
```
| callResult (slot : Nat)   -- "this tmp lives in memory at `slot`; MLOAD it"
```
- `evalExpr`: `| .callResult _ => none` (unreachable in well-formed runs — result tmps
  are read via `.tmp t → st.locals t`, never via `.callResult`).
- `materialiseExpr defs f (.callResult slot) = emitImm (UInt256.ofNat slot) ++ [Byte.mload]`
  (PUSH32 slot, then MLOAD).
- Every other function/proof casing on `Expr` (`MatDec`, `chargeOf`, inductions in
  `MaterialiseRuns`/`DefsSound`/etc.) gets a `.callResult` arm. Most are trivial.

### `defsOf` extension (`Lowering.lean`)
The program-global scan additionally registers each call result:
```
prog.blocks.toList.flatMap (fun b => b.stmts.filterMap (fun
  | .assign t e               => some (t, e)
  | .call ⟨_, _, some t⟩      => some (t, .callResult (slotOf t))
  | _                         => none))
```

### `emitStmt` for `.call` (`Lowering.lean`) — Route B
```
| .call cs =>
    emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
    ++ materialise defs fuel cs.callee
    ++ materialise defs fuel cs.gasFwd
    ++ [Byte.call]
    ++ (match cs.resultTmp with
        | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]   -- PUSH slot; MSTORE
        | none   => [Byte.pop])                                           -- discard flag
```
Stack discipline: after CALL, top = success flag.
- `some t`: PUSH slot ⇒ `slot :: flag :: rest`; MSTORE pops `(addr=slot, val=flag)`, writes
  `mem[slot] = flag`, leaves `rest`. Boundary stack restored (M5). `mem[slot]` now holds the flag.
- `none`: POP discards the flag, leaves `rest`. Boundary stack restored (M5).

### `MemAgree` (new `Corr` clause, `SimStmt.lean`)
```
/-- Bytecode memory realises the IR's call-result locals. For every call-result tmp `t`
    (one registered as `.callResult slot` in `defsOf`) that is currently bound in
    `st.locals`, the frame's memory at `slot` holds that value. -/
def MemAgree (prog : Program) (st : Lir.IRState) (fr : Frame) : Prop :=
  ∀ t slot v, defsOf prog t = some (.callResult slot) → st.locals t = some v →
    (fr.exec.toMachineState.mload (UInt256.ofNat slot)).1 = v
```
- **Established** by the call arm (the MSTORE just wrote `mem[slot] = flag`).
- **Consumed** by `materialise_runs` `.callResult` arm (MLOAD slot = bound local).
- **Preserved** by assign/sstore (don't write memory) and across CALL (zero-size return
  window ⇒ caller memory untouched — needs a `resumeAfterCall`-preserves-caller-memory lemma).

---

## Phase DAG (always-green between phases)

- **P0 Scaffolding.** Bytes, `Expr.callResult`, `slotOf`, extend `evalExpr`/`materialiseExpr`/
  `emitStmt`/`defsOf`/`chargeOf`/`MatDec` + all non-exhaustive-match arms. Call-free theorems
  stay green (changes additive; `emitStmt .call` length change only affects programs with calls).
  *Risk:* adding an `Expr` constructor breaks every `match`/`cases` on `Expr` — broad but mechanical.

- **P1 EVM primitive lemmas (`Match.lean`).** `sim_pop`, `sim_mstore`, `sim_mload`
  (templates: `sim_sstore`/`sim_sload`, `Match.lean:197-229`) + memory algebra:
  `mload_after_mstore` (mload slot (mstore slot v) = v), `mstore` preserves other slots,
  `resumeAfterCall` preserves caller memory at a slot. Parallel with P2.

- **P2 Decode anchors.** POP/MSTORE/MLOAD decode over `lower prog`; `MatDec` `.callResult`
  arm; `chargeOf` `.callResult` cost (Gverylow + mem-expansion, mirror SLOAD). Parallel with P1.

- **P3 `MemAgree` into `Corr`.** Add the clause; thread (preserved) through `sim_assign`/
  `sim_sstore_stmt`. Memory expansion gas envelopes folded into the realisability ties.

- **P4 `materialise_runs` `.callResult` arm (`MaterialiseRuns.lean`).** In the `.tmp t` arm,
  when `defsOf t = some (.callResult slot)`, route to the MLOAD-readback path: MLOAD slot
  yields `st.locals t = w` via `MemAgree` (NOT via the `evalExpr` recursion — `.callResult`
  has no `evalExpr` value; this branch is the documented exception to the evalExpr-threading).

- **P5 Call-arm upgrade (`SimStmt.lean`).** `sim_call_stmt`: `CorrCall` → full `Corr`.
  Close M5 (POP/MSTORE consumes the flag) and M1 (pc via the new emit length), establish
  `MemAgree` for the new result tmp, preserve it for existing slots across the CALL.

- **P6 Delete `CallFree`.** `sim_stmts` cons-induction handles `.call`; strip `CallFree`
  from `SimStmts.lean`, `SimTerm.lean`, `LowerConforms.lean` (incl. the `hcf` hypotheses
  and `simStmtStep_callfree`/`simTermStep_callfree`). Headline `lower_conforms` no longer
  carries a call-free side condition.

- **P7 Worked example + round-trips + headline + docs.** Update `WorkedCall.lean`/`Decode.lean`
  bytecode + decode `by decide`/`#eval` checks for the new POP/MSTORE tail; restate the general
  `lower_conforms`; update `docs/ir-design-v3.md` §7/§5, this plan, and memory `[[ir-convergence-v3]]`.
  Sweep cruft (the `lower_conforms_plan.md` call rows, the M1/M5 "documented gap" prose in
  `SimStmt.lean`, the `unused variable o` at `LowerConforms.lean:1082`).

## Progress / decisions log (2026-06-26)

- **P0 done** (dirty tree): `Expr.callResult`, `slotOf := t.id*32`, lowering (`emitStmt .call`
  tail = POP / PUSH slot;MSTORE; `defsOf` registers call results; `materialiseExpr .callResult
  = PUSH32 slot ++ MLOAD`), all `Expr`-match arms (vacuous via `evalExpr (.callResult _)=none`).
- **Green restored (1155 jobs, axiom-clean)**: `sim_pop`/`popFrame` in `Match.lean`;
  `subCharges_snoc/_append` moved to new `LirLean/Charges.lean` (headline **decoupled** from
  `WorkedCall` via `MaterialiseGas`; `CallRealises` still needs worked-example defs, left as-is);
  `WorkedCall` fixed for the POP at offset 300.
- **`zeroes` de-opaqued** (`003_bytecode_layer/EVMLean/Evm/FFI/ffi.lean`): `opaque` →
  `@[extern] def … := ⟨Array.replicate n.toNat 0⟩`. Removes the only opaque on the memory
  read-back path; keeps the pristine axiom list. `zeroes_size`/`zeroes_get` now provable theorems.
- **MemAlgebra.lean** (Agent X): `resumeAfterCall_mload` (CALL preserves caller memory at a slot,
  given zero-size in/out windows — both hold, lowering pushes 0 windows) PROVED axiom-clean.
  Read-back (lemma 1) + disjointness (lemma 2) were walled by `zeroes` opaque → now unblocked;
  finish them post-rebuild. Also still need the pure decoder round-trip
  `fromByteArrayBigEndian (UInt256.toByteArray v) = v.toNat` (no FFI, Nat-recursion, laborious).

### Architecture refinement — `MemAgree` is a supplied-observation tie
The general simulation spine (P3–P6) carries `MemAgree` / "MLOAD slot = bound flag" as a
**realisability side-condition**, threaded exactly like `SloadRealises`/`GasRealises` (§7
supplied-observation form). No raw `ByteArray` reasoning in the spine. The read-back algebra
(MemAlgebra.lean) is needed only to **discharge** that tie concretely (worked example /
`evmCallOracle` instance) — same status as the existing gas/SLOAD/call ties.

### Newly-found real bug — `ret t` lowering underflows RETURN — FIXED
`emitTerm (.ret t) = materialise t ++ [RETURN]` pushed ONE word, but EVM `RETURN` pops TWO
(offset, size). Pre-Route-B the worked program was silently feeding RETURN's `size` from the
**residual CALL success flag**; removing that flag (correct Route B + POP) exposed the underflow.
The headline conformance only projects `Observable.world` (return word NOT checked), so the
*theorem* was never distorted — but the lowering couldn't run to halt.

**FIXED** (minimal, reuses the existing empty-window RETURN brick): `emitTerm (.ret t) =
materialise t ++ emitImm 0 ++ emitImm 0 ++ [RETURN]` — the two `PUSH32 0` push the
`offset = 0` / `size = 0` window, so the stack is `0 :: 0 :: vw :: rest` exactly as
`Match.halt_ret`/`stepFrame_return_empty` consume. `RETURN(0,0)` returns empty and HALTS
(zero-size window ⇒ no gas hypothesis); `world` is untouched (the residual `vw` is discarded
with the frame). `sim_term_halt_ret` runs the two pushes itself (`sim_imm`), discharging the
former supplied empty-window hypothesis; `WorkedCall`'s `wc_preserves` is now hypothesis-free
(the terminal RETURN halt is reached concretely, +66 bytes re-threaded through the worked
program's pcs/gas). Build green at 1155 jobs, axioms `[propext, Classical.choice, Quot.sound]`.
(A faithful scalar-return variant — `MSTORE` the word then `RETURN 32` — remains possible later,
but the world channel never observes the return value, so the empty window is sound.)

### Design lock — call-results are "memory-recomputable" (the gas analogy, with a twist)
`materialise_runs`'s `.tmp t` arm splits bound tmps into recomputable (DefsSound) vs
`NonRecomputable` (gas). Call-results are a THIRD kind:
- **Excluded from `DefsSound`** (like gas: `evalExpr (.callResult _) = none`), so the
  recompute path makes no claim about them.
- **But value-STABLE**: re-emitting `PUSH slot; MLOAD` returns the SAME flag every time
  (memory doesn't change), unlike `GAS` which returns a fresh value. ⇒ call-results may be
  **multi-used** (gas may not) — though single-use is enough to drop `CallFree`; multi-use
  is a free bonus of the stable channel, needs no `WellFormed` change.
- Tied by a new realisability condition **`MemRealises`** carrying, for each bound
  call-result tmp, **coverage + value**: `∀ t slot v, defsOf t = some (.callResult slot) →
  st.locals t = some v → (ofNat slot).toNat + 32 ≤ fr…memory.size ∧ (ofNat slot).toNat <
  fr…activeWords.toNat*32 ∧ (fr…mload (ofNat slot)).1 = v`. The memory analogue of
  `GasRealises`/`SloadRealises`, threaded through `materialise_runs` with a `.transport`.
  **Why coverage:** `MLOAD` is NOT a pure read — it grows `activeWords` (memory expansion),
  which can retroactively un-zero an *uncovered* slot's read. Bound call-result slots are
  always covered (the P5 MSTORE that binds them grows `activeWords` over the slot and
  allocates the bytes), so coverage is honest and travels with the value.
- **`MatRuns` memory clause** (the form that actually transports): **memory BYTES unchanged
  + `activeWords` nondecreasing** — NOT "mload-value preserved" (false across MLOAD). Both
  hold for every arm (imm/tmp/add/lt/sload/gas preserve both; MLOAD preserves bytes, grows
  activeWords). For a covered slot, bytes-equal ⇒ size-equal ⇒ in-bounds preserved;
  activeWords-nondecreasing ⇒ active preserved; covered+bytes-equal ⇒ value preserved. So
  `MemRealises.transport` follows from the two-fact `MatRuns.memory` clause.
- Handled **inline in the `.tmp t` arm**: when `defs t = some (.callResult slot)`, run
  `PUSH slot; MLOAD` (sim_imm + sim_mload), value `= w` via `MemRealises`. The `.callResult`
  arm of `materialise_runs` STAYS vacuous (never reached on a valid `evalExpr` run).
- `materialise_runs`'s `wellScoped` premise is RELAXED to admit call-result tmps:
  `bound t → (¬NonRecomputable t ∨ isCallResult t) ∧ defsOf t ≠ none`.
- `MatRuns` gains a **memory clause** (mload-value at slots preserved by materialise sub-runs)
  so `MemRealises.transport` threads. `Corr` gains a `memAgree : MemRealises …` field;
  assign/sstore preserve it (they don't touch memory); entry is vacuous (empty locals).

### Revised sequencing
P1a (pop) + green-restore + zeroes + MemAlgebra crux: **DONE / in-progress**. Next:
finish MemAlgebra read-back → `sim_mstore`/`sim_mload` (P1b) → P2 decode anchors → P3 MemAgree
→ P4 materialise `.callResult` → P5 call-arm `CorrCall`→`Corr` → P6 drop CallFree →
P7 worked example + `ret` fix + headline + docs.

## P6 shape (the CallFree deletion)
`SimStmtStep` carries `¬ s.isCall`; the induction (`sim_stmts_drop`) gates on `CallFree`.
Spine B made `sim_call_stmt` deliver full `Corr` + `stack=[]` — exactly `SimStmtStep`'s
shape. So P6:
- **Mechanical**: drop `¬ s.isCall` from `SimStmtStep`; delete `CallFree`/`callFree_*` and
  every `hcf` from `sim_stmts*`, `sim_cfg`, `lower_conforms*`; remove the call-exclusion
  `absurd` in `simStmtStep_callfree`'s dispatch.
- **The call discharge** (`simStmtStep_call`, mirroring `simStmtStep_sstore`): build the
  arg-push run (5×PUSH0 + materialise callee/gasFwd → `callFr` pins) and feed `sim_call_stmt`.
  Its remaining supplied premises become per-block ties: the realised **`CallReturns`** +
  resume pins (the §7 CALL tie — replaces the *restriction* "no calls" with a *realisability
  condition* "the call behaves as the realised trace says", like gas/sload ties); `hslots` +
  slot-addressability become new `WellFormedLowered` fields (call-result tmps register
  `slotOf` — true because `.callResult` is lowering-only, never in a source `assign`; add a
  `WellFormed` condition forbidding `.callResult` in source assigns); pre-call `MemRealises`
  from `Corr.memAgree`. Net: `lower_conforms` loses `hcf` and gains a call realisability tie
  — GENERAL over calls.

## Known risk items
1. **`resumeAfterCall` preserves caller memory** at our slots (zero-size out window). Must
   exist or be proved in exp003 territory — first thing P1 confirms.
2. **Memory-expansion gas.** MLOAD/MSTORE charge `Gverylow + M-expansion`; the gas
   realisability ties (§7 supplied observations) must absorb these. Mirror the SLOAD charge.
3. **WellFormed.** A result tmp must not also be `assign`-bound (SSA single-binding) — add to
   `WellFormed`/`DefsSound` scoping so `defsOf`'s call-result entry is unambiguous.
