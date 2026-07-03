import LirLean.LowerDecode
import LirLean.CleanHaltExtract

/-!
# LirLean — `sim_cfg` + `lower_conforms` (Layer **F** of the general `lower_conforms` grind)

The capstone of the **world-channel** `lower_conforms` grind (general over calls). It threads the
per-block bricks of Layers C–E into a whole-CFG simulation (`sim_cfg`, by induction on
`V2.RunFrom`) and then ties that to the instrumented recording interpreter `runWithLog`
(`lower_conforms`).

## The two structured per-block hypotheses

The induction is on `V2.RunFrom`, the IR CFG driver. Each constructor runs a block's
statement list and then its terminator. The statement-list simulation is Layer D
(`sim_stmts_block`); the terminator simulation is Layer E (`sim_term_halt_*` /
`sim_term_edge_*`). Rather than re-thread Layers D and E's *enormous* per-block structured
hypothesis bundles (decode coverage at every static cursor, gas/stack envelopes, the
SSTORE/SLOAD/GAS realisability ties, the jump-destination round-trips) through the CFG
induction — they are per-block and per-intermediate-frame, so they cannot be stated once up
front — we abstract them into **two** structured hypotheses at exactly the altitude of the
Layer-D / Layer-E conclusions:

* `SimStmtStep prog sloadChg obs o L b` (Layer D, `SimStmts.lean`) — the per-statement
  simulation, already the unit Layer D consumes.
* `SimTermStep prog sloadChg obs o self L b` (Layer E, here) — the per-terminator
  simulation: from `Corr` at the terminator cursor and the block's `RunStmts`-post IR state,
  either **halt** with a frame whose `observe` *world* matches the IR halt's world (the `stop`
  / `ret` arms, E1), or **run to the taken successor's entry** re-establishing `Corr` at
  `(succ, 0)` (the `jump` / `branch` arms, E2).

`SimTermStep` is the exact union of E1's and E2's conclusions, dispatched on `b.term` and the
IR run's terminator facts. Discharging it for a concrete program is a mechanical case split on
`b.term` feeding `sim_term_halt_stop` / `sim_term_halt_ret` / `sim_term_edge_jump` /
`sim_term_edge_branch` their structured-hypothesis bundles (the A1–A3 decode anchors, the E3
jump-validity, the gas envelopes) — exactly as `SimStmtStep` is discharged for the statement
arms. This is the **realisability contract**: `sim_cfg` runs the IR under the oracles the
lowered bytecode realises, and carries the per-block realisability as `SimStmtStep` /
`SimTermStep` (the `docs/ir-design-v3.md` §7 supplied-observation model).

## Scope — all statements, world channel

Layer D now ranges over **all** statements: Route B's `sim_call_stmt` consumes the lowered
CALL's success flag (`MSTORE` to the result slot, or `POP`), re-establishing `stack = []`, so a
`Stmt.call` no longer breaks the induction — `lower_conforms` carries no call-free side
condition. The channel is the **world** (storage) component: `observe`'s `result`
is the value-free `.stopped` boundary (the RETURN value channel is the tracked deferral,
`Spec/Recorder.lean` `observe` doc). `sim_cfg`'s conclusion asserts the world component of
`observe self (endFrame last halt)`.

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports the Layer-E bricks);
nothing here touches `V2/Machine.lean` / `V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch
open Lir.V2

/-! ## The per-terminator simulation hypothesis `SimTermStep`

`SimTermStep prog sloadChg obs o self L b` packages Layer E's call-free conclusion uniformly
over the four IR terminators, matching `V2.RunFrom`'s constructor shape. It is what the CFG
induction consumes after Layer D has run the block's statements to the terminator cursor.

Two productions, exactly E1's and E2's conclusions:

* **halt** (`stop` / `ret`) — given `Corr` at the terminator cursor and the matching IR halt
  observable `Oend`, produce a halting frame `last` whose `observe` *world* is `Oend.world`;
* **edge** (`jump` / `branch`) — given `Corr` at the terminator cursor and the IR's chosen
  successor `succ`, run to `succ`'s entry frame re-establishing `Corr` at `(succ, 0)`.

The dispatch is on `b.term` together with the IR-side terminator witnesses (`hterm`, and for
the edges the resolved successor), so a concrete discharge case-splits `b.term` and feeds the
four Layer-E lemmas. Quantified over the post-`RunStmts` IR state `st'` and the terminator
frame `frT` (the frame Layer D delivers at the terminator cursor). -/

/-- **The per-terminator simulation step** (Layer E, call-free, abstracted over the block).
For block `b` at label `L`, a frame `frT` in `Corr`-correspondence with the post-statement IR
state `st'` at the terminator cursor `(L, b.stmts.length)`:

* if `b.term` is a **halt** (`stop` or `ret t`), there is a halting frame `last` reached from
  `frT` whose `observe self` **world** is the IR halt's world (`st'.world` for `stop`;
  `st'.world` for `ret`, the value-free world channel);
* if `b.term` is an **edge** (`jump dst`, or `branch` taking `succ`), there is a frame `fr'`
  reached from `frT` re-establishing `Corr` at the taken successor's entry `(succ, 0)`.

The halt case carries the IR halt observable `O` so the world equation is stated against the
same `O` the `RunFrom` halt constructor produces; the edge case carries the IR-resolved
successor `succ` so the re-established `Corr` is at the block the `RunFrom` recursion enters. -/
structure SimTermStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (o : V2.CallOracle) (selfAddr : AccountAddress) (L : Label) (b : Block) : Prop where
  /-- **Halt arm** (`stop` / `ret`). From `Corr` at the terminator cursor and a halting IR
  terminator with halt-world `wHalt` (`st'.world`), a halting frame matching the world. -/
  halt : ∀ (st' : V2.IRState) (frT : Frame),
    Corr prog sloadChg obs st' frT L b.stmts.length →
    (b.term = .stop ∨ ∃ t, b.term = .ret t) →
    ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
      ∧ (observe selfAddr (endFrame last haltSig)).world = st'.world
  /-- **Edge arm** (`jump` / `branch`). From `Corr` at the terminator cursor and the
  IR-resolved successor `succ` of the edge, a frame at `succ`'s entry re-establishing `Corr`. -/
  edge : ∀ (st' : V2.IRState) (frT : Frame) (succ : Label),
    Corr prog sloadChg obs st' frT L b.stmts.length →
    (b.term = .jump succ
      ∨ (∃ cond elseL cw, b.term = .branch cond succ elseL
            ∧ st'.locals cond = some cw ∧ cw ≠ 0)
      ∨ (∃ cond thenL, b.term = .branch cond thenL succ ∧ st'.locals cond = some 0)) →
    ∃ fr', Runs frT fr' ∧ Corr prog sloadChg obs st' fr' succ 0

/-! ## `WellFormedLowered` — the structural side-conditions, folded

The per-shape `_lowered` wrappers (`sim_sstore_stmt_lowered`, `sim_term_halt_ret_lowered`,
`sim_term_edge_jump_lowered`, `sim_term_edge_branch_lowered`) carry two kinds of *structural*
(non-runtime) side-condition that depend only on the **program text**, not on the trace:

* **recompute-fuel sufficiency** — `MatFueled (defsOf prog) (recomputeFuel prog) e` for every
  expression `e` the block materialises (the `sstore` operands, the `ret` operand). This is the
  honest well-formedness tie: `recomputeFuel` exceeds the def-chain depth of every materialised
  tmp. It is **discharged structurally** from a rank-based SSA acyclicity witness in
  `Acyclic.lean` (`wellFormedLowered_of_acyclic`), so an acyclic program carries no `MatFueled`
  hypothesis (`lower_conforms_acyclic`);
* **program-size pc/offset bounds** — every static cursor / block offset fits a 32-bit pc
  (`< 2^32`). These are pure facts about `offsetTable` / `termOf` / `pcOf` and the size of
  `lower prog`.

`WellFormedLowered prog` folds exactly those structural side-conditions, quantified over every
present block and (for the statement bounds) every cursor. The builders below pull the relevant
field per shape, so the structural residual leaves the builder hypotheses entirely — only the
*genuine* runtime recording-correspondence ties (`SstoreRealises` / `hret` / gas envelopes — the
§7 supplied-observation contract) stay explicit. The `validJumps`-recording ties are no longer
among them: they are discharged structurally from `Corr` (`Corr.validJumps_lower`). -/

/-- **The folded structural well-formedness predicate.** Bundles, over every present block of
`prog`, the recompute-fuel sufficiency of each materialised operand (`MatFueled`) and the
program-size pc/offset bounds (`< 2^32`) the `_lowered` wrappers carry. Purely structural — a
function of the program text, independent of the run. The `MatFueled` fields are discharged from
acyclicity (`Acyclic.lean`); the bounds are a finite check on the lowered program size. -/
structure WellFormedLowered (prog : Program) : Prop where
  /-- `sstore` operand fuel-sufficiency, at every `sstore` cursor of every present block. -/
  matFueled_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    MatFueled (defsOf prog) (recomputeFuel prog) (.tmp value)
    ∧ MatFueled (defsOf prog) (recomputeFuel prog) (.tmp key)
  /-- `sstore` pc bound: the statement's operand bytes fit a 32-bit pc. -/
  bound_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    pcOf prog L pc
      + ((materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length) < 2 ^ 32
  /-- **Spilled-`sload` key fuel-sufficiency.** At every `assign t (.sload k)` cursor of every
  present block, the key `k` materialises within the reduced recompute fuel `recomputeFuel prog -
  1` (the spilled-sload emit recurses on the key at one less fuel, `materialiseExpr_sload`). The
  analogue of `matFueled_sstore`, indexed to the reduced fuel `f` of `sim_assign_sload_lowered`. -/
  matFueled_sload : ∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    1 ≤ recomputeFuel prog
    ∧ MatFueled (defsOf prog) (recomputeFuel prog - 1) (.tmp k)
  /-- **Spilled-`sload` pc bound.** The whole stash (key materialise + the 35-byte
  `SLOAD;PUSH32;MSTORE` tail) fits a 32-bit pc. -/
  bound_sload : ∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    pcOf prog L pc
      + ((materialiseExpr (defsOf prog) (recomputeFuel prog - 1) (.tmp k)).length + 35) < 2 ^ 32
  /-- `ret` operand fuel-sufficiency, at every `ret`-terminated present block. -/
  matFueled_ret : ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    MatFueled (defsOf prog) (recomputeFuel prog) (.tmp t)
  /-- `branch` condition fuel-sufficiency, at every `branch`-terminated present block. The
  cond-materialise of `branch_landing_of_cleanHalt` recomputes `cond` within the full
  `recomputeFuel`; the `matFueled_ret` analogue for the terminator condition. -/
  matFueled_branch : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    MatFueled (defsOf prog) (recomputeFuel prog) (.tmp cond)
  /-- `ret` pc bound: the RETURN-value operand bytes fit a 32-bit pc. -/
  bound_ret : ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    termOf prog L
      + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length ≤ 2 ^ 32
  /-- `stop` pc bound: the terminator cursor fits a 32-bit pc. -/
  bound_stop : ∀ (L : Label) (b : Block),
    prog.blocks.toList[L.idx]? = some b → b.term = .stop →
    termOf prog L < 2 ^ 32
  /-- `jump` pc/offset bounds: the `PUSH4; JUMP` bytes and the destination offset fit. -/
  bound_jump : ∀ (L : Label) (b : Block) (dst : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
    termOf prog L + 5 < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32
  /-- `branch` pc/offset bounds: the cond-materialise + two `PUSH4; J…` bytes and both
  successor offsets fit. -/
  bound_branch : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    termOf prog L
        + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp cond)).length + 11 < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32
  /-- **Call-result slot registration.** Every tmp registered as a call result in `defsOf`
  carries its canonical slot `slotOf tw`. True structurally: `defsOf` registers each
  `.call ⟨_, _, some t⟩` as `(t, .slot (slotOf t))`, and a source `assign` never
  carries the lowering-only `.slot` marker (a `WellFormed` invariant, vacuous for real
  IR — no source program writes a `.slot` expression). This is `sim_call_stmt`'s
  `hslots`: it pins the result slot of the binding MSTORE and the 32-aligned disjointness of
  distinct bound call-result slots. (Call-result slot *addressability* — `slotOf t + 63 < 2^64`
  — is a property of the realised resume frame's memory, so it travels with the `CallRealises`
  tie, not here.) -/
  slots_slot : ∀ (tw : Tmp) (slot' : Nat),
    defsOf prog tw = some (.slot slot') → slot' = slotOf tw

/-! ## Discharging `SimStmtStep` / `SimTermStep` for the call-free fragment

`SimStmtStep`/`SimTermStep` are the per-block realisability bundles `sim_cfg` consumes.
Discharging them for a concrete program is a case split on the statement / terminator
shape feeding the Layer-C/E lemmas (`sim_assign` / `sim_sstore_stmt` ; `sim_term_*`).
Those lemmas in turn carry their *own* honest structured hypotheses — the per-byte
`MatDec` decode coverage at the runtime cursors, the immediate round-trips, the gas/stack
envelopes, and the genuine SLOAD/SSTORE/GAS realisability ties (the §7
supplied-observation contract). The two builders below carry exactly that residual,
minimised to the per-(cursor/frame) ties, so `sim_cfg`/`lower_conforms` see a thin
realisability surface rather than the opaque `SimStmtStep`/`SimTermStep` props.

### The `assign`-arm discharge (fully closed down to the genuine ties)

A **rematerialised** `assign` needs *no* decode bundle — `emitStmt … (.assign _ _) = []`
when the target is not spilled, so the lowered segment is `Runs.refl` and `sim_assign`
consumes only the per-step scoping (`StepScoped`) and the post-state realisability ties. A
**spilled gas** `assign t .gas` (Phase B) emits the `[GAS] ++ PUSH ++ MSTORE` stash and is
discharged by `sim_assign_gas` (the gas value lands in `slotOf t`, tied by `MemRealises`).
Both arms are folded into the general `simStmtStep_block` below; the old assign-only
specialisation is retired (superseded, and it baked in the now-false "every assign emits
nothing"). The `sstore` arm additionally needs the `MatDec` decode coverage over
`materialiseExpr` at the runtime cursors, and so is carried whole. -/

/-! ### The `call`-arm discharge (the §7 CALL tie)

For a `.call cs` cursor, `simStmtStep_call` feeds `sim_call_stmt` (`SimStmt.lean` Arm 3,
Route B). The CALL is a *genuine runtime call observation*: the realised external CALL trace
(`CallReturns`, the resume frame, the realised-oracle pinning, the arg-push run reaching the
CALL site, and the Route-B tail) cannot be discharged from the program text — it is the
analogue of `SstoreRealises`/the gas-SLOAD ties (the `docs/ir-design-v3.md` §7 supplied
observation). `CallRealises` bundles exactly that supply, quantified over the cursor frame;
the structural side-conditions (slot registration + addressability) come from
`WellFormedLowered`, and the pre-call `MemRealises` comes from `Corr.memAgree`.

The realised step is pinned via `o = evmV2CallOracle result pd self` (in the headline,
`o = realisedCall log self` *is* that realised oracle, `realisedCall_eq_evmV2` — `rfl`-clean
when the log recorded the CALL), so the abstract `EvalStmt prog o` call step *is* the realised
step `sim_call_stmt` consumes. -/

/-- **The §7 CALL realisability tie.** For a `.call cs` cursor with frame `fr0` in `Corr`
correspondence, `CallRealises` supplies the realised external-CALL trace `sim_call_stmt`
consumes: the recorded `(result, pd)` and self address, the realised-oracle identification
`o = evmV2CallOracle result pd self` (so the abstract call step is the realised step), the
arg-push run reaching the CALL-site frame `callFr` with its pc/memory pins, the returning CALL
(`CallReturns callFr resumeFr`) with the resume-frame pins, the post-state realisability ties,
and the Route-B tail's realisability. The genuine runtime call observation (the analogue of
`SstoreRealises`), supplied per cursor and quantified over the corresponding frame. -/
def CallRealises (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word) (o : V2.CallOracle)
    (L : Label) (b : Block) (pc : Nat) (cs : CallSpec) (st0 : V2.IRState) (fr0 : Frame) : Prop :=
  Corr prog sloadChg obs st0 fr0 L pc →
  ∃ (result : Evm.CallResult) (pd : Evm.PendingCall) (callFr resumeFr : Frame) (argsLen : Nat),
    -- the per-step scoping of the call statement (the §7 call scoping):
    StepScoped prog st0 (.call cs)
    -- the realised oracle pinning (so the abstract call step is the realised one):
    ∧ o = evmV2CallOracle result pd fr0.exec.executionEnv.address
    -- the arg-push run + its pins (`MatRuns`-style, the realised arg materialisation):
    ∧ argsLen = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
        ++ materialise (defsOf prog) (recomputeFuel prog) cs.callee
        ++ materialise (defsOf prog) (recomputeFuel prog) cs.gasFwd).length
    ∧ Runs fr0 callFr
    ∧ callFr.exec.pc = fr0.exec.pc + UInt32.ofNat argsLen
    ∧ callFr.exec.toMachineState.memory = fr0.exec.toMachineState.memory
    ∧ fr0.exec.toMachineState.activeWords.toNat ≤ callFr.exec.toMachineState.activeWords.toNat
    -- the returning external CALL + realised resume:
    ∧ CallReturns callFr resumeFr
    ∧ resumeFr = Evm.resumeAfterCall result pd
    -- the realised-call resume-frame pins (`resumeAfterCall` keeps the caller's env):
    ∧ resumeFr.exec.executionEnv.address = fr0.exec.executionEnv.address
    ∧ resumeFr.exec.executionEnv.code = lower prog
    ∧ resumeFr.exec.executionEnv.canModifyState = true
    ∧ resumeFr.exec.pc = callFr.exec.pc + 1
    ∧ resumeFr.exec.stack = callSuccessFlag result pd :: []
    ∧ resumeFr.exec.toMachineState.memory = callFr.exec.toMachineState.memory
    ∧ callFr.exec.toMachineState.activeWords.toNat ≤ resumeFr.exec.toMachineState.activeWords.toNat
    ∧ resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0
    -- the post-state scoping/realisability (downstream-supplied, as in `materialise_runs`):
    ∧ (∀ t, (match cs.resultTmp with
              | some t' => { st0 with world := fun key =>
                              evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }.setLocal
                              t' (callSuccessFlag result pd)
              | none   => { st0 with world := fun key =>
                              evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }).locals t ≠ none →
            (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
            ∧ defsOf prog t ≠ none)
    -- the Route-B tail's realisability (decode anchors + gas + memory-expansion witness):
    ∧ (∀ flag : Word, resumeFr.exec.stack = flag :: [] →
        (∀ (t : Tmp), cs.resultTmp = some t →
          (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
          ∧ ∃ endFr,
              Runs resumeFr endFr
            -- honest memory channel (`.memory` bytes + `.activeWords`, NOT the over-constrained
            -- full `toMachineState` — gas is a `MachineState` field a real run never preserves;
            -- this is exactly what `stash_tail_runs` constructs):
            ∧ endFr.exec.toMachineState.memory
                = (resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag).memory
            ∧ endFr.exec.toMachineState.activeWords
                = (resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag).activeWords
            ∧ endFr.exec.pc = resumeFr.exec.pc + UInt32.ofNat 34
            ∧ endFr.exec.executionEnv.code = resumeFr.exec.executionEnv.code
            ∧ endFr.validJumps = resumeFr.validJumps
            ∧ endFr.exec.executionEnv.address = resumeFr.exec.executionEnv.address
            ∧ endFr.exec.executionEnv.canModifyState = resumeFr.exec.executionEnv.canModifyState
            ∧ (∀ k, selfStorage endFr k = selfStorage resumeFr k)
            ∧ endFr.exec.stack = [])
        ∧ (cs.resultTmp = none →
            Runs resumeFr (popFrame resumeFr [])))

/-- **`SimStmtStep` for a `.call`-only block (the call-arm discharge).** For a `.call cs`
cursor, feeds `sim_call_stmt`: `WellFormedLowered` supplies the slot registration
(`slots_slot`) and addressability (`slots_addressable`), `Corr.memAgree` the pre-call
`MemRealises`, and the §7 `CallRealises` tie supplies the realised external-CALL trace. The
realised-oracle pinning makes the abstract call step the realised step. -/
theorem simStmtStep_call {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {L : Label} {b : Block} {pc : Nat} {cs : CallSpec}
    {st0 st0' : V2.IRState} {T0 T0' : Trace} {fr0 : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hget : b.stmts[pc]? = some (.call cs))
    (hwf : WellFormedLowered prog)
    (hcorr : Corr prog sloadChg obs st0 fr0 L pc)
    (hstep : EvalStmt prog o st0 T0 (.call cs) st0' T0')
    (hcall : CallRealises prog sloadChg obs o L b pc cs st0 fr0) :
    ∃ fr0', Runs fr0 fr0' ∧ Corr prog sloadChg obs st0' fr0' L (pc + 1)
      ∧ fr0'.exec.stack = [] := by
  obtain ⟨result, pd, callFr, resumeFr, argsLen, hsc, hosame, hargslen, hargs, hcallpc, hcallmem,
    hcallactive, hcallreturns, hresume, hresaddr, hrescode, hrescanmod, hrespc, hresstack,
    hresmem, hresactive, hresvalidjumps, hscoped', htail⟩ := hcall hcorr
  set self := fr0.exec.executionEnv.address with hselfdef
  -- the realised post-state (with `callSuccessFlag`, matching `CallRealises`'s ties).
  set stRes : V2.IRState := (match cs.resultTmp with
    | some t' => { st0 with world := fun key => evmCallOracle.postStorage result pd self key }.setLocal
                  t' (callSuccessFlag result pd)
    | none   => { st0 with world := fun key => evmCallOracle.postStorage result pd self key }) with hstRes
  -- the realised IR step into `stRes` (oracle pinned by `hosame`, success word reflexively
  -- the CALL flag): built fresh so `sim_call_stmt`'s post-state IS `stRes`.
  obtain ⟨calleeW, gasFwdW, hcallee, hgasfwd⟩ : ∃ cw gw, st0.locals cs.callee = some cw
      ∧ st0.locals cs.gasFwd = some gw := by
    cases hstep with
    | call hcallee hgasr _ => exact ⟨_, _, hcallee, hgasr⟩
  have hsuccW : evmCallOracle.successWord result pd = callSuccessFlag result pd :=
    evmCallOracle_successWord_eq_x result pd
  have hores : evmV2CallOracle result pd self calleeW gasFwdW st0.world
      = ((fun key => evmCallOracle.postStorage result pd self key), callSuccessFlag result pd) := by
    show ((fun key => evmCallOracle.postStorage result pd self key),
          evmCallOracle.successWord result pd) = _
    rw [hsuccW]
  have hstepRes : EvalStmt prog (evmV2CallOracle result pd self) st0 T0 (.call cs) stRes T0 := by
    have h := EvalStmt.call (prog := prog) (o := evmV2CallOracle result pd self) (T := T0)
      hcallee hgasfwd hores
    -- `EvalStmt.call`'s post-state matches `stRes` (the `match cs.resultTmp` shapes coincide).
    cases hr : cs.resultTmp with
    | some t' => rw [hstRes, hr]; rw [hr] at h; exact h
    | none    => rw [hstRes, hr]; rw [hr] at h; exact h
  -- the abstract step has the SAME post-state as `stRes` (the realised oracle ignores its
  -- argument words, so `hstep`'s own callee/gasFwd reads don't matter; success word reflexive).
  have hst0eq : st0' = stRes := by
    cases hstep with
    | call hcallee0 hgasr0 ho =>
      rw [hosame] at ho
      rw [show evmV2CallOracle result pd self _ _ st0.world
            = ((fun key => evmCallOracle.postStorage result pd self key),
               evmCallOracle.successWord result pd) from rfl] at ho
      injection ho with hw' hs'
      rw [hstRes, ← hsuccW]
      cases cs.resultTmp <;> rw [← hw', ← hs']
  rw [hst0eq]
  exact sim_call_stmt hb hget hcorr.pc_eq hargslen hargs hcallpc hcallmem hcallactive
    hcallreturns hresume hstepRes hresaddr hrescode hrescanmod
    hrespc hresstack hresmem hresactive hresvalidjumps hcorr.defsSound hsc hcorr.memAgree
    (hwf.slots_slot) hscoped' htail

/-! ### The combined statement discharge

`simStmtStep_block` case-splits a general block's statements per shape into the
`assign` / `sstore` / `call` arms — so `SimStmtStep` is CONSTRUCTIBLE for *any* block, given
`WellFormedLowered` and the per-shape genuine ties (including the §7 `CallRealises` tie for the
call arm). The three arms are exhaustive over `EvalStmt`. -/

/-- **`SimStmtStep` for any block (general over calls).** Dispatches each statement on its
shape: `assign` via `sim_assign` (no decode), `sstore` via `sim_sstore_stmt_lowered` (decode
discharged inside), `call` via `simStmtStep_call` (`sim_call_stmt` + the §7 `CallRealises`
tie). `WellFormedLowered` supplies the structural fuel/pc/slot side-conditions; the per-shape
genuine runtime ties (assign post-state realisability; sstore gas/`SstoreRealises`/non-zero;
the realised CALL trace) are the explicit §7 hypotheses. The three arms are exhaustive over
`EvalStmt`, so NO call-free side condition is needed. -/
theorem simStmtStep_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hwf : WellFormedLowered prog)
    -- the genuine **rematerialised** `assign`-cursor ties (target not spilled; post-state
    -- realisability at the unchanged frame — empty emit ⇒ `Runs.refl`):
    (hassign : ∀ (pc : Nat) (t : Tmp) (e : Expr) (st0 st0' : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.assign t e) →
        Corr prog sloadChg obs st0 fr0 L pc →
        (∀ n, defsOf prog t ≠ some (.slot n))
        ∧ StepScoped prog st0 (.assign t e)
        ∧ (∀ t', st0'.locals t' ≠ none →
              (¬ NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
              ∧ defsOf prog t' ≠ none)
        ∧ MemRealises prog st0' fr0)
    -- the genuine **spilled sload** `assign t (.sload k)`-cursor ties (Phase C): the SLOAD value
    -- (and its cold/warm warmth charge) lives in `slotOf t`, written once by the def-site stash
    -- `materialise k ++ [SLOAD] ++ PUSH slot ++ MSTORE`. `sim_assign_sload_lowered`
    -- (`LowerDecode.lean`) *builds* the run from the decode layout, and **the tail runtime envelope
    -- (SLOAD warmth + PUSH/MSTORE gas + memory-expansion witness) is no longer supplied** — it is
    -- DERIVED from the per-cursor clean-halt witness `hcs` via `sload_envelope_of_cleanHalt` (keyed
    -- on the post-materialise frame `frk`); **and the key-prefix gas fold is also DERIVED** from
    -- `hcs` via `materialise_runs_of_cleanHalt` (the gas charge-descent fold). `hsloadassign` now
    -- supplies only the honest residual: the slot registration, the loaded-value tie, the
    -- addressability, the **key-prefix stack-room fold** `hstkKey` (a stack-depth-profile argument —
    -- NOT gas-derivable; the stack goes up and down over the materialise so the peak bound is not a
    -- charge-accumulation), the **activeWords-flatness** `hawk` (materialising the key expanded no
    -- memory — a memory-shape fact, not clean-halt-derivable), and the post-state scoping.
    (hsloadassign : ∀ (pc : Nat) (t k : Tmp) (w : Word) (st0 : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.assign t (.sload k)) →
        Corr prog sloadChg obs st0 fr0 L pc →
        defsOf prog t = some (.slot (slotOf t))
        ∧ StepScoped prog st0 (.assign t (.sload k))
        ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
        ∧ V2.evalExpr st0 0 (.sload k) = some w
        ∧ (∀ t', (st0.setLocal t w).locals t' ≠ none →
              (¬ NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
              ∧ defsOf prog t' ≠ none)
        ∧ (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        -- key-prefix gas fold DROPPED: DERIVED from `hcs` via `materialise_runs_of_cleanHalt`.
        -- The key-prefix stack-room fold stays supplied (separate stack-depth-profile argument):
        ∧ fr0.exec.stack.size
            + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k)).length ≤ 1024
        -- the activeWords-flatness `hawk` at the post-materialise frame (a memory-shape fact):
        ∧ (∀ frk : Frame,
            MatRuns (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k)
                (match st0.locals k with | some keyVal => keyVal | none => 0) fr0 frk →
            frk.exec.toMachineState.activeWords = fr0.exec.toMachineState.activeWords))
    -- the genuine **spilled gas** `assign t .gas`-cursor ties (Phase B, P1): the gas value lives
    -- in `slotOf t`, written by the `[GAS] ++ PUSH ++ MSTORE` stash. **The stash run is no longer
    -- supplied** — `sim_assign_gas_lowered` (P1) *constructs* it from the decode layout +
    -- `stash_tail_gas`; and **the runtime gas/memory-expansion envelope is no longer supplied
    -- either** — it is DERIVED from the per-cursor clean-halt witness `hcs` via
    -- `gas_envelope_of_cleanHalt` (a frame that clean-halts non-exceptionally cannot have faulted
    -- on its next GAS/PUSH/MSTORE step, so each gas guard held). `hgasassign` now supplies only the
    -- honest residual: the slot registration, the **positional gas value tie** `ob = ofUInt64
    -- (fr0.gas − Gbase)` (the realised one-read `GAS` output — no `∀`-frames, no constancy), the
    -- addressability + pc-bound, and the post-state scoping/SLOAD ties:
    (hgasassign : ∀ (pc : Nat) (t : Tmp) (ob : Word) (st0 : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.assign t .gas) →
        Corr prog sloadChg obs st0 fr0 L pc →
        defsOf prog t = some (.slot (slotOf t))
        ∧ StepScoped prog st0 (.assign t .gas)
        ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
        -- the positional gas value tie: the consumed read is the realised `GAS` output:
        ∧ ob = UInt256.ofUInt64 (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase)
        ∧ (∀ t', (st0.setLocal t ob).locals t' ≠ none →
              (¬ NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
              ∧ defsOf prog t' ≠ none)
        ∧ ((slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
          ∧ pcOf prog L pc + 34 < 2 ^ 32))
    -- the genuine `sstore`-cursor ties (the §7 supplied-observation contract):
    (hsstore : ∀ (pc : Nat) (key value : Tmp) (kw vw : Word) (st0 : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.sstore key value) →
        Corr prog sloadChg obs st0 fr0 L pc →
        st0.locals key = some kw → st0.locals value = some vw →
        StepScoped prog st0 (.sstore key value)
        -- gas aggregate DROPPED: now DERIVED from the threaded clean-halt witness `hcs`
        -- via `sim_sstore_stmt`'s two-frame chained fold.
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
            + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024
        ∧ (∃ acc, SstoreRealises fr0 kw vw acc) ∧ vw ≠ 0)
    -- the genuine `call`-cursor tie (the §7 realised-CALL trace):
    (hcallties : ∀ (pc : Nat) (cs : CallSpec) (st0 : V2.IRState) (fr0 : Frame),
        b.stmts[pc]? = some (.call cs) →
        CallRealises prog sloadChg obs o L b pc cs st0 fr0) :
    SimStmtStep prog sloadChg obs o L b := by
  intro pc s st0 st0' T0 T0' fr0 hget hcorr hcs hstep
  -- `s` is at a present cursor; case on the `EvalStmt` step (assign / sstore / call).
  cases hstep with
  | assignPure hne hv =>
    rename_i t e w
    -- split on whether `e` is a spilled `.sload k` (Phase C) or a rematerialised pure expr.
    cases e with
    | sload k =>
      obtain ⟨hslotdef, hsc, hslots, hwval, hscoped', hslot63, hslotplat, hstkKey, hawk⟩ :=
        hsloadassign pc t k w st0 fr0 hget hcorr
      -- the reduced fuel `f = recomputeFuel prog - 1` (the key materialises at `f`).
      obtain ⟨hfuelpos, hwfk⟩ := hwf.matFueled_sload L b pc t k hb hget
      have hfuel : recomputeFuel prog = (recomputeFuel prog - 1) + 1 := by omega
      -- the SLOAD tail runtime envelope AND the key-prefix gas fold are DERIVED from the clean-halt
      -- witness `hcs`; only the key-prefix stack-room fold `hstkKey` and the activeWords-flatness
      -- `hawk` (memory-shape) stay supplied.
      refine sim_assign_sload_lowered hb hget hslotdef hcorr hsc hslots hwval hfuel hwfk
        hslot63 hslotplat (hwf.bound_sload L b pc t k hb hget) hcs hstkKey ?_ hscoped'
      intro frk hmrk
      -- the per-cursor clean-halt witness threads to `frk` inside the extractor.
      obtain ⟨hdecSLOAD, hdecPUSH, hdecMSTORE⟩ :=
        decode_sloadstash (t := t) hb hget hslotdef hfuel (hwf.bound_sload L b pc t k hb hget) hcorr hmrk
      exact ⟨hawk frk hmrk,
        CleanHaltExtract.sload_envelope_of_cleanHalt
          (f := recomputeFuel prog - 1) (ekey := .tmp k)
          (wkey := (match st0.locals k with | some keyVal => keyVal | none => 0))
          fr0 frk (match st0.locals k with | some keyVal => keyVal | none => 0) (slotOf t)
          hcs hcorr.stack_nil hmrk rfl hdecSLOAD hdecPUSH hdecMSTORE⟩
    | imm v =>
      obtain ⟨hremat, hsc, hscoped', hmem'⟩ :=
        hassign pc t (.imm v) st0 (st0.setLocal t w) fr0 hget hcorr
      obtain ⟨_, hc', _⟩ := sim_assign hb hget hremat hcorr
        (EvalStmt.assignPure (prog := prog) (o := o) (T := T0) hne hv) hsc hscoped' hmem'
      exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
    | tmp t' =>
      obtain ⟨hremat, hsc, hscoped', hmem'⟩ :=
        hassign pc t (.tmp t') st0 (st0.setLocal t w) fr0 hget hcorr
      obtain ⟨_, hc', _⟩ := sim_assign hb hget hremat hcorr
        (EvalStmt.assignPure (prog := prog) (o := o) (T := T0) hne hv) hsc hscoped' hmem'
      exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
    | add a b =>
      obtain ⟨hremat, hsc, hscoped', hmem'⟩ :=
        hassign pc t (.add a b) st0 (st0.setLocal t w) fr0 hget hcorr
      obtain ⟨_, hc', _⟩ := sim_assign hb hget hremat hcorr
        (EvalStmt.assignPure (prog := prog) (o := o) (T := T0) hne hv) hsc hscoped' hmem'
      exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
    | lt a b =>
      obtain ⟨hremat, hsc, hscoped', hmem'⟩ :=
        hassign pc t (.lt a b) st0 (st0.setLocal t w) fr0 hget hcorr
      obtain ⟨_, hc', _⟩ := sim_assign hb hget hremat hcorr
        (EvalStmt.assignPure (prog := prog) (o := o) (T := T0) hne hv) hsc hscoped' hmem'
      exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
    | slot n =>
      obtain ⟨hremat, hsc, hscoped', hmem'⟩ :=
        hassign pc t (.slot n) st0 (st0.setLocal t w) fr0 hget hcorr
      obtain ⟨_, hc', _⟩ := sim_assign hb hget hremat hcorr
        (EvalStmt.assignPure (prog := prog) (o := o) (T := T0) hne hv) hsc hscoped' hmem'
      exact ⟨fr0, Runs.refl fr0, hc', hcorr.stack_nil⟩
    | gas => exact absurd rfl hne
  | assignGas =>
    rename_i ob t
    obtain ⟨hslotdef, hsc, hslots, hobeq, hscoped', hslot63, hslotplat, hpcbound⟩ :=
      hgasassign pc t ob st0 fr0 hget hcorr
    -- the positional gas value tie pins the consumed read to the realised `GAS` output.
    subst hobeq
    -- the GAS-stash decode anchors (reusable, structural) + the clean-halt witness DERIVE the
    -- full runtime gas/memory envelope `sim_assign_gas_lowered` consumes (no longer supplied).
    obtain ⟨hdecGAS, hdecPUSH, hdecMSTORE⟩ := decode_gasstash hb hget hslotdef hpcbound hcorr
    obtain ⟨hgasGas, hgasPush, words', hmem, hgasMem, hgasMstore⟩ :=
      CleanHaltExtract.gas_envelope_of_cleanHalt fr0 (slotOf t) hcs hcorr.stack_nil
        hdecGAS hdecPUSH hdecMSTORE
    exact sim_assign_gas_lowered hb hget hslotdef hcorr hsc hslots hslot63 hslotplat hpcbound
      hgasGas hgasPush hmem hgasMem hgasMstore hscoped'
  | sstore hk hv =>
    rename_i key value kw vw
    obtain ⟨hsc, hstk, ⟨acc, hsr⟩, hnz⟩ := hsstore pc key value kw vw st0 fr0 hget hcorr hk hv
    obtain ⟨hwfv, hwfk⟩ := hwf.matFueled_sstore L b pc key value hb hget
    exact sim_sstore_stmt_lowered hb hget hcorr hk hv hsc hwfv hwfk
      (hwf.bound_sstore L b pc key value hb hget) hcs hstk hsr hnz
  | call hcallee hgasr ho =>
    rename_i cs calleeW gasFwdW success world'
    exact simStmtStep_call hb hget hwf hcorr
      (EvalStmt.call (prog := prog) (o := o) (T := T0) hcallee hgasr ho)
      (hcallties pc cs st0 fr0 hget)

/-! ### The `stop`-terminator discharge (fully closed down to the genuine frame facts)

For a block whose terminator is `Stmt`-free `Term.stop`, `SimTermStep`'s `edge` arm is
vacuous (its `b.term = jump/branch` hypotheses are unsatisfiable) and the `halt` arm's `ret`
disjunct is too. The remaining `stop` halt routes through `sim_term_halt_stop`, whose `STOP`
decode is itself discharged from A3 (`decode_at_term_nonpush`) + the terminator-cursor pc
bridge (`pcOf_eq_termOf`): the only residual is the genuine top-level-frame facts — the self
address (`hself`), the `.call`-kind (`hkind`), and the non-empty committed accounts (`hne`) —
exactly the `EntersAsCode`/successful-run facts the §7 contract supplies. A complete
`SimTermStep` discharge for the `stop` terminator. -/

/-- **`SimTermStep` for a `stop`-terminator block.** If `b.term = .stop`, then — given the
genuine top-level-frame facts at every terminator-cursor frame (self address `= fr.address`,
`.call`-kind, non-empty committed accounts) and the pc bound — `SimTermStep` holds. The `STOP`
decode is discharged from A3; the `edge`/`ret` arms are vacuous. -/
theorem simTermStep_stop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .stop)
    (hbound : termOf prog L < 2 ^ 32)
    -- the genuine top-level-frame facts at any terminator-cursor frame in `Corr`:
    (hframe : ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        self = frT.exec.executionEnv.address
        ∧ (∃ cp, frT.kind = .call cp)
        ∧ ¬ (frT.exec.accounts == ∅) = true) :
    SimTermStep prog sloadChg obs o self L b := by
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: only the `stop` disjunct fires (the `ret` one contradicts `hterm`).
    intro st' frT hcorr hdisj
    obtain ⟨hself, ⟨cp, hkind⟩, hne⟩ := hframe st' frT hcorr
    -- the `STOP` decode at the terminator cursor, from A3 + `pcOf_eq_termOf`.
    have hpcterm : frT.exec.pc = UInt32.ofNat (termOf prog L) := by
      rw [hcorr.pc_eq, pcOf_eq_termOf prog L b hb]
    have hdec : decode frT.exec.executionEnv.code frT.exec.pc
        = some (.System .STOP, .none) := by
      rw [hcorr.code_eq, hpcterm]
      have hk : 0 < (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term).length := by
        rw [hterm]; simp [emitTerm]
      have hbyte0 : (emitTerm (defsOf prog) (recomputeFuel prog)
          (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks) b.term)[0]?
          = some Byte.stop := by rw [hterm]; rfl
      have := decode_at_term_nonpush prog L b 0 Byte.stop hb (by simpa using hk)
        hbyte0 (by simpa using hbound) (by decide)
      simpa using this
    obtain ⟨last, halt, hruns, hhalt, hworld, _⟩ :=
      sim_term_halt_stop hcorr hterm hself hdec hkind hne
    exact ⟨last, halt, hruns, hhalt, hworld⟩
  · -- edge arm: vacuous (b.term = .stop contradicts every jump/branch disjunct).
    intro st' frT succ hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩ <;> exact absurd h (by simp)

/-! ### The `ret`-terminator discharge (decode-free via `sim_term_halt_ret_lowered`)

For a block whose terminator is `Term.ret t`, `SimTermStep`'s `edge` arm is vacuous and the
`halt` arm's `stop` disjunct contradicts. The `ret` halt routes through
`sim_term_halt_ret_lowered` — the operand `MatDec` is discharged inside; `WellFormedLowered`
supplies the structural `MatFueled` + pc bound. The genuine residual is the value-channel
RETURN-site tie (`hself`, the returned-value binding `st'.locals t = some vw`, the gas/stack
envelopes, and the RETURN-site `hret` — the §7 supplied-observation contract). -/

/-- **`SimTermStep` for a `ret`-terminator block.** If `b.term = .ret t`, then — given
`WellFormedLowered` and, at every terminator-cursor frame in `Corr`, the genuine value-channel
ties (`hself`, the returned-value binding, gas/stack envelopes, the RETURN-site `hret`) —
`SimTermStep` holds. The decode is discharged inside `sim_term_halt_ret_lowered`; the
`edge`/`stop` arms are vacuous. -/
theorem simTermStep_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block} {t : Tmp}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .ret t)
    (hwf : WellFormedLowered prog)
    -- the genuine value-channel RETURN-site ties (the §7 contract) at any terminator-cursor frame:
    (hties : ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        self = frT.exec.executionEnv.address
        ∧ (∃ vw, st'.locals t = some vw)
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
            ≤ frT.exec.gasAvailable.toNat
        ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
        ∧ (∀ (vw : Word), st'.locals t = some vw →
            ∀ frv : Frame, Runs frT frv →
            frv.exec.executionEnv.code = frT.exec.executionEnv.code →
            frv.exec.executionEnv.address = frT.exec.executionEnv.address →
            (∀ k, selfStorage frv k = selfStorage frT k) →
            frv.exec.stack = vw :: frT.exec.stack →
            ∃ cp,
              decode frv.exec.executionEnv.code frv.exec.pc
                  = some (.Push .PUSH32, some ((0 : Word), 32))
              ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
                  = some (.Push .PUSH32, some ((0 : Word), 32))
              ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
                  = some (.System .RETURN, .none)
              ∧ 3 ≤ frv.exec.gasAvailable.toNat
              ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
              ∧ frv.kind = .call cp
              ∧ ¬ (frv.exec.accounts == ∅) = true)) :
    SimTermStep prog sloadChg obs o self L b := by
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: only the `ret` disjunct fires (the `stop` one contradicts `hterm`).
    intro st' frT hcorr _hdisj
    obtain ⟨hself, ⟨vw, hv⟩, hgas, hstk, hret⟩ := hties st' frT hcorr
    exact sim_term_halt_ret_lowered hb hcorr hterm hself hv
      (hwf.matFueled_ret L b t hb hterm) (hwf.bound_ret L b t hb hterm) hgas hstk (hret vw hv)
  · -- edge arm: vacuous (b.term = .ret t contradicts every jump/branch disjunct).
    intro st' frT succ hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩ <;> exact absurd h (by simp)

/-! ### The `jump`-terminator discharge (decode-free via `sim_term_edge_jump_lowered`)

For an unconditional `Term.jump dst`, `SimTermStep`'s `halt` arm is vacuous. The `edge` arm's
`jump` disjunct (`succ = dst`) routes through `sim_term_edge_jump_lowered` — the PUSH4/JUMP/
landing-JUMPDEST decode bundle and the offset round-trip are discharged inside;
`WellFormedLowered` supplies the structural pc/offset bounds; the `validJumps`-recording tie is
discharged structurally from `Corr` (`Corr.validJumps_lower`) inside the wrapper. The genuine
residual is the gas envelopes (§7), plus the destination block's presence. -/

/-- **`SimTermStep` for a `jump`-terminator block.** If `b.term = .jump dst` with `dst` present,
then — given `WellFormedLowered` and, at every terminator-cursor frame, the genuine control-flow
ties (the gas envelopes) — `SimTermStep` holds. The decode and the `validJumps` tie are
discharged inside `sim_term_edge_jump_lowered`; the `halt` arm is vacuous. -/
theorem simTermStep_jump {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    {dst : Label} {bdst : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .jump dst)
    (hwf : WellFormedLowered prog)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hdstlt : dst.idx < prog.blocks.size)
    -- the genuine control-flow ties (gas envelopes) at any terminator-cursor frame. The
    -- `validJumps`-recording tie is no longer carried — it is discharged structurally inside
    -- `sim_term_edge_jump_lowered` from `Corr` (frame-invariant `validJumps = validJumpDests
    -- code 0` + `code = lower prog`).
    (hties : ∀ (st' : V2.IRState) (frT : Frame),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        3 ≤ frT.exec.gasAvailable.toNat
        ∧ GasConstants.Gmid ≤ (pushFrameW frT
            (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
            4).exec.gasAvailable.toNat
        ∧ GasConstants.Gjumpdest
            ≤ (jumpFrame (pushFrameW frT
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32)) 4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                frT.exec.stack).exec.gasAvailable.toNat) :
    SimTermStep prog sloadChg obs o self L b := by
  obtain ⟨hbt, hbo⟩ := hwf.bound_jump L b dst hb hterm
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: vacuous (b.term = .jump dst contradicts stop/ret).
    intro st' frT hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, h⟩ <;> exact absurd h (by simp)
  · -- edge arm: the `jump` disjunct (`succ = dst`).
    intro st' frT succ hcorr hdisj
    have hsucc : succ = dst := by
      rw [hterm] at hdisj
      rcases hdisj with h | ⟨_, _, _, h, _⟩ | ⟨_, _, h, _⟩
      · exact (Term.jump.inj h).symm
      · exact absurd h (by simp)
      · exact absurd h (by simp)
    subst hsucc
    obtain ⟨hgpush, hgjump, hgjd⟩ := hties st' frT hcorr
    obtain ⟨fr', L', hL', hruns', hcorr'⟩ :=
      sim_term_edge_jump_lowered hcorr hterm hb hbdst hdstlt hbt hbo hgpush hgjump hgjd
    subst hL'
    exact ⟨fr', hruns', hcorr'⟩

/-! ### The `branch`-terminator discharge (decode-free via `sim_term_edge_branch_lowered`)

For a `Term.branch cond thenL elseL`, `SimTermStep`'s `halt` arm is vacuous. The `edge` arm's
two branch disjuncts (`cw ≠ 0 → succ = thenL`, `cw = 0 → succ = elseL`) route through
`sim_term_edge_branch_lowered`, whose strengthened cw-tied conclusion pins the resolved
successor to the runtime condition — so the `succ` `SimTermStep` asks for is exactly the one the
lowered branch lands on. The decode bundle and the `validJumps`-recording tie (via
`Corr.validJumps_lower` + `MatRuns.validJumps`) are discharged inside; `WellFormedLowered`
supplies the structural pc/offset bounds. The genuine residual is the cond-materialise run
(`MatRuns`) and the gas envelopes (§7), plus the successor blocks' presence. -/

/-- **`SimTermStep` for a `branch`-terminator block.** If `b.term = .branch cond thenL elseL`
with both successors present, then — given `WellFormedLowered` and, at every terminator-cursor
frame, the genuine control-flow ties (the cond-materialise `MatRuns`, the gas envelopes) —
`SimTermStep` holds. The cw-tied conclusion of `sim_term_edge_branch_lowered` reconciles the
`SimTermStep.edge` disjunct's chosen `succ` with the runtime-resolved branch. -/
theorem simTermStep_branch {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    {cond : Tmp} {thenL elseL : Label} {bthen belse : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hterm : b.term = .branch cond thenL elseL)
    (hwf : WellFormedLowered prog)
    (hbthen : prog.blocks.toList[thenL.idx]? = some bthen)
    (hbelse : prog.blocks.toList[elseL.idx]? = some belse)
    (hthenlt : thenL.idx < prog.blocks.size)
    (helselt : elseL.idx < prog.blocks.size)
    -- the genuine control-flow ties at any terminator-cursor frame, parametrised over the
    -- runtime condition word `cw` and the cond-materialise endpoint `frc`:
    (hties : ∀ (st' : V2.IRState) (frT : Frame) (cw : Word),
        Corr prog sloadChg obs st' frT L b.stmts.length →
        st'.locals cond = some cw →
        ∃ frc, MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
          ∧ 3 ≤ frc.exec.gasAvailable.toNat
          ∧ GasConstants.Ghigh ≤ (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              GasConstants.Ghigh
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word)).exec.gasAvailable.toNat
          ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              ([] : Stack Word))
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
              GasConstants.Gmid
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
              (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat) :
    SimTermStep prog sloadChg obs o self L b := by
  obtain ⟨hbt, hbthenoff, hbelseoff⟩ := hwf.bound_branch L b cond thenL elseL hb hterm
  refine { halt := ?_, edge := ?_ }
  · -- halt arm: vacuous (b.term = .branch contradicts stop/ret).
    intro st' frT hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨_, h⟩ <;> exact absurd h (by simp)
  · -- edge arm: the two branch disjuncts, each tied to `cw` via the strengthened conclusion.
    intro st' frT succ hcorr hdisj
    rw [hterm] at hdisj
    rcases hdisj with h | ⟨cond', elseL', cw, heq, hc, hnz⟩ | ⟨cond', thenL', heq, hc⟩
    · exact absurd h (by simp)
    · -- then-branch taken (`cw ≠ 0`), so the `SimTermStep` `succ` is `thenL`.
      obtain ⟨hcond, hsucc, helse⟩ := Term.branch.inj heq
      subst hcond; subst hsucc; subst helse
      obtain ⟨frc, hmrc, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hties st' frT cw hcorr hc
      obtain ⟨fr', L', hL', hruns', hcorr'⟩ :=
        sim_term_edge_branch_lowered hcorr hterm hb hc hbthen hbelse hthenlt helselt hmrc
          hbt hbthenoff hbelseoff hg1 hg2 hg3 hg4 hg5 hg6
      rcases hL' with ⟨_, hLt⟩ | ⟨hcw0, _⟩
      · subst hLt; exact ⟨fr', hruns', hcorr'⟩
      · exact absurd hcw0 hnz
    · -- else-branch taken (`cw = 0`), so the `SimTermStep` `succ` is `elseL`.
      obtain ⟨hcond, hthen, hsucc⟩ := Term.branch.inj heq
      subst hcond; subst hthen; subst hsucc
      obtain ⟨frc, hmrc, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hties st' frT 0 hcorr hc
      obtain ⟨fr', L', hL', hruns', hcorr'⟩ :=
        sim_term_edge_branch_lowered hcorr hterm hb hc hbthen hbelse hthenlt helselt hmrc
          hbt hbthenoff hbelseoff hg1 hg2 hg3 hg4 hg5 hg6
      rcases hL' with ⟨hcwne, _⟩ | ⟨_, hLe⟩
      · exact absurd rfl hcwne
      · subst hLe; exact ⟨fr', hruns', hcorr'⟩

/-! ### The combined call-free terminator discharge

`simTermStep_block` case-splits a block's terminator into the four arms — so `SimTermStep` is
CONSTRUCTIBLE for any block, given `WellFormedLowered`, the successor presence, and the per-shape
genuine §7 ties. The genuine ties are collected as one hypothesis dispatched on `b.term`. -/

/-- **`SimTermStep` for any block.** Dispatches `b.term` into the four arms
(`simTermStep_stop`/`_ret`/`_jump`/`_branch`). `WellFormedLowered` supplies the structural
fuel/pc/offset side-conditions; the per-shape genuine §7 ties are supplied by the `hstop`/`hret`/
`hjump`/`hbranch` hypotheses (each consumed only on its matching terminator shape). The successor
blocks (for the edges) are supplied by `hsucc`. -/
theorem simTermStep_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {L : Label} {b : Block}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hwf : WellFormedLowered prog)
    -- successor-block presence for the edges (vacuous on halts):
    (hsucc : ∀ (L' : Label), (b.term = .jump L' ∨ (∃ c o', b.term = .branch c L' o')
        ∨ (∃ c t', b.term = .branch c t' L')) →
        ∃ b', prog.blocks.toList[L'.idx]? = some b' ∧ L'.idx < prog.blocks.size)
    -- the genuine §7 ties, dispatched on the terminator shape:
    (hstop : b.term = .stop →
        ∀ (st' : V2.IRState) (frT : Frame),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          self = frT.exec.executionEnv.address
          ∧ (∃ cp, frT.kind = .call cp)
          ∧ ¬ (frT.exec.accounts == ∅) = true)
    (hretties : ∀ t, b.term = .ret t →
        ∀ (st' : V2.IRState) (frT : Frame),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          self = frT.exec.executionEnv.address
          ∧ (∃ vw, st'.locals t = some vw)
          ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
              ≤ frT.exec.gasAvailable.toNat
          ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
          ∧ (∀ (vw : Word), st'.locals t = some vw →
              ∀ frv : Frame, Runs frT frv →
              frv.exec.executionEnv.code = frT.exec.executionEnv.code →
              frv.exec.executionEnv.address = frT.exec.executionEnv.address →
              (∀ k, selfStorage frv k = selfStorage frT k) →
              frv.exec.stack = vw :: frT.exec.stack →
              ∃ cp,
                decode frv.exec.executionEnv.code frv.exec.pc
                    = some (.Push .PUSH32, some ((0 : Word), 32))
                ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
                    = some (.Push .PUSH32, some ((0 : Word), 32))
                ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
                    = some (.System .RETURN, .none)
                ∧ 3 ≤ frv.exec.gasAvailable.toNat
                ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
                ∧ frv.kind = .call cp
                ∧ ¬ (frv.exec.accounts == ∅) = true))
    (hjump : ∀ dst bdst, b.term = .jump dst →
        prog.blocks.toList[dst.idx]? = some bdst → dst.idx < prog.blocks.size →
        ∀ (st' : V2.IRState) (frT : Frame),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          3 ≤ frT.exec.gasAvailable.toNat
          ∧ GasConstants.Gmid ≤ (pushFrameW frT
              (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
              4).exec.gasAvailable.toNat
          ∧ GasConstants.Gjumpdest
              ≤ (jumpFrame (pushFrameW frT
                  (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32)) 4)
                  GasConstants.Gmid
                  (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                  frT.exec.stack).exec.gasAvailable.toNat)
    (hbranch : ∀ cond thenL elseL bthen belse, b.term = .branch cond thenL elseL →
        prog.blocks.toList[thenL.idx]? = some bthen → prog.blocks.toList[elseL.idx]? = some belse →
        thenL.idx < prog.blocks.size → elseL.idx < prog.blocks.size →
        ∀ (st' : V2.IRState) (frT : Frame) (cw : Word),
          Corr prog sloadChg obs st' frT L b.stmts.length →
          st'.locals cond = some cw →
          ∃ frc, MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
            ∧ 3 ≤ frc.exec.gasAvailable.toNat
            ∧ GasConstants.Ghigh ≤ (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
                4).exec.gasAvailable.toNat
            ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                GasConstants.Ghigh
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
                ([] : Stack Word)).exec.gasAvailable.toNat
            ∧ 3 ≤ (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word)).exec.gasAvailable.toNat
            ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word))
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4).exec.gasAvailable.toNat
            ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                ([] : Stack Word))
                (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
                (jumpiFallthroughFrame (pushFrameW frc
                  (UInt256.ofNat ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                  ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat) :
    SimTermStep prog sloadChg obs o self L b := by
  -- dispatch on the terminator shape.
  cases hb' : b.term with
  | stop => exact simTermStep_stop hb hb' (hwf.bound_stop L b hb hb') (hstop hb')
  | ret t => exact simTermStep_ret hb hb' hwf (hretties t hb')
  | jump dst =>
    obtain ⟨bdst, hbdst, hdstlt⟩ := hsucc dst (Or.inl hb')
    exact simTermStep_jump hb hb' hwf hbdst hdstlt (hjump dst bdst hb' hbdst hdstlt)
  | branch cond thenL elseL =>
    obtain ⟨bthen, hbthen, hthenlt⟩ := hsucc thenL (Or.inr (Or.inl ⟨cond, elseL, hb'⟩))
    obtain ⟨belse, hbelse, helselt⟩ := hsucc elseL (Or.inr (Or.inr ⟨cond, thenL, hb'⟩))
    exact simTermStep_branch hb hb' hwf hbthen hbelse hthenlt helselt
      (hbranch cond thenL elseL bthen belse hb' hbthen hbelse hthenlt helselt)

/-! ## `sim_cfg` — the whole-CFG simulation

Induction on `V2.RunFrom`. Each constructor:

* runs the block's statement list (any statements, incl. calls) via Layer D
  (`sim_stmts_block`), from `Corr` at the block entry `(L, 0)` to `Corr` at the terminator
  cursor `(L, b.stmts.length)` with the working stack back to `[]`;
* then dispatches on the terminator: `stop`/`ret` halt via `SimTermStep.halt` (the world
  matches `st'.world`, which is the IR halt's world); `jump`/`branch` run to the successor's
  entry via `SimTermStep.edge`, re-establishing `Corr`, and the **IH** closes the recursion.

`RunFrom` is an inductive `Prop`, so the structural recursion on the derivation is well-founded
— no fuel. The per-block simulation is supplied uniformly as the two `∀`-quantified structured
hypotheses (`SimStmtStep` already ranges over calls, via `sim_call_stmt`). -/

/-- **`sim_cfg` — whole-program CFG simulation (general over calls, world channel).** From
`Corr` at the entry cursor `(L, 0)` and a `V2.RunFrom prog o st T L O`, where every block
reached supplies the per-statement (`SimStmtStep`) and per-terminator (`SimTermStep`)
simulations, the lowered bytecode runs from `fr` to a halting frame `last` whose `observe self`
**world** is the IR observable `O`'s world.

Induction on the `RunFrom` derivation: Layer D runs each block's statements; `SimTermStep`
either halts (matching the world, the `stop`/`ret` base cases) or steps to the taken
successor's entry where the IH applies (the `jump`/`branch` recursion). -/
theorem sim_cfg {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {o : V2.CallOracle}
    {self : AccountAddress}
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs o L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs o self L b)
    {st : V2.IRState} {T : Trace} {L : Label} {O : V2.Observable} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hcs : CleanHaltsNonException fr)
    (hrun : V2.RunFrom prog o st T L O) :
    ∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world := by
  induction hrun generalizing fr with
  | @ret st st' T T' L b t w hb hss hterm' hv =>
    -- Layer D: run the block's statements to the terminator cursor.
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hcs hss
    -- Layer E: `ret` halts with world = st'.world (the IR ret halt's world).
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ :=
      (hterm L b hb).halt st' frT hcorrT (Or.inr ⟨t, hterm'⟩)
    exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld⟩
  | @stop st st' T T' L b hb hss hterm' =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hcs hss
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ :=
      (hterm L b hb).halt st' frT hcorrT (Or.inl hterm')
    exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld⟩
  | @branchThen st st' T T' L b cond cw thenL elseL O hb hss hterm' hc hnz hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hcs hss
    -- Layer E (edge): step to `thenL`'s entry, re-establishing `Corr` at `(thenL, 0)`.
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT thenL hcorrT
        (Or.inr (Or.inl ⟨cond, elseL, cw, hterm', hc, hnz⟩))
    -- DERIVE the successor's clean-halt from `fr`'s, across the block + edge run.
    have hcs' : CleanHaltsNonException fr' :=
      cleanHaltsNonException_forward hcs (hrunsT.trans hruns')
    -- IH on the recursion into `thenL`, from the re-established `Corr`.
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr' hcs'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩
  | @branchElse st st' T T' L b cond thenL elseL O hb hss hterm' hc hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hcs hss
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT elseL hcorrT
        (Or.inr (Or.inr ⟨cond, thenL, hterm', hc⟩))
    have hcs' : CleanHaltsNonException fr' :=
      cleanHaltsNonException_forward hcs (hrunsT.trans hruns')
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr' hcs'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩
  | @jump st st' T T' L b dst O hb hss hterm' hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hcs hss
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT dst hcorrT (Or.inl hterm')
    have hcs' : CleanHaltsNonException fr' :=
      cleanHaltsNonException_forward hcs (hrunsT.trans hruns')
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr' hcs'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩

/-! ## `entry_corr` — the entry correspondence builder (the leading-JUMPDEST step)

`sim_cfg` is seeded at `Corr prog … { locals := fun _ => none, world := w₀ } fr₀ prog.entry 0`
— `Corr` at the *entry block's body cursor* `(prog.entry, 0)`, whose pc is
`pcOf prog prog.entry 0 = offsetTable … prog.entry.idx + 1`: one byte *past* the entry block's
leading `JUMPDEST`. The top-level entry frame `fr₀ = codeFrame p (lower prog)`, however, sits at
pc `0` — *on* that `JUMPDEST` (when the entry block is block 0, `offsetTable … 0 = 0`). So the
entry `Corr` is reached by the single leading-`JUMPDEST` step, exactly as a `jump`/`branch` edge
lands on a successor block's `JUMPDEST` and steps it (`corr_at_jumpdest_landing`).

`entry_corr` discharges the former `hentry` hypothesis from:

* the entry block being block `0` (`prog.entry.idx = 0`, so its `JUMPDEST` is at byte 0 = the
  codeFrame's pc) and present (`blockAt prog prog.entry = some bentry`);
* the *genuine* entry-frame realisability tie — `StorageAgree` between `w₀` and the entry
  frame's storage lens (the IR initial world *is* the accounts the run uses). (There is NO
  entry-frame gas/sload universal anymore: both are spilled, their values live in memory slots
  tied by `MemRealises` at the def-sites — Phase B/C.)
* the `Gjumpdest` gas margin.

The structural `Corr` clauses (code / pc / stack / canModifyState) are read off `codeFrame`
mechanically; `DefsSound`/`wellScoped` are vacuous at the empty-locals entry state
(`defsSound_entry`). -/

/-- **The entry frame field reductions.** `codeFrame p (lower prog)` runs `lower prog` at pc 0
with an empty stack, the modifiable flag of `p`, gas `p.gas`, validJumps `validJumpDests (lower
prog) 0`, and a `.call`-kind. (All `rfl` off the `codeFrame`/`codeEnv` definitions.) -/
theorem codeFrame_pc (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.pc = 0 := rfl

theorem codeFrame_stack (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.stack = [] := rfl

theorem codeFrame_code (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.executionEnv.code = code := rfl

theorem codeFrame_canMod (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.executionEnv.canModifyState = p.canModifyState := rfl

theorem codeFrame_gas (p : CallParams) (code : ByteArray) :
    (codeFrame p code).exec.gasAvailable = p.gas := rfl

theorem codeFrame_validJumps (p : CallParams) (code : ByteArray) :
    (codeFrame p code).validJumps = validJumpDests code 0 := rfl

/-! ### Discharging the entry STORAGE tie definitionally

`entry_corr`'s `hstore : StorageAgree { …, world := w₀ } (codeFrame p (lower prog))` ties the
IR initial world `w₀` to the entry frame's self-storage lens. In `lower_conforms`/
`lower_conforms_acyclic` the world `w₀` is **universally quantified** (a free choice), so this
tie is not a runtime fact — it is *definitional*: choosing `w₀ := selfStorage (codeFrame …)`
makes `StorageAgree` hold by `rfl`. The lemma below records that canonical choice, banking the
`hstore` entry tie (the only entry-frame tie not intrinsic to the recording — `hsload`/`hgasr`
constrain *every* same-address frame's warmth/gas, the supplied-observation correspondence,
and so stay genuine). -/

/-- **The entry STORAGE tie, definitionally.** Taking the IR initial world to be the entry
frame's own self-storage lens (`selfStorage (codeFrame p code)`) discharges `StorageAgree` by
reflexivity. The canonical `w₀` choice for the entry-frame storage tie. -/
theorem entry_storageAgree_codeFrame (p : CallParams) (code : ByteArray) :
    StorageAgree { locals := fun _ => none, world := selfStorage (codeFrame p code) }
      (codeFrame p code) :=
  fun _ => rfl

/-- **`entry_corr` — the entry correspondence.** For an entry block `bentry` that is block `0`
(`prog.entry.idx = 0`) and present, the top-level entry frame `codeFrame p (lower prog)` —
running `lower prog` from pc 0 with empty stack, `p` modifiable — steps its leading `JUMPDEST`
(`runs_jumpdest`) to a frame in `Corr`-correspondence with the empty-locals entry state at
`(prog.entry, 0)`. The genuine ties (`StorageAgree` at the entry frame, and the
`Gjumpdest` margin) are the entry-frame realisability contract; `DefsSound` / `wellScoped` are
vacuous at empty locals. (The gas value channel is now `MemRealises` at the gas def-sites, not
an entry-frame universal — Phase B.) -/
theorem entry_corr {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word} {w₀ : V2.World}
    {p : CallParams} {bentry : Block}
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hgas : GasConstants.Gjumpdest ≤ p.gas.toNat) :
    ∃ fr₀, Runs (codeFrame p (lower prog)) fr₀
      ∧ Corr prog sloadChg obs { locals := fun _ => none, world := w₀ } fr₀ prog.entry 0 := by
  set fe := codeFrame p (lower prog) with hfe
  -- the entry block sits at offset 0 (it is block 0), so the codeFrame's pc (= 0) is its
  -- leading `JUMPDEST` byte.
  have hbtl : prog.blocks.toList[prog.entry.idx]? = some bentry := by
    have : blockAt prog prog.entry = prog.blocks.toList[prog.entry.idx]? := by
      unfold blockAt; rw [Array.getElem?_toList]
    rwa [this] at hbentry
  have hoff0 : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx = 0 := by
    unfold offsetTable; rw [hentry0]; simp
  -- pc of the codeFrame is `UInt32.ofNat (offsetTable … entry.idx)` (= 0).
  have hpc : fe.exec.pc
      = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx) := by
    rw [hfe, codeFrame_pc, hoff0]; rfl
  have hcode : fe.exec.executionEnv.code = lower prog := by rw [hfe, codeFrame_code]
  have hvalid : fe.validJumps = validJumpDests fe.exec.executionEnv.code 0 := by
    rw [hfe, codeFrame_validJumps, codeFrame_code]
  have hstk : fe.exec.stack = [] := by rw [hfe, codeFrame_stack]
  have hcanmod : fe.exec.executionEnv.canModifyState = true := by rw [hfe, codeFrame_canMod, hmod]
  have hstore' : ∀ k, selfStorage fe k = ({ locals := fun _ => none, world := w₀ } : V2.IRState).world k :=
    hstore
  -- the leading-`JUMPDEST` decode at the entry offset.
  have hdec : decode fe.exec.executionEnv.code fe.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    rw [hcode, hpc]; exact decode_at_block_offset_jumpdest prog prog.entry bentry hbtl hbound
  have hgas' : GasConstants.Gjumpdest ≤ fe.exec.gasAvailable.toNat := by rw [hfe, codeFrame_gas]; exact hgas
  obtain ⟨hjdrun, hjdcorr⟩ :=
    corr_at_jumpdest_landing (st := { locals := fun _ => none, world := w₀ }) hbtl hpc hcode hvalid
      hstk hcanmod hstore' (defsSound_entry prog w₀) (by intro t ht; simp at ht)
      (by intro t slot v _ hloc; simp at hloc) hdec hgas'
  exact ⟨jumpdestFrame fe, hjdrun, hjdcorr⟩

/-! ## `lower_conforms` — tying `sim_cfg` to the recording interpreter

The headline. From a successful `runWithLog` over the lowered program, recover:

1. **the IR run** — `IRRun prog (realisedGas log) (realisedCall log self) w₀ O` for *some*
   observable `O`. We do **not** synthesise the `RunFrom` derivation from the bytecode
   (`runWithLog` records the *bytecode* trace, not the IR one); instead we carry the IR run as
   a structured hypothesis (`hir`) — the **IR side** of the conformance diagram, supplied for
   the program under study and itself the subject of the IR-determinism / supplied-observation
   contract (`docs/ir-design-v3.md` §7). This is the honest realisability hypothesis: the IR
   run *under the realised oracles* the bytecode produces.
2. **the world equation** — `O.world = (observe self log.observable).world`. This is the
   load-bearing conformance edge, and it is **fully discharged** here from `sim_cfg`:
   `runWithLog_messageCall` pins `messageCall = .ok log.observable.toCallResult`; `sim_cfg` +
   `messageCall_runs` pins `messageCall = .ok (toCallResult (endFrame last haltSig))`; equating
   the two `toCallResult`s (`observe` reads only `.toCallResult`) gives `observe self
   log.observable = observe self (endFrame last haltSig)`, whose world is `O.world` by
   `sim_cfg` and `IRRun.det`.

The former entry `Corr` hypothesis is now **discharged** in-proof by `entry_corr` (the
leading-`JUMPDEST` step from the top-level frame), so `lower_conforms` no longer carries it:
its replacements are the structural entry facts (`hentry0`/`hbentry`/`hbound` — the entry block
is block 0, present, pc-bounded) plus the *genuine* entry-frame realisability ties
(`hstore`/`hsload`/`hgasr`/`hgasj`). The per-block simulations (`hstmts`/`hterm`) and the IR
run (`hir`) remain the carried structured hypotheses — the supplied-observation realisability
contract (`hstmts`/`hterm` are themselves now dischargeable per shape by `simStmtStep_block`
/ `simTermStep_block`, down to the per-cursor genuine ties — including the §7 `CallRealises`
tie for `.call` — and the per-shape decode bundles). `runWithLog` at the seed fuel makes the
`messageCall` bridge exact. There is **no** call-free side condition: the call statement is
folded into the spine via `sim_call_stmt` (Route B). -/

/-- **`lower_conforms` (general over calls, world channel — under the realisability contract).**
For a program `prog`, initial world `w₀`, self address `self`, observable IR run `O` and run log
`log`: if the recording run `runWithLog p (seedFuel p.gas)` over the top-level params `p`
succeeds with `log`, where `p` is a top-level
`.Code (lower prog)` modifiable call (`hp`/`hmod`), the entry block is block 0 and present
(`hentry0`/`hbentry`/`hbound`), the genuine entry-frame realisability ties hold
(`hstore`/`hsload`/`hgasr`/`hgasj`), the per-block simulations (`hstmts`/`hterm`) hold, and the
IR runs under the realised oracles to `O` (`hir`), then **the IR observable's world equals the
`observe` world of the recorded bytecode result**:

  `O.world = (observe self log.observable).world`.

The world edge is fully discharged from `sim_cfg` + the `messageCall` bridge + `IRRun.det`; the
IR run itself and the per-block realisability are the carried hypotheses (the §7
supplied-observation contract). -/
theorem lower_conforms {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {O : V2.Observable} {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    -- the recording run succeeded over the lowered program at the seed fuel:
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    -- the lowered program is entered as a top-level `.Code (lower prog)` call; `p` may modify
    -- state:
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    -- the entry block is block 0 (its leading `JUMPDEST` is at byte 0 = the entry frame's pc),
    -- present, and the program fits a 32-bit pc:
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    -- the GENUINE entry-frame realisability ties (the §7 supplied-observation contract at the
    -- entry frame): the IR initial world `w₀` is the entry frame's storage lens, and the entry
    -- SLOAD-warmth observation holds; plus the `Gjumpdest` gas margin. (The gas value channel is
    -- now `MemRealises` at the gas def-sites — there is NO entry-frame gas universal, Phase B.)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ }
                (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    -- the honest non-exception scope boundary: the entry code frame's run reaches a
    -- `.success`/`.revert` terminal (not a genuine OOG/exception, which the gas-agnostic IR cannot
    -- model). This is what lets `sim_cfg`'s per-cursor §7 ties DERIVE their gas/mem envelopes.
    (hcs : CleanHaltsNonException (codeFrame p (lower prog)))
    -- the per-block simulations (the realisability contract over `lower prog`):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs (realisedCall log self) L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs (realisedCall log self) self L b)
    -- the IR run under the realised oracles (the IR side of the conformance diagram):
    (hir : V2.IRRun prog (realisedCall log self) w₀ (realisedGas log) O) :
    O.world = (observe self log.observable).world := by
  -- the lowered program enters as code from `codeFrame p (lower prog)` (`beginCall_code`).
  have hbegin : EntersAsCode p (codeFrame p (lower prog)) := beginCall_code p (lower prog) hp
  -- `entry_corr`: the leading-`JUMPDEST` step lands the entry frame in `Corr` at `(entry, 0)`.
  obtain ⟨fr₀, hjdruns, hentry⟩ :=
    entry_corr (sloadChg := sloadChg) (obs := obs) (w₀ := w₀) hmod hentry0 hbentry hbound
      hstore hgasj
  -- forward the entry clean-halt across the leading `JUMPDEST` to the `Corr` entry frame `fr₀`.
  have hcs₀ : CleanHaltsNonException fr₀ := cleanHaltsNonException_forward hcs hjdruns
  -- `sim_cfg`: from the entry `Corr`, the lowered run halts with world = O.world.
  obtain ⟨last, haltSig, hruns, hhalt, hworld⟩ :=
    sim_cfg (self := self) hstmts hterm hentry hcs₀ hir
  -- the `messageCall` bridge, two ways: the assembled `Runs` halt (entry JUMPDEST then the CFG
  -- run), and the recorder.
  have hmc_runs : messageCall p = .ok (FrameResult.toCallResult (endFrame last haltSig)) :=
    messageCall_runs p hbegin (hjdruns.trans hruns) hhalt
  have hmc_log : messageCall p = .ok log.observable.toCallResult :=
    runWithLog_messageCall hwl
  -- equate the two recorded results' `toCallResult`s.
  have htcr : log.observable.toCallResult = FrameResult.toCallResult (endFrame last haltSig) := by
    rw [hmc_log] at hmc_runs; exact Except.ok.inj hmc_runs
  -- `observe`'s world reads only `.toCallResult.accounts`, so the two `observe` worlds agree.
  have hobs : (observe self log.observable).world
      = (observe self (endFrame last haltSig)).world := by
    funext key
    show resultStorageAt log.observable self key
      = resultStorageAt (endFrame last haltSig) self key
    unfold resultStorageAt
    rw [htcr]
  rw [hobs, hworld]

/-- `prog.blocks.toList[L.idx]? = some b` from `blockAt prog L = some b` (the reverse of
`blockAt_of_toList`). -/
theorem toList_of_blockAt {prog : Program} {L : Label} {b : Block}
    (hbat : blockAt prog L = some b) : prog.blocks.toList[L.idx]? = some b := by
  have : blockAt prog L = prog.blocks.toList[L.idx]? := by
    unfold blockAt; rw [Array.getElem?_toList]
  rwa [this] at hbat

end Lir
