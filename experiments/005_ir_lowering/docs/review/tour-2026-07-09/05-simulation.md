# 05 — Simulation & CFG simulation: `LirLean/Sim/` + `LirLean/CfgSim/`

Part of the [exp005 tour](00-overview.md).
Upstream inputs: [01-trusted-base](01-trusted-base.md) (exp003 `Runs`/Hoare bricks + `Engine/` theory), [03-code-geometry](03-code-geometry.md) (the `Decode/` byte-layout algebra), [04-value-channel](04-value-channel.md) (`Materialise/`+`Frame/`: `MatRunsC`, `MemRealises`, `StashTail`, clean-halt extractors). Downstream consumer: [06-realisability](06-realisability.md) (Drive + Realisability, the `lower_conforms` flagships).

**Scope.** All five files: [`Sim/SimStmt.lean`](../../../LirLean/Sim/SimStmt.lean) (1150 LOC), [`Sim/SimStmts.lean`](../../../LirLean/Sim/SimStmts.lean) (164), [`Sim/SimTerm.lean`](../../../LirLean/Sim/SimTerm.lean) (843), [`CfgSim/LowerConforms.lean`](../../../LirLean/CfgSim/LowerConforms.lean) (1127), [`CfgSim/LowerDecode.lean`](../../../LirLean/CfgSim/LowerDecode.lean) (1069).

---

## TL;DR

This layer is the **forward simulation core** of exp005: the between-statements invariant [`Corr`](../../../LirLean/Sim/SimStmt.lean#L102) relating a V2 IR state to an EVM frame, one proved simulation arm per IR statement/terminator shape (Layers C/E), the statement-list glue (Layer D), and the cycle-agnostic whole-CFG induction [`sim_cfg`](../../../LirLean/CfgSim/LowerConforms.lean#L938) (Layer F). All five files sit in the default sorry-free build cone; grep confirms zero `sorry`/`admit`/`native_decide`/`bv_decide` in scope, and [`Audit.lean`](../../../LirLean/Audit.lean#L45) build-pins the axiom footprint of the deepest wrapper at `[propext, Classical.choice, Quot.sound]` (build green: reported, not re-run).

The honest status is two-sided. The **C/E-layer arms and the low-level decode dischargers are live and load-bearing** — the closed flagship [`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L222) consumes `Corr`, the accessor/emit lemmas, and helpers like [`decode_gasstash`](../../../LirLean/CfgSim/LowerDecode.lean#L632) and [`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503) directly. But the **builder half of `CfgSim/` is superseded scaffolding with zero term-level callers**: [`simStmtStep_block`](../../../LirLean/CfgSim/LowerConforms.lean#L337), [`simTermStep_block`](../../../LirLean/CfgSim/LowerConforms.lean#L799), [`entry_corr`](../../../LirLean/CfgSim/LowerConforms.lean#L1063) and the [`CallRealises`](../../../LirLean/CfgSim/LowerConforms.lean#L235) tie feed only `sim_cfg` → the uncalled [`lower_conforms_cyclic'`](../../../LirLean/Drive/DriveSim.lean#L661) endpoint, because two of their supplied seam shapes ([`SstoreRealises`](../../../LirLean/Sim/SimStmt.lean#L317)'s ∀-frames form; `CallRealises`'s embedded `StepScoped`) are not producible from a real run — the flagship re-implements the walk with coupling-aware point-wise variants instead (§Two paths, verified against current source below).

---

## 1. Where this sits in the stack

```
Layer A/B  Decode/ (03) + Materialise/ (04)      decode anchors, MatDecC, MatRunsC, MemRealises, StashTail
Layer C    Sim/SimStmt.lean                      Corr + one arm per statement shape
Layer D    Sim/SimStmts.lean                     SimStmtStep abstraction + statement-list induction
Layer E    Sim/SimTerm.lean                      terminator halt/edge arms
Layer F    CfgSim/LowerConforms.lean             SimTermStep, WellFormedLowered, CallRealises,
                                                 builders, sim_cfg, entry_corr
   (F aux) CfgSim/LowerDecode.lean               decode-discharge (`_lowered`) wrappers + PUSH4 round-trips
Consumers  Drive/DriveSim.lean (superseded path) and Realisability/* (flagship path) — see 06
```

| File | Role | One-line verdict |
|---|---|---|
| [`Sim/SimStmt.lean`](../../../LirLean/Sim/SimStmt.lean) | `Corr` + arms `sim_assign`/`sim_sstore_stmt`/`sim_call_stmt`/`sim_assign_gas`/`sim_assign_sload` + frame-accessor reductions | live; heart of the layer |
| [`Sim/SimStmts.lean`](../../../LirLean/Sim/SimStmts.lean) | `SimStmtStep` + `sim_stmts_drop`/`sim_stmts`/`sim_stmts_block` | live via DriveSim; flagship re-implements a coupled twin |
| [`Sim/SimTerm.lean`](../../../LirLean/Sim/SimTerm.lean) | halt arms (`stop`/`ret`), edge arms (`jump`/`branch`), shared landing/`jump_to_block` tails | mixed: landing/edge sub-lemmas live in flagship; top arms feed the builder path |
| [`CfgSim/LowerConforms.lean`](../../../LirLean/CfgSim/LowerConforms.lean) | tie units (`SimTermStep`, `WellFormedLowered`, `CallRealises`), builders, `sim_cfg`, `entry_corr` | `WellFormedLowered` live; builders + `sim_cfg` + `entry_corr` currently caller-less |
| [`CfgSim/LowerDecode.lean`](../../../LirLean/CfgSim/LowerDecode.lean) | discharges the arms' decode hypotheses generically over `lower prog` | low-level helpers live in flagship; `_lowered` arm wrappers only feed the builders |

**Folder charter (reviewer Q5).** `CfgSim/` names the role directly: these modules compose
per-block proof ties and simulate the CFG; they do not assemble bytes. Byte emission remains in
[`emitStmt`](../../../LirLean/Spec/Lowering.lean#L114), [`emitTerm`](../../../LirLean/Spec/Lowering.lean#L158),
and [`lower`](../../../LirLean/Spec/Lowering.lean#L186). The separate planned assembler layer is
described in [07-assembler](07-assembler.md).

---

## 2. The `Corr` invariant (reviewer Q1)

The heart of "what must hold between IR state and EVM frame at every statement boundary" — [`Corr`](../../../LirLean/Sim/SimStmt.lean#L102), quoted whole:

```lean
structure Corr (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : Lir.IRState) (fr : Frame) (L : Label) (pc : Nat) : Prop where
  /-- `M1` — program counter at the offset-table address of cursor `(L, pc)`. -/
  pc_eq      : fr.exec.pc = UInt32.ofNat (pcOf prog L pc)
  /-- `M2` — the frame runs the lowered program. -/
  code_eq    : fr.exec.executionEnv.code = lower prog
  /-- `M2′` — the frame's recorded jump destinations are those of its own code. This is
  a frame-invariant: `validJumps` is set once at frame creation from `code` (`codeFrame`)
  and every non-call step preserves both fields together. Combined with `code_eq` it
  discharges the `validJumps = validJumpDests (lower prog) 0` control-flow ties
  structurally (see `Corr.validJumps_lower`). -/
  validJumps_eq : fr.validJumps = validJumpDests fr.exec.executionEnv.code 0
  /-- `M5` — empty working stack at the statement boundary. -/
  stack_nil  : fr.exec.stack = []
  /-- Standing well-formedness: the call may modify state (top-level call). -/
  can_modify : fr.exec.executionEnv.canModifyState = true
  /-- `M3` — storage correspondence through the observable lens. -/
  storage    : StorageAgree st fr
  /-- B3 — recompute-on-use soundness. -/
  defsSound  : DefsSound prog st
  /-- Define-before-use scoping: every currently-bound tmp is either recomputable or a
  call result registered in the recompute env, and present in it (the `WellScoped` content
  `materialise_runs` consumes — relaxed to admit the memory value channel). -/
  wellScoped : ∀ t, st.locals t ≠ none →
    (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
    ∧ defsOf prog t ≠ none
  /-- The memory value channel: the frame's memory realises the IR's bound spilled locals
  (coverage + readback value at each gas/sload/call-result slot). … -/
  memAgree   : MemRealises prog st fr
```

Field-by-field gloss, split as the reviewer asked:

**Geometry (pins the frame to the code layout):**
- `pc_eq` — the frame's pc is exactly the offset-table address [`pcOf`](../../../LirLean/Decode/Layout.lean#L227)` prog L pc` of statement cursor `(L, pc)` (prefix sum of `emitStmt` byte lengths over `b.stmts.take pc`). Advanced per statement via [`pcOf_succ`](../../../LirLean/Sim/SimStmt.lean#L78).
- `code_eq` — the frame executes [`lower prog`](../../../LirLean/Spec/Lowering.lean#L186), nothing else.
- `validJumps_eq` — a frame invariant: `validJumps` tracks the frame's own code. Combined with `code_eq`, [`Corr.validJumps_lower`](../../../LirLean/Sim/SimStmt.lean#L140) yields `fr.validJumps = validJumpDests (lower prog) 0` — this *structurally* retired the old `TermTies` validJumps-recording ties (one of the vacuity sources the 2026-07-02 audit flagged).
- `stack_nil` (M5) — the working stack is empty between statements. This is the whole design bet of the recompute/spill lowering: every arm ends with `stack = []`, so the induction threads with no stack-shape bookkeeping.

**Semantic (relates IR state to machine state):**
- `can_modify` — standing top-level-CALL fact (SSTORE needs the mutable flag).
- `storage` — [`StorageAgree`](../../../LirLean/Materialise/MaterialiseRuns.lean#L326): `selfStorage fr key = st.world key` for all keys, the shared `find?/lookupStorage` lens.
- `defsSound` — [`DefsSound`](../../../LirLean/Materialise/DefsSound.lean#L209) (B3): every bound *recomputable* tmp still evaluates, under the current world, to its bound value (soundness of recompute-on-use).
- `wellScoped` — every bound tmp is recomputable or spilled ([`NonRecomputable`](../../../LirLean/Materialise/DefsSound.lean#L127) ⇒ has a `.slot` in [`defsOf`](../../../LirLean/Spec/Lowering.lean#L56)), and is registered.
- `memAgree` — [`MemRealises`](../../../LirLean/Materialise/MaterialiseRuns.lean#L366): each bound spilled local's 32-byte slot is covered by memory/`activeWords` and MLOADs back to exactly the bound value. This positional channel is what replaced *both* vacuous universals (`GasRealises`, `SloadRealises`) in Phases B/C.

One structural oddity worth noting: **`sloadChg` and `obs` are phantom parameters of `Corr`** — no clause mentions them. They only index the arms' downstream `chargeCache`/`evalExpr` calls uniformly. Harmless, but a candidate simplification.

---

## 3. Layer C — the per-statement arms (reviewer Q2)

All arms share one contract: from `Corr … st fr L pc`, an [`EvalStmt`](../../../LirLean/Spec/Semantics.lean#L48) step, and the statement's honest runtime ties, produce `∃ fr', Runs fr fr' ∧ Corr … st' fr' L (pc+1) ∧ fr'.exec.stack = []` — where [`Runs`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L140) is exp003's reflexive-transitive step relation. The cursor advance is [`pcOf_succ`](../../../LirLean/Sim/SimStmt.lean#L78):

```lean
theorem pcOf_succ (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s) :
    pcOf prog L (pc + 1)
      = pcOf prog L pc + (emitStmt (matCache prog) (defsOf prog) s).length
```

### 3.1 `sim_assign` — rematerialised assign ([`SimStmt.lean#L198`](../../../LirLean/Sim/SimStmt.lean#L198))

A non-spilled `assign t e` emits **no bytes** ([`emitStmt_assign_remat`](../../../LirLean/Sim/SimStmt.lean#L149)), so the machine segment is `Runs.refl`:

```lean
theorem sim_assign {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : Lir.IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
    {t : Tmp} {e : Expr}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t e))
    (hremat : ∀ n, defsOf prog t ≠ some (.slot n))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hstep : EvalStmt prog st T C D (.assign t e) st' T' C' D')
    (hsc : StepScoped prog st (.assign t e))
    (hscoped' : ∀ t, st'.locals t ≠ none → …)
    (hmem' : MemRealises prog st' fr) :
    Runs fr fr ∧ Corr prog sloadChg obs st' fr L (pc + 1) ∧ fr.exec.stack = []
```

The content is invariant re-establishment: world untouched, `DefsSound` survives via B3 preservation (proof: case split on the step + record rebuild). `hscoped'`/`hmem'` are the standard downstream-supplied post-state ties (same pattern as `materialise_runsC`).

### 3.2 `sim_sstore_stmt` ([`SimStmt.lean#L347`](../../../LirLean/Sim/SimStmt.lean#L347))

Lowering `matCache value ++ matCache key ++ [SSTORE]`; two fold value-channel calls glued by `Runs.trans`, then exp003-side [`sim_sstore`](../../../LirLean/Frame/Match.lean#L219):

```lean
theorem sim_sstore_stmt {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : Lir.IRState} {key value : Tmp} {kw vw : Word}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame} {acc : Account}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hk : st.locals key = some kw) (hv : st.locals value = some vw)
    (hsc : StepScoped prog st (.sstore key value))
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (hdv : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc (.tmp value))
    (hdk : MatDecC prog hdc hord fr.exec.executionEnv.code
            (fr.exec.pc + UInt32.ofNat (matCache prog value).length) (.tmp key))
    (hdop : decode fr.exec.executionEnv.code
            (fr.exec.pc + UInt32.ofNat (matCache prog value).length
              + UInt32.ofNat (matCache prog key).length)
            = some (.Smsf .SSTORE, .none))
    (hcs : CleanHaltsNonException fr)
    (hstk : (chargeCache prog sloadChg value).length
              + (chargeCache prog sloadChg key).length + 1 ≤ 1024)
    (hsstore : SstoreRealises fr kw vw acc) :
    ∃ fr', Runs fr fr'
      ∧ Corr prog sloadChg obs (st.setStorage kw vw) fr' L (pc + 1)
      ∧ fr'.exec.stack = []
```

Notable design points: the operand gas envelopes are **derived, not supplied** — the clean-halt witness [`CleanHaltsNonException`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L62) is fed to [`materialise_runsC_of_cleanHalt`](../../../LirLean/Materialise/MaterialiseCleanHalt.lean#L372) twice (value at `fr`, key at the intermediate frame, forwarded via [`cleanHaltsNonException_forward`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean#L80)). The remaining runtime seam is [`SstoreRealises`](../../../LirLean/Sim/SimStmt.lean#L317):

```lean
def SstoreRealises (fr : Frame) (kw vw : Word) (acc : Account) : Prop :=
  ∀ (g : Frame),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    g.exec.stack = kw :: vw :: [] →
    (¬ g.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    ∧ sstoreChargeOf g.exec kw vw ≤ g.exec.gasAvailable.toNat
    ∧ g.exec.accounts.find? g.exec.executionEnv.address = some acc
```

**Flag (load-bearing).** This is a ∀-over-frames shape: it demands the stipend/charge/presence facts of *every* frame sharing the self-address and stack shape — including frames the real run never visits. The flagship's coupled twin [`sim_sstore_stmt'`](../../../LirLean/Realisability/Producer.lean#L1036) calls it, verbatim, "the **unsatisfiable** `∀`-quantified `hsstore`" and replaces it with a point-wise derivation at the actual internal SSTORE frame (`sstoreRealises_at_frame`, from `SelfPresent` + clean-halt). As a *hypothesis of a consumed lemma* it is sound; as a *producible tie* it is dead — this is exactly why the builder path below has no producer. No headline currently depends on `SstoreRealises` being produced.

### 3.3 `sim_call_stmt` — the call arm ([`SimStmt.lean#L579`](../../../LirLean/Sim/SimStmt.lean#L579), reviewer Q2 centrepiece)

Route-B lowering: `5×(PUSH 0) ++ matCache callee ++ matCache gasFwd ++ [CALL] ++ tail`, where the tail is `PUSH32 slotOf t; MSTORE` (result bound) or `POP` (dropped). The CALL becomes a `Runs.call` node via exp003-side [`sim_call`](../../../LirLean/Frame/Match.lean#L433) carrying a [`CallReturns`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L91) witness. Statement quoted whole (it *is* the hypothesis ledger):

```lean
theorem sim_call_stmt {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : Lir.IRState} {cs : CallSpec}
    {L : Label} {b : Block} {pc : Nat} {argsLen : Nat}
    {fr callFr resumeFr : Frame} {result : Evm.CallResult} {pd : Evm.PendingCall}
    {self : AccountAddress}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.call cs))
    (hfrpc : fr.exec.pc = UInt32.ofNat (pcOf prog L pc))
    (hargslen : argsLen
      = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ matCache prog cs.callee ++ matCache prog cs.gasFwd).length)
    (hargs : Runs fr callFr)
    (hcallpc : callFr.exec.pc = fr.exec.pc + UInt32.ofNat argsLen)
    (hcallmem : callFr.exec.toMachineState.memory = fr.exec.toMachineState.memory)
    (hcallactive : fr.exec.toMachineState.activeWords.toNat
      ≤ callFr.exec.toMachineState.activeWords.toNat)
    (hcall : CallReturns callFr resumeFr)
    (hresume : resumeFr = Evm.resumeAfterCall result pd)
    (hst' : st' = (match cs.resultTmp with
        | some t => { st with world := fun key => evmCallOracle.postStorage result pd self key }.setLocal
                      t (callSuccessFlag result pd)
        | none   => { st with world := fun key => evmCallOracle.postStorage result pd self key }))
    (hresaddr : resumeFr.exec.executionEnv.address = self)
    (hrescode : resumeFr.exec.executionEnv.code = lower prog)
    (hrescanmod : resumeFr.exec.executionEnv.canModifyState = true)
    (hrespc : resumeFr.exec.pc = callFr.exec.pc + 1)
    (hresstack : resumeFr.exec.stack = callSuccessFlag result pd :: [])
    (hresmem : resumeFr.exec.toMachineState.memory = callFr.exec.toMachineState.memory)
    (hresactive : callFr.exec.toMachineState.activeWords.toNat
      ≤ resumeFr.exec.toMachineState.activeWords.toNat)
    (hresvalidjumps : resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0)
    (hdefs : DefsSound prog st)
    (hsc : StepScoped prog st (.call cs))
    (hmem : MemRealises prog st fr)
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    (hscoped' : ∀ t, st'.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (htail : ∀ flag : Word, resumeFr.exec.stack = flag :: [] →
      (∀ (t : Tmp), cs.resultTmp = some t →
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr, StashRuns resumeFr endFr (slotOf t) flag 34 [])
      ∧ (cs.resultTmp = none →
          Runs resumeFr (popFrame resumeFr []))) :
    ∃ endFr, Runs fr endFr ∧ Corr prog sloadChg obs st' endFr L (pc + 1)
      ∧ endFr.exec.stack = []
```

**Hypothesis count from current source: 25** (named hypotheses `hb`…`htail`; the [codebase map](../../codebase-map-2026-07-06.md) says "25 hyps (verified)"; the older [cluster-sim deep-dive](../../deepdive-2026-07-04/cluster-sim.md) still says 28 — stale, see §7). Honest seams-vs-plumbing split:

| Class | Hypotheses (count) | Verdict |
|---|---|---|
| **Genuine oracle seam** — the irreducible external-call observation | `hcall` (`CallReturns`), `hresume` (resume = [`resumeAfterCall`](../../../../003_bytecode_layer/EVMLean/Evm/Semantics/Call.lean#L122)` result pd`), `hst'` (IR post-state = the recorded [`evmCallOracle`](../../../LirLean/Frame/Call.lean#L108)/[`callSuccessFlag`](../../../LirLean/Frame/Call.lean#L120) effect) (3) | The real seam. In the flagship these come from the recorder log's positional call-stream head (`realisedCall_cons` + `recorderCoupled_call_extract`, Piece A of R3 — landed). |
| **Genuine machine-run obligation** — the arg-push prefix | `hargs`, `hcallpc`, `hcallmem`, `hcallactive` (4) | Honest but *currently has no producer anywhere in tree*: [`callRealises_of_recorded`](../../../LirLean/Realisability/Machinery.lean#L392)'s docstring names this exactly ("In-tree this run is only ever SUPPLIED to `sim_call_stmt` …; no producing lemma exists" — R3 Piece B, the open blocker). Constructible in principle from `Corr` + the decode layout (the precedent is the branch cond driver in LowerDecode). |
| **Route-B tail** | `htail` (1) | Genuine but mechanically dischargeable via [`stash_tail_runs`](../../../LirLean/Materialise/StashTail.lean#L157) ([`StashRuns`](../../../LirLean/Materialise/MaterialiseRuns.lean#L217) is the named endpoint bundle) — exactly what the gas/sload arms' `_lowered` wrappers already do. |
| **Derivable `resumeAfterCall` projections** | `hresaddr`, `hrescode`, `hrescanmod`, `hrespc`, `hresstack`, `hresmem`, `hresactive`, `hresvalidjumps` (8) | Mostly `rfl`-level projections of `hresume` (e.g. `resumeAfterCall_stack` is proved `rfl` in Machinery). Two carry real content: `hresstack` embeds the empty-boundary collapse `pd.stack = []`, `hresmem` the zero-in/out-window memory preservation. Absorbable once bytecode-layer computation lemmas about `resumeAfterCall` exist (flagged in Machinery as exp003-side work). |
| **Exploded-`Corr` plumbing** | `hfrpc`, `hdefs`, `hmem` (3) | Interface unevenness: unlike every sibling arm, `sim_call_stmt` takes `Corr`'s fields exploded instead of `hcorr : Corr …`. Pure refactor. |
| **Cursor/structural plumbing** | `hb`, `hs`, `hargslen`, `hslots`, `hsc`, `hscoped'` (6) | `hargslen` is definitional; `hslots` is [`WellFormedLowered.slots_slot`](../../../LirLean/CfgSim/LowerConforms.lean#L182); `hsc`/`hscoped'` are the standard scoping ties. |

The `memAgree` re-establishment is the arm's real content: the freshly bound result slot reads back the flag ([`mstore_reads_back`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L713)), and every other bound slot survives the disjoint MSTORE ([`slot_windows_disjoint`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L872) on [`slotOf`](../../../LirLean/Spec/Lowering.lean#L39)`= t.id * 32`, [`mstore_preserves_slot_grow`](../../../../003_bytecode_layer/BytecodeLayer/Hoare/MemAlgebra.lean#L919)). Proof method: direct frame-chain assembly + record rebuild; no induction.

### 3.4 `sim_assign_gas` / `sim_assign_sload` — the spill arms

[`sim_assign_gas`](../../../LirLean/Sim/SimStmt.lean#L880) (Phase B): a gas-defined tmp is spilled by `[GAS] ++ PUSH32 slot ++ MSTORE`; the value tie is *positional* — the IR binds exactly the one realised `GAS` read:

```lean
theorem sim_assign_gas {prog : Program} {sloadChg : Tmp → ℕ} {obs ob : Word}
    {st : Lir.IRState} {t : Tmp}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t .gas))
    (hslotdef : defsOf prog t = some (.slot (slotOf t)))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hsc : StepScoped prog st (.assign t .gas))
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    (hscoped' : ∀ t', (st.setLocal t ob).locals t' ≠ none → …)
    (hstash :
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr, StashRuns fr endFr (slotOf t) ob
            (emitStmt (matCache prog) (defsOf prog) (.assign t .gas)).length []) :
    ∃ endFr, Runs fr endFr ∧ Corr prog sloadChg obs (st.setLocal t ob) endFr L (pc + 1)
      ∧ endFr.exec.stack = []
```

[`sim_assign_sload`](../../../LirLean/Sim/SimStmt.lean#L1030) (Phase C) is the exact twin for `assign t (.sload k)` (stash `matCache k ++ [SLOAD] ++ PUSH32 slot ++ MSTORE`, bound value = the loaded word `w`, warmth charged once at the def-site). Both take the stash run as a `StashRuns` bundle — deliberately over the honest `.memory`-bytes + `activeWords` channel, *not* full `toMachineState` equality (the stash drops gas, so the full equality would be unsatisfiable — a lesson the docstring records). Their `hstash` is **not left to callers**: the `_lowered` wrappers in LowerDecode construct it (§5).

---

## 4. Layers D/E — list glue and terminators (reviewer Q2 cont.)

### 4.1 `SimStmtStep` and `sim_stmts_block`

The per-statement ties are per-cursor and per-intermediate-state, so they cannot be stated once up front of a list induction. [`SimStmtStep`](../../../LirLean/Sim/SimStmts.lean#L66) abstracts Layer C's conclusion at exactly its altitude:

```lean
def SimStmtStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (L : Label) (b : Block) : Prop :=
  ∀ (pc : Nat) (s : Stmt) (st0 st0' : Lir.IRState) (T0 T0' : Trace) (C0 C0' : CallStream)
    (D0 D0' : CreateStream) (fr0 : Frame),
    b.stmts[pc]? = some s →
    Corr prog sloadChg obs st0 fr0 L pc →
    CleanHaltsNonException fr0 →
    EvalStmt prog st0 T0 C0 D0 s st0' T0' C0' D0' →
    ∃ fr0', Runs fr0 fr0' ∧ Corr prog sloadChg obs st0' fr0' L (pc + 1)
      ∧ fr0'.exec.stack = []
```

[`sim_stmts_block`](../../../LirLean/Sim/SimStmts.lean#L150) (via the general suffix form [`sim_stmts_drop`](../../../LirLean/Sim/SimStmts.lean#L91), induction on [`RunStmts`](../../../LirLean/Spec/Semantics.lean#L82) generalising cursor+frame; the clean-halt witness is forwarded across each head segment):

```lean
theorem sim_stmts_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : Lir.IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
    {L : Label} {b : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hcs : CleanHaltsNonException fr)
    (hrun : Lir.RunStmts prog st T C D b.stmts st' T' C' D') :
    ∃ fr', Runs fr fr' ∧ Corr prog sloadChg obs st' fr' L b.stmts.length
      ∧ fr'.exec.stack = []
```

Note the **`∀`-quantification inside `SimStmtStep`**: it demands the step conclusion for *every* `Corr`-corresponding `(st0, fr0)` pair at every cursor, not just the ones on the actual run. This is precisely the shape the flagship cannot discharge (its arm conclusions hold only under the recorder-coupling antecedent), and why [`stmtTies'_of_runWithLog`](../../../LirLean/Realisability/Producer.lean#L2488)-style off-run robustness became R10's problem — see [06-realisability](06-realisability.md).

### 4.2 Terminator arms (`SimTerm.lean`)

The terminator cursor coincides with the byte anchor: [`pcOf_eq_termOf`](../../../LirLean/Sim/SimTerm.lean#L86) (`pcOf prog L b.stmts.length = `[`termOf`](../../../LirLean/Decode/DecodeAnchors.lean#L156)` prog L`). The world channel of a halt goes through the `endCall` success-commit bridge [`resultStorageAt_endFrame_success`](../../../LirLean/Sim/SimTerm.lean#L109) (`.call`-kind + non-empty committed accounts ⇒ the finished result's storage lens *is* the frame lens).

**E1 halt arms.** [`sim_term_halt_stop`](../../../LirLean/Sim/SimTerm.lean#L263) — a `STOP` at the terminator cursor halts immediately with both channels matching:

```lean
theorem sim_term_halt_stop … :
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
      ∧ (observe self (endFrame last halt)).world = st.world
      ∧ (observe self (endFrame last halt)).result = .stopped
```

[`sim_term_halt_ret`](../../../LirLean/Sim/SimTerm.lean#L312) is the **full-observable** ret arm — it runs the whole epilogue `matCache t ; PUSH32 0 ; MSTORE ; PUSH32 32 ; PUSH32 0 ; RETURN` itself and proves the *value* channel too (the returned 32-byte window decodes back to the bound word):

```lean
theorem sim_term_halt_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : Lir.IRState} {t : Tmp} {vw : Word}
    {L : Label} {b : Block} {fr : Frame} {self : AccountAddress}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (_hterm : b.term = .ret t)
    (hself : self = fr.exec.executionEnv.address)
    (hv : st.locals t = some vw)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    (hdv : MatDecC prog hdc hord fr.exec.executionEnv.code fr.exec.pc (.tmp t))
    (hgas : (chargeCache prog sloadChg t).sum ≤ fr.exec.gasAvailable.toNat)
    (hstk : (chargeCache prog sloadChg t).length ≤ 1024)
    (hret : ∀ frv : Frame, Runs fr frv → … )
      -- [snip: `hret` = the RETURN-site bundle at the materialise endpoint — 5 epilogue
      --  decodes, 5 gas margins, the MSTORE memory-expansion witness, `.call`-kind +
      --  non-empty accounts; see the link for the 30-line bundle]
    :
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
      ∧ (observe self (endFrame last halt)).world = st.world
      ∧ (observe self (endFrame last halt)).result = .returned vw
```

(The interpreter-side halt brick is [`stepFrame_return_word`](../../../LirLean/Frame/Match.lean#L357); [`observe`](../../../LirLean/Spec/Recorder.lean#L122) decodes the window via `uInt256OfByteArray_toByteArray`.) Note the header docstring of `SimTerm.lean` (lines 27–39, "value channel DEFERRED") describes the *old* scope and contradicts this arm's own docstring and statement — the value channel is proven here now; the module-header paragraph is stale.

**E2 edge arms.** The shared tails: [`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503) (a frame sitting on the successor's `JUMPDEST` byte steps it and re-establishes `Corr` at `(succ, 0)` — entry cursor is [`pcOf_zero`](../../../LirLean/Sim/SimTerm.lean#L492)` = offsetTable + 1`) and [`jump_to_block`](../../../LirLean/Sim/SimTerm.lean#L544) (`PUSH4 dest ; JUMP ; JUMPDEST`, destination resolved through E3's [`block_offset_validJump`](../../../LirLean/Decode/JumpValid.lean#L226) + the frame's `validJumps`). On top:

```lean
theorem sim_term_edge_jump … :
    ∃ fr' L', L' = dst ∧ Runs fr fr' ∧ Corr prog sloadChg obs st fr' L' 0
```

([`sim_term_edge_jump`](../../../LirLean/Sim/SimTerm.lean#L628)), and [`sim_term_edge_branch`](../../../LirLean/Sim/SimTerm.lean#L671) with the cw-tied conclusion that pins the taken successor to the runtime condition:

```lean
    ∃ fr' L', (cw ≠ 0 ∧ L' = thenL ∨ cw = 0 ∧ L' = elseL)
      ∧ Runs fr fr' ∧ Corr prog sloadChg obs st fr' L' 0
```

The branch arm takes the cond materialise as a [`MatRunsC`](../../../LirLean/Materialise/MatFoldChannel.lean#L782) witness and case-splits on `cw` (JUMPI taken via exp003's [`runs_jumpi_taken`](../../../../003_bytecode_layer/BytecodeLayer/Hoare.lean#L684), fall-through reuses `jump_to_block`). The IR state is unchanged across an edge, so the semantic `Corr` clauses transport verbatim; ~15 `rfl` accessor lemmas ([`jumpFrame_*`, `jumpdestFrame_*`, `jumpiFallthroughFrame_*`](../../../LirLean/Sim/SimTerm.lean#L150)) expose exactly the clauses to thread.

---

## 5. Layer F — `CfgSim/` (reviewer Q3)

### 5.1 `WellFormedLowered` — post-P8, fuel-free

Quoted whole from current source ([`LowerConforms.lean#L144`](../../../LirLean/CfgSim/LowerConforms.lean#L144)) — **7 fields**, all pc/offset bounds plus slot registration; no fuel, no acyclicity (the old `MatFueled`/`Acyclic` stack was deleted by P9):

```lean
structure WellFormedLowered (prog : Program) : Prop where
  bound_sstore : ∀ (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.sstore key value) →
    pcOf prog L pc
      + ((matCache prog value).length + (matCache prog key).length) < 2 ^ 32
  bound_sload : ∀ (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    pcOf prog L pc + ((matCache prog k).length + 35) < 2 ^ 32
  bound_ret : ∀ (L : Label) (b : Block) (t : Tmp),
    prog.blocks.toList[L.idx]? = some b → b.term = .ret t →
    termOf prog L + (matCache prog t).length ≤ 2 ^ 32
  bound_stop : ∀ (L : Label) (b : Block),
    prog.blocks.toList[L.idx]? = some b → b.term = .stop →
    termOf prog L < 2 ^ 32
  bound_jump : ∀ (L : Label) (b : Block) (dst : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .jump dst →
    termOf prog L + 5 < 2 ^ 32
    ∧ offsetTable (matCache prog) (defsOf prog) prog.blocks dst.idx < 2 ^ 32
  bound_branch : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    prog.blocks.toList[L.idx]? = some b → b.term = .branch cond thenL elseL →
    termOf prog L + (matCache prog cond).length + 11 < 2 ^ 32
    ∧ offsetTable (matCache prog) (defsOf prog) prog.blocks thenL.idx < 2 ^ 32
    ∧ offsetTable (matCache prog) (defsOf prog) prog.blocks elseL.idx < 2 ^ 32
  slots_slot : ∀ (tw : Tmp) (slot' : Nat),
    defsOf prog tw = some (.slot slot') → slot' = slotOf tw
```

Every `bound_*` field is dischargeable from the single scalar budget `codeFits prog` via the [`bound_*_of_codeFits`](../../../LirLean/Spec/BudgetDerivations.lean#L96) lemmas (`Spec/BudgetDerivations.lean`), and `slots_slot` is structural for `defsOf`. **It is live**: the flagship's internal [`WellLowered`](../../../LirLean/Realisability/Surface.lean#L151) adapter embeds it as its `wf` field, and a concrete satisfiability witness exists ([`wellFormedLowered_exProg`](../../../LirLean/Realisability/Witness.lean#L569), inside [`wellLowered_exProg`](../../../LirLean/Realisability/Witness.lean#L590) — `decide`-discharged with `maxRecDepth 8000` on a hardcoded program; WIP-lib-only anti-vacuity anchor, nothing in the default cone depends on it).

### 5.2 `CallRealises` — the §7 CALL tie

[`CallRealises`](../../../LirLean/CfgSim/LowerConforms.lean#L235) packages *everything* `sim_call_stmt` needs, quantified per cursor over the corresponding frame:

```lean
def CallRealises (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (L : Label) (pc : Nat) (cs : CallSpec) (st0 st0' : Lir.IRState) (fr0 : Frame) : Prop :=
  Corr prog sloadChg obs st0 fr0 L pc →
  ∃ (result : Evm.CallResult) (pd : Evm.PendingCall) (callFr resumeFr : Frame) (argsLen : Nat),
    StepScoped prog st0 (.call cs)
    ∧ st0' = (match cs.resultTmp with
        | some t' => { st0 with world := fun key =>
                        evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }.setLocal
                        t' (callSuccessFlag result pd)
        | none   => { st0 with world := fun key =>
                        evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key })
    -- [snip: 18 further conjuncts — the arg-push run + pins, `CallReturns callFr resumeFr`,
    --  the 8 resume-frame pins, the post-state scoping fold, and the Route-B tail; they
    --  mirror `sim_call_stmt`'s hypotheses one-for-one — see the link]
```

**Flag.** [`callRealises_of_recorded`](../../../LirLean/Realisability/Machinery.lean#L392) (the flagship's R3, the would-be producer) states in its docstring that it deliberately does **not** target `Lir.CallRealises` verbatim, because the embedded live-scope `StepScoped (.call cs)` clause "is refutable within this theorem's own hypothesis envelope for a `WellLowered` program whose call result has a registered reader" — it produces the reshaped [`CallRealisesS`](../../../LirLean/Realisability/Surface.lean#L78) (static `StepScopedS` + kernel) instead. So the in-tree `CallRealises` has no producer and no consumer outside the builder below; treat it as the builder path's frozen interface, not a live seam.

### 5.3 `SimTermStep` and the builders

[`SimTermStep`](../../../LirLean/CfgSim/LowerConforms.lean#L101) is the Layer-E union, matching `RunFrom`'s constructor shape:

```lean
structure SimTermStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (selfAddr : AccountAddress) (L : Label) (b : Block) : Prop where
  halt : ∀ (st' : Lir.IRState) (frT : Frame),
    Corr prog sloadChg obs st' frT L b.stmts.length →
    (b.term = .stop ∨ ∃ t, b.term = .ret t) →
    ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
      ∧ (observe selfAddr (endFrame last haltSig)).world = st'.world
  edge : ∀ (st' : Lir.IRState) (frT : Frame) (succ : Label),
    Corr prog sloadChg obs st' frT L b.stmts.length →
    (b.term = .jump succ
      ∨ (∃ cond elseL cw, b.term = .branch cond succ elseL
            ∧ st'.locals cond = some cw ∧ cw ≠ 0)
      ∨ (∃ cond thenL, b.term = .branch cond thenL succ ∧ st'.locals cond = some 0)) →
    ∃ fr', Runs frT fr' ∧ Corr prog sloadChg obs st' fr' succ 0
```

The builders construct the two step-props from `WellFormedLowered` + the per-shape §7 ties:

- [`simStmtStep_call`](../../../LirLean/CfgSim/LowerConforms.lean#L297) — feeds `sim_call_stmt` from a `CallRealises` tie (only internal caller: the next item).
- [`simStmtStep_block`](../../../LirLean/CfgSim/LowerConforms.lean#L337) — `SimStmtStep` for any **create-free** block: dispatches each `EvalStmt` constructor to `sim_assign` (remat), `sim_assign_sload_lowered`/`sim_assign_gas_lowered` (spills, runtime envelopes **derived** from the per-cursor clean-halt witness via [`gas_envelope_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L700)/[`sload_envelope_of_cleanHalt`](../../../LirLean/Materialise/CleanHaltExtract.lean#L790)), `sim_sstore_stmt_lowered`, and `simStmtStep_call`. A `.create` cursor is excluded by `hnocreate` (create-reflection is planned Step 5; CREATE is a wanted feature, not dead weight).
- [`simTermStep_stop`](../../../LirLean/CfgSim/LowerConforms.lean#L526) / [`simTermStep_ret`](../../../LirLean/CfgSim/LowerConforms.lean#L579) / [`simTermStep_jump`](../../../LirLean/CfgSim/LowerConforms.lean#L652) / [`simTermStep_branch`](../../../LirLean/CfgSim/LowerConforms.lean#L714), combined by [`simTermStep_block`](../../../LirLean/CfgSim/LowerConforms.lean#L799) — per-terminator dispatch; decode facts discharged inside the `_lowered` wrappers, residual = gas envelopes + top-level-frame facts + (`ret`) the RETURN-site bundle.

### 5.4 `sim_cfg` — the cycle-agnostic whole-CFG induction

Quoted whole ([`LowerConforms.lean#L938`](../../../LirLean/CfgSim/LowerConforms.lean#L938)):

```lean
theorem sim_cfg {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress}
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs self L b)
    {st : Lir.IRState} {T : Trace} {C : CallStream} {D : CreateStream}
    {L : Label} {O : Lir.Observable} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hcs : CleanHaltsNonException fr)
    (hrun : Lir.RunFrom prog st T C D L O) :
    ∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world
```

Induction on the [`RunFrom`](../../../LirLean/Spec/Semantics.lean#L99) derivation (an inductive `Prop`, so no fuel and **no acyclicity assumption** — cycles are fine because the IR derivation itself is finite); each constructor runs Layer D then dispatches the terminator; the clean-halt witness is forwarded across each block+edge. Conclusion is the **world channel only** (`O.world`); the result channel rides the flagships' `Conforms` conjunct instead.

[`entry_corr`](../../../LirLean/CfgSim/LowerConforms.lean#L1063) seeds it: the top-level `codeFrame p (lower prog)` (pc 0 = the entry block's leading `JUMPDEST` when `prog.entry.idx = 0`) steps once into `Corr … {locals := fun _ => none, world := w₀} … prog.entry 0`, the only genuine tie being the entry `StorageAgree` and the `Gjumpdest` margin — `DefsSound`/`wellScoped`/`memAgree` are vacuous at empty locals.

**This file contains no discharged headline.** Its closing section states the boundary directly:
the local payoff is `sim_cfg`, while the closed `lower_conforms`, `lower_conforms_exact`, and
`lower_conforms_gasfree` flagships live in
[`RealisabilitySpec.lean`](../../../LirLean/Realisability/RealisabilitySpec.lean#L222).

### 5.5 `LowerDecode.lean` — the decode-discharge layer

Two kinds of content:

**Reusable byte-layout facts** (live on both paths): [`sstore_op_decode`](../../../LirLean/CfgSim/LowerDecode.lean#L74) (trailing SSTORE decodes at `pcOf + lv + lk`), [`term_dest_decode`](../../../LirLean/CfgSim/LowerDecode.lean#L332) (a `PUSH4` destination inside `emitTerm` decodes with immediate `ofNat (off % 2^32)`), the round-trip pair [`uInt256_offsetBytesBE`](../../../LirLean/CfgSim/LowerDecode.lean#L296)/[`ofNatMod_toUInt32?`](../../../LirLean/CfgSim/LowerDecode.lean#L303) (discharges the `hdestword` jump-destination tie), and the stash anchor packs [`decode_gasstash`](../../../LirLean/CfgSim/LowerDecode.lean#L632) / [`decode_sloadstash`](../../../LirLean/CfgSim/LowerDecode.lean#L806) (the three stash opcodes decode at their successor frames, read off [`flatBytes`](../../../LirLean/Decode/DecodeLower.lean#L45) via the [03-code-geometry](03-code-geometry.md) anchors).

**`_lowered` arm wrappers** (builder-path only): [`sim_sstore_stmt_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L112), [`sim_term_halt_ret_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L206), [`sim_term_edge_jump_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L396), [`sim_term_edge_branch_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L474), [`sim_assign_gas_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L705), [`sim_assign_sload_lowered`](../../../LirLean/CfgSim/LowerDecode.lean#L915). Each is its Sim-layer arm with the carried decode bundle discharged generically over `lower prog` and (for the spills) the opaque `StashRuns` bundle *constructed* from [`stash_tail_gas`](../../../LirLean/Materialise/StashTail.lean#L295)/[`stash_tail_sload`](../../../LirLean/Materialise/StashTail.lean#L383) — leaving only genuinely runtime residuals (gas margins, memory-expansion witnesses, `SstoreRealises`, stack-room folds, the activeWords-flatness fact `hawk`).

---

## 6. THE TWO-PATHS FINDING — verified against current source (reviewer Q4)

Two proof paths run through this layer toward a conformance statement:

```
BUILDER PATH (frozen scaffolding, endpoint uncalled)
  sim_*_lowered ──▶ simStmtStep_block / simTermStep_block ──▶ SimStmtStep/SimTermStep
      ──▶ sim_cfg ──▶ lower_conforms_cyclic / lower_conforms_cyclic'  (DriveSim, F3/F3′)
                             └── ZERO callers of the endpoint

FLAGSHIP PATH (live, WIP): lower_conforms (R11, RealisabilitySpec.lean)
  runFrom_of_driveCorrLog ──▶ coupled walk (DriveCorrLog / RecorderCoupled) re-implementing
  Layers C–F with point-wise S-variants (sim_sstore_stmt', CallRealisesS, P3a block walk,
  strong-totalGas CFG induction) — consuming from THIS layer only Corr + the low-level
  bricks/decode helpers, never the builders.
```

Caller audit (term-level applications, prose mentions excluded; grepped 2026-07-09):

| Symbol | Term-level callers | Verdict |
|---|---|---|
| [`simStmtStep_block`](../../../LirLean/CfgSim/LowerConforms.lean#L337), [`simTermStep_block`](../../../LirLean/CfgSim/LowerConforms.lean#L799) | **none** | superseded scaffolding; top of the builder path |
| [`simStmtStep_call`](../../../LirLean/CfgSim/LowerConforms.lean#L297), [`CallRealises`](../../../LirLean/CfgSim/LowerConforms.lean#L235), the four `simTermStep_*` arms | only `simStmtStep_block`/`simTermStep_block` | same |
| [`entry_corr`](../../../LirLean/CfgSim/LowerConforms.lean#L1063) | **none** (prose refs only, in [Producer](../../../LirLean/Realisability/Producer.lean#L129)/[Surface](../../../LirLean/Realisability/Surface.lean#L267)) | superseded; the flagship builds its own entry `DriveCorrLog` |
| the six `sim_*_lowered` wrappers | only the builders (+ the [`Audit`](../../../LirLean/Audit.lean#L45) axiom pin on the sload one) | superseded as *wrappers*; their internal construction pattern is the precedent the flagship's missing call-arg driver will copy |
| [`sim_cfg`](../../../LirLean/CfgSim/LowerConforms.lean#L938), [`sim_stmts_block`](../../../LirLean/Sim/SimStmts.lean#L150), [`jump_to_block`](../../../LirLean/Sim/SimTerm.lean#L544), the four `sim_term_*` arms | [`DriveSim`](../../../LirLean/Drive/DriveSim.lean#L618) only ([`lower_conforms_cyclic`](../../../LirLean/Drive/DriveSim.lean#L618)/[`′`](../../../LirLean/Drive/DriveSim.lean#L661) chain) | endpoint uncalled; [`RealisabilitySpec`](../../../LirLean/Realisability/RealisabilitySpec.lean#L282) states why: `lower_conforms_cyclic'` "needs an UNCONDITIONAL all-frames `SimStmtStep`, which the reshaped `StmtTies'` cannot supply … the coupling-free path is exactly the vacuity the reshape exists to kill" |
| [`Corr`](../../../LirLean/Sim/SimStmt.lean#L102) + field lemmas, [`pcOf_succ`](../../../LirLean/Sim/SimStmt.lean#L78), [`pcOf_eq_termOf`](../../../LirLean/Sim/SimTerm.lean#L86), the `sstoreFrame_*`/`jumpFrame_*` accessor packs, [`emitStmt_*`](../../../LirLean/Sim/SimStmt.lean#L149) | **flagship** ([Producer](../../../LirLean/Realisability/Producer.lean#L1036)/[Machinery](../../../LirLean/Realisability/Machinery.lean#L392)) + DriveSim | **live, load-bearing** |
| [`corr_at_jumpdest_landing`](../../../LirLean/Sim/SimTerm.lean#L503) | flagship ([Producer L243](../../../LirLean/Realisability/Producer.lean#L243)) + DriveSim | live |
| [`sstore_op_decode`](../../../LirLean/CfgSim/LowerDecode.lean#L74), [`decode_gasstash`](../../../LirLean/CfgSim/LowerDecode.lean#L632), [`term_dest_decode`](../../../LirLean/CfgSim/LowerDecode.lean#L332), [`ofNatMod_toUInt32?`](../../../LirLean/CfgSim/LowerDecode.lean#L303) | flagship ([Producer L1258](../../../LirLean/Realisability/Producer.lean#L1258), [Machinery L1663](../../../LirLean/Realisability/Machinery.lean#L1663), [L774](../../../LirLean/Realisability/Machinery.lean#L774), [L787](../../../LirLean/Realisability/Machinery.lean#L787)) | live |
| [`decode_sloadstash`](../../../LirLean/CfgSim/LowerDecode.lean#L806) | only `sim_assign_sload_lowered`/`simStmtStep_block` | builder-path today; same dual-use design as `decode_gasstash`, likely to go live when the coupled sload step lands |

Direct answers to the reviewer's four sub-questions:

1. **Which builders have zero callers?** `simStmtStep_block`, `simTermStep_block`, `entry_corr` (and transitively `simStmtStep_call`, the four `simTermStep_*` arms, `CallRealises`, the six `_lowered` wrappers). `sim_cfg` has exactly one consumer chain — DriveSim's `lower_conforms_cyclic`/`′` — whose own endpoint has zero callers.
2. **Is the old acyclic capstone `lower_conforms` still in `LowerConforms.lean`?** **Deleted.** The file points to the closed flagship [`lower_conforms`](../../../LirLean/Realisability/RealisabilitySpec.lean#L222) in the WIP library. Grep confirms no `lower_conforms` declaration anywhere under `CfgSim/`.
3. **Are `jump_landing_of_cleanHalt` / `branch_landing_of_cleanHalt` still orphaned?** **No — they no longer exist.** Deleted 2026-07-04 in commit `738ac23` ("retire superseded acyclic-CFG + Plus-thread scaffolding", −437 LOC from LowerDecode; the flagship re-derives the landing walk inline). The [cluster-assembly deep-dive](../../deepdive-2026-07-04/cluster-assembly.md), which lists them as present-but-orphaned at `LowerDecode.lean:486/769`, predates that commit by hours and is stale.
4. **Live / incremental / superseded.** *Live*: `Corr` + accessor/emit lemmas, `pcOf_succ`/`pcOf_eq_termOf`/`pcOf_zero`, `corr_at_jumpdest_landing`, `WellFormedLowered` (embedded in `WellLowered`), and the low-level decode helpers named above. *Incremental-toward-the-flagship*: the arm lemmas themselves (`sim_assign*`, `sim_sstore_stmt`, `sim_call_stmt`, `sim_term_*`) — the coupled S-variants either re-derive their bodies "verbatim" ([`sim_sstore_stmt'`](../../../LirLean/Realisability/Producer.lean#L1036)'s own words) or plan to feed them once the R3 arg-push driver lands, and `decode_sloadstash`'s interface was explicitly shaped for that hand-off. *Superseded scaffolding awaiting the R11 dust*: `SimStmtStep`/`SimTermStep` as ∀-quantified units, the builders, `CallRealises`, `entry_corr`, `sim_cfg`, and DriveSim's F3 endpoints — kept green in the default cone (the [lakefile](../../../lakefile.lean) comment says so deliberately) but with no path to the flagship in their current all-frames shape. Coordinate the disposal decision with [06-realisability](06-realisability.md).

---

## 7. Results taxonomy, smells, and doc-vs-source discrepancies

**Headline-grade in scope:** none — by design this layer has no capstone; its strongest self-contained results are `sim_cfg` and the five statement arms, all *conditional on per-block ties*. The experiment's headline lives in 06.

**Bricks (load-bearing):** `Corr` + `Corr.validJumps_lower`, `pcOf_succ`/`pcOf_eq_termOf`, the five C-layer arms, `sim_stmts_block`, the E-layer arms + `corr_at_jumpdest_landing`/`jump_to_block`, `WellFormedLowered`, and LowerDecode's byte-layout facts. Proof style throughout: frame-chain assembly + record rebuilds; the only inductions are `sim_stmts_drop` (list) and `sim_cfg` (derivation); no `omega`-storms beyond cursor arithmetic.

**Examples:** `wellFormedLowered_exProg`/`wellLowered_exProg` ([Witness.lean](../../../LirLean/Realisability/Witness.lean#L569), WIP lib) — hardcoded-program satisfiability witnesses for this layer's tie vocabulary; consumed only by the WIP anti-vacuity check, no real result depends on them.

**Smells** (each with the does-a-headline-depend-on-it call):

1. **`SstoreRealises` ∀-frames shape** ([SimStmt.lean#L317](../../../LirLean/Sim/SimStmt.lean#L317)) — judged unsatisfiable-as-a-producible-tie by the flagship's own docstring. Headline exposure: *none directly* (the flagship bypasses it point-wise), but it blocks `sim_sstore_stmt` from ever being consumed as-is and forced the `sim_sstore_stmt'` body duplication.
2. **`CallRealises`'s embedded `StepScoped`** ([LowerConforms.lean#L235](../../../LirLean/CfgSim/LowerConforms.lean#L235)) — refutable in R3's envelope per [Machinery](../../../LirLean/Realisability/Machinery.lean#L392); same family. Headline exposure: none (flagship uses `CallRealisesS`), but it makes the in-tree tie a dead interface.
3. **`sim_call_stmt`'s arg-push run has no producer** — the honest open obligation (R3 Piece B). Headline exposure: **yes** — this is on the flagship's critical path; the missing driver is ~200 lines by Machinery's own estimate, precedent in this very layer (`sim_term_edge_branch_lowered`'s cond driver).
4. **`SimStmtStep`/`SimTermStep`'s all-frames ∀** — the shape that made the deleted headline vacuous; anything rebuilt on the builders inherits it. Headline exposure: only if someone resurrects the builder path.
5. **`maxRecDepth 8192`** set six times in [LowerDecode](../../../LirLean/CfgSim/LowerDecode.lean#L29) — byte-index reduction depth, mild; no `maxHeartbeats` cranks anywhere in scope. Headline exposure: cosmetic.
6. **`Corr`'s phantom `sloadChg`/`obs` parameters** (§2). Cosmetic.

**Doc-vs-source discrepancies found (for the tour record):**

- [cluster-sim.md](../../deepdive-2026-07-04/cluster-sim.md) calls `sim_call_stmt` "the 28-hyp shape lemma" consumed by the cyclic headline — current source: **25 hypotheses**, consumer chain now caller-less; the newer [codebase map](../../codebase-map-2026-07-06.md) already says "25 hyps (verified)".
- [cluster-assembly.md](../../deepdive-2026-07-04/cluster-assembly.md) lists `jump_landing_of_cleanHalt`/`branch_landing_of_cleanHalt` as present orphans — deleted the same day the audit was written (commit `738ac23`).
- [codebase map §L6](../../codebase-map-2026-07-06.md) says `WellFormedLowered … (11 static fields)` — current structure has **7** (slot-addressability moved out to `IRWellFormed.slotAddr`/the call tie; the map's own §L6 code block is otherwise accurate about fuel-freedom). Its line anchors for this layer (`:143`, `:983`, `:1108`) have drifted a few dozen lines.

---

## 8. Recommendations

1. **Decide the builder half's fate as part of R11 close-out** — the all-frames `SimStmtStep`/`SimTermStep`/`CallRealises`/builders/`sim_cfg`/`entry_corr` chain (plus DriveSim's F3 endpoints) is superseded in its current shape. Either delete it with the same discipline as the b144af8 purge once `runFrom_of_driveCorrLog` closes, or explicitly re-shape it to the coupled interfaces; do not leave two walks indefinitely (`sim_sstore_stmt'` already duplicates ~120 lines of `sim_sstore_stmt`'s body).
2. **Land the call arg-push driver in this layer**, next to `sim_term_edge_branch_lowered`'s cond driver — it is the one missing machine-run producer for `sim_call_stmt`, and it unblocks the flagship's R3 Piece B.
3. **Interface repair on `sim_call_stmt`**: take `hcorr : Corr …` instead of the three exploded fields, and absorb the eight `resumeAfterCall` projections behind `hresume` via exp003-side computation lemmas (tracked as STOP-and-report since `resumeAfterCall` is upstream).
4. **Keep `CfgSim/` focused on CFG simulation** as the planned assembler develops
   ([07-assembler](07-assembler.md)); byte-emission APIs should not migrate into this folder.
5. **Sweep remaining stale docstrings** such as `SimTerm`'s "value channel deferred" paragraph;
   this layer's docstrings are otherwise unusually good navigation surfaces.
