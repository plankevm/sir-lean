# Assessment: would a SIR small-step conformance be substantially simpler than `Lir`'s big-step bridge?

*2026-07-15 — grounded evaluation of `docs/planning/sir-smallstep-bridge-2026-07-15.md`.
Read-only investigation of the actual Lean; file:line evidence throughout.*

## TL;DR

**Partially, and less than the hypothesis hopes.** The big-step↔small-step reconciliation
(recorder coupling, `driveLog` suffix threading, the boundary/cyclic walk, stream alignment)
is real overhead — roughly **35–40%** of the closed-proof mass — and a small-step SIR would
genuinely dissolve most of it into a standard simulation induction. But the **majority of the
mass (55–60%) is value-channel work** (`materialise*`, `Corr`, decode geometry, gas/stack
envelopes, recompute-on-use soundness) that survives *any* IR choice unchanged. And SIR adds
**new obligations `Lir` never had** (block-argument `Locals.transfer` lowering; existential
gas/call quantifier direction for an equality-strength theorem; a gas cost model + CREATE to
reach parity). Net: a SIR conformance would be **moderately simpler on the control spine and
noticeably cleaner to state**, but not a step-change, because the grind lives in the value
channel.

---

## 1. Apportionment of the current `Lir` proof mass

Measured line counts (the closed cones; `wc -l`):

| Cluster | Modules | Lines | Nature |
|---|---|---|---|
| **Realisability coupling + producer** | `Realisability/Machinery.lean` (4183), `Producer.lean` (3116), `Surface.lean` (694), `Witness*` (999) | ~8,990 | **mixed** — value channel *threaded through* coupling |
| **Value channel (Materialise)** | `Materialise/*` (3089) | 3,089 | **survives any IR** |
| **CFG capstone** | `CfgSim/LowerConforms.lean` (1120), `LowerDecode.lean` (1107) | 2,227 | **big-step induction on `RunFrom`** |
| **Decode geometry** | `Decode/*` (2171) | 2,171 | **survives any IR** (byte layout, boundaries, jump validity) |
| **Lowering + well-formedness + spec** | `Spec/*` (1777), `Sim/*` | ~3,000 | mostly **survives** (emit tables, budgets) |
| **Generic engine (reused, IR-agnostic)** | `EVM/BytecodeLayer/*` | 22,410 | **already reused as-is** |

The generic `EVM/BytecodeLayer` engine (22k lines: frame calculus, `Runs`, drive/descent,
`Asm`, interpreter, recorder) is *already IR-agnostic* and would be reused verbatim by a SIR
proof. The interesting apportionment is inside exp005's ~22.7k `LirLean` lines.

### 1a. What is big-step↔small-step *bridging* overhead (would shrink/dissolve)

The bridging story is entirely visible in the code:

- **`RunFrom` is big-step** (`LirLean/Spec/Semantics.lean:89-126`): an inductive whose
  `branch`/`jump` constructors carry a *recursive* `RunFrom … dst O` premise — the recursion
  tree *is* the control flow; there is no machine state, no PC, and effects are threaded as
  *consumed input oracle streams* (`GasOracle`/`CallStream`/`CreateStream`,
  `Semantics.lean:41-74`). `RunFromLeft`/`RunFromAll` (`:134-180`) exist *only* to track
  stream leftovers for the exact-consumption flagship — pure big-step-effect-model artifact.

- **The recorder + `RecorderCoupled`** (`EVM/BytecodeLayer/Exec/Recorder.lean:230-243`)
  instruments the small-step run so its externally-observed effects become suffix-streams
  (`gasSuffix/sloadSuffix/callSuffix/createSuffix`), each field a `∃ pre, log.x = pre ++
  suffix` prefix-witness plus a `restart : driveLog … = .ok (…)` replay obligation. This
  whole structure exists to *manufacture a per-block step structure on the big-step IR side*.

- **`DriveCorrLog` + `StreamsAligned` + the producer recursion**
  (`Realisability/Producer.lean:72-120, 3038-3115`): `runFrom_of_driveCorrLog` is a
  strong-`totalGas` induction carrying the coupling suffix + a `StreamsAligned` fact pinning
  the IR streams `(T,C,D)` to the *realised image* of the un-consumed recorder suffixes
  (`Producer.lean:72-76`). Every per-block step either bottoms out to `RunFromCoupled`
  (terminal world+result equation + `RunFrom`) or advances to a strictly-smaller-gas
  successor re-establishing `DriveCorrLog`+`StreamsAligned` (`DriveLogStep`,
  `Producer.lean:96-109`). This is the machinery that "puts a big-step recursion tree in
  lockstep with small steps."

- **`CfgSim/LowerConforms.lean` inducts on `RunFrom`** (`:11-45`) and *manufactures* the
  small-step bytecode run per block (`SimTermStep`/`SimStmtStep` abstract the per-block,
  per-intermediate-frame bundles because "they cannot be stated once up front" — exactly
  the mismatch a small-step relation removes).

Density evidence (grep counts): `Producer.lean` is ~all coupling — `RecorderCoupled` 36,
`DriveCorrLog` 29, `StreamsAligned` 24, `suffix/Suffix` 25, `CoupledAdvance` 10,
`simStmt_coupled` 17. `Machinery.lean` carries `RecorderCoupled` 40, `suffix/Prefix` 37,
`RunLog` 21.

**Bridging-overhead estimate: ~35–40% of the ~22.7k LirLean mass** — concentrated in
`Producer.lean` (nearly all of 3116), the coupling half of `Machinery.lean`, the
`RunFrom`-induction scaffolding of `CfgSim/*` (2227), the `RunFromLeft`/`RunFromAll`
duplication, and the recorder-suffix bookkeeping.

### 1b. What is value-channel work (survives *any* IR)

The value channel is `Corr` and everything it carries (`Sim/SimStmt.lean:105-137`):
- `M1 pc_eq` / `M2 code_eq` / `M2′ validJumps_eq` / `M5 stack_nil` — geometry;
- `M3 storage : StorageAgree` — storage agreement through the observable lens;
- `defsSound : DefsSoundS` — recompute-on-use soundness (`Materialise/DefsSound.lean`);
- `wellScoped` — define-before-use scoping;
- `memAgree : MemRealises` — **the temps→memory-slot channel** (the honest positional value
  tie that replaced the gas/sload universals).

The engine that discharges these is `materialise_runsC` and its charge/decode twins
(`Materialise/MatFoldChannel.lean` 1381, `DefsSound.lean` 650, plus `MaterialiseGas/Runs/
CleanHalt`). Grep: `Machinery.lean` mentions `materialise*/matExpr/matCache/MatRuns` **219**
times — the module is *dominated* by value-channel runs, with the coupling threaded through as
a rider. The smoking gun is `recorderCoupled_matRunsC` (`Machinery.lean:906-925`): it is
*literally* `materialise_runsC` (value agreement: decode geometry + gas/stack envelopes +
readback value) **plus** a `RecorderCoupled log fr' gS sS cS dS` rider proved to "ride
unchanged" by inserting one `recorderCoupled_step_other` per emitted opcode. Strip the rider
and the value-channel run is untouched.

Decode geometry (`Decode/*` 2171: boundary reachability, byte layout, jump validity,
segment alignment) is entirely about *the lowering's byte-level correctness* and survives
verbatim.

**Value-channel estimate: ~55–60% of the LirLean mass** — the Materialise cone (3089), the
value half of `Machinery.lean`, `Sim/*`, `Decode/*` (2171), and the emit/budget spec (`Spec/*`).

---

## 2. What SIR gives you, and what it costs

SIR's `SmallStep` (`sir/Sir/Semantics/SmallStep.lean:6-48`) is a per-cursor relation
`MachineState → Trace → MachineState` with an explicit `ProgramCursor`
(`State.lean:47-51` / block-io `ProgramCursor`+`BlockPosition`) and an *emitted* event
`Trace = List Event` (`State.lean:70-74`). `Steps` (`:50-62`) is its closure. Crucially it is
at the **same altitude as the bytecode `Runs`** (`EVM/BytecodeLayer/Hoare.lean:140-166`),
which is itself a refl+step(+call+create) reflexive-transitive relation.

### Wins (dissolve the bridging overhead)

1. **No recorder, no suffix streams, no `StreamsAligned`.** SIR *emits* `Trace` events that
   the bytecode recorder *also* emits; alignment becomes "the two traces are equal (up to the
   realise map)" proved *along the simulation induction*, not reconstructed from a
   `restart`/`prefix` replay. `Producer.lean`'s ~3116 lines of coupling orchestration largely
   evaporate; `RecorderCoupled`'s 5-field prefix/restart structure is unnecessary.
2. **No `RunFrom`-tree ↔ small-step manufacturing.** `CfgSim/LowerConforms.lean`'s induction
   on the big-step recursion tree becomes a standard forward-simulation induction on
   `Steps`/`SmallStep`, matching each SIR step to a bounded `Runs` segment. The
   `SimTermStep`/`SimStmtStep` "can't-be-stated-up-front" abstraction disappears — a
   simulation relation `R : Sir.MachineState → Frame → Prop` *is* stated up front.
3. **No `RunFromLeft`/`RunFromAll` duplication.** Exact consumption is automatic: a trace
   equality is already exact; there is no "leftover suffix" to separately close (this is the
   entire reason `lower_conforms_exact` needed a parallel relation).
4. **`totalGas` strong-induction well-foundedness** is replaced by induction on the `Steps`
   derivation — simpler and standard.

### Costs (new obligations `Lir` never had)

1. **Block-argument lowering + its proof.** `Lir` has a *global temp namespace* with
   recompute-on-use (`Materialise/DefsSound.lean` header) — no phi, no block-args. SIR
   (block-io) passes values across edges via `Locals.transfer outputs inputs`
   (`git show origin/feat/block-io:sir/Sir/Semantics/State.lean`, `Locals.transfer`): a
   *local rename* at the jump edge. A lowering must realise `transfer` as concrete
   stack/memory moves, and the simulation must prove those moves reproduce the rename. This
   is *net-new* lowering code + a new per-edge proof obligation. It partially offsets win #2.
2. **Existential/non-determinism direction.** SIR `.gas`/`.call` steps *choose* a value
   existentially (`SmallStep.gas`/`.call` bind an arbitrary `gas`/`result`). To get an
   *equality-strength* conformance (the analogue of `lower_conforms_exact`, not a mere
   refinement) the simulation must be **backward** (bytecode-driven): instantiate SIR's
   existentials from the *recorded* bytecode values. That is exactly what `realisedGas`/
   `realisedCall` do today (`Recorder.lean:269-283`) — so the "who-produces-the-stream"
   realisability argument does **not** fully vanish; it re-appears as "the SIR trace this run
   witnesses is the realised bytecode trace." Somewhat cleaner (a trace equality vs a
   consumed-oracle threading), but the value-agreement obligations underneath are identical.
3. **`Steps` shape.** SIR's `Steps` is `single + chain` (TransGen-style,
   `SmallStep.lean:50-62`). A forward/backward simulation composes far better with
   `refl + tail` (ReflTransGen) — matching the bytecode `Runs` (refl+step). This is already
   the preferred direction (memory: *canonical Steps = reflexive-transitive*) and should be
   settled **before** building a simulation on it, else every composition step fights the
   `chain`-associativity.
4. **Maturity gap is large.** SIR on `main` has: no gas *cost* model (only an emitted gas
   *observation*), no CREATE, and (block-io) an unfinished edge model — `Terminator.jump`
   still carries only a target (`CFG.lean`), with `outputs`/`inputs` as *separate block
   fields* wired through `eval_jump`'s `Locals.transfer`. A *fair* comparison must fund
   bringing SIR to parity: a gas cost model (the whole `chargeExpr`/`chargeCache` cone,
   `MaterialiseGas.lean` + the gas envelopes in `materialise_runsC`), CREATE
   (`Create.lean` + the CREATE coupling arms in `Machinery.lean:3329-4183`), and clean-halt/
   revert handling. None of that is bridging overhead — it is value-channel + feature work
   that would have to be rebuilt, *not* saved.

---

## 3. Sketch: the SIR-side conformance statement

The analogue of `lower_conforms` (`RealisabilitySpec.lean:221-236`):

```lean
-- simulation relation: a SIR machine state corresponds to a bytecode frame
def SimRel (prog : Sir.Program) (ctx : Sir.CallContext) (self : AccountAddress)
    (s : Sir.MachineState) (fr : Frame) : Prop :=
  -- geometry: cursor (block,pos) ↦ pcOf; code = lowerSir prog; validJumps; stack shape
  -- value:    Locals ↦ memory slots (MemRealises analogue); world ↦ StorageAgree
  -- scoping:  block-arg live-in at s.control.block realised in fr's memory
  ...

theorem lowerSir_conforms {prog : Sir.Program} {params : CallParams} {log : RunLog}
    (hcode  : params.codeSource = .Code (lowerSir prog))
    (hwf    : SirWellFormed prog)          -- block-arg arity, define-before-use, budgets
    (hrun   : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ (s_final : Sir.MachineState) (tr : Sir.Trace),
      Sir.Steps prog (ctxOf params) (initState params) tr s_final
      ∧ s_final.control = .halted
      ∧ traceRealises tr log                         -- the emitted trace IS the recorded one
      ∧ Conforms params.recipient log
          { world := s_final.world, result := resultOf s_final } := by
  ...
```

Note `traceRealises tr log` replaces `RunFrom … (realisedGas log) (realisedCall log …)`: the
SIR trace is *produced*, then shown equal to the recorded log — rather than the log being
*consumed* as an oracle by the IR relation.

## 4. Proof skeleton

1. **`SimRel` at entry** (`driveCorrLog_entry` analogue): `initState`↔`fr₀`. Reuses the entry
   boundary lemmas verbatim (geometry) + the empty-locals base case (trivial value side).
2. **Backward step simulation** (the core lemma, replacing `driveLogStep_of_block` +
   `runFrom_of_driveCorrLog_rec`):
   `∀ s fr, SimRel s fr → (bytecode has a bounded `Runs fr fr'` to the next boundary) →
     ∃ s' tr, Sir.Steps s tr s' ∧ SimRel s' fr' ∧ traceRealises tr (segment of log)`.
   Case split on `Sir.SmallStep`:
   - `assign`/`sstore`: **reuse `materialise_runsC` + `StorageAgree` verbatim** (empty trace,
     no coupling rider) — this is the bulk, and it is *unchanged*.
   - `gas`/`call`: instantiate SIR's existential from the recorded `log` head (backward
     direction), then reuse the CALL/CREATE resume geometry from `EVM/BytecodeLayer` + the
     `MemRealises` result-slot writeback. Trace-head equality is a one-liner vs today's
     `recorderCoupled_call_extract` suffix surgery.
   - `terminator` (`jump`/`branch`): geometry via decode anchors (**reuse `Decode/*`**) +
     **new** `Locals.transfer` ↦ stack/memory-move lemma.
3. **Induction on `Steps`** to a `.halted` control, composing #2 — a standard small-step
   simulation closure over the reflexive-transitive `Runs`.
4. **`Conforms`** at the halting terminal: **reuse `conforms_of_worldeq`**
   (`RealisabilitySpec.lean:174-202`) essentially verbatim — it is already IR-agnostic
   (it speaks only of `Runs`/`observe`/`log`).
5. **Non-vacuity witness** (`exProg_satisfies_hypotheses` analogue): identical
   kernel-crank shape (`WitnessChecks.lean`), on a SIR witness program.

Lemmas that **survive verbatim or near-verbatim**: all of `Materialise/*`, `Decode/*`,
`Sim/SimStmt.lean`'s `Corr` fields, `conforms_of_worldeq`, the entire `EVM/BytecodeLayer`
engine, the gas envelopes. Lemmas that **disappear**: `RecorderCoupled` (as a threaded
invariant), `StreamsAligned`, `DriveCorrLog`, `DriveLogStep`, `RunFromLeft`/`RunFromAll`, the
`totalGas` strong induction, the whole of `Producer.lean`'s coupling orchestration, the
suffix-prefix bookkeeping in `Machinery.lean`. Lemmas that are **new**: `Locals.transfer`
lowering + proof, backward-instantiation of SIR existentials, `traceRealises`.

---

## 5. Ranked risk list (addressing the brief's "what we do NOT yet know")

1. **[HIGH — confirmed] The mass is in the value channel, not the bridge.** Grep + structure
   evidence: `Machinery.lean` is 219 `materialise*` hits vs 40 `RecorderCoupled`;
   `recorderCoupled_matRunsC` is `materialise_runsC` + a thin rider. SIR saves the ~35–40%
   bridging overhead but the ~55–60% value channel is unchanged. **This is the dominant
   finding: expect a moderate, not dramatic, simplification.**
2. **[HIGH — new] Feature-parity cost dwarfs the saving.** SIR lacks a gas *cost* model and
   CREATE; both are value-channel/feature work (not bridging), so rebuilding them on SIR
   costs roughly what they cost on `Lir` — the `chargeCache` cone + `Machinery.lean:3329-4183`
   CREATE coupling. A fair ledger nets much of the bridging saving back out.
3. **[MED — confirmed] Block-argument lowering is genuinely new.** `Lir` never lowered
   phi/block-args (global temps + recompute-on-use); SIR's `Locals.transfer` needs a new
   stack/memory-move lowering and per-edge proof. Offsets part of the control-spine win.
4. **[MED — confirmed] Existential direction re-introduces "realisability-lite".** Equality
   strength forces a *backward* simulation instantiating SIR's gas/call existentials from the
   recorded log — the `realisedGas`/`realisedCall` idea persists (cleaner as trace-equality,
   but not free). The hypothesis that SIR "subsumes the who-produces-the-stream argument" is
   **only half true**: it subsumes the *threading*, not the *instantiation*.
5. **[MED — confirmed] `Steps` must be re-shaped to ReflTransGen first.** SIR's `single+chain`
   `Steps` (`SmallStep.lean:50-62`) will fight a simulation induction; settle refl+tail before
   building (already the preferred direction). Cheap if done early, expensive if retrofitted.
6. **[LOW — new] SIR is a moving target on a separate repo/branch.** Block-io is unmerged and
   still evolving (jump has no block-args in the terminator; `outputs`/`inputs` are block
   fields wired via `eval_jump`). A conformance built now risks churn.
7. **[LOW] Clean-halt / zero-gas-revert seam.** `Lir`'s `RunLog.clean` seam
   (`RealisabilitySpec.lean:90-95`) is IR-agnostic and would carry over unchanged — neither a
   risk nor a saving.

---

## VERDICT

A SIR small-step conformance would be **moderately simpler and materially cleaner to state**
(dissolving ~35–40% big-step-bridging overhead — the recorder coupling, `Producer.lean`, the
`RunFrom`-tree induction, and the `RunFromAll` duplication — into a standard simulation), but
**not a step-change**, because ~55–60% of the mass is value-channel work (`materialise*`,
`Corr`, decode geometry, gas envelopes) that survives any IR, and SIR *adds* block-arg
lowering, backward existential instantiation, and a full gas-model + CREATE parity bill that
nets much of the saving back out.
