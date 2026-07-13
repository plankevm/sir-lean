I have all the evidence I need. Writing the report now.

---

# Track: BYTECODE-LAYER INTERFACE — diagnosing and fixing the exp003 abstraction boundary

**Scope note.** All paths relative to `/Users/eduardo/workspace/evm-semantics/.worktrees/ir-lowering/`. exp003 = `experiments/003_bytecode_layer/BytecodeLayer/`, exp005 = `experiments/005_ir_lowering/LirLean/`. All line numbers verified against the current `exp005-honesty-cleanup` tree (post-Phase-1; `TieDischarge.lean` = 4506 lines, headline at :4292).

---

## 0. Executive diagnosis: why the abstraction "kind of failed"

exp003 exports **two tiers** and the lowering proof could use **neither as intended**:

1. **The abstract tier** — `Behaves` (`Hoare/Behaves.lean:45`, "for-all-programs behavior predicate at the messageCall boundary"), `Outcome`/`Observables` (`Observables.lean`), `EVMSpec.lean`, `SharedObservable.lean`, `Refinement.lean`. This tier abstracts the outcome of a **whole completed call**. exp005 uses it **zero times** (grep across `LirLean/`: `Behaves` 0 hits, `EVMSpec`/`SharedObservable`/`Refinement` 0 hits). It is consumed only by the exp003/exp004 equivalence track.

2. **The frame tier** — `StepsTo` (`Hoare.lean:52`), `Runs` (`:114`), `CallReturns` (`:91`), `Runs.trans` (`:129`), the per-opcode `runs_*` rules (`:280–:638`), `runs_branch` (`:667`), `messageCall_runs` (`Hoare/CallSequence.lean:132`), `Runs.gasAvailable_le` (`Hoare/GasMonotone.lean:251`). This is what exp005 actually lives on: `Runs.trans` ×35, `Runs.gasAvailable_le` ×23, `runs_push` ×17, `messageCall_runs` ×14, `runs_jump` ×13, `subCharges` ×120.

The structural reason: **a lowering-correctness proof is a forward simulation, and a forward simulation needs a mid-run, per-cursor judgment.** exp003 offers only two altitudes — single opcode steps on `Frame`s, and whole-call outcomes on `CallParams` — with **nothing in between**: no block-level composition, no code-geometry algebra for *emitted* (as opposed to hand-written) bytecode, no engine invariants along `Runs`, no recording interpreter. Every future IR needs exactly that middle band, so exp005 built all of it in-house, at frame level.

The failure is even self-documented. `Hoare.lean:27–30` promises *"`Runs` mentions `Frame` and so is an internal brick … it never appears in an exported statement"* — yet exp005's flagship **conclusion** is stated as `∃ last haltSig, Runs (codeFrame params code) last ∧ stepFrame last = .halted haltSig ∧ (observe self (endFrame last haltSig)).world = O.world` (`TieDischarge.lean:4328–4330`). The client didn't just reach below the surface for lemmas; it had to state its *headline* in below-surface vocabulary, because no exported big-step judgment exists to state it against.

Aggravating factors, each with a smoking gun:

- **Missing engine invariants.** exp005 opens `namespace Evm` three times *inside its own tree* (`TieDischarge.lean:543, :604, :1653`) and proves ~2,190 lines of pure engine facts there (spans :543–587, :604–1486, :1653–2914: the `*_next_self` ×17 and `*_next_accMono` ×17 dispatch walks, `stepFrame_needsCall_inv`/`_needsCreate_inv`, `stepFrame_halted_success_accMono`), plus engine-level `Lir` blocks (`resumeAfterCall_address/_accounts`, `endCall_revert/exception_accounts`, `AccPresent`/`AccMono` bricks at :1488–1651; `beginCall_inl_checkpoint`, `drive_accounts_find_mono`, the `CallPreservesSelf` chain at :2916–~3560).
- **Missing inversion bricks, admitted in writing.** `CleanHaltExtract.lean:26–28`: *"per-op OOG / `.next`-inversion bricks (§1) — for the charge-only ops with **no inversion in 003** (`GAS`/`PUSH`/`SLOAD`/`ADD`/`LT`)"*.
- **Missing recording interpreter.** `driveLog`/`runWithLog` — a pure engine artifact (an instrumented `drive`) — are defined in the IR layer (`RunLog.lean:156, :219`), as is the observables projection `observe` (`:321`).
- **Code geometry proven only for hand-written examples.** exp003's decode lemmas are literal per-program facts (`Hoare/Sequence.lean`: `decode_seq_0`, `decode_seq_2`, … for the fixed `seqProgram`). There is no generic "decode of an emitted concatenation" algebra, so exp005 built Layout/DecodeLower/DecodeAnchors/MatDecLower/LowerDecode/JumpValid/NoCreateBytes/BoundaryReach (~4,100 lines) from scratch.
- **Even exp003's internals leak.** exp005 imports `BytecodeLayer.Semantics.Dispatch`/`UInt64` directly (4 files: `Create.lean`, `Call.lean`, `Mono.lean`, `Preserve.lean`) and names `Dispatch.memExpansionChargeOf` ×20, `memChargedState` ×14, `binOpPost`/`gasPost`/`sloadPost`; it uses the fuel-measure `totalGas` from `Semantics/Interpreter/Measure.lean:64` (via `driveCorr_measure`, `DriveSim.lean:97`); and 9 exp005 files `import Evm` (the vendored engine) directly.

---

## 1. Leak inventory

### 1.1 What exp003 currently exports (the intended surface)

| Export | Location | Used by exp005? |
|---|---|---|
| `StepsTo`, `Runs`, `CallReturns`, `Runs.trans/single/linear_to_halt/step_cancel/gas_cancel` | `Hoare.lean:52–246, :352` | Heavily (×35 `trans`) |
| Per-opcode `runs_*` rules + post-frame transformers (`pushFrameW`, `sstoreFrame`, `addFrame`, `ltFrame`, `sloadFrame`, `gasFrame`, `popFrame`, `mstoreFrame`, `mloadFrame`, `jumpFrame`, `jumpdestFrame`) + effect/framing companions (`sloadFrame_storage_self:409`, `sstoreFrame_storage_self:705`, `sstoreFrame_storage_frame:725`, `mloadFrame_value:539`) | `Hoare.lean:260–748` | Heavily |
| `runs_branch` combinator | `Hoare.lean:667` | ×8 |
| `messageCall_runs`, `Runs.drive_reconcile` | `Hoare/CallSequence.lean:132, :75` | ×14, ×1 |
| `Runs.gasAvailable_le`, `StepsTo.gas_le`, `CallReturns.gas_le` | `Hoare/GasMonotone.lean:251` | ×23 (the cyclic measure) |
| `subCharges`/`toNat_subCharges` | `Hoare/Sequence.lean:62` | ×120 |
| `Behaves`, `Outcome`, `Observables`, `EVMSpec`, `SharedObservable`, `Refinement` | `Hoare/Behaves.lean:45`, `Observables.lean`, top-level files | **Zero** |

### 1.2 Everything exp005 reaches below that surface, categorized

**Category (i) — pure engine facts, zero IR content, belong in exp003 verbatim (~5,100 lines):**

| Item | Location | Content |
|---|---|---|
| `Evm`-namespace dispatch walks | `TieDischarge.lean:543–587, :604–1486, :1653–2914` (~2,190 ln) | `sstore/tstore_self_present`, `resumeAfterCall_selfAt`, the ×17 `*_next_self` and ×17 `*_next_accMono` per-opcode walks, `stepFrame_needsCall_inv`/`_needsCreate_inv`, `stepFrame_halted_success_accMono` (audit §7's ~2,100 ln, confirmed at shifted line numbers) |
| Engine-level `Lir` blocks | `TieDischarge.lean:1488–1651, :2916–~3560` (~800 ln) | `resumeAfterCall_address/_accounts`, `endCall_revert/exception_accounts`, `AccPresent`/`AccMono` bricks, `beginCall_inl_accounts_present/_checkpoint`, `beginCreate_ok_*`, `drive_accounts_find_mono`, `callPreservesSelf(_success/_modGuards)`, `selfPresent_runs(_of_call)`, `selfPresent_codeFrame` |
| Memory/byte/word algebra | `MemAlgebra.lean` (978 ln, `import Evm` only) | `mload_after_mstore`, `mstore_mload_disjoint`, `copySlice_*`, `writeWord_*`, `fromBytes'/toBytes'`, `resumeAfterCall_memory/_activeWords/_mload`, UInt256/USize toNat algebra |
| Clean-halt scope | `CleanHalt.lean` (~107 ln) | `CleanHalts`, `CleanHaltsNonException`, `*_forward` (forward closure along `Runs`), `haltNonException_*` |
| Clean-halt envelope extractor (engine half) | `CleanHaltExtract.lean` (1,169 ln; §0–§2 are engine) | per-op `op_oog`/`op_inv` inversions "with no inversion in 003" (:26–28), `halted_runs_eq`, per-op `next_*_of_cleanHalt` |
| Drive/fuel framing | `DriveRuns.lean` (374 ln) | `drive_append_framing_lt`, `drive_descend_lt`, `drive_error_oof`, `child_terminates`, `runs_of_drive_ok` (the drive→`Runs` reverse construction) |
| Recording interpreter | `RunLog.lean` (674 ln; ~90% engine) | `CallRecord`/`RunLog` (:68/:82), `driveLog` (:156), `runWithLog` (:219), `observe` (:321), drive-adequacy; only the `realisedCall_eq_evmV2`-style oracle ties are IR-flavored |
| Charge algebra | `Charges.lean` (43 ln) | `subCharges_snoc/append` — extends exp003's own `Hoare/Sequence.lean` |

**Category (ii) — lowering-specific but frame-level (~14,000 lines; the cost every future IR re-pays under the current design).** Three distinct sub-bands:

- **(ii-a) Code geometry / "assembler correctness" (~4,100 ln):** `Layout.lean` (205; offset-table prefix sums over emitted bytes), `DecodeLower.lean` (159) + `LowerDecode.lean` (1,517; incl. the 322-line `branch_landing_of_cleanHalt` at :755 — the longest proof in the study) + `DecodeAnchors.lean` (318; decode-at-cursor anchors) + `MatDecLower.lean` (516), `JumpValid.lean` (515; jumpdest validity of emitted code), `NoCreateBytes.lean` (433; no CREATE byte at any boundary), `BoundaryReach.lean` (435; `AtReachableBoundary` whole-run invariant). Nothing here mentions IR *semantics* — only the byte lists `emitStmt`/`emitTerm` produce. This is, de facto, the correctness proof of an assembler fused into Lir.
- **(ii-b) Simulation glue (~5,500 ln):** `Corr` (`SimStmt.lean:103` — fields `pc_eq`/`code_eq`/`validJumps_eq`/`stack_nil` are pure geometry; `storage`/`defsSound`/`wellScoped`/`memAgree` are IR), `SimStmt/SimStmts/SimTerm`, `sim_cfg` glue in `LowerConforms.lean` (1,497), the `DriveCorr` walk + gas-descent measure (`DriveSim.lean:87, :97, :196, :586`), `StashTail.lean` (523), `Modellable.lean` (490, `AtReachableBoundary` at :407), `Preserve.lean` (618), TieDischarge's `DriveCorrPlus`→headline block (:3589–4506).
- **(ii-c) Value channel (~3,600 ln):** `MaterialiseRuns.lean` (1,370; `StorageAgree` at :561), `MaterialiseCleanHalt/Gas`, `DefsSound.lean`, `Match.lean` (459; `selfStorage` lens at :111). Tied to Lir's recompute-on-use + spill-to-slot strategy — portable as a *pattern*, not a library.

**Category (iii) — genuinely IR-level (~2,300 ln, under 10% of the experiment):** `IR.lean` (114), `SmallStep.lean` (131), `Lowering.lean` (415), `Machine.lean` (277), `IRRun.lean` (378), `Law.lean` (227), `Oracle.lean` (205), `Call.lean`+`CallRealises.lean` (271), `Call.lean`/`Create.lean`.

**Headline stat:** of exp005's ~24,700 lines, roughly **20% is misplaced pure engine theory, ~57% is frame-level lowering machinery, and <10% is actual IR content**. Under the current interface, IR #2 re-pays the 57% and (absent Phase 4) re-discovers the 20%.

---

## 2. Interface design: the exported exp003 surface

Five components, each a spec file (signatures + defs, reviewable standalone, per Eduardo's spec/proof-separation requirement) with proofs in a sibling directory. Names indicative.

### 2.1 `BytecodeLayer/Exec.lean` — the big-step judgment

```lean
/-- Big-step execution: entry `params` running `code` halts cleanly at
observables `O`. `Frame`, `Runs`, `stepFrame`, fuel never appear in client
statements; this is the ONLY vocabulary an IR-conformance headline needs. -/
def Exec (params : CallParams) (code : ByteArray) (O : Observables) : Prop :=
  ∃ fr₀ last halt, EntersAsCode params fr₀ ∧ Runs fr₀ last
    ∧ stepFrame last = .halted halt ∧ O = observeFR params.recipient (endFrame last halt)

theorem exec_messageCall : Exec params code O →
    ∃ r, messageCall params = .ok r ∧ observeCR params.recipient r = O
theorem Exec.det : Exec params code O → Exec params code O' → O = O'
```
Packages: `messageCall_runs` (`CallSequence.lean:132`), `Runs.drive_reconcile` (`:75`), `endFrame`, exp005's `observe` (`RunLog.lean:321`, relocated). The `∃`-form is deliberately also the *introduction* interface: layer-builders (the Asm layer, §2.4) construct it from `Runs`; IR clients only ever destruct `Exec`/`ExecEv`. **exp005's flagship restates as** `runWithLog params fuel = some log → log clean → Exec params (lower prog) O ∧ RunFrom prog (oraclesOf log) st₀ (traceOf log) prog.entry O' ∧ O.world = O'.world` — frame-free, matching the accepted target shape.

### 2.2 `BytecodeLayer/Exec/Recorder.lean` — the recording-interpreter contract

The recorder moves to exp003 (it is an instrumented `drive`), and — the key new design element — the event trace becomes a first-class *indexed run judgment*, because Phase 3's realisability closure is precisely "positional facts about recorded events," which cannot be stated against a `Prop`-only `Runs`:

```lean
inductive Event | gasRead (v : Word) | sloadRead (k v : Word) (warm : Bool) | call (rec : CallRecord)

/-- `Runs` refined with the in-order event trace of GAS/SLOAD/CALL sites. -/
inductive RunsEv : Frame → Frame → List Event → Prop
  | refl | stepSilent … | stepGas … | stepSload … | call …

theorem RunsEv.erase   : RunsEv fr fr' evs → Runs fr fr'
theorem RunsEv.trans   : RunsEv fr m evs₁ → RunsEv m fr' evs₂ → RunsEv fr fr' (evs₁ ++ evs₂)
theorem RunsEv.det_events : RunsEv fr last evs → RunsEv fr last evs' →   -- stepFrame is a function
    stepFrame last = .halted h → evs = evs'

def runWithLog (params : CallParams) (fuel : ℕ) : Option RunLog   -- relocated verbatim

/-- Recorder adequacy: a clean recorded run IS an event-indexed big-step run,
and the log's events are exactly the run's events. -/
theorem runWithLog_adequate :
    runWithLog params (seedFuel params.gas) = some log → log.nonException →
    ∃ fr₀ last halt, EntersAsCode params fr₀ ∧ RunsEv fr₀ last log.events
      ∧ stepFrame last = .halted halt ∧ log.observable = observeFR params.recipient (endFrame last halt)
```
Packages: `driveLog`/`runWithLog` (`RunLog.lean:156/:219`), `runs_of_drive_ok` (`DriveRuns.lean`), `cleanHalts_of_runWithLog`. `RunsEv.det_events` + per-opcode event rules are what turn the audit-§3 "recorded gas prefix = in-order `gasReadOf` of post-GAS frames at Corr cursors" induction into a one-time exp003 fact instead of a per-IR joint induction. This is the single highest-leverage export for Phase 3 *and* every later IR.

### 2.3 `BytecodeLayer/Exec/Invariants.lean` — invariant laws along `Runs`

```lean
theorem Runs.self_present    : Runs fr fr' → CallsCodeAlong fr →   -- the hprec seam, made explicit
    SelfPresent fr → SelfPresent fr'
theorem Runs.find_mono       : Runs fr fr' → CallsCodeAlong fr →
    fr.exec.accounts.find? a = some acc → ∃ acc', fr'.exec.accounts.find? a = some acc'
theorem stepFrame_needsCall_inv / stepFrame_needsCreate_inv / stepFrame_halted_success_accMono
theorem CallReturns.checkpoint …                       -- begin/resume/endCall accounts discipline
-- clean-halt scope + envelope extraction:
def CleanHaltsNonException (fr : Frame) : Prop
theorem cleanHaltsNonException_forward : Runs fr fj → CleanHaltsNonException fr → …
theorem next_of_cleanHalt : CleanHaltsNonException fr →
    decode fr.exec.executionEnv.code fr.exec.pc = some op → Continuing op →
    ∃ e, stepFrame fr = .next e ∧ gasGuardOf op fr    -- per-op gas/mem envelope, DERIVED not supplied
```
Packages: the entire audit-§7 relocation list — the unified `SelfAt`/`AccMono` walk (`TieDischarge.lean:604–1486, :1653–2914`), `drive_accounts_find_mono` + `callPreservesSelf_modGuards` chain (:2916–3560), `CleanHalt.lean`, `CleanHaltExtract.lean` §0–§2, `MemAlgebra.lean`, `Charges.lean`. Note the seams (`CallsCodeAlong` ≈ hprec/CallsCode; oracle-shaped, per the conformance-oracle-surface memory) surface **here**, once, as documented hypotheses of two laws — instead of being threaded through 28-hypothesis IR-side bundles.

### 2.4 `BytecodeLayer/Asm.lean` — structured assembly + the assembled-code algebra

The centerpiece; the reusable form of category (ii-a) and the geometric half of (ii-b):

```lean
inductive AsmInstr | push (v : UInt256) | op (o : StraightOp)   -- no pc-affecting ops in a body
inductive AsmTerm  | stop | ret | jump (dst : Label) | branch (dst thenL elseL : Label)
structure AsmBlock where body : List AsmInstr ; term : AsmTerm
structure AsmProgram where blocks : Array AsmBlock ; data : Array ByteArray  -- data segs: v2

def assemble  : AsmProgram → ByteArray                 -- JUMPDEST-prefixed blocks + offset table
def entryPc   : AsmProgram → Label → ℕ                 -- packages Layout.lean's offsetTable
def cursorPc  : AsmProgram → Label → ℕ → ℕ

-- static geometry, proven ONCE about `assemble`:
theorem assemble_decode_at   : instrAt p L i = some ins →
    decode (assemble p) (cursorPc p L i) = some (opcodeOf ins)          -- ⇐ DecodeAnchors/DecodeLower/MatDecLower
theorem assemble_validJumps  : validJumpDests (assemble p) 0 = entryPcSet p   -- ⇐ JumpValid.lean
theorem assemble_no_create   : …                                             -- ⇐ NoCreateBytes.lean
theorem assemble_boundary_reach : …                                          -- ⇐ BoundaryReach.lean

-- the cursor judgment hiding Corr's geometric fields (pc_eq/code_eq/validJumps_eq/stack_nil):
def AtCursor (p : AsmProgram) (fr : Frame) (L : Label) (i : ℕ) (stk : List UInt256) : Prop

-- dynamic landing, proven ONCE (⇐ jump/branch_landing_of_cleanHalt, LowerDecode.lean:755):
theorem jump_landing   : AtCursor p frT L (bodyLen p L) [] → termOf p L = .jump dst →
    CleanHaltsNonException frT → ∃ fj, Runs frT fj ∧ AtEntry p fj dst ∧ EffectFree frT fj
theorem branch_landing : …  (cond-split form, mirroring runs_branch)
```
For each signature the packaged exp005 source is noted inline. The `data : Array ByteArray` field plus a `theorem assemble_codecopy_data : CODECOPY of handle d reads segment d's bytes at whatever offset assemble chose` is exactly where the real Plank IR's data segments (variable-length constants at non-deterministic offsets) and its allocator nondeterminism belong — see §3.

### 2.5 `BytecodeLayer/Exec/CyclicSim.lean` — the cyclic forward-simulation driver

The IR-agnostic form of the gas-descent enabling idea (audit §5 row 1):

```lean
/-- Generic cyclic simulation: any abstract transition system `(σ, stepA, haltA)`
whose block-entry coupling `R` makes forward progress with strict gas descent
conforms along a clean-halting run. Well-founded on `gasAvailable` via
`Runs.gasAvailable_le` — works for arbitrary cyclic CFGs. -/
theorem sim_cyclic {σ : Type} (stepA : σ → σ → Prop) (haltA : σ → Observables → Prop)
    (R : σ → Frame → Prop)
    (hstep : ∀ a fr, R a fr → CleanHaltsNonException fr →
        (∃ O last halt, RunsHalts fr last halt ∧ haltA a O ∧ observeFR … = O)
      ∨ (∃ a' fr', Runs fr fr' ∧ stepA a a' ∧ R a' fr'
           ∧ fr'.exec.gasAvailable.toNat < fr.exec.gasAvailable.toNat)) :
    R a₀ fr₀ → CleanHaltsNonException fr₀ →
    ∃ O, Exec params code O ∧ Star stepA a₀ (haltA · O)
```
Packages: `DriveCorr` walk skeleton + `driveCorr_measure` (`DriveSim.lean:87/:97`), `totalGas_succ_lt` (`:196`), `runFrom_of_driveCorr` strong induction (`:586`), `totalGas` (`Semantics/Interpreter/Measure.lean:64`), `Runs.gasAvailable_le` (`GasMonotone.lean:251`). exp005's `runFrom_of_driveCorrPlus` becomes an instantiation at `σ := Lir.IRState × Label`.

---

## 3. Honest feasibility assessment

**Can category (ii) be hidden from future IRs?** Split the question:

- **It cannot be *eliminated*.** pc arithmetic, jumpdest validity, and landing behavior are the semantic content of "bytes on an EVM implement this CFG." Someone must prove them; no fork evades this — they evade the *problem*. The remediation plan's own prior-art survey (`docs/remediation-plan-2026-07-02.md:13`) is blunt: *"all forks target structured Yul/IR interpreters — no pc/stack/jumpdest reasoning. Our bytecode layer … has no fork analogue."* Verified directly: verity's `Compiler/` (Codegen.lean etc.) contains no jumpdest reasoning anywhere; its byte-level gap is the admitted trust assumption (plan:9 — the run-match is *supplied* at `EndToEnd.lean:128`). The forks are precedent that IRs *want* a structured target; none of them has the verified assembler underneath. That layer is genuinely this project's novel asset — the right move is to make it reusable, not to regret it.

- **It can be *paid once*.** The evidence that it factors cleanly out of Lir is already in the tree: (a) the geometry files (ii-a) reason about `emitStmt`-produced *byte lists* and offset sums, never about IR semantics (`Layout.lean` header: decode obligations reduce to "a list-local fact: which byte `flatBytes prog` holds at the pc"); (b) `Corr`'s geometric fields (`pc_eq/code_eq/validJumps_eq/stack_nil`, `SimStmt.lean:106–118`) mention only the lowered code, and `Corr.validJumps_lower` (`:141`) is already a purely structural discharge; (c) exp005 *already contains an assembler* (`emitStmt`/`emitTerm` → `flatBytes` → `offsetTable`) — it's just fused with the IR. The Asm layer is a refactor that de-fuses it, not new proof mass. Estimated one-time cost: re-plumbing ~4,100 lines of (ii-a) plus the geometric third of (ii-b) behind the §2.4 signatures; the proofs themselves move mostly intact.

- **What stays with each IR, irreducibly:** (1) its lowering function into `AsmProgram` and per-statement *effect* simulation — that statement `s` compiles to a body slice whose effect (via the exported post-frame transformers `addFrame`/`sloadFrame`/`gasFrame`/`mstoreFrame`… — usable as-is) matches the IR step; (2) its coupling invariant's semantic fields (Lir's `storage`/`defsSound`/`wellScoped`/`memAgree`); (3) its value-channel strategy (recompute-on-use + spill is a Lir *policy*; (ii-c) ports as a worked pattern, not a library); (4) its oracle ties (the CallRealises-shaped seams). Within-block stack profiles are the IR's business; **block-boundary** profiles should be an `AtCursor` parameter (v1: fix "empty stack at boundaries," Lir's convention).

- **Forward-looking clincher — the real Plank IR.** Memory allocator (non-deterministic placement, UB on undefined access) and data segments (CODECOPY at non-deterministic offsets) are *placement nondeterminism*. Against raw bytes, every IR would fight offset-existentials in decode proofs forever. Against `AsmProgram` with symbolic labels + data handles, nondeterministic placement is the assembler's freedom, and the algebra's theorems (`assemble_decode_at`, `assemble_codecopy_data`) are precisely the quotient by placement. The structured target isn't just convenient — it is the natural home for exactly the features the toy IR lacks.

**Recommendation.** Yes to the structured-assembly intermediate target, exp003-side, as the long-term shape. **IR #2 imports:** `Exec`/`ExecEv` + recorder contract (§2.1–2.2), invariant laws + clean-halt envelopes (§2.3), the Asm algebra (§2.4), the cyclic driver (§2.5), and the existing per-opcode post-frame vocabulary (`Hoare.lean`). **IR #2 still proves:** lowering-to-Asm, per-statement effect sims, its coupling invariant's semantic fields, its value channel, its oracle-tie realisation from the recorded log. That flips the ratio from ~85% substrate / 15% IR (today) to a substrate-free IR proof whose obligations are all IR-shaped — which is precisely the "Philogy can vibe-code passes on it" criterion. One honest caveat: until a second IR actually exercises it, the Asm interface parameterization (opcode alphabet, boundary stack profile, data handles) is a design bet; keep v1 minimal (Lir's 16-opcode alphabet, empty-stack boundaries) and let IR #2's needs — not speculation — drive generalization.

---

## 4. Relationship to remediation Phase 4

**Verdict: extends it; changes its *destination shape* and adds sequencing constraints — does not change its content.** Phase 4 as written (`remediation-plan-2026-07-02.md:43–44`: unify `SelfAt`/`AccMono` → save ~1,000 ln, then per-decl move to `003_bytecode_layer/BytecodeLayer/Hoare/AccountsMonotone.lean`) is exactly the category-(i) TieDischarge slice of §2.3. Two amendments and a concrete order:

1. **Amendment A — destination is the new surface, not a Hoare/ appendix.** Land the relocated material as `BytecodeLayer/Exec.lean` + `Exec/{Recorder,Invariants}.lean` spec files with proofs under `Exec/Proofs/` (Eduardo's spec/proof separation), rather than one more file under `Hoare/`. Same proofs, same effort; the move *is* the surface-creation opportunity — don't spend it twice.
2. **Amendment B — widen category (i) beyond TieDischarge.** Add to the Phase-4 manifest: `MemAlgebra.lean` (978), `CleanHalt.lean`, `CleanHaltExtract.lean` §0–§2, `DriveRuns.lean`, `Charges.lean`, and `RunLog.lean` (recorder + `observe`; the `realisedCall_eq_evmV2` oracle tie stays exp005-side). ~2,700 further lines, all import-clean (verified: `MemAlgebra` imports only `Evm`; `CleanHalt` only `BytecodeLayer.Hoare`; `DriveRuns` only `Hoare.CallSequence`; `Charges` only `Hoare.Sequence`; `RunLog` needs its two `Lir.Oracle` refs split first — note this touches the Phase-2 `Oracle.lean`-deletion decision, so sequence Phase 2 → this move).
3. **Sequencing — the Asm layer (§2.4) is Phase 5, strictly after Phase 3.** Phase 3's realisability closure rewrites the consumers of exactly the (ii-a)/(ii-b) files the Asm refactor would churn; running both concurrently is the churn the workflow memory warns about. Moreover, doing Phase 3 *first* reveals which recorder laws the closure actually needs — build `RunsEv` (§2.2) *as part of* Phase 3 (it is the natural statement language for the S3 trace↔recorder bridge; the plan's step 2 at line 36 is `RunsEv.det_events` in disguise), then promote it to exp003 in Phase 5.

**Concrete migration order:** Phase 2 (gas-law decision, as staged) → Phase 3 with `RunsEv` introduced exp005-side → Phase 4 = unify walks + relocate categories (i) (amendments A+B) into the §2.1–2.3 surface, restate the flagship through `Exec` (frame-free headline) → Phase 5 = extract the Asm algebra from Layout/DecodeLower/LowerDecode/DecodeAnchors/MatDecLower/JumpValid/NoCreateBytes/BoundaryReach, retarget `lower` as `assemble ∘ lowerAsm` with a definitional-equality bridge to `lower prog` so the closed conformance proof survives unmodified → IR #2 starts against the finished surface.

**Key files:** `experiments/005_ir_lowering/LirLean/TieDischarge.lean` (Evm spans :543–587, :604–1486, :1653–2914; engine Lir :1488–1651, :2916–3560; headline :4292 with `Runs` in conclusion :4328–4330), `experiments/003_bytecode_layer/BytecodeLayer/Hoare.lean` (:27 broken encapsulation promise; :52/:91/:114 the frame tier), `Hoare/CallSequence.lean:132`, `Hoare/GasMonotone.lean:251`, `Hoare/Behaves.lean:45` (the unused abstract tier), `LirLean/RunLog.lean:156/:219/:321` (misplaced recorder), `LirLean/CleanHaltExtract.lean:26–28` (missing-inversions admission), `LirLean/SimStmt.lean:103` (Corr), `LirLean/DriveSim.lean:87–:586` (the cyclic driver to generalize), `experiments/005_ir_lowering/docs/remediation-plan-2026-07-02.md:13,43–44`.