import LirLean.Assembly.LowerConforms
import LirLean.V2.IRRun
import BytecodeLayer.Hoare.DriveRuns
import LirLean.Decode.Modellable
-- `Runs.gasAvailable_le` (used below in the gas-descent measure) lives here; imported
-- directly rather than plumbed through `Spec/Recorder.lean` (keeps the trusted spec cone
-- free of this exp003 gas-monotonicity dependency).
import BytecodeLayer.Hoare.GasMonotone

/-!
# LirLean v2 — drive-indexed forward simulation, cyclic-CFG construction (`DriveSim`, F1–F3)

The **cyclic** CFG construction
(`experiments/005_ir_lowering/docs/cyclic-cfg-forward-sim-plan.md`). The acyclic
`runFrom_exists` (`V2/IRRun.lean`) builds the IR `RunFrom` by a *static* control-flow
block-rank (`CFGAcyclic`), which has no measure across a back-edge ⇒ no loops. This module
replaces that static measure with the **dynamic bytecode `totalGas`** (`Interpreter/Measure`),
which strictly descends per block *regardless of CFG cycles* — every block runs at least its
leading `JUMPDEST` (`Gjumpdest = 1`), so the successor entry frame holds strictly less gas. That
is the well-founded measure the cyclic recursion uses (`runFrom_of_driveCorr`, F2), assembled into
the cyclic-general headline `lower_conforms_cyclic` (F3) — **`CFGAcyclic` retired**.

## What this file delivers (F1 foundation + F2/F3 — the full cyclic construction)

* **`DriveCorr`** (§2) — the boundary invariant relating a block-entry bytecode frame (stack `[]`)
  to an IR cursor `(L, st)`: `Corr prog … st fr L 0` together with the frame's remaining run
  reaching a clean **non-exception** `.halted` outcome (`CleanHaltsNonException fr`), whose
  `totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat` (`driveCorr_measure`) is the recursion
  measure. The clean-halt predicates live in `experiments/003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean`.
* **`cleanHaltsNonException_forward`** (`experiments/003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean`) — the **forward clean-halt
  split** (the former wall, now DERIVED). `stepFrame` is a function, so the halting `Runs` path is
  *linear* (`Runs.linear_to_halt`, exp003 `BytecodeLayer/Hoare.lean`): every frame reachable on the
  way to a halt continues to the *same* halt. So `CleanHaltsNonException` is forward-closed along
  `Runs` — a block successor inherits its predecessor's non-exception clean-halt, no longer
  supplied. The predicate and forward split live in `BytecodeLayer/Hoare/CleanHalt.lean` (upstream of both this walk
  and the `SimStmts` induction).
* **`jumpdestFrame_gas_lt` / `totalGas_succ_lt`** (§3) — the **strict `totalGas` descent**: a
  `JUMPDEST` step (cost `Gjumpdest = 1 ≥ 1`) drops `gasAvailable.toNat` by exactly one, so the
  post-`JUMPDEST` successor entry frame's `totalGas` is strictly below the source block-entry
  frame's. This is the per-block descent that makes the drive recursion well-founded.
* **`drive_step_block_{stop,ret,jump,branch}`** (§4) — the per-block drive step, split by IR
  terminator shape. From `DriveCorr` at block `L` and the IR-side one-block facts (the block's
  `RunStmts` to `st'`, the halt operand / the branch condition `cw`), running the block's lowered
  bytecode forward reaches the next boundary, AND the IR takes the matching one-block `RunFrom`
  step:
  - **halt** (`stop`/`ret`): a clean `.halted` bytecode frame whose `observe` *world* is `st'`'s
    world, AND the IR `RunFrom prog o st T L { world := st'.world, result := … }`;
  - **edge** (`jump`/`branch`): the successor block's entry frame `jumpdestFrame fj` re-establishing
    `DriveCorr` at the taken `succ` with **strictly smaller `totalGas`** (and the successor
    clean-halt now DERIVED via `cleanHaltsNonException_forward`), AND the IR one-block continuation `∀ O,
    RunFrom … st' T' succ O → RunFrom … st T L O` (prepend this block's `RunStmts` + the firing
    terminator). The branch direction is fixed by the **bytecode** — the same condition word `cw =
    st'.locals cond` chooses both the bytecode edge and the IR `RunFrom.branch*` edge (the §7 tie).
* **`DriveStep` + `runFrom_of_driveCorr`** (§5/§6, **F2**) — the per-block obligation `DriveStep`
  (halt OR strictly-smaller-`totalGas` edge), and the drive recursion gluing it into a whole IR
  `RunFrom` by **strong induction on `totalGas`**. The measure is the dynamic bytecode gas, so the
  recursion is well-founded *regardless of CFG cycles* — the back-edge a loop takes is fine. This
  is exactly what the static block-rank `CFGAcyclic` cannot express; F2 **retires** it.
* **`lower_conforms_cyclic`** (§7, **F3**) — feed F2's `∃ O, RunFrom …` into the EXISTING
  cycle-agnostic `sim_cfg` to recover the world equation, **general over CYCLIC CFGs** (no
  `CFGAcyclic`/`RunDefinable`). The per-block ties (`SimStmtStep`/`SimTermStep`, the `DriveStep`
  bundle) stay **supplied** per the RE-SCOPE (charged later); the entry `CleanHaltsNonException` is
  the honest scope boundary (the run reaches a `.success`/`.revert` terminal — `runWithLog … = some
  log` plus the non-exception scope premise).

Bytecode-coupled (imports the Layer C–E bricks via `LowerConforms`); nothing here touches
`Spec/Semantics.lean` / `V2/Law.lean` / `BytecodeLayer/Hoare/MemAlgebra.lean`. No `sorry`/`axiom`/`native_decide`.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open Lir

/-! ## §2 — the boundary invariant `DriveCorr` (clean-halt predicates: `experiments/003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean`)

`CleanHalts` / `CleanHaltsNonException` and their forward splits live in `experiments/003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean`
(upstream of both this drive walk and the `SimStmts` per-statement induction, so they are visible
to the whole tower). `open Lir.V2` (this namespace) brings them into scope here. -/

/-- **The drive-boundary invariant `DriveCorr`.** At a block-entry frame (working stack `[]`),
the bytecode frame `fr` is `Corr`-aligned with the IR cursor `(L, st)` at the entry cursor
`(L, 0)`, and `fr`'s remaining run clean-halts to a **non-exception** terminal. The recursion
measure is `fr`'s `totalGas` (`totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat`,
`driveCorr_measure`). The non-exception strengthening (over the bare `CleanHalts`) is what lets the
per-cursor §7 extractor (`CleanHaltExtract`) DERIVE each lowered opcode's gas/mem envelope — a
genuine OOG/exception run, un-modellable by the gas-agnostic IR, is the honest scope boundary. -/
structure DriveCorr (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) (L : Label) : Prop where
  /-- The `Corr` boundary at the block-entry cursor `(L, 0)`. -/
  corr : Corr prog sloadChg obs (fun _ => False) st fr L 0
  /-- `fr`'s remaining bytecode run reaches a clean **non-exception** `.halted` outcome. -/
  cleanHalts : CleanHaltsNonException fr

/-- **The drive measure is `gasAvailable`.** At a block-entry frame (empty pending stack), the
`totalGas` measure of `Measure.lean` collapses to the frame's own `gasAvailable.toNat` — the
quantity that strictly descends across each block. -/
theorem driveCorr_measure (fr : Frame) :
    totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat := by
  simp only [totalGas, activeGas, List.map_nil, List.sum_nil, Nat.add_zero]

/-! ## §2.2 — `hclean` discharged from the clean-halt outcome (`drive → Runs`)

The entry `CleanHaltsNonException fr₀` is no longer a raw hypothesis: it is **derived** from the
honest scope boundary — the recording interpreter reaching a clean `.halted` outcome,
`runWithLog params (seedFuel params.gas) = some log`, *plus* the non-exception scope premise `hne`
(the recorded outcome is `.success`/`.revert`, not OOG/exception). `runWithLog_drive`
(`RecorderLemmas.lean`) pins the verified `drive (seedFuel params.gas) [] (running fr₀) = .ok
log.observable`; the reverse construction `runs_of_drive_ok` (`BytecodeLayer/Hoare/DriveRuns.lean`) reconstructs the
halting `Runs fr₀ last` from that clean termination, under the `Runs`-modellability side condition
(every reachable frame issues a code CALL or a halt — no CREATE / precompile-CALL, discharged
structurally for `lower prog`). -/

/-- **`hclean` from the clean-halt outcome.** From `runWithLog params (seedFuel params.gas) = some
log` (the run reaches a clean `.halted` outcome) and `beginCall params = .inl fr₀` (the entry
frame), the entry frame `CleanHaltsNonException`. The `drive → Runs` reverse construction
(`runs_of_drive_ok`) reconstructs the halting `Runs` from the verified `drive` outcome
`runWithLog_drive` pins, under the `Runs`-modellability of every reachable frame — which is **no
longer a raw supplied universal**: it is **produced** by `lower_modellable` (`Decode/Modellable.lean`)
from the two per-frame residuals

* `CreateResolves` — every reachable CREATE whose init child terminates resumes successfully (the
  63/64 retention guard passing). The former "no CREATE at all" clause is **RETIRED**: `emitStmt
  .create` now emits a real `CREATE2` byte and CREATE is **modelled** by `Runs.create`
  (`runs_of_drive_ok`'s `.needsCreate` arm). `CreateResolves` is the honest R4 residual — a gas
  retention fact, NOT a lowering property (vacuous for any create-free program). Supplied as `hcr`.
* `CallsCode` — every `.needsCall` targets a *code* account, not a precompile `1..10`. The **honest
  residual**: a runtime condition on the program's reachable call targets, NOT a lowering property
  (vacuous for any call-free program). Supplied here as `hcc`.

`lower_modellable` discharges the `runs_of_drive_ok` modellability universal from `hcr`/`hcc` via
the proved reductions (`modellableStep_of`, `beginCall_isCode_of_codeSource_ne_precompiled`).

The **non-exception scope premise** `hne` is the visible, approved scope boundary: the recorded
interpreter outcome routes *any* halt (including `.exception`) to `.ok`, so the reverse
construction alone cannot tell a `.success`/`.revert` terminal from an OOG/exception one. `hne`
records that the run's (linearly-unique) terminal is non-exception — exactly the runs the
gas-agnostic IR can model. It is discharged trivially for any program proved to reach a
`.success`/`.revert` epilogue. -/
theorem cleanHalts_of_runWithLog {prog : Lir.Program} {params : Evm.CallParams} {fr₀ : Frame}
    {log : RunLog}
    (hlog : runWithLog params (Evm.seedFuel params.gas) = some log)
    (hbegin : Evm.beginCall params = .inl fr₀)
    (hcr : ∀ fr', Runs fr₀ fr' → BytecodeLayer.Interpreter.CreateResolves fr')
    (hcc : ∀ fr', Runs fr₀ fr' → BytecodeLayer.Interpreter.CallsCode fr')
    (hne : ∀ last halt, Runs fr₀ last → stepFrame last = .halted halt → HaltNonException halt) :
    CleanHaltsNonException fr₀ := by
  obtain ⟨frame, hbc, hdrive⟩ := runWithLog_drive hlog
  -- `beginCall` pins the entry frame: `frame = fr₀`.
  rw [hbegin] at hbc
  have hfeq : frame = fr₀ := (Sum.inl.injEq _ _).mp hbc.symm
  rw [hfeq] at hdrive
  -- the reverse construction yields the halting `Runs`; modellability is PRODUCED, not supplied —
  -- CREATE is now MODELLED (`Runs.create`), the exclusion RETIRED; the two honest residuals
  -- `CreateResolves` (no CREATE OOG-fault on resume) and `CallsCode` (no precompile CALL) remain.
  obtain ⟨last, halt, hruns, hhalt, _⟩ :=
    BytecodeLayer.Interpreter.runs_of_drive_ok (Evm.seedFuel params.gas) fr₀ log.observable
      hdrive (BytecodeLayer.Interpreter.lower_modellable hcr hcc)
  exact ⟨last, halt, hruns, hhalt, hne last halt hruns hhalt⟩

/-! ## §3 — The strict `totalGas` descent across a block (the KEY new content)

Every block, reached as a jump/branch successor, runs through its leading `JUMPDEST`. The
`JUMPDEST` step charges `Gjumpdest = 1`, so it drops `gasAvailable.toNat` by exactly one — the
post-`JUMPDEST` frame holds strictly less gas. This is the per-block strict descent that makes the
successor entry frame a strictly-smaller `totalGas` measure (so the drive recursion is
well-founded *regardless of CFG cycles* — the back-edge that defeats the static block-rank is fine
here, because the measure is the dynamic bytecode gas, not the CFG shape). -/

/-- **`JUMPDEST` drops `gasAvailable.toNat` by exactly one.** `jumpdestFrame` charges `Gjumpdest =
1` (and `incrPC` leaves gas untouched), so given enough gas the post-frame's `gasAvailable.toNat`
is the pre-frame's minus one. -/
theorem jumpdestFrame_gasToNat (fj : Frame)
    (hgas : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat) :
    (jumpdestFrame fj).exec.gasAvailable.toNat = fj.exec.gasAvailable.toNat - 1 := by
  show (fj.exec.gasAvailable - UInt64.ofNat GasConstants.Gjumpdest).toNat = _
  rw [BytecodeLayer.UInt64.toNat_sub_ofNat fj.exec.gasAvailable GasConstants.Gjumpdest hgas
        (by show (1 : ℕ) < 2 ^ 64; omega)]
  show fj.exec.gasAvailable.toNat - 1 = fj.exec.gasAvailable.toNat - 1
  rfl

/-- **`JUMPDEST` strictly descends `gasAvailable.toNat`.** With `Gjumpdest ≤ gas` the post-frame's
gas is strictly below the pre-frame's — the strict descent the drive recursion needs. -/
theorem jumpdestFrame_gas_lt (fj : Frame)
    (hgas : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat) :
    (jumpdestFrame fj).exec.gasAvailable.toNat < fj.exec.gasAvailable.toNat := by
  rw [jumpdestFrame_gasToNat fj hgas]
  have : (1 : ℕ) ≤ fj.exec.gasAvailable.toNat := hgas
  omega

/-- **The successor-frame strict `totalGas` descent.** If the successor entry frame is a
`JUMPDEST` landing `jumpdestFrame fj` whose pre-`JUMPDEST` frame `fj` is reachable from `fr`
(`Runs fr fj`) and holds enough gas, then its `totalGas` is strictly below `fr`'s: `gasAvailable`
never rises across `Runs fr fj` (`Runs.gasAvailable_le`), and the `JUMPDEST` strictly drops it.
This is the descent the drive recursion measures on. -/
theorem totalGas_succ_lt {fr fj : Frame}
    (hrun : Runs fr fj)
    (hgas : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat) :
    totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr) := by
  rw [driveCorr_measure, driveCorr_measure]
  have hle : fj.exec.gasAvailable.toNat ≤ fr.exec.gasAvailable.toNat := Runs.gasAvailable_le hrun
  have hlt := jumpdestFrame_gas_lt fj hgas
  omega

/-! ## §4 — `drive_step_block`, the per-block drive step

From `DriveCorr` at `L` (block `b`), the lowered bytecode runs forward to the next boundary and
the IR takes the matching one-block `RunFrom` step. We split the conclusion by the IR terminator
shape, supplied as IR-side one-block facts (`RunStmts` to `st'`, the halt operand for `ret`, the
branch condition `cw` for `branch`) — exactly the data the eventual F2 recursion threads (the
`RunDefinable`-style supply of `runFrom_exists`).

### §4.1 — the halt arm (`stop` / `ret`)

A halt terminator bottoms out the recursion: the lowered statements + terminator run to a clean
`.halted` bytecode frame whose `observe` *world* is `st'.world`, and the IR `RunFrom` halts at the
matching observable (constructed here via `RunFrom.stop` / `RunFrom.ret`). We reuse Layer D
(`sim_stmts_block`) for the statements and the supplied Layer E halt brick (exactly
`sim_term_halt_stop` / `sim_term_halt_ret`'s world-channel conclusion) for the terminator. -/

/-- **`drive_step_block`, the `stop` arm.** From `DriveCorr` at `L` (block `b`, `b.term = .stop`)
and the block's IR `RunStmts` to `st'`, the lowered bytecode runs to a clean `.halted` frame `last`
whose `observe self` **world** is `st'.world`, AND the IR halts: `RunFrom prog o st T L ⟨st'.world,
.stopped⟩` (constructed here via `RunFrom.stop`). The terminator world-channel brick is supplied as
`hterm` (exactly `sim_term_halt_stop`'s conclusion). -/
theorem drive_step_block_stop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress} {st st' : V2.IRState} {T T' : Trace} {C C' : CallStream}
    {D D' : CreateStream} {L : Label} {b : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hb : blockAt prog L = some b)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hbterm : b.term = .stop)
    (hrunstmts : V2.RunStmts prog st T C D b.stmts st' T' C' D')
    -- the terminator world-channel brick (supplied — `sim_term_halt_stop`):
    (hterm : ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) st' frT L b.stmts.length →
      ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = st'.world) :
    ∃ last haltSig O, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world
      ∧ RunFrom prog st T C D L O ∧ O = { world := st'.world, result := .stopped } := by
  -- Layer D: run the block's statements to the terminator cursor.
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hdrive.cleanHalts hrunstmts
  -- Layer E (halt): a clean `.halted` frame whose world is `st'.world`.
  obtain ⟨last, haltSig, hlast, hstep, hworld⟩ := hterm frT hcorrT
  exact ⟨last, haltSig, _, hrunsT.trans hlast, hstep, hworld,
    RunFrom.stop hb hrunstmts hbterm, rfl⟩

/-- **`drive_step_block`, the `ret` arm.** As `drive_step_block_stop`, with `b.term = .ret t` and
the operand `st'.locals t = some w` bound at the post-statement state: the IR halts returning `w`
(`RunFrom.ret`), and the bytecode's `observe` *world* matches `st'.world`. (The world channel is
what this driver arm forwards; the returned-value channel — now live in `observe` and proven by
`sim_term_halt_ret` — rides the `Conforms` result conjunct downstream, not this world-only brick.) -/
theorem drive_step_block_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress} {st st' : V2.IRState} {T T' : Trace} {C C' : CallStream}
    {D D' : CreateStream} {L : Label} {b : Block} {t : Tmp} {w : Word} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hb : blockAt prog L = some b)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hbterm : b.term = .ret t)
    (hrunstmts : V2.RunStmts prog st T C D b.stmts st' T' C' D')
    (hv : st'.locals t = some w)
    (hterm : ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) st' frT L b.stmts.length →
      ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = st'.world) :
    ∃ last haltSig O, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world
      ∧ RunFrom prog st T C D L O ∧ O = { world := st'.world, result := .returned w } := by
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hdrive.cleanHalts hrunstmts
  obtain ⟨last, haltSig, hlast, hstep, hworld⟩ := hterm frT hcorrT
  exact ⟨last, haltSig, _, hrunsT.trans hlast, hstep, hworld,
    RunFrom.ret hb hrunstmts hbterm hv, rfl⟩

/-! ### §4.2 — the edge arm (`jump`)

The IR one-block step for an edge is a *continuation*: given a `RunFrom` from the successor `succ`
(the IH of the F2 recursion), prepend this block's `RunStmts` + the firing terminator to obtain a
`RunFrom` from `L`. We package the four outputs — the bytecode `Runs fr fr'`, the re-established
`DriveCorr` at `succ`, the strict descent, and the IR continuation. The bytecode side reuses the
Layer E `corr_at_jumpdest_landing` tail, which exposes the `JUMPDEST` landing `fj`, so the strict
`totalGas` descent (`totalGas_succ_lt`) is **proven**, not assumed. -/

/-- **The JUMPDEST-landing bundle** shared by every edge terminator (`jump`/`branch`, across
`drive_step_block_{jump,branch}`, `driveStep_of_block`, and `lower_conforms_cyclic''`). Packages
what running a block's lowered terminator (`PUSH4 dest ; JUMP` for `jump`, cond-materialise +
`JUMPI` for `branch`) delivers at the taken successor's `JUMPDEST` landing `fj` (reached from the
post-statement frame `frT`): the forward run, the `Gjumpdest` gas margin at the landing, the
landing pc (`target`'s block offset), the code / valid-jumps / stack / can-modify pins, the
storage lens against `st'`, the pre-entry `MemRealises`, and the `JUMPDEST` decode. Named so a
clause reorder does not ripple across the (previously positional) destructurings. -/
structure JumpdestLanding (prog : Program) (st' : V2.IRState) (frT fj : Frame) (target : Label) :
    Prop where
  runs       : Runs frT fj
  gas        : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
  pc         : fj.exec.pc = UInt32.ofNat (offsetTable (matCache prog) (defsOf prog)
                 prog.blocks target.idx)
  code       : fj.exec.executionEnv.code = lower prog
  validJumps : fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
  stack      : fj.exec.stack = []
  canMod     : fj.exec.executionEnv.canModifyState = true
  storage    : ∀ k, selfStorage fj k = st'.world k
  mem        : MemRealises prog st' fj
  jumpdest   : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)

/-- **`drive_step_block`, the `jump` arm.** From `DriveCorr` at `L` (block `b`, `b.term = .jump
dst`) and the block's IR `RunStmts` (gas-free, trace unchanged) to `st'`, running the lowered
statements (`sim_stmts_block`) then the supplied `PUSH4; JUMP; ⟨land⟩ JUMPDEST` (the Layer E
`jump_to_block` data, exposing the `JUMPDEST` landing `fj`) reaches the successor `dst`'s entry
frame `jumpdestFrame fj`, with:

* `Runs fr (jumpdestFrame fj)` — the bytecode forward run to the next boundary;
* `DriveCorr … st' (jumpdestFrame fj) dst` — the re-established boundary at `dst` (`Corr` via
  `corr_at_jumpdest_landing`; the successor clean-halt `hcleanSucc` supplied — the standing
  whole-run witness F2 threads, NOT fabricated from `fr`'s);
* `totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)` — the **strict descent**;
* the IR continuation `∀ O, RunFrom … st' T dst O → RunFrom … st T L O` (prepend this block's
  `RunStmts` + the `jump` terminator via `RunFrom.jump`).

The decode/gas/jump-validity bundle for the terminator and the `Gjumpdest` margin at the landing
are supplied as the structured `hjump` hypothesis (the §7 ties), exactly as `sim_term_edge_jump`
takes them; `hjump` is dischargeable for a concrete program from `jump_to_block`'s internals. -/
theorem drive_step_block_jump {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : V2.IRState} {T : Trace} {C C' : CallStream} {D D' : CreateStream}
    {L : Label} {b : Block} {dst : Label} {bdst : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hb : blockAt prog L = some b)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hterm : b.term = .jump dst)
    (hrunstmts : V2.RunStmts prog st T C D b.stmts st' T C' D')
    -- the terminator §7 bundle (supplied): the post-statement `Corr`-frame `frT` runs the
    -- lowered `PUSH4 dest ; JUMP ; ⟨land⟩ JUMPDEST` to the successor's `JUMPDEST` landing `fj`,
    -- with enough gas at the landing. The data `jump_to_block` + `corr_at_jumpdest_landing`
    -- consume, exposing `fj` (so the descent is provable) — discharged for a concrete program
    -- exactly as `sim_term_edge_jump`. The successor clean-halt is NO LONGER supplied: it is
    -- DERIVED via `cleanHaltsNonException_forward` from `fr`'s clean-halt (`hdrive.cleanHalts`).
    (hjump : ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) st' frT L b.stmts.length →
      ∃ fj : Frame, JumpdestLanding prog st' frT fj dst) :
    ∃ fj : Frame,
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorr prog sloadChg obs st' (jumpdestFrame fj) dst
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog st' T C' D' dst O → RunFrom prog st T C D L O) := by
  -- Layer D: run the block's statements to the terminator cursor.
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hdrive.cleanHalts hrunstmts
  -- Layer E: the supplied jump bundle delivers the `JUMPDEST` landing `fj`.
  obtain ⟨fj, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk, hfjmod, hfjstore,
    hfjmem, hfjdec⟩ := hjump frT hcorrT
  -- the `JUMPDEST` step lands at `(dst, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbdst hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore ((defsSoundS_empty_iff prog st').mp hcorrT.defsSound) hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from `fr`'s (the forward split — was supplied).
  have hcleanSucc : CleanHaltsNonException (jumpdestFrame fj) :=
    cleanHaltsNonException_forward hdrive.cleanHalts hfrrun
  refine ⟨fj, hfrrun, ⟨hjdcorr, hcleanSucc⟩, ?_, ?_⟩
  · -- strict `totalGas` descent across the block (the JUMPDEST drop).
    exact totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas
  · -- the IR continuation: prepend this block's `RunStmts` + the `jump` terminator.
    intro O hO
    exact RunFrom.jump hb hrunstmts hterm hO

/-! ### §4.3 — the branch arm (`branch`)

The structural twin of `drive_step_block_jump`. The IR branch condition `cw = st'.locals cond`
fixes the taken edge — `thenL` when `cw ≠ 0`, `elseL` when `cw = 0` — and the **same** `cw`
fixes the bytecode edge (the §7 condition tie). The taken successor's bytecode landing is again a
`JUMPDEST` entry frame `jumpdestFrame fj` (the THEN arm via `runs_jumpi_taken` +
`corr_at_jumpdest_landing`; the ELSE fall-through via `jumpiFallthroughFrame` + `jump_to_block`,
whose tail is also a `corr_at_jumpdest_landing` landing), so `totalGas_succ_lt` gives the same
strict descent and `cleanHaltsNonException_forward` derives the successor's clean-halt. The IR continuation is
`RunFrom.branchThen` / `RunFrom.branchElse` on the supplied `cw`. The terminator §7 bundle
(`hbranch`) is the `branch` analogue of `hjump`: it resolves the taken successor `succ` (with its
direction witness) and exposes the `JUMPDEST` landing `fj`, exactly the data
`sim_term_edge_branch` consumes; it is dischargeable for a concrete program from that lemma's
internals. -/

/-- **`drive_step_block`, the `branch` arm.** From `DriveCorr` at `L` (block `b`, `b.term =
.branch cond thenL elseL`), the block's IR `RunStmts` to `st'` (trace `T → T'`), and the bound
condition `st'.locals cond = some cw`, running the lowered statements then the cond-materialise +
`JUMPI` lands at the **taken** successor `succ`'s entry frame `jumpdestFrame fj` (`succ = thenL`
when `cw ≠ 0`, `succ = elseL` when `cw = 0`), with:

* `Runs fr (jumpdestFrame fj)` — the bytecode forward run to the next boundary;
* `DriveCorr … st' (jumpdestFrame fj) succ` — the re-established boundary at the taken `succ`
  (`Corr` via `corr_at_jumpdest_landing`; the successor clean-halt DERIVED via
  `cleanHaltsNonException_forward` from `fr`'s);
* `totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)` — the **strict descent**;
* the IR continuation `∀ O, RunFrom … st' T' succ O → RunFrom … st T L O` (prepend this block's
  `RunStmts` + the firing `branch` terminator via `RunFrom.branchThen` / `.branchElse`).

The cond-materialise/`JUMPI`/landing bundle is supplied as `hbranch` (the §7 ties), exactly as
`sim_term_edge_branch` takes them; it resolves the taken successor and exposes `fj`. -/
theorem drive_step_block_branch {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : V2.IRState} {T T' : Trace} {C C' : CallStream} {D D' : CreateStream}
    {L : Label} {b : Block} {cond : Tmp} {cw : Word} {thenL elseL : Label} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hb : blockAt prog L = some b)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hterm : b.term = .branch cond thenL elseL)
    (hrunstmts : V2.RunStmts prog st T C D b.stmts st' T' C' D')
    (hc : st'.locals cond = some cw)
    -- the terminator §7 bundle (supplied): the post-statement `Corr`-frame `frT` runs the lowered
    -- cond-materialise + `JUMPI` to the TAKEN successor's `JUMPDEST` landing `fj`, with the taken
    -- successor `succ` resolved by `cw` (`thenL` if `cw ≠ 0`, `elseL` if `cw = 0`) and present.
    -- This is the data `sim_term_edge_branch` produces, exposing `fj` (so the descent is provable).
    -- The successor clean-halt is DERIVED (not supplied) via `cleanHaltsNonException_forward`.
    (hbranch : ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) st' frT L b.stmts.length →
      ∃ (succ : Label) (bsucc : Block) (fj : Frame),
        ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
        ∧ prog.blocks.toList[succ.idx]? = some bsucc
        ∧ JumpdestLanding prog st' frT fj succ) :
    ∃ (succ : Label) (fj : Frame),
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorr prog sloadChg obs st' (jumpdestFrame fj) succ
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog st' T' C' D' succ O → RunFrom prog st T C D L O) := by
  -- Layer D: run the block's statements to the terminator cursor.
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hdrive.cleanHalts hrunstmts
  -- Layer E: the supplied branch bundle resolves the taken successor `succ` and its
  -- `JUMPDEST` landing `fj`.
  obtain ⟨succ, bsucc, fj, hdir, hbsucc, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk,
    hfjmod, hfjstore, hfjmem, hfjdec⟩ := hbranch frT hcorrT
  -- the `JUMPDEST` step lands at `(succ, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbsucc hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore ((defsSoundS_empty_iff prog st').mp hcorrT.defsSound) hcorrT.wellScoped hfjmem hfjdec hfjgas
  -- the bytecode forward run to the successor entry frame `jumpdestFrame fj`.
  have hfrrun : Runs fr (jumpdestFrame fj) := (hrunsT.trans hfjrun).trans hjdrun
  -- DERIVE the successor clean-halt from `fr`'s (the forward split).
  have hcleanSucc : CleanHaltsNonException (jumpdestFrame fj) :=
    cleanHaltsNonException_forward hdrive.cleanHalts hfrrun
  refine ⟨succ, fj, hfrrun, ⟨hjdcorr, hcleanSucc⟩, totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas,
    ?_⟩
  -- the IR continuation: prepend this block's `RunStmts` + the firing `branch` terminator.
  intro O hO
  rcases hdir with ⟨hsucc, hnz⟩ | ⟨hsucc, hz⟩
  · subst hsucc
    exact RunFrom.branchThen hb hrunstmts hterm hc hnz hO
  · subst hsucc; subst hz
    exact RunFrom.branchElse hb hrunstmts hterm hc hO

/-! ## §5 — `DriveStep`, the per-block drive obligation (F2's quantified hypothesis)

The F2 recursion needs, **at every block-entry boundary `DriveCorr … st fr L`** it reaches, the
matching per-block fact: either a halting block (yielding the IR halt observable `O` and `O.world
= st'.world`), or an edge (a strictly-smaller-`totalGas` successor `DriveCorr … st' fr' succ`,
plus the IR continuation `RunFrom … st' T' succ O → RunFrom … st T L O`). `DriveStep` is exactly
that disjunction, quantified over all reachable `(st, fr, L)` — it is the abstraction the F1
per-block steps (`drive_step_block_stop`/`_ret`/`_jump`/`_branch`) discharge from the supplied
§7 ties + the IR-side block runs. Threading it through the recursion (rather than the raw bundles)
keeps F2 a clean well-founded recursion and isolates the supplied surface in one predicate. -/

/-- **The per-block drive obligation.** From `DriveCorr … st fr L` at a block-entry boundary,
either the block **halts** — producing the IR observable `O` with `O.world` the bytecode's
halt-world (and a matching `RunFrom … st T L O`) — or it takes an **edge** to a successor `succ`
whose re-established `DriveCorr` has **strictly smaller `totalGas`**, together with the IR
continuation `RunFrom … st' T' succ O → RunFrom … st T L O`. This is the disjunction `drive_step_
block_{stop,ret}` (halt) and `drive_step_block_{jump,branch}` (edge) discharge; F2 recurses on it.

The trace `T'` / IR state `st'` of the edge are existential here (the F1 steps realise them from
the supplied IR block run); the recursion only consumes the `totalGas` descent and the two
`RunFrom` pieces. -/
def DriveStep (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream)
    (D : CreateStream) : Prop :=
  -- halt arm: the block bottoms out, IR halts at `O` matching the bytecode world.
  (∃ O : V2.Observable, RunFrom prog st T C D L O)
  ∨
  -- edge arm: a strictly-smaller successor boundary + the IR continuation.
  (∃ (st' : V2.IRState) (T' : Trace) (C' : CallStream) (D' : CreateStream)
      (succ : Label) (fr' : Frame),
      DriveCorr prog sloadChg obs st' fr' succ
    ∧ totalGas [] (.inl fr') < totalGas [] (.inl fr)
    ∧ (∀ O, RunFrom prog st' T' C' D' succ O → RunFrom prog st T C D L O))

/-! ## §5.1 — `driveStep_of_block`: assemble a `DriveStep` from the per-block ties

`DriveStep` is `runFrom_of_driveCorr`'s quantified hypothesis. `driveStep_of_block` discharges
it **at one block** from: `DriveCorr` at `L`; the block present (`blockAt prog L = some b`); the
per-block §7 ties (`SimStmtStep` for the statements, and — dispatched on `b.term` — the halt
world-channel brick / the `jump`/`branch` edge bundles that `drive_step_block_*` consume); and the
static **operand-definability** `RunDefinable` (`V2/IRRun.lean`). Note this is **not** benign:
`StmtDefinable` is `False` for `.call`/`.create` and excludes `.gas`, so `RunDefinable prog` is
UNSATISFIABLE for any program touching those channels — it silently restricts the caller to the
PURE fragment (the honest gas/call-aware replacement is `RunDefinableG`, Spec/WellFormed.lean). The
IR block run itself is
built forward by `runStmts_exists` (`RunStmts b.stmts` to `stmtsPost st b.stmts`, trace unchanged),
exactly the per-block forward body `runFrom_exists` runs; we then case on `b.term` and dispatch:

* `stop` / `ret` → `drive_step_block_{stop,ret}`, packaged as the **halt** disjunct (LEFT);
* `jump` / `branch` → `drive_step_block_{jump,branch}`, packaged as the **edge** disjunct (RIGHT).

So `hstep` of `lower_conforms_cyclic` is no longer a raw hypothesis: it is produced uniformly from
`RunDefinable` + the per-block ties (`lower_conforms_cyclic'` below). -/

/-- **`driveStep_of_block`.** From `DriveCorr` at `L`, the block present, the per-statement tie
`SimStmtStep`, the static operand-definability `RunDefinable`, and the terminator-shape ties
(`hhalt` for `stop`/`ret`, `hjump`/`hbranch` for the edges — exactly the bundles
`drive_step_block_*` consume), produce the per-block drive obligation `DriveStep`. The IR block
run is `runStmts_exists`; the conclusion is the halt disjunct for `stop`/`ret`, the edge disjunct
for `jump`/`branch`. -/
theorem driveStep_of_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress}
    {st : V2.IRState} {fr : Frame} {L : Label} {T : Trace} {C : CallStream} {D : CreateStream}
    {b : Block}
    (hb : blockAt prog L = some b)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hsim : SimStmtStep prog sloadChg obs L b)
    (hdef : RunDefinable prog)
    -- the halt world-channel brick (used only on `stop`/`ret`, exactly `sim_term_halt_*`):
    (hhalt : ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) (stmtsPost st b.stmts) frT L b.stmts.length →
      ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = (stmtsPost st b.stmts).world)
    -- the `jump` destination block's presence (static, replacing `CFGAcyclic.succ_present`):
    (hjumpPresent : ∀ (dst : Label), b.term = .jump dst →
      ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `jump` edge bundle (used only on `jump dst`, exactly `drive_step_block_jump`'s):
    (hjump : ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) (stmtsPost st b.stmts) frT L b.stmts.length →
        ∃ fj : Frame, JumpdestLanding prog (stmtsPost st b.stmts) frT fj dst)
    -- the `branch` edge bundle (used only on `branch cond thenL elseL`):
    (hbranch : ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) (stmtsPost st b.stmts) frT L b.stmts.length →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ JumpdestLanding prog (stmtsPost st b.stmts) frT fj succ) :
    DriveStep prog sloadChg obs st fr L T C D := by
  -- run the block's statements forward (gas-free / call-free / create-free, definable from any
  -- state — so the gas trace `T`, the call stream `C` AND the create stream `D` are threaded
  -- unchanged).
  have hrunstmts : V2.RunStmts prog st T C D b.stmts (stmtsPost st b.stmts) T C D :=
    runStmts_exists (hdef.stmts st L b hb)
  set st' := stmtsPost st b.stmts with hst'
  -- dispatch on the terminator shape.
  cases hterm : b.term with
  | stop =>
    -- halt disjunct (LEFT) via `drive_step_block_stop`.
    obtain ⟨_, _, O, _, _, _, hir, _⟩ :=
      drive_step_block_stop (self := self) hsim hb hdrive hterm hrunstmts hhalt
    exact Or.inl ⟨O, hir⟩
  | ret t =>
    -- halt disjunct (LEFT) via `drive_step_block_ret`; the operand is `RunDefinable.ret_def`.
    obtain ⟨w, hv⟩ := hdef.ret_def st L b t hb hterm
    obtain ⟨_, _, O, _, _, _, hir, _⟩ :=
      drive_step_block_ret (self := self) hsim hb hdrive hterm hrunstmts hv hhalt
    exact Or.inl ⟨O, hir⟩
  | jump dst =>
    -- edge disjunct (RIGHT) via `drive_step_block_jump`; `dst`'s presence via `hjumpPresent`.
    obtain ⟨bdst, hbdst⟩ := hjumpPresent dst hterm
    obtain ⟨fj, hfrrun, hdcorr, hlt, hcont⟩ :=
      drive_step_block_jump hsim hb hbdst hdrive hterm hrunstmts (hjump dst hterm)
    exact Or.inr ⟨st', T, C, D, dst, jumpdestFrame fj, hdcorr, hlt, hcont⟩
  | branch cond thenL elseL =>
    -- edge disjunct (RIGHT) via `drive_step_block_branch`; the condition is `RunDefinable`.
    obtain ⟨cw, hc⟩ := hdef.branch_def st L b cond thenL elseL hb hterm
    obtain ⟨succ, fj, hfrrun, hdcorr, hlt, hcont⟩ :=
      drive_step_block_branch hsim hb hdrive hterm hrunstmts hc (hbranch cond thenL elseL cw hterm hc)
    exact Or.inr ⟨st', T, C, D, succ, jumpdestFrame fj, hdcorr, hlt, hcont⟩

/-! ## §6 — F2, the drive recursion: `runFrom_of_driveCorr`

By strong induction on `totalGas [] (.inl fr)` (= `fr.exec.gasAvailable.toNat`,
`driveCorr_measure`), glue the per-block `DriveStep`s into a whole IR `RunFrom`. The halt arm is
the base case (the block bottoms out); the edge arm recurses at the strictly-smaller successor
`DriveCorr` (the descent makes this well-founded **regardless of CFG cycles** — the back-edge a
loop takes is fine, the measure is the dynamic bytecode gas, not the static block-rank), then
prepends the block via the supplied IR continuation. This is exactly what `CFGAcyclic` cannot
express and what retires it. -/

/-- **F2 — `runFrom_of_driveCorr`.** From `DriveCorr … st fr L` and the per-block drive obligation
`DriveStep` available at **every** reachable boundary, the IR `RunFrom prog o st T L` exists for
some observable `O`. Proved by strong induction on the bytecode `totalGas` measure (which strictly
descends per block, `totalGas_succ_lt`), so it holds for **cyclic** CFGs — no `CFGAcyclic`. -/
theorem runFrom_of_driveCorr {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    (hstep : ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream)
        (D : CreateStream),
      DriveCorr prog sloadChg obs st fr L → DriveStep prog sloadChg obs st fr L T C D) :
    ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream) (D : CreateStream),
      DriveCorr prog sloadChg obs st fr L → ∃ O, RunFrom prog st T C D L O := by
  -- strong induction on the bytecode `totalGas` measure of the boundary frame.
  intro st fr L T C D hdrive
  -- generalise the goal over `(st, L, T, C, D)` so the IH applies at the successor's data.
  induction hmeasure : totalGas [] (.inl fr) using Nat.strong_induction_on
    generalizing st fr L T C D with
  | _ n ih =>
    subst hmeasure
    rcases hstep st fr L T C D hdrive with
      ⟨O, hir⟩ | ⟨st', T', C', D', succ, fr', hdrive', hlt, hcont⟩
    · -- halt arm: the block bottoms out.
      exact ⟨O, hir⟩
    · -- edge arm: recurse at the strictly-smaller successor, then prepend the block.
      obtain ⟨O, hO⟩ := ih (totalGas [] (.inl fr')) hlt st' fr' succ T' C' D' hdrive' rfl
      exact ⟨O, hcont O hO⟩

/-! ## §7 — F3, `lower_conforms_cyclic`: feed F2's `RunFrom` into `sim_cfg`

F2 builds a `RunFrom prog (realisedCall log self) … prog.entry O` for the clean-halting bytecode
run, over **cyclic** CFGs. F3 feeds it into the EXISTING cycle-agnostic `sim_cfg` (ties still
supplied) to recover the world equation `O.world = (observe self log.observable).world` — a
headline with **no `CFGAcyclic` / `RunDefinable`**. The entry `Corr` comes from the entry frame
(as the acyclic headline builds it); the entry `CleanHalts` is the single clean-halt hypothesis
(the whole run reaches `.halted` — supplied here as the honest scope boundary, `runWithLog … =
some log`). -/

/-- **F3 — `lower_conforms_cyclic` (driver).** Given the entry `Corr` and the entry frame's
`CleanHalts` (the run clean-halts) plus the per-block drive obligation `DriveStep` at every
boundary and the `sim_cfg` ties, the world equation holds for the F2-constructed run's existential
observable — **general over CYCLIC CFGs** (no `CFGAcyclic`/`RunDefinable`; `runFrom_of_driveCorr`'s
`totalGas` measure replaces the static block-rank). The entry `DriveCorr` is assembled from the
entry `Corr` + the entry `CleanHalts`; F2 yields `∃ O, RunFrom … prog.entry O`; `sim_cfg` ties it
to the bytecode halt's world. -/
theorem lower_conforms_cyclic {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress}
    {st₀ : V2.IRState} {T : Trace} {C : CallStream} {D : CreateStream} {fr₀ : Frame}
    -- the entry boundary: `Corr` at `(prog.entry, 0)` + the run clean-halts NON-EXCEPTIONALLY
    -- (honest scope: the run reaches a `.success`/`.revert` terminal — not a genuine
    -- OOG/exception, which the gas-agnostic IR cannot model).
    (hentry : Corr prog sloadChg obs (fun _ => False) st₀ fr₀ prog.entry 0)
    (hclean : CleanHaltsNonException fr₀)
    -- the per-block drive obligation at every reachable boundary (the §7 ties, supplied):
    (hstep : ∀ (st : V2.IRState) (fr : Frame) (L : Label) (T : Trace) (C : CallStream)
        (D : CreateStream),
      DriveCorr prog sloadChg obs st fr L → DriveStep prog sloadChg obs st fr L T C D)
    -- the `sim_cfg` per-block ties (supplied — charged later):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs self L b) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world)
      ∧ RunFrom prog st₀ T C D prog.entry O := by
  -- F2: build the IR `RunFrom` from the entry `DriveCorr` (cyclic-general, totalGas-measured).
  obtain ⟨O, hir⟩ :=
    runFrom_of_driveCorr hstep st₀ fr₀ prog.entry T C D ⟨hentry, hclean⟩
  -- the EXISTING cycle-agnostic `sim_cfg`: tie the constructed run to the bytecode halt world.
  obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := sim_cfg hstmts hterm hentry hclean hir
  exact ⟨O, ⟨last, haltSig, hlast, hhalt, hworld⟩, hir⟩

/-! ### §7.1 — `lower_conforms_cyclic'`: `hstep` discharged from `RunDefinable` + the per-block ties

`lower_conforms_cyclic` carries the raw per-boundary obligation `hstep : DriveCorr → DriveStep`.
`lower_conforms_cyclic'` removes it: `hstep` is **produced** at every boundary by
`driveStep_of_block` from the static operand-definability `RunDefinable` and the per-block ties
(`SimStmtStep` for the statements, the halt world-channel brick, and the `jump`/`branch` edge
bundles), each quantified over all `(st, L, b)`. So the only raw hypotheses left are the entry
boundary, the entry `CleanHalts` (the honest scope), `RunDefinable`, and the per-block §7 ties —
not a `DriveStep` placeholder. -/

/-- **F3′ — `lower_conforms_cyclic'`.** As `lower_conforms_cyclic`, but with the raw `hstep`
hypothesis replaced by the static operand-definability `RunDefinable` and the per-block tie
families (`hhalt`/`hjumpPresent`/`hjump`/`hbranch`, quantified over all `(st, L, b)`):
`driveStep_of_block` assembles the per-boundary `DriveStep` from them, so `hstep` is no longer
supplied. -/
theorem lower_conforms_cyclic' {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {self : AccountAddress}
    {st₀ : V2.IRState} {T : Trace} {C : CallStream} {D : CreateStream} {fr₀ : Frame}
    (hentry : Corr prog sloadChg obs (fun _ => False) st₀ fr₀ prog.entry 0)
    (hclean : CleanHaltsNonException fr₀)
    -- static operand-definability `RunDefinable` (`V2/IRRun.lean`). NOT benign: `StmtDefinable`
    -- is `False` for `.call`/`.create` and excludes `.gas`, so this premise is UNSATISFIABLE for
    -- any program using those channels — it restricts `lower_conforms_cyclic'` to the PURE
    -- fragment. The honest gas/call-aware replacement is `RunDefinableG` (Spec/WellFormed.lean).
    (hdef : RunDefinable prog)
    -- block presence at every reachable boundary (the CFG is closed; `Corr`'s `pc_eq` alone does
    -- not pin `L` in range, so presence is supplied — vacuous wherever no `DriveCorr` is reached):
    (hpresent : ∀ (st : V2.IRState) (fr : Frame) (L : Label),
      DriveCorr prog sloadChg obs st fr L → ∃ b, blockAt prog L = some b)
    -- the per-statement tie (`sim_cfg`'s + `driveStep_of_block`'s):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs self L b)
    -- the halt world-channel brick, at every block / post-statement frame:
    (hhalt : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) (stmtsPost st b.stmts) frT L b.stmts.length →
        ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
          ∧ (observe self (endFrame last haltSig)).world = (stmtsPost st b.stmts).world)
    -- the `jump` destination presence, at every block:
    (hjumpPresent : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
        ∃ bdst : Block, prog.blocks.toList[dst.idx]? = some bdst)
    -- the `jump` edge bundle, at every block / post-statement frame:
    (hjump : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (dst : Label), b.term = .jump dst →
      ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) (stmtsPost st b.stmts) frT L b.stmts.length →
        ∃ fj : Frame, JumpdestLanding prog (stmtsPost st b.stmts) frT fj dst)
    -- the `branch` edge bundle, at every block / post-statement frame:
    (hbranch : ∀ (st : V2.IRState) (L : Label) (b : Block), blockAt prog L = some b →
      ∀ (cond : Tmp) (thenL elseL : Label) (cw : Word),
      b.term = .branch cond thenL elseL →
      (stmtsPost st b.stmts).locals cond = some cw →
      ∀ frT : Frame, Corr prog sloadChg obs (fun _ => False) (stmtsPost st b.stmts) frT L b.stmts.length →
        ∃ (succ : Label) (bsucc : Block) (fj : Frame),
          ((succ = thenL ∧ cw ≠ 0) ∨ (succ = elseL ∧ cw = 0))
          ∧ prog.blocks.toList[succ.idx]? = some bsucc
          ∧ JumpdestLanding prog (stmtsPost st b.stmts) frT fj succ) :
    ∃ O : V2.Observable,
      (∃ last haltSig, Runs fr₀ last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = O.world)
      ∧ RunFrom prog st₀ T C D prog.entry O := by
  -- assemble the per-boundary `DriveStep` from `driveStep_of_block` at each reachable block.
  refine lower_conforms_cyclic (self := self) hentry hclean ?_ hstmts hterm
  intro st fr L T' C' D' hdrive
  -- the block at `L` is present (supplied at every reachable boundary).
  obtain ⟨b, hb⟩ := hpresent st fr L hdrive
  exact driveStep_of_block (self := self) hb hdrive (hstmts L b hb) hdef
    (hhalt st L b hb) (hjumpPresent L b hb) (hjump st L b hb) (hbranch st L b hb)

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the cyclic-CFG deliverables: the strict `totalGas`
-- descent, the four per-block drive steps, the F2 recursion (`runFrom_of_driveCorr`) and the F3
-- assembly (`lower_conforms_cyclic`) depend only on `[propext, Classical.choice, Quot.sound]`.
-- (The forward clean-halt split lives in `experiments/003_bytecode_layer/BytecodeLayer/Hoare/CleanHalt.lean`, guarded there.)
