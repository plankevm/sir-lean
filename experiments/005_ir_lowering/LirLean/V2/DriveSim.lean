import LirLean.LowerConforms

/-!
# LirLean v2 — drive-indexed forward simulation foundation (`DriveSim`, F1)

The crux brick of the **cyclic** CFG construction
(`experiments/005_ir_lowering/docs/cyclic-cfg-forward-sim-plan.md`). The acyclic
`runFrom_exists` (`V2/IRRun.lean`) builds the IR `RunFrom` by a *static* control-flow
block-rank (`CFGAcyclic`), which has no measure across a back-edge ⇒ no loops. This module
replaces that static measure with the **dynamic bytecode `totalGas`** (`Interpreter/Measure`),
which strictly descends per block *regardless of CFG cycles* — every block runs at least its
leading `JUMPDEST` (`Gjumpdest = 1`), so the successor entry frame holds strictly less gas. That
is the well-founded measure the cyclic recursion will use.

## What this file delivers (F1 — the per-block drive step, plus the foundation)

* **`CleanHalts` / `DriveCorr`** (§2) — the boundary invariant relating a block-entry bytecode
  frame (stack `[]`) to an IR cursor `(L, st)`: `Corr prog … st fr L 0` together with the frame's
  remaining run reaching a clean `.halted` outcome (`CleanHalts fr`), whose `totalGas [] (.inl
  fr) = fr.exec.gasAvailable.toNat` (`driveCorr_measure`) is the recursion measure.
* **`jumpdestFrame_gas_lt` / `totalGas_succ_lt`** (§3) — the **strict `totalGas` descent**: a
  `JUMPDEST` step (cost `Gjumpdest = 1 ≥ 1`) drops `gasAvailable.toNat` by exactly one, so the
  post-`JUMPDEST` successor entry frame's `totalGas` is strictly below the source block-entry
  frame's. This is the per-block descent that makes the drive recursion well-founded.
* **`drive_step_block_halt` / `drive_step_block_jump`** (§4) — the per-block drive step, split by
  IR terminator shape. From `DriveCorr` at block `L` and the IR-side one-block facts (the block's
  `RunStmts` to `st'`, the halt operand / the branch condition), running the block's lowered
  bytecode forward reaches the next boundary, AND the IR takes the matching one-block `RunFrom`
  step:
  - **halt** (`stop`/`ret`): a clean `.halted` bytecode frame whose `observe` *world* is `st'`'s
    world, AND the IR `RunFrom prog o st T L { world := st'.world, result := … }`;
  - **edge** (`jump`): the successor block's entry frame `jumpdestFrame fj` re-establishing
    `DriveCorr` at `dst` with **strictly smaller `totalGas`**, AND the IR one-block continuation
    `∀ O, RunFrom … st' T dst O → RunFrom … st T L O` (prepend this block's `RunStmts` + the
    firing terminator).

  The branch direction is fixed by the **bytecode** (the same condition word `cw = st'.locals
  cond` chooses both the bytecode edge and the IR `RunFrom.branch*` edge — the §7 tie); the
  `branch` arm is the obvious variant of `drive_step_block_jump` with the cond-materialise prefix
  (sketched in §5, not yet instantiated — see the report). The per-statement / per-terminator
  realisability bundles (`SimStmtStep` and the terminator decode/gas/jump-validity bundle) are
  taken as **supplied** hypotheses, per the RE-SCOPE (ties charged later); the deliverable is the
  cyclic *structure* (the block-step with the `totalGas` descent), reusing the existing forward
  bricks (`sim_stmts_block`, `corr_at_jumpdest_landing`, the `sim_term_halt_*` conclusions).

## The clean-halt of the successor — honest threading (NOT fabricated)

Re-establishing `DriveCorr` at the successor needs `CleanHalts` of the successor frame. We do
**not** manufacture it from the source frame's `CleanHalts` (that forward split needs the
deterministic-run reconciliation bridge — an F2 obligation). Instead the successor's clean-halt is
**supplied** alongside the edge's `JUMPDEST` landing (`CleanHalts fj` in the `hjump` bundle): it is
the standing whole-run clean-halt the F2 recursion threads as its base-case witness (F0 scope:
`runWithLog … = some log`). This keeps the per-block step honest — no `sorry`, no fabricated
halt — and isolates the forward-split as the one remaining F2 obligation (see §5 / the report).

Bytecode-coupled (imports the Layer C–E bricks via `LowerConforms`); nothing here touches
`V2/Machine.lean` / `V2/Law.lean` / `V2/MemAlgebra.lean`. No `sorry`/`axiom`/`native_decide`.
-/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open Lir

/-! ## §2 — `CleanHalts` and the boundary invariant `DriveCorr` -/

/-- **Clean-halt of a frame's remaining run.** `fr` reaches, by a run of opcode steps and
returning external calls (`Runs`), a frame `last` that **halts** (`stepFrame last = .halted
halt`). The bytecode side of the F2 base case (`STOP`/`RETURN`), and the standing
well-foundedness witness threaded through the drive recursion. -/
def CleanHalts (fr : Frame) : Prop :=
  ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt

/-- **The drive-boundary invariant `DriveCorr`.** At a block-entry frame (working stack `[]`),
the bytecode frame `fr` is `Corr`-aligned with the IR cursor `(L, st)` at the entry cursor
`(L, 0)`, and `fr`'s remaining run clean-halts. The recursion measure is `fr`'s `totalGas`
(`totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat`, `driveCorr_measure`). -/
structure DriveCorr (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) (L : Label) : Prop where
  /-- The `Corr` boundary at the block-entry cursor `(L, 0)`. -/
  corr : Corr prog sloadChg obs st fr L 0
  /-- `fr`'s remaining bytecode run reaches a clean `.halted` outcome (the measure is finite). -/
  cleanHalts : CleanHalts fr

/-- **The drive measure is `gasAvailable`.** At a block-entry frame (empty pending stack), the
`totalGas` measure of `Measure.lean` collapses to the frame's own `gasAvailable.toNat` — the
quantity that strictly descends across each block. -/
theorem driveCorr_measure (fr : Frame) :
    totalGas [] (.inl fr) = fr.exec.gasAvailable.toNat := by
  simp only [totalGas, activeGas, List.map_nil, List.sum_nil, Nat.add_zero]

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
    {o : V2.CallOracle} {self : AccountAddress} {st st' : V2.IRState} {T T' : Trace}
    {L : Label} {b : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hb : blockAt prog L = some b)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hbterm : b.term = .stop)
    (hrunstmts : V2.RunStmts prog o st T b.stmts st' T')
    -- the terminator world-channel brick (supplied — `sim_term_halt_stop`):
    (hterm : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = st'.world) :
    ∃ last haltSig O, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world
      ∧ RunFrom prog o st T L O ∧ O = { world := st'.world, result := .stopped } := by
  -- Layer D: run the block's statements to the terminator cursor.
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hrunstmts
  -- Layer E (halt): a clean `.halted` frame whose world is `st'.world`.
  obtain ⟨last, haltSig, hlast, hstep, hworld⟩ := hterm frT hcorrT
  exact ⟨last, haltSig, _, hrunsT.trans hlast, hstep, hworld,
    RunFrom.stop hb hrunstmts hbterm, rfl⟩

/-- **`drive_step_block`, the `ret` arm.** As `drive_step_block_stop`, with `b.term = .ret t` and
the operand `st'.locals t = some w` bound at the post-statement state: the IR halts returning `w`
(`RunFrom.ret`), and the bytecode's `observe` *world* matches `st'.world` (the value channel is the
tracked deferral — `observe`'s result is `.stopped`, asserted only on the world). -/
theorem drive_step_block_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {self : AccountAddress} {st st' : V2.IRState} {T T' : Trace}
    {L : Label} {b : Block} {t : Tmp} {w : Word} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hb : blockAt prog L = some b)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hbterm : b.term = .ret t)
    (hrunstmts : V2.RunStmts prog o st T b.stmts st' T')
    (hv : st'.locals t = some w)
    (hterm : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      ∃ last haltSig, Runs frT last ∧ stepFrame last = .halted haltSig
        ∧ (observe self (endFrame last haltSig)).world = st'.world) :
    ∃ last haltSig O, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world
      ∧ RunFrom prog o st T L O ∧ O = { world := st'.world, result := .returned w } := by
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hrunstmts
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
    {o : V2.CallOracle} {st st' : V2.IRState} {T : Trace}
    {L : Label} {b : Block} {dst : Label} {bdst : Block} {fr : Frame}
    (hsim : SimStmtStep prog sloadChg obs o L b)
    (hb : blockAt prog L = some b)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hdrive : DriveCorr prog sloadChg obs st fr L)
    (hterm : b.term = .jump dst)
    (hrunstmts : V2.RunStmts prog o st T b.stmts st' T)
    -- the terminator §7 bundle (supplied): the post-statement `Corr`-frame `frT` runs the
    -- lowered `PUSH4 dest ; JUMP ; ⟨land⟩ JUMPDEST` to the successor's `JUMPDEST` landing `fj`,
    -- with enough gas at the landing AND the successor clean-halt (the standing whole-run witness).
    -- The data `jump_to_block` + `corr_at_jumpdest_landing` consume, exposing `fj` (so the descent
    -- is provable) — discharged for a concrete program exactly as `sim_term_edge_jump`.
    (hjump : ∀ frT : Frame, Corr prog sloadChg obs st' frT L b.stmts.length →
      ∃ fj : Frame, Runs frT fj
        ∧ GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat
        ∧ fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
            prog.blocks dst.idx)
        ∧ fj.exec.executionEnv.code = lower prog
        ∧ fj.validJumps = validJumpDests fj.exec.executionEnv.code 0
        ∧ fj.exec.stack = []
        ∧ fj.exec.executionEnv.canModifyState = true
        ∧ (∀ k, selfStorage fj k = st'.world k)
        ∧ SloadRealises sloadChg st' fj
        ∧ Lir.GasRealises obs fj
        ∧ MemRealises prog st' fj
        ∧ decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none)
        ∧ CleanHalts (jumpdestFrame fj)) :
    ∃ fj : Frame,
        Runs fr (jumpdestFrame fj)
      ∧ DriveCorr prog sloadChg obs st' (jumpdestFrame fj) dst
      ∧ totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)
      ∧ (∀ O, RunFrom prog o st' T dst O → RunFrom prog o st T L O) := by
  -- Layer D: run the block's statements to the terminator cursor.
  obtain ⟨frT, hrunsT, hcorrT, _⟩ := sim_stmts_block hsim hdrive.corr hrunstmts
  -- Layer E: the supplied jump bundle delivers the `JUMPDEST` landing `fj`.
  obtain ⟨fj, hfjrun, hfjgas, hfjpc, hfjcode, hfjvalid, hfjstk, hfjmod, hfjstore,
    hfjsload, hfjgasr, hfjmem, hfjdec, hcleanSucc⟩ := hjump frT hcorrT
  -- the `JUMPDEST` step lands at `(dst, 0)`, re-establishing `Corr`.
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing hbdst hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hcorrT.defsSound hcorrT.wellScoped hfjsload hfjgasr hfjmem hfjdec hfjgas
  refine ⟨fj, (hrunsT.trans hfjrun).trans hjdrun, ⟨hjdcorr, hcleanSucc⟩, ?_, ?_⟩
  · -- strict `totalGas` descent across the block (the JUMPDEST drop).
    exact totalGas_succ_lt (hrunsT.trans hfjrun) hfjgas
  · -- the IR continuation: prepend this block's `RunStmts` + the `jump` terminator.
    intro O hO
    exact RunFrom.jump hb hrunstmts hterm hO

/-! ## §5 — Toward `drive_step_block_branch` and the F2 recursion (sketch, no `sorry`)

**`branch` arm.** `drive_step_block_branch` is the obvious variant of `drive_step_block_jump`: it
takes the IR branch condition `cw = st'.locals cond` and, by `sim_term_edge_branch`, the bytecode
takes the *same* edge — `thenL` when `cw ≠ 0`, `elseL` when `cw = 0` (the bytecode-fixes-the-branch
tie is the shared `cw`). The bytecode-side landing is again a `jumpdestFrame fj` (the taken arm via
`runs_jumpi_taken`/`corr_at_jumpdest_landing`, the fall-through via
`jumpiFallthroughFrame`+`jump_to_block`), so `totalGas_succ_lt` gives the same strict descent. The
IR continuation is `RunFrom.branchThen` / `RunFrom.branchElse` on the supplied `cw`. It is
structurally identical to the `jump` arm; we leave it for the F2 instantiation pass (the `hjump`
bundle there gains the `cw`-cased decode anchors).

**F2 — the drive recursion.** Well-founded recursion on `totalGas [] (.inl fr)`:

```text
theorem driveRunFrom_exists … :
    DriveCorr prog sloadChg obs st fr L →
    ∃ O, RunFrom prog o st T L O := by
  -- strong induction on `totalGas [] (.inl fr)` (= fr.exec.gasAvailable.toNat).
  -- case on `b.term`:
  --   stop/ret  ⇒  drive_step_block_halt  ⇒  ⟨O, hir⟩                       (base)
  --   jump dst  ⇒  drive_step_block_jump  gives `fj`, `DriveCorr … (jumpdestFrame fj) dst`,
  --               `totalGas (jumpdestFrame fj) < totalGas fr`, and the continuation `k`;
  --               the IH at the strictly-smaller measure yields `⟨O, hO⟩ : RunFrom … dst O`;
  --               return `⟨O, k O hO⟩`.                                     (recurse)
  --   branch    ⇒  drive_step_block_branch, symmetric.
```

The measure strictly descends at every recursive call (`totalGas_succ_lt`) **regardless of CFG
cycles** — the back-edge a loop takes is fine, because the measure is the dynamic bytecode gas, not
the static block-rank. This is precisely what `CFGAcyclic` cannot express and what retires it.

**The one remaining F2 obligation** is the *forward clean-halt split*: re-establishing `DriveCorr`
at the successor needs `CleanHalts (jumpdestFrame fj)`, which we **supply** in the `hjump` bundle
rather than derive from `fr`'s `CleanHalts`. Deriving it (the successor lies on `fr`'s unique
deterministic run to the halt, so it reaches the same `.halted`) needs the `drive`/`Runs`
reconciliation bridge to *split* `fr`'s `Runs`-to-halt at the forward frame. That bridge — relating
`Runs`-reachability to the fuelled `driveLog` run whose clean halt is the F0 hypothesis — is the
honest next brick; until it lands, the successor clean-halt rides as a supplied standing witness
(sound: the whole top-level run clean-halts by `runWithLog … = some log`). No `sorry` is incurred
here: the per-block step consumes the witness, it does not fabricate it. -/

end Lir.V2

-- Build-enforced axiom-cleanliness guards for the F1 drive-step deliverables: the strict
-- `totalGas` descent and the per-block drive steps (halt arms + the `jump` edge arm) depend only
-- on `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.V2.driveCorr_measure
#print axioms Lir.V2.jumpdestFrame_gas_lt
#print axioms Lir.V2.totalGas_succ_lt
#print axioms Lir.V2.drive_step_block_stop
#print axioms Lir.V2.drive_step_block_ret
#print axioms Lir.V2.drive_step_block_jump
