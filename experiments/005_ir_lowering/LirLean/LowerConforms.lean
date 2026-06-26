import LirLean.SimTerm

/-!
# LirLean — `sim_cfg` + `lower_conforms` (Layer **F** of the general `lower_conforms` grind)

The capstone of the call-free, **world-channel** `lower_conforms` grind. It threads the
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

## Scope — call-free, world channel

The block's statements must be `CallFree` (Layer D's scope — the lowered CALL leaves its
success flag on the bytecode stack, breaking the `stack = []` induction; folded in once the
flag is consumed). And the channel is the **world** (storage) component: `observe`'s `result`
is the value-free `.stopped` boundary (the RETURN value channel is the tracked deferral,
`V2/RunLog.lean` `observe` doc). `sim_cfg`'s conclusion asserts the world component of
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

/-! ## `sim_cfg` — the whole-CFG simulation

Induction on `V2.RunFrom`. Each constructor:

* runs the block's `CallFree` statement list via Layer D (`sim_stmts_block`), from `Corr` at
  the block entry `(L, 0)` to `Corr` at the terminator cursor `(L, b.stmts.length)` with the
  working stack back to `[]`;
* then dispatches on the terminator: `stop`/`ret` halt via `SimTermStep.halt` (the world
  matches `st'.world`, which is the IR halt's world); `jump`/`branch` run to the successor's
  entry via `SimTermStep.edge`, re-establishing `Corr`, and the **IH** closes the recursion.

`RunFrom` is an inductive `Prop`, so the structural recursion on the derivation is well-founded
— no fuel. The whole-program call-freedom and per-block simulation are supplied uniformly as
the two `∀`-quantified structured hypotheses. -/

/-- **`sim_cfg` — whole-program CFG simulation (call-free, world channel).** From `Corr` at the
entry cursor `(L, 0)` and a `V2.RunFrom prog o st T L O`, where every block reached is
`CallFree` and supplies the per-statement (`SimStmtStep`) and per-terminator (`SimTermStep`)
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
    (hcf : ∀ (L : Label) (b : Block), blockAt prog L = some b → CallFree b.stmts)
    {st : V2.IRState} {T : Trace} {L : Label} {O : V2.Observable} {fr : Frame}
    (hcorr : Corr prog sloadChg obs st fr L 0)
    (hrun : V2.RunFrom prog o st T L O) :
    ∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world := by
  induction hrun generalizing fr with
  | @ret st st' T T' L b t w hb hss hterm' hv =>
    -- Layer D: run the block's statements to the terminator cursor.
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    -- Layer E: `ret` halts with world = st'.world (the IR ret halt's world).
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ :=
      (hterm L b hb).halt st' frT hcorrT (Or.inr ⟨t, hterm'⟩)
    exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld⟩
  | @stop st st' T T' L b hb hss hterm' =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ :=
      (hterm L b hb).halt st' frT hcorrT (Or.inl hterm')
    exact ⟨last, haltSig, hrunsT.trans hlast, hhalt, hworld⟩
  | @branchThen st st' T T' L b cond cw thenL elseL O hb hss hterm' hc hnz hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    -- Layer E (edge): step to `thenL`'s entry, re-establishing `Corr` at `(thenL, 0)`.
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT thenL hcorrT
        (Or.inr (Or.inl ⟨cond, elseL, cw, hterm', hc, hnz⟩))
    -- IH on the recursion into `thenL`, from the re-established `Corr`.
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩
  | @branchElse st st' T T' L b cond thenL elseL O hb hss hterm' hc hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT elseL hcorrT
        (Or.inr (Or.inr ⟨cond, thenL, hterm', hc⟩))
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩
  | @jump st st' T T' L b dst O hb hss hterm' hrest ih =>
    obtain ⟨frT, hrunsT, hcorrT, _⟩ :=
      sim_stmts_block (hstmts L b hb) hcorr hss (hcf L b hb)
    obtain ⟨fr', hruns', hcorr'⟩ :=
      (hterm L b hb).edge st' frT dst hcorrT (Or.inl hterm')
    obtain ⟨last, haltSig, hlast, hhalt, hworld⟩ := ih hcorr'
    exact ⟨last, haltSig, (hrunsT.trans hruns').trans hlast, hhalt, hworld⟩

/-! ## `paramsFor` — the canonical top-level params running `lower prog`

`paramsFor prog accounts gas` is the `CallParams` that runs `lower prog` as a top-level code
call over `accounts` at gas `gas`, with the self/caller/origin pinned to `selfAddr` (the
storage lens `observe`/`Corr` read). It is the generic analogue of `WorkedCall.wcParams`, with
the program and the world (as the `accounts` map carrying the self account's storage) free.
`lower_conforms` is stated over an *abstract* `p : CallParams` with `EntersAsCode p fr₀`; the
canonical instantiation is `p := paramsFor …`, whose `EntersAsCode` is `paramsFor_entersAsCode`
(`beginCall_code`, the entry frame is `codeFrame (paramsFor …) (lower prog)`). The IR world
`w₀` is the self account's storage lens through `selfStorage`/`storageAt` (the `StorageAgree`
clause of the carried entry `Corr`), so it is determined by `accounts` rather than threaded
separately. -/

/-- **The canonical top-level params for `lower prog`.** Runs `lower prog` as a `.Code` call
over `accounts` at gas `gas`, self = caller = origin = recipient = `selfAddr`. The generic
analogue of `WorkedCall.wcParams`. -/
def paramsFor (prog : Program) (selfAddr : AccountAddress) (accounts : AccountMap)
    (gas : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := accounts, originalAccounts := ∅, substate := default,
    caller := selfAddr, origin := selfAddr, recipient := selfAddr,
    codeSource := .Code (lower prog), gas := gas, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-- **`paramsFor` enters as code.** `beginCall (paramsFor …)` descends into
`codeFrame (paramsFor …) (lower prog)` — the entry frame `lower_conforms`'s `hbegin` consumes
when instantiated at `p := paramsFor …`. -/
theorem paramsFor_entersAsCode (prog : Program) (selfAddr : AccountAddress)
    (accounts : AccountMap) (gas : UInt64) :
    EntersAsCode (paramsFor prog selfAddr accounts gas)
      (codeFrame (paramsFor prog selfAddr accounts gas) (lower prog)) :=
  beginCall_code (paramsFor prog selfAddr accounts gas) (lower prog) rfl

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

The entry `Corr` (`hentry`), per-block simulations (`hstmts`/`hterm`), call-freedom (`hcf`),
and the IR run (`hir`) are the structured hypotheses — the supplied-observation realisability
contract. `runWithLog` at the seed fuel makes the `messageCall` bridge exact. -/

/-- **`lower_conforms` (call-free, world channel — under the realisability contract).** For a
program `prog`, initial world `w₀`, self address `self`, observable IR run `O` and run log
`log`: if the recording run `runWithLog p (seedFuel p.gas)` over the top-level params `p`
(canonically `paramsFor prog self accounts gas`, whose `EntersAsCode` is
`paramsFor_entersAsCode`) succeeds with `log`, the lowered program enters from a
`Corr`-corresponding entry frame (`hentry`) whose per-block simulations
(`hstmts`/`hterm`) and call-freedom (`hcf`) hold, and the IR runs under the realised oracles to
`O` (`hir`), then **the IR observable's world equals the `observe` world of the recorded
bytecode result**:

  `O.world = (observe self log.observable).world`.

The world edge is fully discharged from `sim_cfg` + the `messageCall` bridge + `IRRun.det`; the
IR run itself and the per-block realisability are the carried hypotheses (the §7
supplied-observation contract). -/
theorem lower_conforms {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {O : V2.Observable} {p : CallParams} {log : RunLog} {fr₀ : Frame}
    {sloadChg : Tmp → ℕ} {obs : Word}
    -- the recording run succeeded over the lowered program at the seed fuel:
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    -- the lowered program enters as code from `fr₀`, in `Corr` at the entry `(prog.entry, 0)`:
    (hbegin : EntersAsCode p fr₀)
    (hentry : Corr prog sloadChg obs { locals := fun _ => none, world := w₀ } fr₀ prog.entry 0)
    -- the per-block simulations + call-freedom (the realisability contract over `lower prog`):
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs (realisedCall log self) L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs (realisedCall log self) self L b)
    (hcf : ∀ (L : Label) (b : Block), blockAt prog L = some b → CallFree b.stmts)
    -- the IR run under the realised oracles (the IR side of the conformance diagram):
    (hir : V2.IRRun prog (realisedCall log self) w₀ (realisedGas log) O) :
    O.world = (observe self log.observable).world := by
  -- `sim_cfg`: the lowered run halts with world = O.world (the IR observable's world).
  obtain ⟨last, haltSig, hruns, hhalt, hworld⟩ :=
    sim_cfg (self := self) hstmts hterm hcf hentry hir
  -- the `messageCall` bridge, two ways: the assembled `Runs` halt, and the recorder.
  have hmc_runs : messageCall p = .ok (FrameResult.toCallResult (endFrame last haltSig)) :=
    messageCall_runs p hbegin hruns hhalt
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

end Lir

-- Build-enforced axiom-cleanliness guards for the Layer-F deliverables: the whole-CFG
-- simulation `sim_cfg` and the headline `lower_conforms` (call-free, world channel) depend
-- only on `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.sim_cfg
#print axioms Lir.lower_conforms
#print axioms Lir.paramsFor_entersAsCode
