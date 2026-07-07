import LirLean.V2.Drive.Headline
import LirLean.Assembly.Acyclic
import LirLean.Decode.BoundaryReach
import LirLean.Spec.WellFormed
import LirLean.Spec.Conformance

/-!
# LirLean v2 — Realisability spec, SURFACE (§1–§4)

Split out of `RealisabilitySpec.lean` for legibility (pure relocation, no proof change).
Holds the sorry-free helper definitions (§1), the recorder-restart coupling (§2), the
reshaped ties `StmtTies'`/`TermTies'` (§3), and exact stream consumption (§4). See
`RealisabilitySpec.lean` for the module-level overview and the vacuity lessons. -/

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Hoare
open BytecodeLayer.Interpreter
open BytecodeLayer.Dispatch

/-! ## §1 — Helper definitions (all REAL; no sorry)

The flagship's hypothesis vocabulary that has NOT yet been hoisted to the trusted surface:
the static well-formedness bundle, the shadowing-aware CALL tie, the honest oracle seams,
and the scope seams. The sorry-free vocabulary already lifted into `Spec/` — `entryState`,
`RunLog.clean`, `Conforms`, `NoGasReads` (`Spec/Conformance.lean`), the `RunFromLeft`/
`RunFromAll` mirror (`Spec/Semantics.lean`), and `evmV2CallEntry`/`evmV2CreateEntry`
(`Spec/CallEntry.lean`) — is `open`ed via the imports above. Still stranded here (blocked on
the `CallsCode`/`AccPresent` relocations, plan §1D/§1E): `PrecompileAssumptions`,
`ReachableFrom`, `WellFormedLowered`. -/

/-- **Static CFG closure** — entry present and pc-bounded, every jump/branch target present,
in-bounds, and offset-bounded. Folds the current headline's `hentry0`-adjacent presence
facts, `hjumpPresent`, `hbranchPresent`, and the `offsetTable … < 2^32` bounds that
`entry_corr` and the edge bundles consume. SUPPLIED status: static, a finite check on the
program text (the R9 checker's territory); R8 is its named consumer (kills the inside-out
`hpresent`). -/
structure ClosedCFG (prog : Program) : Prop where
  /-- The entry block is present. -/
  entry_present : ∃ b, blockAt prog prog.entry = some b
  /-- The entry block's byte offset fits a 32-bit pc (what `entry_corr` consumes). -/
  entry_bound :
    offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32
  /-- Every jump target is present, in-bounds, and offset-bounded. -/
  jump_closed : ∀ (L : Label) (b : Block) (dst : Label),
    blockAt prog L = some b → b.term = .jump dst →
    (∃ b', blockAt prog dst = some b')
    ∧ dst.idx < prog.blocks.size
    ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx < 2 ^ 32
  /-- Both branch targets are present, in-bounds, and offset-bounded. -/
  branch_closed : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    ((∃ b', blockAt prog thenL = some b')
      ∧ thenL.idx < prog.blocks.size
      ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx < 2 ^ 32)
    ∧ ((∃ b', blockAt prog elseL = some b')
      ∧ elseL.idx < prog.blocks.size
      ∧ offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx < 2 ^ 32)

/-- **The shadowing-aware CALL realisability tie** — `Lir.CallRealises`
(`LowerConforms.lean:261`) with its embedded `Lir.StepScoped prog st0 (.call cs)`
conjunct replaced by the static `StepScopedS prog (.call cs)` (header lesson 8: the
embedded live-scope clause for the result tmp is refutable WITHIN the R10a hypothesis
envelope for any `WellLowered` program whose call result has a registered reader — not
at `exProg` itself, whose `t5` has none, but the disease shape is identical). Everything
else is VERBATIM the in-tree kernel: the realised `(result, pd)` oracle pinning, the
arg-push run + its pins, the returning `CallReturns` + resume-frame pins, the post-state
scoping fold (derivable: prior-live tmps from the `Corr` antecedent's `wellScoped`,
locals untouched by the world swap; the result tmp from `DefsConsistent`'s call clause),
and the Route-B tail. The `obs` phantom is pinned to `0` (as everywhere in this file).
The copy is deliberate, recorded Phase-3 unification debt: the R0b reshape re-plumbs
`sim_call_stmt`'s input to this form and retires the in-tree original (this track edits
no existing files). -/
def CallRealisesS (prog : Program) (sloadChg : Tmp → ℕ)
    (L : Label) (_b : Block) (pc : Nat) (cs : CallSpec) (st0 st0' : IRState) (fr0 : Frame) :
    Prop :=
  Lir.Corr prog sloadChg 0 st0 fr0 L pc →
  ∃ (result : Evm.CallResult) (pd : Evm.PendingCall) (callFr resumeFr : Frame)
      (argsLen : Nat),
    -- the STATIC per-step scoping of the call statement (lesson 8; was `StepScoped`):
    StepScopedS prog (.call cs)
    -- the realised post-state pin: the consumed call-stream head IS this call's recorded
    -- `evmV2CallEntry` effect (the positional multi-call tie — no single-call restriction):
    ∧ st0' = (match cs.resultTmp with
        | some t' => { st0 with world := fun key =>
                        evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }.setLocal
                        t' (callSuccessFlag result pd)
        | none   => { st0 with world := fun key =>
                        evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key })
    -- the arg-push run + its pins (the realised arg materialisation):
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
    ∧ resumeFr.exec.executionEnv.address = fr0.exec.executionEnv.address
    ∧ resumeFr.exec.executionEnv.code = lower prog
    ∧ resumeFr.exec.executionEnv.canModifyState = true
    ∧ resumeFr.exec.pc = callFr.exec.pc + 1
    ∧ resumeFr.exec.stack = callSuccessFlag result pd :: []
    ∧ resumeFr.exec.toMachineState.memory = callFr.exec.toMachineState.memory
    ∧ callFr.exec.toMachineState.activeWords.toNat
        ≤ resumeFr.exec.toMachineState.activeWords.toNat
    ∧ resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0
    -- the post-state scoping fold (derivable — see the docstring):
    ∧ (∀ t, (match cs.resultTmp with
              | some t' => { st0 with world := fun key =>
                              evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }.setLocal
                              t' (callSuccessFlag result pd)
              | none   => { st0 with world := fun key =>
                              evmCallOracle.postStorage result pd fr0.exec.executionEnv.address key }).locals t ≠ none →
            (¬ Lir.NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
            ∧ defsOf prog t ≠ none)
    -- the Route-B tail's realisability (decode anchors + gas + memory-expansion witness):
    ∧ (∀ flag : Word, resumeFr.exec.stack = flag :: [] →
        (∀ (t : Tmp), cs.resultTmp = some t →
          (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
          ∧ ∃ endFr,
              Runs resumeFr endFr
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

/-- **The static well-formedness bundle** (the flagship's `hwl`) — a function of the program
text only, intended to be checker-dischargeable (R9). Folds the current headline's
`hwfl`/`hdef`/`hentry0`/presence/offset/stack-fold hypotheses into one named structure.
SUPPLIED status: one static premise; every field is decidable-in-principle per program.
NOTE the `defs` field is `RunDefinableG`, NOT the in-tree `RunDefinable` — see header
lesson 4 (the in-tree bundle is unsatisfiable for gas/call programs). -/
structure WellLowered (prog : Program) : Prop where
  /-- The folded structural side-conditions (`MatFueled` + pc/offset bounds + slot
  registration) of the `_lowered` wrappers. -/
  wf : Lir.WellFormedLowered prog
  /-- Gas/call-aware operand definability (replaces the unsatisfiable `RunDefinable`). -/
  defs : RunDefinableG prog
  /-- Static `defsOf`-cursor consistency (header lesson 6): every def-site agrees with
  `defsOf`'s first-find registration — excludes the spill-stash/shadowing mismatch that
  refutes the flagship (`RunDefinableG` alone does NOT: its gas arm is unconditionally
  true, which is what opened the hole). -/
  defsCons : DefsConsistent prog
  /-- The entry block is block 0 (its leading `JUMPDEST` is byte 0 = the entry frame's pc). -/
  entry0 : prog.entry.idx = 0
  /-- Static CFG closure (entry/jump/branch presence + offset bounds). -/
  closed : ClosedCFG prog
  /-- The static per-cursor stack-room folds. -/
  stack : StackRoomOK prog
  /-- **Gas-stash pc bound** (R1's `hpcbound`). At every spilled-`.gas` cursor the
  `[GAS] ++ PUSH ++ MSTORE` stash's pc range fits a 32-bit pc (`decode_gasstash`'s
  `+ 34 < 2^32`). Absent from `WellFormedLowered` (which carries no gas-stash bound); a
  static, decidable, checker-dischargeable well-formedness fact — the sibling of
  `bound_sstore`/`bound_sload`, keyed to the gas stash. SUPPLIED status: static per program. -/
  gasBound : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t .gas) →
    pcOf prog L pc + 34 < 2 ^ 32
  /-- **Spill-slot addressability** at every gas/sload cursor: the target tmp's slot is byte-
  and platform-addressable (`slotOf t = t.id * 32`, a bound on tmp ids). Not derivable from
  the program's control structure; in-tree it is always *supplied* to the sim lemmas
  (`SimStmt.lean:630`, `LowerConforms.lean:436/467`). SUPPLIED status: static, decidable. -/
  slotAddr : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt prog L = some b →
    (b.stmts[pc]? = some (.assign t .gas)
      ∨ ∃ k, b.stmts[pc]? = some (.assign t (.sload k))) →
    slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
  /-- **The ret epilogue's pc-bound seam** (R5's `hretEmit`). The 101-byte
  `PUSH32 0; MSTORE; PUSH32 32; PUSH32 0; RETURN` full-observable epilogue after the
  return-value materialise fits a 32-bit pc. `WellFormedLowered.bound_ret` only bounds
  `termOf + |materialise t|` (the operand), not the epilogue (a default-target
  under-specification not editable here); a static, satisfiable, checker-dischargeable
  well-formedness fact, genuinely true of every real ret block. -/
  retEpilogueBound : ∀ (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    termOf prog L + (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length + 100
      < 2 ^ 32
  /-- **No `.slot` source RHS** (the arm-1 direction of `slots_slot`): a source `assign t e`
  never carries the lowering-only `.slot` marker. Vacuous for real IR (no source program
  writes a `.slot` expression — the `WellFormed` invariant `slots_slot`'s docstring cites);
  static and decidable. Excludes the degenerate `defsOf t = .slot n` a pure-assign cursor
  could otherwise register (which would refute the pure-assign arm's not-spilled conclusion). -/
  noSlotSource : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp) (n : Nat),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t (.slot n)) → False

/-- A frame reachable from the call's entry frame: `beginCall params` began a frame and
`Runs` reaches `fr'` from it. The quantifier shape `PrecompileAssumptions.callsCode` needs (and
exactly the `hcc` shape `cleanHalts_of_runWithLog` consumes, once `hbegin` is split off).
The fleet sketch named this `ReachableFrom` without defining it; this is the definition. -/
def ReachableFrom (params : CallParams) (fr' : Frame) : Prop :=
  ∃ fr₀, beginCall params = .inl fr₀ ∧ Runs fr₀ fr'

/-- **The honest oracle seams** (the flagship's `hseams`) — the precompile boundary, both
faces. `noErase` is verbatim the `hprec` hypothesis of `callPreservesSelf_modGuards`
(a live precompile's `.inr` result map genuinely can erase accounts — opaque, honestly
supplied; vacuous for non-precompile-targeting programs). `callsCode` is the reachable-CALL
targets-code residual (`V2/Modellable.lean`; NOT a lowering property — an IR call whose
callee materialises a precompile address would violate it; vacuous for call-free programs).
SUPPLIED status: the irreducible seam structure — both fields are satisfiable and
non-vacuous, and neither is dischargeable from the program text. (`prog` is carried for
signature stability — a future refinement scopes `callsCode` by the program's call sites.)
NON-VACUITY GUARD: `noErase` quantifies over ALL `CallParams` (a global engine fact), so
the flagship's whole hypothesis set is satisfiable only if the current exp003 `beginCall`
precompile stub actually preserves account presence — R12a deliberately DOUBLES as the
machine-check of that engine fact (its `PrecompileAssumptions exProg params` conjunct); a failure
there is diagnosed as a SEAM problem with the engine stub, not an `exProg` problem. -/
structure PrecompileAssumptions (prog : Program) (params : CallParams) : Prop where
  /-- Precompile no-erase (`hprec`): an immediate `.inr` result preserves account presence. -/
  noErase : ∀ (cp : CallParams) (imm : CallResult), beginCall cp = .inr imm →
    ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts
  /-- Every reachable frame's CALLs target code accounts, never a precompile. -/
  callsCode : ∀ fr', ReachableFrom params fr' → CallsCode fr'


/-! ## §2 — The recorder-restart coupling (the hard design piece)

The tie reshape's carrier (target-architecture §3, SETTLED as option (i)): instead of the
free-`∀` value variables, the walk invariant carries ONE real coupling field — *restarting
the recording interpreter at the current top-level boundary frame reproduces the run's final
observable and exactly the un-consumed suffixes of the recorded streams*. The tie value
conjuncts then pin themselves to the SUFFIX HEAD, which the antecedent (restart determinism)
links to the run — no free VALUE variable survives. (The SCOPING conjuncts carried their own
copy of the disease, invisible to this §: the round-3 repair is header lesson 8 / `StepScopedS`.)

Design notes (each load-bearing):

* **`restart` is the load-bearing field**: `driveLog` is a deterministic function, so a
  restart equation from `fr` pins the suffixes AND `log.observable` simultaneously — an
  adversarial `(fr, suffix)` pair must actually reproduce the recorded future, which is
  what makes the R1-style head equations derivable rather than refutable.
* The restart uses pending stack `[]` because coupling is stated at TOP-LEVEL boundary
  frames only (`Corr.stack_nil` cursors) — the same `stack.isEmpty` gate `driveLog` records
  under.
* **Child calls are black-boxed correctly**: a descended CALL's internal GAS/SLOAD reads are
  invisible to the restart exactly as to the original recording (the `stack.isEmpty` gate),
  so `recorderCoupled_call` consumes exactly one `CallRecord` and NO gas/sload entries.
* **Cyclic-correct**: a loop revisits the same cursor with different gas; the coupling is
  indexed by the FRAME (whose gas differs per visit), never by the cursor — no per-cursor
  value function anywhere (the fatal flaw of the rejected option (iii)).
* The three prefix fields make "consumed so far" explicit (the R10 assembly reads them);
  the entry instance is the whole log with `pre = []` (`recorderCoupled_entry`). -/

/-- **Recorder-restart coupling.** Restarting the recording interpreter at the current
top-level boundary frame `fr` reproduces the run's final observable and exactly the
un-consumed suffixes of the recorded streams; each suffix is genuinely a suffix of its
recorded stream. SUPPLIED status: never supplied to the flagship — R7 establishes it at
entry and preserves it across steps/calls; the ties CONSUME it as an antecedent. -/
structure RecorderCoupled (log : RunLog) (fr : Frame)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) : Prop where
  /-- The load-bearing restart equation: some fuel replays `fr`'s future to exactly
  `(log.observable, gasSuffix, sloadSuffix, callSuffix, log.creates)`. The create channel is
  pinned to the FULL `log.creates` (no suffix variable): the R7 walk only traverses
  gas/sload/call/halt edges — none records a CREATE — so no create is ever consumed before a
  coupled boundary frame, and the future's create stream is invariantly the whole `log.creates`
  (established at entry, preserved by every edge). A create-suffix parameter (the Step-6
  `createSuffix`/`createPrefix` twin) is only needed once the walk itself steps through a
  top-level CREATE (Step 8, when `exProg` exercises one). -/
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] [] []
      = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix, log.creates)
  /-- The gas suffix is a suffix of the recorded gas stream. -/
  gasPrefix : ∃ pre, log.gas = pre ++ gasSuffix
  /-- The sload suffix is a suffix of the recorded sload stream. -/
  sloadPrefix : ∃ pre, log.sloads = pre ++ sloadSuffix
  /-- The call suffix is a suffix of the recorded call stream. -/
  callPrefix : ∃ pre, log.calls = pre ++ callSuffix

/-- **The recoupled walk invariant** — the future replacement of `DriveCorrPlus`'s four
dead accumulator lists (which are NOT edited here; Phase 3 proper swaps them). Carried at
every top-level block-entry boundary of the drive walk:

* `corr`/`cleanHalts` — the existing `DriveCorr` content (the cursor + the non-exception
  scope), with the phantom `obs` parameter pinned to `0` (audit-confirmed unused by `Corr`;
  slated for deletion in the Phase-3 reshape — NOT deleted here, no edits to existing files);
* `present` — the reached label is present (R8's consumer; kills the inside-out `hpresent`);
* `selfPresent`/`addrPin`/`kindPin` — decision-4's rfl-preserved companions: they are what
  KILLS the unsatisfiable `TermTies` stop/ret address/kind/nonempty conjuncts (those demands
  become antecedents supplied by this invariant, and non-emptiness is DERIVED via
  `accounts_ne_empty_of_selfPresent`);
* `coupled` — the §2 recorder coupling at the un-consumed suffixes.

SUPPLIED status: never supplied — established at entry (R7 entry + `entry_corr` +
`selfPresent_codeFrame`) and preserved by the walk (R7 edges + `stepPreservesSelf` +
`callPreservesSelf_modGuards hprec`). -/
structure DriveCorrLog (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog)
    (self : AccountAddress) (st : IRState) (fr : Frame) (L : Label)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord) :
    Prop where
  /-- The `Corr` boundary at the block-entry cursor `(L, 0)` (phantom `obs` pinned to 0). -/
  corr : Lir.Corr prog sloadChg 0 st fr L 0
  /-- The non-exception clean-halt scope from this boundary on. -/
  cleanHalts : CleanHaltsNonException fr
  /-- The reached label is present (R8 threads it; seeded from `ClosedCFG.entry_present`). -/
  present : ∃ b, blockAt prog L = some b
  /-- The self account is present (seeded by the flagship's `hself`; preserved by
  `stepPreservesSelf` / `callPreservesSelf_modGuards`). -/
  selfPresent : SelfPresent fr
  /-- The frame executes at the self address (rfl-preserved along the walk). -/
  addrPin : fr.exec.executionEnv.address = self
  /-- The frame is a call frame (rfl-preserved along the walk). -/
  kindPin : ∃ cp, fr.kind = .call cp
  /-- The §2 recorder-restart coupling at the un-consumed suffixes. -/
  coupled : RecorderCoupled log fr gasSuffix sloadSuffix callSuffix

/-! ## §3 — The reshaped ties `StmtTies'` / `TermTies'` (R0 as statements; no free value-∀)

The five statement arms and four terminator arms of the former `StmtTies`/`TermTies`
(since-deleted; formerly `LowerConforms.lean:1273-1423`), re-stated so that every formerly-free
value variable is pinned by an antecedent:

* every arm's antecedent block is: cursor statement + `Corr` (phantom `obs := 0`) +
  `RecorderCoupled` + `CleanHaltsNonException`; the suffix variables are ∀-bound but
  antecedent-pinned through the (deterministic) restart equation — an adversarial witness
  must reproduce the recorded future, which is what makes the value conclusions derivable;
* the gas arm's free `ob = …` equation becomes `gS.head? = some …` (R1 supplies it);
* the sload arm's free `w` becomes the antecedent-pinned `st0.world kv` under
  `st0.locals k = some kv` (the planned `∃ w, evalExpr … = some w` conclusion was itself
  refutable by an empty-locals `Corr` witness — header lesson 5 — so the key binding is an
  antecedent, exactly as the sstore arm's operand bindings always were);
* the plain-assign arm's free `st0'` becomes the pinned post-state `st0.setLocal t w` under
  the `evalExpr st0 0 e = some w` antecedent (the `EvalStmt.assignPure` hypothesis), and the
  arm no longer fires on `.gas`/`.sload` (killing the static contradiction with `defsOf`'s
  spilling);
* the sstore arm DROPS `∃ acc, SstoreRealises fr0 kw vw acc` entirely (header lesson 3 —
  unsatisfiable); its content returns point-wise at the concrete frame (R4). Zero writes
  (slot clears) are now in scope — `sim_sstore` covers `vw = 0` — so the arm has no
  nonzero-write conclusion and no nonzero-write scope antecedent;
* the `TermTies` stop/ret address/kind demands become ANTECEDENTS (supplied by
  `DriveCorrLog`'s rfl-preserved pins), and non-emptiness is the only stop conclusion
  (derivable via `accounts_ne_empty_of_selfPresent`); the ret arm's bare
  `∃ vw, st'.locals t = some vw` conclusion is DROPPED (refutable by an empty-locals `Corr`
  witness; at real states `RunDefinableG.ret_def` supplies it) — the epilogue block is
  stated under the `∀ vw`-antecedent it always had, now strengthened with an explicit pc
  pin (`frv.pc = frT.pc + |materialise t|`) so its decode conclusions are static
  `DecodeAnchors` facts rather than claims about every stack-coincident frame;
* the jump/branch gas-guard conclusions are kept verbatim but now under the
  `CleanHaltsNonException frT` antecedent, which blocks the zero-gas refutation (skeptic
  sub-claim 4's strengthening) and makes them derivable by the
  the jump pre-`JUMPDEST` landing/the branch pre-`JUMPDEST` landing extractors;
* successor-presence conjuncts are gone from the ties (they live in `ClosedCFG`; the
  jump/branch arms take presence as antecedents, supplied by the walk from R8);
* **(round 3, header lesson 8)** every `Lir.StepScoped` conclusion (arms 1–4) is replaced
  by the static `StepScopedS`, and the call arm's `Lir.CallRealises` by `CallRealisesS`:
  the embedded live-scope clauses ("no bound tmp's registered def reads the target") were
  refutable at `exProg`'s own second loop iteration — block 1, pc 0 (`t6 := gas` vs the
  live `t8 ↦ lt t6 t7`) and pc 1 (`t7 := 1000` vs the same `t8`) — at real on-run states
  consistent with every antecedent. Staleness accounting moved to the invalidation set
  (`invalStep`/`DefsSoundS`, R0b); the ties now claim only the static residue.

SUPPLIED status of both defs: never supplied to the flagship — R10 BUILDS them from the
run (`stmtTies'_of_runWithLog`/`termTies'_of_runWithLog`). PRECISION NOTE on the arms'
conclusions (the round-2 review's overclaim fix — they are NOT all "computed from `fr0`
and restart determinism"): each conclusion is one of (i) a static fact of `prog`,
derivable from `hwl` + the cursor (the `StepScopedS`/registration/canonicity/
addressability/stack-fold/pc-bound conjuncts), (ii) a fact carried over from the arm's
own antecedents (the `setLocal`-scoping folds from `Corr.wellScoped` + `DefsConsistent`;
the post-assign `MemRealises` from `Corr.memAgree`), or (iii) a value/trace fact computed from `fr0`/`frT` + restart
determinism under the clean-halt antecedent (the `gS.head?` equation, the CALL kernel,
the gas guards, the epilogue anchors). No conclusion depends on a variable that is not
antecedent-pinned or static — that is the honest residue of the "no free-∀" slogan. -/

/-- **The reshaped per-block STATEMENT ties** (the R0 statement-side). See the section
docstring for the reshape rationale, arm by arm. `self` is consumed by the call arm's
head-of-`callSuffix` post-state pin. DERIVED (R10): built from `hrun`/`hclean`/`hseams` +
`WellLowered`; never supplied. -/
def StmtTies' (prog : Program) (sloadChg : Tmp → ℕ) (log : RunLog)
    (self : AccountAddress) (L : Label) (b : Block) : Prop :=
  -- (1) plain assign (neither `.gas` nor `.sload _`): post-state PINNED by the `evalExpr`
  -- antecedent; conclusions are the not-spilled fact, the STATIC per-step scoping
  -- (`StepScopedS`, lesson 8), and the pinned-post-state scoping/memory ties.
  (∀ (pc : Nat) (t : Tmp) (e : Expr) (w : Word) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t e) →
      e ≠ .gas → (∀ k, e ≠ .sload k) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      evalExpr st0 0 e = some w →
      (∀ n, defsOf prog t ≠ some (.slot n))
      ∧ StepScopedS prog (.assign t e)
      ∧ (∀ t', (st0.setLocal t w).locals t' ≠ none →
            (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
            ∧ defsOf prog t' ≠ none)
      ∧ Lir.MemRealises prog (st0.setLocal t w) fr0)
  -- (2) spilled sload assign: the key binding is an ANTECEDENT (`kv`), the read value is
  -- the storage lens at `kv` (definitional under the antecedent), the post-state is pinned.
  -- Slot registration/canonicity, addressability, the stack-room fold (sourced from
  -- `StackRoomOK.sloadKey` + `Corr.stack_nil`) and the activeWords-flatness stay.
  ∧ (∀ (pc : Nat) (t k : Tmp) (kv : Word) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t (.sload k)) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      st0.locals k = some kv →
      defsOf prog t = some (.slot (slotOf t))
      ∧ StepScopedS prog (.assign t (.sload k))
      ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
      ∧ evalExpr st0 0 (.sload k) = some (st0.world kv)
      ∧ (∀ t', (st0.setLocal t (st0.world kv)).locals t' ≠ none →
            (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
            ∧ defsOf prog t' ≠ none)
      ∧ (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
      ∧ fr0.exec.stack.size
          + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k)).length ≤ 1024
      ∧ (∀ frk : Frame,
          Lir.MatRuns (defsOf prog) sloadChg (recomputeFuel prog - 1) (.tmp k) kv fr0 frk →
          frk.exec.toMachineState.activeWords = fr0.exec.toMachineState.activeWords))
  -- (3) spilled gas assign — THE R1 CONJUNCT: the un-consumed gas suffix's HEAD is the
  -- machine GAS output at this frame (replaces the free-`ob` equation; the coupling +
  -- clean-halt antecedents make it derivable, R1). Post-state scoping is over the pinned
  -- head value. Slot registration/canonicity/addressability/pc-bound stay.
  ∧ (∀ (pc : Nat) (t : Tmp) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.assign t .gas) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      defsOf prog t = some (.slot (slotOf t))
      ∧ StepScopedS prog (.assign t .gas)
      ∧ (∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
      ∧ gS.head? = some (UInt256.ofUInt64
          (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))
      ∧ (∀ t', (st0.setLocal t (UInt256.ofUInt64
              (fr0.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase))).locals t' ≠ none →
            (¬ Lir.NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
            ∧ defsOf prog t' ≠ none)
      ∧ ((slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ pcOf prog L pc + 34 < 2 ^ 32))
  -- (4) sstore: `StepScopedS` + the stack-room fold. Zero writes (slot clears) are IN scope
  -- now — `sim_sstore` covers `vw = 0` via `Evm.Storage.findD_erase_self` — so the arm has
  -- no nonzero-write conclusion and no nonzero-write scope antecedent. The unsatisfiable
  -- `∃ acc, SstoreRealises …` conjunct is GONE (its content is R4, point-wise).
  ∧ (∀ (pc : Nat) (key value : Tmp) (kw vw : Word) (st0 : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (cS : List CallRecord),
      b.stmts[pc]? = some (.sstore key value) →
      Lir.Corr prog sloadChg 0 st0 fr0 L pc →
      RecorderCoupled log fr0 gS sS cS →
      CleanHaltsNonException fr0 →
      st0.locals key = some kw → st0.locals value = some vw →
      StepScopedS prog (.sstore key value)
      ∧ (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
          + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length + 1 ≤ 1024)
  -- (5) call: `CallRealisesS` keyed on the coupling's `callSuffix` HEAD (lesson 8: the in-tree
  -- `CallRealises` embeds `StepScoped (.call cs)`, whose live-scope clause is refutable
  -- in-envelope for reader-carrying programs), kept shape-wise (it is itself
  -- `Corr → ∃ …`), under the coupling/clean-halt/address antecedents — without the
  -- clean halt an adversarial OOG-at-CALL frame refutes the `CallReturns` existential; the
  -- address pin is what lets the recorded record's `evmV2CallEntry` coincide with the
  -- effect at `fr0.address`. The consumed head IS the un-consumed call suffix's HEAD `rec`
  -- (the positional multi-call tie — no `SingleCall`): the post-state `st0'` is pinned to
  -- `rec`'s `evmV2CallEntry` effect, and R3 discharges the bundle from the record.
  ∧ (∀ (pc : Nat) (cs : CallSpec) (st0 st0' : IRState) (fr0 : Frame)
      (gS : List Word) (sS : List Nat) (rec : CallRecord) (cS' : List CallRecord),
      b.stmts[pc]? = some (.call cs) →
      RecorderCoupled log fr0 gS sS (rec :: cS') →
      CleanHaltsNonException fr0 →
      fr0.exec.executionEnv.address = self →
      st0' = (match cs.resultTmp with
          | some t' => { st0 with world := fun key =>
                          evmCallOracle.postStorage rec.result rec.pending self key }.setLocal
                          t' (callSuccessFlag rec.result rec.pending)
          | none   => { st0 with world := fun key =>
                          evmCallOracle.postStorage rec.result rec.pending self key }) →
      CallRealisesS prog sloadChg L b pc cs st0 st0' fr0)

/-- **The reshaped per-block TERMINATOR ties** (the R0 terminator-side). See the section
docstring: address/kind/self-presence demands are ANTECEDENTS (supplied by `DriveCorrLog`),
all gas guards sit under `CleanHaltsNonException`, the ret epilogue's inner `∀ frv` is
`Runs`+pc-pinned (never free), successor presence lives in `ClosedCFG`. `log` is carried
for signature stability with `StmtTies'` (the deferred RETURN-value channel will consume
it). DERIVED (R5/R10): built from the walk invariant; never supplied. -/
def TermTies' (prog : Program) (sloadChg : Tmp → ℕ) (_log : RunLog)
    (self : AccountAddress) (L : Label) (b : Block) : Prop :=
  -- (stop) non-emptiness only — derivable from the `SelfPresent` antecedent
  -- (`accounts_ne_empty_of_selfPresent`); the old address/kind demands are antecedents now.
  (b.term = .stop →
      ∀ (st' : IRState) (frT : Frame),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        SelfPresent frT →
        frT.exec.executionEnv.address = self →
        (∃ cp, frT.kind = .call cp) →
        ¬ (frT.exec.accounts == ∅) = true)
  -- (ret) the charge envelope (clean-halt-derived) + the pc-pinned RETURN epilogue block.
  ∧ (∀ t, b.term = .ret t →
      ∀ (st' : IRState) (frT : Frame),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        SelfPresent frT →
        frT.exec.executionEnv.address = self →
        (∃ cp, frT.kind = .call cp) →
        (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024
        ∧ (∀ (vw : Word), st'.locals t = some vw →
            -- The RETURN-value charge envelope is only witnessed when the returned value is
            -- bound: the IR `ret t` semantics (`RunFrom.ret`/`RunFromLeft.ret`) itself requires
            -- `st'.locals t = some vw`, so demanding the charge-sum bound for an UNBOUND `t` is an
            -- unwitnessable over-demand (same principle as the branch taken-direction restriction;
            -- the charge fold `materialise_charge_le_of_cleanHalt` needs the operand value).
            (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
                ≤ frT.exec.gasAvailable.toNat
            ∧ ∀ frv : Frame, Runs frT frv →
            frv.exec.executionEnv.code = frT.exec.executionEnv.code →
            frv.exec.executionEnv.address = frT.exec.executionEnv.address →
            (∀ k, selfStorage frv k = selfStorage frT k) →
            frv.exec.stack = vw :: frT.exec.stack →
            frv.exec.pc = frT.exec.pc + UInt32.ofNat
              (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp t)).length →
            ∃ cp wms,
              decode frv.exec.executionEnv.code frv.exec.pc
                  = some (.Push .PUSH32, some ((0 : Word), 32))
              ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
                  = some (.Smsf .MSTORE, .none)
              ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + 1)
                  = some (.Push .PUSH32, some ((32 : Word), 32))
              ∧ decode frv.exec.executionEnv.code
                    (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33)
                  = some (.Push .PUSH32, some ((0 : Word), 32))
              ∧ decode frv.exec.executionEnv.code
                    (frv.exec.pc + UInt32.ofNat 33 + 1 + UInt32.ofNat 33 + UInt32.ofNat 33)
                  = some (.System .RETURN, .none)
              ∧ 3 ≤ frv.exec.gasAvailable.toNat
              ∧ memoryExpansionWords? frv.exec.activeWords (0 : Word) 32 = some wms
              ∧ memExpansionChargeOf (pushFrameW frv (0 : Word) 32).exec wms
                  ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
              ∧ GasConstants.Gverylow ≤ ((pushFrameW frv (0 : Word) 32).exec.gasAvailable
                  - UInt64.ofNat (memExpansionChargeOf (pushFrameW frv (0 : Word) 32).exec wms)).toNat
              ∧ 3 ≤ (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms []).exec.gasAvailable.toNat
              ∧ 3 ≤ (pushFrameW (mstoreFrame (pushFrameW frv (0 : Word) 32) (0 : Word) vw wms [])
                        (32 : Word) 32).exec.gasAvailable.toNat
              ∧ frv.kind = .call cp
              ∧ ¬ (frv.exec.accounts == ∅) = true))
  -- (jump) the 3-step gas guards, now under the clean-halt antecedent (derivable via
  -- the jump pre-`JUMPDEST` landing); destination presence is an antecedent (from `ClosedCFG`).
  ∧ (∀ dst bdst, b.term = .jump dst →
      prog.blocks.toList[dst.idx]? = some bdst → dst.idx < prog.blocks.size →
      ∀ (st' : IRState) (frT : Frame),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        3 ≤ frT.exec.gasAvailable.toNat
        ∧ GasConstants.Gmid ≤ (pushFrameW frT
            (UInt256.ofNat
              ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
            4).exec.gasAvailable.toNat
        ∧ GasConstants.Gjumpdest
            ≤ (jumpFrame (pushFrameW frT
                (UInt256.ofNat
                  ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx) % 2^32))
                  4)
                GasConstants.Gmid
                (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
                frT.exec.stack).exec.gasAvailable.toNat)
  -- (branch) the cond-materialise `MatRuns` existence + 6 gas guards, verbatim from the
  -- current tie but under the clean-halt antecedent (derivable via
  -- the branch pre-`JUMPDEST` landing + `materialise_runs_of_cleanHalt`); the condition value
  -- `cw` was always antecedent-pinned; target presence is an antecedent (from `ClosedCFG`).
  ∧ (∀ cond thenL elseL bthen belse, b.term = .branch cond thenL elseL →
      prog.blocks.toList[thenL.idx]? = some bthen →
      prog.blocks.toList[elseL.idx]? = some belse →
      thenL.idx < prog.blocks.size → elseL.idx < prog.blocks.size →
      ∀ (st' : IRState) (frT : Frame) (cw : Word),
        Lir.Corr prog sloadChg 0 st' frT L b.stmts.length →
        CleanHaltsNonException frT →
        st'.locals cond = some cw →
        ∃ frc, Lir.MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw frT frc
          ∧ 3 ≤ frc.exec.gasAvailable.toNat
          ∧ GasConstants.Ghigh ≤ (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32))
              4).exec.gasAvailable.toNat
          -- (taken direction, `cw ≠ 0`) the JUMPDEST landing at `thenL` — only witnessed when
          -- the run actually takes the then-branch (the branch pre-`JUMPDEST` landing then-arm).
          ∧ (cw ≠ 0 → GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW frc
              (UInt256.ofNat
                ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
              GasConstants.Ghigh
              (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
              ([] : Stack Word)).exec.gasAvailable.toNat)
          -- (fall-through direction, `cw = 0`) the PUSH4/JUMP/JUMPDEST chain to `elseL` — only
          -- witnessed when the run actually falls through (the branch pre-`JUMPDEST` landing else-arm).
          ∧ (cw = 0 →
              3 ≤ (jumpiFallthroughFrame (pushFrameW frc
                  (UInt256.ofNat
                    ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                  ([] : Stack Word)).exec.gasAvailable.toNat
              ∧ GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
                  (UInt256.ofNat
                    ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                  ([] : Stack Word))
                  (UInt256.ofNat
                    ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32))
                  4).exec.gasAvailable.toNat
              ∧ GasConstants.Gjumpdest ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc
                  (UInt256.ofNat
                    ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                  ([] : Stack Word))
                  (UInt256.ofNat
                    ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx) % 2^32)) 4)
                  GasConstants.Gmid
                  (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
                  (jumpiFallthroughFrame (pushFrameW frc
                    (UInt256.ofNat
                      ((offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx) % 2^32)) 4)
                    ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat))

end Lir.V2
