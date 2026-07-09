# exp005 codebase map — 2026-07-06

Synthesis of seven module deep-reads (Spec/, Frame/+Engine/, Decode/+Assembly/, Materialise/+Sim/,
V2 core+Drive/, V2/Realisability/, exp003 EVMLean+BytecodeLayer). All claims cite file:line;
disagreements between readers were adjudicated by re-reading the code (noted where done).
Documented WIP (the R0–R12 skeleton, `docs/target-architecture-2026-07-02.md`) is reported as
WIP, not as smell.

> **P9 status note (2026-07-08).** The well-formedness shape has moved since this map was
> written: public WIP theorem statements now use `IRWellFormed` + `codeFits` + `stackFits`, while
> `WellFormedLowered` and `WellLowered` are internal adapters. The old acyclicity/fuel discharge
> (`MatFueled`, `wellFormedLowered_of_acyclic`, `AcyclicWellFormed`) is no longer live
> infrastructure. The residual fuel/materialisation stack (`Expr.slot`, `materialiseExpr`,
> `materialise`, `recomputeFuel`, `MatFueled`, `Assembly/Acyclic.lean`, and `NoSlotSource`) has
> been deleted; old references below are preserved as dated provenance.

---

## 1. Semantic map

### 1.1 The altitude diagram

The development is a tower. Folders do NOT correspond 1:1 to layers — the map below shows the
layers first, then where each folder's content actually sits (misplaced content in *italics*).

```
L9  CONFORMANCE STATEMENT + PRODUCER SKELETON        V2/Realisability/ (WIP lib)
      lower_conforms (R11, sorry'd run-producer)       + *statement vocabulary that belongs in Spec/*
L8  COUPLING / DRIVE WALK                            V2/Drive/ (DriveSim, SelfPresent, Headline)
      DriveCorr, totalGas measure, RecorderCoupled     RecorderCoupled/DriveCorrLog live in L9's Surface.lean
L7  RECORDER / STREAM REALISATION                    Spec/Recorder.lean + V2/CallRealises + V2/RecorderLemmas
      runWithLog, realisedGas/Call/Create, observe
L6  WHOLE-CFG SIMULATION + TIE ASSEMBLY              Assembly/ (sim_cfg, WellFormedLowered, CallRealises)
L5b PER-STATEMENT SIMULATION (Corr invariant)        Sim/ (sim_assign/sstore/call, sim_stmts, sim_term_*)
L5a VALUE CHANNEL (materialise ↔ evalExpr)           Materialise/ + Frame/{Call,Create,Match} oracle half
      MatRuns, MemRealises, DefsSound, StashTail       reflexivity headlines call/create_reflects_lowered
L4  CODE GEOMETRY (pc/offset/decode algebra)         Decode/ (flatBytes, anchors, SegAlignedP, JumpValid)
      + *pcOf lives in Frame/Match — inverted import*
L3  LOWERING FUNCTION                                Spec/Lowering.lean (lower = encode ∘ emit (allocate p))
L2  IR SEMANTICS (oracle-stream big-step)            Spec/Semantics.lean (namespace Lir.V2)
      EvalStmt/RunFrom/IRRun + 3 positional streams    metatheory: V2/Law (determinism), V2/IRRun
L1  IR GRAMMAR                                       Spec/IR.lean (Expr/Stmt/Term/Program)
      + *v1 machine in Frame/SmallStep.lean — IR altitude, dead result-slot channel*
─────────────────────────────────────────────────────────────────────────────────────────────
L0b BYTECODE PROOF SURFACE (exp003)                  003/BytecodeLayer (Runs, messageCall_runs,
      + *~5,800 lines of pure-engine theory             drive_fuel_mono, gasAvailable_le)
        squatting in exp005*: Engine/ (all 8 files),
        Frame/StorageErase, V2/Drive/CallPreservesSelf,
        V2/Modellable, ~1,000 ln of Materialise/CleanHaltExtract,
        ~200 ln of Frame/Match
L0a BYTECODE MACHINE (trusted, executable)           003/EVMLean (stepFrame, drive, messageCall,
      conformance-backed: 2859/2859 fast,               decode, beginCall/Create, resumeAfter*)
      22,308−2 full (Conform/Main.lean:178-181)
```

### 1.2 Folder → layer table

| Folder | Nominal charter | Actual content by layer | Verdict |
|---|---|---|---|
| `Spec/` | trusted spec surface | L1 (IR.lean), L2 (Semantics.lean), L3 (Lowering.lean), L7 (Recorder.lean), plus hoisted conformance/well-formedness vocabulary in Conformance.lean and WellFormed.lean; Seams.lean owns the live `PrecompileAssumptions`/`ReachableFrom` seam vocabulary | Can state the P8 theorem shape; exact-run vocabulary still needs hoisting (see §4.1) |
| `Frame/` | (name suggests frame reasoning) | four altitudes: L1 v1 machine (SmallStep), L5a effect oracles + reflexivity headlines (Call/Create/Match), L4 geometry (pcOf, Match.lean:67-108), L0b pure RBMap facts (StorageErase) | No coherent charter; the honest description is "the v1 line plus whatever it needed" |
| `Engine/` | exp003-machine metatheory staging | L0b, uniformly — token-scan verified zero IR types in 3,978 lines / ~151 decls | Sharp charter, deliberately deferred relocation ("post-Phase-3", AccountMap.lean:26,55,68) — but still **growing** (CREATE twins landed 07-04/05) |
| `Decode/` | code geometry | L4, plus a clean generic sublayer (any-ByteArray decode/boundary facts, Asm/exp003-liftable) and one stowaway (LoweringLemmas.lean = L3 proof companionship, zero geometry) | Good layer, wrong name ("CodeGeometry" honest); imports Frame/Match for pcOf — inverted |
| `Materialise/` | expression value channel | L5a core (MatRuns/MemRealises/DefsSound/StashTail/chargeOf) + ~1,000 IR-free lines of L0b (CleanHaltExtract per-opcode dichotomies) | Core is the strongest-shaped module in the tree; the engine half is misfiled |
| `Sim/` | per-statement simulation | L5b throughout (Corr, sim_* arms, SimStmtStep, sim_term_*) | Correctly placed; interface unevenness in the call arm (§5.4) |
| `Assembly/` | (name suggests an assembler) | L6: tie-unit definitions, decode-bundle discharge wrappers (LowerDecode), whole-CFG `sim_cfg`, `WellFormedLowered`; the old residual rank/fuel support was deleted by P9 | Nothing assembles bytes (emission is Spec/Lowering); "Conformance/" or "CfgSim/" honest |
| `V2/` (top) | proof layer over the oracle-stream IR | L2 metatheory (Law, IRRun), L7 (CallRealises, RecorderLemmas), plus **Modellable.lean whose namespace is `BytecodeLayer.Interpreter`** — L0b in disguise | The `Lir.V2` namespace is mostly *defined outside this folder* (Spec/Semantics.lean:34, Spec/Recorder.lean:49); the folder name is a design-generation fossil (§3) |
| `V2/Drive/` | cyclic drive-indexed walk | L8 (DriveSim, Headline-salvage) + L0b (CallPreservesSelf — no IR type in any code line) + SelfPresent.lean which is ~60% recorder-alignment machinery, ~40% presence invariant | Headline.lean contains no headline (deleted 2026-07-03; Headline.lean:17-25 says so) |
| `V2/Realisability/` | R0–R12 skeleton, non-default WIP lib | L9, but internally three altitudes: spec-surface defs (Surface §1-§2, **sorry-free**), coupling invariant (RecorderCoupled/DriveCorrLog), and R1–R8 proof machinery (majority **proved**; debt concentrated in R11/R10a run-producer, R3 Piece B, R6 engine bricks) | Correctly shaped WIP; the sorry-free statement vocabulary is the one part that must move out |
| exp003 `EVMLean/` | trusted executable machine | L0a; vendored philogy/leanevm @9cefe5b, Cancun, conformance-run | Empirical (not formal) fidelity warrant |
| exp003 `BytecodeLayer/` | proved reasoning surface | L0b: Dispatch characterizations, Runs + fuel erasure + gas monotonicity; plus a dormant cross-engine track (SharedObservable/EVMSpec) exp005 never imports, and a stale wrapper "audit surface" (Spec.lean) that exp005 bypasses | Forward-only Runs theory; exp005 built the reverse (runs_of_drive_ok), the per-step walks, and the recorder in-house |

### 1.3 Prose: how a reader should traverse it

The **trusted base** is L0a (executable machine, conformance-backed) plus, because they appear in
the flagship's statement: exp003's `Runs`/`CallReturns`/`CreateReturns`/`EntersAsCode` (adequacy
pinned in both directions — `messageCall_runs` forward, exp005's `runs_of_drive_ok` backward),
exp005's `runWithLog`/`driveLog`/`observe` recorder (result-adequacy proved via `driveLog_drive`,
V2/RecorderLemmas.lean:62; the *recorded channels* — the gates at Recorder.lean:233-263 — are
definitionally trusted), the L1–L3 spec files, and the remaining exact-run statement vocabulary
still stranded in `V2/Realisability/Surface.lean`.

The **proof tower** runs: geometry (L4) turns global decode obligations into local byte facts;
the value channel (L5a) proves `matCache` bytes reconstruct `evalExpr` values on the EVM
stack, with gas envelopes *derived* from a clean-halt witness (CleanHaltExtract) rather than
supplied — the fix for the retired unsatisfiable `GasRealises`/`SloadRealises` universals
(MaterialiseRuns.lean:496-560); per-statement simulation (L5b) threads the `Corr` invariant;
Assembly (L6) assembles per-block ties and proves the cycle-agnostic `sim_cfg`; the recorder (L7)
realises the three oracle streams from one actual run; the drive walk (L8) provides the
totalGas-measured recursion; and L9 states the flagship and holds the RecorderCoupled reshape
that makes the ties *derived from the run* instead of supplied — the repair of the 2026-07-02/03
vacuity finding.

**Two structural facts dominate everything else:**

1. **The trusted surface is still split, but the P8 theorem shape is cleaner.**
   `Spec/Conformance.lean` now holds the sorry-free `Conforms`, `entryState`, `RunLog.clean`, and
   `NoGasReads` vocabulary. The WIP flagship rebuilds the internal `WellLowered` adapter from
   `IRWellFormed` + `codeFits` + `stackFits`; `PrecompileAssumptions` and `ReachableFrom` now
   live in `Spec/Seams.lean`. The exact-consumption mirrors are the main remaining vocabulary
   still stranded in the non-default WIP lib.
2. **~23% of LirLean is exp003-shaped engine theory** (18.1% whole-file strict, ~23% counting
   the IR-free majorities of CleanHaltExtract and Match) — verified against the audit's ~20%
   claim by token scan; the split-out is done (Engine/), the relocation is deferred, and new
   pure-engine work is still landing in exp005 rather than exp003.

---

## 2. Signature index (by layer)

Statements only; hypothesis bundles trimmed to load-bearing ones.

### L1 — IR grammar (`Spec/IR.lean`)

```lean
inductive Expr where                                          -- IR.lean:75
  | imm (w : Word) | tmp (t : Tmp) | add (a b : Tmp) | lt (a b : Tmp)
  | sload (key : Tmp) | gas
  | slot (slot : Nat)   -- lowering-only spill marker; evalExpr ⇒ none (see smell §5.8)

inductive Stmt where                                          -- IR.lean:98
  | assign (t : Tmp) (e : Expr) | sstore (key value : Tmp)
  | call (cs : CallSpec) | create (cs : CreateSpec)

inductive Term where | ret (t) | stop | jump (dst) | branch (cond thenL elseL)  -- IR.lean:114

structure Program where blocks : Array Block; entry : Label   -- IR.lean:134
```

### L2 — IR semantics (`Spec/Semantics.lean`, namespace `Lir.V2`)

```lean
abbrev World := Word → Word                                   -- :44
structure IRState where locals : Tmp → Option Word; world : World

abbrev GasOracle   := List Word          -- :73 (legacy alias Trace := GasOracle, :78)
abbrev CallStream  := List (World × Word)  -- :99  (post-world, success)
abbrev CreateStream := List (World × Word) -- :116 (post-world, address-or-0)

def evalExpr (st : IRState) (obs : Word) : Expr → Option Word -- :140; .gas => some obs

inductive EvalStmt (prog : Program) :                          -- :181
    IRState → Trace → CallStream → CreateStream → Stmt →
    IRState → Trace → CallStream → CreateStream → Prop
-- assignGas pops gas head; .call/.create pop their stream heads; else channels unchanged

inductive RunFrom (prog : Program) :                           -- :272
    IRState → Trace → CallStream → CreateStream → Label → Observable → Prop
-- leftovers DISCARDED at halt; the exact-consumption fix (RunFromAll) lives at L9

def IRRun (prog) (w₀ T C D O) : Prop :=                        -- :320
  RunFrom prog { locals := fun _ => none, world := w₀ } T C D prog.entry O

structure Observable where world : World; result : IRHalt     -- :254

-- metatheory (V2/Law.lean):
theorem IRRun.det (h₁ : IRRun prog w₀ T C D O) (h₂ : IRRun prog w₀ T C D O') : O = O'  -- Law.lean:173
```

### L3 — lowering (`Spec/Lowering.lean`)

```lean
inductive Loc where | remat (e : Expr) | slot (n : Nat)        -- :94
abbrev Alloc := Tmp → Option Loc                               -- :103
def slotOf (t : Tmp) : Nat := t.id * 32                        -- :134
def defEnv (prog : Program) : List (Tmp × Loc)                 -- :137
def defsOf (prog : Program) : Alloc                            -- :152 (oracle temps ↦ Loc.slot (slotOf t))
def matExpr (cache : Tmp → List UInt8) : Expr → List UInt8     -- :186
def matCache (prog : Program) : Tmp → List UInt8               -- :213
def emit (a : Alloc) (prog : Program) : List UInt8             -- :346
def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)  -- :358
```

### L4 — code geometry (`Decode/`)

```lean
def flatBytes (prog : Program) : List UInt8                    -- DecodeLower.lean:46
theorem lower_eq_flatBytes (prog) : lower prog = ⟨(flatBytes prog).toArray⟩  -- :61
theorem flatBytes_block_split …                                -- Layout.lean:115 (prefix-sum root)
def pcOf (prog) (L : Label) (pc : Nat) : Nat                   -- Frame/Match.lean:67 (misplaced, §4.5)
def termOf (prog) (L : Label) : Nat                            -- DecodeAnchors.lean:156

inductive SegAlignedP (P : Operation → Prop) : List UInt8 → Prop  -- SegAligned.lean:58
def IsLoweringOp (op : Operation) : Prop  -- 18-way allow-list, SegAligned.lean:200
theorem segAlignedP_flatBytes (prog) : SegAlignedP IsLoweringOp (flatBytes prog)  -- :412
theorem block_offset_validJump (prog) (L) (hL : L.idx < prog.blocks.size) :
    UInt32.ofNat (offsetTable … L.idx) ∈ validJumpDests (lower prog) 0   -- JumpValid.lean:223
theorem decode_reachable_boundary_loweringOp … :
    ∃ op arg, Evm.decode (lower prog) (UInt32.ofNat n) = some (op, arg) ∧ IsLoweringOp op  -- BoundaryReach.lean:163
```

### L5a — value channel (`Materialise/`, `Frame/{Call,Create,Match}`)

```lean
def MatDec (code) (defs) (sloadChg) : Nat → UInt32 → Expr → Prop  -- MaterialiseRuns.lean:237
structure MatRuns (defs sloadChg fuel e w fr fr') : Prop          -- :336
  -- runs + stack push w + code/pc/storage pins + MaterialiseGasCharge + memory channel

def MemRealises (prog) (st : V2.IRState) (fr : Frame) : Prop      -- :605
  -- every bound spilled tmp's slot covered, active, addressable, and mloads back its IR value

theorem materialise_runs … (MatDec …) → DefsSound prog st → … → StorageAgree st fr →
    e ≠ .gas → (∀ k, e ≠ .sload k) → MemRealises prog st fr →
    V2.evalExpr st obs e = some w → … → ∃ fr', MatRuns (defsOf prog) sloadChg fuel e w fr fr'  -- :771
theorem materialise_runs_of_cleanHalt … CleanHaltsNonException fr → …
    ∃ fr', MatRuns … ∧ (chargeOf …).sum ≤ fr.exec.gasAvailable.toNat   -- MaterialiseCleanHalt.lean:377

def chargeOf (defs sloadChg) : Nat → Expr → List ℕ                -- MaterialiseGas.lean:73
def DefsSound (prog) (st : IRState) : Prop                        -- DefsSound.lean:209
def NonRecomputable (prog) (t : Tmp) : Prop                       -- :126 (gas ∨ sload ∨ call ∨ create def)
theorem defsSound_preserved (hstep : EvalStmt …) (hsc : StepScoped …) (hsound) : DefsSound prog st'  -- :611
theorem stash_tail_runs …  -- StashTail.lean:156 (PUSH32 slot; MSTORE proved once, memory+activeWords only)
theorem gas_envelope_of_cleanHalt …  -- CleanHaltExtract.lean:699 (envelopes DERIVED, not supplied)

structure CallOracle where postStorage …; restoredGas …; successWord …  -- Frame/Call.lean:79
def evmCallOracle : CallOracle       -- :108 (projections of resumeAfterCall ⇒ rfl-clean)
theorem call_reflects_lowered (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (∀ addr key, evmCallOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ … ∧ evmCallOracle.successWord result pd = callSuccessFlag result pd   -- Frame/Match.lean:520
theorem create_reflects_lowered …                                 -- Frame/Match.lean:577
```

### L5b — per-statement simulation (`Sim/`)

```lean
structure Corr (prog sloadChg obs) (st : V2.IRState) (fr : Frame) (L : Label) (pc : Nat) : Prop  -- SimStmt.lean:103
  -- pc_eq (pcOf pin), code_eq (= lower prog), validJumps_eq, stack_nil, can_modify,
  -- storage (StorageAgree), defsSound, wellScoped, memAgree (MemRealises)

theorem sim_assign …8 hyps… : ∃ fr', Runs fr fr' ∧ Corr … st' fr' L (pc+1) ∧ stack = []   -- :200
theorem sim_sstore_stmt …12 hyps incl. hcs : CleanHaltsNonException, hsstore : SstoreRealises… -- :347
theorem sim_call_stmt …25 hyps (verified)… : ∃ endFr, Runs fr endFr ∧ Corr … st' endFr L (pc+1) ∧ …  -- :577
theorem sim_assign_gas …8 hyps incl. 12-conjunct hstash… -- :894 (sload twin :1056)

def SimStmtStep (prog sloadChg obs L b) : Prop   -- SimStmts.lean:66 (Layer-D abstraction)
theorem sim_stmts_block (hsim : SimStmtStep …) (hcorr) (hcs) (hrun : V2.RunStmts …) :
    ∃ fr', Runs fr fr' ∧ Corr … st' fr' L b.stmts.length ∧ stack = []   -- SimStmts.lean:150
theorem sim_term_halt_ret … : ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
    ∧ (observe self (endFrame last halt)).world = st.world ∧ ….result = .returned vw  -- SimTerm.lean:310
```

### L6 — CFG assembly (`Assembly/`)

```lean
structure WellFormedLowered (prog : Program) : Prop   -- LowerConforms.lean:143 (11 static fields)
def CallRealises (prog sloadChg obs L pc cs st0 st0' fr0) : Prop   -- :263 (the §7 CALL tie)
structure SimTermStep (prog sloadChg obs selfAddr L b) : Prop      -- :96 (halt/edge per-terminator unit)
theorem simStmtStep_block (hwf : WellFormedLowered prog) …per-shape ties… (hnocreate) :
    SimStmtStep prog sloadChg obs L b                              -- :377
theorem sim_cfg (hstmts : ∀ L b, … → SimStmtStep …) (hterm : ∀ L b, … → SimTermStep …) …
    (hcorr : Corr … L 0) (hcs : CleanHaltsNonException fr) (hrun : V2.RunFrom prog st T C D L O) :
    ∃ last haltSig, Runs fr last ∧ stepFrame last = .halted haltSig
      ∧ (observe self (endFrame last haltSig)).world = O.world     -- :983 (cycle-agnostic)
theorem entry_corr … : ∃ fr₀, Runs (codeFrame p (lower prog)) fr₀ ∧ Corr … prog.entry 0  -- :1108
-- Deleted by P9; retained here only as historical map context:
def Acyclic (defs) (rank) : Prop := ∀ t e, defs t = some e → ExprRankLt rank e (rank t)  -- Acyclic.lean:82
```

### L7 — recorder / realisation (`Spec/Recorder.lean`, `V2/CallRealises`, `V2/RecorderLemmas`)

```lean
structure RunLog where observable : FrameResult; gas : List Word; sloads : List Nat;
  calls : List CallRecord; creates : List CreateRecord            -- Recorder.lean:109
def driveLog (fuel) (stack) (state) (…accs) : Except ExecutionException (FrameResult × …)  -- :206
def runWithLog (params : CallParams) (fuel : ℕ) : Option RunLog   -- :289
def realisedGas (log) : GasOracle := log.gas                      -- :307
def realisedCall (log) (self) : CallStream                        -- :328 (via evmV2CallEntry)
def realisedCreate (log) (self) : CreateStream                    -- :343
def observe (self : AccountAddress) (fr : FrameResult) : Observable  -- :383 (the bridge edge)

def evmV2CallEntry (result pd self) : World × Word                -- CallRealises.lean:59
theorem callRealises_bridge (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (evmV2CallEntry result pd self).1 = (fun key => storageAt resumeFr self key)
      ∧ (evmV2CallEntry result pd self).2 = callSuccessFlag result pd   -- :85 (create twin :136)

theorem driveLog_drive : ∀ …, (driveLog f stack state …).map (·.1) = drive f stack state  -- RecorderLemmas.lean:62
theorem runWithLog_drive (h : runWithLog params fuel = some log) :
    ∃ frame, beginCall params = .inl frame ∧ drive fuel [] (.inl frame) = .ok log.observable  -- :118
```

### L8 — drive walk / coupling (`V2/Drive/`, coupling defs in `V2/Realisability/Surface.lean`)

```lean
structure DriveCorr (prog sloadChg obs st fr L) : Prop where
  corr : Corr prog sloadChg obs st fr L 0; cleanHalts : CleanHaltsNonException fr  -- DriveSim.lean:87
theorem totalGas_succ_lt (hrun : Runs fr fj) (hgas : Gjumpdest ≤ …) :
    totalGas [] (.inl (jumpdestFrame fj)) < totalGas [] (.inl fr)   -- :195 (retires CFGAcyclic)
theorem runFrom_of_driveCorr (hstep : ∀ …, DriveCorr … → DriveStep …) :
    ∀ st fr L T C D, DriveCorr … → ∃ O, RunFrom prog st T C D L O   -- :591 (F2)
theorem lower_conforms_cyclic …hentry/hclean/hstep/hstmts/hterm… :
    ∃ O, (∃ last haltSig, Runs fr₀ last ∧ … ∧ (observe self …).world = O.world)
      ∧ RunFrom prog st₀ T C D prog.entry O                        -- :629 (green but CONDITIONAL
                                                                   --  on universal ties — machinery, not headline)

def SelfPresent (fr : Frame) : Prop := ∃ acc, fr.exec.accounts.find? fr.exec.executionEnv.address = some acc  -- SelfPresent.lean:353
theorem selfPresent_runs_of_call (hprec : …precompile no-erase…) (h : SelfPresent fr) (hruns : Runs fr fr') :
    SelfPresent fr'                                                -- CallPreservesSelf.lean:337
def GasLogAligned (gasAcc : List Word) (frs : List Frame) : Prop   -- SelfPresent.lean:98

structure RecorderCoupled (log fr gasSuffix sloadSuffix callSuffix) : Prop where  -- Surface.lean:523
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] [] [] = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix, log.creates)
  gasPrefix/sloadPrefix/callPrefix : ∃ pre, log.X = pre ++ Xsuffix
structure DriveCorrLog (prog sloadChg log self st fr L gS sS cS) : Prop  -- Surface.lean:559
  -- corr + cleanHalts + present + selfPresent + addrPin + kindPin + coupled
```

### L9 — conformance statement + skeleton (`V2/Realisability/`, WIP lib)

```lean
theorem lower_conforms {prog params log acc}                       -- RealisabilitySpec.lean:206 (R11, sorry)
    (hcode : params.codeSource = .Code (lower prog)) (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : Gjumpdest ≤ params.gas.toNat)
    (hwf : IRWellFormed prog) (hcodeFits : codeFits prog) (hstk : stackFits prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log) (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) (realisedCreate log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O
-- variants: lower_conforms_exact (:253, RunFromAll) and lower_conforms_gasfree (:289, NoGasReads)
-- all three sorry'd on the SAME missing run-producer runFrom_of_driveCorrLog (:224-238)

structure WellLowered (prog : Program) : Prop                      -- Surface.lean:401
  -- internal adapter rebuilt by wellLowered_of_IRWellFormed:
  -- wf : WellFormedLowered; defs : RunDefinableG; defsCons; defEnvOrdered; entry0;
  -- closed : ClosedCFG; stack : StackRoomOK; gasBound; slotAddr; retEpilogueBound
structure PrecompileAssumptions (prog params) : Prop where          -- Spec/Seams.lean
  noErase : ∀ cp imm, beginCall cp = .inr imm → ∀ a, AccPresent a cp.accounts → AccPresent a imm.accounts
  callsCode : ∀ fr', ReachableFrom params fr' → CallsCode fr'
def RunLog.clean (log : RunLog) : Prop                             -- Surface.lean:51
def Conforms …                                                     -- Surface.lean:63
def entryState (params : CallParams) : IRState                     -- Surface.lean:34
def RunFromAll (prog st T C D L O) : Prop := RunFromLeft prog st T C D L O [] [] []  -- Surface.lean:947

-- closed producers (selection): defsSoundS_preserved_step (Machinery.lean:91, R0b),
-- gas_suffix_head_realised (:1640, R1), termTies'_of_walk (:495, R5, ~600 ln),
-- recorderCoupled_call_extract (:1919, R7e′), conforms_of_worldeq (RealisabilitySpec.lean:161)
-- refutations landed as theorems: not_defsSound_stale (Witness.lean:229),
-- not_runs_atReachableBoundary (Machinery.lean); witness: wellLowered_exProg (Witness.lean:658)
```

### L0 — exp003 (consumed exports)

```lean
def stepFrame (fr : Frame) : Signal                    -- EVMLean Dispatch.lean:130
def drive (fuel) (stack) (state) : Except ExecutionException FrameResult  -- Interpreter.lean:36
def seedFuel (gas : UInt64) : ℕ := 2 * gas.toNat + 4096  -- :71
def messageCall (params : CallParams) : Except ExecutionException CallResult  -- :73

inductive Runs : Frame → Frame → Prop                  -- BytecodeLayer/Hoare.lean:140
  | refl | step (h : StepsTo fr mid) | call (hcall : CallReturns …) | create (hc : CreateReturns …)
def CallReturns (callFr resumeFr : Frame) : Prop       -- Hoare.lean:91 (EntersAsCode ⇒ no precompiles)
def CreateReturns (createFr resumeFr : Frame) : Prop   -- Hoare.lean:118 (exp005 Step-0 SPIKE)
theorem messageCall_runs (hbegin : EntersAsCode p fr₀) (h : Runs fr₀ last)
    (hhalt : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt))  -- CallSequence.lean:195
theorem drive_fuel_mono (hle : f ≤ f') … : drive f' stack state = drive f stack state  -- Drive.lean:185
theorem messageCall_never_outOfFuel (p) : messageCall p ≠ .error .OutOfFuel  -- NeverOutOfFuel.lean:144
theorem Runs.gasAvailable_le (h : Runs fr last) : last.…gasAvailable.toNat ≤ fr.…gasAvailable.toNat  -- GasMonotone.lean:281
-- exp005-built engine theory living in exp005 (L0b squatters):
theorem runs_of_drive_ok : drive f [] (running fr) = .ok res →
    (∀ fr', Runs fr fr' → ModellableStep fr') →
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt ∧ res = endFrame last halt  -- Engine/DriveRuns.lean:357
theorem stepFrame_next_accMono (h : stepFrame fr = .next exec') (a) (hp : AccPresent a …) :
    AccPresent a exec'.accounts                        -- Engine/StepWalk.lean:1119 (~1,000-ln walk cap)
```

---

## 3. The V2 story

### 3.1 Why V2 exists, what V1 was

**V1** was never a folder: it is the original bytecode-coupled IR line of `docs/ir-design.md` —
the small-step machine now at `Frame/SmallStep.lean`, whose IRState originally carried a gas
counter so the Match invariant's M4 could assert `IR.gas = fr.exec.gasAvailable`
(`ir-design-v2.md` §1 calls this "the rot we are removing"; the counter was excised in 99fef86).

**V2** was created 2026-06-23 (commit e690863) implementing `docs/ir-design-v2.md`: the gas/pc-free
observable machine where gas is a *supplied value*, not accounting. Then two things happened:
(i) `ir-design-v3.md` **converged** v1+v2 (keep v2's machine; fold v1's `resumeAfterCall`
projections in as the realisability witness) — implemented *inside* the V2 folder; (ii) the
role-directory reorg (f9fc14a) plus the spec extractions (8417d67, ca66721) moved the machine
(`V2/Machine.lean` → `Spec/Semantics.lean`) and the recorder (`V2/RunLog.lean` →
`Spec/Recorder.lean`) *out* of the folder while keeping `namespace Lir.V2`.

**Verdict: the name should die.** Three concrete misalignments: (a) the `Lir.V2` namespace is
defined mostly outside the V2 directory (Spec/Semantics.lean:34, Spec/Recorder.lean:49);
(b) the directory contains a file with zero V2 content (`Modellable.lean` is entirely
`namespace BytecodeLayer.Interpreter`, Modellable.lean:45); (c) the "2" contrasts with a "1"
surviving only as the Frame/ reference line — whose result-slot channel is *dead* (§5.5) — and
both numbered design docs are stamped SUPERSEDED. The rename (folder by role; `Lir.V2` → `Lir`
or `Lir.Oracle`) is tree-wide and deserves its own commit; nothing load-bearing depends on the
string "V2".

### 3.2 Gas-free vs oracle-free: is gas special-cased?

**The mechanism is channel-generic; the name is historical.** Evidence: all three channels are
bare lists consumed head-first, positionally, threaded identically through
EvalStmt/RunStmts/RunFrom/IRRun; CreateStream was added (7a1b521) as a "byte-for-byte twin of
CallStream"; each channel has the same three-piece kit — realised projection off the one RunLog
(`realisedGas`/`realisedCall`/`realisedCreate`), a cons/faithfulness lemma
(RecorderLemmas.lean:44/:144), and a realisability bridge (`callRealises_bridge`/
`createRealises_bridge`; gas's is `gasRecord_eq_gasReadOf` + `gasReadOf_gasFrame_eq_obs`,
SelfPresent.lean:60-83). `ir-design-v3.md` states the uniform principle: "gas and external calls
are both things the IR observes but does not model … one shape." Ordering across kinds lives in
the sequential walk, so per-kind channels reconstruct any interleaving. Note the deliberate
asymmetry that is NOT a wart: **storage is not an oracle** — `evalExpr` reads `st.world`
directly, and the recorded sload warmth feeds only bytecode-side gas alignment (consistent with
the conformance-oracle-surface finding: storage is a modelled effect, not an observed one).

**Where gas IS still genuinely special-cased** (three residues, all fixable):
1. **Syntactic**: gas is popped by an *expression* (`Expr.gas` inside assign) while call/create
   are *statements* — hence `evalExpr`'s awkward `obs : Word` parameter (pinned to 0 in
   `assignPure`, Semantics.lean:186-190) and `e ≠ .gas` side conditions rippling through
   StmtDefinable and the determinism case splits. A `Stmt.gasread t` would remove the parameter.
2. **Proof-side**: `Corr` carries a *single fixed* `obs : Word` for the whole run, so positional
   gas selection closes only when all reads report one word (`gasRealises_obs_of_witness`,
   SelfPresent.lean:205, names this the standing obstacle); calls/creates were per-record
   positional from day one. The per-cursor gas refactor (R1 territory — `gas_suffix_head_realised`
   is already the per-cursor suffix-head equation) makes gas exactly as positional as its siblings.
3. **Cosmetic**: `GasOracle` vs `CallStream`/`CreateStream` naming, the deprecated `Trace` alias
   kept live in every Spec signature (Semantics.lean:76-78), and 10-place relations threading
   (T, C, D) positionally — a `Streams` record + `GasStream` rename retires all three at once.

So the honest model name is **supplied-observation / oracle-stream semantics**, of which
"gas-free" was the founding instance. The user-facing instinct ("shouldn't this be a general
oracle thing?") is correct and the code is ~80% of the way there.

---

## 4. Misplacement inventory

Merged and deduped from all seven readers; ranked by how much the move clarifies the trusted
surface. Acknowledged-deferred relocations are ranked by residual confusion, not by blame.

1. **Remaining flagship statement vocabulary → `Spec/`** (highest value). `Conforms`,
   `entryState`, `RunLog.clean`, and `NoGasReads` have moved to `Spec/Conformance.lean`.
   The public P8 statements should not expose `WellFormedLowered`; they use
   `IRWellFormed` + `codeFits` + `stackFits` and rebuild `WellLowered` internally.
   `PrecompileAssumptions` and `ReachableFrom` have moved to `Spec/Seams.lean`. Still
   stranded in the WIP lib are `RunFromLeft`/`RunFromAll` + adequacy (:894-982), and the exact
   call/create entry vocabulary (`evmV2CallEntry`/`evmV2CreateEntry`, CallRealises.lean:59/:117).
   Natural homes: `Spec/Semantics.lean` (the RunFromLeft mirror, next to RunFrom — the anti-vacuity
   strengthening currently lives *outside* Spec while the weak RunFrom lives inside),
   `Spec/Seams.lean` (already re-keyed for PrecompileAssumptions — see #7).

2. **The ~5,800-line engine block → exp003** (largest mass; acknowledged, deferred
   "post-Phase-3"). `Engine/` whole (3,978 ln, token-scan-verified IR-free), `Frame/StorageErase.lean`
   (217 ln, its own docstring: "mention no EVM execution concept"), `V2/Drive/CallPreservesSelf.lean`
   (350 ln, no IR type in code), ~1,000 IR-free lines of `Materialise/CleanHaltExtract.lean`
   (per-opcode stepFrame OOG/inversion/dichotomy families, :82-1101; only §3's envelope family is
   lowering-shaped), ~200 lines of `Frame/Match.lean` (:214-465). The audit's ~20% figure is
   verified (18.1% strict whole-file, ~23% counting mixed-file majorities). **The actionable
   sub-finding**: new pure-engine work is still landing here (CREATE twins in Descent/DriveRuns,
   07-04/05) where relocation cost would be zero for brand-new lemmas — land new engine lemmas in
   exp003 from now on, so Engine/ shrinks instead of grows.

3. **`V2/Modellable.lean` → `Engine/`** (or exp003). The entire file is
   `namespace BytecodeLayer.Interpreter` — pure stepFrame/dispatch routing algebra + the
   `lower_modellable` producer; only `AtReachableBoundary` (:398) mentions `Lir.lower`. A file in
   the IR-proof folder whose namespace is the bytecode engine breaks every navigation model. The
   seam *definitions* (`CallsCode` :410, `CreateResolves` :421) stay reachable via Spec/Seams.

4. **`pcOf` + `pcOf_eq_anchor`/`flatBytes_at_pcOf` (Frame/Match.lean:67-108) → `Decode/Layout.lean`.**
   Pure byte-offset geometry; their current home forces the layering inversion
   `Decode/DecodeAnchors.lean:3` and `Decode/JumpValid.lean:5` importing `Frame.Match` (geometry
   importing the coupling layer). Import-acyclic move (Frame/Match already imports Decode.Layout);
   `termOf` already lives on the correct side, so the current split is internally inconsistent.
   Precondition for the planned Asm-layer extraction.

5. **`Decode/LoweringLemmas.lean` → Spec-companion or `Materialise/`.** Zero geometry content —
   spill-routing exhaustiveness (`defsOf_ne_gas`/`_ne_sload`), the `rematOf` projection twins,
   and `defsOf_eq_defEnv_find`; parked in Decode/ by convenience, pollutes the folder charter.

6. **Spec/Recorder.lean cleanups.** `gasReadOf`/`FramesRun` (Recorder.lean:65-73, proof-walk
   machinery for V2/Drive/SelfPresent per its own relocation comment :58-61) → V2/; the admitted
   plumbing import of `BytecodeLayer.Hoare.GasMonotone` (Recorder.lean:2-5, "the only path
   bringing that module into DriveSim's cone") → DriveSim imports it directly. Both inflate the
   trusted import cone for no spec reason.

7. **`Spec/Seams.lean` → re-keyed to the live flagship.** The current file owns
   `Lir.V2.PrecompileAssumptions` and `ReachableFrom`; under the current flagship,
   `SelfPresent`, `CallPreservesSelf`, and `CleanHaltsNonException` are supporting vocabulary,
   while the live `hseams` fields are `PrecompileAssumptions.noErase` and
   `PrecompileAssumptions.callsCode`. The `noErase` field is definitionally bound to
   `Lir.Spec.PrecompilesPreservePresence`, so the old textual-duplicate drift is gone.

8. **`Frame/SmallStep.lean` (v1 machine) → Spec-adjacent v1 home, or shrink.** IR-spec altitude
   in the frame-coupling folder; its exact v2 counterpart lives in Spec/Semantics.lean. Coupled
   to smell §5.5 (the v1 result-slot channel is dead) — the right move may be shrinking
   Frame/{SmallStep,Call,Create} to the consumed oracle/flag surface + reflexivity pins.

9. **Generic byte-geometry sublayer → exp003 (or future Asm/ByteGeometry).**
   `ReachesBoundary.trans`, `reachesBoundary_of_mem_validJumpDests` (BoundaryReach.lean:92),
   `decode_{nonpush,push}_of_list` (DecodeLower.lean:100/116), SegAlignedP §0-§3 — facts about
   *any* ByteArray and EVMLean's scanner, no `lower`/`flatBytes` mention. Same species: the
   PUSH4/PUSH32 immediate round-trips split across Assembly/LowerDecode.lean:293-325 and
   Materialise/MatDecLower.lean:80-123 (one concept, two folders); the R6 boundary walk +
   witnesses inside Machinery.lean:1252-1517 (deserves its own BoundaryWalk file).

10. **Machinery.lean split + import-chain repair (Realisability-internal).** Nine interleaved
    concerns in one file (already needed a "R6 RELOCATED below its bricks" forward-pointer,
    :1097-1100); and the linear import chain Surface→Machinery→Witness→RealisabilitySpec
    misstates the DAG (Witness.lean:4 imports Machinery but uses nothing from it — verified;
    RealisabilitySpec uses Machinery names only transitively).

11. **exp003-side**: `ExternalCall.lean` (per-example machinery at BytecodeLayer top level,
    its own header disclaims audit relevance) → Examples/; `decode_seq_0..10`
    (Hoare/Sequence.lean:25-52, one concrete program) → Examples/;
    `import …Examples.ConcreteSpecs` off the audit surface (Spec.lean:9); `Runs.gas_cancel`
    (Hoare.lean:436, an exp005-lowering-specific specialization landed by the RUNSFACTOR commit)
    → exp005 or generalize.

---

## 5. Smell inventory

Ranked by severity. R0–R12 sorries, `.create => True` placeholders, and the deliberately-deferred
Engine/ relocation are WIP, not smells, and are excluded.

### HIGH

**5.1 The trusted spec surface is only partly hoisted.** `Spec/Conformance.lean` now carries
`Conforms`, `entryState`, `RunLog.clean`, and `NoGasReads`, `Spec/WellFormed.lean` carries
`IRWellFormed` plus the two budgets, and `Spec/Seams.lean` carries
`PrecompileAssumptions`/`ReachableFrom`. The remaining smell is narrower: exact-consumption
mirrors still live in the non-default WIP lib. **Fix**: finish misplacement #1; leave only
sorry'd theorems in WIP.

**5.2 LowerConforms.lean narrates a theorem it no longer contains.** Title (LowerConforms.lean:5
"sim_cfg + lower_conforms (Layer F)") and the 30-line section at :1148-1177 ("The world equation
… is **fully discharged** here") describe `lower_conforms` as this file's payoff — deleted in
b144af8 (vacuous-ties purge). A reviewer concludes a discharged headline exists here when the
actual flagship is the sorry-blocked R11. **Fix**: retitle; replace §1148 with a pointer to
RealisabilitySpec R11. Directly violates the project's own honesty discipline.

**5.3 P8 fixed the size-bound half by changing the public envelope.** The flagship now takes
`codeFits` and `stackFits` directly, so the R6 size-bound producer is no longer hidden behind
`WellLowered`. `RevalidatesPerBlock` is carried by `IRWellFormed`; the remaining question is
whether the R0b producer consumes it all the way through, not whether the public statement has a
missing scalar premise. Keep this as producer debt, not a reason to expose `WellLowered`.

### MEDIUM

**5.4 sim_call_stmt: 25-hypothesis interface where ~18 are absorbable plumbing** (count
re-verified against source; the audit's "28" was an earlier revision — verdict stands in
substance). SimStmt.lean:577-658. Genuine seams (~7): hcall (CallReturns), hresume+hst' (the
realised-oracle pin), hrescode/hresaddr (CallsCode/self), hsc (scoping), hslots. Plumbing:
this arm uniquely takes **Corr exploded** (hfrpc/hdefs/hmem fed piecewise at
LowerConforms.lean:355) while every sibling takes `hcorr` whole; six resume pins
(hrespc/hresstack/hresmem/hresactive/hrescanmod/hresvalidjumps) should be projection lemmas of
`resumeAfterCall result pd`; htail is constructible from stash_tail_runs exactly as the
gas/sload arms' `_lowered` wrappers already do (LowerDecode.lean:710/921 — the call arm lags its
siblings' own standard); and **hargs : Runs fr callFr is fully opaque** — the pushed
callee/gasFwd words are never tied to `st.locals cs.callee/cs.gasFwd` at any layer (CallRealises,
LowerConforms.lean:264-330, supplies it equally opaquely). Part is R-producer WIP; the exploded
Corr and the derivable resume pins are interface design, not missing producers.

**5.5 Dead v1 coupling surface, extended this month.** `Lir.Match` (Frame/Match.lean:126) has
zero consumers (repo-wide grep; the live invariant is Sim/SimStmt.lean:103 `Corr`). Likewise
`IRState.callResult/createResult`, `bindCallResult/bindCreateResult` (SmallStep.lean:57-124),
`applyCall` (Call.lean:158), `applyCreate` (Create.lean:131): zero consumers — the wired
result-bind path is the V2 stream pop (Semantics.lean:207-235). Docstrings overclaim
(SmallStep.lean:106 calls bindCallResult "the read path for CallSpec.resultTmp"). The dead
channel was *extended* in commit bbd9578 (createResult/applyCreate mirroring the unconsumed CALL
twin). What IS live: the oracle value channel (evmCall/CreateOracle, flags, reflexivity
headlines). Per deep-read-before-touching: no doc names a consumer-to-be for the v1 result
slots, unlike the R-skeleton. **Fix**: shrink to the consumed surface, or give v1 an actual
conformance statement; stop porting features into a machine nothing reads.

**5.6 Anonymous multi-conjunct bundles copy-pasted across files.** Three instances of the same
disease: (a) the 10-12-conjunct stash-endpoint bundle appears ~7 times (StashTail.lean:174-187,
:268-281, :340-355; SimStmt.lean:637-656, :918-932, :1078-1093; LowerConforms.lean:313-329),
destructured positionally, so any clause reorder ripples through six files — name it
`StashRuns`, mirroring MatRuns which proves the pattern works; (b) the 10-conjunct jumpdest
landing bundle ×4 (DriveSim.lean:313-324, :395-409, :512-543, :698-731) — name `JumpdestLanding`;
(c) per-terminator tie bundles duplicated verbatim between per-shape builders and
simTermStep_block (LowerConforms.lean:634-670 vs 869-898; 711-722 vs 903-912; 777-801 vs
920-944) — the call arm's named `CallRealises` def is the in-tree principled alternative
(~120 duplicated lines deletable). Related: `termTies'_of_walk` (Machinery.lean:495-1090) is a
closed ~600-line monolith with 5× copy-pasted decode-window peeling and an inline-copied jump
landing — closed code, so the shape is what gets maintained; factor `decode_window_at_term` +
`push_jump_jumpdest_landing`.

**5.7 Seams.lean stale + duplicate with no definitional link.** See misplacement #7. The
register has been re-keyed to the real flagship hypothesis (`PrecompileAssumptions.noErase`
definitionally uses `PrecompilesPreservePresence`). The former `AcyclicWellFormed` duplication is no longer a live P8 design point:
`WellFormedLowered` is fuel-free, rebuilt from `IRWellFormed` + budgets, and the residual
rank/fuel file was deleted by P9 rather than factored into a shared-bounds source.

**5.8 Expr.slot polluted the source IR grammar.** Historical issue: `Expr.slot` was a
compiler-internal placement marker in the trusted grammar, forcing `noSlotSource`-style
side conditions and dead `.slot` lemma arms. **P9 status:** the marker and the
`NoSlotSource` witnesses are deleted; spill policy now lives in `Loc`.

**5.9 RunDefinable silently narrows "cyclic-general" to the pure fragment.** StmtDefinable
(IRRun.lean:61-65) is False for `.call`/`.create` and excludes `.gas`, so `RunDefinable prog`
(:155) is unsatisfiable for any program using those channels — making `lower_conforms_cyclic'`
(DriveSim.lean:672) vacuous outside the pure fragment while its docstring advertises "benign
well-formedness". This is the audited vacuity pattern recurring one hypothesis over. The
Realisability line already has the honest replacement (`RunDefinableG`, Surface.lean:153);
the present smell is the overclaiming docstring on a surface the plan supersedes.

**5.10 Spec-layer import inversion.** Spec/Recorder.lean:1 imports V2/CallRealises (needed only
for two spec-like defs) plus the admitted GasMonotone plumbing (:2-5); Spec/Seams.lean:1-3
imports three proof modules. Spec/ sits partly *downstream* of the proof tree, making
"read Spec/ first" impossible in import order. Fixed by misplacements #1/#6/#7.

**5.11 exp003 surface drift.** (a) Hoare.lean:27-28 promises "Runs never appears in an exported
statement" — false by exp003's own Spec.lean:51-190 and structurally by exp005's flagship
conclusion; the frame-level surface was later *sanctioned* (exp003 is the low-level layer), so
this is a stale load-bearing docstring stating the wrong trust story. (b) Spec.lean, "THE AUDIT
SURFACE" (:14), is a hand-maintained wrapper duplicate missing the newer workhorses
(runs_pop/mstore/mload/jump/jumpi/jumpdest/branch, step_cancel, the CreateReturns family) and
bypassed by its only external consumer — exp005 imports the Hoare/ modules directly. Demote to
a documentation index. (c) `Behaves` (Behaves.lean:45) has zero consumers in either experiment —
state one real spec through it or delete it. (d) exp005 consumer patches accrete into exp003
core files without an extension discipline (SPIKE markers, "This is R4 in the plan",
Hoare.lean:110) — add a consumer-driven-additions register.

### LOW (grouped)

**5.12 Pervasive stale cross-references** — violates the repo's own just-fix-cruft rule; one
sweep commit fixes all: pre-reorg paths (`V2/Machine.lean` cited in Call.lean:7/10,
CallRealises.lean:11, DriveSim.lean:63, SelfPresent.lean:184, Surface.lean:882/893;
`LirLean/Match.lean`/`SmallStep.lean` flat paths in Frame/SmallStep.lean:13, Frame/Call.lean:23,
Spec/Semantics.lean:27); the stale flagship path in Conformance.lean:16 and Audit.lean:23
(missing the `Realisability/` segment); Lowering.lean:25-27 citing a nonexistent
`LirLean/Decode.lean`; DecodeLower.lean:7-28 narrating superseded C3 state; "16 lowering
opcodes" counts after CREATE/CREATE2 made it 18 (SegAligned.lean:14/:29, BoundaryReach.lean:23-30,
:118-124 — the enumerated allow-list is now factually wrong); SegAligned.lean:13/:67 +
JumpValid.lean:41/:80 citing the deleted NoCreateBytes tower; Headline.lean *named* Headline while
containing salvage only; Law.lean named for deleted laws (it is Determinism.lean);
"Build-enforced guard" trailer comments after guard consolidation (Frame/Match.lean:664,
Engine/CleanHalt.lean:103).

**5.13 Minor design residue**: one engine layer split across four namespaces
(`Evm`/`BytecodeLayer.Interpreter`/`Lir.V2`/`Lir`+`LirLean.MemAlgebra`) by extraction history —
consolidate into one staging namespace; `Trace` deprecated alias live in all Spec signatures;
vestigial `WellFormed` single-use constraint (DefsSound.lean:143, only consumer a sanity
example, asymmetric about create results, with a false companion docstring :190-194);
`slotOf` docstring claims a base offset that does not exist (Lowering.lean:132-134 — slot 0
collides with the ret-epilogue scratch window, currently harmless because ret is terminal);
`lower` silently emits garbage bytes on ill-formed input (Lowering.lean:145/:149 — soundness
recovered through `IRWellFormed` + budgets rebuilding the internal adapter; consider
`Option ByteArray`); `sim_call`/`sim_create` pure
re-exports of exp003 constructors (Frame/Match.lean:481/:543); four hand-maintained lockstep
legacy recursions materialiseExpr/chargeOf/MatDec/MatFueled (deleted or rewritten by P9; one
annotated emission function would make lockstep by construction); identity/alias theorems
`gasLogAligned_step_norecord` and `sloadRecord_discharges_obs` (SelfPresent.lean:150/:240);
CallRealisesS 64-line tracked fork of Lir.CallRealises (Surface.lean:330 — parameterize the
kernel over the scoping predicate when the no-edit rule lifts); `sim_term_edge_branch` gas
bounds stated at four-deep concrete frame expressions (SimTerm.lean:666-722 — the
CleanHaltExtract §4/§5 bricks to collapse them already exist unconsumed); exp003's cross-engine
track carrying a permanent "DRAFT pending sign-off" module (EVMSpec.lean:6-11) and an
undischargeable equivGoal on the default build.

---

## 6. Decision inventory

The technical decisions embodied in the code, with provenance and verdict.

**D1. Oracle-stream semantics (positional list channels, consumed head-first).**
Decided in ir-design-v2/v3: gas, call results, create results are things the IR *observes but
does not model*; each is a `List` popped by the corresponding step
(Semantics.lean:73-116, :181-235), realised from one recorded run (Recorder.lean:307-343), with
per-channel bridges (CallRealises.lean:85/:136). Why: kills both the gas-counter coupling (v1's
M4 rot) and any function-oracle single-call restriction; positional streams reconstruct any
interleaving. **Verdict: sound.** Readers confirm the kit is uniform across all three channels;
determinism (IRRun.det) gives the "THE observable" shape. Residue: gas's three special-casings
(§3.2) and the leftover-discarding RunFrom needing RunFromAll for exact consumption — both
already have in-tree answers.

**D2. Gas as observed Word value, never accounting (permissive-semantics/restrictive-theorem).**
Settled per docs/gas-decision.md and the v3 convergence: no counter, no cost model in the IR;
the monotone-toNat law is *derived* from `Runs.gasAvailable_le`; the proved-but-unused
Trace.gasMonotone law was deleted. **Verdict: sound and settled.** The one open item is
proof-side, not model-side: Corr's single-obs gas model vs the per-cursor stream (R1 landed the
key suffix-head equation, Machinery.lean:1640).

**D3. Uniform spill-to-slot for all oracle temps (gas/sload/call/create results).**
`defsOf`/the value-channel cache route every non-recomputable temp to `Loc.slot (slotOf t)`;
def-sites stash `PUSH32 slot; MSTORE` (proved once, StashTail); uses MLOAD back through
MemRealises. Why: the previous ∀-over-frames universals (GasRealises/SloadRealises) were proven
unsatisfiable on real runs (MaterialiseRuns.lean:496-560) — the value question became positional.
**Verdict: sound — this is the architecture's best idea**, and it caught its own over-constraint
twice (the retired universals; StashTail's full-toMachineState tie, StashTail.lean:58-70).

**D4. Encoding the spill policy back into Expr (`Loc.toDef : Loc.slot n ↦ Expr.slot n`).**
**Superseded by P9.** The old plumbing reuse collapsed the Loc/Alloc abstraction back into
`Expr.slot`; P9 deleted that path and made `Loc` the placement authority.

**D5. Recorder as a Type-valued parallel copy of drive, placed in Spec/.**
driveLog hand-mirrors exp003's drive with accumulator gates (Recorder.lean:206, gates at
:233-263); Type-valued because Prop can't eliminate into Type; result-adequacy proved
(driveLog_drive). Placement in Spec/ is correct under this architecture: the flagship's hrun
hypothesis and conclusion streams are *defined* here — the theorem is a statement about the
recorder. **Verdict: sound-but-fenced.** The fence: the recorded channels (which events, at
which stack depth) are definitionally trusted with no independent check — they are load-bearing
spec content and should be documented as such; and the file needs the §4.6 cleanups (misplaced
helpers, plumbing import, pre-relocation docstring).

**D6. The V2 split and its name.** See §3. **Verdict: the mechanism converged (v3) and won; the
name is a fossil that should die in a dedicated rename commit** (folder → role names, `Lir.V2` →
`Lir`/`Lir.Oracle`, `GasOracle` → `GasStream`, delete `Trace`). The v1 line should shrink to its
consumed oracle surface (smell 5.5) rather than keep growing dead mirrors.

**D7. Cyclic CFGs via the totalGas measure (CFGAcyclic retired).**
Every block entry runs its JUMPDEST (cost 1), so `totalGas_succ_lt` (DriveSim.lean:195) gives
strict descent and `runFrom_of_driveCorr` (:591) recurses without any static acyclicity;
the old def-graph rank/fuel apparatus is no longer part of the live P8 well-formedness path
and was deleted by P9. `DefEnvOrdered` is the source-side def-env condition. **Verdict:
sound.** The dynamic measure is strictly more general and should not be conflated with
either the old CFG rank or the old def-graph fuel rank.

**D8. Derived ties via RecorderCoupled (the post-audit reshape).**
The refuted supplied StmtTies/TermTies (free-∀ disease, confirmed unsatisfiable, headline deleted
2026-07-03) are replaced by ties whose value variables are pinned by antecedents
Corr + RecorderCoupled + clean-halt (Surface.lean:523/:640/:747), with restart-determinism of
driveLog doing the pinning; ties are *built from the run* (R10), never supplied to the flagship.
**Verdict: sound — this is the core fix**, and it is further along than the handoff docs
suggest: R0b/R1/R2/R4/R5/R7(all)/R8/R9/R10b + the witness stack are *closed*; debt is
concentrated in exactly three places (R11/R10a run-producer, R3 Piece B arg-push builder, R6
engine bricks). P8 moved the size/stack facts to explicit public budgets; see the updated 5.3
note for the remaining producer debt.

**D9. Dual/triple flagships: lower_conforms + _exact (RunFromAll) + _gasfree (NoGasReads).**
Decided in the 2026-07-02 design fleet (gasfree co-flagship first; exact consumption closes the
drop-the-suffix vacuity channel). **Verdict: sound** — but the anti-vacuity strengthening
(RunFromAll) belongs next to RunFrom in Spec/ (misplacement #1), and the non-vacuity witness
discipline (exProg_nonvacuity replacing the deleted HonestGasTie) is the right guard.

**D10. exp005 builds engine theory in-house, staged in Engine/ for post-Phase-3 promotion.**
Decided implicitly by exp003's forward-only Runs toolkit (no drive→Runs inversion, no per-step
walks, no recorder) plus the flat/nested toolchain lock making exp003 edits costly mid-sprint.
**Verdict: smell-but-fenced, with one behavior change needed**: the staging was a reasonable
tactical call and the split-out is clean (verified IR-free), but the debt is *growing* — new
CREATE-twin engine lemmas landed in exp005 on 07-04/05 when exp003 already gained
Runs.create/CreateReturns in the same sprint. Land new engine-general lemmas in exp003 from now
on; keep Engine/ shrink-only; unify the four staging namespaces into one.

**D11. WellLowered as the internal static adapter (decidable-in-principle, R9 checker target).**
**Superseded by P8 shape.** `WellLowered` remains useful as the internal adapter consumed by
existing V2 machinery, but public theorem statements should take `IRWellFormed` plus
`codeFits`/`stackFits` and rebuild `WellLowered` internally.

**D12. `lower` total, garbage-on-ill-formed-input.** The deleted `materialiseExpr` path emitted
`[]` on fuel exhaustion and `PUSH32 0` on undefined tmps; the canonical fold path now uses total
`matCache` emission under `DefEnvOrdered`. Soundness is recovered through the P8 `IRWellFormed`
+ budget bridge to the internal adapter. **Verdict: defensible convenience; revisit toward
`Option ByteArray`** as future cleanup, not as a blocker for D4/P9.

**D13. exp003 as trusted base with empirical warrant.** The machine's fidelity rests on the
conformance suite (fast 2859/2859; full 22,308 − 2 listed expected failures), not on formal spec
conformance; `Runs`/`CallReturns`/`CreateReturns` enter exp005's trusted statement vocabulary
but are pinned to drive/messageCall by proved bridges in both directions. **Verdict: sound and
honestly architected**; the caveats to keep visible are the stale exp003 surface docs
(smell 5.11) and that the conform runner enters via the block pipeline while exp005's statements
enter at messageCall directly.

---

## Appendix: adjudications performed by the synthesis agent

- `sim_call_stmt` hypothesis count: **25** (re-counted from SimStmt.lean:577-658), confirming the
  materialise-sim reader over the audit's earlier "28"; the shape verdict stands.
- Flagship + sorry census: confirmed `lower_conforms`/_exact/_gasfree at
  RealisabilitySpec.lean:206/253/289 with 6 sorries in that file (:134, :247, :281, :318, :329,
  :344), matching the realisability reader.
- Spec/Conformance.lean has been partially hoisted since the original audit; it now contains
  `Conforms`/`entryState`/`RunLog.clean`/`NoGasReads`.
- Reader disagreement on "sorry-skeleton" framing (memory/handoff vs realisability reader): the
  reader is right — the Realisability folder is majority *proved*; the handoff language
  undersells it. Debt is concentrated in R11/R10a, R3-B, and R6's engine bricks.
