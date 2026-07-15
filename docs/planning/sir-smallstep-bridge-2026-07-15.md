# SIR small-step vs `Lir` big-step: could the conformance bridge be substantially simpler?

*2026-07-15 — design note / open question. Not a plan of record; an investigation brief.*

## Context

The bytecode-layer consolidation has landed on `main`: the reusable reasoning engine
(`BytecodeLayer` — frame calculus, recorder, cyclic simulation, `Asm` assembler, decode geometry)
now lives in the top-level `EVM/` package and is **IR-agnostic**. Experiment 005 keeps only the
`Lir` IR plus thin adapters, and its three flagships — `lower_conforms`, `lower_conforms_exact`,
`lower_conforms_gasfree` — are **closed and axiom-clean** (`[propext, Classical.choice, Quot.sound]`).

Meanwhile philogy is building the **canonical SIR** directly on `main` (`sir/` package; PR #7
`feat/block-io` adds basic-block inputs/outputs). SIR and `Lir` are ~80% the same IR. The question
this note frames: **because SIR models the IR with a small-step semantics — the same altitude as the
bytecode — could an IR↔bytecode conformance proof against SIR be substantially simpler than the
`Lir` proof, which bridges a big-step IR to small-step bytecode?**

## The two IRs, side by side

Structurally near-identical: same expression alphabet (`constant/var/add/lt/sload`), statements
(`assign/sstore/gas/call`), terminators (`jump/branch` + halt/return), a CFG of basic blocks with an
entry label, built on the `Evm` value types. The differences that matter here:

| Axis | `Lir` (exp005) | SIR (`sir/`, feat/block-io) |
|---|---|---|
| **Control semantics** | **big-step only** (`RunFrom : … → Label → Observable`) | **small-step** (`SmallStep : MachineState → Trace → MachineState`; `Steps` = closure) |
| **Program counter** | none — control flow *is* the recursion structure | explicit `ProgramCursor` (block + position) in `MachineState.control` |
| **SSA form** | global temp namespace, `defsOf` single-def, dominance-scoped; no phi/block-args | **block-argument SSA** (`inputs`/`outputs` + `Locals.transfer` at edges) |
| **Effect model** | **consumes** oracle input streams (`GasOracle`/`CallStream`/`CreateStream`) | **emits** output events (`Trace = List Event`, gas/call existential) |
| **CREATE** | present (`create`/CreateSpec, CREATE2) | not yet |
| **Maturity** | mature; conformance closed | early; minimal, no gas cost model |

## How the `Lir` conformance bridge works today (big-step IR ↔ small-step bytecode)

The altitudes are mismatched, and reconciling them is where the machinery lives:

- **IR side is big-step.** `RunFrom prog st T C D L O` (in `LirLean/Spec/Semantics.lean`) runs a
  block's statement list (`RunStmts`, a fold of per-statement `EvalStmt`) and then, on the
  terminator, **recurses into the successor block** (`branch`/`jump` carry a `RunFrom … dst O`
  premise). There is no machine state and no PC; the recursion tree encodes the whole control flow,
  and the final `Observable` (world + result) is produced at `ret`/`stop`. Effects are threaded as
  **input oracle streams** that statements consume in order.
- **Bytecode side is small-step.** The EVM interpreter in `BytecodeLayer` (`stepFrame`, `Runs`,
  drive/descent) executes the lowered bytecode one opcode at a time.
- **The bridge.** To relate a big-step IR run to a small-step bytecode execution, exp005 leans on the
  generic engine now in `EVM/BytecodeLayer`:
  - the **recorder** (`RunLog`, `runWithLog`, `Exec.Recorder`) instruments the bytecode run so the
    externally-observed effects (gas reads, calls, creates, storage) become a log;
  - **cyclic simulation** (`Exec.CyclicSim`, `RecorderCoupled`, the boundary/segment walk in
    `LirLean/Decode/*` re-indexed over the assembler) matches each IR block's emitted segment against
    the bytecode between control boundaries, one coupled block-step at a time;
  - **realisability** (`LirLean/Realisability/*` — `Machinery`, `Producer`, `Surface`, `Witness`)
    closes the gap between "the IR run consumes these streams" and "the bytecode run actually produces
    exactly these streams," discharging the value/gas/storage channels.

In short: the proof spends a lot of its mass **manufacturing a step structure on the IR side** (via
the recorder + cyclic coupling) so it can be put in lockstep with the inherently-small-step bytecode.
That manufacturing is precisely what a big-step IR forces.

## The hypothesis

SIR's IR is **already small-step** (`Steps`, explicit cursor, event trace). So the IR and the
bytecode are at the *same altitude*, and a conformance proof might be a **direct simulation**:

- a **step/block simulation relation** `R : Sir.MachineState → Frame → Prop` (or a coupling at block
  boundaries), proved to be a forward (and/or backward) simulation: every `Sir.SmallStep` is matched
  by a bounded run of bytecode `stepFrame`s preserving `R`, and conversely;
- the **event trace** on the SIR side lines up directly with the recorder log on the bytecode side —
  potentially subsuming much of the realisability "who-produces-the-stream" argument, because SIR
  *emits* the events the bytecode also emits, rather than *consuming* a pre-supplied oracle;
- the **cyclic-simulation / boundary-walk** machinery may shrink to a standard small-step simulation
  induction, since there is no longer a big-step recursion tree to align against small steps.

If that holds, the parts of the current engine that exist *only* to reconcile big-step-with-small-step
(the coupling recorder, the boundary re-indexing, chunks of realisability) could collapse into a
smaller, more standard simulation argument — while the genuinely-generic bytecode facts (assembler,
decode geometry, gas/memory envelopes) stay reused as-is.

## What we do NOT yet know (the risks to check)

1. **Where the real proof mass is.** If the bulk of the current proof is in the *value channel*
   (materialisation: temps→memory slots, storage agreement, gas costs) rather than in the
   *big-step↔small-step reconciliation*, then switching to small-step SIR saves less than hoped.
2. **Block-argument lowering.** SIR's `inputs`/`outputs` + `transfer` must be lowered to stack/memory
   moves; that is *new* lowering + proof obligation `Lir` never had.
3. **Non-determinism direction.** SIR emits existential gas/call values; the simulation must quantify
   them correctly (forward vs backward simulation) to get an equality-strength conformance like
   `lower_conforms_exact`, not just a refinement.
4. **`Steps` shape.** SIR's `Steps` is `single + chain` (TransGen-style); a `refl + tail`
   (ReflTransGen) formulation may compose better with a simulation induction (this was already a
   preferred direction). Worth settling before building on it.
5. **Maturity gaps.** SIR lacks CREATE and a gas cost model; a fair comparison must account for
   bringing SIR to parity, not just the happy path.

## The ask

Evaluate, against the actual code, whether an IR↔bytecode conformance proof targeting SIR's small-step
semantics would be **substantially simpler** than the `Lir` big-step proof — specifically, how much of
the recorder/cyclic-simulation/realisability machinery is *big-step-bridging overhead* that a
small-step SIR would dissolve, versus *value-channel work* that survives either way. Produce a grounded
verdict with a sketch of the SIR-side conformance statement + proof skeleton and the top risks.

### Key files to ground the evaluation

- `Lir` big-step semantics: `experiments/005_ir_lowering/LirLean/Spec/Semantics.lean` (`RunFrom`,
  `EvalStmt`, `RunStmts`), `LirLean/Spec/Conformance.lean`, `LirLean/Realisability/RealisabilitySpec.lean`
  (the flagship statements), `LirLean/CfgSim/LowerConforms.lean` (the whole-CFG capstone).
- The bridging engine (now generic): `EVM/BytecodeLayer/Exec/CyclicSim.lean`,
  `EVM/BytecodeLayer/Exec/Recorder.lean`, `LirLean/Realisability/Machinery.lean` (the IR-side
  coupling), `LirLean/Materialise/*` (the value channel).
- Bytecode small-step: `EVM/BytecodeLayer/Semantics/Interpreter/*`, `EVM/BytecodeLayer/Hoare/*`
  (`Runs`, drive/descent), `EVM/BytecodeLayer/Asm*` (the assembler the geometry is indexed over).
- SIR small-step: `sir/Sir/Semantics/SmallStep.lean`, `sir/Sir/Semantics/State.lean`,
  `sir/Sir/Semantics/Eval.lean`, `sir/Sir/IR/CFG.lean` (read on branch `feat/block-io` for block IO).

## Appendix: the assembler story (what the Phase-C de-fuse did, and didn't)

The lowering **definitionally factors through an IR-agnostic assembler**. The abstraction is
syntactic: `AsmProgram` is an encoding input, not a second execution semantics.

**The pieces.** `EVM/BytecodeLayer/Asm.lean` is a verified **encoder**: `AsmProgram` (blocks of
`AsmInstr = push | pushLabel | op` over a fixed 14-`Op` alphabet), `blockOffset` (label→offset
relocation), `assemble = resolve + encode`. The IR front-end
`lowerAsm : Lir.Program → AsmProgram` does instruction selection.
`lower prog = assemble (lowerAsm prog)`, and `lower_eq_assemble_lowerAsm := rfl`.

**What IS abstracted through it: geometry.** `Asm/Geometry.lean` proves once, over
`AsmProgram`/`assemble`, the decode alignment (`SegAlignedP`), boundary reachability, cursor
arithmetic, and `mem_validJumpDests_assemble_iff` (valid JUMPDESTs = block-entry offsets). The IR side
transports these to `lower prog`. Any IR emitting an `AsmProgram` inherits this for free — the real
reuse win, and exactly what a future SIR `lowerAsm` would plug into.

**What is NOT: semantics.** `AsmProgram` has **no execution semantics** — so "`assemble` preserves
semantics" is not a statable proposition, and there is nothing missing. `assemble` is an encoder; its
full correctness spec is "it emits exactly these bytes." All semantic reasoning (`lower_conforms`)
happens on the bytecode side.

**Current status: sole assembler spine.** `lowerBytes prog` is definitionally
`bytes (lowerAsm prog)`, and `lower` is definitionally `assemble (lowerAsm prog)`. The former
whole-program direct emitter and its exported byte-equality ladder have been removed. Byte-local
proofs retain only fragment views (`matCache`, `emitStmt`, `emitTerm`, and `emitBlockBody`) for
indexing source constructs inside the assembler output; the private `byteView_*` facts justify those
views, and `lowerBytes_eq_blockBytes` expands the assembler output for local list proofs. These are
not an alternative lowering entry point.

### Sole-spine cleanup outcome

The decode, CFG simulation, budget, and realisability layers now state whole-code facts over
`lowerBytes`. `blockOffset_lowerAsm` is the LIR-specific relocation adapter into the generic
`Asm/Geometry` results. The three conformance statements remain unchanged; only their proof-side
byte-list indexing moved to the assembler accessor.

This cleanup and the SIR retarget are complementary: both want `assemble` as a reusable, sole,
IR-agnostic backend — doing the sole-spine cleanup first makes any later IR front-end (SIR included)
a thin `lowerAsm` + instantiation.
