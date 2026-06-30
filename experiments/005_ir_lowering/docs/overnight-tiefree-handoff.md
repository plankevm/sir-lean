# Overnight tie-free pipeline — verification + handoff (2026-06-30)

Worktree: `experiments/005_ir_lowering`, branch `ir-convergence` (HEAD `079343f`).
Toolchain v4.30.0, `autoImplicit=false`.

## Executive summary

The **tie-free headline `lower_conforms_cyclic_tiefree` (C9) is REACHED, GREEN, and
axiom-clean** `[propext, Classical.choice, Quot.sound]` — no `sorry`/`admit`/`axiom`/
`native_decide`. The full tree builds (1160 jobs with the unrelated `Create.lean` import
present in the working copy; **1159 jobs from the committed-only tree**, verified by an
independent restore-and-build). All `#print axioms` guards across `TieDischarge.lean`,
`DriveSim.lean`, `Modellable.lean`, `LowerConforms.lean` report only the three permitted
axioms.

What "tie-free" means here: the **gas-advance positional channel (S3/S4)** and the
**SSTORE self-presence + `accounts ≠ ∅` invariants** are now THREADED THROUGH the
`DriveCorrPlus` recursion rather than supplied per edge — they are DISCHARGED. The
no-CREATE modellability clause's opcode-set content is DISCHARGED structurally. What
REMAINS SUPPLIED are genuinely-runtime residuals (the serialized `SimStmtStep` spine
S1/S5/S6, the `.success` ext-call self seam `CallPreservesSelf`, the concrete lowered
PUSH/JUMP terminator-edge bundles, and the per-frame pc-reachability premise of NotCreate)
— each satisfiable and non-vacuous, NONE of them the gas/self ties. This is the established
honest-interim pattern: the tie channels are proven; the runtime spine stays as documented
satisfiable hypotheses.

## Per-target status

### NotCreate (clause-1 of modellability) — DISCHARGED (opcode-set); residual = pc-reachability

DISCHARGED. Commit `485f9b7`. New module `LirLean/NoCreateBytes.lean`:
- `SegAlignedSafe` (`NoCreateBytes.lean:59` toSegAligned; the inductive itself above it) —
  `SegAligned` strengthened so every instruction *head* byte parses to a non-CREATE op
  (immediates unconstrained — they are data, a PUSH immediate may itself be `0xf0`, so the
  fact is opcode-positional, not "every byte ≠ 0xf0").
- `reaches_safe_of_segAlignedSafe` (`NoCreateBytes.lean:112`) + `reachesBoundary_le`
  (`NoCreateBytes.lean:107`) — transport: any boundary the aligned walk reaches strictly
  inside a safe segment reads a non-CREATE opcode (induction on `SegAlignedSafe`).
- Per-emitter coverage `segAlignedSafe_{emitImm,emitDest,slot,materialiseExpr,materialise,
  emitStmt,emitTerm,emitBlockBody,loweredBlock,flatBytes}` (`NoCreateBytes.lean:172–350`),
  capped by `segAlignedSafe_flatBytes` (`NoCreateBytes.lean:350`).
- `decode_reachable_boundary_notCreate` (`NoCreateBytes.lean:410`) and the consumer
  `notCreate_of_atReachableBoundary` (`Modellable.lean:421`).

STILL SUPPLIED, and why: only the per-frame **pc-reachability** premise — which boundary
`Runs` actually lands on. This is strictly WEAKER than the original raw `NotCreate`
universal (which asserted no-CREATE at *every* frame unconditionally). The no-CREATE
*opcode-set* fact is now a theorem of the lowering's structure.

Next lemma: thread `ReachesBoundary (lower prog) 0 fr.exec.pc.toNat` from the `Runs` chain
at each modellable step, so `notCreate_of_atReachableBoundary`'s reachability hypothesis is
discharged from the run rather than supplied — eliminating the last NotCreate residual.

### GasWalk-A (S3/S4 gas positional value) — DISCHARGED (S3 PRODUCED)

DISCHARGED. Commit `8172578`. The former `driveCorrPlus_run_stmts` black-boxed per-cursor
frames through `sim_stmts_block`, carrying the gas alignment VERBATIM and leaving S3 (the
positional value `stpc'.locals t = ofUInt64 (frpc.gas − Gbase)`) SUPPLIED. The
re-architected gas-advancing walk PEELS each cursor and threads the alignment, growing the
witness list at each GAS cursor, so S3 is now PRODUCED off the real `lower prog` run:
- `FramesRun.snoc_seed` (`TieDischarge.lean:4027`)
- `gasLogAligned_step_gas_seed` (`TieDischarge.lean:4045`)
- `driveCorrPlus_run_stmts_gasadvance_drop` (`TieDischarge.lean:4102`)
- `driveCorrPlus_run_stmts_gasadvance` (`TieDischarge.lean:4184`)
- `driveCorrPlus_gasval_of_witness` (`TieDischarge.lean:4214`) — the S3 read-off, downstream
  consumer.

STILL SUPPLIED, and why: S4's runtime gas LOWER BOUND (the `50000 ≤ g`-style envelope) is
consumed in the GAS arm but originates as a satisfiable runtime hypothesis — it is a clean
side condition, not a tie. The gas VALUE tie itself is produced.

Next lemma: fold the S4 lower-bound envelope into a `RunDefinable`-derived static fact so the
GAS arm consumes a proven bound rather than a supplied one.

### PlusRec-C (DriveCorrPlus recursion + C8/C9 headline) — REACHED

REACHED. Commit `079343f`. The `DriveCorrPlus` recursion tower assembled on the four proven
`driveCorrPlus_step_*` wrappers + the gas-advance walk:
- `DriveStepPlus` (`TieDischarge.lean:4544`) — the `Plus` analogue of `DriveStep`: at a
  `DriveCorrPlus` boundary, either the block halts (IR `RunFrom`) or it takes an edge to a
  strictly-smaller successor whose re-established invariant is `DriveCorrPlus` (not bare
  `DriveCorr`) — so gas/self channels thread the recursion instead of being supplied per edge.
- `driveStepPlus_of_block` (`TieDischarge.lean:4564`) — C8 assembly.
- `runFrom_of_driveCorrPlus` (`TieDischarge.lean:4648`) — `Plus` recursion building the IR
  `RunFrom` from the entry `DriveCorrPlus` over CYCLIC CFGs (the `totalGas` measure replaces
  static block-rank; no `CFGAcyclic`).
- `lower_conforms_cyclic_tiefree` (`TieDischarge.lean:4691`) — **C9, the tie-free headline.**

DISCHARGED through the `Plus` thread (vs `lower_conforms_cyclic`, which supplies a raw
`hstep`): the gas-advance positional channel (S3), the SSTORE self-presence (`SelfPresent`)
and `accounts ≠ ∅` invariants re-established at every reached boundary.

STILL SUPPLIED in C9's signature (all satisfiable, non-vacuous, NONE are the gas/self ties):
- `hstmts : SimStmtStep` — the serialized S1/S5/S6 spine (the post-P3 statement simulation).
- `hterm : SimTermStep` — the world-channel halt brick.
- `hcall : CallPreservesSelf` — the P3 `.success` ext-call self seam (genuinely-open in its
  `.success` shape; its `.next`-monotonicity is already discharged engine-level per `62a9c53`).
- `hjumpPresent`/`hjump`/`hbranch` — the concrete lowered PUSH/JUMP terminator-edge bundles.

Next lemma: discharge the `SimStmtStep`/`SimTermStep` spine for the lowered program from the
per-statement bricks already in `SimStmt.lean`/`SimStmts.lean`/`SimTerm.lean`, collapsing
C9's supplied set toward the single residual call seam `CallPreservesSelf.success`.

## Verification record (this session)

1. `lake build` — GREEN, 1160 jobs (working copy) / 1159 jobs (committed-only, independent
   restore-build of `LirLean.lean`).
2. `#print axioms` guards in `TieDischarge.lean`, `DriveSim.lean`, `Modellable.lean`,
   `LowerConforms.lean` — all report subsets of `[propext, Classical.choice, Quot.sound]`
   (some report the smaller `[propext, Quot.sound]`).
3. `grep -rn "sorry\|admit\|native_decide" LirLean` (excl. `.lake`) — every hit is docstring
   prose ("admit the memory value channel", "no sorry/axiom", "admits … two-read run"); ZERO
   tactic occurrences.
4. Pipeline commits (newest first): `079343f` DRIVECORRPLUS (C8/C9), `8172578` GASADVANCE
   (S3), `485f9b7` NOCREATE (clause-1), `59f8198` GUARD, `7ecbee7` PATCH, `62a9c53` HMONO,
   `1ec1304` RUNSFACTOR, `bec9f76` EDGE, `9ea5fa7` CALLMONO, `5c8395c` GAS step-1,
   `73f2d6b` C3 cleanup, `516f166` WRAP.

Note: the working copy carries one uncommitted change — `LirLean.lean` adds `import
LirLean.Create` plus untracked `LirLean/Create.lean` and several `docs/*.md`. These belong
to a SEPARATE (create-crosscheck) line of work, NOT this pipeline, and the committed-only
build confirms the tie-free cone stands without them. The `main` stash (`stash@{0}`) is
unrelated and untouched.
