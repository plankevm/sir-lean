# CREATE build — STATUS / handoff

Date: 2026-07-05. Worktree: `.worktrees/create-build`. Branch: `exp005-create`.
Toolchain: `leanprover/lean4:v4.30.0`. Read alongside `docs/create/BUILD-PLAN.md`
(the authoritative what/where), `docs/create/stream-decision.md` (R2 = option A,
parallel `CreateStream`), and `docs/eval-2026-07-04/create-implementation-plan.md`.

## Headline

- **Steps green: 7 of 8** (0R, 1, 2, 3, 4+7, 5, 6). Step 8 (flagship CREATE
  obligation) is the **expected hard stop** — blocked on the same non-existent
  coupled run-producer (`runFrom_of_driveCorrLog`, R11) that gates the CALL flagship.
- **Default `LirLean`: GREEN + sorry-free** (`lake build` → 1172 jobs; verified no
  real `sorry` term anywhere outside `LirLean/V2/Realisability/`, and no default-cone
  module imports the `Realisability` subdir).
- **Flagship `WIP`: GREEN** (`lake build WIP` → 1172 jobs) carrying **12 tracked
  sorries = 11 pre-existing + 1 explicitly-reported NEW tracked CREATE obligation leaf**
  (`Machinery.lean:1454`, the R6 CREATE boundary edge `atReachableBoundaryVJ_create`).

## Build state at HEAD (`7b4dd7d`) — verified this run

| Lib | Command | Result | Sorries |
|-----|---------|--------|---------|
| default `LirLean` | `lake build` | green, 1172 jobs | 0 (sorry-free) |
| `WIP` (flagship) | `lake build WIP` | green, 1172 jobs | 12 (see ledger) |

exp003 (`003_bytecode_layer`) **untouched this run** (`git diff bbd9578..HEAD` has no
exp003 files); it was green + axiom-clean at Step 0 (1135 jobs, `[propext,
Classical.choice, Quot.sound]`). The branch's only exp003 change is the earlier
Step-0 spike commit `90b76ff` (`Runs.create` node).

## Tracked-sorry ledger (WIP cone, `LirLean/V2/Realisability/`)

Base `bbd9578` had **11**; HEAD `7b4dd7d` has **12** (+1, reported):

- `RealisabilitySpec.lean` — 6: `:134` (StmtTies'), `:247` `lower_conforms`, `:281`
  `lower_conforms_exact`, `:318` `lower_conforms_gasfree`, `:329` gasfree-companion,
  `:344` `exProg_satisfies_hypotheses`. (Declaration-start lines in the build warning:
  124/206/253/289/324/336.)
- `Machinery.lean` — 6: `:405` (R3 `fr0`), `:1381`/`:1389`/`:1418`/`:1421` (R6
  pure-engine geometry bricks, pre-existing), **`:1454` (R6 CREATE edge —
  NEW TRACKED CREATE OBLIGATION, the only +1 this run)**.

All 12 are real `:= sorry` terms; all carry `sorryAx` by design (no `#print axioms`
guard in the WIP cone). None are in the default cone.

## Steps landed green

- **Earlier (@`bbd9578` and before):** 0R (`939363c`), 1 (`f9cd5dd`), 2 (`7a1b521`),
  3 (`bbd9578`), plus foundation `90b76ff`/`0126af4`/`555883d`.
- **THIS run:**
  - **Step 4+7 (ATOMIC) @`ac7108c`** — emit `CREATE`/`CREATE2` bytes (`0xf0`/`0xf5`)
    + retire the no-CREATE exclusion. `Decode/NoCreateBytes.lean` deleted (138 lines);
    `IsLoweringOp` extended in `BoundaryReach.lean`; `runs_of_drive_ok`
    (`BytecodeLayer/Hoare/DriveRuns.lean`) builds a `Runs.create` node in the `.needsCreate` arm.
  - **Step 5 @`eb06eea`** — `Frame/Match.lean` gains `sim_create` +
    `create_reflects_lowered` (R3 short-unfold closed).
  - **Step 6 @`3ba90f5`** — recorder / stream realisation: `recordCreate` /
    `createStreamOf` / `realisedCreate` (parallel `CreateStream`, option A),
    `evmV2CreateEntry`, `realisedCreate_cons`.
  - **Step 8 (PARTIAL) @`7b4dd7d`** — wired the real `realisedCreate log
    params.recipient` into all four flagship conclusions + their internal blocker
    existentials, replacing the Step-2 `[]` placeholder (which was a latent falsity for
    any create-containing program). Statement-only change under the pre-existing R11
    producer sorry; no new sorry from this commit. The deep create tie remains open.

## WHERE IT STOPPED — Step 8 (deep flagship CREATE tie)

The FULL flagship CREATE tie cannot close honestly. This is the **expected hard stop,
not a failure**: the deep create machinery is gated on the coupled run-producer
`runFrom_of_driveCorrLog`, which **does not exist anywhere in the tree** —
`RealisabilitySpec.lean:224-237` documents it verbatim as "THE BLOCKER (Route-A, NOT a
citable leaf)". This is the SAME R11 blocker that gates the CALL flagship; CREATE
cannot close its tie before CALL's producer exists.

The three named Step-8 deep pieces are all downstream of it and would be
sorry-scaffolds if landed now:

1. **StmtTies' create arm** — a 6th conjunct at `Surface.lean:640`, sibling of the
   call arm at `:727`; also needs the deferred `RecorderCoupled.createSuffix`/
   `createPrefix` fields (`Surface.lean:526-531`, explicitly deferred "only needed
   once the walk itself steps through a create") and a `CreateRealisesS` predicate.
2. **Create Corr-re-establishment lemma** — analogue of the 28-hyp `sim_call_stmt`
   (`Sim/SimStmt.lean:576`) with CREATE's nonzero init-code memory window carved out
   of `memAgree` (BUILD-PLAN R5, "the deepest exp005 proof").
3. **CREATE boundary heads in the R6 geometry** `atReachableBoundaryVJ_*`
   (`Machinery.lean:1363-1454`; the CREATE edge landed at `:1454` as the reported new
   tracked leaf, sitting on the already-sorry'd pure-engine bricks).

All three are consumed ONLY by the missing walk, so adding them now would discharge
them via a nonexistent producer — a sorry-scaffold the rules forbid.

Separately, **extending `exProg` to exercise CREATE was deferred per plan** (do LAST,
only once machinery is green): while R11 is open, `exProg_satisfies_hypotheses` and
`lower_conforms` are both sorry, so the extension adds decode/geometry blast-radius
risk with zero non-vacuity payoff.

### Path to unblock (design decision for the lead)

Build `runFrom_of_driveCorrLog` — the coupled `RecorderCoupled` walk across the F2
recursion (target-architecture §5.3) — for **CALL first**. It is the terminal R11
obligation of the whole experiment. It is NOT assembly over closed leaves (see
`RealisabilitySpec.lean:230-237`): `lower_conforms_cyclic'` needs an unconditional
all-frames `SimStmtStep` the reshaped `StmtTies'` cannot supply, and R6
`runs_atReachableBoundary` cannot produce `hrb` alone (its B2 side condition
`(flatBytes prog).length ≤ 2^32` has no producer from `WellFormedLowered`). Once CALL's
producer exists, the create arm / Corr lemma / geometry heads become closeable siblings.

## Branch / commit range / mergeable prefix

- Branch `exp005-create`; 11 commits ahead of `main` (merge-base `f9fc14a`).
  Range this run: `bbd9578..7b4dd7d` (4 commits: `ac7108c`, `eb06eea`, `3ba90f5`,
  `7b4dd7d`).
- **Mergeable green prefix: the ENTIRE branch through HEAD `7b4dd7d`.** Default
  `LirLean` is green + sorry-free at HEAD; WIP is green carrying only tracked debt
  (11 pre-existing + 1 reported CREATE leaf). Every step was committed green. No push
  performed (per rules).
