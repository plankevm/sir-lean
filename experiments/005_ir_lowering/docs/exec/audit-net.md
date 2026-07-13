# Track A — AUDIT NET (execution record, 2026-07-02)

Deliverables: `LirLean/Audit.lean` (guard file, wired as the LAST import of the `LirLean`
root), the Batteries `runLinter` baseline freeze (`scripts/nolints.json`), and this record.

> **UPDATE (2026-07-03).** Waves 1–4 of the honesty cleanup executed the structural reorg
> (HEAD `53c2063`) after this record was written. The `Source` column below has been resynced to
> the post-reorg homes: `V2/TieDischarge.lean` is **DISSOLVED** — the headline decls
> (`lower_conforms_cyclic_assembled`, `lower_conforms_cyclic_tiefree`) moved to
> `LirLean/V2/Drive/Headline.lean`, and `callPreservesSelf_modGuards`/`stepPreservesSelf` to
> `LirLean/V2/Drive/CallPreservesSelf.lean`. `V2/RunLog.lean` was deleted (recorder →
> `LirLean/Spec/Recorder.lean`); `V2/{Mono,Oracle,HonestGasTie}.lean` were deleted (§5's merge
> note is now resolved — see the dated note there). `LirLean/V2/RealisabilitySpec.lean` (non-default
> `Nightly` lib) now carries the R0–R12 sorry-skeleton. Full redirect map:
> `../headline-transitive-chain.md`. Plan-of-record: `../target-architecture-2026-07-02.md` +
> `../execution-plan-2026-07-02.md`; the final audit fleet (`../final-audit-2026-07-03.md`, being
> written) gates Phase 3.

> **UPDATE (2026-07-03, second) — the guarded surface changed: vacuous-headline guards REMOVED,
> net repointed to salvage.** The 2026-07-03 banner above (and §1/§2 below) describes the net as it
> stood when it pinned `lower_conforms_cyclic_assembled` & co. That is now stale. In commits
> "delete vacuous conformance surface 1/4..4/4" (`ba42b63..7b763dc`) the vacuous cyclic conformance
> headline and its apparatus were **DELETED**, so the guards that pinned them were necessarily
> removed from `Audit.lean`:
> - the `#print axioms` guards on `lower_conforms_cyclic_assembled` / `_tiefree`, on
>   `Lir.lower_conforms_wf`, and on the four `Spec` re-export decls (`RealisabilityObligations`,
>   `lower_conforms_cyclic_of_obligations`, the two `_assembled`/`_tiefree` aliases) are **GONE**
>   (the guarded decls no longer exist);
> - the flagship **`#check` signature-freeze** (§2 below) is **REMOVED** — it froze the now-deleted
>   assembled headline; it will be re-pointed to the R11 flagship (`Lir.V2.lowering_conforms`) once
>   that is proven.
>
> The net now pins **8 salvage lemmas + `Lir.Spec.callPreservesSelf_of_precompiles`** (the still-live
> Phase-3 salvage: `memRealises_setLocal_nonspilled`, `driveCorrPlus_assign_remat_memRealises`,
> `driveCorrPlus_sload_value`/`_world`, `FramesRun.snoc_seed`, `gasLogAligned_step_gas_seed`,
> `GasReach.trans`, `GasCursorClass`, plus the precompile self-preservation lemma). The **§1 guard
> inventory table and §2 signature-freeze section below are HISTORICAL** — they document the pre-
> deletion net, not the current one.
>
> **KNOWN EXCEPTION (fleet follow-up #2).** `BytecodeLayer/Hoare/MemAlgebra.lean` (~948–976) retains **8**
> `#guard_msgs in #print axioms` commands *outside* `Audit.lean`. These are intentional local guards
> — they still fail-hard on any axiom/`sorry`/native-decide drift in the MemAlgebra cone — and are
> recorded here so that "Audit.lean is the net" is not read as *exclusive*. They were deliberately
> left in place rather than folded into `Audit.lean`.

## 1. Guard inventory

`LirLean/Audit.lean` pins, via `#guard_msgs in #print axioms` (idiom precedent:
`LirLean/MemAlgebra.lean` ~946), the exact axiom-footprint message of 10 declarations. All
10 are axiom-clean today (`[propext, Classical.choice, Quot.sound]`), so the file pins a
fully clean baseline — any new axiom, `sorry`, or native-decide anywhere in a cone becomes
a hard build error.

| Declaration | Source |
|---|---|
| `Lir.V2.lower_conforms_cyclic_assembled` | `LirLean/V2/Drive/Headline.lean` |
| `Lir.V2.lower_conforms_cyclic_tiefree` | `LirLean/V2/Drive/Headline.lean` |
| `Lir.lower_conforms_wf` | `LirLean/LowerConforms.lean` |
| `Lir.V2.callPreservesSelf_modGuards` | `LirLean/V2/Drive/CallPreservesSelf.lean` |
| `Lir.materialise_runs_of_cleanHalt` | `LirLean/MaterialiseCleanHalt.lean` |
| `Lir.V2.cleanHalts_of_runWithLog` | `LirLean/V2/DriveSim.lean` |
| `Lir.jump_landing_of_cleanHalt` | `LirLean/LowerDecode.lean` |
| `Lir.branch_landing_of_cleanHalt` | `LirLean/LowerDecode.lean` |
| `Lir.V2.stepPreservesSelf` | `LirLean/V2/Drive/CallPreservesSelf.lean` |
| `Lir.sim_assign_sload_lowered` | `LirLean/LowerDecode.lean` |

The 252 scattered per-file `#print axioms` commands were deliberately left in place
(Wave 4 removes them); `Audit.lean` is the authoritative net going forward.

## 2. DECISION — flagship signature freeze: primary option taken

The signature freeze is implemented as `#guard_msgs in #check
@Lir.V2.lower_conforms_cyclic_assembled`. The rendered type was verified stable before
committing: 39 lines / 2866 bytes, byte-identical across repeated elaborations and
with/without `pp.mvars`. The brief's fallback (axiom-only guard) was NOT needed and was
not taken.

One mechanical deviation from the planned file layout: the `/-! -/` module docstring
cannot precede `import` in Lean 4 (`invalid 'import' command`), so the header sits after
the import block. Guard content is byte-identical to the verified draft.

## 3. nolints path correction (vs. the brief)

Batteries's `runLinter` hardcodes the nolints path as **cwd-relative
`scripts/nolints.json`** (see `.lake/packages/batteries/scripts/runLinter.lean`), not a
root-level `nolints.json` as the brief said. Track A's ownership claim should read
`scripts/nolints.json`. Note also that `--update` does not create directories —
`scripts/` had to be `mkdir`'d before the run or the write at the end would crash.

## 4. Linter baseline outcome

- Command: `lake exe runLinter --update LirLean` (background), then a confirmation pass
  `lake exe runLinter LirLean`.
- Runtime: the `--update` run completed in ~1 minute (warm cache; the pre-built Batteries
  `runLinter` binary from the cloned `.lake` was used) — nowhere near the 30-min abort
  window. The confirmation pass exited **0**.
- Result line: `Found 47 errors in 1151 declarations (plus 1743 automatically generated
  ones) in LirLean with 16 linters`.
- Per-linter breakdown (frozen in `scripts/nolints.json`, 47 entries):
  - `docBlame`: 40 — missing docstrings, mostly structure field projections and small
    definitions (Batteries's harness enables docBlame by default).
  - `unusedArguments`: 7 — five are derived-`Repr` noise (`Lir.instRepr*.repr` unused
    `prec` argument, an artifact of `deriving Repr`), but **two are substantive**:
    - `Lir.CallRealises` (`LirLean/LowerConforms.lean:253`) — argument 6 `b : Lir.Block`
      unused;
    - `Lir.TermTies` (`LirLean/LowerConforms.lean:1339`) — argument 4 `_o :
      Lir.V2.CallOracle` unused (already underscore-acknowledged in source).
- Triage: **freeze-only**, per plan. No source fixes and no `@[nolint]` attributes — the
  flagged files are owned by other tracks or frozen, and the global name/hypothesis
  freeze applies. Wave 4 re-runs the linter and burns down the nolints file; the two
  substantive `unusedArguments` findings above are the first candidates.
- Full report log: captured at `/tmp/runlinter-lirlean.log` during the run (80 lines);
  the durable artifact is `scripts/nolints.json` itself.

## 5. Merge note (for the lead)

`Audit.lean` imports its guarded modules **directly** — in particular
`LirLean.V2.TieDischarge`. Today the root's only path to TieDischarge is `import
LirLean.V2.HonestGasTie` (`LirLean.lean:78`), which Track B deletes. Audit.lean's direct
import deliberately survives that deletion, keeping the headline cone in the default
`LirLean` target regardless of what happens to the other root imports. The expected merge
conflict at `LirLean.lean` is trivial; the only invariant to defend is that
`import LirLean.Audit` stays LAST.

> **RESOLVED (2026-07-03).** This merge concern is now moot. `LirLean.V2.HonestGasTie` was
> **deleted** in Phase 2 and `V2/TieDischarge.lean` was dissolved; the `LirLean.lean` root is now
> a clean import list. `Audit.lean` reaches the headline cone via its direct imports of the
> `LirLean/V2/Drive/*` modules and remains the LAST import of the root.
