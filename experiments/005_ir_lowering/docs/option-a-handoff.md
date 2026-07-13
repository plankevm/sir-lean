# Option A handoff — faithful CREATE-begin-fault + CALL-seam `hncr` elimination

Branch: `ir-convergence`. Both packages build **green + axiom-clean** at HEAD `59f8198`
(`[propext, Classical.choice, Quot.sound]`, no sorry/native_decide):
- 003 base + Hoare: `experiments/003_bytecode_layer` — 1135 jobs, "Build completed successfully".
- 005 IR conformance: `experiments/005_ir_lowering` — 1158 jobs, "Build completed successfully".

## (a) What LANDED

Two isolated commits on `ir-convergence` (pre-base `62a9c53`):

**`7ecbee7` — PATCH: faithful CREATE-begin-fault checkpoint.**
The base interpreter's `drive` `.needsCreate` / `beginCreate = .error` arm completed a CREATE
that fails to BEGIN with a zeroed result **and an EMPTIED account map** (`accounts := ∅`),
flagged "Historical behavior". That hard-erase of the caller world on a *soft* failure is
UNFAITHFUL to real EVM / the yellow paper (a CREATE that fails to begin pushes 0 and the
CALLER world continues UNCHANGED). Replaced the literal `accounts := ∅` with the caller
pre-CREATE checkpoint **`pending.frame.exec.accounts`** at the reference site plus 3 literal
mirrors that reconstruct drive's output (so they stay matching / definitionally equal):
- REFERENCE: `003.../EVMLean/Evm/Semantics/Interpreter.lean` (drive `.needsCreate/.error` arm; docstring rewritten to document the soft-failure semantics).
- MIRROR (gas-only): `003.../BytecodeLayer/Hoare/GasMonotone.lean` (`drive_gasRemaining_le_totalGas`).
- MIRROR (adequacy, must stay defeq): `005.../LirLean/RunLog.lean` `driveLog` (`driveLog_drive`).
- MIRROR (gas-only): `005.../LirLean/RunLog.lean` `driveLog_gas_inv` — the 4th site the original brief missed; omitting it breaks the 005 build.

Pure runtime VALUE change on a field in NO gas/adequacy measure; no proof body touched.
Fidelity is VERIFIED, not assumed: `resumeAfterCreate` (`Create.lean:168`) writes
`result.accounts` straight into the resumed caller's `exec'.accounts` over base
`evmState = pending.frame.exec`, so the checkpoint is written back unchanged — caller world
genuinely UNCHANGED. Matches `createArm`'s OWN already-faithful nonce-overflow soft-failure
literal (`System.lean` uses `accounts := accounts`). The drive fault arm was the lone anomaly.

**`59f8198` — GUARD: remove the no-CREATE seam (`hncr`) from CallPreservesSelf.**
With the fault arm now presence-preserving, account-presence is monotone across the WHOLE
CREATE step, so the `hncr` side-condition is no longer needed. Touches only `TieDischarge.lean`.
- NEW Evm inversions (create twins of `stepFrame_needsCall_inv`):
  `createArm_needsCreate_inv`, `systemOp_needsCreate_inv`, `stepFrame_needsCreate_inv`
  → `(∀ a, present fr.exec.accounts → present cp.accounts) ∧ pd.frame.kind = fr.kind ∧ pd.frame.exec.accounts = fr.exec.accounts`.
- NEW descent facts: `beginCreate_ok_accounts_present`, `beginCreate_ok_checkpoint`.
- `drive_accounts_find_mono` `.needsCreate` arm now **PROVES both `beginCreate` sub-arms**
  (descent `.ok child` AND soft-failure `.error`) presence-preserving. The old single
  `absurd hstep (hncr …)` line refuted BOTH at once, so both genuinely needed proving — this
  is the real work, not a one-liner.
- Dropped `hncr` plus the `s0`/`t0`/`EngineReaches` reachability-scoping apparatus; deleted
  the now-dead `EngineStep`/`EngineReaches` inductives. Propagated through
  `callPreservesSelf_success` / `callPreservesSelf` / `callPreservesSelf_modGuards`.

## (b) Blast-radius audit — all SAFE

Everything that touched the empty-map was traced. Nothing semantically depended on the world
being wiped:
- **Gas mirrors** (GasMonotone `drive_gasRemaining_le_totalGas`, RunLog `driveLog_gas_inv`):
  read only `gasRemaining`/`totalGas`; `accounts` is in no gas measure. Literal updated to
  keep matching drive. SAFE (and re-verified green/axiom-clean: `realisedGas_monotone`).
- **Adequacy mirror** (`driveLog` / `driveLog_drive`): requires `driveLog` defeq to patched
  `drive`; both changed identically, defeq held, `driveLog_drive` compiles. SAFE.
- **`drive_accounts_find_mono` create arm**: previously AVOIDED the arm via `hncr`; now PROVES
  it. The faithful map made this possible — not a vacuous guard.
- **CALL seam** (`callPreservesSelf*`): routes presence through `drive_accounts_find_mono`;
  `hncr` removed end-to-end. No external consumers (grep-confirmed: these theorems are used
  ONLY inside `TieDischarge.lean`), so the param change rippled nowhere.
- **Unrelated empty-maps NOT touched**: the `endCall`/`beginCall` `if m == ∅ then checkpoint`
  CALL-result guard, genesis/test fixtures, StorageMap fold inits — a DIFFERENT empty-map,
  not produced/consumed by the create-fault arm. SAFE / unrelated.
- The stale `accounts := ∅` / `hncr genuinely needed` docstrings flagged after the PATCH were
  swept by the GUARD (only one residual `hncr` mention remains, describing its elimination).

## (c) New CALL-seam status — 6 of 7

`callPreservesSelf_modGuards` (`TieDischarge.lean`) is the wrapper. Of the 7 hyps
`callPreservesSelf` carries, **6 are now discharged engine-level**, **1 supplied**:
- DISCHARGED (5 already at `62a9c53` via `stepFrame_next_accMono` / `stepFrame_needsCall_inv` /
  `stepFrame_halted_success_accMono`): `hmono`, `hcall_acc`, `hcall_kind`, `hhalt`, `hcall_self`.
- DISCHARGED (now, this work, via `stepFrame_needsCreate_inv`): the former **`hncr`** no-CREATE
  seam — eliminated, the CREATE step is proven in place.
- **SUPPLIED (1): `hprec`** — `beginCall`'s precompile `.inr` arm preserves presence at the
  queried account (precompiles only insert their own output). Genuinely satisfiable and
  non-vacuous; vacuous for the call-free / non-precompile-targeting lowered IR, but opaque for
  a live precompile. So `callPreservesSelf` is **6/7, NOT yet hypothesis-free**.

## (d) INTEGRITY note — patched-leanevm reference, upstream candidate

Conformance is now to a **documented, patched leanevm reference**, NOT to the original base.
This is the honest, intended direction of Option A: the patch FIXES the reference in the
FAITHFUL direction (yellow-paper soft-failure semantics, matching `createArm`'s own faithful
literal) rather than tuning the reference to match the IR — so there is no self-referential
tightening / circularity. The Interpreter docstring records the change inline. This patch is
a clean **upstream candidate** for philogy/leanevm: a single-arm value fix turning an
unfaithful caller-world erase into the correct soft-failure checkpoint. **Until upstreamed,
the conformance claim is explicitly relative to this patched reference — do not represent it
as conformance to unmodified leanevm.**

## (e) Remaining work (honest, ordered)

1. **`hprec` precompile seam** — the last supplied `callPreservesSelf` hyp. To reach a
   hypothesis-free CallPreservesSelf either (i) prove precompiles are presence-preserving
   engine-level (they only insert their own output map — likely a `beginCall_inr_*` inversion
   twin of the create work), or (ii) scope it to the lowered IR (which targets no precompiles,
   making it vacuously dischargeable at the conformance boundary). Decide which; (i) is the
   stronger, upstreamable result.
2. **Downstream hcall-param removal** — with `hprec` gone, propagate the now-clean
   `callPreservesSelf` upward to drop the still-supplied hcall-style params from
   `selfPresent_runs` / L2.0 / wrappers. Deliberately UNTOUCHED so far (out of GUARD scope).
3. **Gas-advancing walk** — the per-cursor gas-channel advance bricks (`5c8395c` GAS STEP 1,
   `1ec1304` RUNSFACTOR) need to be carried through the full driveCorrPlus walk so the gas
   channel advances in lockstep with the observable walk end-to-end.
4. **Add CREATE to the IR surface** — the IR currently emits no CREATE (which is what made the
   no-CREATE seam dischargeable as vacuous on the IR side). Now that the base CREATE step is
   proven presence-preserving, CREATE can be added to the lowered IR surface and tied through.
   This is the natural next conformance frontier and the reason the GUARD work matters.
5. **C6–C9** — the remaining conformance milestones (per the bytecode-first / uniform
   spill-alloc plan). Sequence after the CREATE surface lands.

### Brutal-honesty flags
- `callPreservesSelf` is **not** hypothesis-free — `hprec` is real and supplied. Do not claim
  a clean CALL seam yet.
- Conformance is to a **patched** reference; the patch is unmerged upstream. State this whenever
  the conformance result is reported.
- The CREATE-no-CREATE seam removal only matters once CREATE is actually on the IR surface
  (item 4); until then it strengthens the base layer / the upstream-candidate patch but does
  not yet exercise a CREATE in the lowered program.
- Three untracked handoff docs (`cycle2/cycle3/overnight-handoff.md`) sit in the working tree,
  not committed; this file is the consolidated Option-A record.
