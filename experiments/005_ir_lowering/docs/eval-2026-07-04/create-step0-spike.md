# CREATE Step 0 spike — `Runs.create` de-risking (GO/NO-GO)

Date: 2026-07-04. Time-boxed spike in worktree `.worktrees/create-spike`
(branch `exp005-create-spike`). Prototype changes are **left in the worktree**
(WIP commit). All paths `exp003:` = `experiments/003_bytecode_layer/`,
`exp005:` = `experiments/005_ir_lowering/`.

---

## VERDICT: **GO.**

The `Runs.create` node is **soundly addable**. I prototyped `CreateReturns` +
the `Runs.create` constructor and **closed every core `Runs` recursion the plan
names — `Runs.trans`, `Runs.gasAvailable_le`, `Runs.drive_reconcile` — plus the
whole exp003 downstream — green, sorry-free, and axiom-clean**
(`[propext, Classical.choice, Quot.sound]` only). The full exp003 package builds
(`lake build`, 1135 jobs, exit 0). Crucially, the *hard* direction
(`drive → Runs` reconciliation, `Runs.drive_reconcile`) closed **without a
sorry**, including the 63/64-guard handling — this was the load-bearing unknown
(plan R1) and it is now retired for the node itself.

What is **not** done (by design, per the spike brief): de-`NoCreate`-ing
`runs_of_drive_ok` (exp005 `BytecodeLayer/Hoare/DriveRuns.lean:283`) and the exp005-side
`Runs` recursion arms. Those are mechanical given what's proven here (see §4);
none is a soundness risk, and the two hardest ingredients they need are already
proven green in this spike.

---

## 1. What was prototyped (Lean, all green)

### 1a. `CreateReturns` — the CALL twin, carrying the 63/64 `.ok` witness
`exp003:BytecodeLayer/Hoare.lean:118`

```lean
def CreateReturns (createFr resumeFr : Frame) : Prop :=
  ∃ cp pending childRes,
       stepFrame createFr = .needsCreate cp pending
     ∧ drive (seedFuel cp.gas) [] (running (beginCreate cp)) = .ok childRes
     ∧ resumeAfterCreate childRes.toCreateResult pending = .ok resumeFr
```

Two structural differences from `CallReturns` (exp003:Hoare.lean:91):

* **Entry is *simpler*.** `beginCreate` is **total** (returns a `Frame`, never a
  precompile/immediate `.inr` — exp003:Create.lean:64), so there is **no**
  `EntersAsCode` code/precompile disjunct. The child is literally `beginCreate cp`.
  `CreateReturns` has 3 existentials + 3 conjuncts vs `CallReturns`' 4 + 4.
* **Resume is *harder* — this is the R4 63/64 handling.** `resumeAfterCreate` is
  `Except`-typed: it `throw .OutOfGas` on the 63/64 retention guard
  (`if (gas + gasRemaining).toNat < allButOneSixtyFourth gas.toNat then throw`,
  exp003:Create.lean:200). So `CreateReturns` **carries the `.ok resumeFr`
  witness of the guard passing** as its third conjunct. The OOG branch is
  deliberately *not* a `Runs.create` node: it delivers an exception halt up the
  drive stack (`Pending.resume (.create pd) = resumeAfterCreate …` → `.error` →
  `endFrame … (.exception .OutOfGas)`), a control flow `Runs` does not *resume*.
  Carrying the witness (rather than a separate side-condition bundle) kept the
  whole thing inside `Runs` with no new seam — this is the recommended R4 answer.

### 1b. `Runs.create` constructor
`exp003:BytecodeLayer/Hoare.lean:153`

```lean
| create {createFr resumeFr fr' : Frame} (hc : CreateReturns createFr resumeFr)
    (rest : Runs resumeFr fr') : Runs createFr fr'
```

### 1c. New companions proved (all green, axiom-clean)
* `CreateReturns.det` (Hoare.lean:215) — resumed frame unique (mirror `CallReturns.det`).
* `Runs.create_to_halt` (Hoare.lean:301) — new lemma (mirror `call_to_halt`), fed by `linear_to_halt`.
* `CreateReturns.gas_le` (GasMonotone.lean:249) — the 63/64 net-debit, via
  `gasFundsDescent_conj4'` + `drive_gasRemaining_le_of_running` + `beginCreate_gas`
  + `resumeAfterCreate_gas_le_savedGas` (all pre-existing). Closes by `omega`.
* `driveG_needsCreate` (CallSequence.lean:48) — CREATE descent (simpler than
  `driveG_needsCall_code`: no `beginCall` `.inl/.inr` split).
* `drive_descend_create_eq` (CallSequence.lean:63) — CREATE descent equation,
  **conditioned on the `.ok parent` witness** so it peels the `.ok` branch of the
  `Except`-typed resume. This is the CREATE-specific brick the CALL side didn't need.

---

## 2. Compile status of each core recursion touched

| Recursion | File:line | Status |
|---|---|---|
| `Runs.trans` | Hoare.lean:129 (`| create` :148) | **green** |
| `Runs.step_to_halt` | Hoare.lean (`| create` arm) | **green** (contra `.next`≠`.needsCreate`) |
| `Runs.step_cancel` | Hoare.lean (`| create` arm) | **green** (contra) |
| `Runs.call_to_halt` | Hoare.lean (`| create` arm) | **green** (contra `.needsCall`≠`.needsCreate`) |
| `Runs.create_to_halt` | Hoare.lean:301 (NEW) | **green** |
| `Runs.linear_to_halt` | Hoare.lean (`| create` :via create_to_halt) | **green** |
| `Runs.gasAvailable_le` | GasMonotone.lean:291 | **green, axiom-clean** |
| `Runs.drive_reconcile` | CallSequence.lean:120 (`| @create` :159) | **green, sorry-free** ← the hard one |

Full exp003 `lake build` = **1135 jobs, exit 0**. `#print axioms` guards on
`Runs.gasAvailable_le` / `CallReturns.gas_le` (transitively covering
`CreateReturns.gas_le`) report only `[propext, Classical.choice, Quot.sound]`.

---

## 3. The full ripple list (file:line) a new constructor forces

### 3a. exp003 — DONE and green in this spike (the complete exp003 ripple)
Adding a constructor breaks every exhaustive `Runs` elimination. In exp003 those
are **exactly** (verified by grep — `Drive.lean:190 | refl` is a different
inductive, not `Hoare.Runs`):

* `exp003:Hoare.lean` — `trans` (:129/134), `step_to_halt` (:~200), `step_cancel`
  (:~225), `call_to_halt` (:~245), `linear_to_halt` (:~270). ✅ arms added.
* `exp003:Hoare/GasMonotone.lean` — `Runs.gasAvailable_le` (:291). ✅ arm added.
* `exp003:Hoare/CallSequence.lean` — `Runs.drive_reconcile` (:120). ✅ arm added
  (needed 2 new CREATE descent bricks, both green).

No other exp003 file eliminates `Hoare.Runs`.

### 3b. exp005 — NOT touched in spike; mechanical, non-soundness ripple
Every exhaustive `Hoare.Runs` elimination in exp005 (found via `| refl`/`| call`
correlation; the `| refl`-only hits in `BoundaryReach`/`JumpValid`/`NoCreateBytes`
are over *other* inductives, not `Runs`):

1. `exp005:LirLean/CleanHaltExtract.lean:410` `halted_runs_eq` (`cases`) — add
   contradiction `| create` arm. Trivial.
2. `exp005:LirLean/V2/RealisabilitySpec.lean:1225` `runs_halt_eq` (`cases`) —
   contradiction arm. Trivial.
3. `exp005:LirLean/V2/RealisabilitySpec.lean:1424` `runs_kind` (`induction`) —
   `| create` arm using `resumeAfterCreate_kind` (exp005:BytecodeLayer/Hoare/Descent.lean:390)
   + `stepFrame_needsCreate_inv` (Descent.lean:238). **Both helpers already exist.**
4. `exp005:LirLean/V2/RealisabilitySpec.lean:2414` `atReachableBoundaryVJ_of_runs`
   (`induction`) — `| create` arm needs a **new** edge lemma
   `atReachableBoundaryVJ_create` (twin of `atReachableBoundaryVJ_call`, RS:2369).
   Small; the geometry facts exist.
5. `exp005:LirLean/V2/Drive/CallPreservesSelf.lean:237` `selfPresent_runs`
   (`induction`) — `| create` arm needs a **new** edge hypothesis
   `CreatePreservesSelf` (twin of `CallPreservesSelf`), dischargeable via
   `resumeAfterCreate_exec_accounts_present` (Descent.lean:373) +
   `endFrame_create_accPresent` (DriveMono.lean:87). Both exist.

Transitively-inherited (no new arm; they call the above):
`cleanHaltsNonException_forward` (BytecodeLayer/Hoare/CleanHalt.lean:80) rides
`Runs.linear_to_halt`; `CleanHalts`/`CleanHaltsNonException` are existential
wrappers, not recursions; the `DriveSim`/`driveLog` `totalGas` measure recurses on
`drive` (which already has a `needsCreate` arm), **not** on `Runs` — no change.

### 3c. The one large item — `runs_of_drive_ok` de-`NoCreate`
`exp005:experiments/003_bytecode_layer/BytecodeLayer/Hoare/DriveRuns.lean:283` + `ModellableStep` (:142) + the header
exclusion (:27). The `.needsCreate` arm (:364-365) is currently
`absurd … (hmodel …).1`. De-excluding it means **deleting** the
`ModellableStep` create clause and building a `Runs.create` node in that arm,
mirroring the `.needsCall` code arm (:323-363). **The two hardest ingredients are
already proven in this spike**: `driveG_needsCreate` and (a fuel-bounded variant
of) `drive_descend_create_eq`. The genuinely-new sub-case is the
`resumeAfterCreate = .error .OutOfGas` branch (63/64 OOG), which does **not**
build a `Runs.create` — it must be shown to produce the same halting terminal via
the exception delivery. This is the "largest single proof-engineering item" the
plan flagged (plan §2 step 0c); it is tractable, not a blocker.

---

## 4. The 63/64-guard handling (R4) — how it was resolved

`resumeAfterCreate` (exp003:Create.lean:189, `Except`-typed) can throw on the
63/64 retention guard (:200), unlike CALL's total resume. Resolution, **validated
green**:

* `CreateReturns` **carries `resumeAfterCreate … = .ok resumeFr`** as a conjunct
  (§1a). No separate `PrecompileAssumptions`-style bundle entry was needed — the
  witness lives in the node, so the flagship gets no new *global* seam.
* `drive_descend_create_eq` (CallSequence.lean:63) takes that same `.ok` witness
  `hok` and `rw [hok]` to peel the `.ok` branch of the drive's `Except` match —
  this is the single line where CREATE's partiality shows up, and it discharges
  cleanly.
* The OOG (`.error`) branch is **out of scope of `Runs.create` by construction**:
  it terminates the frame with an exception halt through the drive stack. When
  de-`NoCreate`-ing `runs_of_drive_ok` (§3c), that branch is handled by the
  exception-delivery path, not by a `Runs` node — which is exactly correct
  (an OOG'd CREATE resume is not a "returning create that continues the block").

---

## 5. Decisions the exp003 owner must approve

1. **Add the `Runs.create` constructor to `exp003:Hoare.lean`** (the inductive is
   an exp003-owned brick). Proven sound + axiom-clean here.
2. **`CreateReturns` shape — witness-carrying vs. side-condition.** I chose
   *carry the `.ok resumeFr` witness inside the predicate* (§1a/§4). The
   alternative (a global "enough gas retained" flagship side-condition) was
   rejected because it adds an honest seam CALL doesn't have; the witness form
   keeps parity with `CallReturns` and needs no flagship change. Owner should
   confirm this is the preferred shape.
3. **Two new exp003 descent bricks land in `CallSequence.lean`**
   (`driveG_needsCreate`, `drive_descend_create_eq`). Confirm placement (vs. a
   new `DescentEq`-sibling file) — they are drive-level, could live in
   `Semantics/Interpreter/DescentEq.lean` next to `drive_descend_eq`.
4. **`Runs.create_to_halt` is a genuinely new lemma** (not just an arm). Fine, it
   mirrors `call_to_halt` exactly.
5. **Green-light the `runs_of_drive_ok` de-`NoCreate` as the next step** (§3c) —
   it is the only remaining large item and it is exp005-side
   (`BytecodeLayer/Hoare/DriveRuns.lean`), riding this spike's exp003 bricks.

---

## 6. Prototype location

WIP commit on branch `exp005-create-spike` in `.worktrees/create-spike`.
Changed files (178 insertions, 0 deletions):
`exp003:BytecodeLayer/Hoare.lean` (+84),
`exp003:BytecodeLayer/Hoare/CallSequence.lean` (+63),
`exp003:BytecodeLayer/Hoare/GasMonotone.lean` (+31).
All new decls tagged `SPIKE` in their docstrings. Nothing on `main` or other
worktrees was touched.
