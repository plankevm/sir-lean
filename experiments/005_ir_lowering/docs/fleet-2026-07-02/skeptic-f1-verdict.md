# Skeptic verdict on F1 (tie unsatisfiability) — 2026-07-02

*Adversarial verification of the flagship-signature report's F1 finding. The skeptic was instructed
to REFUTE; it failed to refute. All four sub-claims CONFIRMED by direct definitional reading
(quantifier scope + parenthesization checked against raw source; Corr's nine fields and the
underlying Frame/ExecutionState/ExecutionEnv/MachineState checked for hidden pins).*

## Sub-claim 1 — StmtTies gas conjunct (LowerConforms.lean:1307-1323): CONFIRMED

`ob : Word` bound in the outer `∀`, no antecedent mentions it, conclusion pins
`ob = ofUInt64 (fr0.gasAvailable − Gbase)`. One Corr inhabitant at a gas cursor suffices
(instantiate `ob := 0` and `ob := 1`). Corr IS inhabitable adversarially: `st0 := ⟨fun _ => none,
fun _ => 0⟩` vacuates `defsSound`/`wellScoped`/`memAgree`; a frame with the right pc/code/validJumps,
`stack := []`, `accounts := ∅` satisfies `StorageAgree` via the `.option 0` default (Match.lean:111).
**No Corr field mentions `gasAvailable`.**

Bonus independent contradiction: the plain-assign conjunct (:1275-1283) fires on the SAME
`.assign t .gas` statement and demands `∀ n, defsOf prog t ≠ some (.slot n)`, while `defsOf`
statically registers every gas-assign tmp as `.slot (slotOf t)` (Lowering.lean:247). Contradictory
before even touching `ob`.

Corroboration in-tree: TieDischarge.lean:3637-3638 — "NOT the universal free-`ob` `StmtTies`
predicate, which … is **unreconstructable from a single run**."

## Sub-claim 2 — sload conjunct free `w` (:1284-1306): CONFIRMED

`evalExpr st0 0 (.sload k) = some w` is conclusion-side with `w` free-∀ (parenthesization verified).
Unsatisfiable whether evalExpr returns `some v` (take `w := v` and `w := v+1`) or `none`.

## Sub-claim 3 — assign conjunct free `st0'` (:1275-1283): CONFIRMED

`st0'` appears only in the conclusion; `MemRealises prog st0' fr0` (MaterialiseRuns.lean:601-606)
demands coverage + mload-readback for ANY locals assignment; empty-memory Corr witness or two
conflicting bindings refute. Fires for any program with a gas/sload/call spill + assign.

## Sub-claim 4 — TermTies stop/ret (:1347-1377): CONFIRMED, STRONGER

Corr pins neither `executionEnv.address`, nor `kind`, nor accounts-nonemptiness, nor locals-liveness,
nor gas. **Strengthening: the jump (:1378-1391) and branch (:1392-1399) conjuncts demand
`3 ≤ frT.gasAvailable.toNat` for every Corr `frT`** — a zero-gas Corr witness refutes. So `TermTies`
is unsatisfiable for every block with ANY terminator — the headline's tie hypotheses are
unsatisfiable for essentially every nonempty program, not just the gas/sload/spill/stop/ret domain.

## Consequence: the conditional headline is VACUOUS as stated

`lower_conforms_cyclic_assembled` (TieDischarge.lean:4292) and `lower_conforms_wf`
(LowerConforms.lean:1438): antecedent `False` for every nonempty program. Green ≠ informative.
No producer of `StmtTies`/`TermTies` exists anywhere in the tree (all 7 non-definition occurrences
are hypothesis binders) — the gap is real and **uninstantiable as stated**; the R0 reshape is a
correctness precondition for Phase 3, not polish.

## callOracleOf single-CALL (RunLog.lean:263-266): CONFIRMED

Projects only the head `CallRecord`, discards the tail; own docstring concedes single-CALL scope.
Correct for ≤1 CALL, wrong for ≥2.
