# Acyclic capstone `Lir.lower_conforms` vs cyclic flagship `Lir.V2.lower_conforms`

Read-only statement-level comparison + dependency trace. Question: is the acyclic capstone a
strictly-weaker version of the flagship or a genuinely different theorem, and is the whole acyclic
path (capstone + `Acyclic.lean` + capstone-only support) useless / superseded?

> **P8 status note (2026-07-08).** The old conclusion about `Acyclic.lean` supplying the
> flagship witness is superseded. P8 routes the witness through `IRWellFormed`,
> `codeFits`, `stackFits`, and the internal `WellLowered` adapter. The remaining
> `Acyclic`/`MatFueled` definitions are P9 deletion targets, not live P8 obligations.

Answer up front: the **acyclic capstone THEOREM is genuinely dead** (superseded, drop it). The
2026-07-04 conclusion that `Acyclic.lean` still supplied the live well-formedness core is now
historical: P8 moved the witness and public theorem surface to `IRWellFormed` plus the scalar
`codeFits`/`stackFits` budgets, with `WellFormedLowered`/`WellLowered` kept internal.

---

## 1. The two statements, verbatim

### Acyclic capstone — `Lir.lower_conforms` (`LirLean/LowerConforms.lean:1188`)

```lean
theorem lower_conforms {prog : Program} {w₀ : V2.World} {self : AccountAddress}
    {O : V2.Observable} {p : CallParams} {log : RunLog} {bentry : Block}
    {sloadChg : Tmp → ℕ} {obs : Word}
    (hwl : runWithLog p (seedFuel p.gas) = some log)
    (hp : p.codeSource = .Code (lower prog))
    (hmod : p.canModifyState = true)
    (hentry0 : prog.entry.idx = 0)
    (hbentry : blockAt prog prog.entry = some bentry)
    (hbound : offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks prog.entry.idx < 2 ^ 32)
    (hstore : StorageAgree { locals := fun _ => none, world := w₀ } (codeFrame p (lower prog)))
    (hgasj : GasConstants.Gjumpdest ≤ p.gas.toNat)
    (hcs : CleanHaltsNonException (codeFrame p (lower prog)))
    (hstmts : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimStmtStep prog sloadChg obs L b)
    (hterm : ∀ (L : Label) (b : Block), blockAt prog L = some b →
      SimTermStep prog sloadChg obs self L b)
    (hir : V2.IRRun prog w₀ (realisedGas log) (realisedCall log self) O) :
    O.world = (observe self log.observable).world
```

### Cyclic flagship — `Lir.V2.lower_conforms` (`LirLean/V2/RealisabilitySpec.lean:3705`)

```lean
theorem lower_conforms {prog : Program} {params : CallParams} {log : RunLog}
    {acc : Account}
    (hcode : params.codeSource = .Code (lower prog))
    (hmod : params.canModifyState = true)
    (hself : params.accounts.find? params.recipient = some acc)
    (hgas : GasConstants.Gjumpdest ≤ params.gas.toNat)
    (hwl : WellLowered prog)
    (hrun : runWithLog params (seedFuel params.gas) = some log)
    (hclean : log.clean)
    (hseams : PrecompileAssumptions prog params) :
    ∃ O : Observable,
      RunFrom prog (entryState params) (realisedGas log)
        (realisedCall log params.recipient) prog.entry O
      ∧ Conforms params.recipient log O
```

---

## 2. The difference — this is NOT "same theorem, acyclic vs cyclic CFG"

Neither statement mentions CFG acyclicity in its signature. The word "acyclic" is historical: this
capstone was the endpoint of the path in which the IR `RunFrom`/`IRRun` was to be *constructed*
via the acyclic-CFG machinery (`IRRun.lean` `runFrom_exists`/`irRun_exists`, gated on `CFGAcyclic`).
That construction is itself now retired (DriveSim's dynamic `totalGas` measure replaced the static
block-rank). The real, statement-level differences are three, and every one makes the capstone
strictly weaker / structurally different:

1. **The IR run is SUPPLIED, not produced.** The capstone *takes* `O` and
   `hir : V2.IRRun prog w₀ … O` as hypotheses and only *relates* the supplied run's world to the
   recorded world. The flagship *produces* the run: its conclusion is `∃ O, RunFrom … prog.entry O
   ∧ …`. So the capstone discharges only the right half (world edge) of a diagram whose existence
   half it assumes.

2. **The per-block ties are SUPPLIED unconditionally, not DERIVED.** The capstone assumes
   `hstmts : ∀ L b, blockAt prog L = some b → SimStmtStep …` and the matching `hterm` — the
   unconditional all-frames "§7 supplied-observation contract" (LowerConforms.lean:1202-1217). The
   flagship carries no such hypothesis; it derives the per-frame ties internally (R1–R10) under the
   load-bearing `RecorderCoupled` antecedent (the reshaped `StmtTies'`/`TermTies'`,
   RealisabilitySpec.lean:710/817). This is the crux: those unconditional supplied ties are the
   VACUITY the reshape exists to kill — per the standing MEMORY correction and
   `docs/target-architecture-2026-07-02.md`, the supplied ties are UNSATISFIABLE for a real lowered
   program, so the capstone is a conditional with an unfulfillable antecedent. The flagship's whole
   reason to exist is to replace "assume the ties" with "derive the ties under coupling".

3. **The conclusion is strictly weaker.** Capstone concludes a single equation
   `O.world = (observe self log.observable).world` — the WORLD edge only. The flagship concludes
   full `Conforms params.recipient log O`, which since foundation 4628201 compares BOTH
   `observe.world` AND `observe.result` (Conforms, RealisabilitySpec.lean:155), plus the existence
   of a conforming `RunFrom`. The capstone's world-equation is precisely the input that the
   flagship's own closed lemma `conforms_of_worldeq` (RealisabilitySpec.lean:3661, applied at
   :3747) upgrades to full `Conforms`.

Net: the capstone is a strictly-WEAKER, differently-quantified predecessor — it delivers only the
world half of the conformance diagram, and only after being handed the run and the (unsatisfiable)
all-frames ties. It is not a theorem the flagship cannot prove; it is the earlier "assume what the
flagship derives, conclude less" shape. Everything it establishes is subsumed by the flagship's
world-equation → `conforms_of_worldeq` step.

---

## 3. Dependency trace (grep -rn over LirLean/)

### 3a. The acyclic capstone THEOREM — zero real callers

- `grep` for `lower_conforms` used as a term finds exactly one apparent call outside its own def:
  `RealisabilitySpec.lean:3864  exact lower_conforms hcode hmod hself hgas …`. **This is NOT the
  capstone.** RealisabilitySpec is entirely inside `namespace Lir.V2` (open at line 105, `end
  Lir.V2` at line 3874), so unqualified `lower_conforms` there resolves to `Lir.V2.lower_conforms`
  (the flagship, :3705), which is exactly what R12b `exProg_nonvacuity` intends to instantiate.
- Every other `lower_conforms` hit in the tree is a docstring or the flagship family. The acyclic
  `Lir.lower_conforms` (LowerConforms.lean:1188) therefore has **zero code consumers**. DEAD.

### 3b. Capstone-only support that dies with it

- `runWithLog_messageCall` (RecorderLemmas.lean:143): its ONLY code caller is the capstone
  (LowerConforms.lean:1238). Becomes dead the moment the capstone goes — drop together. The live
  path uses `runWithLog_drive` instead.
- `entry_corr` (LowerConforms.lean:1102): its ONLY code caller is the capstone
  (LowerConforms.lean:1226); all other hits (RealisabilitySpec.lean:162, :626) are docstrings.
  Would be orphaned by the drop — but RS:626 states the flagship's R7 entry face is "established at
  entry (R7 entry + `entry_corr` + …)", i.e. the flagship currently re-implements the entry `Corr`
  inline and may factor `entry_corr` back in. Flag needs-confirmation, not a clean kill.

### 3c. Infra the capstone touches but does NOT own (must stay)

- `sim_cfg` (LowerConforms.lean:970): LIVE — the cyclic headline `lower_conforms_cyclic`
  (DriveSim.lean:648) consumes it. Keep.
- `beginCall_code`: LIVE (RealisabilitySpec.lean:2239/2279/2312). Keep.
- `cleanHaltsNonException_forward`: LIVE across ~15 files incl. the flagship. Keep.
- `messageCall_runs` (Match.lean:557): the capstone uses it (LowerConforms.lean:1236), but its other
  caller is Match's `lower_preserves_ret` (a separately-superseded decl). Not a clean capstone kill.

### 3d. `Acyclic.lean` exports — superseded by P8

This section's original live-path analysis is superseded. The WIP witness no longer depends on
`AcyclicWellFormed` or `wellFormedLowered_of_acyclic`; `WellFormedLowered` has no `MatFueled`
fields to discharge. The remaining `ExprRankLt`/`Acyclic`/`matFueled_*` declarations are legacy
generic-`defs` fuel support kept compiling until the P9 deletion sweep removes them with
`materialiseExpr`/`recomputeFuel`.

---

## 4. Verdict

### (a) Acyclic capstone THEOREM `Lir.lower_conforms` (LowerConforms.lean:1188-1250, ~62 LOC) — DROP.

- Genuinely superseded by the flagship (RealisabilitySpec.lean:3705) and the default-build cyclic
  headline `lower_conforms_cyclic` (DriveSim.lean:648). It is strictly weaker (world edge only,
  supplied run, supplied UNSATISFIABLE all-frames ties) and its world→Conforms upgrade already lives
  as the flagship's closed `conforms_of_worldeq` (:3661).
- **Precise cost of dropping:** essentially nil. Kills the capstone (~62 LOC) and its sole exclusive
  consumer `runWithLog_messageCall` (RecorderLemmas.lean:143). `entry_corr` (LowerConforms.lean:1102)
  becomes caller-less too, but confirm the flagship's R7 entry reshape will not factor it back in
  before removing it (RS:626 names it as intended entry machinery). No live/shared infra is lost:
  `sim_cfg`, `beginCall_code`, `cleanHaltsNonException_forward` all remain used by the cyclic path
  and the flagship.

### (b) `Acyclic.lean` well-formedness witness — P8-superseded.

- It is no longer needed by the flagship's non-vacuity witness: P8 rebuilds the internal
  `WellLowered` adapter from `IRWellFormed`, `codeFits`, and `stackFits`.
- The residual rank/fuel declarations are not a live P8 obligation. P9 deletes them after the
  remaining legacy fuel consumers (`Expr.slot`, `materialiseExpr`, `recomputeFuel`, and
  `MatFueled`) are migrated or removed.
