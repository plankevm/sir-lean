import LirLean.Assembly.LowerConforms
import LirLean.Assembly.LowerDecode
import LirLean.Materialise.MaterialiseCleanHalt
import LirLean.V2.Drive.DriveSim
import LirLean.V2.Drive.CallPreservesSelf
import LirLean.Spec.Seams

/-!
# Audit net (Track A, 2026-07-02; vacuous conformance surface removed 2026-07-03)

Guard file pinning the axiom footprint of the load-bearing exp005 declarations. Each
`#guard_msgs in #print axioms` turns any axiom-footprint drift (new axiom, `sorry`, native
decide) into a hard build error. This file must stay the LAST import of the `LirLean` root.

**Removed 2026-07-03.** The former flagship `Lir.V2.lower_conforms_cyclic_assembled` /
`lower_conforms_cyclic_tiefree`, `Lir.lower_conforms_wf`, and the whole `Lir.Spec` re-export
layer were DELETED as a *vacuous* conformance surface — their supplied `StmtTies`/`TermTies`
antecedents are unsatisfiable for essentially every nonempty program
(`docs/final-audit-2026-07-03.md`, `docs/target-architecture-2026-07-02.md` §1). Their
axiom-footprint guards and the flagship signature-freeze `#check` were removed with them, so
this net now pins the salvage layer only. The plan-of-record conformance surface is
`LirLean/V2/Realisability/RealisabilitySpec.lean` (the `WIP` R0–R12 sorry-skeleton, ties DERIVED from
the run); its flagship signature should be frozen here once R11 is proven. See
`docs/exec/audit-net.md`.
-/

/-- info: 'Lir.V2.callPreservesSelf_modGuards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.callPreservesSelf_modGuards

/-- info: 'Lir.V2.materialise_runsC_of_cleanHalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.materialise_runsC_of_cleanHalt

/-- info: 'Lir.V2.cleanHalts_of_runWithLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.cleanHalts_of_runWithLog

/-- info: 'Lir.V2.stepPreservesSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.stepPreservesSelf

/-- info: 'Lir.sim_assign_sload_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.sim_assign_sload_lowered

/-! ## The `Lir.Spec` audit surface — the surviving precompile-self seam

The `Spec/Conformance.lean` re-export layer was deleted (vacuous). The one surviving
`Lir.Spec` decl is the precompile-self seam forwarder in `Spec/Seams.lean`. -/

/-- info: 'Lir.Spec.callPreservesSelf_of_precompiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.Spec.callPreservesSelf_of_precompiles
