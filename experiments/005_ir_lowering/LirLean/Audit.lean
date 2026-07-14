import LirLean.CfgSim.LowerConforms
import LirLean.CfgSim.LowerDecode
import LirLean.Materialise.MaterialiseCleanHalt
import LirLean.Drive.DriveSim
import LirLean.Drive.CallPreservesSelf
import LirLean.Spec.Seams

/-!
# Audit net (Track A, 2026-07-02; vacuous conformance surface removed 2026-07-03)

Guard file pinning the axiom footprint of the load-bearing exp005 declarations. Each
`#guard_msgs in #print axioms` turns any axiom-footprint drift (new axiom, `sorry`, native
decide) into a hard build error. This file must stay the LAST import of the `LirLean` root.

**Removed 2026-07-03.** The former flagship `Lir.lower_conforms_cyclic_assembled` /
`lower_conforms_cyclic_tiefree`, `Lir.lower_conforms_wf`, and the whole `Lir.Spec` re-export
layer were DELETED as a *vacuous* conformance surface — their supplied `StmtTies`/`TermTies`
antecedents are unsatisfiable for essentially every nonempty program
(`docs/final-audit-2026-07-03.md`, `docs/target-architecture-2026-07-02.md` §1). Their
axiom-footprint guards and the flagship signature-freeze `#check` were removed with them, so
this net now pins the salvage layer only. The plan-of-record conformance surface is
`LirLean/Realisability/RealisabilitySpec.lean` (the non-default `WIP` cone, with ties derived from
the run); its three flagships are closed and checked from an importing axiom-audit module. See
`docs/exec/audit-net.md`.
-/

/-- info: 'BytecodeLayer.Exec.Invariants.callPreservesSelf_modGuards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.callPreservesSelf_modGuards

/-- info: 'Lir.materialise_runsC_of_cleanHalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.materialise_runsC_of_cleanHalt

/-- info: 'Lir.cleanHalts_of_runWithLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.cleanHalts_of_runWithLog

/-- info: 'BytecodeLayer.Exec.Invariants.stepPreservesSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.stepPreservesSelf

/-- info: 'Lir.sim_assign_sload_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.sim_assign_sload_lowered

/-! ## The `Lir.Spec` audit surface — the precompile-self seam

`Spec/Conformance.lean` now owns the public conformance vocabulary, while the
precompile-self seam forwarder remains in `Spec/Seams.lean`. -/

/--
info: 'BytecodeLayer.Exec.Invariants.callPreservesSelf_of_precompiles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lir.Spec.callPreservesSelf_of_precompiles
