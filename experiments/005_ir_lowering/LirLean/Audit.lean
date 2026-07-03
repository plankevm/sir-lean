import LirLean.LowerConforms
import LirLean.LowerDecode
import LirLean.MaterialiseCleanHalt
import LirLean.V2.DriveSim
import LirLean.V2.Drive.CallPreservesSelf
import LirLean.V2.Drive.Headline
import LirLean.Spec.Conformance

/-!
# Audit net (Track A, 2026-07-02)

Guard file pinning the axiom footprint of the 10 load-bearing exp005 declarations plus a
signature freeze of the flagship `Lir.V2.lower_conforms_cyclic_assembled`. Each
`#guard_msgs in #print axioms` turns any axiom-footprint drift (new axiom, sorry, native
decide) into a hard build error; the `#guard_msgs in #check` turns any signature change of
the flagship into one. This file must stay the LAST import of the `LirLean` root.

The scattered per-file `#print axioms` commands remain for now (Wave 4 removes them); this
file is the authoritative net. See `docs/exec/audit-net.md`.
-/

/-- info: 'Lir.V2.lower_conforms_cyclic_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.lower_conforms_cyclic_assembled

/-- info: 'Lir.V2.lower_conforms_cyclic_tiefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.lower_conforms_cyclic_tiefree

/-- info: 'Lir.lower_conforms_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.lower_conforms_wf

/-- info: 'Lir.V2.callPreservesSelf_modGuards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.callPreservesSelf_modGuards

/-- info: 'Lir.materialise_runs_of_cleanHalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.materialise_runs_of_cleanHalt

/-- info: 'Lir.V2.cleanHalts_of_runWithLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.cleanHalts_of_runWithLog

/-- info: 'Lir.jump_landing_of_cleanHalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.jump_landing_of_cleanHalt

/-- info: 'Lir.branch_landing_of_cleanHalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.branch_landing_of_cleanHalt

/-- info: 'Lir.V2.stepPreservesSelf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.V2.stepPreservesSelf

/-- info: 'Lir.sim_assign_sload_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.sim_assign_sload_lowered

/--
info: @Lir.V2.lower_conforms_cyclic_assembled : ∀ {prog : Lir.Program} {sloadChg : Lir.Tmp → ℕ} {obs : Lir.Word}
  {o : Lir.V2.CallOracle} {self : Evm.AccountAddress} {st₀ : Lir.V2.IRState} {T : Lir.V2.Trace}
  {params : Evm.CallParams} {code : ByteArray} {acc : Evm.Account},
  Lir.V2.DriveCorr prog sloadChg obs st₀ (BytecodeLayer.System.codeFrame params code) prog.entry →
    Batteries.RBMap.find? params.accounts params.recipient = some acc →
      Lir.V2.RunDefinable prog →
        Lir.V2.CallPreservesSelf →
          (∀ (st : Lir.V2.IRState) (fr : Evm.Frame) (L : Lir.Label) (gasAcc : List Lir.Word) (gasFrs : List Evm.Frame)
              (sloadAcc : List ℕ) (sloadFrs : List Evm.Frame),
              Lir.V2.DriveCorrPlus prog sloadChg obs st fr L gasAcc gasFrs sloadAcc sloadFrs →
                ∃ b, Lir.V2.blockAt prog L = some b) →
            Lir.WellFormedLowered prog →
              (∀ (L : Lir.Label) (b : Lir.Block),
                  Lir.V2.blockAt prog L = some b → Lir.StmtTies prog sloadChg obs o L b) →
                (∀ (L : Lir.Label) (b : Lir.Block),
                    Lir.V2.blockAt prog L = some b → Lir.TermTies prog sloadChg obs o self L b) →
                  (∀ (L : Lir.Label) (b : Lir.Block),
                      Lir.V2.blockAt prog L = some b →
                        ∀ (dst : Lir.Label),
                          b.term = Lir.Term.jump dst → ∃ bdst, prog.blocks.toList[dst.idx]? = some bdst) →
                    (∀ (L : Lir.Label) (b : Lir.Block),
                        Lir.V2.blockAt prog L = some b →
                          ∀ (cond : Lir.Tmp) (thenL elseL : Lir.Label),
                            b.term = Lir.Term.branch cond thenL elseL →
                              (∃ bthen, prog.blocks.toList[thenL.idx]? = some bthen) ∧
                                ∃ belse, prog.blocks.toList[elseL.idx]? = some belse) →
                      (∀ (L : Lir.Label) (b : Lir.Block),
                          Lir.V2.blockAt prog L = some b →
                            ∀ (cond : Lir.Tmp) (thenL elseL : Lir.Label),
                              b.term = Lir.Term.branch cond thenL elseL →
                                (Lir.chargeOf (Lir.defsOf prog) sloadChg (Lir.recomputeFuel prog)
                                      (Lir.Expr.tmp cond)).length ≤
                                  1024) →
                        ∃ O,
                          (∃ last haltSig,
                              BytecodeLayer.Hoare.Runs (BytecodeLayer.System.codeFrame params code) last ∧
                                Evm.stepFrame last = Evm.Signal.halted haltSig ∧
                                  (Lir.V2.observe self (Evm.endFrame last haltSig)).world = O.world) ∧
                            Lir.V2.RunFrom prog o st₀ T prog.entry O
-/
#guard_msgs in
#check @Lir.V2.lower_conforms_cyclic_assembled

/-! ## The `Lir.Spec` audit surface (Wave 3, spec-extract)

Axiom guards on the `Spec/Seams.lean` + `Spec/Conformance.lean` re-export layer. No
signature freeze here: the existing `#check` freeze above already pins the flagship's
shape, and the aliases / forwarders below are defeq-tied to it (they fail to elaborate
on drift). -/

/-- info: 'Lir.Spec.lower_conforms_cyclic_assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.Spec.lower_conforms_cyclic_assembled

/-- info: 'Lir.Spec.lower_conforms_cyclic_tiefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.Spec.lower_conforms_cyclic_tiefree

/-- info: 'Lir.Spec.lower_conforms_cyclic_of_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.Spec.lower_conforms_cyclic_of_obligations

/-- info: 'Lir.Spec.callPreservesSelf_of_precompiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lir.Spec.callPreservesSelf_of_precompiles

