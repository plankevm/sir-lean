import Sir.Vars.Spec.Check
import Sir.Vars.Proofs.Rank

namespace Sir.Vars.Proofs

theorem lt_size_of_getElem? {α : Type} {xs : Array α} {index : Nat} {x : α}
    (h : xs[index]? = some x) : index < xs.size := by
  by_contra hle
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt hle)] at h
  simp at h

theorem bind_eq_ok {α β : Type} {x : CheckM α} {f : α → CheckM β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error d => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem ensure_eq_ok {d : Diagnostic} {b : Bool} (h : ensure d b = .ok ()) : b = true := by
  cases b with
  | true => rfl
  | false => simp [ensure] at h

theorem checkList_eq_ok {α : Type} {check : α → CheckM Unit} :
    {xs : List α} → checkList check xs = .ok () → ∀ x ∈ xs, check x = .ok ()
  | [], _, _, hx => by simp at hx
  | x :: rest, h, y, hy => by
      obtain ⟨_, hx, hrest⟩ := bind_eq_ok h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact checkList_eq_ok hrest y hy

theorem checkArray_eq_ok {α : Type} {check : α → CheckM Unit} {xs : Array α}
    (h : checkArray check xs = .ok ()) : ∀ x ∈ xs, check x = .ok () :=
  fun x hx => checkList_eq_ok h x (Array.mem_toList_iff.mpr hx)

theorem checkBlocks_eq_ok {p : Program} {check : Function → Block → CheckM Unit}
    (h : checkBlocks p check = .ok ()) :
    ∀ fn ∈ p.functions, ∀ block ∈ fn.blocks, check fn block = .ok () :=
  fun fn hfn block hblock => checkArray_eq_ok (checkArray_eq_ok h fn hfn) block hblock

theorem icallArity_of_check {p : Program} (h : checkIcallArity p = .ok ()) :
    ∀ callee args dests, p.HasStmt (.icall callee args dests) →
      ∃ outputs, p.FunctionInputOutputArity args.size outputs callee ∧
        outputs.getD 0 = dests.size := by
  rintro callee args dests ⟨fn, hfn, block, hblock, hstmt⟩
  have hcheck := checkArray_eq_ok (checkBlocks_eq_ok h fn hfn block hblock) _ hstmt
  simp only [checkIcallArityStmt] at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i target htarget
    have := ensure_eq_ok hcheck
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨target.outputs?, ⟨target, htarget, this.1, rfl⟩, this.2⟩

theorem iretArity_of_check {p : Program} (h : checkIretArity p = .ok ()) :
    ∀ fn ∈ p.functions, ∀ block ∈ fn.blocks,
      block.terminator = .iret → some block.outputs.size = fn.outputs? := by
  intro fn hfn block hblock hiret
  have hcheck := checkBlocks_eq_ok h fn hfn block hblock
  unfold checkIretArityBlock at hcheck
  rw [hiret] at hcheck
  simpa using ensure_eq_ok hcheck

theorem rankDecreases_of_check {p : Program} {rank : FunctionId → Nat}
    (h : checkRankDecreases p rank = .ok ()) : RankDecreases p rank := by
  rintro f g ⟨args, dests, fn, hfn, block, hblock, hstmt⟩
  have hlt : f.id < p.functions.size := lt_size_of_getElem? hfn
  have hblocks : p.blocksOf f = fn.blocks := by simp [Program.blocksOf, hfn]
  have hcheck := checkArray_eq_ok
    (checkArray_eq_ok (checkList_eq_ok h f.id (List.mem_range.mpr hlt)) block (hblocks ▸ hblock))
    _ hstmt
  simpa [checkRankStmt] using ensure_eq_ok hcheck

theorem acyclicCalls_of_check {p : Program} (h : checkAcyclicCalls p = .ok ()) :
    ∀ f, ¬ Relation.TransGen p.callEdge f f :=
  acyclic_of_rank (rankDecreases_of_check h)

theorem entryFunction_of_check {function : FunctionId} {fn : Function}
    (h : checkEntryFunction function fn = .ok ()) :
    fn.paramsOf.size = 0 ∧ fn.outputs? = none := by
  simpa [Bool.and_eq_true, Option.isNone_iff_eq_none] using ensure_eq_ok h

theorem entryArity_of_check {p : Program} (h : checkEntryArity p = .ok ()) :
    (p.init.paramsOf.size = 0 ∧ p.init.outputs? = none) ∧
      ∀ m, p.main = some m → m.paramsOf.size = 0 ∧ m.outputs? = none := by
  obtain ⟨_, hinit, hmain⟩ := bind_eq_ok h
  refine ⟨entryFunction_of_check hinit, fun m hm => ?_⟩
  rw [hm] at hmain
  exact entryFunction_of_check hmain

theorem validJumpTargets_of_check {p : Program} (h : checkValidJumpTargets p = .ok ()) :
    ∀ fn ∈ p.functions,
      ∀ block ∈ fn.blocks, ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, fn.block? target = some targetBlock ∧
          targetBlock.inputs.size = block.outputs.size := by
  intro fn hfn block hblock target htarget
  have hcheck := checkList_eq_ok (checkBlocks_eq_ok h fn hfn block hblock) target htarget
  unfold checkJumpTarget at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i targetBlock hblock?
    exact ⟨targetBlock, hblock?, by simpa using ensure_eq_ok hcheck⟩

theorem Block.variablesDefinedBeforeUse_of_undefinedUse? {block : Block}
    (h : block.undefinedUse? = none) : block.VariablesDefinedBeforeUse := by
  unfold Block.undefinedUse? at h
  split at h
  · simp at h
  · rename_i hstatements
    refine ⟨fun index statement hstatement identifier hread => ?_, fun identifier hread => ?_⟩
    · have hindex := List.findSome?_eq_none_iff.mp hstatements index
        (List.mem_range.mpr (lt_size_of_getElem? hstatement))
      rw [hstatement] at hindex
      simpa using List.find?_eq_none.mp hindex identifier hread
    · simpa using List.find?_eq_none.mp h identifier hread

theorem variablesDefinedBeforeUse_of_check {p : Program}
    (h : checkVariablesDefinedBeforeUse p = .ok ()) :
    ∀ fn ∈ p.functions, ∀ block ∈ fn.blocks, block.VariablesDefinedBeforeUse := by
  intro fn hfn block hblock
  have hcheck := checkBlocks_eq_ok h fn hfn block hblock
  split at hcheck
  · simp at hcheck
  · exact Block.variablesDefinedBeforeUse_of_undefinedUse? (by assumption)

theorem Program.wellFormed_of_check {p : Program} (h : checkWellFormed p = .ok ()) :
    p.WellFormed := by
  obtain ⟨_, hicall, h⟩ := bind_eq_ok h
  obtain ⟨_, hiret, h⟩ := bind_eq_ok h
  obtain ⟨_, hacyclic, h⟩ := bind_eq_ok h
  obtain ⟨_, hentry, h⟩ := bind_eq_ok h
  obtain ⟨_, hjump, hvars⟩ := bind_eq_ok h
  exact { icallArity := icallArity_of_check hicall
          iretArity := iretArity_of_check hiret
          acyclicCalls := acyclicCalls_of_check hacyclic
          entryArity := entryArity_of_check hentry
          validJumpTargets := validJumpTargets_of_check hjump
          variablesDefinedBeforeUse := variablesDefinedBeforeUse_of_check hvars }

end Sir.Vars.Proofs
