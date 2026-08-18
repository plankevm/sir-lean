import Sir.Vars.Proofs.Rank
import Sir.Vars.Proofs.Check

namespace Sir.Vars

inductive Diagnostic where
  | icallArity (callee : FunctionId) (args dests : Nat)
  | iretArity (declared actual : Nat)
  | recursiveCall (caller callee : FunctionId)
  | entryArity (function : FunctionId) (params outputs : Nat)
  | jumpTarget (target : BlockId) (inputs : Option Nat) (outputs : Nat)
  | variableUse (identifier : VarId)

abbrev CheckM := Except Diagnostic

abbrev Ensures (P : Prop) := CheckM (PLift P)

def ensure (diagnostic : Diagnostic) (P : Prop) [Decidable P] : Ensures P :=
  if h : P then .ok ⟨h⟩ else .error diagnostic

def ensureAll {α : Type} {P : α → Prop} : (xs : List α) →
    ((x : α) → x ∈ xs → Ensures (P x)) → Ensures (∀ x ∈ xs, P x)
  | [], _ => .ok ⟨by simp⟩
  | x :: rest, check => do
      let ⟨head⟩ ← check x (List.mem_cons_self ..)
      let ⟨tail⟩ ← ensureAll rest fun y hy => check y (List.mem_cons_of_mem _ hy)
      return ⟨by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact head
        · exact tail y hy⟩

def ensureAllArray {α : Type} {P : α → Prop} (xs : Array α)
    (check : (x : α) → x ∈ xs → Ensures (P x)) : Ensures (∀ x ∈ xs, P x) := do
  let ⟨proof⟩ ← ensureAll xs.toList fun x hx => check x (Array.mem_toList_iff.mp hx)
  return ⟨fun x hx => proof x (Array.mem_toList_iff.mpr hx)⟩

def Stmt.IcallArityOk (p : Program) : Stmt → Prop
  | .icall callee args dests =>
      ∃ outputs, p.FunctionInputOutputArity args.size outputs callee ∧
        outputs.getD 0 = dests.size
  | _ => True

instance (p : Program) (callee : FunctionId) (args dests : Array VarId) :
    Decidable (∃ outputs, p.FunctionInputOutputArity args.size outputs callee ∧
      outputs.getD 0 = dests.size) :=
  match h : p.function? callee with
  | none =>
      isFalse (by
        rintro ⟨outputs, ⟨fn, hfn, _, _⟩, _⟩
        rw [h] at hfn
        simp at hfn)
  | some fn =>
      decidable_of_iff (fn.paramsOf.size = args.size ∧ fn.outputs?.getD 0 = dests.size) (by
        constructor
        · rintro ⟨hparams, houtputs⟩
          exact ⟨fn.outputs?, ⟨fn, h, hparams, rfl⟩, houtputs⟩
        · rintro ⟨outputs, ⟨fn', hfn', hparams, houtputs⟩, hdests⟩
          rw [h] at hfn'
          cases hfn'
          exact ⟨hparams, houtputs ▸ hdests⟩)

def checkIcallArityStmt (p : Program) : (stmt : Stmt) → Ensures (stmt.IcallArityOk p)
  | .icall callee args dests =>
      ensure (.icallArity callee args.size dests.size)
        (∃ outputs, p.FunctionInputOutputArity args.size outputs callee ∧
          outputs.getD 0 = dests.size)
  | .assign _ _ | .sstore _ _ | .gas _ | .call _ | .malloc _ _ | .mallocUninit _ _
  | .mstore32 _ _ | .mload32 _ _ => .ok ⟨trivial⟩

def checkIcallArity (p : Program) :
    Ensures (∀ callee args dests, p.HasStmt (.icall callee args dests) →
      ∃ outputs, p.FunctionInputOutputArity args.size outputs callee ∧
        outputs.getD 0 = dests.size) := do
  let ⟨checked⟩ ← ensureAllArray p.functions fun fn _ =>
    ensureAllArray fn.blocks fun block _ =>
      ensureAllArray block.statements fun stmt _ =>
        checkIcallArityStmt p stmt
  return ⟨by
    rintro callee args dests ⟨fn, hfn, block, hblock, hstmt⟩
    exact checked fn hfn block hblock _ hstmt⟩

def checkIretArity (p : Program) :
    Ensures (∀ fn ∈ p.functions, ∀ block ∈ fn.blocks,
      block.terminator = .iret → some block.outputs.size = fn.outputs?) :=
  ensureAllArray p.functions fun fn _ =>
    ensureAllArray fn.blocks fun block _ =>
      ensure (.iretArity (fn.outputs?.getD 0) block.outputs.size) _

def Program.blocksOf (p : Program) (f : FunctionId) : Array Block :=
  ((p.function? f).map (·.blocks)).getD #[]

def Stmt.calleeId? : Stmt → Option FunctionId
  | .icall callee _ _ => some callee
  | _ => none

def Program.callees (p : Program) (f : FunctionId) : List FunctionId :=
  (p.blocksOf f).toList.flatMap fun block => block.statements.toList.filterMap Stmt.calleeId?

def rankRound (p : Program) (previous : List Nat) : List Nat :=
  (List.range p.functions.size).map fun index =>
    (p.callees ⟨index⟩).foldl (fun bound callee => max bound (previous.getD callee.id 0 + 1)) 0

def rankRounds (p : Program) : Nat → List Nat
  | 0 => List.replicate p.functions.size 0
  | rounds + 1 => rankRound p (rankRounds p rounds)

def Program.rank (p : Program) (f : FunctionId) : Nat :=
  (rankRounds p p.functions.size).getD f.id 0

def Stmt.RankOk (rank : FunctionId → Nat) (caller : FunctionId) : Stmt → Prop
  | .icall callee _ _ => rank callee < rank caller
  | _ => True

def checkRankOkStmt (rank : FunctionId → Nat) (caller : FunctionId) :
    (stmt : Stmt) → Ensures (stmt.RankOk rank caller)
  | .icall callee _ _ => ensure (.recursiveCall caller callee) (rank callee < rank caller)
  | .assign _ _ | .sstore _ _ | .gas _ | .call _ | .malloc _ _ | .mallocUninit _ _
  | .mstore32 _ _ | .mload32 _ _ => .ok ⟨trivial⟩

def checkRankDecreases (p : Program) (rank : FunctionId → Nat) :
    Ensures (RankDecreases p rank) := do
  let ⟨checked⟩ ← ensureAll (List.range p.functions.size) fun index _ =>
    ensureAllArray (p.blocksOf ⟨index⟩) fun block _ =>
      ensureAllArray block.statements fun stmt _ =>
        checkRankOkStmt rank ⟨index⟩ stmt
  return ⟨by
    rintro f g ⟨args, dests, fn, hfn, block, hblock, hstmt⟩
    have hlt : f.id < p.functions.size := lt_size_of_getElem? hfn
    have hblocks : p.blocksOf f = fn.blocks := by simp [Program.blocksOf, hfn]
    exact checked f.id (List.mem_range.mpr hlt) block (hblocks ▸ hblock) _ hstmt⟩

def checkAcyclicCalls (p : Program) :
    Ensures (∀ f, ¬ Relation.TransGen p.callEdge f f) := do
  let ⟨decreasing⟩ ← checkRankDecreases p p.rank
  return ⟨Proofs.acyclic_of_rank decreasing⟩

instance (p : Program) :
    Decidable (∀ m, p.main = some m → m.paramsOf.size = 0 ∧ m.outputs? = none) :=
  match h : p.main with
  | none =>
      isTrue (by
        intro m hm
        simp at hm)
  | some m =>
      decidable_of_iff (m.paramsOf.size = 0 ∧ m.outputs? = none)
        ⟨fun hmain _ hm => by cases hm; exact hmain, fun hall => hall m rfl⟩

def checkEntryArity (p : Program) :
    Ensures ((p.init.paramsOf.size = 0 ∧ p.init.outputs? = none) ∧
      ∀ m, p.main = some m → m.paramsOf.size = 0 ∧ m.outputs? = none) := do
  let ⟨init⟩ ← ensure (.entryArity ⟨0⟩ p.init.paramsOf.size (p.init.outputs?.getD 0))
    (p.init.paramsOf.size = 0 ∧ p.init.outputs? = none)
  let ⟨main⟩ ← ensure
    (.entryArity ⟨1⟩ (p.main.elim 0 (·.paramsOf.size)) (p.main.elim 0 (·.outputs?.getD 0)))
    (∀ m, p.main = some m → m.paramsOf.size = 0 ∧ m.outputs? = none)
  return ⟨init, main⟩

instance (fn : Function) (target : BlockId) (size : Nat) :
    Decidable (∃ targetBlock, fn.block? target = some targetBlock ∧
      targetBlock.inputs.size = size) :=
  match h : fn.block? target with
  | none =>
      isFalse (by
        rintro ⟨targetBlock, htarget, _⟩
        simp at htarget)
  | some targetBlock =>
      decidable_of_iff (targetBlock.inputs.size = size) (by
        constructor
        · intro hsize
          exact ⟨targetBlock, rfl, hsize⟩
        · rintro ⟨other, hother, hsize⟩
          cases hother
          exact hsize)

def checkValidJumpTargets (p : Program) :
    Ensures (∀ fn ∈ p.functions,
      ∀ block ∈ fn.blocks, ∀ target ∈ block.terminator.jumpTargets,
        ∃ targetBlock, fn.block? target = some targetBlock ∧
          targetBlock.inputs.size = block.outputs.size) :=
  ensureAllArray p.functions fun fn _ =>
    ensureAllArray fn.blocks fun block _ =>
      ensureAll block.terminator.jumpTargets fun target _ =>
        ensure (.jumpTarget target ((fn.block? target).map (·.inputs.size))
          block.outputs.size) _

instance (block : Block) : Decidable block.VariablesDefinedBeforeUse :=
  decidable_of_iff _ (Block.variablesDefinedBeforeUse_iff block)

def Block.undefinedUse? (block : Block) : Option VarId :=
  ((List.range block.statements.size).findSome? fun index =>
      (block.statements[index]?).bind fun statement =>
        statement.variablesRead.find? fun identifier =>
          decide (identifier ∉ block.variablesDefinedBefore index)) <|>
    (block.terminator.variablesRead ++ block.outputs.toList).find? fun identifier =>
      decide (identifier ∉ block.variablesDefinedBefore block.statements.size)

def checkVariablesDefinedBeforeUse (p : Program) :
    Ensures (∀ fn ∈ p.functions, ∀ block ∈ fn.blocks, block.VariablesDefinedBeforeUse) :=
  ensureAllArray p.functions fun fn _ =>
    ensureAllArray fn.blocks fun block _ =>
      ensure (.variableUse (block.undefinedUse?.getD ⟨0⟩)) _

def checkWellFormed (p : Program) : Ensures p.WellFormed := do
  let ⟨icallArity⟩ ← checkIcallArity p
  let ⟨iretArity⟩ ← checkIretArity p
  let ⟨acyclicCalls⟩ ← checkAcyclicCalls p
  let ⟨entryArity⟩ ← checkEntryArity p
  let ⟨validJumpTargets⟩ ← checkValidJumpTargets p
  let ⟨variablesDefinedBeforeUse⟩ ← checkVariablesDefinedBeforeUse p
  return ⟨{ icallArity := icallArity, iretArity := iretArity,
            acyclicCalls := acyclicCalls, entryArity := entryArity,
            validJumpTargets := validJumpTargets,
            variablesDefinedBeforeUse := variablesDefinedBeforeUse }⟩

end Sir.Vars
