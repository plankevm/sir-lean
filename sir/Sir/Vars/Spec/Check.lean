import Sir.Vars.Spec

namespace Sir.Vars

inductive Diagnostic where
  | icallArity (callee : FunctionId) (args dests : Nat)
  | iretArity (declared actual : Nat)
  | recursiveCall (caller callee : FunctionId)
  | entryArity (function : FunctionId) (params outputs : Nat)
  | jumpTarget (target : BlockId) (inputs : Option Nat) (outputs : Nat)
  | variableUse (identifier : VarId)

abbrev CheckM := Except Diagnostic

def ensure (diagnostic : Diagnostic) (condition : Bool) : CheckM Unit :=
  if condition then .ok () else .error diagnostic

def checkList {α : Type} (check : α → CheckM Unit) : List α → CheckM Unit
  | [] => .ok ()
  | x :: rest => do
      check x
      checkList check rest

def checkArray {α : Type} (check : α → CheckM Unit) (xs : Array α) : CheckM Unit :=
  checkList check xs.toList

def checkBlocks (p : Program) (check : Function → Block → CheckM Unit) : CheckM Unit :=
  checkArray (fun fn => checkArray (check fn) fn.blocks) p.functions

def checkIcallArityStmt (p : Program) : Stmt → CheckM Unit
  | .icall callee args dests =>
      match p.function? callee with
      | none => .error (.icallArity callee args.size dests.size)
      | some fn =>
          ensure (.icallArity callee args.size dests.size)
            (fn.paramsOf.size == args.size && fn.outputs?.getD 0 == dests.size)
  | .assign _ _ | .sstore _ _ | .gas _ | .call _ | .malloc _ _ | .mallocUninit _ _
  | .mstore32 _ _ | .mload32 _ _ => .ok ()

def checkIcallArity (p : Program) : CheckM Unit :=
  checkBlocks p fun _ block => checkArray (checkIcallArityStmt p) block.statements

def checkIretArityBlock (fn : Function) (block : Block) : CheckM Unit :=
  match block.terminator with
  | .iret =>
      ensure (.iretArity (fn.outputs?.getD 0) block.outputs.size)
        (some block.outputs.size == fn.outputs?)
  | .halt | .jump _ | .branch _ _ _ => .ok ()

def checkIretArity (p : Program) : CheckM Unit :=
  checkBlocks p checkIretArityBlock

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

def checkRankStmt (rank : FunctionId → Nat) (caller : FunctionId) : Stmt → CheckM Unit
  | .icall callee _ _ =>
      ensure (.recursiveCall caller callee) (decide (rank callee < rank caller))
  | .assign _ _ | .sstore _ _ | .gas _ | .call _ | .malloc _ _ | .mallocUninit _ _
  | .mstore32 _ _ | .mload32 _ _ => .ok ()

def checkRankDecreases (p : Program) (rank : FunctionId → Nat) : CheckM Unit :=
  checkList
    (fun index => checkArray
      (fun block => checkArray (checkRankStmt rank ⟨index⟩) block.statements)
      (p.blocksOf ⟨index⟩))
    (List.range p.functions.size)

def checkAcyclicCalls (p : Program) : CheckM Unit :=
  checkRankDecreases p p.rank

def checkEntryFunction (function : FunctionId) (fn : Function) : CheckM Unit :=
  ensure (.entryArity function fn.paramsOf.size (fn.outputs?.getD 0))
    (fn.paramsOf.size == 0 && fn.outputs?.isNone)

def checkEntryArity (p : Program) : CheckM Unit := do
  checkEntryFunction ⟨0⟩ p.init
  match p.main with
  | none => .ok ()
  | some m => checkEntryFunction ⟨1⟩ m

def checkJumpTarget (fn : Function) (block : Block) (target : BlockId) : CheckM Unit :=
  match fn.block? target with
  | none => .error (.jumpTarget target none block.outputs.size)
  | some targetBlock =>
      ensure (.jumpTarget target (some targetBlock.inputs.size) block.outputs.size)
        (targetBlock.inputs.size == block.outputs.size)

def checkValidJumpTargets (p : Program) : CheckM Unit :=
  checkBlocks p fun fn block =>
    checkList (checkJumpTarget fn block) block.terminator.jumpTargets

def Block.undefinedUse? (block : Block) : Option VarId :=
  match (List.range block.statements.size).findSome? fun index =>
      (block.statements[index]?).bind fun statement =>
        statement.variablesRead.find? fun identifier =>
          decide (identifier ∉ block.variablesDefinedBefore index) with
  | some identifier => some identifier
  | none =>
      (block.terminator.variablesRead ++ block.outputs.toList).find? fun identifier =>
        decide (identifier ∉ block.variablesDefinedBefore block.statements.size)

def checkVariablesDefinedBeforeUse (p : Program) : CheckM Unit :=
  checkBlocks p fun _ block =>
    match block.undefinedUse? with
    | some identifier => .error (.variableUse identifier)
    | none => .ok ()

def checkWellFormed (p : Program) : CheckM Unit := do
  checkIcallArity p
  checkIretArity p
  checkAcyclicCalls p
  checkEntryArity p
  checkValidJumpTargets p
  checkVariablesDefinedBeforeUse p

end Sir.Vars
