import LirLean.Spec.IR
import BytecodeLayer.Asm
import BytecodeLayer.Exec
import Evm

namespace Lir

open Evm

namespace Byte
def stop     : UInt8 := 0x00
def add      : UInt8 := 0x01
def lt       : UInt8 := 0x10
def pop      : UInt8 := 0x50
def mload    : UInt8 := 0x51
def mstore   : UInt8 := 0x52
def sload    : UInt8 := 0x54
def sstore   : UInt8 := 0x55
def jump     : UInt8 := 0x56
def jumpi    : UInt8 := 0x57
def gas      : UInt8 := 0x5a
def jumpdest : UInt8 := 0x5b
def push4    : UInt8 := 0x63
def push32   : UInt8 := 0x7f
def call     : UInt8 := 0xf1
def create2  : UInt8 := 0xf5
def ret      : UInt8 := 0xf3
end Byte

inductive Loc where
  | remat (e : Expr)
  | slot  (n : Nat)
deriving DecidableEq, Repr

abbrev Alloc := Tmp → Option Loc

def emitImm (w : Word) : List UInt8 := Byte.push32 :: BytecodeLayer.Exec.wordBytesBE w

def slotOf (t : Tmp) : Nat := t.id * 32

def emitDest (off : Nat) : List UInt8 := Byte.push4 :: BytecodeLayer.Exec.offsetBytesBE off

def locOfExpr : Expr → Loc
  | e => .remat e

def defEnv (prog : Program) : List (Tmp × Loc) :=
  prog.blocks.toList.flatMap (fun b =>
    b.stmts.filterMap (fun
      | .assign t .gas       => some (t, Loc.slot (slotOf t))
      | .assign t (.sload _) => some (t, Loc.slot (slotOf t))
      | .assign t e          => some (t, locOfExpr e)
      | .call ⟨_, _, some t⟩ => some (t, Loc.slot (slotOf t))
      | .create ⟨_, _, _, _, some t⟩ => some (t, Loc.slot (slotOf t))
      | _                    => none))

def defsOf (prog : Program) : Alloc :=
  fun t => ((defEnv prog).find? (fun p => p.1 == t)).map (·.2)

def rematOf (prog : Program) (t : Tmp) : Option Expr :=
  match defsOf prog t with
  | some (.remat e) => some e
  | _               => none

@[reducible] def allocate (prog : Program) : Alloc := defsOf prog

def matExpr (cache : Tmp → List UInt8) : Expr → List UInt8
  | .imm w   => emitImm w
  | .tmp t   => cache t
  | .add a b => cache b ++ cache a ++ [Byte.add]
  | .lt  a b => cache b ++ cache a ++ [Byte.lt]
  | .sload k => cache k ++ [Byte.sload]
  | .gas     => [Byte.gas]

def matLoc (cache : Tmp → List UInt8) : Loc → List UInt8
  | .remat e => matExpr cache e
  | .slot n  => emitImm (UInt256.ofNat n) ++ [Byte.mload]

def matStep (c : Tmp → List UInt8) (p : Tmp × Loc) : Tmp → List UInt8 :=
  Function.update c p.1 (matLoc c p.2)

def matFold (init : Tmp → List UInt8) (l : List (Tmp × Loc)) : Tmp → List UInt8 :=
  l.foldl matStep init

def matCache (prog : Program) : Tmp → List UInt8 :=
  matFold (fun _ => emitImm 0) (defEnv prog)

@[simp] theorem matExpr_imm (cache : Tmp → List UInt8) (w : Word) :
    matExpr cache (.imm w) = emitImm w := rfl
@[simp] theorem matExpr_tmp (cache : Tmp → List UInt8) (t : Tmp) :
    matExpr cache (.tmp t) = cache t := rfl
@[simp] theorem matExpr_add (cache : Tmp → List UInt8) (a b : Tmp) :
    matExpr cache (.add a b) = cache b ++ cache a ++ [Byte.add] := rfl
@[simp] theorem matExpr_lt (cache : Tmp → List UInt8) (a b : Tmp) :
    matExpr cache (.lt a b) = cache b ++ cache a ++ [Byte.lt] := rfl
@[simp] theorem matExpr_sload (cache : Tmp → List UInt8) (k : Tmp) :
    matExpr cache (.sload k) = cache k ++ [Byte.sload] := rfl
@[simp] theorem matExpr_gas (cache : Tmp → List UInt8) :
    matExpr cache .gas = [Byte.gas] := rfl

@[simp] theorem matLoc_remat (cache : Tmp → List UInt8) (e : Expr) :
    matLoc cache (.remat e) = matExpr cache e := rfl
@[simp] theorem matLoc_slot (cache : Tmp → List UInt8) (n : Nat) :
    matLoc cache (.slot n) = emitImm (UInt256.ofNat n) ++ [Byte.mload] := rfl

@[simp] theorem matFold_nil (init : Tmp → List UInt8) :
    matFold init [] = init := rfl
@[simp] theorem matFold_cons (init : Tmp → List UInt8) (p : Tmp × Loc)
    (l : List (Tmp × Loc)) :
    matFold init (p :: l) = matFold (matStep init p) l := rfl

theorem matCache_eq (prog : Program) :
    matCache prog = matFold (fun _ => emitImm 0) (defEnv prog) := rfl

def emitStmt (cache : Tmp → List UInt8) (alloc : Alloc) : Stmt → List UInt8
  | .assign t e =>
      match alloc t with
      | some (.slot n) =>
          matExpr cache e
            ++ emitImm (UInt256.ofNat n)
            ++ [Byte.mstore]
      | _ =>
          []
  | .sstore key value =>
      cache value ++ cache key ++ [Byte.sstore]
  | .call cs =>
      -- Stack order for CALL: ret/arg windows are zero, then callee and gas.
      emitImm 0
        ++ emitImm 0
        ++ emitImm 0
        ++ emitImm 0
        ++ emitImm 0
        ++ cache cs.callee
        ++ cache cs.gasFwd
        ++ [Byte.call]
        -- A result tmp stores the success word; otherwise discard it.
        ++ (match cs.resultTmp with
            | some t =>
                emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none =>
                [Byte.pop])
  | .create cs =>
      -- CREATE2 pops value, init offset, init size, salt.
      cache cs.salt
        ++ cache cs.initSize
        ++ cache cs.initOffset
        ++ cache cs.value
        ++ [Byte.create2]
        -- A result tmp stores the address word; otherwise discard it.
        ++ (match cs.resultTmp with
            | some t =>
                emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none =>
                [Byte.pop])

def emitTerm (cache : Tmp → List UInt8) (labelOff : Nat → Nat) : Term → List UInt8
  | .ret t              => cache t
                             ++ emitImm 0 ++ [Byte.mstore]
                             ++ emitImm 32 ++ emitImm 0 ++ [Byte.ret]
  | .stop               => [Byte.stop]
  | .jump dst           => emitDest (labelOff dst.idx) ++ [Byte.jump]
  | .branch cond thenL elseL =>
      cache cond
      ++ emitDest (labelOff thenL.idx) ++ [Byte.jumpi]
      ++ emitDest (labelOff elseL.idx) ++ [Byte.jump]

def emitBlockBody (cache : Tmp → List UInt8) (alloc : Alloc)
    (labelOff : Nat → Nat) (b : Block) : List UInt8 :=
  (b.stmts.flatMap (emitStmt cache alloc)) ++ emitTerm cache labelOff b.term

def blockLen (cache : Tmp → List UInt8) (alloc : Alloc) (b : Block) : Nat :=
  1 + (emitBlockBody cache alloc (fun _ => 0) b).length

def offsetTable (cache : Tmp → List UInt8) (alloc : Alloc) (blocks : Array Block) (i : Nat) : Nat :=
  ((blocks.toList.take i).map (blockLen cache alloc)).sum

def emit (a : Alloc) (prog : Program) : List UInt8 :=
  let cache := matCache prog
  let labelOff := offsetTable cache a prog.blocks
  prog.blocks.toList.flatMap (fun b => Byte.jumpdest :: emitBlockBody cache a labelOff b)

namespace Asm

open BytecodeLayer.Asm

def emitImm (w : Word) : List AsmInstr := [.push w]

def matExpr (cache : Tmp → List AsmInstr) : Expr → List AsmInstr
  | .imm w   => emitImm w
  | .tmp t   => cache t
  | .add a b => cache b ++ cache a ++ [.op .add]
  | .lt  a b => cache b ++ cache a ++ [.op .lt]
  | .sload k => cache k ++ [.op .sload]
  | .gas     => [.op .gas]

def matLoc (cache : Tmp → List AsmInstr) : Loc → List AsmInstr
  | .remat e => matExpr cache e
  | .slot n  => emitImm (UInt256.ofNat n) ++ [.op .mload]

def matStep (cache : Tmp → List AsmInstr) (binding : Tmp × Loc) :
    Tmp → List AsmInstr :=
  Function.update cache binding.1 (matLoc cache binding.2)

def matFold (init : Tmp → List AsmInstr) (bindings : List (Tmp × Loc)) :
    Tmp → List AsmInstr :=
  bindings.foldl matStep init

def matCache (prog : Program) : Tmp → List AsmInstr :=
  matFold (fun _ => emitImm 0) (defEnv prog)

def emitStmt (cache : Tmp → List AsmInstr) (alloc : Alloc) : Stmt → List AsmInstr
  | .assign t e =>
      match alloc t with
      | some (.slot n) =>
          matExpr cache e ++ emitImm (UInt256.ofNat n) ++ [.op .mstore]
      | _ =>
          []
  | .sstore key value =>
      cache value ++ cache key ++ [.op .sstore]
  | .call cs =>
      emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
        ++ cache cs.callee ++ cache cs.gasFwd ++ [.op .call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [.op .mstore]
            | none => [.op .pop])
  | .create cs =>
      cache cs.salt ++ cache cs.initSize ++ cache cs.initOffset ++ cache cs.value
        ++ [.op .create2]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [.op .mstore]
            | none => [.op .pop])

def emitTerm (cache : Tmp → List AsmInstr) : Term → List AsmInstr
  | .ret t =>
      cache t ++ emitImm 0 ++ [.op .mstore]
        ++ emitImm 32 ++ emitImm 0 ++ [.op .ret]
  | .stop =>
      [.op .stop]
  | .jump dst =>
      [.pushLabel dst.idx, .op .jump]
  | .branch cond thenL elseL =>
      cache cond ++ [.pushLabel thenL.idx, .op .jumpi,
        .pushLabel elseL.idx, .op .jump]

def emitBlock (cache : Tmp → List AsmInstr) (alloc : Alloc) (block : Block) : AsmBlock :=
  ⟨block.stmts.flatMap (emitStmt cache alloc) ++ emitTerm cache block.term⟩

end Asm

/-- Translate LIR into structured assembly without choosing block offsets. -/
def lowerAsm (prog : Program) : BytecodeLayer.Asm.AsmProgram :=
  let cache := Asm.matCache prog
  let alloc := defsOf prog
  ⟨prog.blocks.map (Asm.emitBlock cache alloc)⟩

def lower (prog : Program) : ByteArray :=
  BytecodeLayer.Asm.assemble (lowerAsm prog)

namespace Asm

open BytecodeLayer.Asm

theorem encode_matExpr (labelOffset : Nat → Nat)
    {asmCache : Tmp → List AsmInstr} {byteCache : Tmp → List UInt8}
    (hcache : ∀ t, encodeInstrs labelOffset (asmCache t) = byteCache t)
    (expr : Expr) :
    encodeInstrs labelOffset (matExpr asmCache expr) = Lir.matExpr byteCache expr := by
  cases expr <;> simp [matExpr, Lir.matExpr, emitImm, Lir.emitImm,
    encodeInstr, Op.byte, hcache, Lir.Byte.push32, Lir.Byte.add, Lir.Byte.lt,
    Lir.Byte.sload, Lir.Byte.gas]

theorem encode_matLoc (labelOffset : Nat → Nat)
    {asmCache : Tmp → List AsmInstr} {byteCache : Tmp → List UInt8}
    (hcache : ∀ t, encodeInstrs labelOffset (asmCache t) = byteCache t)
    (loc : Loc) :
    encodeInstrs labelOffset (matLoc asmCache loc) = Lir.matLoc byteCache loc := by
  cases loc with
  | remat expr => exact encode_matExpr labelOffset hcache expr
  | slot n => simp [matLoc, Lir.matLoc, emitImm, Lir.emitImm,
      encodeInstr, Op.byte, Lir.Byte.push32, Lir.Byte.mload]

theorem encode_matStep (labelOffset : Nat → Nat)
    {asmCache : Tmp → List AsmInstr} {byteCache : Tmp → List UInt8}
    (hcache : ∀ t, encodeInstrs labelOffset (asmCache t) = byteCache t)
    (binding : Tmp × Loc) (t : Tmp) :
    encodeInstrs labelOffset (matStep asmCache binding t) =
      Lir.matStep byteCache binding t := by
  by_cases h : t = binding.1
  · subst t
    simp [matStep, Lir.matStep, Function.update, encode_matLoc labelOffset hcache]
  · simp [matStep, Lir.matStep, Function.update, h, hcache]

theorem encode_matFold (labelOffset : Nat → Nat)
    {asmCache : Tmp → List AsmInstr} {byteCache : Tmp → List UInt8}
    (hcache : ∀ t, encodeInstrs labelOffset (asmCache t) = byteCache t)
    (bindings : List (Tmp × Loc)) (t : Tmp) :
    encodeInstrs labelOffset (matFold asmCache bindings t) =
      Lir.matFold byteCache bindings t := by
  induction bindings generalizing asmCache byteCache with
  | nil => exact hcache t
  | cons binding rest ih =>
      simp only [matFold, Lir.matFold, List.foldl_cons]
      exact ih (encode_matStep labelOffset hcache binding)

theorem encode_matCache (prog : Program) (labelOffset : Nat → Nat) (t : Tmp) :
    encodeInstrs labelOffset (matCache prog t) = Lir.matCache prog t := by
  apply encode_matFold labelOffset (bindings := defEnv prog)
  intro u
  simp [emitImm, Lir.emitImm, encodeInstr, Lir.Byte.push32]

theorem encode_emitStmt (prog : Program) (labelOffset : Nat → Nat) (stmt : Stmt) :
    encodeInstrs labelOffset (emitStmt (matCache prog) (defsOf prog) stmt) =
      Lir.emitStmt (Lir.matCache prog) (defsOf prog) stmt := by
  cases stmt with
  | assign t expr =>
      cases halloc : defsOf prog t with
      | none => simp [emitStmt, Lir.emitStmt, halloc]
      | some loc =>
          cases loc with
          | remat e => simp [emitStmt, Lir.emitStmt, halloc]
          | slot n =>
              simp [emitStmt, Lir.emitStmt, halloc,
                encode_matExpr labelOffset (fun t => encode_matCache prog labelOffset t),
                emitImm, Lir.emitImm, encodeInstr, Op.byte,
                Lir.Byte.push32, Lir.Byte.mstore]
  | sstore key value =>
      simp [emitStmt, Lir.emitStmt, encode_matCache, encodeInstr, Op.byte,
        Lir.Byte.sstore]
  | call spec =>
      cases hresult : spec.resultTmp <;>
        simp [emitStmt, Lir.emitStmt, encode_matCache, emitImm, Lir.emitImm,
          encodeInstr, Op.byte, Lir.Byte.push32, Lir.Byte.call,
          Lir.Byte.mstore, Lir.Byte.pop, hresult]
  | create spec =>
      cases hresult : spec.resultTmp <;>
        simp [emitStmt, Lir.emitStmt, encode_matCache, emitImm, Lir.emitImm,
          encodeInstr, Op.byte, Lir.Byte.push32, Lir.Byte.create2,
          Lir.Byte.mstore, Lir.Byte.pop, hresult]

theorem encode_emitTerm (prog : Program) (labelOffset : Nat → Nat) (term : Term) :
    encodeInstrs labelOffset (emitTerm (matCache prog) term) =
      Lir.emitTerm (Lir.matCache prog) labelOffset term := by
  cases term <;> simp [emitTerm, Lir.emitTerm, encode_matCache, emitImm, Lir.emitImm,
    Lir.emitDest, encodeInstr, Op.byte, Lir.Byte.push32, Lir.Byte.push4,
    Lir.Byte.mstore, Lir.Byte.ret, Lir.Byte.stop, Lir.Byte.jump,
    Lir.Byte.jumpi]

theorem encode_emitStmts (prog : Program) (labelOffset : Nat → Nat)
    (stmts : List Stmt) :
    encodeInstrs labelOffset (stmts.flatMap (emitStmt (matCache prog) (defsOf prog))) =
      stmts.flatMap (Lir.emitStmt (Lir.matCache prog) (defsOf prog)) := by
  induction stmts with
  | nil => rfl
  | cons stmt rest =>
      simp [encode_emitStmt, *]

theorem encode_emitBlock (prog : Program) (labelOffset : Nat → Nat) (block : Block) :
    encodeInstrs labelOffset (emitBlock (matCache prog) (defsOf prog) block).body =
      Lir.emitBlockBody (Lir.matCache prog) (defsOf prog) labelOffset block := by
  simp [emitBlock, Lir.emitBlockBody, encode_emitTerm, encode_emitStmts]

theorem blockLength_emitBlock (prog : Program) (block : Block) :
    blockLength (emitBlock (matCache prog) (defsOf prog) block) =
      Lir.blockLen (Lir.matCache prog) (defsOf prog) block := by
  rw [blockLength, ← encodeInstrs_length (fun _ => 0)]
  rw [encode_emitBlock]
  rfl

theorem blockOffset_lowerAsm (prog : Program) (label : Nat) :
    blockOffset (lowerAsm prog) label =
      Lir.offsetTable (Lir.matCache prog) (defsOf prog) prog.blocks label := by
  unfold blockOffset lowerAsm Lir.offsetTable
  simp only [Array.toList_map]
  have h : ∀ (blocks : List Block) (i : Nat),
      (List.take i (List.map
          (blockLength ∘ emitBlock (matCache prog) (defsOf prog)) blocks)).sum =
        (List.take i
          (List.map (Lir.blockLen (Lir.matCache prog) (defsOf prog)) blocks)).sum := by
    intro blocks i
    induction blocks generalizing i with
    | nil => simp
    | cons block rest ih =>
        cases i <;> simp [blockLength_emitBlock, ih]
  rw [List.map_take, List.map_take, List.map_map]
  exact h prog.blocks.toList label

theorem encodeBlock_emitBlock (prog : Program) (labelOffset : Nat → Nat) (block : Block) :
    BytecodeLayer.Asm.encodeBlock labelOffset
        (emitBlock (matCache prog) (defsOf prog) block) =
      Lir.Byte.jumpdest ::
        Lir.emitBlockBody (Lir.matCache prog) (defsOf prog) labelOffset block := by
  simp [BytecodeLayer.Asm.encodeBlock, encode_emitBlock, Lir.Byte.jumpdest]

theorem bytes_lowerAsm (prog : Program) :
    BytecodeLayer.Asm.bytes (lowerAsm prog) = Lir.emit (defsOf prog) prog := by
  unfold BytecodeLayer.Asm.bytes
  rw [show blockOffset (lowerAsm prog) =
      Lir.offsetTable (Lir.matCache prog) (defsOf prog) prog.blocks from by
    funext label
    exact blockOffset_lowerAsm prog label]
  unfold lowerAsm Lir.emit
  simp only [Array.toList_map]
  induction prog.blocks.toList with
  | nil => rfl
  | cons block rest ih =>
      simp [encodeBlock_emitBlock, ih]

end Asm

/-- The bytecode lowering factors through the IR-independent assembler. -/
theorem lower_eq_assemble_lowerAsm (prog : Program) :
    lower prog = BytecodeLayer.Asm.assemble (lowerAsm prog) := rfl

end Lir
