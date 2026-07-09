import LirLean.Spec.IR
import LirLean.Util.Words
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

def emitImm (w : Word) : List UInt8 := Byte.push32 :: wordBytesBE w

def slotOf (t : Tmp) : Nat := t.id * 32

def emitDest (off : Nat) : List UInt8 := Byte.push4 :: offsetBytesBE off

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

def encode (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

def lower (prog : Program) : ByteArray := encode (emit (defsOf prog) prog)

end Lir
