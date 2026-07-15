import LirLean.Spec.IR
import BytecodeLayer.Exec.Observable
import Evm

namespace Lir

open Evm

abbrev World := BytecodeLayer.Exec.World
abbrev HaltResult := BytecodeLayer.Exec.HaltResult
abbrev GasOracle := BytecodeLayer.Exec.GasOracle
abbrev Trace := GasOracle
abbrev CallStream := BytecodeLayer.Exec.CallStream
abbrev CreateStream := BytecodeLayer.Exec.CreateStream
abbrev Observable := BytecodeLayer.Exec.Observable

structure IRState where
  locals : Tmp → Option Word
  world  : World

def IRState.setLocal (st : IRState) (t : Tmp) (w : Word) : IRState :=
  { st with locals := fun t' => if t' = t then some w else st.locals t' }

def IRState.setStorage (st : IRState) (k v : Word) : IRState :=
  { st with world := fun k' => if k' = k then v else st.world k' }

def evalExpr (st : IRState) (obs : Word) : Expr → Option Word
  | .imm w   => some w
  | .tmp t   => st.locals t
  | .add a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.add x y)
  | .lt  a b => do let x ← st.locals a; let y ← st.locals b; pure (UInt256.lt x y)
  | .sload k => do let key ← st.locals k; pure (st.world key)
  | .gas     => some obs

def blockAt (prog : Program) (L : Label) : Option Block :=
  prog.blocks[L.idx]?

-- A statement consumes the oracle streams it actually observes: `.gas` pops one
-- gas word, `.call` pops one call result/world pair, and `.create` pops one
-- create result/world pair. Pure statements leave all streams untouched.
inductive EvalStmt (prog : Program) :
    IRState → GasOracle → CallStream → CreateStream → Stmt →
    IRState → GasOracle → CallStream → CreateStream → Prop where
  | assignPure {st : IRState} {T : GasOracle} {C : CallStream} {D : CreateStream}
      {t : Tmp} {e : Expr} {w : Word}
      (hne : e ≠ .gas) (hv : evalExpr st 0 e = some w) :
      EvalStmt prog st T C D (.assign t e) (st.setLocal t w) T C D
  | assignGas {st : IRState} {obs : Word} {T : GasOracle}
      {C : CallStream} {D : CreateStream} {t : Tmp} :
      EvalStmt prog st (obs :: T) C D (.assign t .gas) (st.setLocal t obs) T C D
  | sstore {st : IRState} {T : GasOracle} {C : CallStream} {D : CreateStream}
      {key value : Tmp} {kw vw : Word}
      (hk : st.locals key = some kw) (hv : st.locals value = some vw) :
      EvalStmt prog st T C D (.sstore key value) (st.setStorage kw vw) T C D
  | call {st : IRState} {T : GasOracle} {C : CallStream} {D : CreateStream} {cs : CallSpec}
      {calleeW gasFwdW success : Word} {world' : World}
      (hcallee : st.locals cs.callee = some calleeW)
      (hgas : st.locals cs.gasFwd = some gasFwdW) :
      EvalStmt prog st T ((world', success) :: C) D (.call cs)
        (match cs.resultTmp with
          | some t => { st with world := world' }.setLocal t success
          | none   => { st with world := world' })
        T C D
  | create {st : IRState} {T : GasOracle} {C : CallStream} {D : CreateStream}
      {cs : CreateSpec} {valueW initOffW initSizeW saltW addrW : Word} {world' : World}
      (hvalue : st.locals cs.value = some valueW)
      (hoff   : st.locals cs.initOffset = some initOffW)
      (hsize  : st.locals cs.initSize = some initSizeW)
      (hsalt  : st.locals cs.salt = some saltW) :
      EvalStmt prog st T C ((world', addrW) :: D) (.create cs)
        (match cs.resultTmp with
          | some t => { st with world := world' }.setLocal t addrW
          | none   => { st with world := world' })
        T C D

inductive RunStmts (prog : Program) :
    IRState → GasOracle → CallStream → CreateStream → List Stmt →
    IRState → GasOracle → CallStream → CreateStream → Prop where
  | nil {st : IRState} {T : GasOracle} {C : CallStream} {D : CreateStream} :
      RunStmts prog st T C D [] st T C D
  | cons {st st' st'' : IRState} {T T' T'' : GasOracle} {C C' C'' : CallStream}
      {D D' D'' : CreateStream} {s : Stmt} {ss : List Stmt}
      (hh : EvalStmt prog st T C D s st' T' C' D')
      (ht : RunStmts prog st' T' C' D' ss st'' T'' C'' D'') :
      RunStmts prog st T C D (s :: ss) st'' T'' C'' D''

-- Big-step execution from a label to an observable. The relation threads the
-- oracle streams through statement lists but does not expose the leftovers.
inductive RunFrom (prog : Program) :
    IRState → GasOracle → CallStream → CreateStream → Label → Observable → Prop where
  | ret {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {t : Tmp} {w : Word}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFrom prog st T C D L { world := st'.world, result := .returned w }
  | stop {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .stop) :
      RunFrom prog st T C D L { world := st'.world, result := .stopped }
  | branchThen {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {cond : Tmp} {cw : Word} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some cw) (hnz : cw ≠ 0)
      (hrest : RunFrom prog st' T' C' D' thenL O) :
      RunFrom prog st T C D L O
  | branchElse {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {cond : Tmp} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some 0)
      (hrest : RunFrom prog st' T' C' D' elseL O) :
      RunFrom prog st T C D L O
  | jump {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {dst : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .jump dst)
      (hrest : RunFrom prog st' T' C' D' dst O) :
      RunFrom prog st T C D L O

def IRRun (prog : Program) (w₀ : World) (T : GasOracle) (C : CallStream) (D : CreateStream)
    (O : Observable) : Prop :=
  RunFrom prog { locals := fun _ => none, world := w₀ } T C D prog.entry O

-- Variant of `RunFrom` that also returns the unconsumed suffixes. This supports
-- exact-consumption statements without changing the main observable relation.
inductive RunFromLeft (prog : Program) :
    IRState → GasOracle → CallStream → CreateStream → Label → Observable →
    GasOracle → CallStream → CreateStream → Prop where
  | ret {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block} {t : Tmp} {w : Word}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .ret t)
      (hv : st'.locals t = some w) :
      RunFromLeft prog st T C D L { world := st'.world, result := .returned w } T' C' D'
  | stop {st st' : IRState} {T T' : GasOracle} {C C' : CallStream} {D D' : CreateStream}
      {L : Label} {b : Block}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .stop) :
      RunFromLeft prog st T C D L { world := st'.world, result := .stopped } T' C' D'
  | branchThen {st st' : IRState} {T T' Tleft : GasOracle} {C C' Cleft : CallStream}
      {D D' Dleft : CreateStream} {L : Label}
      {b : Block} {cond : Tmp} {cw : Word} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some cw) (hnz : cw ≠ 0)
      (hrest : RunFromLeft prog st' T' C' D' thenL O Tleft Cleft Dleft) :
      RunFromLeft prog st T C D L O Tleft Cleft Dleft
  | branchElse {st st' : IRState} {T T' Tleft : GasOracle} {C C' Cleft : CallStream}
      {D D' Dleft : CreateStream} {L : Label}
      {b : Block} {cond : Tmp} {thenL elseL : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .branch cond thenL elseL)
      (hc : st'.locals cond = some 0)
      (hrest : RunFromLeft prog st' T' C' D' elseL O Tleft Cleft Dleft) :
      RunFromLeft prog st T C D L O Tleft Cleft Dleft
  | jump {st st' : IRState} {T T' Tleft : GasOracle} {C C' Cleft : CallStream}
      {D D' Dleft : CreateStream} {L : Label}
      {b : Block} {dst : Label} {O : Observable}
      (hb : blockAt prog L = some b)
      (hss : RunStmts prog st T C D b.stmts st' T' C' D')
      (hterm : b.term = .jump dst)
      (hrest : RunFromLeft prog st' T' C' D' dst O Tleft Cleft Dleft) :
      RunFromLeft prog st T C D L O Tleft Cleft Dleft

-- Exact-consumption run: all supplied oracle streams are used by the path.
def RunFromAll (prog : Program) (st : IRState) (T : GasOracle) (C : CallStream) (D : CreateStream)
    (L : Label) (O : Observable) : Prop :=
  RunFromLeft prog st T C D L O [] [] []

theorem runFrom_of_runFromLeft {prog : Program} {st : IRState}
    {T Tleft : GasOracle} {C Cleft : CallStream} {D Dleft : CreateStream} {L : Label} {O : Observable}
    (h : RunFromLeft prog st T C D L O Tleft Cleft Dleft) : RunFrom prog st T C D L O := by
  induction h with
  | ret hb hss hterm hv => exact .ret hb hss hterm hv
  | stop hb hss hterm => exact .stop hb hss hterm
  | branchThen hb hss hterm hc hnz _hrest ih => exact .branchThen hb hss hterm hc hnz ih
  | branchElse hb hss hterm hc _hrest ih => exact .branchElse hb hss hterm hc ih
  | jump hb hss hterm _hrest ih => exact .jump hb hss hterm ih

theorem runFromLeft_exists {prog : Program} {st : IRState}
    {T : GasOracle} {C : CallStream} {D : CreateStream} {L : Label} {O : Observable}
    (h : RunFrom prog st T C D L O) :
    ∃ Tleft Cleft Dleft, RunFromLeft prog st T C D L O Tleft Cleft Dleft := by
  induction h with
  | ret hb hss hterm hv => exact ⟨_, _, _, .ret hb hss hterm hv⟩
  | stop hb hss hterm => exact ⟨_, _, _, .stop hb hss hterm⟩
  | branchThen hb hss hterm hc hnz _hrest ih =>
      obtain ⟨Tleft, Cleft, Dleft, hl⟩ := ih
      exact ⟨Tleft, Cleft, Dleft, .branchThen hb hss hterm hc hnz hl⟩
  | branchElse hb hss hterm hc _hrest ih =>
      obtain ⟨Tleft, Cleft, Dleft, hl⟩ := ih
      exact ⟨Tleft, Cleft, Dleft, .branchElse hb hss hterm hc hl⟩
  | jump hb hss hterm _hrest ih =>
      obtain ⟨Tleft, Cleft, Dleft, hl⟩ := ih
      exact ⟨Tleft, Cleft, Dleft, .jump hb hss hterm hl⟩

end Lir
