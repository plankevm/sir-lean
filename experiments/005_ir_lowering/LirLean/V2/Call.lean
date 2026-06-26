import LirLean.V2.Law
import LirLean.DefsSound

/-!
# LirLean v2 — a worked external-`Stmt.call` example (gas-free, abstract oracle)

The call-free prototype (`LirLean/V2/Preserve.lean`) and the two-read milestone
(`LirLean/V2/Mono.lean`) exercise the gas channel — the supplied gas-read *sequence*.
This file is the companion for the **call channel**: the `Stmt.call` `EvalStmt` arm of
`LirLean/V2/Machine.lean`, run under an **arbitrary abstract `CallOracle`**
(`docs/ir-design-v3.md` §3, §7).

It is **frame-free** — it imports only `LirLean.V2.Law` (hence `Machine`/`IR`/`Evm`), no
`BytecodeLayer`/`Frame`/`Runs`. The oracle stays a parameter; the v1 `evmCallOracle`
instantiation (the realisability witness) is a separate, later piece.

The point it makes (the §7 interaction model, on the call side):

* a call is a **function oracle** of the call's IR-visible inputs (here: callee address
  and gas-to-forward), queried at the call site, returning the `(world', success)`
  bundle the semantics **applies as a state change** — `world := world'`, and the success
  flag bound straight into `locals` at `resultTmp` (**no `callResult` slot**);
* it is **gas-free** — the bundle carries no restored gas; the call touches no gas
  notion. Post-call gas reads, if any, still come from the gas sequence;
* the two channels **coexist**: the program also reads `Expr.gas` (a gas read) and
  feeds that observed word to the call as the gas-to-forward input.

The example mirrors the prototype's `proto_IRRun` style — hand-assembled `EvalStmt`s
chained into a `RunStmts`, closed by a `RunFrom.ret`.
-/

namespace Lir.V2

open Evm

private def tmp (n : Nat) : Tmp := ⟨n⟩
private def lbl (n : Nat) : Label := ⟨n⟩

/-! ## The program

One block (the entry), with one external `Stmt.call`. In order:

```text
t0 := 42            -- the callee address (an immediate, for concreteness)
t1 := gas           -- gas-to-forward = the observed GAS value (a gas read)
call(callee=t0, gasFwd=t1, result=t2)   -- query the oracle, bind success → t2
ret t2              -- return the success flag
```

The `t1 := gas` / `call …` pair is the deliberate coexistence of the two channels: the
gas value travels through the supplied gas read, and is then handed to the call as
an ordinary IR-visible input. -/
def callBlock : Block :=
  { stmts :=
      [ .assign (tmp 0) (.imm 42)
      , .assign (tmp 1) .gas
      , .call { callee := tmp 0, gasFwd := tmp 1, resultTmp := some (tmp 2) } ]
    term := .ret (tmp 2) }

/-- The one-block program with one external call. Entry is block 0. -/
def callIR : Program := { blocks := #[callBlock], entry := lbl 0 }

/-- `WellFormed` sanity check (B3): the two non-recomputable tmps — the gas read `t1`
(used once, as the call's `gasFwd`) and the call-result `t2` (used once, as `ret t2`) —
are each used at most once. Discharged via the decidable surrogate `WellFormedDec`. -/
example : Lir.WellFormed callIR := Lir.wellFormed_of_dec (by decide)

private theorem callIR_block0 : blockAt callIR (lbl 0) = some callBlock := rfl

/-! ## The intermediate states (gas-free; only `locals`/`world` change) -/

/-- Start: empty locals, world `w₀`. -/
private def c0 (w₀ : World) : IRState := { locals := fun _ => none, world := w₀ }
/-- After `t0 := 42`. -/
private def c1 (w₀ : World) : IRState := (c0 w₀).setLocal (tmp 0) 42
/-- After `t1 := gas` (consumes the gas read `obs`; `t1 := obs`). -/
private def c2 (w₀ : World) (obs : Word) : IRState := (c1 w₀).setLocal (tmp 1) obs
/-- After the call: world replaced by the oracle's `world'`, `t2 := success`. -/
private def c3 (o : CallOracle) (w₀ : World) (obs : Word) : IRState :=
  match (o 42 obs w₀) with
  | (world', success) => { (c2 w₀ obs) with world := world' }.setLocal (tmp 2) success

private theorem c2_callee (w₀ : World) (obs : Word) : (c2 w₀ obs).locals (tmp 0) = some 42 := rfl
private theorem c2_gasFwd (w₀ : World) (obs : Word) : (c2 w₀ obs).locals (tmp 1) = some obs := rfl
private theorem c2_world (w₀ : World) (obs : Word) : (c2 w₀ obs).world = w₀ := rfl
private theorem c3_result (o : CallOracle) (w₀ : World) (obs : Word) :
    (c3 o w₀ obs).locals (tmp 2) = some (o 42 obs w₀).2 := by
  unfold c3; rw [show (o 42 obs w₀) = ((o 42 obs w₀).1, (o 42 obs w₀).2) from rfl]; rfl

/-! ## The observable

The whole run halts returning the success flag the oracle produced, in the world the
oracle produced — both **read off the oracle**, never computed in the IR. -/

/-- The observable of `callIR` under oracle `o`, world `w₀`, observed gas `obs`: the
post-call world is the oracle's `world'`, the result is `returned (success)`. -/
def callObsResult (o : CallOracle) (w₀ : World) (obs : Word) : Observable :=
  { world := (o 42 obs w₀).1, result := .returned (o 42 obs w₀).2 }

/-! ## The worked run -/

/-- **The gas-free IR run, with one external call, under an arbitrary oracle.** For any
oracle `o`, initial world `w₀` and observed gas `obs`, `callIR` consuming the single
gas read `obs` halts with `callObsResult o w₀ obs`: the gas read feeds the call's
gas-to-forward input, the oracle's `(world', success)` bundle is applied as the state
change, and the success flag is returned. The oracle is held abstract throughout. -/
theorem call_IRRun (o : CallOracle) (w₀ : World) (obs : Word) :
    IRRun callIR o w₀ [obs] (callObsResult o w₀ obs) := by
  -- the three block-0 statements
  have e0 : EvalStmt callIR o (c0 w₀) [obs]
      (.assign (tmp 0) (.imm 42)) (c1 w₀) [obs] :=
    EvalStmt.assignPure (by nofun) rfl
  have e1 : EvalStmt callIR o (c1 w₀) [obs]
      (.assign (tmp 1) .gas) (c2 w₀ obs) [] := EvalStmt.assignGas
  have e2 : EvalStmt callIR o (c2 w₀ obs) []
      (.call { callee := tmp 0, gasFwd := tmp 1, resultTmp := some (tmp 2) })
      (c3 o w₀ obs) [] := by
    have ho : o 42 obs (c2 w₀ obs).world = ((o 42 obs w₀).1, (o 42 obs w₀).2) := by
      rw [c2_world]
    have h := EvalStmt.call (prog := callIR) (o := o) (st := c2 w₀ obs) (T := [])
      (cs := { callee := tmp 0, gasFwd := tmp 1, resultTmp := some (tmp 2) })
      (c2_callee w₀ obs) (c2_gasFwd w₀ obs) ho
    -- the post-state of the constructor is definitionally `c3 o w₀ obs`
    have hpost :
        (match (some (tmp 2)) with
          | some t => { (c2 w₀ obs) with world := (o 42 obs w₀).1 }.setLocal t (o 42 obs w₀).2
          | none   => { (c2 w₀ obs) with world := (o 42 obs w₀).1 }) = c3 o w₀ obs := by
      unfold c3; rw [show (o 42 obs w₀) = ((o 42 obs w₀).1, (o 42 obs w₀).2) from rfl]
    rw [← hpost]; exact h
  have hss : RunStmts callIR o (c0 w₀) [obs] callBlock.stmts (c3 o w₀ obs) [] :=
    .cons e0 (.cons e1 (.cons e2 .nil))
  -- the terminator `ret t2` returns the success flag, in the oracle's world
  have hret :
      RunFrom callIR o (c0 w₀) [obs] (lbl 0)
        { world := (c3 o w₀ obs).world, result := .returned (o 42 obs w₀).2 } :=
    RunFrom.ret (b := callBlock) (t := tmp 2) callIR_block0 hss rfl (c3_result o w₀ obs)
  -- the post-call world is exactly the oracle's `world'`
  have hworld : (c3 o w₀ obs).world = (o 42 obs w₀).1 := by
    unfold c3; rw [show (o 42 obs w₀) = ((o 42 obs w₀).1, (o 42 obs w₀).2) from rfl]; rfl
  rw [hworld] at hret
  exact hret

/-- The §4 "*the* observable" shape on the call side: by `IRRun.det`, the observable
above is the **only** one `callIR` yields on this trace under `o`. -/
theorem call_IRRun_unique (o : CallOracle) (w₀ : World) (obs : Word) :
    ∀ O, IRRun callIR o w₀ [obs] O → O = callObsResult o w₀ obs :=
  fun _ hO => IRRun.det hO (call_IRRun o w₀ obs)

-- Build-enforced axiom-cleanliness guard: the worked call run and its uniqueness depend
-- only on `[propext, Classical.choice, Quot.sound]`.
#print axioms call_IRRun
#print axioms call_IRRun_unique

end Lir.V2
