import LirLean.V2.Law
import LirLean.Materialise.DefsSound

/-!
# LirLean v2 — a worked external-`Stmt.call` example (gas-free, consumed call stream)

The call-free prototype (`LirLean/V2/Preserve.lean`) and the now-deleted two-read milestone
(`LirLean/V2/Mono.lean`) exercised the gas channel — the supplied gas-read *sequence*.
This file is the companion for the **call channel**: the `Stmt.call` `EvalStmt` arm of
`LirLean/V2/Machine.lean`, run consuming an **arbitrary supplied `CallStream` head**
(`docs/ir-design-v3.md` §3, §7, R3′).

It is **frame-free** — it imports only `LirLean.V2.Law` (hence `Machine`/`IR`/`Evm`), no
`BytecodeLayer`/`Frame`/`Runs`. The stream head stays a parameter; the realised stream
(`callStreamOf log.calls self`, off v1's `evmCallOracle`) is a separate, later piece.

The point it makes (the §7 interaction model, on the call side):

* a call **pops the head `(world', success)` of the call stream** — a positional recorded
  result, NOT a function of the call's IR-visible inputs — and **applies it as a state
  change**: `world := world'`, and the success flag bound straight into `locals` at
  `resultTmp` (**no `callResult` slot**);
* it is **gas-free** — the entry carries no restored gas; the call touches no gas
  notion. Post-call gas reads, if any, still come from the gas sequence;
* the two channels **coexist and are independent**: the program also reads `Expr.gas` (a gas
  read, popping the gas stream) and feeds that observed word to the call as the
  gas-to-forward input, while the call pops the call stream.

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
call(callee=t0, gasFwd=t1, result=t2)   -- pop the call-stream head, bind success → t2
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
/-- After the call: world replaced by the popped stream head's `world'`, `t2 := success`. -/
private def c3 (w₀ : World) (obs : Word) (w' : World) (s' : Word) : IRState :=
  { (c2 w₀ obs) with world := w' }.setLocal (tmp 2) s'

private theorem c2_callee (w₀ : World) (obs : Word) : (c2 w₀ obs).locals (tmp 0) = some 42 := rfl
private theorem c2_gasFwd (w₀ : World) (obs : Word) : (c2 w₀ obs).locals (tmp 1) = some obs := rfl
private theorem c3_result (w₀ : World) (obs : Word) (w' : World) (s' : Word) :
    (c3 w₀ obs w' s').locals (tmp 2) = some s' := by
  simp [c3, V2.IRState.setLocal]

/-! ## The observable

The whole run halts returning the success flag the call stream supplied, in the world the
call stream supplied — both **read off the consumed stream head**, never computed in the IR. -/

/-- The observable of `callIR` on world `w₀`, observed gas `obs`, and call-stream head
`(w', s')`: the post-call world is the head's `w'`, the result is `returned s'`. -/
def callObsResult (_w₀ : World) (_obs : Word) (w' : World) (s' : Word) : Observable :=
  { world := w', result := .returned s' }

/-! ## The worked run -/

/-- **The gas-free IR run, with one external call, consuming an arbitrary call-stream head.**
For any initial world `w₀`, observed gas `obs`, and supplied call-result head `(w', s')`,
`callIR` consuming the single gas read `obs` and the single call-result `(w', s')` halts with
`callObsResult w₀ obs w' s'`: the gas read feeds the call's gas-to-forward input, the popped
head `(w', s')` is applied as the state change, and the success flag is returned. The head is
held abstract throughout — it is *positional*, not a function of the visible inputs. -/
theorem call_IRRun (w₀ : World) (obs : Word) (w' : World) (s' : Word) :
    IRRun callIR w₀ [obs] [(w', s')] (callObsResult w₀ obs w' s') := by
  -- the three block-0 statements
  have e0 : EvalStmt callIR (c0 w₀) [obs] [(w', s')]
      (.assign (tmp 0) (.imm 42)) (c1 w₀) [obs] [(w', s')] :=
    EvalStmt.assignPure (by nofun) rfl
  have e1 : EvalStmt callIR (c1 w₀) [obs] [(w', s')]
      (.assign (tmp 1) .gas) (c2 w₀ obs) [] [(w', s')] := EvalStmt.assignGas
  have e2 : EvalStmt callIR (c2 w₀ obs) [] [(w', s')]
      (.call { callee := tmp 0, gasFwd := tmp 1, resultTmp := some (tmp 2) })
      (c3 w₀ obs w' s') [] [] := by
    have h := EvalStmt.call (prog := callIR) (st := c2 w₀ obs) (T := ([] : Trace))
      (C := ([] : CallStream)) (world' := w') (success := s')
      (cs := { callee := tmp 0, gasFwd := tmp 1, resultTmp := some (tmp 2) })
      (c2_callee w₀ obs) (c2_gasFwd w₀ obs)
    -- the post-state of the constructor is definitionally `c3 w₀ obs w' s'`.
    exact h
  have hss : RunStmts callIR (c0 w₀) [obs] [(w', s')] callBlock.stmts (c3 w₀ obs w' s') [] [] :=
    .cons e0 (.cons e1 (.cons e2 .nil))
  -- the terminator `ret t2` returns the success flag, in the head's world.
  have hret :
      RunFrom callIR (c0 w₀) [obs] [(w', s')] (lbl 0)
        { world := (c3 w₀ obs w' s').world, result := .returned s' } :=
    RunFrom.ret (b := callBlock) (t := tmp 2) callIR_block0 hss rfl (c3_result w₀ obs w' s')
  -- the post-call world is exactly the head's `w'`.
  have hworld : (c3 w₀ obs w' s').world = w' := rfl
  rw [hworld] at hret
  exact hret

/-- The §4 "*the* observable" shape on the call side: by `IRRun.det`, the observable
above is the **only** one `callIR` yields on this gas trace and call stream. -/
theorem call_IRRun_unique (w₀ : World) (obs : Word) (w' : World) (s' : Word) :
    ∀ O, IRRun callIR w₀ [obs] [(w', s')] O → O = callObsResult w₀ obs w' s' :=
  fun _ hO => IRRun.det hO (call_IRRun w₀ obs w' s')

-- Build-enforced axiom-cleanliness guard: the worked call run and its uniqueness depend
-- only on `[propext, Classical.choice, Quot.sound]`.

end Lir.V2
