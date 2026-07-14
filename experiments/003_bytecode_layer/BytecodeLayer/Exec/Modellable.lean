import BytecodeLayer.Hoare.DriveRuns
import BytecodeLayer.Exec.Invariants

namespace BytecodeLayer.Interpreter

open Evm
open BytecodeLayer
open BytecodeLayer.Hoare

/-! ## §1 — the pure-semantics structural facts about `stepFrame`

`stepFrame` produces a `.needsCreate` / `.needsCall` signal *only* through the `dispatch (.System
s)` arm (`systemOp`), and within `systemOp` only the CREATE/CREATE2 arms (`createArm`) emit
`.needsCreate` and only the CALL-family arms (`callArm`) emit `.needsCall`. Everything else is
`continueWith` (`.next`), `charge`/`throw` (`.error` → `.halted`), or `haltOp` (`.halted`). These
two lemmas extract that, case-analysing the decoded op. -/

/-- The op `stepFrame` reads at `fr`'s current pc (with `decode`'s `STOP` default for an
out-of-range / undecodable pc). The quantity both structural lemmas case-split on. -/
def currentOp (fr : Frame) : Operation :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none)).1

/-! ### §1.0 — the combinator non-`needsCreate`/non-`needsCall` facts

Every non-`System` `dispatch` arm bottoms out in one of these `Step`-producing combinators (or an
explicit `do`-block of the same shape: a `charge`/`pop`/guard prefix then `continueWith` or
`throw`). None of them can return `.ok (.needsCreate …)` or `.ok (.needsCall …)` — `continueWith`
is `.ok (.next …)` and `throw` is `.error …`. We record the two negatives uniformly; `simp` closes
the `dispatch` case split with them. -/

/-- A `Step` that is `.ok` of a signal that is neither `.needsCall` nor `.needsCreate`. The shape
every non-`System` `dispatch` arm satisfies (its `.ok` outcomes are all `.next`). -/
def NoCallCreate : Step → Prop
  | .ok (.needsCall _ _)   => False
  | .ok (.needsCreate _ _) => False
  | _                      => True

@[simp] theorem noCallCreate_continueWith (exec : ExecutionState) :
    NoCallCreate (continueWith exec) := trivial

@[simp] theorem noCallCreate_error (e : ExecutionException) :
    NoCallCreate (.error e : Step) := trivial

theorem noCallCreate_bind {α : Type} (x : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, NoCallCreate (k a)) : NoCallCreate (x >>= k) := by
  cases x with
  | error e => exact trivial
  | ok a => exact hk a

/-- A lifted `Option` (via `MonadLift Option Except`), bound into a `NoCallCreate`-preserving
continuation, preserves `NoCallCreate`. The `pop`/`pop?` prefix every stack combinator opens with. -/
theorem noCallCreate_liftOption {α : Type} (x : Option α) (k : α → Step)
    (hk : ∀ a, NoCallCreate (k a)) : NoCallCreate ((x : Except ExecutionException α) >>= k) := by
  cases x with
  | none => exact trivial
  | some a => exact hk a

theorem noCallCreate_unOp (f : UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ) :
    NoCallCreate (unOp f exec cost) := by
  unfold unOp
  apply noCallCreate_bind; intro e
  apply noCallCreate_liftOption; intro r; exact trivial

theorem noCallCreate_binOp (f : UInt256 → UInt256 → UInt256) (exec : ExecutionState) (cost : ℕ) :
    NoCallCreate (binOp f exec cost) := by
  unfold binOp
  apply noCallCreate_bind; intro e
  apply noCallCreate_liftOption; intro r; exact trivial

theorem noCallCreate_ternOp (f : UInt256 → UInt256 → UInt256 → UInt256) (exec : ExecutionState)
    (cost : ℕ) : NoCallCreate (ternOp f exec cost) := by
  unfold ternOp
  apply noCallCreate_bind; intro e
  apply noCallCreate_liftOption; intro r; exact trivial

theorem noCallCreate_pushOp (v : ExecutionState → UInt256) (exec : ExecutionState) (cost : ℕ) :
    NoCallCreate (pushOp v exec cost) := by
  unfold pushOp
  apply noCallCreate_bind; intro e; exact trivial

theorem noCallCreate_unStateOp (f : Evm.State → UInt256 → Evm.State × UInt256)
    (cost : ExecutionState → UInt256 → ℕ) (exec : ExecutionState) :
    NoCallCreate (unStateOp f cost exec) := by
  unfold unStateOp
  apply noCallCreate_liftOption; intro r
  apply noCallCreate_bind; intro e; exact trivial

theorem noCallCreate_dup (n : ℕ) (exec : ExecutionState) : NoCallCreate (dup n exec) := by
  unfold dup
  apply noCallCreate_bind; intro e
  cases e.stack[n-1]? with
  | none => exact trivial
  | some v => exact trivial

theorem noCallCreate_swap (n : ℕ) (exec : ExecutionState) : NoCallCreate (swap n exec) := by
  unfold swap
  apply noCallCreate_bind; intro e
  dsimp only
  split <;> exact trivial

theorem noCallCreate_logArm (exec : ExecutionState) (stack : Stack UInt256) (offset size : UInt256)
    (topics : Array UInt256) : NoCallCreate (logArm exec stack offset size topics) := by
  unfold logArm
  apply noCallCreate_bind; intro _
  apply noCallCreate_bind; intro _
  apply noCallCreate_bind; intro _
  exact trivial

/-- `returnOrRevertOp` only ever halts (or errors). -/
theorem noCallCreate_returnOrRevertOp (op : Operation.SystemOp) (exec : ExecutionState) :
    NoCallCreate (returnOrRevertOp op exec) := by
  unfold returnOrRevertOp
  apply noCallCreate_liftOption; intro r
  apply noCallCreate_bind; intro e
  dsimp only
  split <;> exact trivial

/-- `selfdestructOp` only ever halts (or errors). -/
theorem noCallCreate_selfdestructOp (exec : ExecutionState) :
    NoCallCreate (selfdestructOp exec) := by
  unfold selfdestructOp
  apply noCallCreate_bind; intro _
  apply noCallCreate_liftOption; intro _
  apply noCallCreate_bind; intro _
  dsimp only
  split <;> exact trivial

/-- `haltOp` only ever halts (or errors): never `.needsCall`/`.needsCreate`. -/
theorem noCallCreate_haltOp (op : Operation.SystemOp) (exec : ExecutionState) :
    NoCallCreate (haltOp op exec) := by
  unfold haltOp
  cases op <;>
    first
      | exact trivial
      | exact noCallCreate_returnOrRevertOp _ exec
      | exact noCallCreate_selfdestructOp exec

/-! ### §1.1 — `callArm` never `.needsCreate` (the one-sided `NoCreate` algebra)

The CREATE arms of `systemOp` are the only ones that emit `.needsCreate`; the CALL-family arms run
`callArm`, which produces `.needsCall` (the descent) or `.next` (the failed/insufficient-funds
resume) — never `.needsCreate`. We mirror the `NoCallCreate` algebra one-sided as `NoCreate` (the
`.ok` outcome is never `.needsCreate`) and prove `callArm` satisfies it (`noCreate_callArm` below).
That, with `NoCallCreate` for the halt/smsf/combinator arms, routes `.needsCreate` to exactly the
CREATE/CREATE2 ops. -/

/-- A `Step` whose `.ok` outcome is never `.needsCreate` (it may be `.needsCall`/`.next`/`.halted`).
The invariant the CALL-family `systemOp` arms satisfy. -/
def NoCreate : Step → Prop
  | .ok (.needsCreate _ _) => False
  | _                      => True

theorem noCreate_bind {α : Type} (x : Except ExecutionException α) (k : α → Step)
    (hk : ∀ a, NoCreate (k a)) : NoCreate (x >>= k) := by
  cases x with
  | error e => exact trivial
  | ok a => exact hk a

theorem noCreate_liftOption {α : Type} (x : Option α) (k : α → Step)
    (hk : ∀ a, NoCreate (k a)) : NoCreate ((x : Except ExecutionException α) >>= k) := by
  cases x with
  | none => exact trivial
  | some a => exact hk a

/-- `smsfOp` never `.needsCall`/`.needsCreate`s: every `SmsfOp` arm bottoms out in
`continueWith`/`pushOp`/`unStateOp`/`charge`/`throw`. -/
theorem noCallCreate_smsfOp (op : Operation.SmsfOp) (fr : Frame) (exec : ExecutionState) :
    NoCallCreate (smsfOp op fr exec) := by
  unfold smsfOp
  cases op <;>
    first
      | exact noCallCreate_pushOp _ _ _
      | exact noCallCreate_unStateOp _ _ _
      | (dsimp only
         repeat' first
           | exact trivial
           | (apply noCallCreate_bind; intro _)
           | split)

/-! ### §1.2 — `systemOp` routes `.needsCreate` to CREATE/CREATE2

`systemOp` dispatches on the `SystemOp`: halt-family → `haltOp` (no create), CALL-family →
`callArm` (no create), CREATE/CREATE2 → `requireStateMod`/charges then `createArm`. So a
`.needsCreate` outcome forces `op ∈ {CREATE, CREATE2}`. -/

/-- `callArm` satisfies `NoCreate` (the `.ne` form, packaged for the `systemOp` split). -/
theorem noCreate_callArm (fr : Frame) (exec : ExecutionState) (stack : Stack UInt256)
    (gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) :
    NoCreate (callArm fr exec stack gas caller recipient codeAddress value apparentValue
      inOffset inSize outOffset outSize permission) := by
  unfold callArm
  split
  · apply noCreate_bind; intro _
    dsimp only
    apply noCreate_bind; intro _
    dsimp only
    split <;> exact trivial
  · exact trivial

/-- `NoCallCreate` (no `.needsCall` *and* no `.needsCreate`) is in particular `NoCreate`. -/
theorem NoCreate.of_noCallCreate {x : Step} (h : NoCallCreate x) : NoCreate x := by
  unfold NoCallCreate at h; unfold NoCreate
  split <;> first | exact h | trivial

/-- The hypothesis-free disjunction: each `systemOp` arm is either a CREATE/CREATE2 op or `NoCreate`
(its `.ok` outcome is never `.needsCreate`). The brick both `systemOp_needsCreate_isCreate` and the
`dispatch` lift consume. -/
theorem systemOp_isCreate_or_noCreate (s : Operation.SystemOp) (fr : Frame) (exec : ExecutionState) :
    (s = .CREATE ∨ s = .CREATE2) ∨ NoCreate (systemOp s fr exec) := by
  cases s with
  | CREATE => exact Or.inl (Or.inl rfl)
  | CREATE2 => exact Or.inl (Or.inr rfl)
  | STOP | RETURN | REVERT | SELFDESTRUCT | INVALID =>
    exact Or.inr (by unfold systemOp; exact NoCreate.of_noCallCreate (noCallCreate_haltOp _ exec))
  | CALL =>
    refine Or.inr ?_
    unfold systemOp; dsimp only
    apply noCreate_liftOption; intro _; dsimp only
    split
    · exact trivial
    · exact noCreate_callArm ..
  | CALLCODE =>
    refine Or.inr ?_
    unfold systemOp; dsimp only
    apply noCreate_liftOption; intro _; exact noCreate_callArm ..
  | DELEGATECALL =>
    refine Or.inr ?_
    unfold systemOp; dsimp only
    apply noCreate_liftOption; intro _; exact noCreate_callArm ..
  | STATICCALL =>
    refine Or.inr ?_
    unfold systemOp; dsimp only
    apply noCreate_liftOption; intro _; exact noCreate_callArm ..

theorem systemOp_needsCreate_isCreate {s : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {cp : CreateParams} {pending : PendingCreate}
    (h : systemOp s fr exec = .ok (.needsCreate cp pending)) :
    s = .CREATE ∨ s = .CREATE2 := by
  rcases systemOp_isCreate_or_noCreate s fr exec with hc | hnc
  · exact hc
  · exfalso; rw [h] at hnc; exact hnc

/-! ### §1.3 — `dispatch` and `stepFrame` route `.needsCreate` to a CREATE op

Lift the `systemOp` fact through `dispatch` (every non-`System` arm is a `NoCallCreate`
combinator) and then through `stepFrame` (whose only non-halt, non-error outcome *is* `dispatch`).
The conclusion is at the `currentOp` level: `stepFrame fr = .needsCreate …` forces the current op
to be `CREATE`/`CREATE2`. -/

theorem dispatch_needsCreate_isCreate {op : Operation} {arg : Option (UInt256 × UInt8)}
    {fr : Frame} {exec : ExecutionState} {cp : CreateParams} {pending : PendingCreate}
    (h : dispatch op arg fr exec = .ok (.needsCreate cp pending)) :
    op = .System .CREATE ∨ op = .System .CREATE2 := by
  -- each `dispatch` arm is either a CREATE/CREATE2 system op or `NoCreate`.
  have key : (op = .System .CREATE ∨ op = .System .CREATE2) ∨ NoCreate (dispatch op arg fr exec) := by
    unfold dispatch
    split
    · -- `.System s`: use the systemOp disjunction.
      rename_i s
      rcases systemOp_isCreate_or_noCreate s fr exec with (hs | hs) | hnc
      · exact Or.inl (Or.inl (by rw [hs]))
      · exact Or.inl (Or.inr (by rw [hs]))
      · exact Or.inr hnc
    -- every other arm is a `NoCreate` combinator (or an explicit `do`-block of that shape: a
    -- prefix of `pop`/`charge`/guards then `continueWith`/`throw`). Peel binds/lifts/ifs/matches.
    all_goals
      refine Or.inr ?_
      first
        | exact NoCreate.of_noCallCreate (noCallCreate_binOp _ _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_unOp _ _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_ternOp _ _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_pushOp _ _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_unStateOp _ _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_dup _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_swap _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_logArm _ _ _ _ _)
        | exact NoCreate.of_noCallCreate (noCallCreate_smsfOp _ _ _)
        | (dsimp only
           repeat' first
             | exact trivial
             | (apply noCreate_bind; intro _)
             | (dsimp only; split))
  rcases key with hc | hnc
  · exact hc
  · exfalso; rw [h] at hnc; exact hnc

/-- **`stepFrame` `.needsCreate` ⟹ current op is CREATE/CREATE2.** Lift `dispatch_needsCreate_
isCreate` through `stepFrame`: a `.needsCreate` outcome can only come from `stepFrame`'s `dispatch`
branch (the INVALID/overflow guards halt), and there it forces `currentOp fr ∈ {CREATE, CREATE2}`. -/
theorem stepFrame_needsCreate_isCreate {fr : Frame} {cp : CreateParams} {pending : PendingCreate}
    (h : stepFrame fr = .needsCreate cp pending) :
    currentOp fr = .System .CREATE ∨ currentOp fr = .System .CREATE2 := by
  -- expose the decoded op/arg and reduce `stepFrame` to its `dispatch` arm.
  unfold stepFrame at h
  set dec := decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none) with hdec
  -- `currentOp fr = dec.1`.
  have hco : currentOp fr = dec.1 := by rw [currentOp, ← hdec]
  rw [hco]
  -- peel `stepFrame`'s INVALID/overflow guards; only the `dispatch` `.ok` arm yields `.needsCreate`.
  simp only at h
  split at h
  · exact absurd h (by nofun)
  · split at h
    · exact absurd h (by nofun)
    · -- the `match dispatch … with | .ok s => s | .error _ => .halted` arm.
      cases hd : dispatch dec.1 dec.2 fr fr.exec with
      | error e => rw [hd] at h; exact absurd h (by nofun)
      | ok signal =>
        rw [hd] at h
        -- `signal = .needsCreate cp pending`.
        subst h
        exact dispatch_needsCreate_isCreate hd

/-! ## §2 — clause 2: `beginCall = .inr` ⟺ the call target is a precompile

`beginCall cp` is `.inr` (no code descent) exactly when `cp.codeSource = .Precompiled _`. In a
`.needsCall` produced by `callArm`, `cp.codeSource = toExecute accounts codeAddress` where
`codeAddress = AccountAddress.ofUInt256 toAddress` is the CALL **target taken off the stack at
runtime**, and `toExecute … = .Precompiled _` iff the target is a precompile address (`1..10`). So
clause 2 is genuinely a runtime fact about the call target, captured below as the residual. -/

/-- **`beginCall` is `.inr` exactly for a precompile code source.** The `beginCall` body branches
on `params.codeSource`: `.Precompiled _` returns `.inr`, `.Code _` returns `.inl`. So a non-
precompile code source rules out the `.inr` (precompile) outcome. -/
theorem beginCall_isCode_of_codeSource_ne_precompiled {cp : CallParams}
    (h : ∀ p, cp.codeSource ≠ .Precompiled p) : ∀ result, beginCall cp ≠ .inr result := by
  intro result
  unfold beginCall
  -- the trailing `match params.codeSource with | .Precompiled _ => .inr … | .Code _ => .inl …`.
  cases hcs : cp.codeSource with
  | Precompiled p => exact absurd hcs (h p)
  | Code code => intro hc; cases hc

/-! ## §3 — the per-frame `ModellableStep` reduction and reachable-run closure

`ModellableStep fr` reduces to two *per-frame, decode-level* facts:

* **clause 1** — every `.needsCreate` child run resumes successfully (`CreateResolves`);
* **clause 2** — every `.needsCall cp` that `fr` issues has a non-precompile code source
  (`beginCall_isCode_of_codeSource_ne_precompiled`: a non-precompile code source rules out the
  precompile `.inr`).

`modellableStep_of` packages exactly that reduction. The reachable-run closure then threads it
over every `Runs`-reachable frame when both facts hold at each frame. -/


/-- **`ModellableStep` from the two per-frame residuals.** A frame whose CREATEs resume
successfully (`CreateResolves`) and whose CALLs all target code (`CallsCode`) is `ModellableStep`:
the create clause is `CreateResolves` verbatim; the no-precompile-CALL clause is
`beginCall_isCode_of_codeSource_ne_precompiled` fed `CallsCode`. -/
theorem modellableStep_of {fr : Frame} (hcr : CreateResolves fr) (hcc : CallsCode fr) :
    ModellableStep fr := by
  refine ⟨hcr, ?_⟩
  -- clause 2: a `.needsCall` never begins as a precompile.
  intro cp pending result hstep
  exact beginCall_isCode_of_codeSource_ne_precompiled (hcc cp pending hstep) result

/-- If every frame reachable from `fr₀` satisfies `CreateResolves` and `CallsCode`, then every
reachable frame is `ModellableStep`. This packages the two runtime conditions required by the
`Runs` reconstruction. -/
theorem lower_modellable {fr₀ : Frame}
    (hcr : ∀ fr', Runs fr₀ fr' → CreateResolves fr')
    (hcc : ∀ fr', Runs fr₀ fr' → CallsCode fr') :
    ∀ fr', Runs fr₀ fr' → ModellableStep fr' :=
  fun fr' hr => modellableStep_of (hcr fr' hr) (hcc fr' hr)

end BytecodeLayer.Interpreter
