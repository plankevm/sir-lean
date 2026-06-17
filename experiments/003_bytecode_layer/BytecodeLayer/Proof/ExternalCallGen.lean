import BytecodeLayer.Reasoning.Behaves
import BytecodeLayer.Reasoning.Drive
import BytecodeLayer.Observables
import BytecodeLayer.Programs
import BytecodeLayer.Proof.ExternalCall
import BytecodeLayer.Proof.Straightline

/-!
# Proof — the general external-call rung (rung 2): `behaves_call`

The concrete `messageCall_call_storageAt` is about *one* caller (`callerProg`)
calling *one* callee (`calleeProg`) in *one* world. Rung 2 makes the external
call **general over both programs**: for ANY callee characterized by its own
`Behaves` (under a callee precondition `calleePre`, e.g. "the forwarded gas
clears the SSTORE cost"), a caller that forwards a `CALL` to it gets the same
`completedWith a k v` named outcome — with the **63/64 `callGasCap` as the `∃G₀`
gas floor** that makes `calleePre` hold for the child.

## What is genuinely general here, and what the witness supplies

The driver `drive` is a single fuel-bounded recursion over a *flat* pending
stack, so there is no clean "this sub-tree is exactly a child `messageCall`"
decomposition to lean on generically — the parent and child interleave under one
fuel counter. So rung 2 takes a **per-entry
structural witness** about the caller (`CallerForwards`), and the theorem's own
content is the part that is genuinely program-agnostic:

* it **consumes the callee's `Behaves`** generically — the callee is a black box,
  named only by its code and its `calleePre`/`completedWith` contract;
* it threads the **gas floor `G₀`** so that `G₀ ≤ p.gas` forces `calleePre` on the
  child params the caller produces (this is where the 63/64 cap lives);
* it lands everything on the named `Outcome`, never a raw `.ok`.

The witness packages exactly the *caller-specific* facts the engine cannot know
generically: which child params `cp` the caller's `CALL` produces, that they run
`calleeCode` and satisfy `calleePre`, and that the caller **faithfully forwards**
a completed child's outcome to the top level
(`Outcome.ofCall (messageCall p) = Outcome.ofCall (messageCall cp)`). The
concrete `callerProg` instance discharges that witness from the existing
reflexive child-run reductions in `ExternalCall.lean`.

## The world must be constrained — `callerPre` is a genuine parameter

A subtlety the design's draft signature glossed: `Behaves` quantifies over **all**
worlds `p` running `callerCode`, but a caller only forwards to *this* callee when
the world actually places `calleeCode` at the called address. In an adversarial
world (different code at the target, or no account there) the call fails and the
cell is untouched — so a conclusion of the bare form `Behaves (fun p => G₀ ≤
p.gas) callerCode …` is simply **false** over all worlds (the `CallerForwards.hcode`
field cannot be supplied there). The honest, sound statement therefore keeps a
**caller precondition** `callerPre : World → Prop` (conjoined with the gas floor)
that pins the world enough for forwarding to hold; every other design decision is
unchanged — callee as its own `Behaves`, named `Outcome`, the `∃G₀` 63/64 floor,
gas first-class. The concrete instance supplies `callerPre p := ∃ g, p =
callerParams g`, recovering the original fixed-world `∃G₀ ∀g` theorem. -/

namespace BytecodeLayer.Proof
open Evm
open BytecodeLayer.System

/-! ## The per-entry caller-forwarding witness -/

/-- `CallerForwards callerCode calleeCode calleePre G₀ p`: the caller-specific
facts rung 2 needs for entry `p` (running `callerCode` with `G₀ ≤ p.gas`). It
names the child `CallParams cp` the caller's `CALL` descends into and asserts:

* **`hcode`** — `cp` runs the callee's real code (`calleeCode`), so the callee's
  own `Behaves` applies to it (no oracle: the child is a genuine `messageCall`);
* **`hpre`** — `cp` satisfies the callee precondition `calleePre`. This is the
  load-bearing gas fact: with `G₀ ≤ p.gas`, the 63/64 `callGasCap` forwards enough
  gas that `calleePre cp` holds (in the instance, `calleePre cp = 22106 ≤ cp.gas`
  via `childGas_lb`);
* **`hforward`** — IF the child completes leaving `v` at `(a, k)`, the **top-level**
  call also completes leaving `v` at `(a, k)`
  (`completedWith (ofCall (messageCall p)) a k v`). This is the faithful-forwarding
  fact the concrete reflexive child run establishes: in a completing run the caller
  carries the child's committed cell straight to the top-level observable and does
  no further write to `(a, k)`. Note this asks only that the *cell* survive, not
  that the whole `Outcome` (output bytes, full storage map) match — the caller may
  legitimately return different bytes or touch other cells.

The theorem feeds `cp` to the callee's `Behaves` to get `completedWith`, then
forwards it to the top level through `hforward`. -/
structure CallerForwards
    (calleeCode : ByteArray) (calleePre : World → Prop)
    (a : AccountAddress) (k v : UInt256) (p : World) where
  /-- The child `CallParams` the caller's `CALL` descends into. -/
  cp : CallParams
  /-- The child runs the callee's real code. -/
  hcode : cp.codeSource = .Code calleeCode
  /-- The forwarded gas clears the callee precondition (the 63/64-cap content). -/
  hpre : calleePre cp
  /-- A completed child forwards its `(a,k) = v` observable to the top level. -/
  hforward : Outcome.completedWith (Outcome.ofCall (messageCall cp)) a k v →
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v

/-! ## The general rung-2 theorem -/

/-- **Rung 2: the general external-call theorem (`behaves_call`).** For ANY callee
characterized by its own `Behaves calleePre calleeCode (completedWith … a k v)`, a
caller (`callerCode`) that forwards a `CALL` to it `Behaves` with the **same**
`completedWith a k v` named outcome, for every entry satisfying `callerPre` whose
gas clears a floor `G₀` — the floor being exactly the `∃G₀` the 63/64 `callGasCap`
forces.

The callee is consumed only through its `Behaves` (a black box). The caller is
supplied a per-entry `CallerForwards` witness; the theorem applies the callee's
`Behaves` to the witness's child params and rewrites the top-level outcome through
the forwarding equation. Gas stays first-class: `G₀ ≤ p.gas` is part of the `pre`,
and `CallerForwards` ties it to `calleePre cp` on the child. `callerPre` carries
whatever world constraint forwarding needs (see the module note); for the bare
"any world" reading take `callerPre := fun _ => True`. -/
theorem behaves_call
    (callerCode calleeCode : ByteArray)
    (callerPre calleePre : World → Prop)
    (a : AccountAddress) (k v : UInt256) (G₀ : ℕ)
    (hcallee : Behaves calleePre calleeCode (fun o => Outcome.completedWith o a k v))
    (W : ∀ p : World, p.codeSource = .Code callerCode → callerPre p → G₀ ≤ p.gas.toNat →
        CallerForwards calleeCode calleePre a k v p) :
    Behaves (fun p => callerPre p ∧ G₀ ≤ p.gas.toNat) callerCode
      (fun o => Outcome.completedWith o a k v) := by
  intro p hc hpre
  obtain ⟨hcaller, hgas⟩ := hpre
  -- The caller-forwarding witness for this entry.
  obtain ⟨cp, hcode, hprec, hforward⟩ := W p hc hcaller hgas
  -- The callee, as a black box, completes leaving `v` at `(a, k)`.
  have hchild : Outcome.completedWith (Outcome.ofCall (messageCall cp)) a k v :=
    hcallee cp hcode hprec
  -- The caller faithfully forwards that completed cell to the top level.
  exact hforward hchild

/-! ## Re-deriving the concrete external call as an instance

`messageCall_call_storageAt` (the original fixed-world `∃G₀ ∀g` theorem about
`callerProg` calling `calleeProg`) is now an **instance** of `behaves_call`: the
callee `calleeProg` is characterized by its own `Behaves`, and the caller supplies
a `CallerForwards` witness from the reflexive child run.
-/

/-- Decode a successful `.map`: `x.map f = .ok y` exposes the underlying `.ok r`. -/
theorem ok_of_map_ok {α β : Type} {x : Except ExecutionException α} {f : α → β} {y : β}
    (h : x.map f = .ok y) : ∃ r, x = .ok r ∧ f r = y := by
  cases x with
  | error e => simp [Except.map] at h
  | ok r => exact ⟨r, rfl, by simpa [Except.map] using h⟩

open Evm in
/-- A completed `.ok r` with `r.success` and cell `(a,k) = v` is `completedWith`. -/
theorem completedWith_of_ok {p : CallParams} {r : CallResult}
    {a : AccountAddress} {k v : UInt256}
    (hmc : messageCall p = .ok r) (hsucc : r.success = true)
    (hstore : CallResult.storageAt r a k = v) :
    Outcome.completedWith (Outcome.ofCall (messageCall p)) a k v := by
  refine ⟨r.output, CallResult.storageAt r, ?_, hstore⟩
  rw [ofCall_completed_of_success hmc hsucc]

/-- The callee precondition the instance uses: the child params are *exactly* the
ones the caller's `CALL` produces, with enough top-level gas (`30000 ≤ g`) that the
63/64 cap forwards ≥ `22106` to the callee. Pins the world to the genuine child run
(`callChildParams (callerCalled g) …`), so the callee `Behaves` is the reflexive
child-run fact `messageCall_child_reflexive`. -/
def calleeChildPre (cp : CallParams) : Prop :=
  ∃ g : UInt64, 30000 ≤ g.toNat ∧ cp = callChildParams (callerCalled g) 13242862 4294967295

/-- **The callee, characterized by its own `Behaves`.** `calleeProg`, run on the
child params the caller produces (with the 63/64-forwarded gas clearing its SSTORE
cost), completes leaving `5` at `(addrCallee, 7)`. This is exactly the reflexive
child-run fact, repackaged as a `Behaves` — the black box rung 2 consumes. -/
theorem behaves_callee :
    Behaves calleeChildPre calleeProg (fun o => Outcome.completedWith o addrCallee 7 5) := by
  intro cp _ hpre
  obtain ⟨g, hg, rfl⟩ := hpre
  -- The reflexive child run delivers `(success, cell) = (true, 5)`.
  obtain ⟨r, hmc, hpair⟩ := ok_of_map_ok (messageCall_child_reflexive g hg)
  have hsucc : r.success = true := (Prod.mk.inj hpair).1
  have hstore : CallResult.storageAt r addrCallee 7 = 5 := (Prod.mk.inj hpair).2
  exact completedWith_of_ok hmc hsucc hstore

/-- The caller precondition the instance uses: the world is one of the genuine
`callerParams g` entries. This is the world constraint forwarding needs (see the
module note); it recovers the original fixed-world theorem. -/
def callerParamsPre (p : CallParams) : Prop := ∃ g : UInt64, p = callerParams g

/-- **The `CallerForwards` witness for `callerProg`.** For an entry `p = callerParams g`
with `30000 ≤ g`, the child params are `callChildParams (callerCalled g) …`; they run
`calleeProg`, satisfy `calleeChildPre`, and the caller forwards the child's committed
cell to the top level — discharged from `messageCall_call_eq`/`final_obs`. -/
noncomputable def callerForwards_callerProg (p : CallParams)
    (_hc : p.codeSource = .Code callerProg) (hcaller : callerParamsPre p)
    (hgas : 30000 ≤ p.gas.toNat) :
    CallerForwards calleeProg calleeChildPre addrCallee 7 5 p := by
  -- `callerParamsPre` is a Prop `∃`; pick the witness `g` via choice.
  let g : UInt64 := hcaller.choose
  have hpg : p = callerParams g := hcaller.choose_spec
  have hg : 30000 ≤ g.toNat := by
    have hgg : p.gas = g := by rw [hpg]; rfl
    rw [hgg] at hgas; exact hgas
  refine
    { cp := callChildParams (callerCalled g) 13242862 4294967295
      hcode := ?_
      hpre := ⟨g, hg, rfl⟩
      hforward := ?_ }
  · -- the child's code source is the callee's real code
    show toExecute callerXfer (AccountAddress.ofUInt256 13242862) = ToExecute.Code calleeProg
    unfold toExecute; rw [if_neg (by decide)]; rfl
  · -- a completed child ⇒ the top-level caller completes with the same cell
    intro _hchild
    rw [hpg]
    refine completedWith_of_ok (messageCall_call_eq g hg) (callerResult_success g) ?_
    -- `callerResult g` is the `endFrame …` whose cell at `(addrCallee, 7)` is `5`
    exact final_obs g

/-- **`messageCall_call_storageAt` as a rung-2 instance.** Applying `behaves_call`
to `behaves_callee` and `callerForwards_callerProg`, then specializing the resulting
`Behaves` back to the fixed `callerParams g` world, reproduces the original
fixed-world `∃G₀ ∀g` storage theorem. -/
theorem messageCall_call_storageAt_via_behaves_call :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 := by
  have hbeh :
      Behaves (fun p => callerParamsPre p ∧ 30000 ≤ p.gas.toNat) callerProg
        (fun o => Outcome.completedWith o addrCallee 7 5) :=
    behaves_call callerProg calleeProg callerParamsPre calleeChildPre addrCallee 7 5 30000
      behaves_callee callerForwards_callerProg
  refine ⟨30000, fun g hg => ?_⟩
  -- specialize the general `Behaves` to the `callerParams g` world
  have hcw : Outcome.completedWith (Outcome.ofCall (messageCall (callerParams g))) addrCallee 7 5 :=
    hbeh (callerParams g) rfl ⟨⟨g, rfl⟩, hg⟩
  obtain ⟨out, σ, hco, hσ⟩ := hcw
  -- turn the named `completed` back into the raw `.ok r` storage observable
  rcases hmc : messageCall (callerParams g) with e | r
  · rw [hmc] at hco; simp [Outcome.ofCall] at hco
  · rw [hmc] at hco
    simp only [Outcome.ofCall, Outcome.ofResult] at hco
    split at hco
    · -- success: `completed r.output (storageAt r) = completed out σ`
      injection hco with hout hσeq
      simp only [Except.map]
      rw [show CallResult.storageAt r addrCallee 7 = σ addrCallee 7 from by rw [hσeq], hσ]
    · nomatch hco

end BytecodeLayer.Proof
