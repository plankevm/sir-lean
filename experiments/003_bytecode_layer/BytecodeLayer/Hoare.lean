import BytecodeLayer.Semantics.Dispatch
import BytecodeLayer.Semantics.Interpreter.Drive
import BytecodeLayer.Semantics.System
import BytecodeLayer.Semantics.Maps
import BytecodeLayer.Observables

/-!
# A thin Hoare-style composition layer for non-branching blocks

A straight-line engine could run a block once you hand it the *whole* list of
intermediate frames. That list is exactly the execution trace, and writing it out
— `sstoreF1`, `sstoreF2`, … with their gas arithmetic — is the per-program pain
this file removes.

The idea here is to never name a trace. We introduce one relation,

  `Runs fr fr'`  :=  "`fr` reaches `fr'` by some run of non-halting steps",

as the reflexive–transitive closure of `StepsTo`. The chain of frames lives
*inside* the `Runs` proof (in the inductive's recursion), never in any
statement or hypothesis. Composition is `Runs.trans` — the **sequencing rule**:
glue "one opcode step" onto "the rest of the block". Each opcode rule is a
`Runs`-producing lemma derived from the `Step.lean` characterizations; the
SSTORE rule additionally carries a **framing** clause (what storage it leaves
untouched).

`Runs` mentions `Frame` and so is an internal brick (like `StepsTo`); it never
appears in an exported statement. The boundary bridge `messageCall_runs_completed`
turns a `Runs … halt` into a high-level `Outcome` — observables and queryable
storage only.
-/

namespace BytecodeLayer.Hoare
open Evm
open GasConstants
open BytecodeLayer.Maps
open BytecodeLayer.Dispatch
open BytecodeLayer.Interpreter
open BytecodeLayer.System

/-! ## The single-step primitive

`StepsTo fr fr'` is the atom everything is built on: one non-halting `stepFrame`
carries `fr` to `fr'`, which keeps `fr`'s `kind`/`validJumps` and only moves
`exec` forward. `drive_stepsTo` connects it to the fuel-level driver. These are
fuel-level bricks (they mention `Frame`, `drive`, fuel); they never appear in an
exported statement. -/

/-- **One non-halting step.** `stepFrame fr` advances to `fr'`, which keeps `fr`'s
`kind`/`validJumps` and only moves `exec` forward. The atom `Runs` is the closure
of. -/
def StepsTo (fr fr' : Frame) : Prop :=
  stepFrame fr = Signal.next fr'.exec ∧ fr' = { fr with exec := fr'.exec }

/-- `StepsTo` preserves the frame `kind` (only `exec` advances). -/
theorem StepsTo.kind_eq {fr fr' : Frame} (h : StepsTo fr fr') : fr'.kind = fr.kind := by
  rw [h.2]

/-- **Build a `StepsTo` from a `.next` step.** `stepFrame fr = .next e` gives a
`StepsTo fr { fr with exec := e }` — the successor frame is `fr` with `exec`
replaced by `e`. The one constructor the opcode rules feed each `Step` lemma
into. -/
theorem stepsTo_of_next {fr : Frame} {e : ExecutionState} (h : stepFrame fr = Signal.next e) :
    StepsTo fr { fr with exec := e } := ⟨h, rfl⟩

/-- A single `StepsTo` is exactly one `drive` step at the top level: `drive`
spends one fuel and re-enters on `fr'`. -/
theorem drive_stepsTo (n : ℕ) {fr fr' : Frame} (h : StepsTo fr fr') :
    drive (n + 1) [] (running fr) = drive n [] (running fr') := by
  obtain ⟨hstep, hfr'⟩ := h
  rw [drive_step n fr fr'.exec hstep]
  rw [← hfr']

/-! ## The composition relation

`Runs n fr fr'` is the reflexive–transitive closure of `StepsTo`, indexed by the
**number of opcode steps** `n`. The index is a plain `Nat`, not a trace: it lets
the boundary bridge phrase its fuel obligation as a numeric bound (`n + 2 ≤
seedFuel`) without ever naming an intermediate frame. The frames themselves live
inside the `Runs` derivation. -/

/-- **`Runs n fr fr'`: `fr` reaches `fr'` by exactly `n` non-halting opcode
steps.** The intermediate frames are the recursion of this proof — they never
surface in a statement. This is the single carrier the opcode rules thread and
the sequencing rule composes. -/
inductive Runs : ℕ → Frame → Frame → Prop where
  /-- Zero steps: a frame reaches itself. -/
  | refl (fr : Frame) : Runs 0 fr fr
  /-- One opcode step `fr → mid`, then the rest of the block `mid → fr'`. -/
  | head {n : ℕ} {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs n mid fr') :
      Runs (n + 1) fr fr'

/-- **The sequencing rule.** Compose a block `fr → mid` (`m` steps) with the block
that follows it `mid → fr'` (`n` steps) into one block `fr → fr'` (`m + n`
steps). This is the whole point: a program's `Runs` is built by gluing per-opcode
`Runs`es, never by exhibiting the trace. -/
theorem Runs.trans {m n : ℕ} {fr mid fr' : Frame}
    (h₁ : Runs m fr mid) (h₂ : Runs n mid fr') : Runs (m + n) fr fr' := by
  induction h₁ with
  | refl _ => simpa using h₂
  | @head k a b c hstep _ ih =>
    rw [show k + 1 + n = (k + n) + 1 by omega]
    exact Runs.head hstep (ih h₂)

/-- A single opcode step is a one-instruction block. The atom the opcode rules
return. -/
theorem Runs.single {fr fr' : Frame} (h : StepsTo fr fr') : Runs 1 fr fr' :=
  Runs.head h (Runs.refl fr')

/-! ## The `messageCall` boundary bridge

`messageCall_runs` turns a `Runs n fr₀ last` whose `last` halts into a
`messageCall` result, driving the block under the interpreter by induction on the
`Runs` derivation. No list of frames is ever materialized: the bridge consumes
the `Runs` proof directly. The fuel obligation is the numeric `n + 2 ≤ seedFuel`. -/

/-- A `Runs n` block, run under the driver from the empty pending stack, advances
the driver from `fr` to `last` while spending exactly `n` fuel — for any spare
`extra`. Proved by induction on the `Runs` derivation (the trace is the
recursion); reuses `drive_stepsTo` for each link. -/
theorem Runs.drive_advance {n : ℕ} {fr last : Frame} (h : Runs n fr last) (extra : ℕ) :
    drive (n + extra) [] (running fr) = drive extra [] (running last) := by
  induction h with
  | refl _ => rw [Nat.zero_add]
  | @head k a b c hstep _ ih =>
    rw [show k + 1 + extra = (k + extra) + 1 by omega]
    rw [drive_stepsTo (k + extra) hstep]
    exact ih

/-- **A `Runs` block at the `messageCall` boundary, halting.** If a code call's
initial frame `fr₀` (`EntersAsCode p fr₀`) `Runs` to a frame `last` that halts
with `halt`, then `messageCall p = .ok (toCallResult (endFrame last halt))`. The
fuel obligation is the numeric bound `n + 2 ≤ seedFuel p.gas` — no trace.

This is the boundary; from here up, statements are observable-only. -/
theorem messageCall_runs {n : ℕ} {fr₀ last : Frame} {halt : FrameHalt} (p : CallParams)
    (hbegin : EntersAsCode p fr₀)
    (h : Runs n fr₀ last)
    (hhalt : stepFrame last = Signal.halted halt)
    (hfuel : n + 2 ≤ seedFuel p.gas) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) := by
  rw [messageCall_eq_drive p fr₀ hbegin]
  rw [show seedFuel p.gas = n + (seedFuel p.gas - n) by omega]
  rw [h.drive_advance (seedFuel p.gas - n)]
  rw [show seedFuel p.gas - n = (seedFuel p.gas - n - 2) + 2 by omega]
  rw [drive_halt (seedFuel p.gas - n - 2) last halt hhalt]
  rfl

/-! ## Opcode rules

Each opcode rule is a `Runs 1` lemma: under purely **semantic** preconditions
(decode, gas bound, stack shape) it advances one frame, deriving the post-frame
from the corresponding `Step.lean` characterization. The post-frame is named by a
transformer (`pushFrame`, `sstoreFrame`) so the next rule consumes it and
composition by `Runs.trans` threads the symbolic state without ever exhibiting a
trace.

These mention `Frame`/`ExecutionState` and so are internal bricks; observable
statements appear only at the `messageCall_runs` boundary and above. -/

/-- The frame after `PUSH1 imm`: `imm` pushed, pc + 2, `Gverylow` charged. -/
def pushFrame (fr : Frame) (imm : UInt256) : Frame :=
  { fr with exec :=
      ({ fr.exec with gasAvailable := fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
        ).replaceStackAndIncrPC (fr.exec.stack.push imm) (pcΔ := 2) }

/-- The frame after a generic `PUSH<w>`: `imm` pushed, pc + `w+1`, `Gverylow`
charged. Generalizes `pushFrame` (which fixes `w = 1`) to the multi-byte pushes. -/
def pushFrameW (fr : Frame) (imm : UInt256) (w : UInt8) : Frame :=
  { fr with exec :=
      ({ fr.exec with gasAvailable := fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gverylow }
        ).replaceStackAndIncrPC (fr.exec.stack.push imm) (pcΔ := w + 1) }

/-- The frame after `SSTORE` writing `newValue` at `key` (operands popped off the
top of the stack), via `sstorePost`. -/
def sstoreFrame (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256) : Frame :=
  { fr with exec := sstorePost fr.exec key newValue rest }

/-- **The PUSH1 rule.** From a frame decoding to `PUSH1 imm` with gas and stack
room, one step `Runs` to `pushFrame fr imm`. Pure `Step.lean` derivation. -/
theorem runs_push1 (fr : Frame) (imm : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH1, some (imm, 1)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs 1 fr (pushFrame fr imm) :=
  Runs.single (stepsTo_of_next (stepFrame_push1 fr imm hdec hgas hstk))

/-- **The general PUSH rule (any width).** From a frame decoding to `PUSH<w> imm`
(any push opcode `op ≠ PUSH0`) with gas and stack room, one step `Runs` to
`pushFrameW fr imm w`. Built from the general `stepFrame_push`; `runs_push1` is the
`w = 1` special case. The caller supplies the pop/push counts (`δ = 0`, `α = 1`,
shared by every PUSH). -/
theorem runs_push (fr : Frame) (op : Operation.PushOp) (imm : UInt256) (w : UInt8)
    (hp0 : op ≠ .PUSH0)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push op, some (imm, w)))
    (hpop : stackPopCount (.Push op) = 0) (hpush : stackPushCount (.Push op) = 1)
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs 1 fr (pushFrameW fr imm w) :=
  Runs.single (stepsTo_of_next (stepFrame_push fr op imm w hp0 hdec hpop hpush hgas hstk))

/-- **The SSTORE rule (effect).** From a frame decoding to `SSTORE` with
`key :: newValue :: rest` on the stack, in a state-modifying context with enough
gas, one step `Runs` to `sstoreFrame fr key newValue rest`. -/
theorem runs_sstore (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: newValue :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key newValue ≤ fr.exec.gasAvailable.toNat) :
    Runs 1 fr (sstoreFrame fr key newValue rest) :=
  Runs.single (stepsTo_of_next (stepFrame_sstore fr key newValue rest hdec hstk hsz hmod hstip hcost))

/-! ### Storage effect and framing of `sstoreFrame`

The SSTORE rule's two halves at the **observable** level: reading the resulting
account map's storage. `storage_self` gives the *effect* (the written cell holds
the value); `storage_frame` gives the *frame* (any other cell, in any account, is
unchanged). Both are stated through the same `find?/lookupStorage` lens the
`Observables` use. The self address is `fr.exec.executionEnv.address`. -/

/-- The account map left by `sstoreFrame` is `fr`'s account map with the self
account's storage updated at `key` — provided the self account is present. -/
theorem sstoreFrame_accounts (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc) :
    (sstoreFrame fr key newValue rest).exec.accounts
      = fr.exec.accounts.insert fr.exec.executionEnv.address (acc.updateStorage key newValue) := by
  show (sstorePost fr.exec key newValue rest).accounts = _
  show (Evm.State.sstore _ key newValue).accounts = _
  unfold Evm.State.sstore
  simp only [Evm.State.lookupAccount, hself, Option.option]
  rfl

/-- **SSTORE effect.** After `sstoreFrame` (writing a *non-zero* `newValue`),
reading the self account's storage at `key` returns `newValue`. -/
theorem sstoreFrame_storage_self (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (hnz : newValue ≠ 0) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? fr.exec.executionEnv.address
      |>.option 0 (·.lookupStorage key)) = newValue := by
  rw [sstoreFrame_accounts fr key newValue rest acc hself]
  rw [accounts_find?_insert_self]
  show (acc.updateStorage key newValue).lookupStorage key = newValue
  unfold Account.updateStorage Account.lookupStorage
  rw [if_neg (by
    show ¬ ((newValue == (default : UInt256)) = true)
    rw [show (default : UInt256) = 0 from rfl]
    intro hc; exact hnz ((UInt256.beq_iff_eq newValue 0).mp hc))]
  exact storage_findD_insert_self _ _ _ _

/-- **SSTORE framing.** After `sstoreFrame`, reading **any other** cell `(a', k')`
— a different account, or the same account at a different slot — returns exactly
what `fr` held there. This is the frame clause: the write touches only `(self,
key)`. -/
theorem sstoreFrame_storage_frame (fr : Frame) (key newValue : UInt256) (rest : Stack UInt256)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (hnz : newValue ≠ 0)
    (a' : AccountAddress) (k' : UInt256)
    (hframe : a' ≠ fr.exec.executionEnv.address ∨ k' ≠ key) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? a' |>.option 0 (·.lookupStorage k'))
      = (fr.exec.accounts.find? a' |>.option 0 (·.lookupStorage k')) := by
  rw [sstoreFrame_accounts fr key newValue rest acc hself]
  rcases hframe with ha | hk
  · -- different account: the insert doesn't change `find? a'`
    rw [accounts_find?_insert_of_ne _ _ ha]
  · -- same account possible, different slot: account read may change, slot read does not
    by_cases ha : a' = fr.exec.executionEnv.address
    · subst ha
      rw [accounts_find?_insert_self, hself]
      show (acc.updateStorage key newValue).lookupStorage k' = acc.lookupStorage k'
      unfold Account.updateStorage Account.lookupStorage
      rw [if_neg (by
    show ¬ ((newValue == (default : UInt256)) = true)
    rw [show (default : UInt256) = 0 from rfl]
    intro hc; exact hnz ((UInt256.beq_iff_eq newValue 0).mp hc))]
      exact storage_findD_insert_of_ne _ _ _ hk
    · rw [accounts_find?_insert_of_ne _ _ ha]

end BytecodeLayer.Hoare
