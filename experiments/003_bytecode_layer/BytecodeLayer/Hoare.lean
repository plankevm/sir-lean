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

/-! ## The bundled `CallReturns` predicate

`CallReturns callFr resumeFr` bundles the facts of one external CALL that returns:
the CALL step (`stepFrame callFr = .needsCall cp pending`), the child entering as
code (`EntersAsCode cp child`), the child's **black-box** terminating run
(`drive (seedFuel cp.gas) [] (running child) = .ok childRes`), and the resumed
parent frame pinned to `resumeAfterCall childRes.toCallResult pending`. It is the
payload of the `Runs.call` constructor, so an external call that returns is a node
of a `Runs` path rather than a separate boundary theorem. -/

/-- `callFr` issues a CALL whose child runs to completion, resuming at `resumeFr`.

Bundles the four call-facts of the external-CALL sequence: the CALL step
(`stepFrame callFr = .needsCall cp pending`), the child entering as code
(`EntersAsCode cp child`), the child's black-box terminating run
(`drive (seedFuel cp.gas) [] (running child) = .ok childRes`), pinning the
resumed parent frame to `resumeAfterCall childRes.toCallResult pending`. -/
def CallReturns (callFr resumeFr : Frame) : Prop :=
  ∃ cp pending child childRes,
       stepFrame callFr = .needsCall cp pending
     ∧ EntersAsCode cp child
     ∧ drive (seedFuel cp.gas) [] (running child) = .ok childRes
     ∧ resumeFr = resumeAfterCall childRes.toCallResult pending

/-! ## The composition relation

`Runs fr fr'` is the reflexive–transitive closure of `StepsTo` **extended with an
external-CALL link**: a `call` step jumps from a CALL site `callFr` to the resumed
frame `resumeFr` whenever `CallReturns callFr resumeFr` holds. There is no longer
a `Nat` step-index — the boundary bridges discharge their fuel obligation by
never-out-of-fuel reconciliation (`Runs.drive_reconcile`), not by a numeric bound,
so an explicit step count carries no information. The intermediate frames (and the
whole descended child run) live inside the `Runs` derivation; they never surface
in a statement. -/

/-- **`Runs fr fr'`: `fr` reaches `fr'` by a run of non-halting opcode steps and
returning external calls.** The intermediate frames are the recursion of this
proof — they never surface in a statement. This is the single carrier the opcode
rules thread and the sequencing rule composes; external calls that return are
`call` nodes (see `CallReturns`), so a multi-call program is one `Runs` value. -/
inductive Runs : Frame → Frame → Prop where
  /-- Zero steps: a frame reaches itself. -/
  | refl (fr : Frame) : Runs fr fr
  /-- One opcode step `fr → mid`, then the rest of the block `mid → fr'`. -/
  | step {fr mid fr' : Frame} (h : StepsTo fr mid) (rest : Runs mid fr') :
      Runs fr fr'
  /-- An external CALL at `callFr` that returns, resuming at `resumeFr`
  (`CallReturns callFr resumeFr`), then the rest of the block `resumeFr → fr'`. -/
  | call {callFr resumeFr fr' : Frame} (hcall : CallReturns callFr resumeFr)
      (rest : Runs resumeFr fr') : Runs callFr fr'

/-- **The sequencing rule.** Compose a block `fr → mid` with the block that
follows it `mid → fr'` into one block `fr → fr'`. This is the whole point: a
program's `Runs` is built by gluing per-opcode `Runs`es (and returning-call nodes),
never by exhibiting the trace. -/
theorem Runs.trans {fr mid fr' : Frame}
    (h₁ : Runs fr mid) (h₂ : Runs mid fr') : Runs fr fr' := by
  induction h₁ with
  | refl _ => exact h₂
  | step hstep _ ih => exact Runs.step hstep (ih h₂)
  | call hcall _ ih => exact Runs.call hcall (ih h₂)

/-- A single opcode step is a one-instruction block. The atom the opcode rules
return. -/
theorem Runs.single {fr fr' : Frame} (h : StepsTo fr fr') : Runs fr fr' :=
  Runs.step h (Runs.refl fr')

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
    Runs fr (pushFrame fr imm) :=
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
    Runs fr (pushFrameW fr imm w) :=
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
    Runs fr (sstoreFrame fr key newValue rest) :=
  Runs.single (stepsTo_of_next (stepFrame_sstore fr key newValue rest hdec hstk hsz hmod hstip hcost))

/-! ## Arithmetic / storage-read / introspection rules (ADD / LT / SLOAD / GAS)

The pure-stack and storage-read bricks Track C's expression lowering threads. Each
is a one-step `Runs` to a named post-frame derived from the matching `Step.lean`
characterization, under purely semantic preconditions (decode, gas bound, stack
shape) — the same shape as `runs_push`/`runs_sstore`. SLOAD additionally carries a
**storage-read companion** (`sloadFrame_storage_self`) mirroring
`sstoreFrame_storage_self`: it exposes the pushed value through the same
`find?/lookupStorage` lens C3's storage `Match` uses. -/

/-- The frame after `ADD` (operands `a`/`b` popped off the top): `a + b` pushed onto
`rest`, pc + 1, `Gverylow` charged. -/
def addFrame (fr : Frame) (a b : UInt256) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.binOpPost fr.exec UInt256.add a b rest }

/-- The frame after `LT` (operands `a`/`b` popped off the top): `UInt256.lt a b`
(`= if a < b then 1 else 0`) pushed onto `rest`, pc + 1, `Gverylow` charged. -/
def ltFrame (fr : Frame) (a b : UInt256) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.binOpPost fr.exec UInt256.lt a b rest }

/-- The frame after `SLOAD` (key popped off the top): the self account's stored
value at `key` pushed onto `rest`, pc + 1, `sloadCost warm` charged, `(self, key)`
marked accessed. -/
def sloadFrame (fr : Frame) (key : UInt256) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.sloadPost fr.exec key rest }

/-- The frame after `GAS`: `ofUInt64` of the *post-charge* `gasAvailable` pushed,
pc + 1, `Gbase` charged. -/
def gasFrame (fr : Frame) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.gasPost fr.exec }

/-- **The ADD rule.** From a frame decoding to `ADD` with `a :: b :: rest` on the
stack, enough gas (`Gverylow`) and stack room, one step `Runs` to `addFrame fr a b
rest` (top = `a + b`). Pure `Step.lean` derivation. -/
theorem runs_add (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (addFrame fr a b rest) :=
  Runs.single (stepsTo_of_next (stepFrame_add fr a b rest hdec hstk hsz hgas))

/-- **The LT rule.** From a frame decoding to `LT` with `a :: b :: rest` on the
stack, enough gas (`Gverylow`) and stack room, one step `Runs` to `ltFrame fr a b
rest` (top = `UInt256.lt a b`, the boolean-as-word `a < b`). -/
theorem runs_lt (fr : Frame) (a b : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (ltFrame fr a b rest) :=
  Runs.single (stepsTo_of_next (stepFrame_lt fr a b rest hdec hstk hsz hgas))

/-- **The SLOAD rule.** From a frame decoding to `SLOAD` with `key :: rest` on the
stack and enough gas (`sloadCost warm`), one step `Runs` to `sloadFrame fr key rest`
(top = the self account's stored value at `key`). The `warm` flag is the
`accessedStorageKeys.contains (self, key)` membership the cost depends on. -/
theorem runs_sload (fr : Frame) (key : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (sloadFrame fr key rest) :=
  Runs.single (stepsTo_of_next (stepFrame_sload fr key rest hdec hstk hsz hgas))

/-- **The GAS rule.** From a frame decoding to `GAS` with enough gas (`Gbase`) and
stack room, one step `Runs` to `gasFrame fr` (top = `ofUInt64` of the *post-charge*
`gasAvailable`). -/
theorem runs_gas (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gasFrame fr) :=
  Runs.single (stepsTo_of_next (stepFrame_gas fr hdec hsz hgas))

/-- **SLOAD read companion** (mirrors `sstoreFrame_storage_self`). The value SLOAD
pushes — the head of `sloadFrame`'s resulting stack — is exactly the self account's
stored value at `key`, read through the same `find?/lookupStorage` lens C3's storage
`Match` uses. This connects the pushed word to the IR-level storage cell. -/
theorem sloadFrame_storage_self (fr : Frame) (key : UInt256) (rest : Stack UInt256) :
    (sloadFrame fr key rest).exec.stack.head?
      = some (fr.exec.accounts.find? fr.exec.executionEnv.address
          |>.option 0 (·.lookupStorage key)) := by
  show ((BytecodeLayer.Dispatch.sloadPost fr.exec key rest).stack).head? = _
  rfl

/-! ## POP (stack discard)

The stack-discard brick Track C's fire-and-forget (`resultTmp = none`) call tail
uses: one step that charges `Gbase`, drops the top operand and advances pc by one.
Built from `stepFrame_pop`; the same shape as `runs_gas` (no operand pushed). -/

/-- The frame after `POP` (top operand `v` popped off, leaving `rest`): `Gbase`
charged, pc + 1. -/
def popFrame (fr : Frame) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.popPost fr.exec rest }

/-- **The POP rule.** From a frame decoding to `POP` with `v :: rest` on the stack
and enough gas (`Gbase`), one step `Runs` to `popFrame fr rest` (top dropped,
leaving `rest`). Pure `Step.lean` derivation. -/
theorem runs_pop (fr : Frame) (v : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .POP, .none))
    (hstk : fr.exec.stack = v :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (popFrame fr rest) :=
  Runs.single (stepsTo_of_next (stepFrame_pop fr v rest hdec hstk hsz hgas))

/-! ## MSTORE / MLOAD (memory write / read)

The memory bricks Track C's value channel threads. Each is a one-step `Runs` to a
named post-frame derived from the matching `Step.lean` characterization, under
purely semantic preconditions (decode, stack shape, the memory-expansion witness
`hmem` pinning `words'`, and the two gas bounds). MLOAD additionally carries a
**value companion** (`mloadFrame_value`) exposing the pushed word as
`(toMachineState.mload addr).1`, mirroring `sloadFrame_storage_self`. The accessor
reductions (`mstoreFrame_*` / `mloadFrame_*`) mirror the `sstoreFrame_*` family so
later layers can read off the post-frame's code/pc/stack by `simp`. -/

/-- The frame after `MSTORE` (operands `addr`/`val` popped off the top): `val`
written at `addr` in memory, pc + 1, memory-expansion (to `words'`) + `Gverylow`
charged, via `mstorePost`. -/
def mstoreFrame (fr : Frame) (addr val : UInt256) (words' : UInt64) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.mstorePost fr.exec addr val words' rest }

/-- The frame after `MLOAD` (operand `addr` popped off the top): the loaded word
pushed onto `rest`, pc + 1, memory-expansion (to `words'`) + `Gverylow` charged, via
`mloadPost`. -/
def mloadFrame (fr : Frame) (addr : UInt256) (words' : UInt64) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.mloadPost fr.exec addr words' rest }

@[simp] theorem mstoreFrame_code (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mstoreFrame fr addr val words' rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem mstoreFrame_validJumps (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mstoreFrame fr addr val words' rest).validJumps = fr.validJumps := rfl

@[simp] theorem mstoreFrame_canMod (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mstoreFrame fr addr val words' rest).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem mstoreFrame_pc (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mstoreFrame fr addr val words' rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem mstoreFrame_stack (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mstoreFrame fr addr val words' rest).exec.stack = rest := rfl

@[simp] theorem mloadFrame_code (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mloadFrame fr addr words' rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem mloadFrame_validJumps (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mloadFrame fr addr words' rest).validJumps = fr.validJumps := rfl

@[simp] theorem mloadFrame_canMod (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mloadFrame fr addr words' rest).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem mloadFrame_pc (fr : Frame) (addr : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mloadFrame fr addr words' rest).exec.pc = fr.exec.pc + 1 := rfl

/-- **The MSTORE rule (effect).** From a frame decoding to `MSTORE` with
`addr :: val :: rest` on the stack, the memory-expansion witness `hmem` (pinning
`words'`) and enough gas for both charges, one step `Runs` to
`mstoreFrame fr addr val words' rest` (memory holds `val` at `addr`). -/
theorem runs_mstore (fr : Frame) (addr val : UInt256) (words' : UInt64) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words'
                ≤ fr.exec.gasAvailable.toNat)
    (hgas : GasConstants.Gverylow
              ≤ (fr.exec.gasAvailable
                  - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words')).toNat) :
    Runs fr (mstoreFrame fr addr val words' rest) :=
  Runs.single (stepsTo_of_next
    (stepFrame_mstore fr addr val words' rest hdec hstk hsz hmem hgasMem hgas))

/-- **The MLOAD rule (value).** From a frame decoding to `MLOAD` with `addr :: rest`
on the stack, the memory-expansion witness `hmem` (pinning `words'`) and enough gas
for both charges, one step `Runs` to `mloadFrame fr addr words' rest` (top = the
loaded word at `addr`). -/
theorem runs_mload (fr : Frame) (addr : UInt256) (words' : UInt64) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words'
                ≤ fr.exec.gasAvailable.toNat)
    (hgas : GasConstants.Gverylow
              ≤ (fr.exec.gasAvailable
                  - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words')).toNat) :
    Runs fr (mloadFrame fr addr words' rest) :=
  Runs.single (stepsTo_of_next
    (stepFrame_mload fr addr words' rest hdec hstk hsz hmem hgasMem hgas))

/-- **MLOAD value companion** (mirrors `sloadFrame_storage_self`). The value MLOAD
pushes — the head of `mloadFrame`'s resulting stack — is exactly the word read from
memory at `addr` (`(toMachineState.mload addr).1`, on the doubly-charged state). The
charges touch only `gasAvailable`, so this is the value read from `fr`'s memory. -/
theorem mloadFrame_value (fr : Frame) (addr : UInt256) (words' : UInt64) (rest : Stack UInt256) :
    (mloadFrame fr addr words' rest).exec.stack.head?
      = some ((BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mload addr).1 := by
  show ((BytecodeLayer.Dispatch.mloadPost fr.exec addr words' rest).stack).head? = _
  rfl

/-- **MSTORE memory effect.** The machine state `mstoreFrame` leaves is exactly
`fr`'s machine state (on the doubly-charged state) with `val` written at `addr`
(`mstore addr val`) — the read-back a later MLOAD lemma consumes. -/
theorem mstoreFrame_memory (fr : Frame) (addr val : UInt256) (words' : UInt64)
    (rest : Stack UInt256) :
    (mstoreFrame fr addr val words' rest).exec.toMachineState
      = (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mstore addr val := rfl

/-! ## Control-flow rules (JUMP / JUMPI) — the CFG combinator

The conditional/unconditional jumps lift the `Step.lean` jump lemmas to `Runs`.
Each is a one-step `Runs` to a post-frame whose `exec` is the jump's result
(`jumpPost`/`jumpiFallthroughPost`); the only difference from PUSH/SSTORE is that
the post-frame moves `pc` to a resolved destination rather than `pc + width`.

- `runs_jump` — unconditional jump to a valid destination (`fr.get_dest dest =
  some new_pc`).
- `runs_jumpi_taken` — conditional jump with a non-zero condition, to a valid
  destination.
- `runs_jumpi_fallthrough` — conditional jump with a zero condition, falling
  through to `pc + 1`.

A program with a conditional branch is then assembled by *case-splitting on the
branch condition* and threading the matching rule into `Runs.trans` — see
`runs_branch` below, the branching reasoning helper. Loops (back-edges) need no
extra theory: a `Runs` already expresses any finite trace, so a `runs_jump` back
to an earlier `pc` is just another `Runs` node glued by `Runs.trans`. -/

/-- The frame after JUMP / a taken JUMPI: `exec` is `jumpPost` (gas charged by
`cost`, `pc := new_pc`, operands popped to `rest`); `kind`/`validJumps` unchanged. -/
def jumpFrame (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.jumpPost fr.exec cost new_pc rest }

/-- The frame after a not-taken JUMPI: `exec` is `jumpiFallthroughPost` (gas
charged `Ghigh`, `pc := pc + 1`, operands popped to `rest`). -/
def jumpiFallthroughFrame (fr : Frame) (rest : Stack UInt256) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.jumpiFallthroughPost fr.exec rest }

/-- **The JUMP rule.** From a frame decoding to `JUMP` with `dest :: rest` on the
stack, enough gas (`Gmid`), and `dest` a valid jump destination
(`fr.get_dest dest = some new_pc`), one step `Runs` to `jumpFrame fr Gmid new_pc
rest` (pc set to `new_pc`). Pure `Step.lean` derivation. -/
theorem runs_jump (fr : Frame) (dest : UInt256) (new_pc : UInt32) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMP, .none))
    (hstk : fr.exec.stack = dest :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gmid ≤ fr.exec.gasAvailable.toNat)
    (hdest : fr.get_dest dest = some new_pc) :
    Runs fr (jumpFrame fr GasConstants.Gmid new_pc rest) :=
  Runs.single (stepsTo_of_next (stepFrame_jump fr dest new_pc rest hdec hstk hsz hgas hdest))

/-- **The JUMPI rule (taken).** From a frame decoding to `JUMPI` with
`dest :: cond :: rest`, a non-zero `cond`, enough gas (`Ghigh`), and `dest` a
valid jump destination, one step `Runs` to `jumpFrame fr Ghigh new_pc rest`
(pc set to `new_pc`). -/
theorem runs_jumpi_taken (fr : Frame) (dest cond : UInt256) (new_pc : UInt32)
    (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: cond :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Ghigh ≤ fr.exec.gasAvailable.toNat)
    (hcond : cond ≠ 0)
    (hdest : fr.get_dest dest = some new_pc) :
    Runs fr (jumpFrame fr GasConstants.Ghigh new_pc rest) :=
  Runs.single (stepsTo_of_next
    (stepFrame_jumpi_taken fr dest cond new_pc rest hdec hstk hsz hgas hcond hdest))

/-- **The JUMPI rule (fall-through).** From a frame decoding to `JUMPI` with
`dest :: 0 :: rest` (zero condition) and enough gas (`Ghigh`), one step `Runs` to
`jumpiFallthroughFrame fr rest` (pc advanced by one). No destination requirement —
the jump is not taken. -/
theorem runs_jumpi_fallthrough (fr : Frame) (dest : UInt256) (rest : Stack UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: (0 : UInt256) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Ghigh ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (jumpiFallthroughFrame fr rest) :=
  Runs.single (stepsTo_of_next
    (stepFrame_jumpi_fallthrough fr dest rest hdec hstk hsz hgas))

/-- The frame after JUMPDEST: `exec` is `jumpdestPost` (gas charged `Gjumpdest`,
pc advanced by one). The no-op landing pad a taken jump steps past. -/
def jumpdestFrame (fr : Frame) : Frame :=
  { fr with exec := BytecodeLayer.Dispatch.jumpdestPost fr.exec }

/-- **The JUMPDEST rule.** From a frame decoding to `JUMPDEST` with enough gas
(`Gjumpdest`), one step `Runs` to `jumpdestFrame fr` (pc advanced by one, stack
unchanged). Lets a taken jump step past its target landing pad. -/
theorem runs_jumpdest (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gjumpdest ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (jumpdestFrame fr) :=
  Runs.single (stepsTo_of_next (stepFrame_jumpdest fr hdec hsz hgas))

/-! ### The branching reasoning helper

A conditional branch is reasoned about by *case-splitting on the runtime value of
the branch condition* and supplying, for each side, the `Runs` that the JUMPI
takes from there. `runs_branch` packages exactly that: given the JUMPI frame, the
`Runs` continuation for the taken side (from the destination frame) and for the
fall-through side (from `pc + 1`), it produces the single `Runs fr fr'` for the
whole `if`. The caller no longer threads the JUMPI step by hand — it just hands
over the two branch continuations and a decision about the condition.

`hcond_dec` lets the caller decide the condition: it returns either the taken
witness (`cond ≠ 0` together with the resolved destination) or the fall-through
witness (`cond = 0`). This keeps the combinator usable both when the condition is
statically known and when it is only known to be one of the two cases. -/

/-- **The conditional-branch combinator.** A JUMPI at `fr` (decoding to `JUMPI`,
stack `dest :: cond :: rest`, gas/overflow OK) composes into one `Runs fr fr'`
once the caller supplies, for whichever branch the condition selects, the `Runs`
that continues from there:

* taken side: `cond ≠ 0`, `fr.get_dest dest = some new_pc`, and a
  `Runs (jumpFrame fr Ghigh new_pc rest) fr'`;
* fall-through side: `cond = 0` and a `Runs (jumpiFallthroughFrame fr rest) fr'`.

The decision between the two is the caller's `branch` value. This is the building
block Track C's branch lowering threads through `Runs.trans` like straight-line
code. -/
theorem runs_branch {fr fr' : Frame} {dest cond : UInt256} {rest : Stack UInt256}
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .JUMPI, .none))
    (hstk : fr.exec.stack = dest :: cond :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Ghigh ≤ fr.exec.gasAvailable.toNat)
    (branch :
      (∃ new_pc, cond ≠ 0 ∧ fr.get_dest dest = some new_pc
        ∧ Runs (jumpFrame fr GasConstants.Ghigh new_pc rest) fr')
      ∨ (cond = 0 ∧ Runs (jumpiFallthroughFrame fr rest) fr')) :
    Runs fr fr' := by
  rcases branch with ⟨new_pc, hcond, hdest, htaken⟩ | ⟨hcond, hfall⟩
  · exact (runs_jumpi_taken fr dest cond new_pc rest hdec hstk hsz hgas hcond hdest).trans htaken
  · subst hcond
    exact (runs_jumpi_fallthrough fr dest rest hdec hstk hsz hgas).trans hfall

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
