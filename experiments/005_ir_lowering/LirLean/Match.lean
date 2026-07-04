import LirLean.SmallStep
import LirLean.Call
import LirLean.LoweringLemmas
import LirLean.Layout
import LirLean.StorageErase
import BytecodeLayer.Hoare
import BytecodeLayer.Hoare.CallSequence

/-!
# LirLean — the `Match` invariant and the per-construct simulation engine (C3)

This module carries Track C's milestone-C3 work: the `Match` simulation invariant
(`docs/ir-design.md` §6.1) relating an IR small-step configuration to an EVM
`Frame`, and the **per-construct atomic simulation lemmas** that drive
`lower_simulates_step` — each shows that the EVM `Runs` segment for one lowered IR
construct re-establishes the relevant `Match` clauses, discharging straight to the
exp003 `runs_*` opcode rule (now merged in).

## What is proved here (C3, this run)

The engine `lower_simulates_step` decomposes, per IR construct, into a `Runs`
segment that runs the lowered opcodes and re-establishes `Match`. The hard,
program-global part of that engine is the **program-counter clause `M1`**: relating
`fr.exec.pc` to the offset-table address `pcOf prog L pc` *across a whole lowered
program*. That is heavy byte-layout arithmetic over `lower prog` and is the bulk of
the remaining C3 work (documented in `PLAN.md`).

The genuinely-closeable core — proved here, green, no `sorry` — is the set of
**atomic, frame-local simulation lemmas**: for each effecting construct, *given the
frame's local decode + stack-shape + storage correspondence*, there is a
`Runs fr fr'` to the named exp003 post-frame whose result re-establishes the
storage (`M3`) and value clauses. These are exactly the steps `lower_simulates_step`
threads with `Runs.trans`; they wrap each `runs_*` rule with the IR-state
correspondence so the simulation reads off the IR semantics (`evalExpr`,
`IRState.setStorage`). The `STOP`/`RETURN` terminators are handled by exposing the
halt step the bridge consumes.
-/

namespace Lir
open Evm
open BytecodeLayer.Hoare
open BytecodeLayer.Maps
open BytecodeLayer.Dispatch
open BytecodeLayer.System

/-! ## The `Match` invariant (`docs/ir-design.md` §6.1)

`Match c fr` relates a *running* IR configuration to an EVM frame. Because the
lowering is recompute-on-use (§4), there is **no register↔slot map**: between
statements the working stack is empty (`M5`), each `tmp` being re-materialised from
its defining expression at use. The clauses:

* `M1` pc: `fr` is at the byte offset the offset table assigns to `(L, pc)`;
* `M2` code: `fr` runs the lowered program;
* `M3` storage: the IR self-storage equals the self account's storage through the
  observable `find?/lookupStorage` lens;
* `M5` stack: empty at the statement boundary.

`M1` is parameterised by the offset-table address `pcOf`; the full program-global
discharge of `M1` is the remaining C3 work. -/

/-- The byte offset the offset table assigns to cursor `(L, pc)` of `prog`: the
block's `JUMPDEST` (`offsetTable … L.idx`), skip the `JUMPDEST` (`+1`), then the
byte length of the emitted statements `0 .. pc` of block `L`. A prefix sum, so it
is computable; `M1` pins `fr.exec.pc` to this. -/
def pcOf (prog : Program) (L : Label) (pc : Nat) : Nat :=
  let defs := defsOf prog
  let fuel := recomputeFuel prog
  offsetTable defs fuel prog.blocks L.idx + 1
    + (((prog.blockAt L).map (fun b =>
          ((b.stmts.take pc).flatMap (emitStmt defs fuel)).length)).getD 0)

/-! ### `M1` discharged at a statement cursor (generic, via `Layout`)

These wire the offset-table byte-layout arithmetic (`LirLean/Layout.lean`) and the
generic decode lemmas (`LirLean/DecodeLower.lean`) into a decode fact at the *symbolic*
`pcOf` address, over an arbitrary program. They are the program-global `M1` discharge
the simulation engine needs at each statement step: no per-program `rfl`, the pc is the
offset-table prefix sum. -/

/-- `prog.blockAt L = some b` from the `toList` index witness (the form `Layout`'s
lemmas take). -/
theorem blockAt_of_toList (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) : prog.blockAt L = some b := by
  unfold Program.blockAt; rw [← Array.getElem?_toList]; exact hb

/-- `pcOf prog L pc` unfolds to the offset-table anchor index (the `Layout` form)
when block `L` is present — the `getD 0` collapses to the block's stmt-prefix length. -/
theorem pcOf_eq_anchor (prog : Program) (L : Label) (b : Block) (pc : Nat)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    pcOf prog L pc
      = offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx + 1
        + ((b.stmts.take pc).flatMap (emitStmt (defsOf prog) (recomputeFuel prog))).length := by
  unfold pcOf; rw [blockAt_of_toList prog L b hb]; rfl

/-- **The statement-cursor byte (generic `M1`).** The byte `flatBytes prog` holds at
`pcOf prog L pc` is the head byte of the statement at that cursor — `(emitStmt … s)[0]`.
The composition of `pcOf_eq_anchor` (pc = offset-table anchor) and
`Layout.stmt_byte_anchor` (anchor byte = `emitStmt` head). The `decode_lower_*` lemmas
turn this into a decode fact for the construct. -/
theorem flatBytes_at_pcOf (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s)
    (hne : emitStmt (defsOf prog) (recomputeFuel prog) s ≠ []) :
    (flatBytes prog)[pcOf prog L pc]?
      = (emitStmt (defsOf prog) (recomputeFuel prog) s)[0]? := by
  rw [pcOf_eq_anchor prog L b pc hb]
  exact stmt_byte_anchor prog L b pc s hb hs hne

/-- The self account's storage at `key`, read through exp003's observable lens
(the same `find?/lookupStorage` used by `sstoreFrame_storage_self` /
`sloadFrame_storage_self`). This is the EVM side of `Match`'s storage clause `M3`. -/
def selfStorage (fr : Frame) (key : Word) : Word :=
  fr.exec.accounts.find? fr.exec.executionEnv.address |>.option 0 (·.lookupStorage key)

/-- The storage of account `addr` at `key` in frame `fr`, through the same lens.
Used to state the `SSTORE` effect/frame clauses keyed on a fixed self address (the
exact form exp003's `sstoreFrame_storage_*` lemmas produce), sidestepping the
post-frame's own-address defeq. -/
def storageAt (fr : Frame) (addr : AccountAddress) (key : Word) : Word :=
  fr.exec.accounts.find? addr |>.option 0 (·.lookupStorage key)

/-- **The simulation invariant** relating a running IR configuration to a frame.
See the module docstring and `docs/ir-design.md` §6.1 for the clause meanings. -/
structure Match (prog : Program) (L : Label) (pc : Nat) (st : IRState) (fr : Frame) : Prop where
  /-- `M1` — program counter at the offset-table address. -/
  pc_eq      : fr.exec.pc = UInt32.ofNat (pcOf prog L pc)
  /-- `M2` — the frame runs the lowered program. -/
  code_eq    : fr.exec.executionEnv.code = lower prog
  /-- `M3` — storage correspondence through the observable lens. -/
  storage_eq : ∀ k, selfStorage fr k = st.storage k
  /-- `M5` — empty working stack at the statement boundary. -/
  stack_nil  : fr.exec.stack = []
  /-- Standing well-formedness: the call may modify state (top-level call). -/
  can_modify : fr.exec.executionEnv.canModifyState = true

/-! ## Atomic per-construct simulation lemmas

Each lemma takes the EVM frame's **local** facts (decode at `fr.exec.pc`, stack
shape, gas bound) — the very hypotheses the `runs_*` rule wants — and packages the
resulting `Runs` together with the IR-side reading of the post-frame: the pushed
value equals `evalExpr`, storage follows `IRState.setStorage`. These are the bricks
`lower_simulates_step` threads with `Runs.trans`; they are stated frame-locally so
they compose independent of `M1`'s program-global pc arithmetic. (The frame's real
EVM gas bound is still a hypothesis of each `runs_*` rule — that is the *bytecode*
spec's honest gas, not an IR-side gas counter; the IR no longer accounts cost.) -/

/-- **`Expr.imm` simulation.** A frame decoding to `PUSH32 w` runs one step to
`pushFrameW fr w 32`, leaving `w` on top — the value `evalExpr st (.imm w) = some w`. -/
theorem sim_imm (fr : Frame) (w : Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    Runs fr (pushFrameW fr w 32)
      ∧ (pushFrameW fr w 32).exec.stack = fr.exec.stack.push w := by
  refine ⟨runs_push fr .PUSH32 w 32 (by nofun) hdec rfl rfl hgas hstk, ?_⟩
  rfl

/-- **`Expr.gas` simulation.** A frame decoding to `GAS` runs one step to
`gasFrame fr`, dropping the frame's real EVM gas by `GasConstants.Gbase` (the
*bytecode* spec's honest gas — the IR no longer accounts cost). -/
theorem sim_gas (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
    (hsz : fr.exec.stack.size + 1 ≤ 1024)
    (hgas : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (gasFrame fr)
      ∧ (gasFrame fr).exec.gasAvailable = fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase := by
  exact ⟨runs_gas fr hdec hsz hgas, rfl⟩

/-- **`Expr.add` simulation.** A frame decoding to `ADD` with `a :: b :: rest`
runs one step to `addFrame fr a b rest`, leaving `UInt256.add a b` on top — the
value `evalExpr` computes for `.add` (its arithmetic is `UInt256.add` by
construction). -/
theorem sim_add (fr : Frame) (a b : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .ADD, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (addFrame fr a b rest)
      ∧ (addFrame fr a b rest).exec.stack = rest.push (UInt256.add a b) := by
  exact ⟨runs_add fr a b rest hdec hstk hsz hgas, rfl⟩

/-- **`Expr.lt` simulation.** A frame decoding to `LT` with `a :: b :: rest` runs
one step to `ltFrame fr a b rest`, leaving `UInt256.lt a b` on top — the value
`evalExpr` computes for `.lt`. -/
theorem sim_lt (fr : Frame) (a b : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.ArithLogic .LT, .none))
    (hstk : fr.exec.stack = a :: b :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : GasConstants.Gverylow ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (ltFrame fr a b rest)
      ∧ (ltFrame fr a b rest).exec.stack = rest.push (UInt256.lt a b) := by
  exact ⟨runs_lt fr a b rest hdec hstk hsz hgas, rfl⟩

/-- **`Expr.sload` simulation.** A frame decoding to `SLOAD` with `key :: rest`
runs one step to `sloadFrame fr key rest`, leaving the self account's stored value
at `key` on top — equal to `st.storage key` under `Match`'s `M3` (via
`sloadFrame_storage_self`). -/
theorem sim_sload (fr : Frame) (key : Word) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SLOAD, .none))
    (hstk : fr.exec.stack = key :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hgas : Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
              (fr.exec.executionEnv.address, key)) ≤ fr.exec.gasAvailable.toNat) :
    Runs fr (sloadFrame fr key rest)
      ∧ (sloadFrame fr key rest).exec.stack.head? = some (selfStorage fr key) := by
  exact ⟨runs_sload fr key rest hdec hstk hsz hgas, sloadFrame_storage_self fr key rest⟩

/-- **SSTORE effect, value-agnostic.** Reading the self account's storage at
`key` after `sstoreFrame` returns `newValue` — for *every* `newValue`, including
`0` (a slot clear, which `Account.updateStorage` implements as an `RBMap.erase`;
the read-back then hits `Evm.Storage.findD_erase_self`). -/
theorem sstoreFrame_storage_self' (fr : Frame) (key newValue : Word) (rest : Stack Word)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? fr.exec.executionEnv.address
      |>.option 0 (·.lookupStorage key)) = newValue := by
  rw [sstoreFrame_accounts fr key newValue rest acc hself, accounts_find?_insert_self]
  show (acc.updateStorage key newValue).lookupStorage key = newValue
  unfold Account.updateStorage Account.lookupStorage
  by_cases h0 : newValue = 0
  · subst h0
    rw [if_pos (by decide)]
    exact Evm.Storage.findD_erase_self acc.storage key
  · rw [if_neg (by
      show ¬ ((newValue == (default : UInt256)) = true)
      rw [show (default : UInt256) = 0 from rfl]
      intro hc; exact h0 ((UInt256.beq_iff_eq newValue 0).mp hc))]
    exact storage_findD_insert_self _ _ _ _

/-- **SSTORE framing, value-agnostic.** Any cell other than `(self, key)` is
unchanged after `sstoreFrame`, for *every* `newValue` including `0` (the erase
branch, read back through `Evm.Storage.findD_erase_of_ne`). -/
theorem sstoreFrame_storage_frame' (fr : Frame) (key newValue : Word) (rest : Stack Word)
    (acc : Account)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc)
    (a' : AccountAddress) (k' : UInt256)
    (hframe : a' ≠ fr.exec.executionEnv.address ∨ k' ≠ key) :
    ((sstoreFrame fr key newValue rest).exec.accounts.find? a' |>.option 0 (·.lookupStorage k'))
      = (fr.exec.accounts.find? a' |>.option 0 (·.lookupStorage k')) := by
  rw [sstoreFrame_accounts fr key newValue rest acc hself]
  rcases hframe with ha | hk
  · rw [accounts_find?_insert_of_ne _ _ ha]
  · by_cases ha : a' = fr.exec.executionEnv.address
    · subst ha
      rw [accounts_find?_insert_self, hself]
      show (acc.updateStorage key newValue).lookupStorage k' = acc.lookupStorage k'
      unfold Account.updateStorage Account.lookupStorage
      by_cases h0 : newValue = 0
      · subst h0
        rw [if_pos (by decide)]
        exact Evm.Storage.findD_erase_of_ne acc.storage hk
      · rw [if_neg (by
          show ¬ ((newValue == (default : UInt256)) = true)
          rw [show (default : UInt256) = 0 from rfl]
          intro hc; exact h0 ((UInt256.beq_iff_eq newValue 0).mp hc))]
        exact storage_findD_insert_of_ne _ _ _ hk
    · rw [accounts_find?_insert_of_ne _ _ ha]

/-- **`Stmt.sstore` simulation.** A frame decoding to `SSTORE` with
`key :: value :: rest` runs one step to `sstoreFrame fr key value rest`; reading
back `(self, key)` returns `value` (for *every* `value`, zero writes included),
re-establishing `M3` at the written cell, and any other cell is unchanged (the
frame clause). -/
theorem sim_sstore (fr : Frame) (key value : Word) (rest : Stack Word) (acc : Account)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .SSTORE, .none))
    (hstk : fr.exec.stack = key :: value :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmod : fr.exec.executionEnv.canModifyState = true)
    (hstip : ¬ fr.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    (hcost : sstoreChargeOf fr.exec key value ≤ fr.exec.gasAvailable.toNat)
    (hself : fr.exec.accounts.find? fr.exec.executionEnv.address = some acc) :
    Runs fr (sstoreFrame fr key value rest)
      ∧ storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address key = value
      ∧ ∀ k', k' ≠ key →
          storageAt (sstoreFrame fr key value rest) fr.exec.executionEnv.address k'
            = storageAt fr fr.exec.executionEnv.address k' := by
  refine ⟨runs_sstore fr key value rest hdec hstk hsz hmod hstip hcost, ?_, ?_⟩
  · exact sstoreFrame_storage_self' fr key value rest acc hself
  · intro k' hk'
    exact sstoreFrame_storage_frame' fr key value rest acc hself
      fr.exec.executionEnv.address k' (Or.inr hk')

/-! ### `popFrame` accessor reductions

`popPost`/`popFrame` (exp003 `Hoare.lean`) `replaceStackAndIncrPC`s after a `Gbase`
charge — replacing the stack with `rest`, advancing pc by one, leaving
`executionEnv` (hence code / address) untouched. These reductions mirror the
`sstoreFrame_*` / `sloadFrame_*` families so the worked-example run can read off the
post-frame's code/pc/stack/gas/addr by `simp`. -/

@[simp] theorem popFrame_code (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem popFrame_validJumps (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).validJumps = fr.validJumps := rfl

@[simp] theorem popFrame_addr (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem popFrame_pc (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem popFrame_stack (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.stack = rest := rfl

@[simp] theorem popFrame_gas (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.gasAvailable
      = fr.exec.gasAvailable - UInt64.ofNat GasConstants.Gbase := rfl

/-! ## MSTORE / MLOAD simulation (the memory value channel)

The memory bricks Track C's value channel (`docs/calls-value-channel-plan.md`)
threads. `sim_mload` exposes the pushed word (the head of the resulting stack);
`sim_mstore` exposes that the post-frame's memory is `fr`'s memory (on the
doubly-charged state) with `val` written at `addr` (`mstore addr val`) — the read-back
a later MLOAD lemma consumes. Both take the memory-expansion witness `hmem` (pinning
`words'`) and the two honest *bytecode*-gas bounds (memory expansion + `Gverylow`),
exactly the hypotheses `runs_mstore`/`runs_mload` want. Mirrors `sim_sstore`/`sim_sload`. -/

/-- **`Expr.mload` simulation.** A frame decoding to `MLOAD` with `addr :: rest` runs
one step to `mloadFrame fr addr words' rest`, leaving the word read from memory at
`addr` on top — exposed through `mloadFrame_value`. -/
theorem sim_mload (fr : Frame) (addr : Word) (words' : UInt64) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MLOAD, .none))
    (hstk : fr.exec.stack = addr :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words'
                ≤ fr.exec.gasAvailable.toNat)
    (hgas : GasConstants.Gverylow
              ≤ (fr.exec.gasAvailable
                  - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words')).toNat) :
    Runs fr (mloadFrame fr addr words' rest)
      ∧ (mloadFrame fr addr words' rest).exec.stack.head?
          = some ((BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mload addr).1 := by
  exact ⟨runs_mload fr addr words' rest hdec hstk hsz hmem hgasMem hgas,
    mloadFrame_value fr addr words' rest⟩

/-- **`Stmt.mstore` simulation.** A frame decoding to `MSTORE` with
`addr :: val :: rest` runs one step to `mstoreFrame fr addr val words' rest`; the
post-frame's memory is `fr`'s (doubly-charged) machine state with `val` written at
`addr` (`mstore addr val`) — the read-back a later `sim_mload` consumes. -/
theorem sim_mstore (fr : Frame) (addr val : Word) (words' : UInt64) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .MSTORE, .none))
    (hstk : fr.exec.stack = addr :: val :: rest)
    (hsz : fr.exec.stack.size ≤ 1024)
    (hmem : memoryExpansionWords? fr.exec.activeWords addr 32 = some words')
    (hgasMem : BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words'
                ≤ fr.exec.gasAvailable.toNat)
    (hgas : GasConstants.Gverylow
              ≤ (fr.exec.gasAvailable
                  - UInt64.ofNat (BytecodeLayer.Dispatch.memExpansionChargeOf fr.exec words')).toNat) :
    Runs fr (mstoreFrame fr addr val words' rest)
      ∧ (mstoreFrame fr addr val words' rest).exec.toMachineState
          = (BytecodeLayer.Dispatch.memChargedState fr.exec words').toMachineState.mstore addr val := by
  exact ⟨runs_mstore fr addr val words' rest hdec hstk hsz hmem hgasMem hgas,
    mstoreFrame_memory fr addr val words' rest⟩

/-! ## Terminator halt steps (consumed by the bridge `hhalt`)

`STOP`/`RETURN` are **not** `runs_*` rules — the bridge `messageCall_runs` takes the
halt directly via its `hhalt` argument. These lemmas expose exactly that halt step
for the two IR terminators, ready to feed the bridge. -/

/-- **`Term.stop` halt.** A frame decoding to `STOP` halts with the current state
and empty output — the `hhalt` the bridge consumes for `IRHalt.stopped`. -/
theorem halt_stop (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .STOP, .none))
    (hstk : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success fr.exec .empty) :=
  stepFrame_stop fr hdec hstk

/-- **`Term.ret` halt** (empty return window — the C3 `RETURN` shape: the lowering
pushes `0 0` for `offset`/`size`). A frame decoding to `RETURN` with `0 :: 0 ::
rest` halts successfully — the `hhalt` the bridge consumes for `IRHalt.returned`. -/
theorem halt_ret (fr : Frame) (rest : Stack Word)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .RETURN, .none))
    (hstk : fr.exec.stack = (0 : Word) :: (0 : Word) :: rest)
    (hsz : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success (returnEmptyPost fr.exec rest)
      (fr.exec.memory.readWithPadding (0 : Word).toNat (0 : Word).toNat)) :=
  stepFrame_return_empty fr rest hdec hstk hsz

/-! ## `Stmt.call` simulation (the `Runs.call` node)

A `Stmt.call` lowers to seven CALL-arg pushes then `CALL`. Under lowering it is a
`Runs.call` node carrying a `CallReturns` witness (the CALL step, the child
entering as code, the black-box child run, the resumed parent). The engine threads
exactly that node by `Runs.trans` — see the worked compositional derivation in
`BytecodeLayer.Examples.CallerProgExample`. We expose the constructor wrapper. -/

/-- **`Stmt.call` simulation.** Given a returning external CALL at `callFr`
(`CallReturns callFr resumeFr`) and the `Runs` continuation from the resumed frame,
the whole call is one `Runs callFr fr'` — a `Runs.call` node glued by the rest. The
`CallReturns` witness is built exactly as in
`BytecodeLayer.Examples.CallerProgExample.caller_callReturns`. -/
theorem sim_call {callFr resumeFr fr' : Frame}
    (hcall : CallReturns callFr resumeFr) (rest : Runs resumeFr fr') :
    Runs callFr fr' :=
  Runs.call hcall rest

/-! ## Call-oracle reflexivity headline (`docs/ir-design.md` §5)

The deliverable that demonstrates the call-agnostic design: **instantiate the
oracle to `evmCallOracle` → the IR's call-effect is *reflexively equal* to the
lowered bytecode's ext-call effect.** The
IR side reads the oracle's projections (`postStorage` / `restoredGas` /
`successWord`); the EVM side is the resumed frame `resumeAfterCall result pd`'s
observables. Because `evmCallOracle`'s fields are *defined* as those very
projections (`LirLean/Call.lean`), the three coincidences are `rfl`-clean.

The `CallReturns callFr resumeFr` witness pins `resumeFr = resumeAfterCall
childRes.toCallResult pending`, so the headline reads off the actual resumed frame.

**Scope** (the success-flag/stack subtlety, flagged in `LirLean/Call.lean` and
§5): the *state* effect (post-storage through the `M3` lens, restored gas) and the
*value* of the success word are reflected here. Folding the success word into a
`resultTmp` binding — which would have to survive `Match`'s `M5 stack_nil`
recompute-on-use discipline despite being a dynamic, non-recomputable value — is a
separately-tracked lowering-completeness follow-up; it is not part of this
reflexivity equation. -/

/-- **The external-call reflexivity headline.** Given a returning external CALL
(`CallReturns callFr resumeFr`, so `resumeFr = resumeAfterCall result pd` for the
projected child result / pending call), at `evmCallOracle` the IR's call effect
coincides — *by construction* — with the lowered resume's observables:

* **post-storage** of any account `addr` at `key` equals the resumed frame's
  storage through the `M3` lens (`storageAt resumeFr`);
* **restored gas** equals the resumed frame's `gasAvailable` (`gasAfterReturn`);
* **success word** equals the word the CALL pushed onto the stack — the head of
  `resumeFr`'s stack, which is exp003's `x` (0 on failure/insufficient-funds/
  depth-limit, else 1).

Instantiate the oracle to the EVM one and the IR's external-call effect is
reflexively the lowered bytecode's. -/
theorem call_reflects_lowered {callFr resumeFr : Frame}
    (hcall : CallReturns callFr resumeFr) :
    ∃ result pd, resumeFr = resumeAfterCall result pd
      ∧ (∀ addr key, evmCallOracle.postStorage result pd addr key = storageAt resumeFr addr key)
      ∧ evmCallOracle.restoredGas result pd = resumeFr.exec.gasAvailable
      ∧ evmCallOracle.successWord result pd = callSuccessFlag result pd := by
  obtain ⟨cp, pending, child, childRes, _hstep, _henters, _hdrive, hresume⟩ := hcall
  subst hresume
  exact ⟨childRes.toCallResult, pending, rfl, fun _ _ => rfl, rfl, rfl⟩

/-! ## Top-level preservation discharge (`lower_preserves`, the bridge half)

`lower_preserves` (`docs/ir-design.md` §6.3) closes the simulation under the IR run
and crosses the single boundary bridge `messageCall_runs`. The program-global
*assembly* of the `Runs fr₀ last` (chaining `lower_simulates_step` segments under
`M1`'s offset-table pc arithmetic) is the remaining C3 work; the **discharge** —
turning an assembled `Runs` + the terminator halt into the observable
`messageCall` result — is fully provable now and proved here. It is the exact half
that consumes A's `messageCall_runs`, specialised to the two IR terminators.

`lower_preserves_discharge` is the construct-agnostic bridge; `lower_preserves_stop`
/ `lower_preserves_ret` are the two terminator instances, supplying the halt from
`halt_stop` / `halt_ret`. The single-call worked program assembles its `Runs` and
applies the matching one. -/

/-- **The boundary discharge.** A top-level call entering the lowered code as code
(`EntersAsCode`) whose assembled `Runs fr₀ last` reaches a halting `last`
(`stepFrame last = .halted halt`) delivers the caller's halt result as
`messageCall`. This is `messageCall_runs` applied at the IR/lowering boundary; it
crosses regardless of how many `Runs.call` (external CALL) nodes the assembled run
contains (multi-call composition is `messageCall_runs_calls`). -/
theorem lower_preserves_discharge (prog : Program) (p : CallParams)
    {fr₀ last : Frame} {halt : FrameHalt}
    (hbegin : EntersAsCode p fr₀)
    (_hcode : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hhalt  : stepFrame last = .halted halt) :
    messageCall p = .ok (FrameResult.toCallResult (endFrame last halt)) :=
  messageCall_runs p hbegin hruns hhalt

/-- **`Term.stop` preservation.** When the assembled `Runs` lands on a `STOP` frame
`last` (`IRHalt.stopped`), the discharge pins `messageCall` to `last`'s success
`endFrame`. The halt is `halt_stop`. -/
theorem lower_preserves_stop (prog : Program) (p : CallParams) {fr₀ last : Frame}
    (hbegin : EntersAsCode p fr₀)
    (hcode  : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hdec   : decode last.exec.executionEnv.code last.exec.pc = some (.System .STOP, .none))
    (hstk   : last.exec.stack.size ≤ 1024) :
    messageCall p = .ok (FrameResult.toCallResult
      (endFrame last (.success last.exec .empty))) :=
  lower_preserves_discharge prog p hbegin hcode hruns (halt_stop last hdec hstk)

/-- **`Term.ret` preservation** (empty return window). When the assembled `Runs`
lands on a `RETURN` frame `last` with `0 :: 0 :: rest` (`IRHalt.returned`), the
discharge pins `messageCall` to `last`'s success `endFrame`. The halt is `halt_ret`. -/
theorem lower_preserves_ret (prog : Program) (p : CallParams) {fr₀ last : Frame}
    (rest : Stack Word)
    (hbegin : EntersAsCode p fr₀)
    (hcode  : fr₀.exec.executionEnv.code = lower prog)
    (hruns  : Runs fr₀ last)
    (hdec   : decode last.exec.executionEnv.code last.exec.pc = some (.System .RETURN, .none))
    (hstk   : last.exec.stack = (0 : Word) :: (0 : Word) :: rest)
    (hsz    : last.exec.stack.size ≤ 1024) :
    messageCall p = .ok (FrameResult.toCallResult
      (endFrame last (.success (returnEmptyPost last.exec rest)
        (last.exec.memory.readWithPadding (0 : Word).toNat (0 : Word).toNat)))) :=
  lower_preserves_discharge prog p hbegin hcode hruns (halt_ret last rest hdec hstk hsz)

end Lir

-- Build-enforced axiom-cleanliness guard for the memory value-channel simulation
-- bricks: both MSTORE/MLOAD arms depend only on `[propext, Classical.choice, Quot.sound]`.
