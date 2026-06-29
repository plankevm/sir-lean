import LirLean.SimStmts
import LirLean.JumpValid
import LirLean.DecodeAnchors
import LirLean.V2.RunLog

/-!
# LirLean — `sim_term` (Layer **E** of the general `lower_conforms` grind)

Block-terminator simulation: from a frame in `Corr`-correspondence with the V2 IR state
at the *terminator cursor* `(L, b.stmts.length)` — the frame Layer D's `sim_stmts_block`
delivers — running the lowered terminator bytes either **halts** (matching the IR halt's
world channel, E1) or **runs to the successor block's entry frame**, re-establishing `Corr`
at `(successor, 0)` (E2). These are the two bricks the program-global block driver (Layer F)
threads with `Runs.trans` to walk a whole CFG path.

## The terminator cursor coincides with the offset-table terminator anchor

`Corr prog … st fr L b.stmts.length` pins `fr.exec.pc = UInt32.ofNat (pcOf prog L
b.stmts.length)`. At the full statement count the `pcOf` prefix sum `(b.stmts.take
b.stmts.length).flatMap (emitStmt …)` runs over *all* the block's statements, so it equals
`termOf prog L` (`DecodeAnchors.termOf` — the byte offset of the block's `emitTerm` bytes).
`pcOf_eq_termOf` makes the bridge, so the A3 terminator decode anchors (`decode_at_term_*`)
land at exactly the frame's running pc.

## Scope — WORLD channel only (value channel deferred)

`observe self fr` (`V2/RunLog.lean`) returns `{ world := resultStorageAt fr self, result :=
.stopped }`: its `world` is the self-account storage lens of the finished `FrameResult`, its
`result` is the **value-free** success boundary `.stopped`. So:

* **`stop`** — both the `world` (storage lens) and the `result` (`.stopped`) match the IR
  halt `{ world := st.world, result := .stopped }` (`RunFrom.stop`).
* **`ret t`** — only the **world** (storage delta) is asserted: `observe`'s `result` is
  `.stopped`, while the IR's `RunFrom.ret` halt gives `.returned w`. The RETURN **value
  channel is DEFERRED** (a tracked follow-up, `V2/RunLog.lean` `observe` doc). We still run
  `materialise t` (B1, `materialise_runs`) for the RETURN, but the returned word is **not**
  asserted; only the storage lens (`world`) is matched.

The `world`-channel bridge `observe self (endFrame last halt) = storageAt last self` is the
`endCall` success commit (`resultStorageAt_endFrame_success`): for a `.call`-kind frame
halting `.success` with non-empty committed accounts, `endFrame`'s `toCallResult.accounts`
is the frame's `exec.accounts`, so the result lens *is* the frame lens (`storageAt last
self`), which `Corr`'s `StorageAgree` ties to `st.world`. The `.call`-kind + non-empty
hypotheses are the honest top-level-frame facts (the lowered program is entered as a
top-level CALL — `EntersAsCode` / `beginCall`), taken as structured hypotheses exactly as
the per-statement layers take their `hself`/decode bundles.

## Scope — `ret`/`branch` stack-shape + destination resolution as structured hypotheses

* **`ret t`** — the lowering is `materialise t ++ PUSH32 0 ++ PUSH32 0 ++ [RETURN]`
  (`emitTerm`): `materialise t` leaves `vw`, then the two `PUSH32 0` push the `offset = 0` /
  `size = 0` window the empty-window halt brick (`halt_ret`/`stepFrame_return_empty`) consumes
  (`0 :: 0 :: rest`). The `ret` arm runs those two pushes ITSELF (via `sim_imm`), so the former
  supplied empty-window stack hypothesis is now **discharged internally** — only the two PUSH32
  0 + RETURN decode/gas envelopes and the top-level-frame facts remain as the structured `hret`
  bundle (the §7 supplied observation), exactly where the concrete program pins them.
* **`jump`/`branch`** — the JUMP/JUMPI destination must resolve (`fr.get_dest dest = some
  new_pc`). E3 (`block_offset_validJump`) gives `UInt32.ofNat (offsetTable … dst.idx) ∈
  validJumpDests (lower prog) 0`; tying that to `fr.get_dest dest` needs the frame's
  `validJumps = validJumpDests (lower prog) 0` (a top-level-frame fact) and the PUSH4
  immediate round-tripping to `UInt32.ofNat (offsetTable … dst.idx)`. Both are taken as
  structured hypotheses (`hvalid`/`hdestword`), discharged by E3 + the offset round-trip at
  the call site, mirroring how `materialise_runs` takes `MatDec`.

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `Match.lean`,
`JumpValid.lean`); nothing here touches `V2/Machine.lean` / `V2/Law.lean` (the frame-free
spine).
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.V2

/-! ## The terminator cursor = the offset-table terminator anchor -/

/-- **The terminator cursor coincides with `termOf`.** At the full statement count, the
`pcOf` prefix sum runs over all the block's statements, so it equals `termOf prog L`. -/
theorem pcOf_eq_termOf (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    pcOf prog L b.stmts.length = termOf prog L := by
  rw [pcOf_eq_anchor prog L b b.stmts.length hb, termOf_eq_anchor prog L b hb,
      List.take_length]

/-! ## The world-channel bridge: `observe` of a success halt = the frame's storage lens

`observe self (endFrame fr halt)` reads the *finished result*'s self-account storage
(`resultStorageAt`, the `.toCallResult.accounts` lens). For a `.call`-kind frame halting
`.success fr.exec output` with the committed accounts non-empty, `endCall`'s `.success`
branch keeps `exec.accounts` (the non-empty branch of its `if … == ∅`), so the result lens
is *exactly* `storageAt fr self` — the frame lens `Corr`'s `StorageAgree` ties to the IR
world. These are the honest top-level-frame facts (the lowered program is entered as a
top-level CALL — its frame `kind` is `.call`, and a run that wrote storage has non-empty
accounts), taken as structured hypotheses. -/

/-- **The success-halt world bridge.** For a `.call`-kind frame `fr` halting `.success
hexec output` where the halt exec's committed accounts equal the frame's own non-empty
accounts (`hacc_eq`), the `observe` world of the finished result is the frame's storage lens
`storageAt fr self`. (`stop` halts with `hexec = fr.exec` directly; `ret` halts with `hexec =
returnEmptyPost fr.exec rest`, which leaves `accounts` untouched — the `hacc_eq` is `rfl` in
both.) -/
theorem resultStorageAt_endFrame_success (fr : Frame) (hexec : Evm.ExecutionState)
    (output : ByteArray) (self : AccountAddress) (key : Word) (cp : Evm.Checkpoint)
    (hkind : fr.kind = .call cp)
    (hacc_eq : hexec.accounts = fr.exec.accounts)
    (hne : ¬ (fr.exec.accounts == ∅) = true) :
    resultStorageAt (endFrame fr (.success hexec output)) self key
      = storageAt fr self key := by
  show ((endFrame fr (.success hexec output)).toCallResult.accounts.find? self
          |>.option 0 (·.lookupStorage key))
        = (fr.exec.accounts.find? self |>.option 0 (·.lookupStorage key))
  have hacc : (endFrame fr (.success hexec output)).toCallResult.accounts
      = fr.exec.accounts := by
    unfold Evm.endFrame
    rw [hkind]
    show (Evm.endCall cp (.success hexec output)).accounts = fr.exec.accounts
    have hne' : (hexec.accounts == ∅) = false := by
      cases h : (hexec.accounts == ∅) with
      | false => rfl
      | true => rw [hacc_eq] at h; exact absurd h hne
    show (if (hexec.accounts == ∅) = true then cp.accounts else hexec.accounts)
      = fr.exec.accounts
    rw [hne', if_neg (by simp), hacc_eq]
  rw [hacc]

/-! ## Frame-accessor reductions for the control-flow post-frames

`jumpFrame` / `jumpdestFrame` leave the `executionEnv` (code / address / canModifyState) and
the accounts (hence the self-storage lens) untouched — only `stack`, `pc`, `gasAvailable`
change. These `rfl` lemmas expose exactly the clauses E2's `Corr` re-establishment threads. -/

@[simp] theorem jumpFrame_code (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem jumpFrame_addr (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.executionEnv.address
      = fr.exec.executionEnv.address := rfl

@[simp] theorem jumpFrame_canMod (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem jumpFrame_selfStorage (fr : Frame) (cost : ℕ) (new_pc : UInt32)
    (rest : Stack Word) (k : Word) :
    selfStorage (jumpFrame fr cost new_pc rest) k = selfStorage fr k := rfl

@[simp] theorem jumpFrame_pc (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.pc = new_pc := rfl

@[simp] theorem jumpFrame_stack (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.stack = rest := rfl

@[simp] theorem jumpFrame_validJumps (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).validJumps = fr.validJumps := rfl

@[simp] theorem jumpdestFrame_code (fr : Frame) :
    (jumpdestFrame fr).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem jumpdestFrame_addr (fr : Frame) :
    (jumpdestFrame fr).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem jumpdestFrame_canMod (fr : Frame) :
    (jumpdestFrame fr).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem jumpdestFrame_selfStorage (fr : Frame) (k : Word) :
    selfStorage (jumpdestFrame fr) k = selfStorage fr k := rfl

@[simp] theorem jumpdestFrame_pc (fr : Frame) :
    (jumpdestFrame fr).exec.pc = fr.exec.pc + UInt32.ofNat 1 := rfl

@[simp] theorem jumpdestFrame_stack (fr : Frame) :
    (jumpdestFrame fr).exec.stack = fr.exec.stack := rfl

@[simp] theorem jumpdestFrame_validJumps (fr : Frame) :
    (jumpdestFrame fr).validJumps = fr.validJumps := rfl

@[simp] theorem jumpiFallthroughFrame_code (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem jumpiFallthroughFrame_addr (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem jumpiFallthroughFrame_canMod (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem jumpiFallthroughFrame_selfStorage (fr : Frame) (rest : Stack Word) (k : Word) :
    selfStorage (jumpiFallthroughFrame fr rest) k = selfStorage fr k := rfl

@[simp] theorem jumpiFallthroughFrame_pc (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem jumpiFallthroughFrame_stack (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.stack = rest := rfl

@[simp] theorem jumpiFallthroughFrame_validJumps (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).validJumps = fr.validJumps := rfl

/-! ### `toMachineState.memory` / `activeWords` reductions for the control-flow post-frames

Control-flow steps (JUMP / JUMPDEST / JUMPI-fallthrough) charge gas and move the pc/stack but
never touch memory — these `rfl` lemmas thread the `Corr.memAgree` memory value channel across
block edges (the frames preserve both `memory` bytes and `activeWords`). -/

@[simp] theorem jumpFrame_memory (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem jumpFrame_activeWords (fr : Frame) (cost : ℕ) (new_pc : UInt32) (rest : Stack Word) :
    (jumpFrame fr cost new_pc rest).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem jumpdestFrame_memory (fr : Frame) :
    (jumpdestFrame fr).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem jumpdestFrame_activeWords (fr : Frame) :
    (jumpdestFrame fr).exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem jumpiFallthroughFrame_memory (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.toMachineState.memory
      = fr.exec.toMachineState.memory := rfl

@[simp] theorem jumpiFallthroughFrame_activeWords (fr : Frame) (rest : Stack Word) :
    (jumpiFallthroughFrame fr rest).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := rfl

/-! ## E1 — `sim_term_halt` (the halting terminators `stop` / `ret`)

A block whose terminator is `stop` or `ret t` runs (the `ret` value via B1 `materialise_runs`)
to a frame `last` that **halts** (`stepFrame last = .halted halt`), whose `observe` **world**
matches the IR halt's world (the storage lens, tied through `Corr`'s `StorageAgree`). For
`stop` the `result` (`.stopped`) also matches; for `ret` the `result` is the value channel,
**deferred** (asserted on the world only).

The `self` address is the frame's own (`hself`), so `Corr`'s `selfStorage = storageAt fr
self` lens applies; the `.call`-kind + non-empty-accounts top-level-frame facts feed the
world bridge (`resultStorageAt_endFrame_success`). -/

/-- **`sim_term_halt`, the `stop` arm.** From `Corr` at the terminator cursor `(L,
b.stmts.length)` with `b.term = .stop`, a frame decoding to `STOP` halts immediately
(`Runs.refl`) with the success `endFrame`; its `observe` **world** is `st.world` (the storage
lens, via `Corr`'s `StorageAgree`) and its `result` is `.stopped` — both channels match the
IR `RunFrom.stop` halt. -/
theorem sim_term_halt_stop {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {L : Label} {b : Block} {fr : Frame} {self : AccountAddress}
    {cp : Evm.Checkpoint}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (_hterm : b.term = .stop)
    (hself : self = fr.exec.executionEnv.address)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .STOP, .none))
    (hkind : fr.kind = .call cp)
    (hne : ¬ (fr.exec.accounts == ∅) = true) :
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
      ∧ (observe self (endFrame last halt)).world = st.world
      ∧ (observe self (endFrame last halt)).result = .stopped := by
  refine ⟨fr, .success fr.exec .empty, Runs.refl fr,
    halt_stop fr hdec (by rw [hcorr.stack_nil]; show (0 : ℕ) ≤ 1024; omega), ?_, rfl⟩
  -- world channel: observe's world is the frame's storage lens = st.world.
  funext key
  show (observe self (endFrame fr (.success fr.exec .empty))).world key = st.world key
  show resultStorageAt (endFrame fr (.success fr.exec .empty)) self key = st.world key
  rw [resultStorageAt_endFrame_success fr fr.exec .empty self key cp hkind rfl hne]
  -- storageAt fr self = selfStorage fr (self = fr's own address) = st.world (StorageAgree).
  rw [hself]
  show selfStorage fr key = st.world key
  exact hcorr.storage key

/-- **`sim_term_halt`, the `ret` arm (world channel only — value DEFERRED).** From `Corr` at
the terminator cursor `(L, b.stmts.length)` with `b.term = .ret t` and `st.locals t = some
vw`, running the lowered `materialise t ++ PUSH32 0 ++ PUSH32 0 ++ RETURN` (B1
`materialise_runs`, the genuine value run, followed by the two zero window operands) reaches a
frame with the empty-window `0 :: 0 :: vw :: rest` stack and **halts** on `RETURN`. The
`materialise t` leaves `vw`; the two `PUSH32 0` (run here via `sim_imm`, the B1 `.imm` leaf)
push the `offset=0`/`size=0` window the `RETURN` consumes — so the former supplied empty-window
stack hypothesis (`hretstk`) is now **discharged internally** (the lowering grew by `emitImm 0
++ emitImm 0`, +66 bytes, and we run those two pushes ourselves). `RETURN(0,0)` returns the
empty output and halts; the residual `vw` underneath is discarded with the frame.

The `observe` **world** of the finished result is `st.world` (the storage lens, preserved
across the materialise + two pushes by `MatRuns.storage` / `pushFrameW_selfStorage`, tied
through `Corr`'s `StorageAgree`). The `result` is **NOT** asserted — `observe`'s result is
`.stopped`, while the IR `RunFrom.ret` gives `.returned vw`; the RETURN value channel is a
tracked follow-up (`V2/RunLog.lean` `observe` doc).

The decode (`hdv`) / gas (`hgas`) / stack (`hstk`) bundle for the materialise is the per-leaf
B1 interface (as in `sim_sstore_stmt`). The two PUSH32 0 + RETURN decode/gas envelopes and the
top-level-frame `kind`/non-empty facts are the honest structured hypotheses (`hret`), supplied
at the materialise endpoint `frv` — exactly where the concrete program pins them. -/
theorem sim_term_halt_ret {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {t : Tmp} {vw : Word}
    {L : Label} {b : Block} {fr : Frame} {self : AccountAddress}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (_hterm : b.term = .ret t)
    (hself : self = fr.exec.executionEnv.address)
    (hv : st.locals t = some vw)
    -- B1 materialise bundle for the RETURN value `t` (the per-leaf interface):
    (hdv : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
            fr.exec.pc (.tmp t))
    (hgas : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).sum
              ≤ fr.exec.gasAvailable.toNat)
    (hstk : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp t)).length ≤ 1024)
    -- RETURN-site structured hypotheses on the materialise endpoint `frv`: the two PUSH32 0
    -- window operands decode/gas-cover, RETURN decodes after them, and the frame is a
    -- top-level `.call` frame with non-empty committed accounts (the honest top-level facts).
    (hret : ∀ frv : Frame, Runs fr frv →
        frv.exec.executionEnv.code = fr.exec.executionEnv.code →
        frv.exec.executionEnv.address = fr.exec.executionEnv.address →
        (∀ k, selfStorage frv k = selfStorage fr k) →
        frv.exec.stack = vw :: fr.exec.stack →
        ∃ cp,
          -- decode of the two zero window pushes and the RETURN that follows them:
          decode frv.exec.executionEnv.code frv.exec.pc
              = some (.Push .PUSH32, some ((0 : Word), 32))
          ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33)
              = some (.Push .PUSH32, some ((0 : Word), 32))
          ∧ decode frv.exec.executionEnv.code (frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33)
              = some (.System .RETURN, .none)
          -- gas margins for the two PUSH32 0 (Gverylow each, via `sim_imm`'s `3 ≤ …`):
          ∧ 3 ≤ frv.exec.gasAvailable.toNat
          ∧ 3 ≤ (pushFrameW frv (0 : Word) 32).exec.gasAvailable.toNat
          -- top-level-frame facts at `frv` (transported across the two pushes by `pushFrameW`):
          ∧ frv.kind = .call cp
          ∧ ¬ (frv.exec.accounts == ∅) = true) :
    ∃ last halt, Runs fr last ∧ stepFrame last = .halted halt
      ∧ (observe self (endFrame last halt)).world = st.world := by
  -- B1: run `materialise t`, reaching `frv` with `vw` pushed, storage lens preserved.
  have hevv : V2.evalExpr st obs (.tmp t) = some vw := hv
  have hszfr : fr.exec.stack.size = 0 := by rw [hcorr.stack_nil]; rfl
  have hstkv : fr.exec.stack.size + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog)
      (.tmp t)).length ≤ 1024 := by rw [hszfr]; omega
  obtain ⟨frv, hmrv⟩ := materialise_runs sloadChg (recomputeFuel prog) st obs (.tmp t) vw fr
    hdv hcorr.defsSound hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
    hevv hgas hstkv
  -- the RETURN-site facts at `frv` (the two PUSH32 0 decode/gas + top-level frame facts).
  obtain ⟨cp, hd1, hd2, hdret, hg1, hg2, hkind, hne⟩ :=
    hret frv hmrv.runs hmrv.code hmrv.addr hmrv.storage hmrv.stack
  -- stack at `frv` is `vw :: fr.stack = [vw]` (the boundary stack is empty).
  have hfrvstk : frv.exec.stack = vw :: ([] : Stack Word) := by
    rw [hmrv.stack, hcorr.stack_nil]; rfl
  -- run the first PUSH32 0: stack `0 :: vw :: []`, pc `frv.pc + 33`.
  have hsz1 : frv.exec.stack.size + 1 ≤ 1024 := by rw [hfrvstk]; show (1 : ℕ) + 1 ≤ 1024; omega
  obtain ⟨hr1, hs1⟩ := sim_imm frv (0 : Word) hd1 hg1 hsz1
  set f1 := pushFrameW frv (0 : Word) 32 with hf1
  have hf1stk : f1.exec.stack = (0 : Word) :: vw :: ([] : Stack Word) := by
    rw [hs1, hfrvstk]; rfl
  have hf1pc : f1.exec.pc = frv.exec.pc + UInt32.ofNat 33 := by
    rw [hf1, pushFrameW_pc, push32_pcΔ]
  have hf1code : f1.exec.executionEnv.code = frv.exec.executionEnv.code := rfl
  -- run the second PUSH32 0: stack `0 :: 0 :: vw :: []`, pc `frv.pc + 33 + 33`.
  have hd1' : decode f1.exec.executionEnv.code f1.exec.pc
      = some (.Push .PUSH32, some ((0 : Word), 32)) := by rw [hf1code, hf1pc]; exact hd2
  have hsz2 : f1.exec.stack.size + 1 ≤ 1024 := by rw [hf1stk]; show (2 : ℕ) + 1 ≤ 1024; omega
  obtain ⟨hr2, hs2⟩ := sim_imm f1 (0 : Word) hd1' hg2 hsz2
  set f2 := pushFrameW f1 (0 : Word) 32 with hf2
  have hf2stk : f2.exec.stack = (0 : Word) :: (0 : Word) :: vw :: ([] : Stack Word) := by
    rw [hs2, hf1stk]; rfl
  have hf2pc : f2.exec.pc = frv.exec.pc + UInt32.ofNat 33 + UInt32.ofNat 33 := by
    rw [hf2, pushFrameW_pc, push32_pcΔ, hf1pc]
  have hf2code : f2.exec.executionEnv.code = frv.exec.executionEnv.code := rfl
  -- RETURN at `f2`: the empty-window halt brick consumes `0 :: 0 :: [vw]`.
  have hdret' : decode f2.exec.executionEnv.code f2.exec.pc
      = some (.System .RETURN, .none) := by rw [hf2code, hf2pc]; exact hdret
  have hf2sz : f2.exec.stack.size ≤ 1024 := by rw [hf2stk]; show (3 : ℕ) ≤ 1024; omega
  have hhalt := halt_ret f2 (vw :: ([] : Stack Word)) hdret' hf2stk hf2sz
  refine ⟨f2, _, ((hmrv.runs.trans hr1).trans hr2), hhalt, ?_⟩
  -- top-level frame facts transport across the two pushes (`pushFrameW` keeps kind/accounts).
  have hf2kind : f2.kind = .call cp := hkind
  have hf2acc : ¬ (f2.exec.accounts == ∅) = true := hne
  -- world channel: observe's world is `f2`'s storage lens = st.world.
  funext key
  show resultStorageAt (endFrame f2 (.success (returnEmptyPost f2.exec (vw :: []))
        (f2.exec.memory.readWithPadding (0 : Word).toNat (0 : Word).toNat))) self key = st.world key
  have hretacc : (returnEmptyPost f2.exec (vw :: ([] : Stack Word))).accounts = f2.exec.accounts := rfl
  rw [resultStorageAt_endFrame_success f2 (returnEmptyPost f2.exec (vw :: []))
        (f2.exec.memory.readWithPadding (0 : Word).toNat (0 : Word).toNat) self key cp
        hf2kind hretacc hf2acc]
  -- storageAt f2 self = selfStorage f2 = selfStorage frv = selfStorage fr = st.world.
  have hf2addr : f2.exec.executionEnv.address = fr.exec.executionEnv.address := by
    rw [hf2, pushFrameW_addr, hf1, pushFrameW_addr]; exact hmrv.addr
  rw [hself, ← hf2addr]
  show selfStorage f2 key = st.world key
  rw [hf2, pushFrameW_selfStorage, hf1, pushFrameW_selfStorage, hmrv.storage key]
  exact hcorr.storage key

/-! ## E2 — `sim_term_edge` (the control-flow terminators `jump` / `branch`)

A block whose terminator is `jump dst` or `branch cond thenL elseL` runs the lowered
control-flow opcodes to the **taken successor block's entry frame**, re-establishing `Corr` at
`(successor, 0)` — the frame the successor block's Layer-D `sim_stmts_block` consumes.

The successor's entry cursor is `pcOf prog succ 0 = offsetTable succ.idx + 1`: the jump lands
on the `JUMPDEST` byte at `offsetTable succ.idx` (E3 `block_offset_validJump`), and the
`JUMPDEST` step (`runs_jumpdest`) advances pc by one to the block body. The destination
resolves (`fr.get_dest dest = some new_pc`) via E3's `validJumpDests` membership, tied to the
frame's `validJumps` (`hvalid`) and the PUSH4 immediate round-trip (`hdestword`). The IR state
`st` is unchanged across the edge, so `DefsSound` / scoping / the realisability ties transport
verbatim (address preserved by every control-flow post-frame). -/

/-- **The successor entry cursor.** `pcOf prog L 0` is the offset-table anchor `offsetTable
… L.idx` plus one (skip the block's leading `JUMPDEST`). -/
theorem pcOf_zero (prog : Program) (L : Label) (b : Block)
    (hb : prog.blocks.toList[L.idx]? = some b) :
    pcOf prog L 0 = offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks L.idx + 1 := by
  rw [pcOf_eq_anchor prog L b 0 hb]; simp

/-- **`Corr` at the JUMPDEST landing.** A frame `fj` sitting on the successor block's
`JUMPDEST` byte (`fj.exec.pc = UInt32.ofNat (offsetTable … succ.idx)`), running the lowered
program, with an empty stack, the modifiable flag, the successor block present, and `fj`'s
self-address / storage lens agreeing with the source `Corr` (carried `st`) — steps the
`JUMPDEST` (`runs_jumpdest`) to `jumpdestFrame fj`, which is in `Corr`-correspondence with the
(unchanged) `st` at the successor's entry cursor `(succ, 0)`. The shared E2 tail. -/
theorem corr_at_jumpdest_landing {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {succ : Label} {bsucc : Block} {fj : Frame}
    (hbsucc : prog.blocks.toList[succ.idx]? = some bsucc)
    (hpc : fj.exec.pc = UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog)
            prog.blocks succ.idx))
    (hcode : fj.exec.executionEnv.code = lower prog)
    (hvalid : fj.validJumps = validJumpDests fj.exec.executionEnv.code 0)
    (hstk : fj.exec.stack = [])
    (hmod : fj.exec.executionEnv.canModifyState = true)
    (hstore : ∀ k, selfStorage fj k = st.world k)
    (hsound : DefsSound prog st)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hmem : MemRealises prog st fj)
    (hdec : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none))
    (hgas : GasConstants.Gjumpdest ≤ fj.exec.gasAvailable.toNat) :
    Runs fj (jumpdestFrame fj) ∧ Corr prog sloadChg obs st (jumpdestFrame fj) succ 0 := by
  have hsz : fj.exec.stack.size ≤ 1024 := by rw [hstk]; show (0 : ℕ) ≤ 1024; omega
  refine ⟨runs_jumpdest fj hdec hsz hgas, ?_⟩
  refine
    { pc_eq := ?_
      code_eq := by rw [jumpdestFrame_code]; exact hcode
      validJumps_eq := by rw [jumpdestFrame_validJumps, jumpdestFrame_code]; exact hvalid
      stack_nil := by rw [jumpdestFrame_stack]; exact hstk
      can_modify := by rw [jumpdestFrame_canMod]; exact hmod
      storage := ?_
      defsSound := hsound
      wellScoped := hscoped
      memAgree := hmem.transport (by rw [jumpdestFrame_memory]) (by rw [jumpdestFrame_activeWords]) }
  · -- pc: (offsetTable succ.idx) + 1 = pcOf prog succ 0.
    rw [jumpdestFrame_pc, hpc, pcOf_zero prog succ bsucc hbsucc, UInt32.ofNat_add]
  · intro key; rw [jumpdestFrame_selfStorage]; exact hstore key


/-- **`PUSH4 dest ; JUMP ; ⟨land⟩ JUMPDEST` to a successor block.** From a frame `g` (running
the lowered program, empty stack, modifiable, address/storage-lens agreeing with the carried
`st`, realisability ties holding) whose `validJumps` are the lowered program's, with the PUSH4
immediate `dest` round-tripping to the successor offset and the three decodes/gas margins,
runs to the successor block `succ`'s entry frame, re-establishing `Corr` at `(succ, 0)`. The
shared tail of E2's `jump` and the `branch` fall-through (`else`) arm. -/
theorem jump_to_block {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {succ : Label} {bsucc : Block} {g : Frame} {dest : Word}
    (hbsucc : prog.blocks.toList[succ.idx]? = some bsucc)
    (hsucclt : succ.idx < prog.blocks.size)
    (hgcode : g.exec.executionEnv.code = lower prog)
    (hgstk : g.exec.stack = [])
    (hgmod : g.exec.executionEnv.canModifyState = true)
    (hgstore : ∀ k, selfStorage g k = st.world k)
    (hsound : DefsSound prog st)
    (hscoped : ∀ t, st.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hmem : MemRealises prog st g)
    (hvalid : g.validJumps = validJumpDests (lower prog) 0)
    (hdestword : dest.toUInt32?
        = some (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks succ.idx)))
    (hdpush : decode g.exec.executionEnv.code g.exec.pc = some (.Push .PUSH4, some (dest, 4)))
    (hdjump : decode g.exec.executionEnv.code (g.exec.pc + UInt32.ofNat 5)
        = some (.Smsf .JUMP, .none))
    (hdjd : decode (lower prog)
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks succ.idx))
        = some (.Smsf .JUMPDEST, .none))
    (hgpush : 3 ≤ g.exec.gasAvailable.toNat)
    (hgjump : GasConstants.Gmid ≤ (pushFrameW g dest 4).exec.gasAvailable.toNat)
    (hgjd : GasConstants.Gjumpdest
        ≤ (jumpFrame (pushFrameW g dest 4) GasConstants.Gmid
            (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks succ.idx))
            g.exec.stack).exec.gasAvailable.toNat) :
    ∃ fr', Runs g fr' ∧ Corr prog sloadChg obs st fr' succ 0 := by
  set new_pc := UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks succ.idx)
    with hnew
  -- step 1: PUSH4 the destination.
  have hstk1 : g.exec.stack.size + 1 ≤ 1024 := by rw [hgstk]; show (0 : ℕ)+1≤1024; omega
  have hpush : Runs g (pushFrameW g dest 4) :=
    runs_push g .PUSH4 dest 4 (by nofun) hdpush rfl rfl hgpush hstk1
  have hpcode : (pushFrameW g dest 4).exec.executionEnv.code = g.exec.executionEnv.code := rfl
  have hppc : (pushFrameW g dest 4).exec.pc = g.exec.pc + UInt32.ofNat 5 := by
    show g.exec.pc + ((4 : UInt8) + 1).toUInt32 = _
    rw [show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide]
  have hpstk : (pushFrameW g dest 4).exec.stack = dest :: g.exec.stack := rfl
  -- step 2: JUMP to new_pc (rest = g's stack = []).
  have hpjdec : decode (pushFrameW g dest 4).exec.executionEnv.code (pushFrameW g dest 4).exec.pc
      = some (.Smsf .JUMP, .none) := by rw [hpcode, hppc]; exact hdjump
  have hpjsz : (pushFrameW g dest 4).exec.stack.size ≤ 1024 := by
    rw [hpstk, hgstk]; show (1 : ℕ) ≤ 1024; omega
  have hgetdest : (pushFrameW g dest 4).get_dest dest = some new_pc := by
    refine Frame.get_dest_of_mem _ hdestword ?_
    show new_pc ∈ g.validJumps
    rw [hvalid, hnew]
    simpa using block_offset_validJump prog succ hsucclt
  have hjump : Runs (pushFrameW g dest 4)
      (jumpFrame (pushFrameW g dest 4) GasConstants.Gmid new_pc g.exec.stack) :=
    runs_jump (pushFrameW g dest 4) dest new_pc g.exec.stack hpjdec hpstk hpjsz hgjump hgetdest
  set fj := jumpFrame (pushFrameW g dest 4) GasConstants.Gmid new_pc g.exec.stack with hfj
  have hfjpc : fj.exec.pc = new_pc := rfl
  have hfjcode : fj.exec.executionEnv.code = lower prog := by
    rw [hfj, jumpFrame_code, hpcode]; exact hgcode
  have hfjstk : fj.exec.stack = [] := by rw [hfj, jumpFrame_stack]; exact hgstk
  have hfjmod : fj.exec.executionEnv.canModifyState = true := by
    rw [hfj, jumpFrame_canMod]; exact hgmod
  have hfjstore : ∀ k, selfStorage fj k = st.world k := by
    intro k; rw [hfj, jumpFrame_selfStorage]; exact hgstore k
  have hfjdec : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
    rw [hfjcode, hfjpc, hnew]; exact hdjd
  have hfjaddr : fj.exec.executionEnv.address = g.exec.executionEnv.address := by
    rw [hfj, jumpFrame_addr]; rfl
  -- the memory value channel survives the PUSH4 + JUMP (neither touches memory/activeWords).
  have hfjmem : MemRealises prog st fj :=
    hmem.transport
      (by rw [hfj, jumpFrame_memory]; rfl)
      (by rw [hfj, jumpFrame_activeWords]; exact le_refl _)
  have hfjvalid : fj.validJumps = validJumpDests fj.exec.executionEnv.code 0 := by
    rw [hfjcode, hfj, jumpFrame_validJumps, pushFrameW_validJumps]; exact hvalid
  obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing (st := st) hbsucc hfjpc hfjcode hfjvalid hfjstk
    hfjmod hfjstore hsound hscoped hfjmem hfjdec (by rw [hfj]; exact hgjd)
  exact ⟨jumpdestFrame fj, (hpush.trans hjump).trans hjdrun, hjdcorr⟩

/-- **`sim_term_edge`, the `jump` arm.** From `Corr` at the terminator cursor `(L,
b.stmts.length)` with `b.term = .jump dst`, running the lowered `PUSH4 (offsetTable dst.idx);
JUMP; ⟨land⟩ JUMPDEST` reaches the successor block's entry frame `fr'`, re-establishing `Corr`
at `(dst, 0)` (the IR state `st` unchanged across the edge — `RunFrom.jump` recurses into
`dst` with the same `st'`). The jump destination resolves through E3
(`block_offset_validJump`): the offset is a recorded `validJumpDests` of `lower prog`, tied to
the frame's `validJumps` (`hvalid`) and the PUSH4 immediate round-trip (`hdestword`). -/
theorem sim_term_edge_jump {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {L : Label} {b : Block} {dst : Label} {bdst : Block}
    {fr : Frame} {dest : Word}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (_hterm : b.term = .jump dst)
    (hbdst : prog.blocks.toList[dst.idx]? = some bdst)
    (hdstlt : dst.idx < prog.blocks.size)
    -- the frame's recorded jump destinations are the lowered program's:
    (hvalid : fr.validJumps = validJumpDests (lower prog) 0)
    -- the PUSH4 immediate round-trips to the successor's offset:
    (hdestword : dest.toUInt32?
        = some (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx)))
    -- decode bundle (PUSH4 dest ; JUMP ; JUMPDEST at the landing):
    (hdpush : decode fr.exec.executionEnv.code fr.exec.pc
        = some (.Push .PUSH4, some (dest, 4)))
    (hdjump : decode fr.exec.executionEnv.code (fr.exec.pc + UInt32.ofNat 5)
        = some (.Smsf .JUMP, .none))
    (hdjd : decode (lower prog)
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
        = some (.Smsf .JUMPDEST, .none))
    -- gas / stack envelopes (honest runtime bounds):
    (hgpush : 3 ≤ fr.exec.gasAvailable.toNat)
    (hgjump : GasConstants.Gmid ≤ (pushFrameW fr dest 4).exec.gasAvailable.toNat)
    (hgjd : GasConstants.Gjumpdest
        ≤ (jumpFrame (pushFrameW fr dest 4) GasConstants.Gmid
            (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks dst.idx))
            fr.exec.stack).exec.gasAvailable.toNat) :
    ∃ fr' L', L' = dst ∧ Runs fr fr' ∧ Corr prog sloadChg obs st fr' L' 0 := by
  obtain ⟨fr', hruns, hcorr'⟩ := jump_to_block (st := st) (g := fr) (dest := dest)
    hbdst hdstlt hcorr.code_eq hcorr.stack_nil hcorr.can_modify hcorr.storage hcorr.defsSound
    hcorr.wellScoped hcorr.memAgree hvalid hdestword hdpush hdjump hdjd
    hgpush hgjump hgjd
  exact ⟨fr', dst, rfl, hruns, hcorr'⟩

/-- **`sim_term_edge`, the `branch` arm.** From `Corr` at the terminator cursor `(L,
b.stmts.length)` with `b.term = .branch cond thenL elseL` and `st.locals cond = some cw`,
running the lowered `materialise cond ; PUSH4 thenOff ; JUMPI ; PUSH4 elseOff ; JUMP ; ⟨land⟩
JUMPDEST` reaches the **taken successor**'s entry frame, re-establishing `Corr` at the taken
`(succ, 0)`: `thenL` when `cw ≠ 0` (the IR `RunFrom.branchThen`), `elseL` when `cw = 0`
(`RunFrom.branchElse`). The condition value comes from B1 `materialise_runs` (`frc`, stack
`[cw]`); the taken arm jumps via `runs_branch` (the CFG combinator); the fall-through arm
JUMPI-falls-through to the `PUSH4 elseOff ; JUMP` and reuses `jump_to_block`. Both successor
destinations resolve through E3 (`block_offset_validJump`). -/
theorem sim_term_edge_branch {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {L : Label} {b : Block} {cond : Tmp} {cw : Word}
    {thenL elseL : Label} {bthen belse : Block}
    {fr frc : Frame} {thenWord elseWord : Word}
    (hcorr : Corr prog sloadChg obs st fr L b.stmts.length)
    (_hterm : b.term = .branch cond thenL elseL)
    (hc : st.locals cond = some cw)
    (hbthen : prog.blocks.toList[thenL.idx]? = some bthen)
    (hbelse : prog.blocks.toList[elseL.idx]? = some belse)
    (hthenlt : thenL.idx < prog.blocks.size)
    (helselt : elseL.idx < prog.blocks.size)
    -- B1: `materialise cond` reaches `frc` (the JUMPI-arg-push site).
    (hmrc : MatRuns (defsOf prog) sloadChg (recomputeFuel prog) (.tmp cond) cw fr frc)
    -- the materialise endpoint's recorded jump destinations are the lowered program's
    -- (the materialise of a pure cond is call-free, so its `Runs` preserves `validJumps`):
    (hfrcvalid : frc.validJumps = validJumpDests (lower prog) 0)
    -- the two PUSH4 immediates round-trip to the successor offsets:
    (hthenword : thenWord.toUInt32?
        = some (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx)))
    (helseword : elseWord.toUInt32?
        = some (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx)))
    -- decode bundle, relative to the post-materialise frame `frc`:
    --   PUSH4 thenOff (at frc.pc) ; JUMPI (at frc.pc+5) ; PUSH4 elseOff (at frc.pc+6) ;
    --   JUMP (at frc.pc+11) ; the two landing JUMPDESTs.
    (hdpushT : decode frc.exec.executionEnv.code frc.exec.pc
        = some (.Push .PUSH4, some (thenWord, 4)))
    (hdjumpi : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 5)
        = some (.Smsf .JUMPI, .none))
    (hdpushE : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 6)
        = some (.Push .PUSH4, some (elseWord, 4)))
    (hdjump : decode frc.exec.executionEnv.code (frc.exec.pc + UInt32.ofNat 6 + UInt32.ofNat 5)
        = some (.Smsf .JUMP, .none))
    (hdjdT : decode (lower prog)
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
        = some (.Smsf .JUMPDEST, .none))
    (hdjdE : decode (lower prog)
        (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
        = some (.Smsf .JUMPDEST, .none))
    -- gas / stack envelopes (honest runtime bounds):
    (hgpushT : 3 ≤ frc.exec.gasAvailable.toNat)
    (hgjumpi : GasConstants.Ghigh ≤ (pushFrameW frc thenWord 4).exec.gasAvailable.toNat)
    -- taken (then) arm: the JUMPDEST landing gas.
    (hgjdT : GasConstants.Gjumpdest
        ≤ (jumpFrame (pushFrameW frc thenWord 4) GasConstants.Ghigh
            (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx))
            ([] : Stack Word)).exec.gasAvailable.toNat)
    -- fall-through (else) arm: PUSH4 elseOff / JUMP / JUMPDEST gas, from the fallthrough frame.
    (hgpushE : 3 ≤ (jumpiFallthroughFrame (pushFrameW frc thenWord 4)
        ([] : Stack Word)).exec.gasAvailable.toNat)
    (hgjumpE : GasConstants.Gmid ≤ (pushFrameW (jumpiFallthroughFrame (pushFrameW frc thenWord 4)
        ([] : Stack Word)) elseWord 4).exec.gasAvailable.toNat)
    (hgjdE : GasConstants.Gjumpdest
        ≤ (jumpFrame (pushFrameW (jumpiFallthroughFrame (pushFrameW frc thenWord 4)
            ([] : Stack Word)) elseWord 4) GasConstants.Gmid
            (UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks elseL.idx))
            (jumpiFallthroughFrame (pushFrameW frc thenWord 4)
              ([] : Stack Word)).exec.stack).exec.gasAvailable.toNat) :
    ∃ fr' L', (cw ≠ 0 ∧ L' = thenL ∨ cw = 0 ∧ L' = elseL)
      ∧ Runs fr fr' ∧ Corr prog sloadChg obs st fr' L' 0 := by
  -- materialise-endpoint facts (`frc` carries `cw` on top of `fr`'s empty stack).
  have hfrcstk : frc.exec.stack = cw :: [] := by rw [hmrc.stack, hcorr.stack_nil]; rfl
  have hfrccode : frc.exec.executionEnv.code = lower prog := by
    rw [hmrc.code]; exact hcorr.code_eq
  have hfrcaddr : frc.exec.executionEnv.address = fr.exec.executionEnv.address := hmrc.addr
  have hfrcmod : frc.exec.executionEnv.canModifyState = true := by
    rw [hmrc.canMod]; exact hcorr.can_modify
  have hfrcstore : ∀ k, selfStorage frc k = st.world k := by
    intro k; rw [hmrc.storage k]; exact hcorr.storage k
  have hfrcmem : MemRealises prog st frc :=
    hcorr.memAgree.transport hmrc.memBytes hmrc.memActive
  -- step: PUSH4 thenOff at `frc`.
  have hstk1 : frc.exec.stack.size + 1 ≤ 1024 := by rw [hfrcstk]; show (1:ℕ)+1≤1024; omega
  have hpushT : Runs frc (pushFrameW frc thenWord 4) :=
    runs_push frc .PUSH4 thenWord 4 (by nofun) hdpushT rfl rfl hgpushT hstk1
  set frp := pushFrameW frc thenWord 4 with hfrp
  have hfrpcode : frp.exec.executionEnv.code = frc.exec.executionEnv.code := rfl
  have hfrppc : frp.exec.pc = frc.exec.pc + UInt32.ofNat 5 := by
    show frc.exec.pc + ((4 : UInt8) + 1).toUInt32 = _
    rw [show ((4 : UInt8) + 1).toUInt32 = UInt32.ofNat 5 from by decide]
  have hfrpstk : frp.exec.stack = thenWord :: cw :: [] := by
    show frc.exec.stack.push thenWord = _; rw [hfrcstk]; rfl
  have hfrpjidec : decode frp.exec.executionEnv.code frp.exec.pc = some (.Smsf .JUMPI, .none) := by
    rw [hfrpcode, hfrppc]; exact hdjumpi
  have hfrpsz : frp.exec.stack.size ≤ 1024 := by rw [hfrpstk]; show (2:ℕ)≤1024; omega
  -- case-split on the runtime condition `cw`.
  by_cases hcw : cw = 0
  · -- ELSE arm: JUMPI falls through to `PUSH4 elseOff ; JUMP ; JUMPDEST` → `elseL`.
    subst hcw
    set gff := jumpiFallthroughFrame frp ([] : Stack Word) with hgff
    have hfall : Runs frp gff :=
      runs_jumpi_fallthrough frp thenWord ([] : Stack Word) hfrpjidec hfrpstk hfrpsz hgjumpi
    -- the fallthrough frame is `jump_to_block`'s entry for the else successor.
    have hgffcode : gff.exec.executionEnv.code = lower prog := by
      rw [hgff, jumpiFallthroughFrame_code, hfrpcode]; exact hfrccode
    have hgffstk : gff.exec.stack = [] := by rw [hgff, jumpiFallthroughFrame_stack]
    have hgffmod : gff.exec.executionEnv.canModifyState = true := by
      rw [hgff, jumpiFallthroughFrame_canMod]
      show (pushFrameW frc thenWord 4).exec.executionEnv.canModifyState = true
      rw [show (pushFrameW frc thenWord 4).exec.executionEnv.canModifyState
            = frc.exec.executionEnv.canModifyState from rfl]; exact hfrcmod
    have hgffstore : ∀ k, selfStorage gff k = st.world k := by
      intro k; rw [hgff, jumpiFallthroughFrame_selfStorage]
      show selfStorage frp k = st.world k
      show selfStorage (pushFrameW frc thenWord 4) k = st.world k
      rw [pushFrameW_selfStorage]; exact hfrcstore k
    have hgffaddr : gff.exec.executionEnv.address = frc.exec.executionEnv.address := by
      rw [hgff, jumpiFallthroughFrame_addr]; rfl
    have hgffmem : MemRealises prog st gff :=
      hfrcmem.transport
        (by rw [hgff, jumpiFallthroughFrame_memory, hfrp, pushFrameW_memory])
        (by rw [hgff, jumpiFallthroughFrame_activeWords, hfrp, pushFrameW_activeWords])
    have hgffvalid : gff.validJumps = validJumpDests (lower prog) 0 := by
      rw [hgff, jumpiFallthroughFrame_validJumps]
      show frp.validJumps = _; rw [hfrp, pushFrameW_validJumps]; exact hfrcvalid
    -- the else PUSH4 sits at `gff.pc = frc.pc + 6`; JUMP at `gff.pc + 5`.
    have hgffpc : gff.exec.pc = frc.exec.pc + UInt32.ofNat 6 := by
      rw [hgff, jumpiFallthroughFrame_pc, hfrppc]
      rw [show (UInt32.ofNat 6) = UInt32.ofNat 5 + 1 from by decide]; ac_rfl
    have hdpushE' : decode gff.exec.executionEnv.code gff.exec.pc
        = some (.Push .PUSH4, some (elseWord, 4)) := by rw [hgffcode, hgffpc, ← hfrccode]; exact hdpushE
    have hdjump' : decode gff.exec.executionEnv.code (gff.exec.pc + UInt32.ofNat 5)
        = some (.Smsf .JUMP, .none) := by rw [hgffcode, hgffpc, ← hfrccode]; exact hdjump
    obtain ⟨fr', hruns', hcorr'⟩ := jump_to_block (st := st) (g := gff) (dest := elseWord)
      hbelse helselt hgffcode hgffstk hgffmod hgffstore hcorr.defsSound hcorr.wellScoped
      hgffmem hgffvalid helseword hdpushE' hdjump' hdjdE
      (by rw [hgff]; exact hgpushE) (by rw [hgff]; exact hgjumpE) (by rw [hgff]; exact hgjdE)
    exact ⟨fr', elseL, Or.inr ⟨rfl, rfl⟩, ((hmrc.runs.trans hpushT).trans hfall).trans hruns', hcorr'⟩
  · -- THEN arm: JUMPI taken jumps to `thenL`'s JUMPDEST.
    set new_pc := UInt32.ofNat (offsetTable (defsOf prog) (recomputeFuel prog) prog.blocks thenL.idx)
      with hnewT
    have hgetdest : frp.get_dest thenWord = some new_pc := by
      refine Frame.get_dest_of_mem _ hthenword ?_
      show new_pc ∈ frp.validJumps
      rw [hfrp, pushFrameW_validJumps, hfrcvalid, hnewT]
      simpa using block_offset_validJump prog thenL hthenlt
    set fj := jumpFrame frp GasConstants.Ghigh new_pc ([] : Stack Word) with hfj
    have htaken : Runs frp fj :=
      runs_jumpi_taken frp thenWord cw new_pc ([] : Stack Word) hfrpjidec
        hfrpstk hfrpsz hgjumpi hcw hgetdest
    -- `fj` is the JUMPDEST landing for `thenL`.
    have hfjpc : fj.exec.pc = new_pc := rfl
    have hfjcode : fj.exec.executionEnv.code = lower prog := by
      rw [hfj, jumpFrame_code, hfrpcode]; exact hfrccode
    have hfjstk : fj.exec.stack = [] := by rw [hfj, jumpFrame_stack]
    have hfjmod : fj.exec.executionEnv.canModifyState = true := by
      rw [hfj, jumpFrame_canMod]
      show (pushFrameW frc thenWord 4).exec.executionEnv.canModifyState = true
      rw [show (pushFrameW frc thenWord 4).exec.executionEnv.canModifyState
            = frc.exec.executionEnv.canModifyState from rfl]; exact hfrcmod
    have hfjstore : ∀ k, selfStorage fj k = st.world k := by
      intro k; rw [hfj, jumpFrame_selfStorage]
      show selfStorage (pushFrameW frc thenWord 4) k = st.world k
      rw [pushFrameW_selfStorage]; exact hfrcstore k
    have hfjdec : decode fj.exec.executionEnv.code fj.exec.pc = some (.Smsf .JUMPDEST, .none) := by
      rw [hfjcode, hfjpc, hnewT]; exact hdjdT
    have hfjmem : MemRealises prog st fj :=
      hfrcmem.transport
        (by rw [hfj, jumpFrame_memory, hfrp, pushFrameW_memory])
        (by rw [hfj, jumpFrame_activeWords, hfrp, pushFrameW_activeWords])
    have hfjvalid : fj.validJumps = validJumpDests fj.exec.executionEnv.code 0 := by
      rw [hfjcode, hfj, jumpFrame_validJumps, hfrp, pushFrameW_validJumps]; exact hfrcvalid
    obtain ⟨hjdrun, hjdcorr⟩ := corr_at_jumpdest_landing (st := st) hbthen hfjpc hfjcode hfjvalid
      hfjstk hfjmod hfjstore hcorr.defsSound hcorr.wellScoped hfjmem hfjdec
      (by rw [hfj]; exact hgjdT)
    exact ⟨jumpdestFrame fj, thenL, Or.inl ⟨hcw, rfl⟩,
      ((hmrc.runs.trans hpushT).trans htaken).trans hjdrun, hjdcorr⟩

end Lir

-- Build-enforced axiom-cleanliness guard for the E-layer `sim_term` deliverables: the two
-- halting terminators (`stop` fully; `ret` on the world channel — value deferred) and the
-- two control-flow edges (`jump`/`branch`) depend only on `[propext, Classical.choice,
-- Quot.sound]`.
#print axioms Lir.sim_term_halt_stop
#print axioms Lir.sim_term_halt_ret
#print axioms Lir.sim_term_edge_jump
#print axioms Lir.sim_term_edge_branch
