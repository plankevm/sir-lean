import LirLean.MaterialiseRuns
import LirLean.V2.CallRealises

/-!
# LirLean — `sim_stmt` (Layer **C** of the general `lower_conforms` grind)

Per-statement simulation: one IR `EvalStmt` step is matched, on the bytecode side, by
the `Runs` segment of that statement's lowered bytes. From a frame in *correspondence*
with the V2 IR state, running the statement's lowered opcodes reaches a frame in
correspondence with the post-`EvalStmt` IR state, advancing one statement position
(`pcOf prog L pc → pcOf prog L (pc+1)`) and returning the working stack to empty (`M5`).

This is the C-layer brick that the program-global engine `lower_simulates_step` threads
with `Runs.trans`. It sits *above* B1 (`materialise_runs`, the expression linchpin) and
B3 (`DefsSound`, recompute-soundness), wiring them through the per-construct bytecode
shape (`emitStmt`, `LirLean/Lowering.lean`) into the per-statement step.

## The state-correspondence bundle `Corr`

`Corr prog sloadChg obs st fr L pc` is the invariant the induction carries. It is the
V2-native fusion of:

* `Match`'s clauses, restated for the V2 `IRState` (`.world`/`.locals`) the gas-free
  machine carries: `M1` pc (`fr.exec.pc = pcOf prog L pc`), `M2` code
  (`= lower prog`), `M5` stack-nil, and the standing `canModifyState`;
* `M3` storage through `StorageAgree` (`selfStorage fr key = st.world key`, the
  `find?/lookupStorage` lens both sides read);
* `DefsSound prog st` (B3) — recompute-on-use soundness;
* the **B1 realisability side-conditions** `SloadRealises sloadChg st fr` /
  `GasRealises obs fr` — the honest runtime ties (SLOAD warmth-cost, GAS value) the
  realised trace supplies, threaded so the `materialise_runs` calls discharge.

The bundle is *re-establishable at `pc+1`*: each arm shows the post-frame satisfies
`Corr … st' fr' L (pc+1)`. The pc advance is `pcOf_succ` (one more statement's
`emitStmt` length); the storage/realisability transports come from `MatRuns`'s
`.addr`/`.storage` clauses, exactly as B1's recursion threads them.

## The three arms

* **`assign t e`** — `emitStmt … (.assign _ _) = []`, so the `Runs` segment is
  `Runs.refl`; the work is re-establishing `Corr` under `setLocal t (evalExpr…e)` via
  **B3** (`defsSound_preserved_assignPure` / `assignGas`). The pc still advances
  (`pcOf_succ` with the zero-length emit) and the stack is untouched (still `[]`).
* **`sstore key value`** — lowered `materialise value ++ materialise key ++ [SSTORE]`:
  two **B1** `materialise_runs` calls (`.tmp value`, `.tmp key`) glued by `Runs.trans`,
  then `sim_sstore`. Re-establishes the `M3` lens at the written cell; `DefsSound`
  survives the write by **B3** `defsSound_preserved_sstore`.
* **`call cs`** — lowered `5×(PUSH 0) ++ materialise callee ++ materialise gasFwd ++
  [CALL]` → a `Runs.call` node (`sim_call`) carrying a `CallReturns` witness; the IR
  `EvalStmt.call` applies the oracle bundle, tied to the `CallReturns` via
  `callRealises_bridge`. `DefsSound` survives by **B3** `defsSound_preserved_call`.

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `Match.lean` via
`MaterialiseRuns.lean`); nothing here touches `V2/Machine.lean` / `V2/Law.lean`.
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch
open Lir.V2

/-! ## The statement-cursor pc advance

`pcOf prog L (pc+1) = pcOf prog L pc + (emitStmt … s).length` when statement `s` sits
at cursor `(L, pc)`. The offset-table anchor is a prefix sum over `b.stmts.take pc`;
taking one more statement appends exactly `emitStmt … s`'s bytes. This is the M1
advance every arm re-establishes. -/

/-- **The statement-cursor pc advance.** For statement `s` at cursor `(L, pc)`, the next
cursor's byte offset is the current one plus `s`'s emitted byte length. -/
theorem pcOf_succ (prog : Program) (L : Label) (b : Block) (pc : Nat) (s : Stmt)
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some s) :
    pcOf prog L (pc + 1)
      = pcOf prog L pc + (emitStmt (defsOf prog) (recomputeFuel prog) s).length := by
  rw [pcOf_eq_anchor prog L b (pc + 1) hb, pcOf_eq_anchor prog L b pc hb]
  set defs := defsOf prog
  set fuel := recomputeFuel prog
  have hlt : pc < b.stmts.length := by
    rcases Nat.lt_or_ge pc b.stmts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none_iff.mpr h] at hs; exact absurd hs (by simp)
  have hget : b.stmts[pc] = s := by
    have h2 := List.getElem?_eq_getElem hlt; rw [h2] at hs; exact Option.some.inj hs
  have htake : b.stmts.take (pc + 1) = b.stmts.take pc ++ [s] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, hget]; rfl
  rw [htake, List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  omega

/-! ## The state-correspondence bundle -/

/-- **The per-statement state-correspondence invariant.** Relates a running V2 IR state
`st` to an EVM frame `fr` at statement cursor `(L, pc)`, carrying the B1 realisability
ties (`sloadChg`/`obs`) so the `materialise_runs` calls discharge. See the module
docstring for the clause meanings. -/
structure Corr (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) (L : Label) (pc : Nat) : Prop where
  /-- `M1` — program counter at the offset-table address of cursor `(L, pc)`. -/
  pc_eq      : fr.exec.pc = UInt32.ofNat (pcOf prog L pc)
  /-- `M2` — the frame runs the lowered program. -/
  code_eq    : fr.exec.executionEnv.code = lower prog
  /-- `M2′` — the frame's recorded jump destinations are those of its own code. This is
  a frame-invariant: `validJumps` is set once at frame creation from `code` (`codeFrame`)
  and every non-call step preserves both fields together. Combined with `code_eq` it
  discharges the `validJumps = validJumpDests (lower prog) 0` control-flow ties
  structurally (see `Corr.validJumps_lower`). -/
  validJumps_eq : fr.validJumps = validJumpDests fr.exec.executionEnv.code 0
  /-- `M5` — empty working stack at the statement boundary. -/
  stack_nil  : fr.exec.stack = []
  /-- Standing well-formedness: the call may modify state (top-level call). -/
  can_modify : fr.exec.executionEnv.canModifyState = true
  /-- `M3` — storage correspondence through the observable lens. -/
  storage    : StorageAgree st fr
  /-- B3 — recompute-on-use soundness. -/
  defsSound  : DefsSound prog st
  /-- Define-before-use scoping: every currently-bound tmp is recomputable and present
  in the recompute environment (the `WellScoped` content `materialise_runs` consumes). -/
  wellScoped : ∀ t, st.locals t ≠ none → ¬ NonRecomputable prog t ∧ defsOf prog t ≠ none
  /-- B1 — SLOAD warmth-cost realisability. -/
  sloadReal  : SloadRealises sloadChg st fr
  /-- B1 — GAS value realisability. -/
  gasReal    : GasRealises obs fr

/-- **`validJumps` discharge.** From `Corr`, the frame's `validJumps` are exactly those of
`lower prog` — `validJumpDests (lower prog) 0`. Combines the frame-invariant `validJumps_eq`
(`validJumps = validJumpDests code 0`) with `code_eq` (`code = lower prog`). This is the
structural discharge of the former `validJumps`-recording ties of `TermTies`. -/
theorem Corr.validJumps_lower {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {fr : Frame} {L : Label} {pc : Nat}
    (hcorr : Corr prog sloadChg obs st fr L pc) :
    fr.validJumps = validJumpDests (lower prog) 0 := by
  rw [hcorr.validJumps_eq, hcorr.code_eq]

/-! ## `emitStmt`/byte-length reductions for the three statement shapes -/

/-- `assign` emits no bytes. -/
@[simp] theorem emitStmt_assign (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) (e : Expr) :
    emitStmt defs fuel (.assign t e) = [] := rfl

/-- `sstore` lowers to `materialise value ++ materialise key ++ [SSTORE]`. -/
@[simp] theorem emitStmt_sstore (defs : Tmp → Option Expr) (fuel : Nat) (key value : Tmp) :
    emitStmt defs fuel (.sstore key value)
      = materialiseExpr defs fuel (.tmp value) ++ materialiseExpr defs fuel (.tmp key)
        ++ [Byte.sstore] := rfl

/-! ## Arm 1 — `assign t e`

`emitStmt … (.assign t e) = []`, so the lowered segment is `Runs.refl fr`: the frame is
unchanged (pc included — the next cursor's byte offset is the same, `pcOf_succ` with a
zero-length emit). The IR step binds `t := w` (`setLocal`), leaving the world untouched,
so `M1`/`M2`/`M3`/`M5`/`canModify` survive verbatim and `DefsSound` is re-established by
**B3** (`defsSound_preserved_assignPure` / `assignGas`). The post-state realisability
ties (`SloadRealises`/`GasRealises` over `st'`) are the honest downstream-supplied
side-conditions, threaded in as for `materialise_runs`. -/

/-- **`sim_stmt`, the `assign` arm.** From `Corr` at `(L, pc)` and an `EvalStmt` step of
`assign t e`, the *same* frame `fr` is in correspondence with the post-state `st'` at
cursor `(L, pc+1)`: the lowered segment is empty (`Runs.refl`), the working stack stays
`[]`. Given the per-step B3 scoping (`StepScoped`) and the post-state realisability ties.
-/
theorem sim_assign {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {t : Tmp} {e : Expr}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t e))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hstep : EvalStmt prog o st T (.assign t e) st' T')
    (hsc : StepScoped prog st (.assign t e))
    (hscoped' : ∀ t, st'.locals t ≠ none → ¬ NonRecomputable prog t ∧ defsOf prog t ≠ none)
    (hsload' : SloadRealises sloadChg st' fr)
    (hgas' : GasRealises obs fr) :
    Runs fr fr ∧ Corr prog sloadChg obs st' fr L (pc + 1) ∧ fr.exec.stack = [] := by
  refine ⟨Runs.refl fr, ?_, hcorr.stack_nil⟩
  -- pc advance: emitStmt of assign is empty, so the next cursor coincides.
  have hpc : pcOf prog L (pc + 1) = pcOf prog L pc := by
    rw [pcOf_succ prog L b pc (.assign t e) hb hs, emitStmt_assign]; simp
  -- DefsSound survives via B3.
  have hsound' : DefsSound prog st' := defsSound_preserved hstep hsc hcorr.defsSound
  -- world is untouched by the assign (both arms only setLocal), so M3 survives.
  have hworld : st'.world = st.world := by
    cases hstep with
    | assignPure _ _ => rfl
    | assignGas       => rfl
  refine
    { pc_eq := by rw [hcorr.pc_eq, hpc]
      code_eq := hcorr.code_eq
      validJumps_eq := hcorr.validJumps_eq
      stack_nil := hcorr.stack_nil
      can_modify := hcorr.can_modify
      storage := ?_
      defsSound := hsound'
      wellScoped := hscoped'
      sloadReal := hsload'
      gasReal := hgas' }
  intro key
  rw [hworld]; exact hcorr.storage key

/-! ## `selfStorage`/`storageAt` bridge

`selfStorage fr key` is `storageAt fr fr.exec.executionEnv.address key` definitionally —
the same `find?/lookupStorage` lens at the frame's self address. The `sim_sstore` clauses
are stated through `storageAt fr fr.exec.executionEnv.address`; this is the bridge to the
`StorageAgree`/`selfStorage` form `Corr` carries. -/

/-- `selfStorage` is `storageAt` at the frame's own self address (definitional). -/
theorem selfStorage_eq_storageAt (fr : Frame) (key : Word) :
    selfStorage fr key = storageAt fr fr.exec.executionEnv.address key := rfl

/-! ### `sstoreFrame` accessor reductions

`State.sstore` writes one account's storage and bumps the substate; it leaves the
`executionEnv` (hence code / address / canModifyState) untouched. `sstoreFrame` then
`replaceStackAndIncrPC`s — replacing the stack with `rest`, advancing pc by one. These
reductions expose exactly the `Corr` clauses the SSTORE post-frame must re-establish. -/

/-- `State.sstore` preserves the `executionEnv` (it only touches accounts + substate). -/
theorem sstore_executionEnv (s : Evm.State) (k v : Word) :
    (s.sstore k v).executionEnv = s.executionEnv := by
  unfold Evm.State.sstore; simp only [Option.option]; split <;> rfl

@[simp] theorem sstoreFrame_code (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.executionEnv.code = fr.exec.executionEnv.code := by
  show (fr.exec.sstore key value).executionEnv.code = fr.exec.executionEnv.code
  rw [sstore_executionEnv]

@[simp] theorem sstoreFrame_validJumps (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).validJumps = fr.validJumps := rfl

@[simp] theorem sstoreFrame_addr (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.executionEnv.address = fr.exec.executionEnv.address := by
  show (fr.exec.sstore key value).executionEnv.address = fr.exec.executionEnv.address
  rw [sstore_executionEnv]

@[simp] theorem sstoreFrame_canMod (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := by
  show (fr.exec.sstore key value).executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  rw [sstore_executionEnv]

@[simp] theorem sstoreFrame_pc (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.pc = fr.exec.pc + (1 : UInt8).toUInt32 := by
  simp [sstoreFrame, sstorePost, Evm.ExecutionState.replaceStackAndIncrPC]

@[simp] theorem sstoreFrame_stack (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.stack = rest := by
  simp [sstoreFrame, sstorePost, Evm.ExecutionState.replaceStackAndIncrPC]

/-! ## The SSTORE realisability side-condition

`sim_sstore`'s runtime preconditions — the `Gcallstipend` gate, the EIP-2200 charge bound,
and the self account being present — hold at the *internal* SSTORE frame `frk` (reached
after materialising `value` then `key`). Following the B1 pattern (`SloadRealises`), we
package them as one honest side-condition `SstoreRealises`, quantified over the frame so it
applies at `frk`. The frame is pinned by its self-address (carried by `MatRuns.addr`),
write operands, and the witnessing account. -/

/-- The SSTORE runtime realisability: at every frame `g` sharing `fr`'s self-address, the
EIP-2200 charge fits the available gas, the `Gcallstipend` gate is open, and the self
account `acc` is present. The honest runtime tie at the internal SSTORE frame. -/
def SstoreRealises (fr : Frame) (kw vw : Word) (acc : Account) : Prop :=
  ∀ (g : Frame),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    g.exec.stack = kw :: vw :: [] →
    (¬ g.exec.gasAvailable.toNat ≤ GasConstants.Gcallstipend)
    ∧ sstoreChargeOf g.exec kw vw ≤ g.exec.gasAvailable.toNat
    ∧ g.exec.accounts.find? g.exec.executionEnv.address = some acc

/-! ## Arm 2 — `sstore key value`

Lowered `materialise value ++ materialise key ++ [SSTORE]`. Two **B1** `materialise_runs`
calls — `.tmp value` from `fr` (leaving `[vw]`), then `.tmp key` from the result
(leaving `[kw, vw]` = `kw :: vw :: []`, the shape `sim_sstore` consumes) — glued by
`Runs.trans`, then the `SSTORE` step. The IR step writes `st.setStorage kw vw`; the `M3`
lens is re-established at the written cell from `sim_sstore`'s self-storage clauses, and
`DefsSound` survives the write by **B3** `defsSound_preserved_sstore`.

The decode bundle is taken as `MatDec` hypotheses at the static cursors (as every B1 leaf
takes its `hdec`), transported to the produced frames via `MatRuns.code`/`.pc`. The gas
and stack envelopes for the two materialise calls and the SSTORE charge are honest runtime
side-conditions (`SstoreRealises`, the `SloadRealises` analogue). -/

/-- **`sim_stmt`, the `sstore` arm.** From `Corr` at `(L, pc)` and an `EvalStmt.sstore`
step, running the lowered `materialise value ; materialise key ; SSTORE` reaches a frame
`fr'` in correspondence with `st.setStorage kw vw` at cursor `(L, pc+1)`, with the working
stack back to `[]`. -/
theorem sim_sstore_stmt {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st : V2.IRState} {key value : Tmp} {kw vw : Word}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame} {acc : Account}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.sstore key value))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hk : st.locals key = some kw) (hv : st.locals value = some vw)
    (hsc : StepScoped prog st (.sstore key value))
    -- decode bundle at the static cursors (Layer A discharges this over `lower prog`):
    (hdv : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
            fr.exec.pc (.tmp value))
    (hdk : MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg (recomputeFuel prog)
            (fr.exec.pc + UInt32.ofNat
              (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length) (.tmp key))
    (hdop : decode fr.exec.executionEnv.code
            (fr.exec.pc
              + UInt32.ofNat (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp value)).length
              + UInt32.ofNat (materialiseExpr (defsOf prog) (recomputeFuel prog) (.tmp key)).length)
            = some (.Smsf .SSTORE, .none))
    -- gas / stack envelopes (honest runtime bounds):
    (hgas : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).sum
              + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).sum
              ≤ fr.exec.gasAvailable.toNat)
    (hstk : (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp value)).length
              + (chargeOf (defsOf prog) sloadChg (recomputeFuel prog) (.tmp key)).length
              + 1 ≤ 1024)
    (hsstore : SstoreRealises fr kw vw acc) (hnz : vw ≠ 0) :
    ∃ fr', Runs fr fr'
      ∧ Corr prog sloadChg obs (st.setStorage kw vw) fr' L (pc + 1)
      ∧ fr'.exec.stack = [] := by
  classical
  set defs := defsOf prog with hdefs
  set fuel := recomputeFuel prog with hfuel
  -- abbreviations for the two materialise lengths / charges
  set lv := (materialiseExpr defs fuel (.tmp value)).length with hlv
  set lk := (materialiseExpr defs fuel (.tmp key)).length with hlk
  have hstacknil := hcorr.stack_nil
  -- == B1 call 1: materialise `value` from `fr`, leaving `[vw]` ==
  have hevv : V2.evalExpr st obs (.tmp value) = some vw := hv
  have hgasv : (chargeOf defs sloadChg fuel (.tmp value)).sum ≤ fr.exec.gasAvailable.toNat := by
    omega
  have hszfr : fr.exec.stack.size = 0 := by rw [hstacknil]; rfl
  have hstkv : fr.exec.stack.size + (chargeOf defs sloadChg fuel (.tmp value)).length ≤ 1024 := by
    rw [hszfr]; omega
  obtain ⟨frv, hmrv⟩ := materialise_runs sloadChg fuel st obs (.tmp value) vw fr
    hdv hcorr.defsSound hcorr.wellScoped hcorr.storage hcorr.sloadReal hcorr.gasReal
    hevv hgasv hstkv
  -- frv facts
  have hvcode : frv.exec.executionEnv.code = fr.exec.executionEnv.code := hmrv.code
  have hvaddr : frv.exec.executionEnv.address = fr.exec.executionEnv.address := hmrv.addr
  have hvpc : frv.exec.pc = fr.exec.pc + UInt32.ofNat lv := hmrv.pc
  have hvstk : frv.exec.stack = vw :: fr.exec.stack := by rw [hmrv.stack]; rfl
  -- == B1 call 2: materialise `key` from `frv`, leaving `[kw, vw]` ==
  have hevk : V2.evalExpr st obs (.tmp key) = some kw := hk
  have hdk' : MatDec frv.exec.executionEnv.code defs sloadChg fuel frv.exec.pc (.tmp key) := by
    rw [hvcode, hvpc]; exact hdk
  have hgask : (chargeOf defs sloadChg fuel (.tmp key)).sum ≤ frv.exec.gasAvailable.toNat := by
    rw [hmrv.gasToNat]
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact hgas)
  have hfrvsz : frv.exec.stack.size = fr.exec.stack.size + 1 := by rw [hvstk]; simp
  have hstkk : frv.exec.stack.size + (chargeOf defs sloadChg fuel (.tmp key)).length ≤ 1024 := by
    rw [hfrvsz, hszfr]; omega
  obtain ⟨frk, hmrk⟩ := materialise_runs sloadChg fuel st obs (.tmp key) kw frv
    hdk' hcorr.defsSound hcorr.wellScoped
    (hcorr.storage.transport hmrv.storage) (hcorr.sloadReal.transport hmrv.addr)
    (hcorr.gasReal.transport hmrv.addr) hevk hgask hstkk
  -- frk facts
  have hkcode : frk.exec.executionEnv.code = fr.exec.executionEnv.code := by
    rw [hmrk.code, hvcode]
  have hkvalid : frk.validJumps = fr.validJumps := by
    rw [hmrk.validJumps, hmrv.validJumps]
  have hkaddr : frk.exec.executionEnv.address = fr.exec.executionEnv.address := by
    rw [hmrk.addr, hvaddr]
  have hkpc : frk.exec.pc = fr.exec.pc + UInt32.ofNat lv + UInt32.ofNat lk := by
    rw [hmrk.pc, hvpc]
  have hkstk : frk.exec.stack = kw :: vw :: [] := by
    rw [hmrk.stack, hvstk, hstacknil]; rfl
  -- the SSTORE step at `frk`
  have hkdec : decode frk.exec.executionEnv.code frk.exec.pc = some (.Smsf .SSTORE, .none) := by
    rw [hkcode, hkpc]; exact hdop
  have hksz : frk.exec.stack.size ≤ 1024 := by rw [hkstk]; simp
  have hkmod : frk.exec.executionEnv.canModifyState = true := by
    rw [hmrk.canMod, hmrv.canMod]; exact hcorr.can_modify
  obtain ⟨hstip, hcost, hself⟩ := hsstore frk hkaddr hkstk
  obtain ⟨hsrun, hswrite, hsframe⟩ :=
    sim_sstore frk kw vw [] acc hkdec hkstk hksz hkmod hstip hcost hself hnz
  -- assemble the Runs and re-establish Corr
  refine ⟨sstoreFrame frk kw vw [], (hmrv.runs.trans hmrk.runs).trans hsrun, ?_, ?_⟩
  · -- re-establish `Corr` at `(L, pc+1)` for `st.setStorage kw vw`.
    -- the post-frame's self address coincides with `frk`'s (sstoreFrame preserves env).
    have hfraddr : (sstoreFrame frk kw vw []).exec.executionEnv.address
        = frk.exec.executionEnv.address := sstoreFrame_addr frk kw vw []
    -- M1: pc advance.
    have hemit : (emitStmt defs fuel (.sstore key value)).length = lv + lk + 1 := by
      rw [emitStmt_sstore]; simp only [List.length_append, List.length_singleton, hlv, hlk]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (lv + lk + 1) := by
      rw [pcOf_succ prog L b pc (.sstore key value) hb hs, hemit]
    refine
      { pc_eq := ?_
        code_eq := ?_
        validJumps_eq := ?_
        stack_nil := by rw [sstoreFrame_stack]
        can_modify := by rw [sstoreFrame_canMod, hkmod]
        storage := ?_
        defsSound := ?_
        wellScoped := ?_
        sloadReal := ?_
        gasReal := ?_ }
    · -- pc: (fr.pc + lv + lk) + 1 = ofNat (pcOf + (lv+lk+1)).
      rw [sstoreFrame_pc, hkpc, hcorr.pc_eq, hpcN,
          show ((1 : UInt8).toUInt32) = UInt32.ofNat 1 from rfl,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add]
      ac_rfl
    · rw [sstoreFrame_code, hkcode]; exact hcorr.code_eq
    · -- M2′: validJumps tracks the (unchanged) code, threaded through frk and the SSTORE frame.
      rw [sstoreFrame_validJumps, sstoreFrame_code, hkvalid, hkcode]; exact hcorr.validJumps_eq
    · -- M3 at the written cell.
      intro keyw
      rw [selfStorage_eq_storageAt, hfraddr]
      show storageAt (sstoreFrame frk kw vw []) frk.exec.executionEnv.address keyw
        = (st.setStorage kw vw).world keyw
      by_cases hk0 : keyw = kw
      · subst hk0
        rw [hswrite]
        show vw = (if keyw = keyw then vw else st.world keyw)
        simp
      · rw [hsframe keyw hk0]
        show storageAt frk frk.exec.executionEnv.address keyw
          = (st.setStorage kw vw).world keyw
        rw [show storageAt frk frk.exec.executionEnv.address keyw = selfStorage frk keyw from rfl,
            hmrk.storage keyw, hmrv.storage keyw, hcorr.storage keyw]
        show st.world keyw = (if keyw = kw then vw else st.world keyw)
        simp [hk0]
    · -- B3: DefsSound survives the storage write (no live recomputable sload across it).
      exact defsSound_preserved_sstore hsc hcorr.defsSound
    · -- wellScoped: setStorage leaves `locals` untouched.
      intro tw htw
      exact hcorr.wellScoped tw (by simpa [V2.IRState.setStorage] using htw)
    · -- SLOAD realisability over the post-state/post-frame: setStorage leaves `locals`
      -- untouched, and the post-frame shares `fr`'s self address.
      intro g kt keyk hgaddr hloc
      have hloc' : st.locals kt = some keyk := by simpa [V2.IRState.setStorage] using hloc
      have hgaddr' : g.exec.executionEnv.address = fr.exec.executionEnv.address := by
        rw [hgaddr, hfraddr, hkaddr]
      exact hcorr.sloadReal g kt keyk hgaddr' hloc'
    · -- GAS realisability over the post-frame: same self address as `fr`.
      intro g hgaddr
      have hgaddr' : g.exec.executionEnv.address = fr.exec.executionEnv.address := by
        rw [hgaddr, hfraddr, hkaddr]
      exact hcorr.gasReal g hgaddr'
  · rw [sstoreFrame_stack]

/-! ## Arm 3 — `call cs` (the `Runs.call` node)

A `Stmt.call` lowers to `5×(PUSH 0) ++ materialise callee ++ materialise gasFwd ++ [CALL]`.
Under lowering it is a `Runs.call` node carrying a `CallReturns callFr resumeFr` witness
(the CALL step, the child entering as code, the black-box child run, the resumed parent).
The IR `EvalStmt.call` queries the oracle and applies its `(world', success)` bundle.

We instantiate the abstract oracle to the **realised** `evmV2CallOracle result pd self`
(`LirLean/V2/CallRealises.lean`), whose output `callRealises_bridge` ties to the lowered
CALL's observable effect: `world' = storageAt resumeFr self` (the `M3` lens) and
`success = callSuccessFlag result pd` (exp003's CALL flag `x`). With that tie the post-
`EvalStmt` IR world *is* the resumed frame's storage lens, so `M3` (`StorageAgree`) is
re-established at `resumeFr`; `DefsSound` survives the world-replacement + result-binding
by **B3** `defsSound_preserved_call`; code/canModifyState are preserved by
`resumeAfterCall` (it keeps the caller's `executionEnv`).

### Scope (the documented stack/pc gap)

Two `Corr` clauses are **not** re-established at `resumeFr` and are reported here as a
precise, honest gap rather than papered over:

* **`stack_nil` (M5)** — the lowered CALL leaves its 0/1 success flag *on the bytecode
  stack* (`resumeFr.exec.stack = callSuccessFlag result pd :: pd.stack`, and `pd.stack`
  is the suspended stack below the seven CALL args). The IR side folds that flag into
  state (the oracle bundle / `resultTmp`), keeping its own stack empty — but the *lowered*
  bytecode has no POP / consuming opcode for it. Re-establishing `M5` needs the lowering
  to bind/consume the flag (the `resultTmp`-binding lowering-completeness follow-up flagged
  in `LirLean/Call.lean` §5 and `LirLean/Match.lean`).
* **`pc_eq` (M1)** — `resumeAfterCall` sets `resumeFr.exec.pc = pd.frame.exec.pc + 1`,
  pinned by the CALL step's `pending.frame` pc; relating that to `pcOf prog L (pc+1)`
  requires the CALL-site pc bookkeeping, which is the same Layer-A offset arithmetic the
  arg-push hypothesis already abstracts.

So this arm delivers the **call-effect correspondence** `CorrCall` — code / canModifyState
/ `M3` storage / `DefsSound` / scoping / the B1 realisability ties — fully and axiom-cleanly
at `resumeFr`, with the success word tied to the bytecode flag, under the realised
`CallReturns`. The two omitted clauses are the lowering-completeness gap above. -/

/-- The **call-effect correspondence**: the `Corr` clauses re-establishable at the resumed
frame after an external CALL — everything except `pc_eq` (M1) and `stack_nil` (M5), which
are the documented lowering-completeness gap (the success flag is left on the bytecode
stack; the resume pc is `resumeAfterCall`'s, not yet tied to `pcOf`). -/
structure CorrCall (prog : Program) (sloadChg : Tmp → ℕ) (obs : Word)
    (st : V2.IRState) (fr : Frame) : Prop where
  code_eq    : fr.exec.executionEnv.code = lower prog
  can_modify : fr.exec.executionEnv.canModifyState = true
  storage    : StorageAgree st fr
  defsSound  : DefsSound prog st
  wellScoped : ∀ t, st.locals t ≠ none → ¬ NonRecomputable prog t ∧ defsOf prog t ≠ none
  sloadReal  : SloadRealises sloadChg st fr
  gasReal    : GasRealises obs fr

/-- **`sim_stmt`, the `call` arm (strongest closed form).** Let `callFr` be the CALL-site
frame reached from `fr` by running the lowered CALL-argument pushes (the assembled
`Runs fr callFr`, with `callFr` preserving `fr`'s self address `self`, code, canModifyState
and storage lens — the `materialise_runs` arg chain). Given a returning external CALL
(`CallReturns callFr resumeFr`) and the IR step taken under the **realised** oracle
`evmV2CallOracle result pd self` (so `resumeFr = resumeAfterCall result pd`), the whole
call is one `Runs fr resumeFr` (a `Runs.call` node), and the post-`EvalStmt` IR state is in
**call-effect correspondence** `CorrCall` with `resumeFr`: its world is the resumed frame's
storage lens (`M3`), `DefsSound` survives (B3), and the bound success flag is exactly
exp003's `callSuccessFlag result pd`. (The `pc_eq`/`stack_nil` clauses are the documented
gap — see the section docstring.) -/
theorem sim_call_stmt {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : V2.IRState} {T : Trace} {cs : CallSpec} {calleeW gasFwdW : Word}
    {fr callFr resumeFr : Frame} {result : Evm.CallResult} {pd : Evm.PendingCall}
    {self : AccountAddress}
    -- the assembled CALL-argument push run:
    (hargs : Runs fr callFr)
    (_hself : self = fr.exec.executionEnv.address)
    -- the returning external CALL and the realised-oracle IR step:
    (hcall : CallReturns callFr resumeFr)
    (hresume : resumeFr = Evm.resumeAfterCall result pd)
    (_hcallee : st.locals cs.callee = some calleeW)
    (_hgasfwd : st.locals cs.gasFwd = some gasFwdW)
    (hstep : EvalStmt prog (evmV2CallOracle result pd self) st T (.call cs) st' T)
    -- realised-call frame pins (resumeAfterCall keeps the caller's executionEnv; the caller
    -- is our lowered top-level frame — honest properties of the realised returning call):
    (hresaddr : resumeFr.exec.executionEnv.address = self)
    (hrescode : resumeFr.exec.executionEnv.code = lower prog)
    (hrescanmod : resumeFr.exec.executionEnv.canModifyState = true)
    -- standing B3 / per-step scoping of `st`:
    (hdefs : DefsSound prog st)
    (hsc : StepScoped prog st (.call cs))
    -- the post-state scoping/realisability (downstream-supplied, as in `materialise_runs`):
    (hscoped' : ∀ t, st'.locals t ≠ none → ¬ NonRecomputable prog t ∧ defsOf prog t ≠ none)
    (hsload' : SloadRealises sloadChg st' resumeFr)
    (hgas' : GasRealises obs resumeFr) :
    Runs fr resumeFr
      ∧ CorrCall prog sloadChg obs st' resumeFr
      ∧ (∀ t, cs.resultTmp = some t → st'.locals t = some (callSuccessFlag result pd)) := by
  classical
  -- == the Runs: arg pushes then the returning CALL node ==
  have hruns : Runs fr resumeFr := hargs.trans (sim_call hcall (Runs.refl resumeFr))
  -- the realised oracle's projections (`callRealises_bridge`, here `rfl`-clean for the
  -- concrete `result pd` from `hresume`): `successWord = callSuccessFlag` (the §5 reflexivity),
  -- and `postStorage result pd self = storageAt (resumeAfterCall result pd) self` by construction.
  have hsuccW : evmCallOracle.successWord result pd = callSuccessFlag result pd :=
    evmCallOracle_successWord_eq_x result pd
  -- `M3` re-established at `resumeFr`: `selfStorage resumeFr key = storageAt resumeFr resumeFr.addr
  -- key`, and `resumeFr.addr = self` (`hresaddr`); `storageAt resumeFr self = postStorage…`
  -- (by construction, `resumeFr = resumeAfterCall result pd`).
  have hM3 : ∀ key,
      selfStorage resumeFr key = (fun key => evmCallOracle.postStorage result pd self key) key := by
    intro key
    show selfStorage resumeFr key = evmCallOracle.postStorage result pd self key
    rw [selfStorage_eq_storageAt, hresaddr]
    rw [hresume]; rfl
  refine ⟨hruns, ?_, ?_⟩
  · -- the call-effect correspondence at `resumeFr`, by inverting the IR step.
    cases hstep with
    | call hc hg ho =>
      rw [show evmV2CallOracle result pd self _ _ st.world
            = ((fun key => evmCallOracle.postStorage result pd self key),
               evmCallOracle.successWord result pd) from rfl] at ho
      -- `ho` pins the constructor's `world'`/`success` to the realised projections.
      injection ho with hw' hs'
      subst hw'; subst hs'
      -- B3: DefsSound survives world-replacement + result-binding.
      obtain ⟨hnoSload, hisresult, hscopeCall⟩ := hsc
      have hsound' : DefsSound prog
          (match cs.resultTmp with
            | some t => { st with world := fun key => evmCallOracle.postStorage result pd self key }.setLocal
                          t (evmCallOracle.successWord result pd)
            | none   => { st with world := fun key => evmCallOracle.postStorage result pd self key }) :=
        defsSound_preserved_call hnoSload hisresult hscopeCall hdefs
      refine
        { code_eq := hrescode
          can_modify := hrescanmod
          storage := ?_
          defsSound := hsound'
          wellScoped := hscoped'
          sloadReal := hsload'
          gasReal := hgas' }
      -- M3: the post-state world is the realised post-storage = resumeFr's self lens, in
      -- both `resultTmp` branches (`setLocal` does not touch `world`).
      intro key
      cases cs.resultTmp <;> exact hM3 key
  · -- the bound success flag is exactly exp003's `callSuccessFlag`.
    intro t ht
    cases hstep with
    | call hc hg ho =>
      rw [show evmV2CallOracle result pd self _ _ st.world
            = ((fun key => evmCallOracle.postStorage result pd self key),
               evmCallOracle.successWord result pd) from rfl] at ho
      injection ho with hw' hs'
      subst hw'; subst hs'
      rw [ht]
      show (V2.IRState.setLocal _ t (evmCallOracle.successWord result pd)).locals t = _
      rw [hsuccW]
      unfold V2.IRState.setLocal
      simp

end Lir


-- Build-enforced axiom-cleanliness guard for the C-layer `sim_stmt` deliverable: the three
-- per-statement simulation arms depend only on `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.sim_assign
#print axioms Lir.sim_sstore_stmt
#print axioms Lir.sim_call_stmt
