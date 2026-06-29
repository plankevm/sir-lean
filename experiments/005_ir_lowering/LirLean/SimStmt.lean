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
* the memory value channel `MemRealises prog st fr` (`memAgree`) — the honest positional
  one-read value supplied at each spill def-site. (There is **no** gas universal AND **no** sload
  warmth universal: both gas and sload are spilled, so their values live in memory slots tied by
  `memAgree`, and the SLOAD warmth charge is the single cold/warm def-site read — Phase B/C.)

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
  /-- Define-before-use scoping: every currently-bound tmp is either recomputable or a
  call result registered in the recompute env, and present in it (the `WellScoped` content
  `materialise_runs` consumes — relaxed to admit the memory value channel). -/
  wellScoped : ∀ t, st.locals t ≠ none →
    (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
    ∧ defsOf prog t ≠ none
  /-- The memory value channel: the frame's memory realises the IR's bound spilled locals
  (coverage + readback value at each gas/sload/call-result slot). Supplied to the
  `materialise_runs` calls' MLOAD-readback arm, preserved by assign/sstore (they don't touch
  memory), vacuous at the empty-locals entry. This is the honest positional value tie that
  replaced BOTH the gas universal (`GasRealises`, Phase B) and the SLOAD warmth universal
  (`SloadRealises`, Phase C). -/
  memAgree   : MemRealises prog st fr

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

/-- A **rematerialised** `assign` (the tmp is not spilled to a slot) emits no bytes. -/
theorem emitStmt_assign_remat (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) (e : Expr)
    (h : ∀ n, defs t ≠ some (.slot n)) :
    emitStmt defs fuel (.assign t e) = [] := by
  show (match defs t with
        | some (.slot n) =>
            materialiseExpr defs fuel e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
        | _ => []) = []
  cases hd : defs t with
  | none => rfl
  | some loc => cases loc with
    | slot n => exact absurd hd (h n)
    | _ => rfl

/-- A **spilled** `assign` (the tmp lives in `slot n`) stashes `materialise e ++ PUSH n ++
MSTORE` — computed once at the def-site. For gas (`e = .gas`, `materialise .gas = [GAS]`)
this is the `[GAS] ++ PUSH n ++ MSTORE` stash. -/
theorem emitStmt_assign_slot (defs : Tmp → Option Expr) (fuel : Nat) (t : Tmp) (e : Expr)
    {n : Nat} (h : defs t = some (.slot n)) :
    emitStmt defs fuel (.assign t e)
      = materialiseExpr defs fuel e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore] := by
  show (match defs t with
        | some (.slot n) =>
            materialiseExpr defs fuel e ++ emitImm (UInt256.ofNat n) ++ [Byte.mstore]
        | _ => []) = _
  rw [h]

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
**B3** (`defsSound_preserved_assignPure`). The post-state memory value channel
(`MemRealises` over `st'`) is the honest downstream-supplied side-condition, threaded in as
for `materialise_runs`. (There is no sload/gas warmth universal — both are spilled, Phase B/C.) -/

/-- **`sim_stmt`, the rematerialised `assign` arm.** From `Corr` at `(L, pc)` and an
`EvalStmt` step of `assign t e` whose target is **not** spilled to a slot (`hremat`), the
*same* frame `fr` is in correspondence with the post-state `st'` at cursor `(L, pc+1)`: the
lowered segment is empty (`Runs.refl`), the working stack stays `[]`. Given the per-step B3
scoping (`StepScoped`) and the post-state realisability ties.

The spilled (gas) arm — `defsOf prog t = some (.slot n)`, which emits the `[GAS] ++ PUSH n
++ MSTORE` stash — is `sim_assign_gas` below. -/
theorem sim_assign {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {o : V2.CallOracle} {st st' : V2.IRState} {T T' : Trace} {t : Tmp} {e : Expr}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t e))
    (hremat : ∀ n, defsOf prog t ≠ some (.slot n))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hstep : EvalStmt prog o st T (.assign t e) st' T')
    (hsc : StepScoped prog st (.assign t e))
    (hscoped' : ∀ t, st'.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    (hmem' : MemRealises prog st' fr) :
    Runs fr fr ∧ Corr prog sloadChg obs st' fr L (pc + 1) ∧ fr.exec.stack = [] := by
  refine ⟨Runs.refl fr, ?_, hcorr.stack_nil⟩
  -- pc advance: emitStmt of a rematerialised assign is empty, so the next cursor coincides.
  have hpc : pcOf prog L (pc + 1) = pcOf prog L pc := by
    rw [pcOf_succ prog L b pc (.assign t e) hb hs,
        emitStmt_assign_remat (defsOf prog) (recomputeFuel prog) t e hremat]; simp
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
      memAgree := hmem' }
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

/-- `SSTORE` writes storage, not memory: the post-frame's memory bytes are `fr`'s. (`State.sstore`
touches accounts + substate only; `replaceStackAndIncrPC` touches stack/pc only.) -/
@[simp] theorem sstoreFrame_memory (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.toMachineState.memory
      = fr.exec.toMachineState.memory := by
  show ((sstorePost fr.exec key value rest).toMachineState.memory) = _
  unfold sstorePost Evm.ExecutionState.replaceStackAndIncrPC Evm.State.sstore
  simp only [Option.option]

/-- `SSTORE` leaves `activeWords` untouched (it does not access memory). -/
@[simp] theorem sstoreFrame_activeWords (fr : Frame) (key value : Word) (rest : Stack Word) :
    (sstoreFrame fr key value rest).exec.toMachineState.activeWords
      = fr.exec.toMachineState.activeWords := by
  show ((sstorePost fr.exec key value rest).toMachineState.activeWords) = _
  unfold sstorePost Evm.ExecutionState.replaceStackAndIncrPC Evm.State.sstore
  simp only [Option.option]

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
    hdv hcorr.defsSound hcorr.wellScoped hcorr.storage (by nofun) (by nofun) hcorr.memAgree
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
    (hcorr.storage.transport hmrv.storage) (by nofun)
    (by nofun) (hcorr.memAgree.transport hmrv.memBytes hmrv.memActive)
    hevk hgask hstkk
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
        memAgree := ?_ }
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
    · -- memory value channel: SSTORE preserves memory bytes + activeWords (writes storage,
      -- not memory); `setStorage` leaves `locals`, so `MemRealises` transports through the chain.
      intro tw slot v hdef hloc
      have hloc' : st.locals tw = some v := by simpa [V2.IRState.setStorage] using hloc
      have hmembytes : (sstoreFrame frk kw vw []).exec.toMachineState.memory
          = fr.exec.toMachineState.memory := by
        rw [sstoreFrame_memory, hmrk.memBytes, hmrv.memBytes]
      have hmemact : fr.exec.toMachineState.activeWords.toNat
          ≤ (sstoreFrame frk kw vw []).exec.toMachineState.activeWords.toNat := by
        rw [sstoreFrame_activeWords]; exact le_trans hmrv.memActive hmrk.memActive
      exact (hcorr.memAgree.transport hmembytes hmemact) tw slot v hdef hloc'
  · rw [sstoreFrame_stack]

/-! ## Arm 3 — `call cs` (the `Runs.call` node + the Route-B tail)

A `Stmt.call` lowers (Route B) to
`5×(PUSH 0) ++ materialise callee ++ materialise gasFwd ++ [CALL] ++ tail`, where the tail
is `PUSH32 slotOf t ; MSTORE` (`resultTmp = some t`) or `[POP]` (`resultTmp = none`). The
arg-push prefix reaches the CALL-site frame `callFr`; under lowering the CALL is a
`Runs.call` node carrying a `CallReturns callFr resumeFr` witness (the CALL step, the child
entering as code, the black-box child run, the resumed parent); the tail then consumes the
success flag CALL left on the stack — `MSTORE`-ing it to the result slot (`some t`) or
`POP`-ing it (`none`). The IR `EvalStmt.call` queries the oracle and applies its
`(world', success)` bundle.

We instantiate the abstract oracle to the **realised** `evmV2CallOracle result pd self`
(`LirLean/V2/CallRealises.lean`): `world' = postStorage result pd self = storageAt resumeFr
self` (the `M3` lens) and `success = successWord result pd = callSuccessFlag result pd`
(exp003's CALL flag `x`). With that tie the post-`EvalStmt` IR world *is* the resumed
frame's storage lens, so `M3` (`StorageAgree`) is re-established at `endFr` (the tail
touches storage in neither branch); `DefsSound` survives the world-replacement +
result-binding by **B3** `defsSound_preserved_call`; code/canModifyState/validJumps are
preserved by `resumeAfterCall` (it keeps the caller's `executionEnv`) and the tail
transformers (`popFrame`/`mstoreFrame` preserve `executionEnv`).

This arm now delivers the **full** `Corr` at `endFr` for `(L, pc+1)`. The two former
documented gaps close on the Route-B tail:

* **`stack_nil` (M5)** — the tail consumes the flag: `MSTORE` pops `slot :: flag :: []`
  (`some t`) / `POP` pops `flag :: []` (`none`), leaving `[]`.
* **`pc_eq` (M1)** — `endFr.pc = callFr.pc + 1 + tailLen` (CALL + tail), `callFr.pc =
  fr.pc + argsLen` (the supplied arg-push pin), `fr.pc = pcOf prog L pc`, and the
  `emitStmt .call` length is exactly `argsLen + 1 + tailLen` (`pcOf_succ`).

The new **`memAgree`** clause (`MemRealises prog st' endFr`) is the heart: the pre-call
`MemRealises … fr` transports across the arg pushes (`hcallmem`/`hcallactive`) and the CALL
(zero in/out window ⇒ caller memory survives), then the tail: `none` leaves memory (POP),
`some t` writes `mem[slotOf t] = flag` (binding the new call-result slot via
`mstore_reads_back`) while keeping every other bound slot's coverage+value
(`mstore_preserves_slot` + `slot_windows_disjoint`). -/

/-! ### `popFrame` / `mstoreFrame` accessor reductions used by the tail

`popPost`/`mstorePost` (exp003 `Dispatch.lean`) `replaceStackAndIncrPC` only the
`stack`/`pc`, leaving the `executionEnv` (code/address/canMod) and — for `popFrame` — the
`MachineState` (memory/activeWords). `mstoreFrame`'s machine state is `fr`'s with `val`
written at `addr` (`mstoreFrame_memory`, exp003). These reductions expose the `Corr` clauses
the tail must re-establish. -/

@[simp] theorem popFrame_canMod (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.executionEnv.canModifyState
      = fr.exec.executionEnv.canModifyState := rfl

@[simp] theorem popFrame_memory (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.toMachineState.memory = fr.exec.toMachineState.memory := rfl

@[simp] theorem popFrame_activeWords (fr : Frame) (rest : Stack Word) :
    (popFrame fr rest).exec.toMachineState.activeWords = fr.exec.toMachineState.activeWords := rfl

@[simp] theorem mstoreFrame_addr (fr : Frame) (addr val : Word) (words' : UInt64) (rest : Stack Word) :
    (mstoreFrame fr addr val words' rest).exec.executionEnv.address
      = fr.exec.executionEnv.address := rfl

/-- **`sim_stmt`, the `call` arm — FULL `Corr` (Route B).** Let `callFr` be the CALL-site
frame reached from `fr` by running the lowered CALL-argument pushes (`hargs : Runs fr
callFr`), pinned by its pc (`hcallpc`) and a `MatRuns`-style memory pin
to `fr` (`hcallmem` bytes-equal, `hcallactive` `activeWords`-nondecreasing). Given a
returning external CALL (`CallReturns callFr resumeFr`) with the realised resume frame pinned
(`hrespc`/`hresstack` — the empty-boundary collapse `pd.stack = []`, `hresmem`/`hresactive` —
zero in/out windows preserve caller memory) and the IR step taken under the **realised**
oracle (so `resumeFr = resumeAfterCall result pd`), running the whole lowered call *and its
Route-B tail* reaches `endFr` in **full correspondence** `Corr prog sloadChg obs st' endFr L
(pc+1)`, with the working stack back to `[]`. The tail consumes the success flag (M5), the pc
lands on the next statement (M1), and `memAgree` ties the bound call-result slot's memory to
`st'.locals`. -/
theorem sim_call_stmt {prog : Program} {sloadChg : Tmp → ℕ} {obs : Word}
    {st st' : V2.IRState} {T : Trace} {cs : CallSpec} {calleeW gasFwdW : Word}
    {L : Label} {b : Block} {pc : Nat} {argsLen : Nat}
    {fr callFr resumeFr : Frame} {result : Evm.CallResult} {pd : Evm.PendingCall}
    {self : AccountAddress}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.call cs))
    -- M1 anchor: `fr` sits at the statement cursor; `argsLen` is the arg-push prefix length.
    (hfrpc : fr.exec.pc = UInt32.ofNat (pcOf prog L pc))
    (hargslen : argsLen
      = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ materialise (defsOf prog) (recomputeFuel prog) cs.callee
          ++ materialise (defsOf prog) (recomputeFuel prog) cs.gasFwd).length)
    -- the assembled CALL-argument push run + its pins (`MatRuns`-style, supplied by the caller):
    (hargs : Runs fr callFr)
    (hcallpc : callFr.exec.pc = fr.exec.pc + UInt32.ofNat argsLen)
    (hcallmem : callFr.exec.toMachineState.memory = fr.exec.toMachineState.memory)
    (hcallactive : fr.exec.toMachineState.activeWords.toNat
      ≤ callFr.exec.toMachineState.activeWords.toNat)
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
    -- the resume frame's pc / stack / memory, pinned to `callFr` (`resumeAfterCall`: pc + 1,
    -- stack = flag :: pd.stack with `pd.stack = []` at the empty boundary, memory/activeWords
    -- preserved by the zero in/out windows):
    (hrespc : resumeFr.exec.pc = callFr.exec.pc + 1)
    (hresstack : resumeFr.exec.stack = callSuccessFlag result pd :: [])
    (hresmem : resumeFr.exec.toMachineState.memory = callFr.exec.toMachineState.memory)
    (hresactive : callFr.exec.toMachineState.activeWords.toNat
      ≤ resumeFr.exec.toMachineState.activeWords.toNat)
    (hresvalidjumps : resumeFr.validJumps = validJumpDests resumeFr.exec.executionEnv.code 0)
    -- standing B3 / per-step scoping of `st`, the pre-call memory channel:
    (hdefs : DefsSound prog st)
    (hsc : StepScoped prog st (.call cs))
    (hmem : MemRealises prog st fr)
    -- every registered call-result slot is `slotOf` (`defsOf` registers `(t, .slot (slotOf
    -- t))`; a source `assign` never carries the lowering-only `.slot` marker — a
    -- `WellFormed` invariant the eventual caller discharges). Pins the result-slot for the new
    -- binding and the 32-aligned disjointness of distinct bound slots.
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    -- the post-state scoping/realisability (downstream-supplied, as in `materialise_runs`):
    (hscoped' : ∀ t, st'.locals t ≠ none →
      (¬ NonRecomputable prog t ∨ ∃ slot, defsOf prog t = some (.slot slot))
      ∧ defsOf prog t ≠ none)
    -- the Route-B tail's realisability (decode anchors + gas + memory-expansion witness),
    -- supplied at the resume frame — the honest runtime ties the eventual caller discharges:
    (htail : ∀ flag : Word, resumeFr.exec.stack = flag :: [] →
      (∀ (t : Tmp), cs.resultTmp = some t →
        -- `slotOf t` is addressable (the "slots are addressable" side condition):
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr,
            Runs resumeFr endFr
          -- the MSTORE tail writes `flag` at `slotOf t` onto `resumeFr`'s machine state. The
          -- honest channel is the `.memory` bytes + `.activeWords` (NOT the full `toMachineState`:
          -- the push + gas-charges drop gas, a `MachineState` field a real run never preserves —
          -- the full equality is over-constrained / unsatisfiable; only the bytes + activeWords,
          -- which `MemRealises`/`Corr` read, are honest and true). This is exactly what
          -- `stash_tail_runs` constructs:
          ∧ endFr.exec.toMachineState.memory
              = (resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag).memory
          ∧ endFr.exec.toMachineState.activeWords
              = (resumeFr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) flag).activeWords
          ∧ endFr.exec.pc = resumeFr.exec.pc + UInt32.ofNat 34
          ∧ endFr.exec.executionEnv.code = resumeFr.exec.executionEnv.code
          ∧ endFr.validJumps = resumeFr.validJumps
          ∧ endFr.exec.executionEnv.address = resumeFr.exec.executionEnv.address
          ∧ endFr.exec.executionEnv.canModifyState = resumeFr.exec.executionEnv.canModifyState
          -- the MSTORE tail writes memory, not storage: the self-lens is preserved:
          ∧ (∀ k, selfStorage endFr k = selfStorage resumeFr k)
          ∧ endFr.exec.stack = [])
      ∧ (cs.resultTmp = none →
          Runs resumeFr (popFrame resumeFr []))) :
    ∃ endFr, Runs fr endFr ∧ Corr prog sloadChg obs st' endFr L (pc + 1)
      ∧ endFr.exec.stack = [] := by
  classical
  -- == the Runs to `resumeFr`: arg pushes then the returning CALL node ==
  have hruns0 : Runs fr resumeFr := hargs.trans (sim_call hcall (Runs.refl resumeFr))
  -- the realised oracle's projections: `successWord = callSuccessFlag` (§5 reflexivity).
  have hsuccW : evmCallOracle.successWord result pd = callSuccessFlag result pd :=
    evmCallOracle_successWord_eq_x result pd
  -- `M3` re-established at `resumeFr`: `selfStorage resumeFr key = postStorage…`.
  have hM3 : ∀ key,
      selfStorage resumeFr key = evmCallOracle.postStorage result pd self key := by
    intro key
    rw [selfStorage_eq_storageAt, hresaddr, hresume]; rfl
  -- `emitStmt .call` length = argsLen + 1 + tailLen.
  set defs := defsOf prog with hdefs2
  set fuel := recomputeFuel prog with hfuel
  have hemitcall : emitStmt defs fuel (.call cs)
      = (emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ materialise defs fuel cs.callee ++ materialise defs fuel cs.gasFwd)
        ++ [Byte.call]
        ++ (match cs.resultTmp with
            | some t => emitImm (UInt256.ofNat (slotOf t)) ++ [Byte.mstore]
            | none   => [Byte.pop]) := rfl
  -- the IR post-state `st'` projections (invert the realised oracle step once).
  have hst' : st' = (match cs.resultTmp with
      | some t => { st with world := fun key => evmCallOracle.postStorage result pd self key }.setLocal
                    t (callSuccessFlag result pd)
      | none   => { st with world := fun key => evmCallOracle.postStorage result pd self key }) := by
    cases hstep with
    | call hc hg ho =>
      rw [show evmV2CallOracle result pd self _ _ st.world
            = ((fun key => evmCallOracle.postStorage result pd self key),
               evmCallOracle.successWord result pd) from rfl] at ho
      injection ho with hw' hs'
      subst hw'; subst hs'
      cases cs.resultTmp <;> simp [hsuccW]
  -- DefsSound survives world-replacement + result-binding (B3).
  obtain ⟨hnoSload, hisresult, hscopeCall⟩ := hsc
  have hsound' : DefsSound prog st' := by
    rw [hst']
    exact defsSound_preserved_call (world' := fun key => evmCallOracle.postStorage result pd self key)
      (success := callSuccessFlag result pd) hnoSload hisresult hscopeCall hdefs
  -- pre-call MemRealises transports `fr → callFr → resumeFr`.
  have hmemRes : MemRealises prog st resumeFr :=
    ((hmem.transport hcallmem hcallactive).transport hresmem hresactive)
  -- == case on the result tmp: run the Route-B tail ==
  obtain ⟨htailSome, htailNone⟩ := htail (callSuccessFlag result pd) hresstack
  cases hr : cs.resultTmp with
  | none =>
    -- POP tail: `endFr = popFrame resumeFr []`, stack `[]`, memory untouched.
    have hpoprun : Runs resumeFr (popFrame resumeFr []) := htailNone hr
    refine ⟨popFrame resumeFr [], hruns0.trans hpoprun, ?_, by rw [popFrame_stack]⟩
    -- pc: endFr.pc = resumeFr.pc + 1 = (fr.pc + argsLen) + 1 + 1; emit = argsLen + 1 + 1.
    have hemitlen : (emitStmt defs fuel (.call cs)).length = argsLen + 1 + 1 := by
      rw [hemitcall, hr]
      set argsBlock := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ materialise defs fuel cs.callee ++ materialise defs fuel cs.gasFwd with hab
      rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton,
        ← hargslen]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (argsLen + 1 + 1) := by
      rw [pcOf_succ prog L b pc (.call cs) hb hs, hemitlen]
    refine
      { pc_eq := ?_
        code_eq := ?_
        validJumps_eq := ?_
        stack_nil := by rw [popFrame_stack]
        can_modify := ?_
        storage := ?_
        defsSound := hsound'
        wellScoped := hscoped'
        memAgree := ?_ }
    · -- M1
      rw [popFrame_pc, hrespc, hcallpc, hfrpc, hpcN,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add,
          show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
      ac_rfl
    · rw [popFrame_code, hrescode]
    · rw [popFrame_validJumps, popFrame_code, hresvalidjumps]
    · rw [popFrame_canMod, hrescanmod]
    · -- M3: world is the resumed self-lens; POP doesn't touch storage.
      intro key
      have hst'none : st' = { st with world := fun key => evmCallOracle.postStorage result pd self key } := by
        rw [hst', hr]
      rw [hst'none]
      show selfStorage (popFrame resumeFr []) key = _
      rw [show selfStorage (popFrame resumeFr []) key = selfStorage resumeFr key from rfl]
      exact hM3 key
    · -- memAgree: `st'.locals = st.locals`, POP preserves memory bytes + activeWords.
      have hloceq : st' = { st with world := fun key => evmCallOracle.postStorage result pd self key } := by
        rw [hst', hr]
      intro tw slot v hdef hloc
      rw [hloceq] at hloc
      exact (hmemRes.transport (by rw [popFrame_memory]) (by rw [popFrame_activeWords]))
        tw slot v hdef hloc
  | some t =>
    -- PUSH slot; MSTORE tail: `endFr` writes `mem[slotOf t] = flag`, stack `[]`.
    obtain ⟨hslot63, hslotplat, endFr, hendrun, hendmembytes, hendmemactive, hendpc, hendcode,
      hendvalid, hendaddr, hendcanmod, hendstorage, hendstk⟩ := htailSome t hr
    set flag := callSuccessFlag result pd with hflag
    set slot := slotOf t with hslotdef
    refine ⟨endFr, hruns0.trans hendrun, ?_, hendstk⟩
    -- `slotOf t` addressability ports between the `+63 < 2^64` form (`mstore_reads_back`)
    -- and the `.toNat = slot` collapse (`mstore_*` are stated over `(ofNat slot).toNat`).
    have hslotlt256 : slot < 2 ^ 256 := by
      have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    have hslotEq : (UInt256.ofNat slot).toNat = slot := by
      rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslotlt256]
    have hslot63' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by rw [hslotEq]; exact hslot63
    have hslotplat' : (UInt256.ofNat slot).toNat < 2 ^ System.Platform.numBits := by
      rw [hslotEq]; exact hslotplat
    -- pc: endFr.pc = resumeFr.pc + 34 = (fr.pc + argsLen) + 1 + 34; emit = argsLen + 1 + 34.
    have hemitlen : (emitStmt defs fuel (.call cs)).length = argsLen + 1 + 34 := by
      rw [hemitcall, hr]
      set argsBlock := emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0 ++ emitImm 0
          ++ materialise defs fuel cs.callee ++ materialise defs fuel cs.gasFwd with hab
      rw [List.length_append, List.length_append, List.length_singleton, ← hargslen,
        List.length_append, List.length_singleton, emitImm_length]
    have hpcN : pcOf prog L (pc + 1) = pcOf prog L pc + (argsLen + 1 + 34) := by
      rw [pcOf_succ prog L b pc (.call cs) hb hs, hemitlen]
    refine
      { pc_eq := ?_
        code_eq := ?_
        validJumps_eq := ?_
        stack_nil := hendstk
        can_modify := ?_
        storage := ?_
        defsSound := hsound'
        wellScoped := hscoped'
        memAgree := ?_ }
    · -- M1
      rw [hendpc, hrespc, hcallpc, hfrpc, hpcN,
          UInt32.ofNat_add, UInt32.ofNat_add, UInt32.ofNat_add,
          show (UInt32.ofNat 1) = (1 : UInt32) from rfl]
      ac_rfl
    · rw [hendcode, hrescode]
    · rw [hendvalid, hendcode]; exact hresvalidjumps
    · rw [hendcanmod, hrescanmod]
    · -- M3: world is the resumed self-lens; the MSTORE tail preserves the self-lens.
      intro key
      rw [hst', hr]
      show selfStorage endFr key = _
      rw [hendstorage key]; exact hM3 key
    · -- memAgree: the heart. New slot binds flag; other call-result slots preserved.
      -- `endFr.memory = resumeFr.memory.mstore slot flag` (`hendmem`).
      intro tw slot' v hdef hloc
      -- `st'.locals tw`: split on `tw = t`.
      by_cases htw : tw = t
      · -- the just-bound call-result tmp `t`: `slot' = slotOf t = slot`, `v = flag`.
        subst htw
        -- `defsOf prog tw = some (.slot slot')`; the registered slot for `tw` is `slotOf tw`.
        -- and `st'.locals tw = some flag`.
        have hvflag : v = flag := by
          have : st'.locals tw = some flag := by rw [hst', hr]; simp [V2.IRState.setLocal]
          rw [this] at hloc; exact (Option.some.inj hloc).symm
        have hslot'eq : slot' = slot := by
          -- the registered slot for `tw` is `slotOf tw = slot` (`hslots`).
          rw [show slot = slotOf tw from rfl]
          exact hslots tw slot' hdef
        subst hslot'eq; subst hvflag
        -- coverage + readback at the just-written slot.
        refine ⟨?_, ?_, hslot63, ?_⟩
        · -- memory.size ≥ slot + 32
          rw [hendmembytes]
          have := LirLean.MemAlgebra.mstore_memory_size resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag (by rw [hslotEq]; exact hslotplat)
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · -- activeWords*32 ≥ slot + 32
          rw [hendmemactive]
          have := LirLean.MemAlgebra.mstore_activeWords_covers resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63'
          rw [hslotEq] at this
          show (UInt256.ofNat slot).toNat + 32 ≤ _
          rw [hslotEq]; exact this
        · -- readback = flag (`endFr` agrees with `resumeFr….mstore` on memory + activeWords).
          rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot) hendmembytes hendmemactive]
          exact LirLean.MemAlgebra.mstore_reads_back resumeFr.exec.toMachineState
            (UInt256.ofNat slot) flag hslot63' hslotplat'
      · -- another bound tmp `tw ≠ t`: its `st.locals tw` value is unchanged; if it's a
        -- call-result slot it stays covered+valued through the MSTORE at the disjoint slot.
        have hloc0 : st.locals tw = some v := by
          rw [hst', hr] at hloc
          simpa [V2.IRState.setLocal, htw] using hloc
        obtain ⟨hcm, ham, hreal, hval⟩ := hmemRes tw slot' v hdef hloc0
        -- the read slot `slot'` is a realistic offset (`+63 < 2^64`) ⇒ `< 2^256`, so
        -- `(ofNat slot').toNat = slot'` collapses.
        have hslot'lt256 : slot' < 2 ^ 256 := by
          have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
          omega
        have hslot'Eq : (UInt256.ofNat slot').toNat = slot' := by
          rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslot'lt256]
        -- the two slots are distinct tmps' 32-aligned slots ⇒ disjoint windows.
        have hslot'def : slot' = slotOf tw := hslots tw slot' hdef
        have htwne : t.id ≠ tw.id := fun h => htw (by cases t; cases tw; cases h; rfl)
        have hdisN : slot + 32 ≤ slot' ∨ slot' + 32 ≤ slot := by
          rw [hslotdef, hslot'def]
          exact LirLean.MemAlgebra.slot_windows_disjoint t.id tw.id htwne
        -- coverage AND value are preserved in one shot by the grow-aware MSTORE
        -- preservation lemma (`mstore_preserves_slot_grow`): the binding MSTORE at the
        -- result slot `slotOf t` may grow memory past the disjoint, covered slot `slotOf tw`,
        -- yet leaves its coverage and readback intact. Window-disjointness is the 32-aligned
        -- slot fact; the `slot' + 63 < 2^64` realisability clause carries over from `hreal`.
        -- the disjointness in the lemma's orientation (`s + 32 ≤ addr ∨ addr + 32 ≤ s`):
        have hdisN' : (UInt256.ofNat slot').toNat + 32 ≤ (UInt256.ofNat slot).toNat
            ∨ (UInt256.ofNat slot).toNat + 32 ≤ (UInt256.ofNat slot').toNat := by
          rw [hslotEq, hslot'Eq]; exact hdisN.symm
        obtain ⟨hmem', hact', hval'⟩ :=
          LirLean.MemAlgebra.mstore_preserves_slot_grow resumeFr.exec.toMachineState
            (UInt256.ofNat slot) (UInt256.ofNat slot') flag hslot63' hslotplat' hcm ham hdisN'
        -- `endFr` agrees with `resumeFr….mstore slot flag` on memory + activeWords (supplied), so
        -- the disjoint slot `slot'` keeps coverage + readback on `endFr`.
        refine ⟨?_, ?_, hreal, ?_⟩
        · rw [hendmembytes]; exact hmem'
        · rw [hendmemactive]; exact hact'
        · rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot') hendmembytes hendmemactive]
          exact hval'.trans hval

/-! ## Arm 1′ — `assign t .gas` through the spill (Phase B, the gas value channel)

A **gas-defined** tmp is no longer rematerialised — it is spilled to its memory slot
`slotOf t` (`defsOf prog t = some (.slot (slotOf t))`, `emitStmt .assign` emits the stash
`[GAS] ++ PUSH (slotOf t) ++ MSTORE`). The gas value is read **once**, at this clean
statement boundary (empty stack), and reused from memory (`MLOAD`) on every use — so it is
multi-use-safe and the `GAS` opcode runs exactly once per gas read.

The value tie is **local and positional** (no `∀`-over-frames, no constancy): the single
`GAS` opcode at the def-site reports `ofUInt64 (fr.gas − Gbase)`, and the IR binds `t` to the
*consumed* read `obs`; the genuine descending-gas run provides `obs = ofUInt64 (fr.gas −
Gbase)` (`hgasval`) — one read, one frame. This replaces the vacuous universal
`Lir.GasRealises obs fr` entirely: the gas value lives in the slot, tied by `MemRealises`.

Mirroring `sim_call_stmt`'s Route-B result arm, the GAS;PUSH;MSTORE stash run and its frame
pins are taken as a supplied tail hypothesis `hstash` (the honest runtime ties the caller
discharges, exactly as the call's `htail`); the value stored is `obs` (the positional tie
folds in). The arm re-establishes the full `Corr` at `pc+1`, including `MemRealises` for the
just-bound gas slot (coverage + readback `= obs`) and preservation of every other bound slot
across the (disjoint) gas-slot MSTORE. -/

/-- **`sim_stmt`, the spilled `assign t .gas` arm (Phase B).** From `Corr` at `(L, pc)`, an
`EvalStmt.assignGas` step binding `t := obs`, the positional gas value tie `obs = ofUInt64
(fr.gas − Gbase)` (`hgasval`), and the supplied GAS;PUSH;MSTORE stash run `hstash` (writing
`obs` to `slotOf t`), running the lowered stash reaches a frame `endFr` in `Corr` with
`st.setLocal t obs` at `(L, pc+1)`, stack `[]`. The gas value lives in `slotOf t`, tied by
`MemRealises`; no gas universal is used. -/
theorem sim_assign_gas {prog : Program} {sloadChg : Tmp → ℕ} {obs ob : Word}
    {st : V2.IRState} {t : Tmp}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t .gas))
    (hslotdef : defsOf prog t = some (.slot (slotOf t)))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hsc : StepScoped prog st (.assign t .gas))
    -- every registered slot is `slotOf` (the `WellFormed` invariant; pins disjointness):
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    -- the post-state scoping/realisability (downstream-supplied); the bound gas read is `ob`:
    (hscoped' : ∀ t', (st.setLocal t ob).locals t' ≠ none →
      (¬ NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
      ∧ defsOf prog t' ≠ none)
    -- the supplied GAS;PUSH;MSTORE stash run + its pins (the honest runtime tie, as the call
    -- arm's `htail`); `slotOf t` addressable, and `endFr` writes the **consumed gas read** `ob`
    -- at `slotOf t` — the honest positional one-read value tie (no constancy, no `∀`-frames).
    -- The memory channel is stated as the `.memory` bytes + `.activeWords` (NOT the full
    -- `toMachineState`): the gas the stash drops is a `MachineState` field a real run never
    -- preserves, so the full-`toMachineState` equality is over-constrained / unsatisfiable —
    -- only the bytes + activeWords (which `MemRealises`/`Corr` read) are honest and true. This is
    -- exactly what `stash_tail_gas` (`StashTail.lean`) constructs; `sim_assign_gas_lowered`
    -- discharges it from decode + gas facts:
    (hstash :
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr,
            Runs fr endFr
          ∧ endFr.exec.toMachineState.memory
              = (fr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) ob).memory
          ∧ endFr.exec.toMachineState.activeWords
              = (fr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) ob).activeWords
          ∧ endFr.exec.pc = fr.exec.pc + UInt32.ofNat (emitStmt (defsOf prog) (recomputeFuel prog)
                (.assign t .gas)).length
          ∧ endFr.exec.executionEnv.code = fr.exec.executionEnv.code
          ∧ endFr.validJumps = fr.validJumps
          ∧ endFr.exec.executionEnv.address = fr.exec.executionEnv.address
          ∧ endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
          ∧ (∀ k, selfStorage endFr k = selfStorage fr k)
          ∧ endFr.exec.stack = []) :
    ∃ endFr, Runs fr endFr ∧ Corr prog sloadChg obs (st.setLocal t ob) endFr L (pc + 1)
      ∧ endFr.exec.stack = [] := by
  classical
  obtain ⟨hslot63, hslotplat, endFr, hendrun, hendmembytes, hendmemactive, hendpc, hendcode,
    hendvalid, hendaddr, hendcanmod, hendstorage, hendstk⟩ := hstash
  set slot := slotOf t with hsdef
  set st' := st.setLocal t ob with hst'def
  refine ⟨endFr, hendrun, ?_, hendstk⟩
  -- slot addressability collapses (`(ofNat slot).toNat = slot`).
  have hslotlt256 : slot < 2 ^ 256 := by
    have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hslotEq : (UInt256.ofNat slot).toNat = slot := by
    rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslotlt256]
  have hslot63' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by rw [hslotEq]; exact hslot63
  have hslotplat' : (UInt256.ofNat slot).toNat < 2 ^ System.Platform.numBits := by
    rw [hslotEq]; exact hslotplat
  -- DefsSound survives the gas rebind (B3): `t` is non-recomputable (gas), excluded.
  have hsound' : DefsSound prog st' := by
    obtain ⟨_, hgasArm, _⟩ := hsc
    obtain ⟨hgasdef, hscope⟩ := hgasArm rfl
    exact defsSound_preserved_assignGas hgasdef hscope hcorr.defsSound
  -- pc advance.
  have hpcN : pcOf prog L (pc + 1)
      = pcOf prog L pc + (emitStmt (defsOf prog) (recomputeFuel prog) (.assign t .gas)).length :=
    pcOf_succ prog L b pc (.assign t .gas) hb hs
  refine
    { pc_eq := by rw [hendpc, hcorr.pc_eq, hpcN, UInt32.ofNat_add]
      code_eq := by rw [hendcode]; exact hcorr.code_eq
      validJumps_eq := by rw [hendvalid, hendcode]; exact hcorr.validJumps_eq
      stack_nil := hendstk
      can_modify := by rw [hendcanmod]; exact hcorr.can_modify
      storage := ?_
      defsSound := hsound'
      wellScoped := hscoped'
      memAgree := ?_ }
  · -- M3: the stash writes memory, not storage; self-lens preserved (`hendstorage`).
    intro key
    show selfStorage endFr key = st'.world key
    rw [hendstorage key]; exact hcorr.storage key
  · -- memAgree: the just-bound gas slot holds `ob` (the consumed read); other bound slots
    -- survive the disjoint MSTORE.
    intro tw slot' v hdef hloc
    by_cases htw : tw = t
    · -- the just-bound gas tmp `t`: `slot' = slotOf t = slot`, `v = ob`.
      subst htw
      have hvob : v = ob := by
        have : st'.locals tw = some ob := by rw [hst'def]; simp [V2.IRState.setLocal]
        rw [this] at hloc; exact (Option.some.inj hloc).symm
      have hslot'eq : slot' = slot := by rw [show slot = slotOf tw from rfl]; exact hslots tw slot' hdef
      subst hslot'eq; subst hvob
      refine ⟨?_, ?_, hslot63, ?_⟩
      · rw [hendmembytes]
        have := LirLean.MemAlgebra.mstore_memory_size fr.exec.toMachineState
          (UInt256.ofNat slot) v (by rw [hslotEq]; exact hslotplat)
        rw [hslotEq] at this; show (UInt256.ofNat slot).toNat + 32 ≤ _; rw [hslotEq]; exact this
      · rw [hendmemactive]
        have := LirLean.MemAlgebra.mstore_activeWords_covers fr.exec.toMachineState
          (UInt256.ofNat slot) v hslot63'
        rw [hslotEq] at this; show (UInt256.ofNat slot).toNat + 32 ≤ _; rw [hslotEq]; exact this
      · -- readback: `endFr`'s machine state agrees with `fr….mstore slot v` on memory + activeWords
        -- (both supplied), so `mload`'s value coincides (`mload_congr`); then `mstore_reads_back`.
        rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot) hendmembytes hendmemactive]
        exact LirLean.MemAlgebra.mstore_reads_back fr.exec.toMachineState
          (UInt256.ofNat slot) v hslot63' hslotplat'
    · -- another bound tmp `tw ≠ t`: unchanged value; its slot survives the disjoint MSTORE.
      have hloc0 : st.locals tw = some v := by
        rw [hst'def] at hloc; simpa [V2.IRState.setLocal, htw] using hloc
      obtain ⟨hcm, ham, hreal, hval⟩ := hcorr.memAgree tw slot' v hdef hloc0
      have hslot'lt256 : slot' < 2 ^ 256 := by
        have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      have hslot'Eq : (UInt256.ofNat slot').toNat = slot' := by
        rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslot'lt256]
      have hslot'def : slot' = slotOf tw := hslots tw slot' hdef
      have htwne : t.id ≠ tw.id := fun h => htw (by cases t; cases tw; cases h; rfl)
      have hdisN : slot + 32 ≤ slot' ∨ slot' + 32 ≤ slot := by
        rw [hsdef, hslot'def]; exact LirLean.MemAlgebra.slot_windows_disjoint t.id tw.id htwne
      have hdisN' : (UInt256.ofNat slot').toNat + 32 ≤ (UInt256.ofNat slot).toNat
          ∨ (UInt256.ofNat slot).toNat + 32 ≤ (UInt256.ofNat slot').toNat := by
        rw [hslotEq, hslot'Eq]; exact hdisN.symm
      obtain ⟨hmem', hact', hval'⟩ :=
        LirLean.MemAlgebra.mstore_preserves_slot_grow fr.exec.toMachineState
          (UInt256.ofNat slot) (UInt256.ofNat slot') ob hslot63' hslotplat' hcm ham hdisN'
      -- `endFr` agrees with `fr….mstore slot ob` on memory + activeWords (both supplied), so the
      -- disjoint slot `slot'` keeps its coverage (size/active) and readback value on `endFr`.
      refine ⟨?_, ?_, hreal, ?_⟩
      · rw [hendmembytes]; exact hmem'
      · rw [hendmemactive]; exact hact'
      · rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot') hendmembytes hendmemactive]
        exact hval'.trans hval

/-! ## Arm 1″ — `assign t (.sload k)` through the spill (Phase C, the sload value channel)

An **sload-defined** tmp is no longer rematerialised — it is spilled to its memory slot
`slotOf t` (`defsOf prog t = some (.slot (slotOf t))`, `emitStmt .assign` emits the stash
`materialise k ++ [SLOAD] ++ PUSH (slotOf t) ++ MSTORE`). The SLOAD value — and its cold/warm
**warmth charge** — is read **once**, at this clean statement boundary (empty stack), and reused
from memory (`MLOAD`) on every use, so it is multi-use-safe and the `SLOAD` opcode runs exactly
once per source sload read.

The value tie is **local and positional** (no `∀`-over-frames, no constancy): the single `SLOAD`
opcode at the def-site reads the storage cell `st.world key` (= the value the IR's `assignPure`
binds, `evalExpr st 0 (.sload k) = some w`), and the stash writes it to `slotOf t`. This replaces
the vacuous warmth universal `Lir.SloadRealises sloadChg st fr` entirely: the SLOAD value lives in
the slot, tied by `MemRealises`, and its warmth cost is the single def-site read (the positional
`SloadLogAligned` selection, NOT the single-resolver universal).

Mirroring `sim_assign_gas`, the def-site stash run and its frame pins are taken as a supplied tail
hypothesis `hstash` (the honest runtime tie the caller supplies, as the call arm's `htail`;
satisfiable by a real run via `stash_tail_runs_covered` — there is no `sim_assign_sload_lowered`
constructor yet, since the variable-length `materialise k` prefix has no spine decode primitive; its
construction is deferred to the P5 forward-from-real-run discharge). The value stored is `w` (the loaded
storage value). The arm re-establishes the full `Corr` at `pc+1`, including `MemRealises` for the
just-bound sload slot (coverage + readback `= w`) and preservation of every other bound slot across
the (disjoint) sload-slot MSTORE. -/

/-- **`sim_stmt`, the spilled `assign t (.sload k)` arm (Phase C).** From `Corr` at `(L, pc)`, an
`EvalStmt.assignPure` step binding `t := w` for `evalExpr st 0 (.sload k) = some w` (the loaded
storage value), and the supplied stash run `hstash` (writing `w` to `slotOf t`), running the lowered
`materialise k ; SLOAD ; PUSH slot ; MSTORE` stash reaches a frame `endFr` in `Corr` with
`st.setLocal t w` at `(L, pc+1)`, stack `[]`. The sload value lives in `slotOf t`, tied by
`MemRealises`; no sload warmth universal is used (the warmth cost is the single def-site read). -/
theorem sim_assign_sload {prog : Program} {sloadChg : Tmp → ℕ} {obs w : Word}
    {st : V2.IRState} {t k : Tmp}
    {L : Label} {b : Block} {pc : Nat} {fr : Frame}
    (hb : prog.blocks.toList[L.idx]? = some b)
    (hs : b.stmts[pc]? = some (.assign t (.sload k)))
    (hslotdef : defsOf prog t = some (.slot (slotOf t)))
    (hcorr : Corr prog sloadChg obs st fr L pc)
    (hsc : StepScoped prog st (.assign t (.sload k)))
    -- every registered slot is `slotOf` (the `WellFormed` invariant; pins disjointness):
    (hslots : ∀ tw slot', defsOf prog tw = some (.slot slot') → slot' = slotOf tw)
    -- the loaded storage value (the `assignPure` value channel):
    (hwval : V2.evalExpr st 0 (.sload k) = some w)
    -- the post-state scoping (downstream-supplied); the bound sload read is `w`:
    (hscoped' : ∀ t', (st.setLocal t w).locals t' ≠ none →
      (¬ NonRecomputable prog t' ∨ ∃ slot, defsOf prog t' = some (.slot slot))
      ∧ defsOf prog t' ≠ none)
    -- the supplied stash run + its pins (the honest runtime tie, as `sim_assign_gas`'s `hstash`);
    -- `slotOf t` addressable, and `endFr` writes the **loaded value** `w` at `slotOf t` — the
    -- honest positional one-read value tie (no constancy, no `∀`-frames). The memory channel is the
    -- `.memory` bytes + `.activeWords` (NOT the full `toMachineState`: the stash drops gas, a
    -- `MachineState` field a real run never preserves). Supplied here (satisfiable via
    -- `stash_tail_runs_covered`); discharged from the real run in the P5 forward-simulation step:
    (hstash :
        (slotOf t) + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits
        ∧ ∃ endFr,
            Runs fr endFr
          ∧ endFr.exec.toMachineState.memory
              = (fr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) w).memory
          ∧ endFr.exec.toMachineState.activeWords
              = (fr.exec.toMachineState.mstore (UInt256.ofNat (slotOf t)) w).activeWords
          ∧ endFr.exec.pc = fr.exec.pc + UInt32.ofNat (emitStmt (defsOf prog) (recomputeFuel prog)
                (.assign t (.sload k))).length
          ∧ endFr.exec.executionEnv.code = fr.exec.executionEnv.code
          ∧ endFr.validJumps = fr.validJumps
          ∧ endFr.exec.executionEnv.address = fr.exec.executionEnv.address
          ∧ endFr.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
          ∧ (∀ kk, selfStorage endFr kk = selfStorage fr kk)
          ∧ endFr.exec.stack = []) :
    ∃ endFr, Runs fr endFr ∧ Corr prog sloadChg obs (st.setLocal t w) endFr L (pc + 1)
      ∧ endFr.exec.stack = [] := by
  classical
  obtain ⟨hslot63, hslotplat, endFr, hendrun, hendmembytes, hendmemactive, hendpc, hendcode,
    hendvalid, hendaddr, hendcanmod, hendstorage, hendstk⟩ := hstash
  set slot := slotOf t with hsdef
  set st' := st.setLocal t w with hst'def
  refine ⟨endFr, hendrun, ?_, hendstk⟩
  -- slot addressability collapses (`(ofNat slot).toNat = slot`).
  have hslotlt256 : slot < 2 ^ 256 := by
    have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hslotEq : (UInt256.ofNat slot).toNat = slot := by
    rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslotlt256]
  have hslot63' : (UInt256.ofNat slot).toNat + 63 < 2 ^ 64 := by rw [hslotEq]; exact hslot63
  have hslotplat' : (UInt256.ofNat slot).toNat < 2 ^ System.Platform.numBits := by
    rw [hslotEq]; exact hslotplat
  -- DefsSound survives the sload rebind (B3): `t` is non-recomputable (sload), excluded.
  have hsound' : DefsSound prog st' := by
    obtain ⟨_, _, hsloadArm⟩ := hsc
    obtain ⟨hsloaddef, hscope⟩ := hsloadArm k rfl
    exact defsSound_preserved_assignSload hsloaddef hscope hcorr.defsSound
  -- world is untouched by the assign (sload binds a local, leaves the world).
  have hworld : st'.world = st.world := by rw [hst'def]; rfl
  -- pc advance.
  have hpcN : pcOf prog L (pc + 1)
      = pcOf prog L pc + (emitStmt (defsOf prog) (recomputeFuel prog) (.assign t (.sload k))).length :=
    pcOf_succ prog L b pc (.assign t (.sload k)) hb hs
  refine
    { pc_eq := by rw [hendpc, hcorr.pc_eq, hpcN, UInt32.ofNat_add]
      code_eq := by rw [hendcode]; exact hcorr.code_eq
      validJumps_eq := by rw [hendvalid, hendcode]; exact hcorr.validJumps_eq
      stack_nil := hendstk
      can_modify := by rw [hendcanmod]; exact hcorr.can_modify
      storage := ?_
      defsSound := hsound'
      wellScoped := hscoped'
      memAgree := ?_ }
  · -- M3: the stash writes memory, not storage; self-lens preserved (`hendstorage`).
    intro key
    show selfStorage endFr key = st'.world key
    rw [hendstorage key, hworld]; exact hcorr.storage key
  · -- memAgree: the just-bound sload slot holds `w` (the loaded value); other bound slots
    -- survive the disjoint MSTORE.
    intro tw slot' v hdef hloc
    by_cases htw : tw = t
    · -- the just-bound sload tmp `t`: `slot' = slotOf t = slot`, `v = w`.
      subst htw
      have hvw : v = w := by
        have : st'.locals tw = some w := by rw [hst'def]; simp [V2.IRState.setLocal]
        rw [this] at hloc; exact (Option.some.inj hloc).symm
      have hslot'eq : slot' = slot := by rw [show slot = slotOf tw from rfl]; exact hslots tw slot' hdef
      subst hslot'eq; subst hvw
      refine ⟨?_, ?_, hslot63, ?_⟩
      · rw [hendmembytes]
        have := LirLean.MemAlgebra.mstore_memory_size fr.exec.toMachineState
          (UInt256.ofNat slot) v (by rw [hslotEq]; exact hslotplat)
        rw [hslotEq] at this; show (UInt256.ofNat slot).toNat + 32 ≤ _; rw [hslotEq]; exact this
      · rw [hendmemactive]
        have := LirLean.MemAlgebra.mstore_activeWords_covers fr.exec.toMachineState
          (UInt256.ofNat slot) v hslot63'
        rw [hslotEq] at this; show (UInt256.ofNat slot).toNat + 32 ≤ _; rw [hslotEq]; exact this
      · rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot) hendmembytes hendmemactive]
        exact LirLean.MemAlgebra.mstore_reads_back fr.exec.toMachineState
          (UInt256.ofNat slot) v hslot63' hslotplat'
    · -- another bound tmp `tw ≠ t`: unchanged value; its slot survives the disjoint MSTORE.
      have hloc0 : st.locals tw = some v := by
        rw [hst'def] at hloc; simpa [V2.IRState.setLocal, htw] using hloc
      obtain ⟨hcm, ham, hreal, hval⟩ := hcorr.memAgree tw slot' v hdef hloc0
      have hslot'lt256 : slot' < 2 ^ 256 := by
        have : (2 : Nat) ^ 64 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      have hslot'Eq : (UInt256.ofNat slot').toNat = slot' := by
        rw [LirLean.MemAlgebra.toNat_ofNat, Nat.mod_eq_of_lt hslot'lt256]
      have hslot'def : slot' = slotOf tw := hslots tw slot' hdef
      have htwne : t.id ≠ tw.id := fun h => htw (by cases t; cases tw; cases h; rfl)
      have hdisN : slot + 32 ≤ slot' ∨ slot' + 32 ≤ slot := by
        rw [hsdef, hslot'def]; exact LirLean.MemAlgebra.slot_windows_disjoint t.id tw.id htwne
      have hdisN' : (UInt256.ofNat slot').toNat + 32 ≤ (UInt256.ofNat slot).toNat
          ∨ (UInt256.ofNat slot).toNat + 32 ≤ (UInt256.ofNat slot').toNat := by
        rw [hslotEq, hslot'Eq]; exact hdisN.symm
      obtain ⟨hmem', hact', hval'⟩ :=
        LirLean.MemAlgebra.mstore_preserves_slot_grow fr.exec.toMachineState
          (UInt256.ofNat slot) (UInt256.ofNat slot') w hslot63' hslotplat' hcm ham hdisN'
      refine ⟨?_, ?_, hreal, ?_⟩
      · rw [hendmembytes]; exact hmem'
      · rw [hendmemactive]; exact hact'
      · rw [LirLean.MemAlgebra.mload_congr (UInt256.ofNat slot') hendmembytes hendmemactive]
        exact hval'.trans hval

end Lir


-- Build-enforced axiom-cleanliness guard for the C-layer `sim_stmt` deliverable: the four
-- per-statement simulation arms depend only on `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.sim_assign
#print axioms Lir.sim_sstore_stmt
#print axioms Lir.sim_call_stmt
#print axioms Lir.sim_assign_sload
