import LirLean.Match
import LirLean.MaterialiseGas
import LirLean.DefsSound

/-!
# LirLean — `materialise_runs` (Layer **B1** of the `lower_conforms` grind)

`docs/lower-conforms-plan.md` node **B1**, *the linchpin*: running the lowered
push-sequence of an expression (`materialiseExpr defs fuel e`) reproduces, on the
bytecode stack, the value the IR's `evalExpr` computes — and does so leaving the
code, the self-storage and the gas-charge envelope (B2) all accounted for.

This module proves **B1 totally over `Expr`** — `imm` / `tmp` / `add` / `lt` / `sload`
/ `gas` — fully and axiom-cleanly. The induction mirrors `materialiseExpr`
constructor-for-constructor; the leaf/recursion steps are the `Match.lean` bricks
`sim_imm` / `sim_add` / `sim_lt` / `sim_sload` / `sim_gas`; the `.tmp t` recursion
consumes **B3** (`DefsSound`) to equate the recomputed value with `st.locals t`; the
whole-expression gas contract is discharged through **B2** (`MaterialiseGasCharge` +
`materialiseGasCharge_binop` / `materialiseGasCharge_sload` / `materialiseGasCharge_gas`).
The two non-pure leaves `.sload` / `.gas` are closed under **explicit realisability
side-conditions** (`SloadRealises` / `GasRealises` / `StorageAgree`, below) — the honest
runtime ties the realised trace supplies downstream (Layers C/D/F); they are *not*
excluded.

## The honest decode interface

`materialiseExpr` is a *concrete byte stream*; each opcode in it must `decode`
correctly at its running cursor. Deriving those decode facts generically from the
offset-table byte layout (Layer A) requires, for every `PUSH32 w`, that the 32
big-endian immediate bytes `uInt256OfByteArray` back to `w` — a per-literal fact the
worked program discharges by `decide`/`rfl` (`LirLean/Decode.lean`) but which has no
uniform closed form over an arbitrary `w`. We therefore take the decode facts as a
**structured hypothesis** `MatDec` that mirrors `materialiseExpr`'s recursion exactly
(one decode clause per emitted opcode, at the cursor that opcode runs at) — precisely
how every `sim_*` brick takes its `hdec` as a hypothesis. `MatDec` is phrased
relative to the *running frame's* program counter, so the recursion threads cursors
by the post-frames' own pc advance (`UInt32.ofNat_add`), never re-deriving the layout.
Layer A (`decode_at_offset_*`) is what discharges `MatDec` against `lower prog` at the
call site; that wiring is the B1→A composition, downstream of this linchpin.

## The two non-pure leaves, closed under explicit realisability ties

**`.gas`.** `materialiseExpr … .gas = [GAS]`, and `sim_gas` pushes the frame's
*post-`Gbase`* `gasAvailable`, whereas `evalExpr st obs .gas = some obs` (the supplied
value). The two agree under the **realisability tie** `GasRealises obs fr` —
`obs = UInt256.ofUInt64 (post-Gbase gas)` at the running frame — supplied as a
hypothesis quantified over the running frame (the gas-oracle realisability, downstream).

**`.sload`.** `materialiseExpr … (.sload k) = … ++ [SLOAD]`. Fully closed: the value
channel is `sim_sload` + the `sloadFrame` storage lens (`sloadFrame_stack`) tied to
`st.world key` by `StorageAgree` (preserved across the materialisation by
`MatRuns.storage`); the gas contract is `materialiseGasCharge_sload` with the B2
`sloadChg k` resolved to the **actual** `sloadCost warm` at the *internal* SLOAD frame
`frk` by `SloadRealises` (quantified over the frame, address agreement carried by
`MatRuns.addr`). SLOAD's accessed-key substate evolution touches no `MatRuns` clause
(it changes `accessedStorageKeys`, never a storage *value*, code, address, or
pc-length), so the bundle survives it directly.

No `sorry`, no `axiom`, no `native_decide`. Bytecode-coupled (imports `Match.lean`);
nothing here touches `V2/Machine.lean` / `V2/Law.lean` (the frame-free spine).
-/

namespace Lir

open Evm
open GasConstants
open BytecodeLayer.Hoare
open BytecodeLayer.Dispatch

/-! ## Frame-accessor reductions for the materialise post-frames

Each `sim_*` post-frame (`pushFrameW` / `addFrame` / `ltFrame` / `sloadFrame`) leaves
the `executionEnv` (hence `code`, `address`, `canModifyState`) untouched — only
`stack`, `pc`, `gasAvailable` (and, for SLOAD, the accessed-key substate, never a
storage *value*) change. These `rfl` lemmas expose exactly the clauses B1's invariant
threads. -/

@[simp] theorem pushFrameW_code (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem pushFrameW_addr (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem pushFrameW_selfStorage (fr : Frame) (w : Word) (width : UInt8) (k : Word) :
    selfStorage (pushFrameW fr w width) k = selfStorage fr k := rfl

@[simp] theorem pushFrameW_pc (fr : Frame) (w : Word) (width : UInt8) :
    (pushFrameW fr w width).exec.pc = fr.exec.pc + (width + 1).toUInt32 := rfl

@[simp] theorem addFrame_code (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem addFrame_addr (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem addFrame_selfStorage (fr : Frame) (a b : Word) (rest : Stack Word) (k : Word) :
    selfStorage (addFrame fr a b rest) k = selfStorage fr k := rfl

@[simp] theorem addFrame_pc (fr : Frame) (a b : Word) (rest : Stack Word) :
    (addFrame fr a b rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem ltFrame_code (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem ltFrame_addr (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem ltFrame_selfStorage (fr : Frame) (a b : Word) (rest : Stack Word) (k : Word) :
    selfStorage (ltFrame fr a b rest) k = selfStorage fr k := rfl

@[simp] theorem ltFrame_pc (fr : Frame) (a b : Word) (rest : Stack Word) :
    (ltFrame fr a b rest).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem sloadFrame_code (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem sloadFrame_addr (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem sloadFrame_selfStorage (fr : Frame) (key : Word) (rest : Stack Word) (k : Word) :
    selfStorage (sloadFrame fr key rest) k = selfStorage fr k := rfl

@[simp] theorem sloadFrame_pc (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.pc = fr.exec.pc + 1 := rfl

/-- `sloadFrame`'s stack is `rest` with the self-storage cell at `key` pushed (the
value `sloadFrame_storage_self` exposes through the `M3` lens). -/
@[simp] theorem sloadFrame_stack (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.stack = rest.push (selfStorage fr key) := rfl

/-- `SLOAD` charges exactly `sloadCost warm` at `fr` (`warm` the runtime warmth from
`fr`'s accessed-storage-key substate). This is the runtime cost the B2 resolver
`sloadChg k` must equal at the internal SLOAD frame. -/
@[simp] theorem sloadFrame_gas (fr : Frame) (key : Word) (rest : Stack Word) :
    (sloadFrame fr key rest).exec.gasAvailable
      = fr.exec.gasAvailable - UInt64.ofNat (Evm.sloadCost
          (fr.exec.substate.accessedStorageKeys.contains (fr.exec.executionEnv.address, key))) :=
  rfl

/-! ### `gasFrame` accessor reductions

`gasFrame fr` (the `GAS` post-frame) leaves `executionEnv` (code/address) and the
account storage untouched; it charges `Gbase`, pushes `ofUInt64` of the *post-charge*
gas, and advances pc by one. These `rfl` lemmas expose exactly those clauses. -/

@[simp] theorem gasFrame_code (fr : Frame) :
    (gasFrame fr).exec.executionEnv.code = fr.exec.executionEnv.code := rfl

@[simp] theorem gasFrame_addr (fr : Frame) :
    (gasFrame fr).exec.executionEnv.address = fr.exec.executionEnv.address := rfl

@[simp] theorem gasFrame_selfStorage (fr : Frame) (k : Word) :
    selfStorage (gasFrame fr) k = selfStorage fr k := rfl

@[simp] theorem gasFrame_pc (fr : Frame) :
    (gasFrame fr).exec.pc = fr.exec.pc + 1 := rfl

@[simp] theorem gasFrame_stack (fr : Frame) :
    (gasFrame fr).exec.stack
      = fr.exec.stack.push (UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase)) :=
  rfl

@[simp] theorem gasFrame_gas (fr : Frame) :
    (gasFrame fr).exec.gasAvailable = fr.exec.gasAvailable - UInt64.ofNat Gbase := rfl

/-! ## The decode bundle `MatDec`

`MatDec code defs sloadChg fuel p e` is the structured decode hypothesis B1 consumes:
one `decode code … = …` clause per opcode `materialiseExpr defs fuel e` emits, anchored
at the running program counter (`p` is the starting pc; the recursion advances it by
the post-frames' own pc deltas via `UInt32.ofNat_add`). It mirrors `materialiseExpr`
constructor-for-constructor — exactly the shape Layer A's `decode_at_offset_*`
discharges over `lower prog`. The `.sload` clause carries the key-materialise decode
facts plus the `SLOAD` opcode decode; the runtime warmth-cost resolution
(`sloadChg k = sloadCost warm` at the SLOAD frame) is a *separate* realisability
side-condition `SloadRealises`, supplied to `materialise_runs` directly. -/
def MatDec (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) :
    Nat → UInt32 → Expr → Prop
  | _,      p, .imm w  => decode code p = some (.Push .PUSH32, some (w, 32))
  | 0,      _, _       => False   -- fuel exhausted on a non-leaf: no decode facts ⇒ unusable
  | f + 1,  p, .tmp t  =>
      match defs t with
      | some e => MatDec code defs sloadChg f p e
      | none   => decode code p = some (.Push .PUSH32, some ((0 : Word), 32))
  | f + 1,  p, .add a b =>
      MatDec code defs sloadChg f p (.tmp b)
      ∧ MatDec code defs sloadChg f
          (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length) (.tmp a)
      ∧ decode code
          (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
             + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length)
          = some (.ArithLogic .ADD, .none)
  | f + 1,  p, .lt a b =>
      MatDec code defs sloadChg f p (.tmp b)
      ∧ MatDec code defs sloadChg f
          (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length) (.tmp a)
      ∧ decode code
          (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
             + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length)
          = some (.ArithLogic .LT, .none)
  | f + 1,  p, .sload k =>
      MatDec code defs sloadChg f p (.tmp k)
      ∧ decode code (p + UInt32.ofNat (materialiseExpr defs f (.tmp k)).length)
          = some (.Smsf .SLOAD, .none)
  | _ + 1,  p, .gas    => decode code p = some (.Smsf .GAS, .none)

/-! ### `MatDec` reduction lemmas (definitional; pair with `materialiseExpr`'s shape) -/

@[simp] theorem matDec_imm (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (fuel : Nat) (p : UInt32) (w : Word) :
    MatDec code defs sloadChg fuel p (.imm w)
      = (decode code p = some (.Push .PUSH32, some (w, 32))) := by
  cases fuel <;> rfl

theorem matDec_tmp_some (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (p : UInt32) (t : Tmp) (e : Expr) (h : defs t = some e) :
    MatDec code defs sloadChg (f + 1) p (.tmp t) = MatDec code defs sloadChg f p e := by
  show (match defs t with | some e => MatDec code defs sloadChg f p e | none => _) = _
  rw [h]

theorem matDec_tmp_none (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (p : UInt32) (t : Tmp) (h : defs t = none) :
    MatDec code defs sloadChg (f + 1) p (.tmp t)
      = (decode code p = some (.Push .PUSH32, some ((0 : Word), 32))) := by
  show (match defs t with | some e => _ | none => decode code p = _) = _
  rw [h]

@[simp] theorem matDec_add (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (p : UInt32) (a b : Tmp) :
    MatDec code defs sloadChg (f + 1) p (.add a b)
      = (MatDec code defs sloadChg f p (.tmp b)
        ∧ MatDec code defs sloadChg f
            (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length) (.tmp a)
        ∧ decode code
            (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
               + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length)
            = some (.ArithLogic .ADD, .none)) := rfl

@[simp] theorem matDec_lt (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (p : UInt32) (a b : Tmp) :
    MatDec code defs sloadChg (f + 1) p (.lt a b)
      = (MatDec code defs sloadChg f p (.tmp b)
        ∧ MatDec code defs sloadChg f
            (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length) (.tmp a)
        ∧ decode code
            (p + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
               + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length)
            = some (.ArithLogic .LT, .none)) := rfl

@[simp] theorem matDec_sload (code : ByteArray) (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ)
    (f : Nat) (p : UInt32) (k : Tmp) :
    MatDec code defs sloadChg (f + 1) p (.sload k)
      = (MatDec code defs sloadChg f p (.tmp k)
        ∧ decode code (p + UInt32.ofNat (materialiseExpr defs f (.tmp k)).length)
            = some (.Smsf .SLOAD, .none)) := rfl

/-! ## The B1 conclusion bundle

`MatRuns defs sloadChg fuel e w fr fr'` packages everything B1 delivers about the
materialise endpoint `fr'` reached from `fr` by running `materialiseExpr defs fuel e`:
the run itself, the value `w` pushed (= `evalExpr`'s value), code/address/self-storage
preserved, the pc advanced by the emitted byte length, and the B2 gas contract (plus
its `toNat` form, threaded so each step's gas bound follows). -/
structure MatRuns (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (fuel : Nat)
    (e : Expr) (w : Word) (fr fr' : Frame) : Prop where
  runs       : Runs fr fr'
  stack      : fr'.exec.stack = fr.exec.stack.push w
  code       : fr'.exec.executionEnv.code = fr.exec.executionEnv.code
  addr       : fr'.exec.executionEnv.address = fr.exec.executionEnv.address
  canMod     : fr'.exec.executionEnv.canModifyState = fr.exec.executionEnv.canModifyState
  storage    : ∀ k, selfStorage fr' k = selfStorage fr k
  pc         : fr'.exec.pc = fr.exec.pc + UInt32.ofNat (materialiseExpr defs fuel e).length
  gasCharge  : MaterialiseGasCharge defs sloadChg fuel e fr fr'
  gasToNat   : fr'.exec.gasAvailable.toNat
                 = fr.exec.gasAvailable.toNat - (chargeOf defs sloadChg fuel e).sum

/-! ## Small arithmetic facts -/

/-- `(emitImm w).length = 33` (a `PUSH32` opcode byte + 32 immediate bytes). -/
theorem emitImm_length (w : Word) : (emitImm w).length = 33 := by
  simp [emitImm, wordBytesBE]

/-- The materialise length of a literal is `33`. -/
theorem materialiseExpr_imm_length (defs : Tmp → Option Expr) (fuel : Nat) (w : Word) :
    (materialiseExpr defs fuel (.imm w)).length = 33 := by
  cases fuel <;> simp [materialiseExpr, emitImm_length]

/-! ### `materialiseExpr` reduction lemmas (pair with `chargeOf`/`MatDec`) -/

theorem materialiseExpr_tmp_some (defs : Tmp → Option Expr) (f : Nat) (t : Tmp) (e : Expr)
    (h : defs t = some e) :
    materialiseExpr defs (f + 1) (.tmp t) = materialiseExpr defs f e := by
  show (match defs t with | some e => materialiseExpr defs f e | none => emitImm 0) = _
  rw [h]

theorem materialiseExpr_tmp_none (defs : Tmp → Option Expr) (f : Nat) (t : Tmp)
    (h : defs t = none) :
    materialiseExpr defs (f + 1) (.tmp t) = emitImm (0 : Word) := by
  show (match defs t with | some e => materialiseExpr defs f e | none => emitImm 0) = _
  rw [h]

@[simp] theorem materialiseExpr_add (defs : Tmp → Option Expr) (f : Nat) (a b : Tmp) :
    materialiseExpr defs (f + 1) (.add a b)
      = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.add] := rfl

@[simp] theorem materialiseExpr_lt (defs : Tmp → Option Expr) (f : Nat) (a b : Tmp) :
    materialiseExpr defs (f + 1) (.lt a b)
      = materialiseExpr defs f (.tmp b) ++ materialiseExpr defs f (.tmp a) ++ [Byte.lt] := rfl

@[simp] theorem materialiseExpr_sload (defs : Tmp → Option Expr) (f : Nat) (k : Tmp) :
    materialiseExpr defs (f + 1) (.sload k)
      = materialiseExpr defs f (.tmp k) ++ [Byte.sload] := rfl

/-- The charge list of a `.tmp` lookup is non-empty whenever its decode bundle holds —
materialising a defined/undefined tmp emits at least one opcode. (Used for the stack
depth bound in the binary-op case.) -/
theorem chargeOf_length_pos_of_matDec (code : ByteArray) (defs : Tmp → Option Expr)
    (sloadChg : Tmp → ℕ) (fuel : Nat) (p : UInt32) (e : Expr)
    (h : MatDec code defs sloadChg fuel p e) :
    1 ≤ (chargeOf defs sloadChg fuel e).length := by
  cases fuel with
  | zero =>
      cases e with
      | imm w => rw [chargeOf_imm]; simp
      | _ => exact absurd h (by simp [MatDec])
  | succ f =>
      cases e with
      | imm w => rw [chargeOf_imm]; simp
      | gas => rw [chargeOf_gas]; simp
      | tmp t =>
          cases ht : defs t with
          | some e => rw [chargeOf_tmp_some defs sloadChg f t e ht]
                      exact chargeOf_length_pos_of_matDec code defs sloadChg f p e
                        (by rw [matDec_tmp_some code defs sloadChg f p t e ht] at h; exact h)
          | none  => rw [chargeOf_tmp_none defs sloadChg f t ht]; simp
      | add a b => rw [chargeOf_add]; simp only [List.length_append, List.length_singleton]; omega
      | lt a b => rw [chargeOf_lt]; simp only [List.length_append, List.length_singleton]; omega
      | sload k => rw [chargeOf_sload]; simp only [List.length_append, List.length_singleton]; omega

/-- `(32 + 1 : UInt8).toUInt32 = UInt32.ofNat 33`. -/
theorem push32_pcΔ : ((32 : UInt8) + 1).toUInt32 = UInt32.ofNat 33 := by decide

/-! ## The `.imm` leaf -/

/-- **B1 for the `.imm` leaf.** A frame whose code decodes to `PUSH32 w` at its pc,
with `Gverylow` gas and stack room, runs to `pushFrameW fr w 32`, which satisfies the
whole `MatRuns` bundle for `.imm w` (the value `w = evalExpr st obs (.imm w)`). -/
theorem matRuns_imm (defs : Tmp → Option Expr) (sloadChg : Tmp → ℕ) (fuel : Nat)
    (fr : Frame) (w : Word)
    (hdec : MatDec fr.exec.executionEnv.code defs sloadChg fuel fr.exec.pc (.imm w))
    (hgas : (chargeOf defs sloadChg fuel (.imm w)).sum ≤ fr.exec.gasAvailable.toNat)
    (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    MatRuns defs sloadChg fuel (.imm w) w fr (pushFrameW fr w 32) := by
  have hdec' : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH32, some (w, 32)) := by
    rw [matDec_imm] at hdec; exact hdec
  have hg3 : 3 ≤ fr.exec.gasAvailable.toNat := by
    rw [chargeOf_imm] at hgas; simpa [show Gverylow = 3 from rfl] using hgas
  refine
    { runs := (sim_imm fr w hdec' hg3 hstk).1
      stack := (sim_imm fr w hdec' hg3 hstk).2
      code := rfl
      addr := rfl
      canMod := rfl
      storage := fun _ => rfl
      pc := ?_
      gasCharge := materialiseGasCharge_imm defs sloadChg fuel fr w hdec' hg3 hstk
      gasToNat := ?_ }
  · rw [pushFrameW_pc, push32_pcΔ, materialiseExpr_imm_length]
  · show (fr.exec.gasAvailable - UInt64.ofNat Gverylow).toNat = _
    rw [chargeOf_imm]
    have : (3 : ℕ) ≤ fr.exec.gasAvailable.toNat := hg3
    rw [show Gverylow = 3 from rfl,
        BytecodeLayer.UInt64.toNat_sub_ofNat _ 3 this (by omega)]
    simp [List.sum_cons]

/-! ## `evalExpr` obs-irrelevance on the pure fragment

`Lir.V2.evalExpr` reads its `obs` argument **only** in the `.gas` arm. So for any
non-`gas` expression the supplied gas value is irrelevant — this is what lets B1's
`.tmp t` recursion bridge `DefsSound`'s `evalExpr st 0 e'` to the `obs`-threaded value
the rest of the induction carries. -/
theorem evalExpr_obs_irrel (st : V2.IRState) (obs obs' : Word) :
    ∀ {e : Expr}, e ≠ .gas → V2.evalExpr st obs e = V2.evalExpr st obs' e
  | .imm _,   _ => rfl
  | .tmp _,   _ => rfl
  | .add _ _, _ => rfl
  | .lt _ _,  _ => rfl
  | .sload _, _ => rfl
  | .gas,     h => absurd rfl h

/-! ## The realisability side-conditions (`SLOAD` warmth / `GAS` value / storage lens)

The two non-pure leaves — `SLOAD` and `GAS` — each have one *runtime* fact the static
materialisation cannot pin: the SLOAD warmth-cost (whether `(self, key)` is in the
running frame's accessed-key substate) and the `GAS` value (the post-`Gbase` gas the
running frame reports). These are not uniform over `Expr`; they are properties of the
**realised trace** the downstream layers (C/D/F, the gas/state oracle's realisability)
supply. We package each as an explicit, honestly-stated hypothesis on
`materialise_runs`, quantified over the running frame so the recursion threads it
unchanged into every sub-frame:

* **`SloadRealises`** — the B2 resolver `sloadChg k` equals the actual `sloadCost`
  warmth-charge at *every* frame with the same self-address as `fr`. This is exactly
  the warmth-cost tie at the internal SLOAD frame `frk` (reached after materialising
  the key), whose address agrees with `fr` (carried by `MatRuns.addr`) and whose
  substate is the realised one. The `.sload` arm is then **fully closed** against it —
  value channel (storage lens), gas contract (`materialiseGasCharge_sload`), and the
  accessed-key substate evolution (which touches no `MatRuns` clause: SLOAD changes
  `accessedStorageKeys`, never a storage *value*, code, address, or pc-length).

* **`GasRealises`** — the supplied gas word `obs` equals `UInt256.ofUInt64` of the
  post-`Gbase` gas at *every* frame with the same self-address as `fr` (the realised
  running-frame gas the gas oracle reports). The `.gas` arm is closed under it.

* **`StorageAgree`** — the `M3` storage correspondence `selfStorage fr key = st.world
  key`. Preserved across the whole materialisation by `MatRuns.storage` (every
  post-frame leaves the self account's storage *values* untouched), so it threads as a
  plain per-frame fact (re-established at each sub-frame via the `storage` clause). It
  ties the SLOAD value channel (`selfStorage frk key`) to `evalExpr`'s `st.world key`.

These are the honest realisability obligations, factored *out* of the static proof and
discharged downstream by the realised trace — making `materialise_runs` **total over
`Expr`** with `.sload`/`.gas` carrying their side-conditions rather than being excluded
by a pure-stream restriction (retired: the general theorem strictly subsumes it). -/

/-- The B2 SLOAD-cost resolver realisability: at every frame `g` sharing `fr`'s
self-address, `sloadChg k` is the actual `sloadCost` warmth-charge for the bound key
`st.locals k`. (Quantified over `g` so the recursion applies it at the internal SLOAD
frame `frk`, whose address agrees with `fr` by `MatRuns.addr`.) -/
def SloadRealises (sloadChg : Tmp → ℕ) (st : V2.IRState) (fr : Frame) : Prop :=
  ∀ (g : Frame) (k : Tmp) (key : Word),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    st.locals k = some key →
    sloadChg k
      = Evm.sloadCost (g.exec.substate.accessedStorageKeys.contains
          (g.exec.executionEnv.address, key))

/-- The `GAS` value realisability: at every frame `g` sharing `fr`'s self-address, the
supplied gas word `obs` is `ofUInt64` of the post-`Gbase` gas `g` reports. (Quantified
over `g` so the recursion applies it at the actual `GAS` running frame.) -/
def GasRealises (obs : Word) (fr : Frame) : Prop :=
  ∀ (g : Frame),
    g.exec.executionEnv.address = fr.exec.executionEnv.address →
    obs = UInt256.ofUInt64 (g.exec.gasAvailable - UInt64.ofNat Gbase)

/-- The `M3` storage correspondence: the self account's stored value at `key` (through
the observable lens) equals the IR world. Threaded as a plain per-frame fact —
preserved across the materialisation by `MatRuns.storage`. -/
def StorageAgree (st : V2.IRState) (fr : Frame) : Prop :=
  ∀ key, selfStorage fr key = st.world key

/-! ### Transport of the realisability side-conditions across a sub-frame

`SloadRealises`/`GasRealises` are quantified over the running frame and only constrain
frames sharing `fr`'s self-address, so they transport verbatim to any sub-frame `fr'`
with `fr'.address = fr.address` (carried by `MatRuns.addr`). `StorageAgree` transports
through the self-storage equality `MatRuns.storage` provides. These are exactly the
clauses the `add`/`lt`/`sload` recursion needs to pass the side-conditions to its
second/inner operand. -/

theorem SloadRealises.transport {sloadChg : Tmp → ℕ} {st : V2.IRState} {fr fr' : Frame}
    (h : SloadRealises sloadChg st fr)
    (haddr : fr'.exec.executionEnv.address = fr.exec.executionEnv.address) :
    SloadRealises sloadChg st fr' :=
  fun g k key hg hl => h g k key (by rw [hg, haddr]) hl

theorem GasRealises.transport {obs : Word} {fr fr' : Frame}
    (h : GasRealises obs fr)
    (haddr : fr'.exec.executionEnv.address = fr.exec.executionEnv.address) :
    GasRealises obs fr' :=
  fun g hg => h g (by rw [hg, haddr])

theorem StorageAgree.transport {st : V2.IRState} {fr fr' : Frame}
    (h : StorageAgree st fr)
    (hstor : ∀ k, selfStorage fr' k = selfStorage fr k) :
    StorageAgree st fr' :=
  fun key => by rw [hstor key]; exact h key

/-! ## The linchpin — `materialise_runs` (total over `Expr`)

The induction mirrors `materialiseExpr` constructor-for-constructor. The value channel
B1 closes: `imm` (leaf), `tmp` (recompute via **B3** `DefsSound`), `add`/`lt` (operands
then op, via `sim_add`/`sim_lt` and the **B2** gluing law `materialiseGasCharge_binop`),
`sload` (key then SLOAD, via `sim_sload` + the storage lens + `materialiseGasCharge_sload`,
under `SloadRealises`/`StorageAgree`), and `gas` (via `sim_gas` + `materialiseGasCharge_gas`,
under `GasRealises`). The three realisability side-conditions thread through the
recursion unchanged (quantified over the running frame; address agreement is carried by
`MatRuns.addr`, the storage agreement by `MatRuns.storage`). -/

/-- **B1 `materialise_runs` (total over `Expr`).** Running `materialiseExpr defsOf fuel
e` from a frame `fr` whose code decodes as the bundle `MatDec` prescribes, with the IR
state `st` recompute-sound (`DefsSound`, **B3**), the storage lens agreeing
(`StorageAgree`) and the SLOAD/GAS realisability ties holding (`SloadRealises` /
`GasRealises`), reproduces `evalExpr st obs e = some w` on the bytecode stack and
delivers the whole `MatRuns` bundle: the run, the pushed value (= `evalExpr`'s),
code/address/self-storage preserved, pc advanced by the emitted byte length, and the
**B2** gas contract `MaterialiseGasCharge`. The decode facts `MatDec` and the gas/stack
room are the per-opcode preconditions the `sim_*`/B2 bricks consume; Layer A
(`decode_at_offset_*`) discharges `MatDec` over `lower prog` at the call site, and the
realised trace (Layers C/D/F) discharges the realisability side-conditions. -/
theorem materialise_runs {prog : Program} (sloadChg : Tmp → ℕ)
    (fuel : Nat) (st : V2.IRState) (obs : Word) :
    ∀ (e : Expr) (w : Word) (fr : Frame),
      MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg fuel fr.exec.pc e →
      DefsSound prog st →
      -- recompute-sound, define-before-use scoping: every currently-bound tmp is
      -- recomputable (not gas-/call-defined) and present in the recompute env. This is
      -- the honest `WellScoped` content the plan documents (DefsSound's preservation
      -- side conditions); it makes the `.tmp` recursion total and value-faithful.
      (∀ t, st.locals t ≠ none → ¬ NonRecomputable prog t ∧ defsOf prog t ≠ none) →
      StorageAgree st fr →
      SloadRealises sloadChg st fr →
      GasRealises obs fr →
      V2.evalExpr st obs e = some w →
      (chargeOf (defsOf prog) sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat →
      fr.exec.stack.size + (chargeOf (defsOf prog) sloadChg fuel e).length ≤ 1024 →
      ∃ fr', MatRuns (defsOf prog) sloadChg fuel e w fr fr' := by
  set defs := defsOf prog with hdefs
  induction fuel with
  | zero =>
      intro e w fr hdec _ _ _ _ _ heval hgas hstk
      cases e with
      | imm v =>
          refine ⟨pushFrameW fr v 32, ?_⟩
          rw [show w = v from (Option.some.inj heval).symm]
          exact matRuns_imm defs sloadChg 0 fr v hdec hgas
            (by rw [chargeOf_imm] at hstk; simpa using hstk)
      | _ => exact absurd hdec (by simp [MatDec])
  | succ f ih =>
      intro e w fr hdec hsound hscoped hstore hsload hgasreal heval hgas hstk
      cases e with
      | imm v =>
          refine ⟨pushFrameW fr v 32, ?_⟩
          rw [show w = v from (Option.some.inj heval).symm]
          exact matRuns_imm defs sloadChg (f + 1) fr v hdec hgas
            (by rw [chargeOf_imm] at hstk; simpa using hstk)
      | gas =>
          -- `GAS` leaf: `sim_gas` pushes `ofUInt64` of the post-`Gbase` gas; under
          -- `GasRealises` that is `obs`, which is `evalExpr st obs .gas`.
          have hdec' : decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none) := by
            rw [show MatDec fr.exec.executionEnv.code defs sloadChg (f+1) fr.exec.pc .gas
                  = (decode fr.exec.executionEnv.code fr.exec.pc = some (.Smsf .GAS, .none))
                from rfl] at hdec
            exact hdec
          have hwval : w = UInt256.ofUInt64 (fr.exec.gasAvailable - UInt64.ofNat Gbase) := by
            have : some w = some obs := by rw [← heval]; rfl
            rw [Option.some.inj this]
            exact hgasreal fr rfl
          have hg2 : GasConstants.Gbase ≤ fr.exec.gasAvailable.toNat := by
            rw [chargeOf_gas] at hgas; simpa [List.sum_cons] using hgas
          have hsz1 : fr.exec.stack.size + 1 ≤ 1024 := by
            rw [chargeOf_gas] at hstk; simpa using hstk
          refine ⟨gasFrame fr, ?_⟩
          refine
            { runs := (sim_gas fr hdec' hsz1 hg2).1
              stack := by rw [gasFrame_stack, hwval]
              code := rfl
              addr := rfl
              canMod := rfl
              storage := fun _ => rfl
              pc := by
                rw [gasFrame_pc, show (materialiseExpr defs (f+1) .gas).length = 1 from rfl,
                    show (UInt32.ofNat 1) = 1 from rfl]
              gasCharge := materialiseGasCharge_gas defs sloadChg f fr hdec' hsz1 hg2
              gasToNat := ?_ }
          show (fr.exec.gasAvailable - UInt64.ofNat Gbase).toNat = _
          rw [chargeOf_gas]
          have hg2' : (2 : ℕ) ≤ fr.exec.gasAvailable.toNat := by
            rw [show Gbase = 2 from rfl] at hg2; exact hg2
          rw [show Gbase = 2 from rfl,
              BytecodeLayer.UInt64.toNat_sub_ofNat _ 2 hg2' (by omega)]
          simp [List.sum_cons]
      | sload k =>
          -- `SLOAD`: materialise the key `k` (recompute), then run `SLOAD`. Value =
          -- `selfStorage frk key = st.world key` (storage lens + `StorageAgree`); gas =
          -- `sloadCost warm` at `frk`, matched to `sloadChg k` by `SloadRealises`.
          obtain ⟨key, hlk, hwsl⟩ :
              ∃ key, st.locals k = some key ∧ w = st.world key := by
            simp only [V2.evalExpr] at heval
            cases hlk : st.locals k with
            | none => simp [hlk] at heval
            | some key => exact ⟨key, rfl, by simp [hlk] at heval; exact heval.symm⟩
          subst hwsl
          -- decode bundle decomposition (key materialise + SLOAD opcode).
          obtain ⟨hdk, hop⟩ := hdec
          have hcsl : chargeOf defs sloadChg (f + 1) (.sload k)
              = chargeOf defs sloadChg f (.tmp k) ++ [sloadChg k] := chargeOf_sload defs sloadChg f k
          -- evalExpr of the key tmp = its bound value.
          have hevk : V2.evalExpr st obs (.tmp k) = some key := hlk
          -- the whole-`sload` charge sum / length, split once.
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.sload k)).sum
              = (chargeOf defs sloadChg f (.tmp k)).sum + sloadChg k := by
            rw [hcsl]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.sload k)).length
              = (chargeOf defs sloadChg f (.tmp k)).length + 1 := by
            rw [hcsl]; simp only [List.length_append, List.length_singleton]
          -- IH on the key tmp from `fr`.
          have hgask : (chargeOf defs sloadChg f (.tmp k)).sum ≤ fr.exec.gasAvailable.toNat := by
            rw [hsum_split] at hgas; omega
          have hstkk : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp k)).length ≤ 1024 := by
            rw [hlen_split] at hstk; omega
          obtain ⟨frk, hmrk⟩ := ih (.tmp k) key fr hdk hsound hscoped hstore hsload hgasreal
            hevk hgask hstkk
          -- the internal SLOAD frame `frk`: key on top of `fr`'s stack, addr/code/storage
          -- preserved. The SLOAD opcode runs here.
          have hkcode : frk.exec.executionEnv.code = fr.exec.executionEnv.code := hmrk.code
          have hkaddr : frk.exec.executionEnv.address = fr.exec.executionEnv.address := hmrk.addr
          have hkpc : frk.exec.pc = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp k)).length :=
            hmrk.pc
          have hkstk : frk.exec.stack = key :: fr.exec.stack := by
            rw [hmrk.stack]; rfl
          have hkdec : decode frk.exec.executionEnv.code frk.exec.pc
              = some (.Smsf .SLOAD, .none) := by
            rw [hkcode, hkpc]; exact hop
          -- the runtime warmth at `frk`, resolved to `sloadChg k` by `SloadRealises`.
          have hwarm : sloadChg k
              = Evm.sloadCost (frk.exec.substate.accessedStorageKeys.contains
                  (frk.exec.executionEnv.address, key)) :=
            hsload frk k key hkaddr hlk
          -- stack-room and gas bound for the SLOAD step.
          have hksz : frk.exec.stack.size ≤ 1024 := by
            have hfrksz : frk.exec.stack.size = fr.exec.stack.size + 1 := by
              rw [hkstk]; simp
            have hpk1 : 1 ≤ (chargeOf defs sloadChg f (.tmp k)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp k) hdk
            rw [hlen_split] at hstk; rw [hfrksz]; omega
          have hksloadgas :
              Evm.sloadCost (frk.exec.substate.accessedStorageKeys.contains
                (frk.exec.executionEnv.address, key)) ≤ frk.exec.gasAvailable.toNat := by
            rw [hmrk.gasToNat, ← hwarm]; rw [hsum_split] at hgas; omega
          obtain ⟨hslrun, hslhd⟩ := sim_sload frk key fr.exec.stack hkdec hkstk hksz hksloadgas
          -- the pushed value: the self-storage cell at `key` = `st.world key` (StorageAgree),
          -- preserved from `fr` to `frk` by the storage clause.
          have hval : selfStorage frk key = st.world key := by
            rw [hmrk.storage key]; exact hstore key
          refine ⟨sloadFrame frk key fr.exec.stack, ?_⟩
          refine
            { runs := hmrk.runs.trans hslrun
              stack := ?_
              code := ?_
              addr := ?_
              canMod := ?_
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_ }
          · rw [sloadFrame_stack, hval]
          · rw [sloadFrame_code, hkcode]
          · rw [sloadFrame_addr, hkaddr]
          · show (sloadFrame frk key fr.exec.stack).exec.executionEnv.canModifyState = _
            rw [show (sloadFrame frk key fr.exec.stack).exec.executionEnv.canModifyState
                  = frk.exec.executionEnv.canModifyState from rfl, hmrk.canMod]
          · intro k'; rw [sloadFrame_selfStorage, hmrk.storage]
          · rw [sloadFrame_pc, hkpc, materialiseExpr_sload]
            simp only [List.length_append, List.length_singleton]
            rw [UInt32.ofNat_add, show (UInt32.ofNat 1) = 1 from rfl]
            ac_rfl
          · -- gas contract via the `sload` gluing law: `sloadChg k` matches the runtime cost.
            refine materialiseGasCharge_sload defs sloadChg f k fr frk
              (sloadFrame frk key fr.exec.stack) hmrk.gasCharge ?_
            rw [sloadFrame_gas, hwarm]
            rw [subCharges_singleton]
          · -- gasToNat from the gas contract + toNat_chargeOf.
            have hsum : (chargeOf defs sloadChg (f + 1) (.sload k)).sum
                ≤ fr.exec.gasAvailable.toNat := hgas
            have hc :
                (sloadFrame frk key fr.exec.stack).exec.gasAvailable
                  = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg (f + 1) (.sload k)) :=
              materialiseGasCharge_sload defs sloadChg f k fr frk
                (sloadFrame frk key fr.exec.stack) hmrk.gasCharge
                (by rw [sloadFrame_gas, hwarm, subCharges_singleton])
            rw [hc]; exact toNat_chargeOf defs sloadChg (f + 1) (.sload k) _ hsum
      | tmp t =>
          -- recompute-on-use: descend into `defs t`.
          have hloc : st.locals t = some w := heval
          cases ht : defs t with
          | none =>
              -- An undefined-but-bound tmp is ruled out by the define-before-use
              -- scoping `hscoped`: a bound tmp is present in the recompute env.
              exact absurd (by rw [← hdefs, ht] : defsOf prog t = none)
                (hscoped t (by rw [hloc]; simp)).2
          | some e' =>
              have htmd : MatDec fr.exec.executionEnv.code defs sloadChg f fr.exec.pc e' := by
                rw [matDec_tmp_some fr.exec.executionEnv.code defs sloadChg f fr.exec.pc t e' ht]
                  at hdec
                exact hdec
              have hgas' : (chargeOf defs sloadChg f e').sum ≤ fr.exec.gasAvailable.toNat := by
                rw [chargeOf_tmp_some defs sloadChg f t e' ht] at hgas; exact hgas
              have hstk' : fr.exec.stack.size + (chargeOf defs sloadChg f e').length ≤ 1024 := by
                rw [chargeOf_tmp_some defs sloadChg f t e' ht] at hstk; exact hstk
              -- value: `evalExpr st obs (.tmp t) = st.locals t = some w`; DefsSound +
              -- obs-irrelevance give `evalExpr st obs e' = some w`.
              have hnr : ¬ NonRecomputable prog t := (hscoped t (by rw [hloc]; simp)).1
              have he'ng : e' ≠ .gas := by
                rintro rfl
                exact hnr (Or.inl (show isGasDef prog t by rw [isGasDef, ← hdefs, ht]))
              have hdfs : some w = V2.evalExpr st 0 e' :=
                hsound t e' w (by rw [← hdefs, ht]) hnr hloc
              have heval' : V2.evalExpr st obs e' = some w := by
                rw [evalExpr_obs_irrel st obs 0 he'ng]; exact hdfs.symm
              obtain ⟨fr', hmr⟩ := ih e' w fr htmd hsound hscoped hstore hsload hgasreal
                heval' hgas' hstk'
              refine ⟨fr', ?_⟩
              -- rewrite the `(f+1) (.tmp t)` bundle into the `f e'` one (defeq via defs t).
              have hmexp : materialiseExpr defs (f + 1) (.tmp t) = materialiseExpr defs f e' :=
                materialiseExpr_tmp_some defs f t e' ht
              have hchg : chargeOf defs sloadChg (f + 1) (.tmp t) = chargeOf defs sloadChg f e' :=
                chargeOf_tmp_some defs sloadChg f t e' ht
              exact
                { runs := hmr.runs
                  stack := hmr.stack
                  code := hmr.code
                  addr := hmr.addr
                  canMod := hmr.canMod
                  storage := hmr.storage
                  pc := by rw [hmexp]; exact hmr.pc
                  gasCharge := by
                    rw [MaterialiseGasCharge, hchg]; exact hmr.gasCharge
                  gasToNat := by rw [hchg]; exact hmr.gasToNat }
      | add a b =>
          -- operand values from `heval`.
          obtain ⟨va, hla, vb, hlb, hwadd⟩ :
              ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
                ∧ w = UInt256.add va vb := by
            simp only [V2.evalExpr] at heval
            cases hla : st.locals a with
            | none => simp [hla] at heval
            | some va =>
                cases hlb : st.locals b with
                | none => simp [hla, hlb] at heval
                | some vb =>
                    refine ⟨va, rfl, vb, rfl, ?_⟩
                    simp [hla, hlb] at heval; exact heval.symm
          subst hwadd
          -- decode bundle decomposition.
          obtain ⟨hdb, hda, hop⟩ := hdec
          have hcadd : chargeOf defs sloadChg (f + 1) (.add a b)
              = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a)
                ++ [Gverylow] := chargeOf_add defs sloadChg f a b
          -- evalExpr of each operand tmp.
          have hevb : V2.evalExpr st obs (.tmp b) = some vb := hlb
          have heva : V2.evalExpr st obs (.tmp a) = some va := hla
          -- IH on operand b from `fr`.
          have hgasb : (chargeOf defs sloadChg f (.tmp b)).sum ≤ fr.exec.gasAvailable.toNat := by
            rw [hcadd] at hgas
            simp only [List.sum_append] at hgas; omega
          have hstkb : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp b)).length ≤ 1024 := by
            rw [hcadd] at hstk
            simp only [List.length_append] at hstk; omega
          obtain ⟨frb, hmrb⟩ := ih (.tmp b) vb fr hdb hsound hscoped hstore hsload hgasreal
            hevb hgasb hstkb
          -- IH on operand a from `frb`.
          have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
          have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length :=
            hmrb.pc
          have hda' : MatDec frb.exec.executionEnv.code defs sloadChg f frb.exec.pc (.tmp a) := by
            rw [hbcode, hbpc]; exact hda
          -- the whole-`add` charge sum / length, split once.
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.add a b)).sum
              = (chargeOf defs sloadChg f (.tmp b)).sum
                + (chargeOf defs sloadChg f (.tmp a)).sum + Gverylow := by
            rw [hcadd]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.add a b)).length
              = (chargeOf defs sloadChg f (.tmp b)).length
                + (chargeOf defs sloadChg f (.tmp a)).length + 1 := by
            rw [hcadd]; simp only [List.length_append, List.length_singleton]
          have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
            rw [hmrb.stack]; simp [Stack.push]
          have hpb1 : 1 ≤ (chargeOf defs sloadChg f (.tmp b)).length :=
            chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp b) hdb
          have hgasa : (chargeOf defs sloadChg f (.tmp a)).sum ≤ frb.exec.gasAvailable.toNat := by
            rw [hmrb.gasToNat]; rw [hsum_split] at hgas; omega
          have hstka : frb.exec.stack.size + (chargeOf defs sloadChg f (.tmp a)).length ≤ 1024 := by
            rw [hlen_split] at hstk; rw [hfrbsz]; omega
          obtain ⟨fra, hmra⟩ := ih (.tmp a) va frb hda' hsound hscoped
            (hstore.transport hmrb.storage) (hsload.transport hmrb.addr) (hgasreal.transport hmrb.addr)
            heva hgasa hstka
          -- the final ADD step.
          have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
            rw [hmra.code, hbcode]
          have hapc : fra.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
                  + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length := by
            rw [hmra.pc, hbpc]
          have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
            rw [hmra.stack, hmrb.stack]; rfl
          have hadec : decode fra.exec.executionEnv.code fra.exec.pc
              = some (.ArithLogic .ADD, .none) := by
            rw [hacode, hapc]; exact hop
          have haszle : fra.exec.stack.size ≤ 1024 := by
            have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by
              rw [hastk]; simp
            have hpa1 : 1 ≤ (chargeOf defs sloadChg f (.tmp a)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f frb.exec.pc (.tmp a) hda'
            rw [hlen_split] at hstk; rw [hfrasz]; omega
          have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
            rw [hsum_split] at hgas; rw [hmra.gasToNat, hmrb.gasToNat]; omega
          obtain ⟨hadrun, hadstk⟩ := sim_add fra va vb fr.exec.stack hadec hastk haszle hagas
          refine ⟨addFrame fra va vb fr.exec.stack, ?_⟩
          refine
            { runs := (hmrb.runs.trans hmra.runs).trans hadrun
              stack := ?_
              code := ?_
              addr := ?_
              canMod := ?_
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_ }
          · rw [hadstk]
          · rw [addFrame_code, hacode]
          · rw [addFrame_addr, hmra.addr, hmrb.addr]
          · show (addFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState = _
            rw [show (addFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState
                  = fra.exec.executionEnv.canModifyState from rfl, hmra.canMod, hmrb.canMod]
          · intro k; rw [addFrame_selfStorage, hmra.storage, hmrb.storage]
          · rw [addFrame_pc, hapc, materialiseExpr_add]
            simp only [List.length_append, List.length_singleton]
            rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1) = 1 from rfl]
            ac_rfl
          · exact (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
              (addFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
              (charge_binOpPost_gas fra UInt256.add va vb fr.exec.stack)).1
          · -- gasToNat from the gas contract + toNat_chargeOf.
            have hsum : (chargeOf defs sloadChg (f + 1) (.add a b)).sum
                ≤ fr.exec.gasAvailable.toNat := hgas
            have hc :
                (addFrame fra va vb fr.exec.stack).exec.gasAvailable
                  = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg (f + 1) (.add a b)) :=
              (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
                (addFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
                (charge_binOpPost_gas fra UInt256.add va vb fr.exec.stack)).1
            rw [hc]; exact toNat_chargeOf defs sloadChg (f + 1) (.add a b) _ hsum
      | lt a b =>
          -- operand values from `heval`.
          obtain ⟨va, hla, vb, hlb, hwlt⟩ :
              ∃ va, st.locals a = some va ∧ ∃ vb, st.locals b = some vb
                ∧ w = UInt256.lt va vb := by
            simp only [V2.evalExpr] at heval
            cases hla : st.locals a with
            | none => simp [hla] at heval
            | some va =>
                cases hlb : st.locals b with
                | none => simp [hla, hlb] at heval
                | some vb =>
                    refine ⟨va, rfl, vb, rfl, ?_⟩
                    simp [hla, hlb] at heval; exact heval.symm
          subst hwlt
          -- decode bundle decomposition.
          obtain ⟨hdb, hda, hop⟩ := hdec
          have hclt : chargeOf defs sloadChg (f + 1) (.lt a b)
              = chargeOf defs sloadChg f (.tmp b) ++ chargeOf defs sloadChg f (.tmp a)
                ++ [Gverylow] := chargeOf_lt defs sloadChg f a b
          -- evalExpr of each operand tmp.
          have hevb : V2.evalExpr st obs (.tmp b) = some vb := hlb
          have heva : V2.evalExpr st obs (.tmp a) = some va := hla
          -- IH on operand b from `fr`.
          have hgasb : (chargeOf defs sloadChg f (.tmp b)).sum ≤ fr.exec.gasAvailable.toNat := by
            rw [hclt] at hgas
            simp only [List.sum_append] at hgas; omega
          have hstkb : fr.exec.stack.size + (chargeOf defs sloadChg f (.tmp b)).length ≤ 1024 := by
            rw [hclt] at hstk
            simp only [List.length_append] at hstk; omega
          obtain ⟨frb, hmrb⟩ := ih (.tmp b) vb fr hdb hsound hscoped hstore hsload hgasreal
            hevb hgasb hstkb
          -- IH on operand a from `frb`.
          have hbcode : frb.exec.executionEnv.code = fr.exec.executionEnv.code := hmrb.code
          have hbpc : frb.exec.pc = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length :=
            hmrb.pc
          have hda' : MatDec frb.exec.executionEnv.code defs sloadChg f frb.exec.pc (.tmp a) := by
            rw [hbcode, hbpc]; exact hda
          -- the whole-`lt` charge sum / length, split once.
          have hsum_split : (chargeOf defs sloadChg (f + 1) (.lt a b)).sum
              = (chargeOf defs sloadChg f (.tmp b)).sum
                + (chargeOf defs sloadChg f (.tmp a)).sum + Gverylow := by
            rw [hclt]; simp only [List.sum_append, List.sum_cons, List.sum_nil]; omega
          have hlen_split : (chargeOf defs sloadChg (f + 1) (.lt a b)).length
              = (chargeOf defs sloadChg f (.tmp b)).length
                + (chargeOf defs sloadChg f (.tmp a)).length + 1 := by
            rw [hclt]; simp only [List.length_append, List.length_singleton]
          have hfrbsz : frb.exec.stack.size = fr.exec.stack.size + 1 := by
            rw [hmrb.stack]; simp [Stack.push]
          have hpb1 : 1 ≤ (chargeOf defs sloadChg f (.tmp b)).length :=
            chargeOf_length_pos_of_matDec _ defs sloadChg f fr.exec.pc (.tmp b) hdb
          have hgasa : (chargeOf defs sloadChg f (.tmp a)).sum ≤ frb.exec.gasAvailable.toNat := by
            rw [hmrb.gasToNat]; rw [hsum_split] at hgas; omega
          have hstka : frb.exec.stack.size + (chargeOf defs sloadChg f (.tmp a)).length ≤ 1024 := by
            rw [hlen_split] at hstk; rw [hfrbsz]; omega
          obtain ⟨fra, hmra⟩ := ih (.tmp a) va frb hda' hsound hscoped
            (hstore.transport hmrb.storage) (hsload.transport hmrb.addr) (hgasreal.transport hmrb.addr)
            heva hgasa hstka
          -- the final LT step.
          have hacode : fra.exec.executionEnv.code = fr.exec.executionEnv.code := by
            rw [hmra.code, hbcode]
          have hapc : fra.exec.pc
              = fr.exec.pc + UInt32.ofNat (materialiseExpr defs f (.tmp b)).length
                  + UInt32.ofNat (materialiseExpr defs f (.tmp a)).length := by
            rw [hmra.pc, hbpc]
          have hastk : fra.exec.stack = va :: vb :: fr.exec.stack := by
            rw [hmra.stack, hmrb.stack]; rfl
          have hadec : decode fra.exec.executionEnv.code fra.exec.pc
              = some (.ArithLogic .LT, .none) := by
            rw [hacode, hapc]; exact hop
          have haszle : fra.exec.stack.size ≤ 1024 := by
            have hfrasz : fra.exec.stack.size = fr.exec.stack.size + 2 := by
              rw [hastk]; simp
            have hpa1 : 1 ≤ (chargeOf defs sloadChg f (.tmp a)).length :=
              chargeOf_length_pos_of_matDec _ defs sloadChg f frb.exec.pc (.tmp a) hda'
            rw [hlen_split] at hstk; rw [hfrasz]; omega
          have hagas : GasConstants.Gverylow ≤ fra.exec.gasAvailable.toNat := by
            rw [hsum_split] at hgas; rw [hmra.gasToNat, hmrb.gasToNat]; omega
          obtain ⟨hadrun, hadstk⟩ := sim_lt fra va vb fr.exec.stack hadec hastk haszle hagas
          refine ⟨ltFrame fra va vb fr.exec.stack, ?_⟩
          refine
            { runs := (hmrb.runs.trans hmra.runs).trans hadrun
              stack := ?_
              code := ?_
              addr := ?_
              canMod := ?_
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_ }
          · rw [hadstk]
          · rw [ltFrame_code, hacode]
          · rw [ltFrame_addr, hmra.addr, hmrb.addr]
          · show (ltFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState = _
            rw [show (ltFrame fra va vb fr.exec.stack).exec.executionEnv.canModifyState
                  = fra.exec.executionEnv.canModifyState from rfl, hmra.canMod, hmrb.canMod]
          · intro k; rw [ltFrame_selfStorage, hmra.storage, hmrb.storage]
          · rw [ltFrame_pc, hapc, materialiseExpr_lt]
            simp only [List.length_append, List.length_singleton]
            rw [UInt32.ofNat_add, UInt32.ofNat_add, show (UInt32.ofNat 1) = 1 from rfl]
            ac_rfl
          · exact (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
              (ltFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
              (charge_binOpPost_gas fra UInt256.lt va vb fr.exec.stack)).2
          · -- gasToNat from the gas contract + toNat_chargeOf.
            have hsum : (chargeOf defs sloadChg (f + 1) (.lt a b)).sum
                ≤ fr.exec.gasAvailable.toNat := hgas
            have hc :
                (ltFrame fra va vb fr.exec.stack).exec.gasAvailable
                  = subCharges fr.exec.gasAvailable (chargeOf defs sloadChg (f + 1) (.lt a b)) :=
              (materialiseGasCharge_binop defs sloadChg f a b fr frb fra
                (ltFrame fra va vb fr.exec.stack) hmrb.gasCharge hmra.gasCharge
                (charge_binOpPost_gas fra UInt256.lt va vb fr.exec.stack)).2
            rw [hc]; exact toNat_chargeOf defs sloadChg (f + 1) (.lt a b) _ hsum

end Lir

-- Build-enforced axiom-cleanliness guard for the B1 deliverable: the linchpin
-- `materialise_runs` (now total over `Expr`, `.sload`/`.gas` under their realisability
-- side-conditions) and its `.imm` leaf depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.materialise_runs
#print axioms Lir.matRuns_imm
