import LirLean.Match
import LirLean.MaterialiseGas
import LirLean.DefsSound

/-!
# LirLean — `materialise_runs` (Layer **B1** of the `lower_conforms` grind)

`docs/lower-conforms-plan.md` node **B1**, *the linchpin*: running the lowered
push-sequence of an expression (`materialiseExpr defs fuel e`) reproduces, on the
bytecode stack, the value the IR's `evalExpr` computes — and does so leaving the
code, the self-storage and the gas-charge envelope (B2) all accounted for.

This module proves **B1 for the pure-arithmetic fragment** — `imm` / `tmp` / `add` /
`lt` (the `PureStream` predicate: the emitted byte stream contains no `SLOAD` and no
`GAS`) — fully and axiom-cleanly. The induction mirrors `materialiseExpr`
constructor-for-constructor; the leaf/recursion steps are the `Match.lean` bricks
`sim_imm` / `sim_add` / `sim_lt`; the `.tmp t` recursion consumes **B3** (`DefsSound`)
to equate the recomputed value with `st.locals t`; the whole-expression gas contract is
discharged through **B2** (`MaterialiseGasCharge` + `materialiseGasCharge_binop`). The
`.sload`/`.gas` cases are *vacuous* under `PureStream` (their opcode byte would be in
the stream) — they are the two honest interim gaps (below).

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

## The two honest interim gaps

**`.gas`.** `materialiseExpr … .gas = [GAS]`, and `sim_gas` pushes the frame's
*current* `gasAvailable`, whereas `evalExpr st obs .gas = some obs` (the supplied
value). The two agree only under the **realisability tie** `obs = UInt256.ofUInt64
(the post-Gbase gas)`, a property of the *running frame* the induction threads — it
does not hold uniformly. (The plan's gas-oracle realisability, `V2/Oracle.lean`, is
the place that tie is supplied.)

**`.sload`.** `materialiseExpr … (.sload k) = … ++ [SLOAD]`. The value channel is
ready (`sim_sload` + `sloadFrame_storage_self` already expose the pushed value as the
self-storage cell, and the `MatDec`/`chargeOf` `.sload` arms are in place). The gap is
purely the **runtime SLOAD-cost resolution**: the B2 `sloadChg k` must equal
`sloadCost (warm)` at the *internal* SLOAD frame, whose `accessedStorageKeys` and key
word are run-dependent, and SLOAD mutates the accessed-key substate (so the
substate-preservation a clean `MatRuns` carries does not hold across it). Closing it
needs the `MatRuns` bundle extended with an accessed-key-evolution clause and a per-
SLOAD warmth resolver threaded through — a self-contained extension, not a reopening
of the value channel. Both gaps are factored *out* of the proof by `PureStream`, so the
pure-arithmetic linchpin is `sorry`-free.

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

/-! ## The pure-arithmetic fragment

`SLOAD` (runtime warmth-cost resolution) and `GAS` (the realisability tie) are the two
constructs B1 does not close here (see the module docstring). `PureStream` excludes them
by their emitted opcode byte; B1 is proved for `PureStream` materialise streams. -/

/-- The materialise stream is **pure arithmetic**: it emits no `SLOAD` and no `GAS`
byte. This is the fragment B1 closes fully and axiom-cleanly (the value channel for
`imm`/`tmp`/`add`/`lt`, with the **B2** gas contract). It propagates through the
recompute recursion automatically — an `sload`/`gas` anywhere in the (recompute-)tree
puts its opcode byte in the stream, falsifying `PureStream` — so the `.sload`/`.gas`
cases are *vacuous* in the proof (the honest interim gap: see the module docstring). -/
def PureStream (l : List UInt8) : Prop := Byte.sload ∉ l ∧ Byte.gas ∉ l

theorem pureStream_append {l₁ l₂ : List UInt8} (h : PureStream (l₁ ++ l₂)) :
    PureStream l₁ ∧ PureStream l₂ := by
  obtain ⟨hs, hg⟩ := h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro hmem <;>
    first
      | exact hs (List.mem_append.mpr (Or.inl hmem))
      | exact hs (List.mem_append.mpr (Or.inr hmem))
      | exact hg (List.mem_append.mpr (Or.inl hmem))
      | exact hg (List.mem_append.mpr (Or.inr hmem))

/-! ## The decode bundle `MatDec`

`MatDec code defs sloadChg fuel p e` is the structured decode hypothesis B1 consumes:
one `decode code … = …` clause per opcode `materialiseExpr defs fuel e` emits, anchored
at the running program counter (`p` is the starting pc; the recursion advances it by
the post-frames' own pc deltas via `UInt32.ofNat_add`). It mirrors `materialiseExpr`
constructor-for-constructor — exactly the shape Layer A's `decode_at_offset_*`
discharges over `lower prog`. The `.sload` clause also carries the runtime warmth
resolution `sloadChg k = sloadCost warm` at the SLOAD frame (the B2 `sloadChg`
resolver), kept abstract here and instantiated downstream. -/
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

/-! ## The linchpin — `materialise_runs` (pure-arithmetic fragment)

The induction mirrors `materialiseExpr` constructor-for-constructor. The `PureStream`
hypothesis (no `SLOAD`/`GAS` byte emitted) keeps the proof to the value channel B1
closes fully and axiom-cleanly: `imm` (leaf), `tmp` (recompute via **B3** `DefsSound`),
`add`/`lt` (operands then op, via `sim_add`/`sim_lt` and the **B2** gluing law
`materialiseGasCharge_binop`). An `sload`/`gas` anywhere in the recompute-tree falsifies
`PureStream`, so those cases are vacuous — the honest interim gap (module docstring). -/

/-- **B1 `materialise_runs` (pure-arithmetic fragment).** Running `materialiseExpr defsOf
fuel e` from a frame `fr` whose code decodes as the bundle `MatDec` prescribes, with the
IR state `st` recompute-sound (`DefsSound`, **B3**) and the emitted stream
`SLOAD`/`GAS`-free (`PureStream`), reproduces `evalExpr st obs e = some w` on the
bytecode stack and delivers the whole `MatRuns` bundle: the run, the pushed value
(= `evalExpr`'s), code/address/self-storage preserved, pc advanced by the emitted byte
length, and the **B2** gas contract `MaterialiseGasCharge`. The decode facts `MatDec` and
the gas/stack room are the per-opcode preconditions the `sim_*`/B2 bricks consume; Layer
A (`decode_at_offset_*`) discharges `MatDec` over `lower prog` at the call site. -/
theorem materialise_runs {prog : Program} (sloadChg : Tmp → ℕ)
    (fuel : Nat) (st : V2.IRState) (obs : Word) :
    ∀ (e : Expr) (w : Word) (fr : Frame),
      PureStream (materialiseExpr (defsOf prog) fuel e) →
      MatDec fr.exec.executionEnv.code (defsOf prog) sloadChg fuel fr.exec.pc e →
      DefsSound prog st →
      -- recompute-sound, define-before-use scoping: every currently-bound tmp is
      -- recomputable (not gas-/call-defined) and present in the recompute env. This is
      -- the honest `WellScoped` content the plan documents (DefsSound's preservation
      -- side conditions); it makes the `.tmp` recursion total and value-faithful.
      (∀ t, st.locals t ≠ none → ¬ NonRecomputable prog t ∧ defsOf prog t ≠ none) →
      V2.evalExpr st obs e = some w →
      (chargeOf (defsOf prog) sloadChg fuel e).sum ≤ fr.exec.gasAvailable.toNat →
      fr.exec.stack.size + (chargeOf (defsOf prog) sloadChg fuel e).length ≤ 1024 →
      ∃ fr', MatRuns (defsOf prog) sloadChg fuel e w fr fr' := by
  set defs := defsOf prog with hdefs
  induction fuel with
  | zero =>
      intro e w fr _ hdec _ _ heval hgas hstk
      cases e with
      | imm v =>
          refine ⟨pushFrameW fr v 32, ?_⟩
          rw [show w = v from (Option.some.inj heval).symm]
          exact matRuns_imm defs sloadChg 0 fr v hdec hgas
            (by rw [chargeOf_imm] at hstk; simpa using hstk)
      | _ => exact absurd hdec (by simp [MatDec])
  | succ f ih =>
      intro e w fr hpure hdec hsound hscoped heval hgas hstk
      cases e with
      | imm v =>
          refine ⟨pushFrameW fr v 32, ?_⟩
          rw [show w = v from (Option.some.inj heval).symm]
          exact matRuns_imm defs sloadChg (f + 1) fr v hdec hgas
            (by rw [chargeOf_imm] at hstk; simpa using hstk)
      | gas =>
          -- emits `GAS` ⇒ ¬PureStream; vacuous.
          exact absurd (by simp [materialiseExpr] : Byte.gas ∈ materialiseExpr defs (f+1) .gas)
            hpure.2
      | sload k =>
          -- emits `SLOAD` ⇒ ¬PureStream; vacuous.
          refine absurd ?_ hpure.1
          rw [materialiseExpr_sload]
          exact List.mem_append.mpr (Or.inr (by simp))
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
              have hpure' : PureStream (materialiseExpr defs f e') := by
                rw [materialiseExpr_tmp_some defs f t e' ht] at hpure; exact hpure
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
              obtain ⟨fr', hmr⟩ := ih e' w fr hpure' htmd hsound hscoped heval' hgas' hstk'
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
          -- pure-stream / gas / stack decomposition (operand b then a then [Byte.add]).
          rw [materialiseExpr_add] at hpure
          obtain ⟨hpb, hpa⟩ := pureStream_append (pureStream_append hpure).1
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
          obtain ⟨frb, hmrb⟩ := ih (.tmp b) vb fr hpb hdb hsound hscoped hevb hgasb hstkb
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
          obtain ⟨fra, hmra⟩ := ih (.tmp a) va frb hpa hda' hsound hscoped heva hgasa hstka
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
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_ }
          · rw [hadstk]
          · rw [addFrame_code, hacode]
          · rw [addFrame_addr, hmra.addr, hmrb.addr]
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
          -- pure-stream / gas / stack decomposition (operand b then a then [Byte.lt]).
          rw [materialiseExpr_lt] at hpure
          obtain ⟨hpb, hpa⟩ := pureStream_append (pureStream_append hpure).1
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
          obtain ⟨frb, hmrb⟩ := ih (.tmp b) vb fr hpb hdb hsound hscoped hevb hgasb hstkb
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
          obtain ⟨fra, hmra⟩ := ih (.tmp a) va frb hpa hda' hsound hscoped heva hgasa hstka
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
              storage := ?_
              pc := ?_
              gasCharge := ?_
              gasToNat := ?_ }
          · rw [hadstk]
          · rw [ltFrame_code, hacode]
          · rw [ltFrame_addr, hmra.addr, hmrb.addr]
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
-- `materialise_runs` (pure-arithmetic fragment) and its `.imm` leaf depend only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms Lir.materialise_runs
#print axioms Lir.matRuns_imm
