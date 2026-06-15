# Experiment 003 — results

Status: **package green, zero `sorry`.** Milestone **M1 (call-free spine) is
proven** in the export shape we wanted. Milestone **M2 (external calls) is
blocked**, with two precise, independent obstructions reported below — both
foundation-level, neither hidden by a `sorry`.

The single most important finding is the **axiom obstruction**: it is
*structurally impossible* for any theorem about the real `messageCall` to satisfy
the literal axiom-purity gate, because the leanevm foundation's own definitions
already depend on a `bv_decide` axiom. This is detailed in §3 and is the key
result of the experiment.

---

## 1. What is proven (verbatim, with `#print axioms`)

All theorems live under `namespace BytecodeLayer` and build green against the
real `forks/leanevm` (`import Evm`).

### Capstone 1 — single `STOP`, observables only

```lean
def stopProgram : ByteArray := ⟨#[0x00]⟩

theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty }
```

`#print axioms messageCall_stop_observe`:
```
[propext, Classical.choice, Quot.sound,
 Evm.UInt256.blt_iff_toBitVec_lt._native.bv_decide.ax_1_7]
```

### Capstone 1′ — `PUSH1 0x05 ; STOP`, observables only, with the gas floor

```lean
def pushStopProgram : ByteArray := ⟨#[0x60, 0x05, 0x00]⟩

theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty }
```

`#print axioms messageCall_pushStop_observe`: identical 4-axiom list.

Both statements are **frame-free** (no `Frame`, `injectFrame`, pc, stack),
**fuel-free** (`seedFuel`/`drive` fuel never appears), and **observables-only**
(through `CallResult.observe`). `messageCall_pushStop_observe`'s only quantitative
content is `3 ≤ p.gas` — the program's exact intrinsic cost — stated as a plain
hypothesis, *not* an `∃G₀`, because no 63/64-style nonlinearity arises off the
call path.

### Internal bricks (low-level by design, all axiom-clean modulo §3)

```lean
-- BytecodeLayer/Drive.lean
theorem drive_step (n : ℕ) (current : Frame) (exec' : ExecutionState)
    (hstep : stepFrame current = .next exec') :
    drive (n + 1) [] (.inl current) = drive n [] (.inl { current with exec := exec' })

theorem drive_halt (n : ℕ) (current : Frame) (halt : FrameHalt)
    (hstep : stepFrame current = .halted halt) :
    drive (n + 2) [] (.inl current) = .ok (endFrame current halt)

theorem two_le_seedFuel (g : UInt64) : 2 ≤ seedFuel g

-- BytecodeLayer/Step.lean
theorem stepFrame_stop (fr : Frame)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.System .STOP, .none))
    (hstk : fr.exec.stack.size ≤ 1024) :
    stepFrame fr = .halted (.success fr.exec .empty)

theorem stepFrame_push1 (fr : Frame) (imm : UInt256)
    (hdec : decode fr.exec.executionEnv.code fr.exec.pc = some (.Push .PUSH1, some (imm, 1)))
    (hgas : 3 ≤ fr.exec.gasAvailable.toNat) (hstk : fr.exec.stack.size + 1 ≤ 1024) :
    stepFrame fr = .next ((…gas-charged exec…).replaceStackAndIncrPC (fr.exec.stack.push imm) (pcΔ := 2))
```

Every brick's `#print axioms` is the same 4-axiom list (the three standard
axioms plus the §3 foundation axiom).

---

## 2. Abstractions the proofs FORCED (validated-necessary)

- **`drive_step` / `drive_halt` (the run vocabulary).** Forced the moment a
  proof had to advance `drive` past more than zero steps. They are exactly
  `drive`'s own defining `match`, specialised to the empty pending-stack `[]`
  that a top-level `messageCall` starts with. `drive_halt` needs **two** fuel
  units (take the halting step → deliver the `.inr` result through `[]`);
  `drive_step` needs one. This is leanevm's analogue of 001's
  "fuel discharged once": `two_le_seedFuel` + the `seedFuel g = (…-2)+2` peel
  let the fuel `messageCall` actually seeds satisfy `drive_halt`, and fuel then
  never appears again.

- **`stepFrame_*` (vacuity-propagation made concrete).** Each opcode lemma
  discharges the three guards (`InvalidInstruction`, `StackOverflow`, `OutOfGas`)
  as `if_neg`s from explicit hypotheses, exactly as proof-structure.md prescribes
  ("at each check it either passes or the whole run is OutOfGas"). The gas
  hypothesis (`3 ≤ …` for PUSH1, none for STOP) *is* the vacuity premise.

- **`decode_*` equation lemmas (by `rfl`).** Validated 001's "standalone
  equation lemmas, list-first byte encodings": `decode <bytes> <pc>` reduces by
  `rfl`, but only as a *named* lemma — inlined, `simp` cannot find the pattern
  under `getD`. The `(0 : UInt32) + UInt8.toUInt32 2` form of the second decode
  point in capstone-1′ is forced because that is literally the pc `incrPC`
  produces; stating it reduced (`= 2`) breaks the `rw`.

- **`CallResult.observe` + `Observables`.** Forced as the export surface. We
  project `(success, output)` — the two observables that are world-map
  independent. The account map / substate are *also* observables but for these
  clean-completion programs they are returned verbatim from the snapshot;
  exposing them would drag the whole `AccountMap` into the statement without
  adding force. (`success`/`output` is precisely the pair 001's `∃G₀`
  counterexample turns on — the caller's stored flag and its clean halt.)

### Abstractions that turned out UNNECESSARY (so far)

- **No shadow gas ledger, no metered copy of the semantics, no oracle, no
  record-commutation simp** — confirming proof-structure.md. Gas is carried by
  the single `charge` guard inside `stepFrame_*`.
- **No `injectFrame` analogue.** The messageCall boundary is frame-free exactly
  as the README predicted; nothing pins a final frame.
- **No `set`-abbreviation, no record-commutation lemmas** — the documented 001
  dead-ends were not needed; defeq + `dsimp only` + `if_neg` sufficed.

---

## 3. The axiom obstruction (KEY FINDING)

**Every theorem that so much as mentions `messageCall` is forced to depend on a
non-standard axiom, inherited from leanevm.** The literal requirement
(`#print axioms` shows ONLY `propext`, `Classical.choice`, `Quot.sound`) is
therefore **unsatisfiable for this experiment by construction** — not because of
anything the experiment's proofs do.

Root cause, traced precisely:

```
#print axioms Evm.drive       -- [propext, Classical.choice, Quot.sound,
#print axioms Evm.messageCall  --  Evm.UInt256.blt_iff_toBitVec_lt._native.bv_decide.ax_1_7]
#print axioms Evm.beginCall
#print axioms Evm.stepFrame
#print axioms Evm.endFrame
#print axioms Evm.seedFuel     -- does NOT depend on any axioms (pure ℕ)
```

The axiom is `Evm.UInt256.blt_iff_toBitVec_lt._native.bv_decide.ax_1_7`. Its
origin is `forks/leanevm/Evm/UInt256.lean:459`:

```lean
theorem blt_iff_toBitVec_lt (a b : UInt256) : blt a b = true ↔ a.toBitVec < b.toBitVec := by
  …
  bv_decide   -- ← SAT-backed; emits the _native.bv_decide axiom
```

This lemma is used at lines 478–483 to build the **`Decidable (a < b)` and
`Decidable (a ≤ b)` instances for `UInt256`**, which are then used pervasively
across the semantics (`value ≤ balance`, `depth < 1024`, gas comparisons, …).
The taint thus propagates into `stepFrame`, `beginCall`, `drive`, `endFrame`,
and `messageCall`. Decisive evidence that it is definition-level, not
proof-level: even

```lean
theorem d0 (st) : drive 0 [] st = .error .OutOfFuel := by unfold drive; rfl
```

— a pure `match` with zero `UInt256` content — already carries the axiom, while
`seedFuel` (pure `ℕ`) does not. The experiment's own proofs introduce **no**
further axioms: the 4-axiom list of every capstone equals the 4-axiom list of
`Evm.messageCall` itself.

**Honest disposition.** This is a *genuine mathematical theorem* about
`UInt256`, proved by a sound but axiom-introducing tactic in the foundation — it
is not a `sorry`, not a gap, and not introduced here. Reverting the green
proofs over it would destroy real results to no benefit (the next theorem would
hit the same axiom). The proofs are kept; the obstruction is reported.

**The fix (out of scope, the proper resolution).** Reprove
`blt_iff_toBitVec_lt` (and the few sibling `bv_decide` lemmas in
`Evm/UInt256.lean`) without `bv_decide` — e.g. via a generic
`BitVec`-append/`ult` lexicographic-decomposition lemma proved through `toNat`
and `omega`. A bounded attempt confirmed the goal shape is a clean 7-fold fold
of one append-`ult` lemma, but the `Nat.lor`↔`+` bridge for the limb
composition is itself a non-trivial sub-proof; finishing it is a foundation
(UInt256) task, not a bytecode-reasoning-layer task, and was time-boxed out to
keep the package green. Doing it upstream would make **the entire experiment**
axiom-clean at a stroke.

---

## 4. The M2 (external-call) obstruction

Independent of §3, reducing a real `CALL` is blocked at the foundation API:

- **`callArm` and `createArm` are `private`** in
  `forks/leanevm/Evm/Semantics/System.lean` (lines 12, 73). After reducing
  `stepFrame` on `CALL` through `dispatch`/`systemOp` and `Stack.pop7`, the goal
  contains `Evm.callArm✝` — an inaccessible name. It cannot be `unfold`ed or
  `simp`ed by name from the experiment package, so the `.needsCall` descent
  (the reflexive child `messageCall`, the 63/64 `callGasCap`, the flag-0
  resume) cannot be characterised.

  *Unblock:* make `callArm`/`createArm` non-`private` (or add public equation
  lemmas) upstream in leanevm — an endorsed fork change per the README. This was
  not done because (a) §3 independently blocks axiom purity regardless, so M2
  could not have been delivered axiom-clean either, and (b) the privacy change
  needs to be designed and conformance-checked upstream, outside this run's
  green-always budget.

- The `∃G₀` counterexample (cap binds → callee OOG → flag 0 stored → caller
  STOPs cleanly) was **not reached**, because it lives strictly behind the
  `callArm` reduction above.

So M2's headline — external calls — is **not proven**. The two obstructions are
orthogonal: even with `callArm` exposed, §3 would remain; even with §3 fixed,
`callArm`'s privacy would remain.

---

## 5. Green / zero-sorry confirmation

- `lake build` inside `experiments/003_bytecode_layer`: **`Build completed
  successfully (1107 jobs).`**
- `grep -rn "sorry\|admit\|native_decide\|bv_decide" BytecodeLayer/`: only a
  comment hit; **no occurrences in code.**
- Axiom state of every new theorem: the three standard axioms **plus** the
  single foundation-inherited `…bv_decide.ax_1_7` (§3).
