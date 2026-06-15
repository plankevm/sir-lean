# Experiment 003 — results

Status: **package green, zero `sorry`, axiom-clean.** Both milestones are proven
in the export shape we wanted:

- **M1 (call-free spine)** — observables-only, frame-free, fuel-free message-call
  theorems on handwritten straight-line bytecode, up to a multi-instruction
  storage-effecting sequence.
- **M2 (external calls — the headline target)** — the `∃G₀` storage-observable
  theorem for a caller contract that forwards a **real, reflexive** `CALL` to a
  handwritten callee, plus the **executable `∃G₀` counterexample** (the 63/64 cap
  starves the callee, its `SSTORE` rolls back, the caller still completes) and a
  standalone **reflexivity witness** (the in-parent child computation *is* the
  genuine top-level child `messageCall`).

Every exported theorem's `#print axioms` is **exactly** `[propext,
Classical.choice, Quot.sound]`. The two foundation-level obstructions reported by
the previous run — the `bv_decide` axiom inherited by `messageCall`, and the
`private callArm`/`createArm` — were both resolved by **one upstream leanevm
commit** (`9cefe5b`, conformance unchanged at 2859/2859), which §3 records as the
key cross-cutting finding.

---

## 1. What is proven (verbatim, with `#print axioms`)

All theorems live under `namespace BytecodeLayer` and build green against the
real `forks/leanevm` (`import Evm`). Every one below prints **exactly**
`[propext, Classical.choice, Quot.sound]`.

### M1 — call-free spine

```lean
-- BytecodeLayer/Capstone1.lean
def stopProgram : ByteArray := ⟨#[0x00]⟩

theorem messageCall_stop_observe (p : CallParams) (hc : p.codeSource = .Code stopProgram) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty }

def pushStopProgram : ByteArray := ⟨#[0x60, 0x05, 0x00]⟩

theorem messageCall_pushStop_observe (p : CallParams)
    (hc : p.codeSource = .Code pushStopProgram) (hg : 3 ≤ p.gas.toNat) :
    (messageCall p).map CallResult.observe = .ok { success := true, output := .empty }

def sstoreProgram : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x07, 0x55, 0x00]⟩  -- PUSH1 5;PUSH1 7;SSTORE;STOP

theorem messageCall_sstore_storageAt (g : UInt64) (hg : 22106 ≤ g.toNat) :
    (messageCall (paramsSStore g)).map
      (fun r => (CallResult.observe r, CallResult.storageAt r addrA 7))
    = .ok ({ success := true, output := .empty }, 5)

-- BytecodeLayer/Capstone3.lean — a SEQUENCE of charging instructions
def seqProgram : ByteArray := ⟨#[0x60,0x05,0x60,0x07,0x55,0x60,0x0B,0x60,0x09,0x55,0x00]⟩

theorem messageCall_seq_storageAt (g : UInt64) (hg : 44212 ≤ g.toNat) :
    (messageCall (paramsSeq g)).map
      (fun r => (CallResult.observe r,
                 CallResult.storageAt r addrA 7, CallResult.storageAt r addrA 9))
    = .ok ({ success := true, output := .empty }, 5, 11)
```

All four are **frame-free** (no `Frame`, `injectFrame`, pc, stack), **fuel-free**
(`seedFuel`/`drive` fuel never appears), and stated **only** through
`CallResult.observe` / `CallResult.storageAt`. Their only quantitative content is
the program's exact intrinsic cost (`3`, `22106`, `44212` gas) as a plain
hypothesis — **no `∃G₀`**, because no 63/64-style nonlinearity arises off the
call path (vacuity-propagation suffices; see §2).

### M2 — external calls (the headline)

```lean
-- BytecodeLayer/CapstoneCall.lean
-- caller: PUSH1 0 ×5 ; PUSH3 0xCA11EE ; PUSH4 0xFFFFFFFF ; CALL ; STOP
-- callee (0xCA11EE): PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP

theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5

theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0

theorem messageCall_child_reflexive (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (messageCall (callChildParams (callerCalled g) 13242862 4294967295)).map
      (fun r => (r.success, CallResult.storageAt r addrCallee 7)) = .ok (true, 5)
```

- **`messageCall_call_storageAt`** is the goal: a top-level `messageCall` into a
  caller that forwards a `CALL` to a callee leaves the callee's storage cell
  `(addrCallee, 7)` holding `5`, for all `g ≥ G₀ (= 100000)`. The child call is
  the **genuine reflexive** `beginCall`/`drive` on the real child `CallParams`
  (`codeSource = toExecute accounts codeAddress`); the `SSTORE` that writes `5`
  runs inside that real sub-call, clears the 63/64 `callGasCap`, and commits. The
  statement is **observables-only, frame-free, fuel-free** at the messageCall
  boundary.

- **`call_counterexample`** is the executable witness that the `∃G₀` is *forced*,
  not cosmetic: at the modest `g = 24000` the very same observable is `0`
  (`childGas 24000 = 21045 < 22106`, so the callee's `SSTORE` out-of-gases under
  the cap and is rolled back), **while the top-level call still completes** (the
  caller is handed flag `0` and `STOP`s cleanly — no top-level `OutOfGas`). So no
  gas-floor-free statement ("completes ⇒ cell is 5") can hold; the existential is
  necessary. This is 001's executable `∃G₀` counterexample, **reached**.

- **`messageCall_child_reflexive`** makes the reflexivity explicit: the standalone
  `messageCall` on the exact `CallParams` the `CALL` produced succeeds and commits
  `7 = 5`, i.e. the in-parent child computation *is* the real child message call —
  no oracle, no assumption.

### Internal bricks (low-level by design — all also `[propext, Classical.choice, Quot.sound]`)

```lean
-- BytecodeLayer/Drive.lean      (top-level, empty pending stack)
theorem drive_step  (n) (current) (exec') (hstep : stepFrame current = .next exec') :
    drive (n+1) [] (.inl current) = drive n [] (.inl { current with exec := exec' })
theorem drive_halt  (n) (current) (halt) (hstep : stepFrame current = .halted halt) :
    drive (n+2) [] (.inl current) = .ok (endFrame current halt)
theorem two_le_seedFuel (g : UInt64) : 2 ≤ seedFuel g

-- BytecodeLayer/DriveGen.lean   (arbitrary suspended-ancestor stack ps — needed for calls)
theorem driveG_step           …  -- one non-halting step under any ps
theorem driveG_halt_callDeliver … -- a .call frame halts → deliver to suspended ancestor → resume
theorem driveG_needsCall_code  … -- .needsCall whose child is real Code → beginCall descends

-- BytecodeLayer/Step.lean       (vacuity-propagation made concrete)
theorem stepFrame_stop …  theorem stepFrame_push1 …  theorem stepFrame_push …
theorem stepFrame_sstore …  theorem stepFrame_sstore_oog …

-- BytecodeLayer/Call.lean       (the CALL rule, through the now-public callArm)
theorem stepFrame_call (fr) (gasv toAddr) (hdec : … = some (.System .CALL, .none))
    (hstk : fr.exec.stack = gasv :: toAddr :: 0 :: 0 :: 0 :: 0 :: 0 :: [])
    (hsz …) (hmod …) (hdepth : … < 1024) (hgas : callExtraCost … ≤ …) :
    stepFrame fr = .needsCall (callChildParams fr toAddr gasv) (callPending fr toAddr gasv)
```

---

## 2. Abstractions the proofs FORCED (validated-necessary)

- **`drive_step` / `drive_halt` / `two_le_seedFuel` (the top-level run
  vocabulary).** Forced the moment a proof had to advance `drive` past zero steps.
  They are `drive`'s own defining `match`, specialised to the empty pending-stack
  `[]` a top-level `messageCall` starts with. `drive_halt` needs **two** fuel
  units (halting step → deliver `.inr` through `[]`). This is leanevm's analogue
  of 001's "fuel discharged once": `two_le_seedFuel` + the `seedFuel g = (…-k)+k`
  peel let the seeded fuel satisfy the run, and fuel then never reappears in a
  statement.

- **`driveG_*` (the generalized run vocabulary) — forced *only* by M2.** Once a
  child call runs, the parent sits on the pending stack as a `Pending`, so the
  `[]`-specialised `Drive.lean` equations no longer apply. `DriveGen.lean`
  reproves the same `match` equations over an **arbitrary** `ps`, and adds the two
  call-specific arms: `driveG_needsCall_code` (descend into the reflexive child),
  `driveG_halt_callDeliver` (deliver the child result to the suspended ancestor
  and resume). This is exactly the leanevm analogue of the `needsCall`/`Pending`/
  `resume` cycle the README's brick **B′** predicted — and it was added only when
  the call capstone demanded it, not before.

- **`stepFrame_*` (vacuity-propagation made concrete).** Each opcode lemma
  discharges the guards (`InvalidInstruction`, `StackOverflow`, `OutOfGas`,
  `StaticModeViolation`, the `Gcallstipend` gate) as `if_neg`/`if_pos` from
  explicit hypotheses, exactly as proof-structure.md prescribes. The gas
  hypothesis *is* the vacuity premise. `stepFrame_sstore_oog` is the dual: the one
  step where gas is **deliberately insufficient**, used by the counterexample.

- **`stepFrame_call` + `callChildParams`/`callPending`/`callerCharged` (the CALL
  rule).** The reflexive heart. `callChildParams` builds the **real** child
  `CallParams` with `codeSource = toExecute accounts toAddr` — the genuine callee
  code, not an oracle. The proof unfolds the now-public `callArm`, discharges the
  mem-expansion (0), the `callGasCap + callExtraCost ≤ gasAvailable` charge guard,
  and the depth/balance guard; restricted to the value-free zero-memory CALL shape
  so the *only* quantitative content is the 63/64 cap — which is what the `∃G₀`
  turns on. `UInt256.zero_le` was forced to discharge the value-0 balance guard.

- **`childGas` / `childGas_lb` / `childGas_ub` / `subCharges` / `toNat_subCharges`
  (the localized 63/64 arithmetic).** This is the *only* genuine gas arithmetic in
  the experiment, and it lives **only at the call site**, exactly as
  proof-structure.md mandates. `childGas_lb` (≥ 22106 for `g ≥ 30000`) drives the
  success path; the negation (`childGas 24000 = 21045`) drives the counterexample.
  `toNat_subCharges` (gas threading by induction on the charge list) was forced by
  the multi-charge sequences (the 7-push caller, the two-SSTORE sequence) where
  nested `toNat_sub_ofNat` would explode quadratically — extracted exactly when a
  proof would have repeated the work.

- **`CallResult.observe` + `CallResult.storageAt` (the export surface).** Forced
  as the observable projections. `observe` gives `(success, output)` —
  world-map-independent. `storageAt` reads a single cell `(addr, key)` exactly as
  the EVM's `SLOAD` (`findD … 0`), off the returned `accounts` map — still at the
  messageCall boundary, no frame/pc/stack/fuel. It is the persistent observable
  the SSTORE and CALL rungs assert, and the cell whose value (`5` vs `0`) the
  `∃G₀` counterexample distinguishes.

### Abstractions that turned out UNNECESSARY

- **No shadow gas ledger, no metered copy of the semantics, no oracle, no
  record-commutation simp** — confirming proof-structure.md. Gas is carried by the
  single `charge`/`callGasCap` guards inside `stepFrame_*`; the call is the real
  `messageCall` on the child (reflexive), characterized by `beginCall_child` +
  `child_run`, never assumed.
- **No `injectFrame` analogue.** The messageCall boundary is frame-free exactly as
  the README predicted; nothing pins a final frame in any exported statement.
- **No `set`-abbreviation, no record-commutation lemmas** — the documented 001
  dead-ends were not needed; defeq + `dsimp only` + `if_neg`/`if_pos` sufficed.

---

## 3. The foundation fix that unblocked everything (KEY FINDING)

The previous run hit two orthogonal foundation-level walls and reported them as
findings (the correct move — a wall is a finding, not a `sorry`):

1. **`bv_decide` axiom.** `Evm.messageCall`/`drive`/`stepFrame`/`beginCall`/
   `endFrame` all inherited `Evm.UInt256.blt_iff_toBitVec_lt._native.bv_decide.ax_1_7`
   from `Evm/UInt256.lean`, because `blt_iff_toBitVec_lt` was proved by `bv_decide`
   and powered `UInt256`'s `Decidable (·<·)`/`(·≤·)`. This made literal axiom
   purity *structurally impossible* for any `messageCall` theorem.
2. **`private callArm`/`createArm`** in `Evm/Semantics/System.lean` left the CALL
   reduction inaccessible, blocking M2.

**Both were fixed by a single endorsed upstream leanevm commit** (`9cefe5b`,
"Remove bv_decide axiom from the execution path; expose callArm/createArm"):

- `blt_iff_toBitVec_lt` was **reproved without `bv_decide`** — reducing both sides
  to `Nat` (`BitVec.lt_def` + `toNat_limbs`) and discharging the 8-limb
  lexicographic equivalence with `omega` (limb `< 2^32` bounds in scope; the
  `2^(32·i)` weights are constants, so it stays linear). `blt`, `toBitVec`, and the
  `Decidable` instances are unchanged, so the fast limb-wise runtime path is
  preserved. `#print axioms Evm.messageCall` is now `[propext, Classical.choice,
  Quot.sound]`.
- `callArm`/`createArm` made non-`private`.
- **Fast conformance unchanged: 2859/2859 (~11s)** — no semantic regression.

This validates the previous run's central diagnosis exactly: the obstruction was
**definition-level in the foundation, not in the bytecode reasoning layer**, and
fixing it upstream made *all* of experiment 003 axiom-clean at a stroke — every
exported theorem now prints `[propext, Classical.choice, Quot.sound]` (verbatim in
§5). The remaining `bv_decide` uses in `Evm/UInt256.lean` are spec lemmas
unreachable from `messageCall`/`dispatch`, so the execution path is clean.

---

## 4. The `∃G₀` story, completed

001's headline — that external-call correctness *requires* an `∃G₀` gas floor
because the 63/64 cap can starve a callee whose failure the caller swallows — is
now stated and proved against the **real `messageCall`**, in observables:

- `messageCall_call_storageAt`: `∃ G₀, ∀ g ≥ G₀, cell (addrCallee,7) = 5`.
- `call_counterexample`: at `g = 24000 < G₀`, the same cell is `0`, *with the
  top-level call completing* — so the floor is not removable.
- `messageCall_child_reflexive`: the child sub-call is the genuine top-level child
  `messageCall` (no oracle), which is what makes the whole story honest.

The gap between success (`5`) and starvation (`0`) is exactly the 63/64
`callGasCap` (`allButOneSixtyFourth`) binding against the callee's `22106` cold
first-write `SSTORE` cost — the single localized arithmetic of §2, at the call
site, nowhere else.

---

## 5. Green / zero-sorry / axiom confirmation

- `lake build` inside `experiments/003_bytecode_layer`: **`Build completed
  successfully (1111 jobs).`** (Two `linter.unusedSimpArgs` warnings on
  `CapstoneCall.lean` lines 344/511 — cosmetic, not errors.)
- `grep -rEn "sorry|admit|native_decide|bv_decide" BytecodeLayer/`: **no
  occurrences.**
- `#print axioms` on every exported theorem, verbatim:

```
'BytecodeLayer.messageCall_stop_observe'   depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_pushStop_observe' depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_sstore_storageAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_seq_storageAt'  depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_call_storageAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.call_counterexample'        depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.messageCall_child_reflexive' depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.stepFrame_call'             depends on axioms: [propext, Classical.choice, Quot.sound]
'BytecodeLayer.drive_halt'                 depends on axioms: [propext, Classical.choice, Quot.sound]
```
