import NestedEvmYul.ObservableTriple
import NestedEvmYul.TwoCallDemo

/-!
# T2 — the endgame ACCEPTANCE TEST: `nested_twoCall_completedWith` driven
# through a fully concrete two-CALL caller world

**Foundation-grade, sorry-free.** This file is the acceptance test the parity
verdict (docs/planning/exp004-parity-verdict-2026-07-19.md §4, gap #3) said was
missing: the proved endgame `nested_twoCall_completedWith`
(ObservableTriple.lean) applied to a FULLY CONCRETE caller world, with **every
one of its ~20 segment hypotheses discharged** — no hypothesis-supplied
decomposition data left — ending in the hypothesis-free punchline

  `endgame_fired : completedWith (observe_nested (runΘ egWorld)) 0xff 0 42`.

This is *more* concrete than flat's `TwoCallExample` (which keeps `Runs`
hypotheses in `twoCall_completedWith`'s statement): here the entire two-CALL
execution — 14 `PUSH1` iterations, two cold/warm `CALL` firings through real
`Ξ`/`Θ` descents, and the halting `STOP` — is evaluated on concrete data.

## The concrete world

* Caller at `0xaa` (`egCallerAddr`), holding the 31-byte two-CALL bytecode
  `egCd`: twice `[PUSH1 os, PUSH1 oo, PUSH1 is, PUSH1 io, PUSH1 v(0),
  PUSH1 to(0xff), PUSH1 gas(0), CALL]` (push order matches `CALL`'s pop order:
  `μ₀ = gas` popped first ⇒ pushed last), then `STOP`.
  `CALL`s at pc `14`/`29`, `STOP` at pc `30`; `n₁ = n₂ = 7`, `k₁ = k₂ = 5`.
* Callee = TwoCallDemo's `0xff` account (`demoAcct`: single-`STOP` code,
  storage cell `⟨0⟩ ↦ ⟨42⟩`).
* `egWorld.σ` is the two-entry map; `r = 0xaa` (Θ's `.Code` arm runs `egCd`),
  `v = 0`, `e = 0`, real gas budget `g = 100000` (14 `PUSH1`s at 3 gas, one
  cold `CALL` at 2600, one warm `CALL` at 100 — ample margin).

## Deviations from the track spec (both forced, both local to this file)

* **Sender-present Θ forward lemma** (`Θ_stop_forward_present`): the track
  spec's "four side facts rfl on the concrete two-entry map" claim fails for
  TwoCallDemo's `Θ_stop_forward` — its `hs : (…).find? s = none` demands the
  debited sender be ABSENT from the map, but here the inner calls' sender is
  the caller `0xaa`, which IS in the map. The new variant takes the sender's
  entry (`hs : … = some acc₂`) and returns the double-insert post-transfer map.
  Same proof recipe as the original (one Θ-unfold, `Xi_stop_explicit`, `show`
  zeta-nudge, `hne` kills the rollback ifs).
* **Universal `hread` bridge** (`demoInv_observableRead`): the endgame's
  `hread` quantifies over ALL post-maps satisfying `Q₂` (= `demoQ`, the
  balance-∃ `find?` fact), so it is NOT a concrete-map evaluation — it needs
  real RBMap→`toList` reasoning: `Batteries.RBMap.find?_some_mem_toList`
  (membership), `mem_toList_unique` (key uniqueness through the `TransCmp`
  instance TwoCallDemo provides), and a small `List.find?`-of-unique-witness
  induction (`find?_eq_of_unique`). This is the one genuinely universal lemma
  the observable lens costs.

NO `maxHeartbeats` cranks were needed: every `rfl`/`decide` obligation — the
14 chain links, both `Z`-CALL gates, both call firings (which whnf-evaluate
the full concrete `pushSucc`/`thetaTransfer` chains), and the endgame
assembly — closes at default heartbeats.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## 1. The concrete world -/

/-- The caller's two-CALL bytecode (31 bytes): twice
`PUSH1 0 (osz); PUSH1 0 (oo); PUSH1 0 (isz); PUSH1 0 (io); PUSH1 0 (v);
PUSH1 0xff (to); PUSH1 0 (gas); CALL`, then `STOP`.
`CALL`s at pc `14` and `29`, `STOP` at pc `30`. -/
def egCd : ByteArray := ⟨#[
  0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0xff,
  0x60, 0x00, 0xf1,
  0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0xff,
  0x60, 0x00, 0xf1,
  0x00]⟩

/-- The caller's address `0xaa` — distinct from the callee's `0xff`. -/
def egCallerAddr : AccountAddress := AccountAddress.ofUInt256 ⟨0xaa⟩

/-- The top-level transaction sender `0xbb` — absent from the map, so Θ's
top-level debit stage is a no-op. -/
def egSender : AccountAddress := AccountAddress.ofUInt256 ⟨0xbb⟩

/-- The caller's account: holds the two-CALL bytecode, zero balance. -/
def egCallerAcct : Account := { (default : Account) with code := egCd }

/-- The two-entry world map: callee (`demoAcct` at `0xff`) + caller. -/
def egMap : AccountMap :=
  ((∅ : AccountMap).insert demoCallee demoAcct).insert egCallerAddr egCallerAcct

/-- **The concrete world.** `r = 0xaa` executing `.Code egCd`, value `0`,
depth `0`, gas `100000`. -/
def egWorld : NestedWorld :=
  { blobVersionedHashes := []
    createdAccounts := ∅
    genesisBlockHeader := default
    blocks := default
    σ := egMap
    σ₀ := egMap
    A := default
    s := egSender
    o := egSender
    r := egCallerAddr
    c := .Code egCd
    g := ⟨100000⟩
    p := ⟨0⟩
    v := ⟨0⟩
    v' := ⟨0⟩
    d := ByteArray.empty
    e := 0
    H := default
    w := true }

/-! ## 2. The sender-present Θ forward equation

`TwoCallDemo.Θ_stop_forward` requires the debited sender to be ABSENT from the
post-credit map (`hs : … = none`). Here the inner calls' sender is the caller
`0xaa`, present in the map, so the debit arm fires: the post-transfer map is a
DOUBLE insert (credit the callee, debit the sender). Same statement shape and
proof recipe otherwise; all run-ambient arguments universal so the equation
`rw`s into `call`'s reduced do-block. -/

/-- **Θ forward equation, sender-present variant**: a call to a `STOP`-code
callee resolved from the entry map, whose debited sender `s` is also present
(entry `acc₂` in the post-credit map), runs to success at every fuel `f + 4`,
returning the double-insert post-transfer map verbatim. All four side facts
are `rfl` at the concrete call sites below. -/
theorem Θ_stop_forward_present
    (σ : AccountMap) (acct acc₂ : Account) (s r : AccountAddress) (v : UInt256)
    (hfind : σ.find? r = some acct)
    (hexec : toExecute σ r = .Code ⟨#[0x00]⟩)
    (hs : (σ.insert r { acct with balance := acct.balance + v }).find? s = some acc₂)
    (hne : (((σ.insert r { acct with balance := acct.balance + v }).insert s
              { acc₂ with balance := acc₂.balance - v }) == (∅ : AccountMap)) = false)
    (f : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ₀ : AccountMap) (A : Substate)
    (o : AccountAddress) (g p v' : UInt256) (d : ByteArray) (e : ℕ)
    (Hd : BlockHeader) (w : Bool) :
    Θ (f+4) bvh cA gh blocks σ σ₀ A s o r (toExecute σ r) g p v v' d e Hd w
      = .ok (cA, (σ.insert r { acct with balance := acct.balance + v }).insert s
               { acc₂ with balance := acc₂.balance - v },
             stopGas g, A, true, ByteArray.empty) := by
  have hΞ := Xi_stop_explicit f cA gh blocks
    ((σ.insert r { acct with balance := acct.balance + v }).insert s
      { acc₂ with balance := acc₂.balance - v }) σ₀ g A
    { codeOwner := r
      sender := o
      source := s
      weiValue := v'
      calldata := d
      code := ⟨#[0x00]⟩
      gasPrice := p.toNat
      header := Hd
      depth := e
      perm := w
      blobVersionedHashes := bvh } rfl
  simp only [Θ, bind, Except.bind, hfind, hexec, hs]
  rw [hΞ]
  -- Iota-reduce the Ξ-result match by `show`ing the (defeq) post-match form,
  -- exposing the two `σ'' == ∅` rollback ifs …
  show Except.ok (cA,
      (if (((σ.insert r { acct with balance := acct.balance + v }).insert s
             { acc₂ with balance := acc₂.balance - v }) == (∅ : AccountMap)) = true
       then σ
       else (σ.insert r { acct with balance := acct.balance + v }).insert s
              { acc₂ with balance := acc₂.balance - v }),
      stopGas g,
      (if (((σ.insert r { acct with balance := acct.balance + v }).insert s
             { acc₂ with balance := acc₂.balance - v }) == (∅ : AccountMap)) = true
       then A else A),
      true, ByteArray.empty) = _
  -- … and kill them with the concrete beq-false fact.
  rw [hne]
  rfl

/-! ## 3. The straight-line states

Every intermediate state is a def whose body is EXACTLY the successor shape
`IterStepU.push1` produces (so chain links elaborate by structural defeq):
`Z`'s memory debit (`- 0`), the dispatcher `debit` at the `PUSH1` gate cost,
then `replaceStackAndIncrPC` with `pcΔ = 2`. -/

/-- One `PUSH1` successor: the exact `IterStepU.push1` successor shape at
memory cost `0` and gate cost `3` (`Gverylow`). -/
def egPush (s : EVM.State) (v : UInt256) : EVM.State :=
  (XLoop.debit { s with gasAvailable := s.gasAvailable - UInt256.ofNat 0 } 3).replaceStackAndIncrPC
    ((XLoop.debit { s with gasAvailable := s.gasAvailable - UInt256.ofNat 0 } 3).stack.push v) 2

/-- Θ's entry state for the caller world (`callerEntry`, ObservableTriple). -/
def egS₀ : EVM.State := callerEntry egWorld egCd

def egS₁ : EVM.State := egPush egS₀ ⟨0⟩       -- PUSH1 0  (osz)
def egS₂ : EVM.State := egPush egS₁ ⟨0⟩       -- PUSH1 0  (oo)
def egS₃ : EVM.State := egPush egS₂ ⟨0⟩       -- PUSH1 0  (isz)
def egS₄ : EVM.State := egPush egS₃ ⟨0⟩       -- PUSH1 0  (io)
def egS₅ : EVM.State := egPush egS₄ ⟨0⟩       -- PUSH1 0  (v)
def egS₆ : EVM.State := egPush egS₅ ⟨0xff⟩    -- PUSH1 ff (to)
/-- The first call site (pc `14`, 7-deep stack). -/
def egSC₁ : EVM.State := egPush egS₆ ⟨0⟩      -- PUSH1 0  (gas)

/-- Post-`Z` state at call site 1 (`Z`'s memory debit is `- 0`). -/
def egSZ₁ : EVM.State :=
  { egSC₁ with gasAvailable := egSC₁.gasAvailable - UInt256.ofNat 0 }

/-- The `Z` gate cost of the first `CALL` (cold-account access), kept in
expression form — the kernel evaluates it (to `2600`) wherever needed. -/
def egCost₁ : ℕ := C' egSZ₁ .CALL

/-- The first call's child-gas allowance (`Ccallgas` on the pre-debit state;
with gas operand `⟨0⟩` it evaluates to `0`). -/
def egCallgas₁ : ℕ :=
  Ccallgas demoCallee demoCallee ⟨0⟩ ⟨0⟩ (XLoop.bump egSZ₁).accountMap
    (XLoop.bump egSZ₁).toMachineState (XLoop.bump egSZ₁).substate

/-- The callee after the first value-`0` credit. -/
def egAcctF₁ : Account := { demoAcct with balance := demoAcct.balance + ⟨0⟩ }

/-- The caller after the TOP-LEVEL transfer credit (Θ's preamble on `egWorld`;
value `0`). -/
def egCallerAcct₁ : Account :=
  { egCallerAcct with balance := egCallerAcct.balance + ⟨0⟩ }

/-- The caller after the first inner call's sender debit (`- 0`). -/
def egCallerAcct₂ : Account :=
  { egCallerAcct₁ with balance := egCallerAcct₁.balance - ⟨0⟩ }

/-- The map after the first call: credit the callee, debit the sender
(both value `0` — the double insert `Θ_stop_forward_present` returns). -/
def egMapR₁ : AccountMap :=
  ((XLoop.bump egSZ₁).accountMap.insert demoCallee egAcctF₁).insert
    egCallerAddr egCallerAcct₂

/-- The substate after the first call: the callee charged as accessed. -/
def egSubR₁ : Substate := callAccessSubstate egSZ₁ demoT

/-- The machine state after the first call, spelled along `call`'s do-block:
gate-cost debit, degenerate zero-length `writeBytes`, empty return data, gas
re-credited with the callee run's remainder, no-op active-words accounting. -/
def egMachineR₁ : MachineState :=
  let debited : MachineState :=
    { (XLoop.bump egSZ₁).toMachineState with
        gasAvailable := (XLoop.bump egSZ₁).toMachineState.gasAvailable - UInt256.ofNat egCost₁ }
  let written : MachineState := writeBytes ByteArray.empty 0 debited 0 0
  { written with
      returnData := ByteArray.empty
      gasAvailable := written.gasAvailable + stopGas (UInt256.ofNat egCallgas₁)
      activeWords := UInt256.ofNat
        (MachineState.M (MachineState.M debited.activeWords.toNat 0 0) 0 0) }

/-- **The explicit post-state of the first call** (the endgame's `evR₁`). -/
def egEvR₁ : EVM.State :=
  { XLoop.bump egSZ₁ with
      accountMap := egMapR₁
      substate := egSubR₁
      toMachineState := egMachineR₁ }

/-- Resumption after call 1: push the success flag, `pc := 15`. -/
def egSM₀ : EVM.State := egEvR₁.replaceStackAndIncrPC (Stack.push ([] : Stack UInt256) ⟨1⟩)

def egSM₁ : EVM.State := egPush egSM₀ ⟨0⟩
def egSM₂ : EVM.State := egPush egSM₁ ⟨0⟩
def egSM₃ : EVM.State := egPush egSM₂ ⟨0⟩
def egSM₄ : EVM.State := egPush egSM₃ ⟨0⟩
def egSM₅ : EVM.State := egPush egSM₄ ⟨0⟩
def egSM₆ : EVM.State := egPush egSM₅ ⟨0xff⟩
/-- The second call site (pc `29`, 8-deep stack). -/
def egSC₂ : EVM.State := egPush egSM₆ ⟨0⟩

/-- Post-`Z` state at call site 2. -/
def egSZ₂ : EVM.State :=
  { egSC₂ with gasAvailable := egSC₂.gasAvailable - UInt256.ofNat 0 }

/-- The `Z` gate cost of the second `CALL` (warm access: the callee entered the
accessed set during call 1 — evaluates to `100`). -/
def egCost₂ : ℕ := C' egSZ₂ .CALL

/-- The second call's child-gas allowance. -/
def egCallgas₂ : ℕ :=
  Ccallgas demoCallee demoCallee ⟨0⟩ ⟨0⟩ (XLoop.bump egSZ₂).accountMap
    (XLoop.bump egSZ₂).toMachineState (XLoop.bump egSZ₂).substate

/-- The callee after the second credit. -/
def egAcctF₂ : Account := { egAcctF₁ with balance := egAcctF₁.balance + ⟨0⟩ }

/-- The caller after the second debit. -/
def egCallerAcct₃ : Account :=
  { egCallerAcct₂ with balance := egCallerAcct₂.balance - ⟨0⟩ }

/-- The map after the second call. -/
def egMapR₂ : AccountMap :=
  ((XLoop.bump egSZ₂).accountMap.insert demoCallee egAcctF₂).insert
    egCallerAddr egCallerAcct₃

/-- The substate after the second call (idempotent re-charge). -/
def egSubR₂ : Substate := callAccessSubstate egSZ₂ demoT

/-- The machine state after the second call. -/
def egMachineR₂ : MachineState :=
  let debited : MachineState :=
    { (XLoop.bump egSZ₂).toMachineState with
        gasAvailable := (XLoop.bump egSZ₂).toMachineState.gasAvailable - UInt256.ofNat egCost₂ }
  let written : MachineState := writeBytes ByteArray.empty 0 debited 0 0
  { written with
      returnData := ByteArray.empty
      gasAvailable := written.gasAvailable + stopGas (UInt256.ofNat egCallgas₂)
      activeWords := UInt256.ofNat
        (MachineState.M (MachineState.M debited.activeWords.toNat 0 0) 0 0) }

/-- **The explicit post-state of the second call** (the endgame's `evR₂`). -/
def egEvR₂ : EVM.State :=
  { XLoop.bump egSZ₂ with
      accountMap := egMapR₂
      substate := egSubR₂
      toMachineState := egMachineR₂ }

/-- Resumption after call 2: `pc := 30` (the `STOP`). -/
def egSH₀ : EVM.State :=
  egEvR₂.replaceStackAndIncrPC (Stack.push ((⟨1⟩ :: []) : Stack UInt256) ⟨1⟩)

/-- Post-`Z` state at the halting `STOP`. -/
def egSZH : EVM.State :=
  { egSH₀ with gasAvailable := egSH₀.gasAvailable - UInt256.ofNat 0 }

/-! ## 4. The prefix and middle chains (7 `IterStepU.push1` links each) -/

/-- Prefix chain: Θ's entry state to the first call site, 7 `PUSH1`s. -/
theorem egChain₁ (vj : Array UInt256) : XLoop.ItersN vj 7 egS₀ egSC₁ := by
  have h₁ : XLoop.IterStepU vj egS₀ egS₁ := XLoop.IterStepU.push1 rfl rfl
  have h₂ : XLoop.IterStepU vj egS₁ egS₂ := XLoop.IterStepU.push1 rfl rfl
  have h₃ : XLoop.IterStepU vj egS₂ egS₃ := XLoop.IterStepU.push1 rfl rfl
  have h₄ : XLoop.IterStepU vj egS₃ egS₄ := XLoop.IterStepU.push1 rfl rfl
  have h₅ : XLoop.IterStepU vj egS₄ egS₅ := XLoop.IterStepU.push1 rfl rfl
  have h₆ : XLoop.IterStepU vj egS₅ egS₆ := XLoop.IterStepU.push1 rfl rfl
  have h₇ : XLoop.IterStepU vj egS₆ egSC₁ := XLoop.IterStepU.push1 rfl rfl
  exact (((((((XLoop.ItersN.refl egS₀).tail h₁).tail h₂).tail h₃).tail
    h₄).tail h₅).tail h₆).tail h₇

/-- Middle chain: call 1's derived successor to the second call site. -/
theorem egChain₂ (vj : Array UInt256) : XLoop.ItersN vj 7 egSM₀ egSC₂ := by
  have h₁ : XLoop.IterStepU vj egSM₀ egSM₁ := XLoop.IterStepU.push1 rfl rfl
  have h₂ : XLoop.IterStepU vj egSM₁ egSM₂ := XLoop.IterStepU.push1 rfl rfl
  have h₃ : XLoop.IterStepU vj egSM₂ egSM₃ := XLoop.IterStepU.push1 rfl rfl
  have h₄ : XLoop.IterStepU vj egSM₃ egSM₄ := XLoop.IterStepU.push1 rfl rfl
  have h₅ : XLoop.IterStepU vj egSM₄ egSM₅ := XLoop.IterStepU.push1 rfl rfl
  have h₆ : XLoop.IterStepU vj egSM₅ egSM₆ := XLoop.IterStepU.push1 rfl rfl
  have h₇ : XLoop.IterStepU vj egSM₆ egSC₂ := XLoop.IterStepU.push1 rfl rfl
  exact (((((((XLoop.ItersN.refl egSM₀).tail h₁).tail h₂).tail h₃).tail
    h₄).tail h₅).tail h₆).tail h₇

/-! ## 5. Call site 1: decode / gate / stack / firing -/

/-- Decode at pc `14`: `CALL`. -/
theorem egDec₁ :
    (decode egSC₁.executionEnv.code egSC₁.pc).getD (.STOP, .none) = (.CALL, .none) := rfl

/-- `Z` passes at the first `CALL` (cold-access cost). -/
theorem egZ₁ (vj : Array UInt256) : Z vj .CALL egSC₁ = .ok (egSZ₁, egCost₁) := rfl

/-- The 7-deep post-`Z` stack at site 1. -/
theorem egStk₁ :
    egSZ₁.stack = ⟨0⟩ :: demoT :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ([] : Stack UInt256) := rfl

/-- **Firing equation 1**: the first `CALL` succeeds at every fuel `f + 5`,
with the explicit post-state. Recipe of `TwoCallDemo.demo_call₁`: reduce
`call`'s do-block, pass the funds/depth guard by `decide`, `rw` the
sender-present Θ forward equation (four side facts `rfl` on the concrete
two-entry map), close by concrete computation. -/
theorem egCall₁ (f : ℕ) :
    call (f + 5) egCost₁ egSZ₁.executionEnv.blobVersionedHashes ⟨0⟩
      (.ofNat egSZ₁.executionEnv.codeOwner) demoT demoT ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩
      egSZ₁.executionEnv.perm (XLoop.bump egSZ₁)
      = .ok (⟨1⟩, egEvR₁) := by
  simp only [call, bind, Except.bind]
  rw [if_pos (⟨by decide, by decide⟩ : _ ∧ _)]
  rw [Θ_stop_forward_present (XLoop.bump egSZ₁).accountMap demoAcct egCallerAcct₁
        (AccountAddress.ofUInt256 (.ofNat egSZ₁.executionEnv.codeOwner))
        (AccountAddress.ofUInt256 demoT) ⟨0⟩ rfl rfl rfl rfl]
  rfl

/-- `demoTriple`, retyped at site 1's resolved-callee index (`toExecute` on the
post-top-transfer two-entry map computes to `.Code ⟨#[0x00]⟩`). -/
theorem egTriple₁ :
    ThetaTriple demoP
      (toExecute egSZ₁.accountMap (AccountAddress.ofUInt256 demoT)) demoQ :=
  demoTriple

/-- `demoP` at site 1: the top-level transfer (`v = 0`, caller `≠ 0xff`)
leaves the callee's entry intact. -/
theorem egP₁ : demoP egSZ₁.accountMap (callAccessSubstate egSZ₁ demoT) := rfl

/-! ## 6. Call site 2, same shape (warm access) -/

/-- Decode at pc `29`: `CALL`. -/
theorem egDec₂ :
    (decode egSC₂.executionEnv.code egSC₂.pc).getD (.STOP, .none) = (.CALL, .none) := rfl

/-- `Z` passes at the second `CALL` (warm-access cost). -/
theorem egZ₂ (vj : Array UInt256) : Z vj .CALL egSC₂ = .ok (egSZ₂, egCost₂) := rfl

/-- The post-`Z` stack at site 2: 7 operands over the residual `⟨1⟩`. -/
theorem egStk₂ :
    egSZ₂.stack = ⟨0⟩ :: demoT :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ((⟨1⟩ :: []) : Stack UInt256) := rfl

/-- **Firing equation 2**: the second `CALL` succeeds at every fuel `f + 5`. -/
theorem egCall₂ (f : ℕ) :
    call (f + 5) egCost₂ egSZ₂.executionEnv.blobVersionedHashes ⟨0⟩
      (.ofNat egSZ₂.executionEnv.codeOwner) demoT demoT ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩
      egSZ₂.executionEnv.perm (XLoop.bump egSZ₂)
      = .ok (⟨1⟩, egEvR₂) := by
  simp only [call, bind, Except.bind]
  rw [if_pos (⟨by decide, by decide⟩ : _ ∧ _)]
  rw [Θ_stop_forward_present (XLoop.bump egSZ₂).accountMap egAcctF₁ egCallerAcct₂
        (AccountAddress.ofUInt256 (.ofNat egSZ₂.executionEnv.codeOwner))
        (AccountAddress.ofUInt256 demoT) ⟨0⟩ rfl rfl rfl rfl]
  rfl

/-- `demoTriple` at site 2's resolved-callee index (the callee's code survived
call 1: only its balance field was rewritten, by `+ ⟨0⟩`). -/
theorem egTriple₂ :
    ThetaTriple demoP
      (toExecute egSZ₂.accountMap (AccountAddress.ofUInt256 demoT)) demoQ :=
  demoTriple

/-- `demoP` at site 2: the callee's entry after call 1 is `demoAcct` again
(the `+ ⟨0⟩` credit is definitionally absorbed). -/
theorem egP₂ : demoP egSZ₂.accountMap (callAccessSubstate egSZ₂ demoT) := rfl

/-! ## 7. The halting suffix -/

/-- Decode at pc `30` (call 2's successor): `STOP`. -/
theorem egDecH :
    (decode (egEvR₂.replaceStackAndIncrPC (Stack.push ((⟨1⟩ :: []) : Stack UInt256) ⟨1⟩)).executionEnv.code
        (egEvR₂.replaceStackAndIncrPC (Stack.push ((⟨1⟩ :: []) : Stack UInt256) ⟨1⟩)).pc).getD (.STOP, .none)
      = (.STOP, .none) := rfl

/-- `Z` passes at the halting `STOP` (all costs zero). -/
theorem egZH (vj : Array UInt256) :
    Z vj .STOP (egEvR₂.replaceStackAndIncrPC (Stack.push ((⟨1⟩ :: []) : Stack UInt256) ⟨1⟩))
      = .ok (egSZH, C' egSZH .STOP) := rfl

/-- Θ's degenerate empty-map rollback does not fire: the final map is
beq-nonempty. -/
theorem egNe : (egEvR₂.accountMap == (∅ : AccountMap)) = false := rfl

/-! ## 8. The universal `hread` bridge (the observable lens)

The endgame derives the storage read from `Q₂ = demoQ` — a balance-∃ `find?`
fact about an ARBITRARY post-map — so the bridge to the observable's
`toList.find?` lens is genuinely universal RBMap reasoning, not concrete
evaluation: membership + key-uniqueness (through the `TransCmp` instance) pin
the `toList.find?` witness, and the storage read then computes. -/

/-- `List.find?` returns a member that satisfies the predicate uniquely. -/
theorem find?_eq_of_unique {α : Type _} {p : α → Bool} {l : List α} {a : α}
    (ha : a ∈ l) (hpa : p a = true)
    (huniq : ∀ b ∈ l, p b = true → b = a) : l.find? p = some a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    by_cases hx : p x = true
    · rw [List.find?_cons_of_pos hx, huniq x List.mem_cons_self hx]
    · rw [List.find?_cons_of_neg hx]
      rcases List.mem_cons.mp ha with rfl | h
      · exact absurd hpa hx
      · exact ih h (fun b hb hpb => huniq b (List.mem_cons_of_mem x hb) hpb)

/-- **The observable-lens bridge**: any map satisfying `demoInv` (the callee's
entry carries `demoAcct`'s data with SOME balance) reads `42` through the
observable's `toList.find?`/`lookupStorage` lens at `(0xff, 0)`. -/
theorem demoInv_observableRead (σ'' : AccountMap) (h : demoInv σ'') :
    (match σ''.toList.find? (fun p => p.1.val = (0xff : ℕ)) with
     | some p => (p.2.lookupStorage (UInt256.ofNat 0)).toNat
     | none => 0) = 42 := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨y, hyMem, hyCmp⟩ := Batteries.RBMap.find?_some_mem_toList hb
  have hy : y = demoCallee := ((addrCompare_eq_iff demoCallee y).mp hyCmp).symm
  subst hy
  have hfind : σ''.toList.find? (fun p => p.1.val = (0xff : ℕ))
      = some (demoCallee, { demoAcct with balance := b }) := by
    refine find?_eq_of_unique hyMem (by rfl) (fun q hq hpq => ?_)
    refine Batteries.RBMap.mem_toList_unique hq hyMem ?_
    rw [addrCompare_eq_iff]
    exact Fin.eq_of_val_eq (by rw [of_decide_eq_true hpq]; rfl)
  rw [hfind]
  rfl

/-! ## 9. Fuel envelope and the punchline -/

/-- The decomposition fits comfortably under the seeding envelope:
`30 ≤ seedFuel egWorld = 1025·(100000 + 8) + 3`. -/
theorem egFuel : 7 + 7 + 5 + 5 + 6 ≤ seedFuel egWorld := by
  have h : seedFuel egWorld = 102508203 := rfl
  omega

/-- **The endgame, fired**: `nested_twoCall_completedWith` with every segment
hypothesis discharged on the concrete world — both conjuncts of its
conclusion. -/
theorem egEndgame :
    demoQ egEvR₁.accountMap egEvR₁.substate egEvR₁.toMachineState.returnData ∧
    completedWith (observe_nested (runΘ egWorld)) 0xff 0 42 :=
  nested_twoCall_completedWith egWorld egCd (D_J egCd ⟨0⟩) rfl rfl 0xff 0 42
    egFuel
    (egChain₁ _)
    egDec₁ (egZ₁ _) egStk₁ egCall₁ egTriple₁ egP₁
    (egChain₂ _)
    egDec₂ (egZ₂ _) egStk₂ egCall₂ egTriple₂ egP₂
    egDecH (egZH _) egNe
    (fun σ'' _ _ hq => demoInv_observableRead σ'' hq)

/-- **THE PUNCHLINE — the acceptance test the parity verdict said was
missing**: with NO hypotheses at all, the caller world's fuel-free seeded run
completes successfully and the callee's storage cell `0` still reads `42` at
the shared-observable altitude. Segment data is no longer
hypothesis-supplied; this is more concrete than flat's `TwoCallExample`
(which keeps `Runs` hypotheses in its `twoCall_completedWith`). -/
theorem endgame_fired : completedWith (observe_nested (runΘ egWorld)) 0xff 0 42 :=
  egEndgame.2

/-- The `Q₁`-conjunct sibling: the first callee's postcondition (`demoInv` —
the callee's entry survives) holds at call 1's explicit post-state. -/
theorem endgame_Q₁ :
    demoQ egEvR₁.accountMap egEvR₁.substate egEvR₁.toMachineState.returnData :=
  egEndgame.1

end NestedEvmYul
