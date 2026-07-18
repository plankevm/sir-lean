import NestedEvmYul.XiTriple
import NestedEvmYul.XLoop

/-!
# T3 — end-to-end firing demo: `call_spec` fired twice against concrete `Ξ` children

**Foundation-grade, sorry-free.** This file is the nested analog of the flat
two-CALL acceptance test (`EVM/BytecodeLayer/Examples/TwoCallExample.lean`,
`twoCall_messageCall`/`twoCall_completedWith`): a concrete caller state performs
two successive external calls to a concrete `STOP`-code callee holding a
nonzero storage cell, `twoCall_spec` (XiTriple.lean) fires with **every side
condition discharged** — `hΘ` via `theta_of_xi` (with a genuinely-universal
`thetaTransfer` absorption proof), `hP` by `rfl` on the concrete maps, and
`hcall` as a **forward-evaluated** `call … = .ok (⟨1⟩, ·)` equation with the
post-state an explicit record — and the conclusion `Q₁ ∧ Q₂` yields the plain
storage punchline: the callee's cell still reads its value after both calls.

This closes the "one inversion away" item of the shape study: the study proved
the triple surface (`call_spec`/`twoCall_spec`) by *inversion* but never
*fired* it, leaving open whether the surface is non-vacuous end-to-end. It is.

## The technique: existential-free STOP-run producers

The T2 producers (`Xi_stop`, `Xi_stop_cofinal`) hide the run's final gas behind
an `∃ g'`, which blocks `rw`-based forward evaluation of `call`'s do-block (the
existential sits between the ambient universals and the fuel). T1's dispatcher
equations (`XLoop.step_eq_shared_stop` + `XLoop.shared_step_stop`, both with
fuel-free explicit RHS) dissolve that: the whole `Ξ → X → step` STOP chain has
an **explicit** final state (`stopState`) and gas (`stopGas`), so the Θ-level
forward lemma `Θ_stop_forward` below is a plain ∀-fuel *equation* — `rw` it
into `call`'s reduced body, and the remaining goal is closed concrete
computation (`rfl`). This upgrades T2's `Θ_doNothing` (empty map, `∃`-shaped)
to non-empty entry maps with zero existentials.

## Layer map

1. `Std.TransCmp` instance for the `AccountAddress` `compare` +
   `addrCompare_eq_iff` — unlocks Batteries' `RBMap.find?_insert` for the
   transfer-preamble absorption (the only genuinely-universal RBMap reasoning
   in the file; everything demo-concrete is `rfl`).
2. Demo data: `demoCallee` (address `0xff`, code `⟨#[0x00]⟩`, storage
   `⟨0⟩ ↦ ⟨42⟩`), `demoCaller` (default state over the singleton map).
3. `stopState`/`stopGas` + `X_stop_explicit`/`Xi_stop_explicit` — the
   existential-free STOP-run chain (via T1's `X_iter_halt`).
4. `Θ_stop_forward` — the ∀-fuel Θ-equation for a `STOP` callee resolved from
   a non-empty entry map (rollback arm killed by a concrete `beq`-false).
5. `thetaTransfer_find?` (`credit_stage`/`debit_stage`) — the callee's entry
   survives Θ's balance-transfer preamble for **arbitrary** `s`/`r`/`v` with
   only its balance rewritten: the `habsorb` obligation of `theta_of_xi`.
6. `demoTriple` — the concrete `ThetaTriple` via `theta_of_xi`, all three
   side conditions (`hΞ` from `preservesAccount_stop`, `habsorb` from 5,
   `hroll` by structure eta) discharged.
7. `demo_call₁`/`demo_call₂` — the firing equations: `call (f+5) … =
   .ok (⟨1⟩, demoAfter₁/₂)` for every fuel, post-states explicit records.
8. `demo_twoCall` — `twoCall_spec` fired with everything discharged;
   `demo_twoCall_storage` — the storage punchline, read out of `Q` alone (the
   pinned `find?`/`lookupStorage` match shape, per the study's §2.1 lesson).
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## 1. Order-theoretic plumbing for `AccountAddress` maps -/

/-- The `AccountAddress` `compare` (Wheels.lean: compare the `Fin` values as
naturals) is transitive-lawful: it is definitionally `compareOn (·.val)` and
`Nat` is a `TransOrd`. Unlocks Batteries' `RBMap.find?_insert` lemma family. -/
instance : Std.TransCmp (α := AccountAddress) compare :=
  inferInstanceAs (Std.TransCmp (compareOn (fun a : AccountAddress => a.val)))

/-- `compare` on `AccountAddress` decides equality (through `Nat.compare_eq_eq`
and `Fin` extensionality). -/
theorem addrCompare_eq_iff (a b : AccountAddress) : compare a b = .eq ↔ a = b := by
  show compare a.val b.val = .eq ↔ a = b
  rw [Nat.compare_eq_eq]
  exact ⟨Fin.eq_of_val_eq, Fin.val_eq_of_eq⟩

/-! ## 2. The demo world

Everything 0-valued and minimal: the difficulty of a firing demo is 100%
concrete evaluation, so we starve it — transferred value `0`, all four
`io`/`is`/`oo`/`os` memory operands `⟨0⟩`, depth `0`, a singleton account map.
The callee sits at address `0xff` (not a precompile) with single-`STOP` code
and one nonzero storage cell `⟨0⟩ ↦ ⟨42⟩` to make the postcondition
non-trivial. -/

/-- The callee's address, as the `UInt256` the caller pushes: `0xff`. -/
def demoT : UInt256 := ⟨0xff⟩

/-- The callee's `AccountAddress` (`0xff` — comfortably outside the precompile
range `π = {1..10}`). -/
def demoCallee : AccountAddress := AccountAddress.ofUInt256 demoT

/-- The callee's storage: the single cell `⟨0⟩ ↦ ⟨42⟩`. -/
def demoStorage : Storage := (Batteries.RBMap.empty : Storage).insert ⟨0⟩ ⟨42⟩

/-- The callee account: single-`STOP` code over `demoStorage`, default
(zero) nonce/balance. -/
def demoAcct : Account :=
  { (default : Account) with code := ⟨#[0x00]⟩, storage := demoStorage }

/-- The caller-visible account map: the singleton `demoCallee ↦ demoAcct`. -/
def demoMap₀ : AccountMap := (∅ : AccountMap).insert demoCallee demoAcct

/-- The concrete caller state: the default `EVM.State` (depth `0`, zero gas
economy, default `codeOwner = 0` absent from the map — so the value-`0` funds
check passes against the `⟨0⟩` fallback balance) over `demoMap₀`. -/
def demoCaller : EVM.State := { (default : EVM.State) with accountMap := demoMap₀ }

/-! ## 3. The existential-free STOP run (upgrading T2's producers) -/

/-- The explicit final state of a single-`STOP` `X`-run from `s`: the `Z`-gate
debit (`- 0`), the dispatcher debit (`- 0`, `execLength + 1`), and `STOP`'s
`setReturnData .empty`. Fuel-free — T1's dispatcher-equation dividend. -/
def stopState (s : EVM.State) : EVM.State :=
  let s₂ := XLoop.debit { s with gasAvailable := s.gasAvailable - UInt256.ofNat 0 } 0
  { s₂ with toMachineState := s₂.toMachineState.setReturnData ByteArray.empty }

/-- The explicit final gas of a single-`STOP` `Ξ`-run entered with gas `g`
(all STOP-path costs are zero; the two `- 0`s are the two debit sites). -/
def stopGas (g : UInt256) : UInt256 := g - UInt256.ofNat 0 - UInt256.ofNat 0

/-- `X` on single-`STOP` code, with the **explicit** witness `stopState s` —
`Refinement.X_stop` minus its existential. Assembled from T1's
`X_iter_halt` + `step_eq_shared_stop` + `shared_step_stop`. -/
theorem X_stop_explicit (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hcode : s.executionEnv.code = ⟨#[0x00]⟩) (hpc : s.pc = ⟨0⟩)
    (hstk : s.stack = []) :
    X (f+2) vj s = .ok (.success (stopState s) ByteArray.empty) := by
  have hdec : (decode s.executionEnv.code s.pc).getD (.STOP, .none) = (.STOP, .none) := by
    rw [hcode, hpc, decode_stop]
    rfl
  have hstep : EVM.step (f+1) 0 (some (.STOP, .none))
      { s with gasAvailable := s.gasAvailable - UInt256.ofNat 0 } = .ok (stopState s) := by
    rw [XLoop.step_eq_shared_stop f 0 .none, XLoop.shared_step_stop .none]
    rfl
  exact XLoop.X_iter_halt (f+1) vj s _ (stopState s) .STOP .none 0 ByteArray.empty
    hdec (Z_stop vj s hstk) hstep (H_stop _) (fun h => nomatch h)

/-- `Ξ` on single-`STOP` code, with the **explicit** gas `stopGas g` —
`Refinement.Xi_stop` minus its existential. The entry `cA`/`σ`/`A` return
verbatim (STOP touches only the machine state). -/
theorem Xi_stop_explicit (f : ℕ) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256)
    (A : Substate) (I : ExecutionEnv) (hcode : I.code = ⟨#[0x00]⟩) :
    Ξ (f+3) cA gh bl σ σ₀ g A I
      = .ok (.success (cA, σ, stopGas g, A) ByteArray.empty) := by
  rw [Ξ]
  simp only [bind, Except.bind]
  have hX := X_stop_explicit f (D_J I.code ⟨0⟩)
    { (default : EVM.State) with
        accountMap := σ
        σ₀ := σ₀
        substate := A
        executionEnv := I
        blocks := bl
        genesisBlockHeader := gh
        createdAccounts := cA
        gasAvailable := g } hcode rfl rfl
  simp only [] at hX
  rw [hX]
  rfl

/-! ## 4. The ∀-fuel Θ forward equation for a STOP callee on a non-empty map -/

/-- **The Θ forward equation** (the `Θ_doNothing` upgrade): a call to a
`STOP`-code callee resolved from a **non-empty** entry map runs to success at
every fuel `f + 4`, returning the post-transfer map verbatim. All run-ambient
arguments (`bvh cA gh blocks σ₀ A o g p v' d e Hd w`) are universal, so the
equation `rw`s directly into `call`'s reduced do-block with unification doing
the instantiation. The four hypotheses are `rfl` at every concrete use:

* `hfind` — the credited recipient exists (so the transfer takes the
  `some`-arm: an `insert` rewriting only the balance);
* `hexec` — the callee resolves to the single-`STOP` code;
* `hs` — the debited sender is absent from the post-credit map (the debit arm
  is a no-op); and
* `hne` — the post-transfer map is beq-nonempty, so Θ's `σ'' == ∅` rollback
  postprocessing (eqns 127/129) does **not** fire — the concrete beq-false
  fact the do-nothing study never needed. -/
theorem Θ_stop_forward
    (σ : AccountMap) (acct : Account) (s r : AccountAddress) (v : UInt256)
    (hfind : σ.find? r = some acct)
    (hexec : toExecute σ r = .Code ⟨#[0x00]⟩)
    (hs : (σ.insert r { acct with balance := acct.balance + v }).find? s = none)
    (hne : ((σ.insert r { acct with balance := acct.balance + v })
             == (∅ : AccountMap)) = false)
    (f : ℕ) (bvh : List ByteArray) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ₀ : AccountMap) (A : Substate)
    (o : AccountAddress) (g p v' : UInt256) (d : ByteArray) (e : ℕ)
    (Hd : BlockHeader) (w : Bool) :
    Θ (f+4) bvh cA gh blocks σ σ₀ A s o r (toExecute σ r) g p v v' d e Hd w
      = .ok (cA, σ.insert r { acct with balance := acct.balance + v },
             stopGas g, A, true, ByteArray.empty) := by
  have hΞ := Xi_stop_explicit f cA gh blocks
    (σ.insert r { acct with balance := acct.balance + v }) σ₀ g A
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
      (if ((σ.insert r { acct with balance := acct.balance + v })
            == (∅ : AccountMap)) = true
       then σ else σ.insert r { acct with balance := acct.balance + v }),
      stopGas g,
      (if ((σ.insert r { acct with balance := acct.balance + v })
            == (∅ : AccountMap)) = true
       then A else A),
      true, ByteArray.empty) = _
  -- … and kill them with the concrete beq-false fact.
  rw [hne]
  rfl

/-! ## 5. The transfer-preamble absorption (the genuinely-universal leg)

`theta_of_xi`'s `habsorb` quantifies over **all** senders/recipients/values
(that is `ThetaTriple`'s design: `P` sees only the map), so the demo cannot
discharge it by `rfl` — this is the one place real `RBMap` reasoning is owed:
Θ's balance transfer touches only balances, so the callee's entry survives
with (at most) its balance rewritten. -/

/-- Stage 1 (credit): after Θ's recipient-credit match, the account at `a`
still carries `acc₀`'s data, with some balance. -/
theorem credit_stage (σ : AccountMap) (r a : AccountAddress) (v : UInt256)
    (acc₀ : Account) (h : σ.find? a = some acc₀) :
    ∃ bal, (match σ.find? r with
            | none =>
              if v != ⟨0⟩ then σ.insert r { (default : Account) with balance := v }
              else σ
            | some acc => σ.insert r { acc with balance := acc.balance + v }).find? a
      = some { acc₀ with balance := bal } := by
  rcases hr : σ.find? r with _ | acc
  · simp only []
    by_cases hv : (v != ⟨0⟩) = true
    · rw [if_pos hv, Batteries.RBMap.find?_insert,
          if_neg (fun hEq => by
            rw [(addrCompare_eq_iff a r).mp hEq, hr] at h
            exact Option.noConfusion h)]
      exact ⟨acc₀.balance, h⟩
    · rw [if_neg hv]
      exact ⟨acc₀.balance, h⟩
  · simp only []
    rw [Batteries.RBMap.find?_insert]
    by_cases hEq : compare a r = .eq
    · rw [if_pos hEq]
      obtain rfl : a = r := (addrCompare_eq_iff a r).mp hEq
      obtain rfl : acc = acc₀ := Option.some.inj (hr.symm.trans h)
      exact ⟨acc.balance + v, rfl⟩
    · rw [if_neg hEq]
      exact ⟨acc₀.balance, h⟩

/-- Stage 2 (debit): after Θ's sender-debit match over any map `m` in which
`a` carries `acc₀`'s data, it still does. -/
theorem debit_stage (m : AccountMap) (s a : AccountAddress) (v : UInt256)
    (acc₀ : Account) (bal₁ : UInt256)
    (h1 : m.find? a = some { acc₀ with balance := bal₁ }) :
    ∃ bal, (match m.find? s with
            | none => m
            | some acc => m.insert s { acc with balance := acc.balance - v }).find? a
      = some { acc₀ with balance := bal } := by
  rcases hs' : m.find? s with _ | acc
  · simp only []
    exact ⟨bal₁, h1⟩
  · simp only []
    rw [Batteries.RBMap.find?_insert]
    by_cases hEq : compare a s = .eq
    · rw [if_pos hEq]
      obtain rfl : a = s := (addrCompare_eq_iff a s).mp hEq
      obtain rfl : acc = { acc₀ with balance := bal₁ } :=
        Option.some.inj (hs'.symm.trans h1)
      exact ⟨bal₁ - v, rfl⟩
    · rw [if_neg hEq]
      exact ⟨bal₁, h1⟩

/-- **The absorption fact**: `thetaTransfer` (Θ's balance-transfer preamble,
XiTriple.lean) preserves the account at `a` up to its balance, for arbitrary
sender `s`, recipient `r`, and value `v`. -/
theorem thetaTransfer_find? (σ : AccountMap) (s r a : AccountAddress)
    (v : UInt256) (acc₀ : Account) (h : σ.find? a = some acc₀) :
    ∃ bal, (thetaTransfer σ s r v).find? a = some { acc₀ with balance := bal } := by
  obtain ⟨bal₁, h1⟩ := credit_stage σ r a v acc₀ h
  simp only [thetaTransfer]
  exact debit_stage _ s a v acc₀ bal₁ h1

/-! ## 6. The concrete triple via `theta_of_xi` -/

/-- The demo invariant: the callee's map entry carries `demoAcct`'s data
(in particular its storage — the cell `⟨0⟩ ↦ ⟨42⟩`), with some balance. -/
def demoInv (σ : AccountMap) : Prop :=
  ∃ b, σ.find? demoCallee = some { demoAcct with balance := b }

/-- The precondition at call sites: the callee sits in the map exactly as
funded/coded in the demo world. (`rfl` at both concrete call sites.) -/
def demoP : AccountMap → Substate → Prop :=
  fun σ _ => σ.find? demoCallee = some demoAcct

/-- The postcondition `call_spec` lands on the caller: the callee's entry
(hence its storage cell) survives the call. -/
def demoQ : AccountMap → Substate → ByteArray → Prop :=
  fun σ' _ _ => demoInv σ'

/-- The `XiTriple` for the callee's code: a successful `Ξ`-run of single-`STOP`
code preserves the callee's map entry (`preservesAccount_stop`), so `demoInv`
transports from precondition to postcondition. -/
theorem demo_xiTriple (I : ExecutionEnv) (hcode : I.code = ⟨#[0x00]⟩) :
    XiTriple (fun σ _ => demoInv σ) I (fun σ' _ _ => demoInv σ') := by
  intro fuel cA gh blocks σ σ₀ g A r o hpre hrun
  obtain ⟨b, hb⟩ := hpre
  exact ⟨b, (preservesAccount_stop I demoCallee hcode
    fuel cA gh blocks σ σ₀ g A r o hrun).trans hb⟩

/-- **The concrete `ThetaTriple`**, all three `theta_of_xi` side conditions
discharged: `hΞ` from `demo_xiTriple`, `habsorb` from `thetaTransfer_find?`
(the balance-`∃` swallows the transfer), `hroll` from `demoP` directly
(structure eta: `demoAcct` *is* `{demoAcct with balance := demoAcct.balance}`). -/
theorem demoTriple : ThetaTriple demoP (.Code ⟨#[0x00]⟩) demoQ :=
  theta_of_xi demoP (fun σ _ => demoInv σ) demoQ ⟨#[0x00]⟩
    (fun I hcode => demo_xiTriple I hcode)
    (fun σ _A s r v hP => thetaTransfer_find? σ s r demoCallee v demoAcct hP)
    (fun _σ _A _σ'' _A'' _o hP _ _ => ⟨demoAcct.balance, hP⟩)

/-- `demoTriple`, retyped at the resolved-callee index `call_spec` wants for
the **first** call (`toExecute demoCaller.accountMap … ≡ .Code ⟨#[0x00]⟩` by
computation). -/
theorem demoTriple₀ :
    ThetaTriple demoP
      (toExecute demoCaller.accountMap (AccountAddress.ofUInt256 demoT)) demoQ :=
  demoTriple

/-! ## 7. The firing equations (forward evaluation of `call`) -/

/-- The callee account after one value-`0` credit: only the balance field is
rewritten (`+ ⟨0⟩`), the storage untouched. -/
def demoAcct₁ : Account := { demoAcct with balance := demoAcct.balance + ⟨0⟩ }

/-- The map after the first call: Θ's transfer preamble re-inserts the callee
with the credited balance; the STOP body changes nothing. -/
def demoMap₁ : AccountMap := demoMap₀.insert demoCallee demoAcct₁

/-- The substate after the first call: the callee charged as accessed. -/
def demoSub₁ : Substate := callAccessSubstate demoCaller demoT

/-- The machine state after the first call: gas-debit (`- 0`), the degenerate
zero-length `writeBytes`, return data `.empty`, gas re-credited with the
callee run's remainder (`stopGas` of the `Ccallgas` allowance), and the
(no-op) active-words accounting. Spelled exactly along `call`'s do-block. -/
def demoMachine₁ : MachineState :=
  let debited : MachineState :=
    { demoCaller.toMachineState with
        gasAvailable := demoCaller.toMachineState.gasAvailable - UInt256.ofNat 0 }
  let written : MachineState := writeBytes ByteArray.empty 0 debited 0 0
  { written with
      returnData := ByteArray.empty
      gasAvailable := written.gasAvailable
        + stopGas (UInt256.ofNat (Ccallgas demoCallee demoCallee ⟨0⟩ ⟨0⟩
            demoCaller.accountMap demoCaller.toMachineState demoCaller.substate))
      activeWords := UInt256.ofNat
        (MachineState.M (MachineState.M debited.activeWords.toNat 0 0) 0 0) }

/-- **The explicit post-state of the first call.** -/
def demoAfter₁ : EVM.State :=
  { demoCaller with
      accountMap := demoMap₁
      substate := demoSub₁
      toMachineState := demoMachine₁ }

/-- **Firing equation 1**: the first call succeeds (`x = ⟨1⟩`) at every fuel,
with the explicit post-state. Forward evaluation: reduce `call`'s do-block,
pass the funds/depth guard by `decide`, `rw` the Θ forward equation (its four
side facts are `rfl` on the singleton map), and the rest is closed computation. -/
theorem demo_call₁ (f : ℕ) :
    call (f+5) 0 [] ⟨0⟩ ⟨0⟩ demoT demoT ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ true demoCaller
      = .ok (⟨1⟩, demoAfter₁) := by
  simp only [call, bind, Except.bind]
  rw [if_pos (⟨by decide, by decide⟩ : _ ∧ _)]
  rw [Θ_stop_forward demoCaller.accountMap demoAcct (AccountAddress.ofUInt256 ⟨0⟩)
        (AccountAddress.ofUInt256 demoT) ⟨0⟩ rfl rfl rfl rfl]
  rfl

/-- `demoTriple`, retyped at the resolved-callee index for the **second** call
(the callee's code survives the first call: `demoAfter₁`'s map still resolves
it to `.Code ⟨#[0x00]⟩` by computation). -/
theorem demoTriple₁ :
    ThetaTriple demoP
      (toExecute demoAfter₁.accountMap (AccountAddress.ofUInt256 demoT)) demoQ :=
  demoTriple

/-- The callee account after the second value-`0` credit. -/
def demoAcct₂ : Account := { demoAcct₁ with balance := demoAcct₁.balance + ⟨0⟩ }

/-- The map after the second call. -/
def demoMap₂ : AccountMap := demoMap₁.insert demoCallee demoAcct₂

/-- The substate after the second call (the callee re-charged as accessed —
idempotent, but recorded as `call` computes it). -/
def demoSub₂ : Substate := callAccessSubstate demoAfter₁ demoT

/-- The machine state after the second call (same shape as `demoMachine₁`,
threaded from `demoAfter₁`'s machine state and warm-access gas allowance). -/
def demoMachine₂ : MachineState :=
  let debited : MachineState :=
    { demoAfter₁.toMachineState with
        gasAvailable := demoAfter₁.toMachineState.gasAvailable - UInt256.ofNat 0 }
  let written : MachineState := writeBytes ByteArray.empty 0 debited 0 0
  { written with
      returnData := ByteArray.empty
      gasAvailable := written.gasAvailable
        + stopGas (UInt256.ofNat (Ccallgas demoCallee demoCallee ⟨0⟩ ⟨0⟩
            demoAfter₁.accountMap demoAfter₁.toMachineState demoAfter₁.substate))
      activeWords := UInt256.ofNat
        (MachineState.M (MachineState.M debited.activeWords.toNat 0 0) 0 0) }

/-- **The explicit post-state of the second call.** -/
def demoAfter₂ : EVM.State :=
  { demoAfter₁ with
      accountMap := demoMap₂
      substate := demoSub₂
      toMachineState := demoMachine₂ }

/-- **Firing equation 2**: the caller immediately calls again from
`demoAfter₁` (legitimate: `twoCall_spec` leaves the middle state free), and
succeeds at every fuel. Same recipe; the four Θ side facts are now `rfl` **on
the post-transfer literal** `demoMap₁` — the second `toExecute`/`find?`
re-derivation the track spec flags at landmine (e). -/
theorem demo_call₂ (f : ℕ) :
    call (f+5) 0 [] ⟨0⟩ ⟨0⟩ demoT demoT ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ true demoAfter₁
      = .ok (⟨1⟩, demoAfter₂) := by
  simp only [call, bind, Except.bind]
  rw [if_pos (⟨by decide, by decide⟩ : _ ∧ _)]
  rw [Θ_stop_forward demoAfter₁.accountMap demoAcct₁ (AccountAddress.ofUInt256 ⟨0⟩)
        (AccountAddress.ofUInt256 demoT) ⟨0⟩ rfl rfl rfl rfl]
  rfl

/-! ## 8. The two-call composition, fired -/

/-- **The end-to-end firing demo** — the nested analog of the flat
`twoCall_completedWith` acceptance test, with **no hypotheses left**:
`twoCall_spec` applied at `ev₀ := demoCaller`, `ev₂ := demoAfter₁` (the caller
calls again immediately), with

* `hΘ₁`/`hΘ₂` the concrete `theta_of_xi`-built triples (`demoTriple₀/₁`),
* `hP₁`/`hP₂` `rfl` on the respective explicit maps, and
* `hcall₁`/`hcall₂` the forward-evaluated firing equations at fuel `5`,

concluding a real `Q₁ ∧ Q₂` about the two post-states. This is the data point
the shape study recorded as "never attempted": the T2/B3 triple surface is
non-vacuous end-to-end. -/
theorem demo_twoCall :
    demoQ demoAfter₁.accountMap demoAfter₁.substate
      demoAfter₁.toMachineState.returnData ∧
    demoQ demoAfter₂.accountMap demoAfter₂.substate
      demoAfter₂.toMachineState.returnData :=
  twoCall_spec
    (ev₀ := demoCaller) (ev₁ := demoAfter₁) (ev₂ := demoAfter₁) (ev₃ := demoAfter₂)
    demoTriple₀ demoTriple₁
    (rfl : demoP demoCaller.accountMap (callAccessSubstate demoCaller demoT))
    (demo_call₁ 0)
    (rfl : demoP demoAfter₁.accountMap (callAccessSubstate demoAfter₁ demoT))
    (demo_call₂ 0)

/-- **The punchline, in plain storage terms**: after both calls the callee's
cell `⟨0⟩` still reads `⟨42⟩` — read out of `demo_twoCall`'s `Q`-conjunction
alone (rewrite the `find?` fact `Q` delivers, then the storage read computes;
the balance-`∃` never matters because the update leaves the storage field
untouched). Phrased as the pinned `find?`/`lookupStorage` match expression
(the study's §2.1 lesson: reads as match shapes, so no RBMap lemma is owed). -/
theorem demo_twoCall_storage :
    (match demoAfter₁.accountMap.find? demoCallee with
     | some acc => acc.lookupStorage ⟨0⟩
     | none => ⟨0⟩) = (⟨42⟩ : UInt256) ∧
    (match demoAfter₂.accountMap.find? demoCallee with
     | some acc => acc.lookupStorage ⟨0⟩
     | none => ⟨0⟩) = (⟨42⟩ : UInt256) := by
  obtain ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩⟩ := demo_twoCall
  rw [hb₁, hb₂]
  exact ⟨rfl, rfl⟩

end NestedEvmYul
