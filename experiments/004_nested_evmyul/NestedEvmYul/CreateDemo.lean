import NestedEvmYul.LambdaTriple
import NestedEvmYul.TwoCallDemo

/-!
# T3 — CREATE firing demo: `lambda_of_xi`/`create_spec` fired against a concrete child

**Foundation-grade, placeholder-free.** This file is the CREATE-side mirror of
`TwoCallDemo.lean` (the CALL firing demo): a concrete `LambdaTriple` instance is
built via `lambda_of_xi` with **all three side conditions discharged** against a
concrete child — init code `⟨#[0x00]⟩` (single `STOP`), whose successful init
run returns `.empty`, so the deposited code is `.empty` — and then fired at a
concrete parent CREATE site through `create_spec`. This kills the "non-vacuity
by proof structure only" reviewer nit on `LambdaTriple`: the triple surface is
inhabited by a genuine instance over the demo world, not merely closed under
its logical rules.

## The world

The parent map holds the creator (`0xaa`, a default account) and the `0xff`
beacon `demoCallee ↦ demoAcct` from `TwoCallDemo` (single-`STOP` code, storage
`⟨0⟩ ↦ ⟨42⟩`), the observer whose survival makes the postcondition non-trivial.
The created address is **keccak-derived and therefore opaque** throughout
(`ffi.KEC` is `@[extern] opaque`, `EVMYulLean/EvmYul/FFI/ffi.lean:27`); every
statement carries it as a parameter `a` and conditions the beacon claim on
`a ≠ demoCallee`.

## Layer map

1. **Collision-arm closure** (`Z_invalid` → `X_invalid` → `Xi_invalid` →
   `xiTriple_invalid`): `Ξ` on the EIP-7610 swap code `⟨#[0xfe]⟩` **never**
   succeeds at any fuel — decode `0xfe = some .INVALID` (Instr.lean:585),
   `δ .INVALID = none` (Instr.lean:309), so the gate `Z` errors
   `.InvalidInstruction` (Semantics.lean:454) — hence `XiTriple P ⟨#[0xfe]⟩ Q`
   holds for ANY `P`,`Q` by run inversion. This closes `lambda_of_xi`'s
   disjunctive `hΞ` branch honestly, grounded in the semantics (not by
   hand-waving the collision away).
2. `Xi_stop_out_empty` — the missing output pin for `STOP` runs (mirror of
   `preservesAccount_stop`), so the deposited code is provably `.empty`.
3. `lambdaInit_find?` / `lambdaInit_beacon` — the `habsorb` obligation:
   `Λ`'s nonce-bump/endowment preamble at the opaque created address `a`
   preserves the beacon's entry (`thetaTransfer_find?` analog; the substate
   charge `A.addAccessedAccount a` is sidestepped by picking the predicates
   substate-insensitive).
4. `demoCreateTriple` — the concrete `LambdaTriple` via `lambda_of_xi`, all
   three side conditions (`hΞ`, `habsorb`, `hdeposit`) discharged.
5. `demo_create` — `create_spec` fired at a concrete parent state, with ONLY
   `hstep`/`hx` left hypothetical (see the docstring there for why that is the
   designed maximum, not a shortfall), plus the storage punchline.

## Honest precision note (the `a`-blind `Ξ`-interface)

`lambda_of_xi`'s client predicates `Pξ`/`Qξ` are `AccountMap → Substate →
(ByteArray →) Prop` — they do **not** see the created address `a` (`habsorb`
and `hdeposit` quantify over ALL `a`). When `a = demoCallee`, `lambdaInit`
bumps the beacon's own nonce, so the invariant that survives the interface is
`∃ n b` (nonce AND balance rewritten, code/storage intact) — `lambdaInit_find?`
DOES prove the sharper balance-only fact under `a ≠ demoCallee` at the preamble
level, but that conditional cannot ride through the `a`-blind `Ξ` triple, so
`createQ`'s beacon leg is the `∃ n b` form under `a ≠ demoCallee`. The storage
punchline (cell `⟨0⟩` still reads `⟨42⟩`) is unaffected.
-/

namespace NestedEvmYul
open EvmYul EvmYul.EVM

/-! ## 1. Collision-arm closure: `Ξ` on `⟨#[0xfe]⟩` never succeeds

The EIP-7610 arm of `Λ` swaps the init code for `⟨#[0xfe]⟩` when the (keccak-
opaque) target address is occupied. `lambda_of_xi`'s `hΞ` therefore covers
`I.code = i ∨ I.code = ⟨#[0xfe]⟩`. The second disjunct is closed here for free:
the invalid-opcode run can never reach the `.success` arm the triple consumes. -/

/-- `INVALID` has no memory expansion: its `μᵢ'` is the entry `activeWords`
(the `_` catch-all arm). Mirror of `Refinement.memexp_stop`. -/
theorem memexp_invalid (s : EVM.State) :
    memoryExpansionCost s Operation.INVALID = 0 := by
  unfold memoryExpansionCost
  show Cₘ s.activeWords - Cₘ s.activeWords = 0
  exact Nat.sub_self _

/-- `INVALID`'s instruction gas is `0` (it falls through every `W*` class to
the catch-all). Mirror of `Refinement.cprime_stop`. -/
theorem cprime_invalid (s : EVM.State) : C' s Operation.INVALID = 0 := rfl

/-- `decode` of the single-`INVALID` code at `pc = 0`: byte `0xfe` parses to
`.INVALID` with no argument (vendored Instr.lean:585). -/
theorem decode_invalid : decode ⟨#[0xfe]⟩ ⟨0⟩ = some (Operation.INVALID, none) :=
  rfl

/-- **The gate kills `INVALID` unconditionally**: `δ .INVALID = none`
(Instr.lean:309), so after the two (vacuous, cost-`0`) gas checks, `Z` errors
`.InvalidInstruction` (Semantics.lean:454) — for EVERY state, with no stack or
gas hypothesis. -/
theorem Z_invalid (vj : Array UInt256) (s : EVM.State) :
    Z vj Operation.INVALID s = .error .InvalidInstruction := by
  unfold Z
  rw [memexp_invalid]
  simp only [cprime_invalid, Nat.not_lt_zero, reduceIte]
  rfl

/-- One `INVALID` iteration of the execution loop `X`: decode → `Z` errors.
No fuel is consumed past the peel — the error is definitional from `Z_invalid`. -/
theorem X_invalid (f : ℕ) (vj : Array UInt256) (s : EVM.State)
    (hcode : s.executionEnv.code = ⟨#[0xfe]⟩) (hpc : s.pc = ⟨0⟩) :
    X (f+1) vj s = .error .InvalidInstruction := by
  unfold X
  simp only [hcode, hpc, decode_invalid, Option.getD]
  rw [Z_invalid]

/-- **`Ξ` on the EIP-7610 swap code never succeeds, at ANY fuel**: fuels `0`/`1`
die `OutOfFuel` (mirror of the `preservesAccount_stop` small-fuel case split),
and at `f+2` the loop hits `Z`'s `.InvalidInstruction` error. -/
theorem Xi_invalid (fuel : ℕ) (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap)
    (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hcode : I.code = ⟨#[0xfe]⟩)
    (r : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)
    (o : ByteArray) :
    Ξ fuel cA gh blocks σ σ₀ g A I ≠ .ok (.success r o) := by
  intro hΞ
  rcases fuel with _ | (_ | f)
  · rw [NeverOutOfFuel.Ξ_zero] at hΞ
    exact Except.noConfusion hΞ
  · have hΞ' : Ξ 1 cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [Xi_one] at hΞ'
    exact Except.noConfusion hΞ'
  · have hΞ' : Ξ (f+2) cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [Ξ] at hΞ'
    simp only [bind, Except.bind] at hΞ'
    have hX := X_invalid f (D_J I.code ⟨0⟩)
      { (default : EVM.State) with
          accountMap := σ, σ₀ := σ₀, substate := A, executionEnv := I,
          blocks := blocks, genesisBlockHeader := gh, createdAccounts := cA,
          gasAvailable := g } hcode rfl
    simp only [] at hX
    rw [hX] at hΞ'
    exact Except.noConfusion hΞ'

/-- **`XiTriple P ⟨#[0xfe]⟩ Q` holds for ANY `P`, `Q`** — success-only triples
constrain only `.success` runs, and `Xi_invalid` shows there are none. This is
the honest (semantics-grounded, not vacuous-by-fiat) closure of
`lambda_of_xi`'s collision branch. -/
theorem xiTriple_invalid (P : AccountMap → Substate → Prop)
    (Q : AccountMap → Substate → ByteArray → Prop)
    (I : ExecutionEnv) (hcode : I.code = ⟨#[0xfe]⟩) : XiTriple P I Q :=
  fun fuel cA gh blocks σ σ₀ g A r o _ hrun =>
    absurd hrun (Xi_invalid fuel cA gh blocks σ σ₀ g A I hcode r o)

/-! ## 2. The `STOP` output pin (the deposited code is `.empty`) -/

/-- A successful `Ξ`-run of single-`STOP` code returns the empty output —
mirror of `preservesAccount_stop`, reading the output slot instead of the map
out of `Refinement.Xi_stop`. Feeds `hdeposit`: eqn (115) deposits this output
as the created account's code. -/
theorem Xi_stop_out_empty (I : ExecutionEnv) (hcode : I.code = ⟨#[0x00]⟩)
    (fuel : ℕ) (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader)
    (blocks : ProcessedBlocks) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate)
    (r : Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate)
    (o : ByteArray)
    (hΞ : Ξ fuel cA gh blocks σ σ₀ g A I = .ok (.success r o)) :
    o = ByteArray.empty := by
  rcases fuel with _ | (_ | (_ | f))
  · rw [NeverOutOfFuel.Ξ_zero] at hΞ
    exact Except.noConfusion hΞ
  · have hΞ' : Ξ 1 cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [Xi_one] at hΞ'
    exact Except.noConfusion hΞ'
  · have hΞ' : Ξ 2 cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [Xi_two_stop hcode] at hΞ'
    exact Except.noConfusion hΞ'
  · obtain ⟨g', hstop⟩ := Xi_stop f cA gh blocks σ σ₀ g A I hcode
    have hΞ' : Ξ (f + 3) cA gh blocks σ σ₀ g A I = .ok (.success r o) := hΞ
    rw [hstop] at hΞ'
    injection hΞ' with hres
    injection hres with _ h2
    exact h2.symm

/-! ## 3. The predicates and the preamble absorption -/

/-- The demo creation invariant: the beacon's map entry carries `demoAcct`'s
code and storage (in particular the cell `⟨0⟩ ↦ ⟨42⟩`), with SOME nonce and
balance. The nonce existential is forced by the `a`-blind `Ξ`-interface (see
the file header): when the opaque created address collides with the beacon,
`lambdaInit` bumps its nonce, and `Pξ` cannot distinguish that case. -/
def createInv (σ : AccountMap) : Prop :=
  ∃ n b, σ.find? demoCallee = some { demoAcct with nonce := n, balance := b }

/-- The precondition at the creation site: the beacon sits in the map exactly
as coded in the demo world (`rfl` at the concrete parent). Substate-insensitive
by design, sidestepping `Λ`'s `A.addAccessedAccount a` charge. -/
def createP : AccountMap → Substate → Prop :=
  fun σ _ => σ.find? demoCallee = some demoAcct

/-- The init-code precondition (post-preamble): the beacon invariant. -/
def createPξ : AccountMap → Substate → Prop := fun σ _ => createInv σ

/-- The init-code postcondition: the beacon invariant, plus the output pin
(`STOP` returns `.empty` — the to-be-deposited code). -/
def createQξ : AccountMap → Substate → ByteArray → Prop :=
  fun σ _ o => createInv σ ∧ o = ByteArray.empty

/-- The creation postcondition `create_spec` lands on the caller: the created
account exists at the (opaque) address `a` with the deposited `.empty` code,
and — provided `a` is not the beacon itself — the beacon survives with its
code/storage intact. -/
def createQ : AccountAddress → AccountMap → Substate → ByteArray → Prop :=
  fun a σ _ _ =>
    (∃ acct, σ.find? a = some acct ∧ acct.code = ByteArray.empty) ∧
    (a ≠ demoCallee → createInv σ)

/-- **The absorption fact at the opaque created address** (the
`thetaTransfer_find?` analog for `lambdaInit`): the nonce-bump/endowment
preamble at `a` preserves the account at `b` with AT MOST its balance rewritten
— **provided `a ≠ b`** (the debit at the sender `s` touches only the balance;
the only other write is the created-address insert). Split on the sender match
and the `compare b s` inner insert, exactly the `credit_stage`/`debit_stage`
recipe (TwoCallDemo.lean:235-294) collapsed into one two-insert walk. -/
theorem lambdaInit_find? (σ : AccountMap) (s a b : AccountAddress) (v : UInt256)
    (acc₀ : Account) (h : σ.find? b = some acc₀) (hab : a ≠ b) :
    ∃ bal, (lambdaInit σ s a v).find? b = some { acc₀ with balance := bal } := by
  simp only [lambdaInit]
  rcases hs : σ.find? s with _ | ac
  · -- sender absent: the preamble is a no-op (`Λ`'s funds-check comment)
    exact ⟨acc₀.balance, h⟩
  · -- outer insert (created address): skipped since `a ≠ b`; inner insert
    -- (sender debit): balance-only rewrite when `b = s`
    rw [Batteries.RBMap.find?_insert,
        if_neg (fun hEq => hab ((addrCompare_eq_iff b a).mp hEq).symm),
        Batteries.RBMap.find?_insert]
    by_cases hbs : compare b s = .eq
    · rw [if_pos hbs]
      obtain rfl : b = s := (addrCompare_eq_iff b s).mp hbs
      obtain rfl : ac = acc₀ := Option.some.inj (hs.symm.trans h)
      exact ⟨ac.balance - v, rfl⟩
    · rw [if_neg hbs]
      exact ⟨acc₀.balance, h⟩

/-- The `habsorb` obligation, covering BOTH sides of the opaque-address
dichotomy: for `a ≠ demoCallee` via `lambdaInit_find?` (nonce untouched), and
for `a = demoCallee` via the nonce-bump/endowment arm itself (the beacon IS the
created address: nonce `+1`, balance `v + ·`, code/storage untouched — or a
full no-op when the sender is absent). Both land in `createInv`'s `∃ n b`. -/
theorem lambdaInit_beacon (σ : AccountMap) (s a : AccountAddress) (v : UInt256)
    (h : σ.find? demoCallee = some demoAcct) :
    createInv (lambdaInit σ s a v) := by
  by_cases ha : a = demoCallee
  · subst ha
    simp only [lambdaInit]
    rcases hs : σ.find? s with _ | ac
    · exact ⟨demoAcct.nonce, demoAcct.balance, h⟩
    · have hfd : σ.findD demoCallee default = demoAcct := by
        simp only [Batteries.RBMap.findD, h, Option.getD_some]
      refine ⟨demoAcct.nonce + ⟨1⟩, v + demoAcct.balance, ?_⟩
      rw [Batteries.RBMap.find?_insert,
          if_pos ((addrCompare_eq_iff demoCallee demoCallee).mpr rfl), hfd]
  · obtain ⟨bal, hb⟩ := lambdaInit_find? σ s a demoCallee v demoAcct h ha
    exact ⟨demoAcct.nonce, bal, hb⟩

/-! ## 4. The concrete `LambdaTriple` via `lambda_of_xi` -/

/-- The `XiTriple` for the genuine init code: a successful single-`STOP` run
preserves the beacon's entry (`preservesAccount_stop`) and returns `.empty`
(`Xi_stop_out_empty`). -/
theorem create_xiTriple_stop (I : ExecutionEnv) (hcode : I.code = ⟨#[0x00]⟩) :
    XiTriple createPξ I createQξ := by
  intro fuel cA gh blocks σ σ₀ g A r o hpre hrun
  obtain ⟨n, b, hb⟩ := hpre
  exact ⟨⟨n, b, (preservesAccount_stop I demoCallee hcode
            fuel cA gh blocks σ σ₀ g A r o hrun).trans hb⟩,
         Xi_stop_out_empty I hcode fuel cA gh blocks σ σ₀ g A r o hrun⟩

/-- `lambda_of_xi`'s disjunctive `hΞ`, both arms real: the `STOP` child runs
and preserves; the EIP-7610 swap code never succeeds (`xiTriple_invalid`). -/
theorem create_xiTriple (I : ExecutionEnv)
    (hcode : I.code = ⟨#[0x00]⟩ ∨ I.code = ⟨#[0xfe]⟩) :
    XiTriple createPξ I createQξ :=
  hcode.elim (create_xiTriple_stop I) (xiTriple_invalid createPξ createQξ I)

/-- The `hdeposit` obligation: eqn (115)'s code-deposit insert at the opaque
`a`. The created-account leg is the insert's own entry (`find?_insert` self
arm, code pinned `.empty` by `createQξ`'s output leg); the beacon leg falls
through the insert (non-eq arm) — this is exactly where the `a ≠ demoCallee`
conditional in `createQ` is born (when `a = demoCallee` the deposit OVERWRITES
the beacon's code slot, so the unconditional claim would be false). -/
theorem create_deposit (a : AccountAddress) (σ'' : AccountMap) (A'' : Substate)
    (ret : ByteArray) (hQ : createQξ σ'' A'' ret) :
    createQ a (σ''.insert a { σ''.findD a default with code := ret }) A''
      .empty := by
  obtain ⟨⟨n, b, hb⟩, hret⟩ := hQ
  subst hret
  refine ⟨⟨{ σ''.findD a default with code := ByteArray.empty }, ?_, rfl⟩,
          fun hne => ⟨n, b, ?_⟩⟩
  · rw [Batteries.RBMap.find?_insert, if_pos ((addrCompare_eq_iff a a).mpr rfl)]
  · rw [Batteries.RBMap.find?_insert,
        if_neg (fun hEq => hne ((addrCompare_eq_iff demoCallee a).mp hEq).symm)]
    exact hb

/-- **The concrete `LambdaTriple`** — `lambda_of_xi` fired with all three side
conditions discharged: `hΞ` from `create_xiTriple` (both code arms), `habsorb`
from `lambdaInit_beacon`, `hdeposit` from `create_deposit`. This is the
non-vacuity witness for the CREATE-side triple surface. -/
theorem demoCreateTriple : LambdaTriple createP ⟨#[0x00]⟩ createQ :=
  lambda_of_xi createP createPξ createQξ createQ ⟨#[0x00]⟩
    create_xiTriple
    (fun σ _A s a v hP => lambdaInit_beacon σ s a v hP)
    create_deposit

/-! ## 5. The concrete parent and the `create_spec` firing -/

/-- The creator's address: `0xaa` (distinct from the `0xff` beacon). -/
def demoCreator : AccountAddress := AccountAddress.ofUInt256 ⟨0xaa⟩

/-- The parent map: the `TwoCallDemo` beacon (`0xff ↦ demoAcct`) plus the
creator as a default (zero-nonce, zero-balance) account. -/
def demoCreateMap : AccountMap := demoMap₀.insert demoCreator default

/-- The concrete parent state at the CREATE site: stack `[value, offset, size]
= [⟨0⟩, ⟨0⟩, ⟨1⟩]`, memory the single byte `0x00` (so the init code read is the
single-`STOP` program), the creator as `codeOwner` (zero value against its zero
balance passes the funds guard; depth `0`). -/
def demoCreateEv : EVM.State :=
  { (default : EVM.State) with
      accountMap := demoCreateMap
      memory := ⟨#[0x00]⟩
      stack := [⟨0⟩, ⟨0⟩, ⟨1⟩]
      executionEnv :=
        { (default : EVM.State).executionEnv with codeOwner := demoCreator } }

/-- The CREATE operands, in `create_spec`'s `μ₀ :: μ₁ :: μ₂ :: rest` shape. -/
theorem demoCreateEv_stack :
    demoCreateEv.stack = ⟨0⟩ :: ⟨0⟩ :: ⟨1⟩ :: ([] : Stack UInt256) := rfl

/-- The init-code read **computes**: `readWithPadding 0 1` of the one-byte
memory is the single-`STOP` program. Not a bare `rfl`: the padding tail
`zeroes ⟨len - read.size⟩` subtracts in `BitVec System.Platform.numBits`,
whose width is platform-opaque — `BitVec.sub_self` discharges it, and the
rest (the `2^64` panic guard, `readWithoutPadding`, the append) is closed
evaluation (the zero-fill is the pure `ffi.ByteArray.zeroes`, not FFI). -/
theorem demo_initRead :
    demoCreateEv.memory.readWithPadding (⟨0⟩ : UInt256).toNat
      (⟨1⟩ : UInt256).toNat = ⟨#[0x00]⟩ := by
  show (⟨#[0x00]⟩ : ByteArray).readWithPadding 0 1 = ⟨#[0x00]⟩
  unfold ByteArray.readWithPadding
  rw [if_neg (by norm_num)]
  show (⟨#[0x00]⟩ : ByteArray).readWithoutPadding 0 1
      ++ ffi.ByteArray.zeroes ⟨((1:Nat) : BitVec _) - ((1:Nat) : BitVec _)⟩
    = ⟨#[0x00]⟩
  rw [show ((1:Nat) : BitVec _) - ((1:Nat) : BitVec _) = 0#_ from
    BitVec.sub_self _]
  rfl

/-- `demoCreateTriple`, retyped at the memory-read index `create_spec` wants
(the read normalizes to `⟨#[0x00]⟩` by `demo_initRead`). -/
theorem demoCreateTriple' :
    LambdaTriple createP
      (demoCreateEv.memory.readWithPadding (⟨0⟩ : UInt256).toNat
        (⟨1⟩ : UInt256).toNat) createQ := by
  rw [demo_initRead]
  exact demoCreateTriple

/-- The precondition at the parent: the beacon survives the caller-side
nonce-bump preamble (`createInit` touches only the creator's entry) — closed
computation on the concrete two-entry map. -/
theorem demoCreate_pre :
    createP (createInit demoCreateEv.accountMap
      demoCreateEv.executionEnv.codeOwner) demoCreateEv.substate := rfl

/-- **The CREATE firing** — `create_spec` applied at the concrete parent with
`hstk`/`hΛ`/`hP` all discharged (`demoCreateEv_stack`/`demoCreateTriple'`/
`demoCreate_pre`), concluding: the pushed word is the created address, the
created account carries the deposited `.empty` code, and — unless the opaque
address collides with the beacon — the beacon's cell `⟨0⟩` still reads `⟨42⟩`
(the storage punchline, read out of `createQ` alone, mirroring
`demo_twoCall_storage`).

**THE HONEST BOUNDARY (pre-verified, by design): `hstep`/`hx` remain
hypotheses.** A hypothesis-free `hstep` — a forward-evaluated
`step … = .ok (explicit record)` equation like `demo_call₁` — is IMPOSSIBLE
here: the CREATE arm's `Λ` computes the created address via `ffi.KEC`
(`@[extern] opaque`, EVMYulLean/EvmYul/FFI/ffi.lean:27), and both the EIP-7610
collision-`if` and every subsequent map insert depend on that address, so no
concrete forward evaluation crosses the hash. This is the exp005
CREATE-witness keccak wall, verbatim: a boundary forced by the semantics'
opaque FFI, not a proof shortfall.
`hstep`-as-hypothesis (the parent step DID succeed) plus `hx` (the pushed word
is not the failure word `⟨0⟩`) is therefore the designed maximum concreteness
for a CREATE firing; everything on the near side of the hash is concrete and
discharged (no heartbeat crank needed — the concrete `RBMap`/`readWithPadding`
defeq checks are small). -/
theorem demo_create (f gasCost : ℕ) (arg : Option (UInt256 × Nat))
    (s' : EVM.State)
    (hstep : step (f+1) gasCost (some (.CREATE, arg)) demoCreateEv = .ok s')
    (hx : s'.stack ≠ ⟨0⟩ :: []) :
    ∃ a : AccountAddress,
      s'.stack = .ofNat a.val :: [] ∧
      (∃ acct, s'.accountMap.find? a = some acct ∧
        acct.code = ByteArray.empty) ∧
      (a ≠ demoCallee →
        (match s'.accountMap.find? demoCallee with
         | some acc => acc.lookupStorage ⟨0⟩
         | none => ⟨0⟩) = (⟨42⟩ : UInt256)) := by
  obtain ⟨a, hstka, hQ⟩ :=
    create_spec demoCreateEv_stack demoCreateTriple' demoCreate_pre hstep hx
  refine ⟨a, hstka, hQ.1, fun hne => ?_⟩
  obtain ⟨n, b, hb⟩ := hQ.2 hne
  rw [hb]
  rfl

end NestedEvmYul
