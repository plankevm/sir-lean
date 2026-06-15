import BytecodeLayer.DriveGen
import BytecodeLayer.Call
import BytecodeLayer.Step
import BytecodeLayer.Drive
import BytecodeLayer.Observables
import BytecodeLayer.Capstone1
import BytecodeLayer.Capstone3

/-!
# The external-call rung

A caller contract that `CALL`s a handwritten callee, run as a real top-level
`messageCall`, with the child call modeled **reflexively** — the genuine leanevm
`beginCall`/`drive` on the real child `CallParams` (`codeSource = toExecute …`),
never an oracle.

* **caller** `callerProg`: `PUSH1 0 ×5 ; PUSH3 callee ; PUSH4 0xFFFFFFFF ; CALL ; STOP`
  — pushes the seven CALL args (value-free, zero-memory; the gas arg is large, so
  the 63/64 `callGasCap` always binds, never the literal) then forwards a CALL to
  the callee and STOPs.
* **callee** `calleeProg`: `PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP` — stores `5` at slot
  `7`, then STOPs. Its cold first-write cost is `22106`.

The exported observable is the callee's persistent storage cell `(addrCallee, 7)`
in the **caller's** returned account map. This is exactly where the `∃G₀` story
bites: when `g` is large the child gets ≥ `22106` gas, the SSTORE commits, and the
cell reads `5`; when `g` is modest the 63/64 cap starves the child, its SSTORE
out-of-gases and is rolled back, the cell reads `0` — yet the caller never
top-level-OutOfGas's (it pushes flag `0` and STOPs cleanly). So the simpler
"not-OutOfGas ⇒ equal to the full run" form is *false*; the existential `∃G₀` is
forced. `messageCall_call_storageAt` proves the `∃G₀`; `call_counterexample`
exhibits the concrete starving `g`.
-/

namespace BytecodeLayer
open Evm Operation GasConstants

/-! ## Programs and accounts -/

/-- `PUSH1 0 ×5 ; PUSH3 0xCA11EE ; PUSH4 0xFFFFFFFF ; CALL ; STOP`. -/
def callerProg : ByteArray :=
  ⟨#[0x60,0x00, 0x60,0x00, 0x60,0x00, 0x60,0x00, 0x60,0x00,
     0x62,0xCA,0x11,0xEE, 0x63,0xFF,0xFF,0xFF,0xFF, 0xF1, 0x00]⟩

/-- `PUSH1 5 ; PUSH1 7 ; SSTORE ; STOP`. -/
def calleeProg : ByteArray := ⟨#[0x60,0x05, 0x60,0x07, 0x55, 0x00]⟩

def addrCaller : AccountAddress := AccountAddress.ofNat 0xCA11E2
def addrCallee : AccountAddress := AccountAddress.ofNat 0xCA11EE

def callerAccount : Account := { (default : Account) with code := callerProg }
def calleeAccount : Account := { (default : Account) with code := calleeProg }

/-- The world: caller and callee accounts, each with its code. -/
def accts : AccountMap :=
  ((∅ : AccountMap).insert addrCaller callerAccount).insert addrCallee calleeAccount

/-- The caller's account map after `beginCall`'s (value-0, self-recipient)
balance transfer — a no-op on storage, re-inserting the caller with `balance+0`. -/
def callerXfer : AccountMap :=
  accts.insert addrCaller { callerAccount with balance := callerAccount.balance + 0 }

/-- Top-level message-call parameters: run `callerProg` in `addrCaller`. -/
def callerParams (g : UInt64) : CallParams :=
  { blobVersionedHashes := [], createdAccounts := ∅, genesisBlockHeader := default,
    blocks := #[], accounts := accts, originalAccounts := ∅, substate := default,
    caller := addrCaller, origin := addrCaller, recipient := addrCaller,
    codeSource := .Code callerProg, gas := g, gasPrice := 0, value := 0,
    apparentValue := 0, calldata := .empty, depth := 0, blockHeader := default,
    chainId := 0, canModifyState := true }

/-- The caller frame `beginCall` produces (its mess collapsed to `callerXfer`). -/
def callerEnv : ExecutionEnv :=
  { address := addrCaller, origin := addrCaller, caller := addrCaller, value := (0:UInt256),
    calldata := .empty, code := callerProg, gasPrice := (0:UInt256).toNat,
    blockHeader := default, depth := 0, canModifyState := true,
    blobVersionedHashes := [], chainId := 0 }

def callerFrame (g : UInt64) : Frame :=
  { kind := .call ⟨∅, accts, default⟩,
    validJumps := validJumpDests callerProg 0,
    exec := { (default : ExecutionState) with
              accounts := callerXfer, originalAccounts := ∅, executionEnv := callerEnv,
              substate := default, createdAccounts := ∅, gasAvailable := g,
              blocks := #[], genesisBlockHeader := default } }

theorem beginCall_caller (g : UInt64) : beginCall (callerParams g) = .inl (callerFrame g) := by
  unfold beginCall callerParams callerFrame callerEnv callerXfer accts
  dsimp only
  rfl

/-! ## The caller frame after the seven pushes, and the CALL reduction -/

/-- The caller frame after the 7 `PUSH`es: the seven CALL args on the stack
(gas `0xFFFFFFFF = 4294967295` on top, callee addr `0xCA11EE = 13242862` next,
five `0`s below), pc at the `CALL` byte (19), gas `g - 21`. -/
def callerCalled (g : UInt64) : Frame :=
  { kind := .call ⟨∅, accts, default⟩,
    validJumps := validJumpDests callerProg 0,
    exec := { (default : ExecutionState) with
      accounts := callerXfer, originalAccounts := ∅, executionEnv := callerEnv,
      substate := default, createdAccounts := ∅,
      gasAvailable := g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
        - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3,
      blocks := #[], genesisBlockHeader := default,
      pc := 0 + UInt8.toUInt32 2 + UInt8.toUInt32 2 + UInt8.toUInt32 2 + UInt8.toUInt32 2
        + UInt8.toUInt32 2 + (3+1).toUInt32 + (4+1).toUInt32,
      stack := ((((((Stack.push [] 0).push 0).push 0).push 0).push 0).push 13242862).push 4294967295 } }

/-- The forwarded child gas: the 63/64-capped `callGasCap`. With the large gas
arg, this is `allButOneSixtyFourth ((g - 21) - 2600)` — the quantity the `∃G₀`
story turns on. -/
def childGas (g : UInt64) : ℕ :=
  callGasCap (AccountAddress.ofUInt256 13242862) (AccountAddress.ofUInt256 13242862) 0 4294967295
    callerXfer (g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
      - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3) default

/-- The callee account map after the (value-0) child value transfer: credit callee
`balance+0`, debit caller `balance-0` — a storage no-op, leaving callee's cell `7`
still `0`. -/
def childXfer : AccountMap :=
  let m1 := callerXfer.insert (AccountAddress.ofUInt256 13242862)
              { calleeAccount with balance := calleeAccount.balance + 0 }
  match m1.find? (AccountAddress.ofUInt256 (UInt256.ofNat callerEnv.address.val)) with
  | none => m1
  | some acc => m1.insert (AccountAddress.ofUInt256 (UInt256.ofNat callerEnv.address.val))
                  { acc with balance := acc.balance - 0 }

/-- The callee's execution env. -/
def childEnv : ExecutionEnv :=
  { address := AccountAddress.ofUInt256 13242862, origin := callerEnv.origin,
    caller := AccountAddress.ofUInt256 (UInt256.ofNat callerEnv.address.val), value := 0,
    calldata := (default : ExecutionState).memory.readWithPadding (UInt256.toNat 0) (UInt256.toNat 0),
    code := calleeProg, gasPrice := (UInt256.ofNat callerEnv.gasPrice).toNat,
    blockHeader := callerEnv.blockHeader, depth := callerEnv.depth + 1,
    canModifyState := callerEnv.canModifyState, blobVersionedHashes := callerEnv.blobVersionedHashes,
    chainId := callerEnv.chainId }

/-- The checkpoint substate of the child frame (caller's substate plus the
accessed callee account). -/
def childCkptSubstate : Substate :=
  ((default : ExecutionState) |>.addAccessedAccount (AccountAddress.ofUInt256 13242862)).substate

/-- The child frame `beginCall (callChildParams …)` produces — the **reflexive**
callee frame: code `calleeProg`, gas `childGas g`, depth `1`, with the child value
transfer applied. -/
def childFrame (g : UInt64) : Frame :=
  { kind := .call ⟨∅, callerXfer, childCkptSubstate⟩,
    validJumps := validJumpDests calleeProg 0,
    exec := { (default : ExecutionState) with
      accounts := childXfer, originalAccounts := ∅, executionEnv := childEnv,
      substate := childCkptSubstate, createdAccounts := ∅,
      gasAvailable := UInt64.ofNat (childGas g) } }

theorem beginCall_child (g : UInt64) :
    beginCall (callChildParams (callerCalled g) 13242862 4294967295) = .inl (childFrame g) := by
  unfold callChildParams callerCalled
  dsimp only [callerCharged]
  unfold beginCall
  dsimp only
  rw [show toExecute callerXfer (AccountAddress.ofUInt256 13242862) = ToExecute.Code calleeProg from by
        unfold toExecute; rw [if_neg (by decide)]; rfl]
  dsimp only
  unfold childFrame childEnv childXfer childCkptSubstate childGas callerEnv
  rfl

/-! ## Caller-side decode lemmas (pc forms as `incrPC` produces them) -/

theorem dc0 : decode callerProg 0 = some (.Push .PUSH1, some (0,1)) := by rfl
theorem dc2 : decode callerProg ((0:UInt32) + UInt8.toUInt32 2)
  = some (.Push .PUSH1, some (0,1)) := by rfl
theorem dc4 : decode callerProg (((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
  = some (.Push .PUSH1, some (0,1)) := by rfl
theorem dc6 : decode callerProg ((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
  = some (.Push .PUSH1, some (0,1)) := by rfl
theorem dc8 : decode callerProg (((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
    + UInt8.toUInt32 2) = some (.Push .PUSH1, some (0,1)) := by rfl
theorem dc10 : decode callerProg ((((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
    + UInt8.toUInt32 2) + UInt8.toUInt32 2) = some (.Push .PUSH3, some (0xCA11EE,3)) := by rfl
theorem dc14 : decode callerProg (((((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
    + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 4) = some (.Push .PUSH4, some (0xFFFFFFFF,4)) := by rfl
theorem dc19 : decode callerProg ((((((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
    + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 4) + UInt8.toUInt32 5)
  = some (.System .CALL, .none) := by rfl
theorem dc20 : decode callerProg (((((((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
    + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 4) + UInt8.toUInt32 5) + UInt8.toUInt32 1)
  = some (.System .STOP, .none) := by rfl

/-! ## Callee-side decode lemmas -/

theorem dce0 : decode calleeProg 0 = some (.Push .PUSH1, some (5,1)) := by rfl
theorem dce2 : decode calleeProg ((0:UInt32) + UInt8.toUInt32 2)
  = some (.Push .PUSH1, some (7,1)) := by rfl
theorem dce4 : decode calleeProg (((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2)
  = some (.Smsf .SSTORE, .none) := by rfl
theorem dce5 : decode calleeProg ((((0:UInt32) + UInt8.toUInt32 2) + UInt8.toUInt32 2) + UInt8.toUInt32 1)
  = some (.System .STOP, .none) := by rfl

/-! ## The child (callee) run — reflexive, success path -/

theorem gv : GasConstants.Gverylow = 3 := rfl

/-- SSTORE's cold first-write cost in the callee is `22100`, for any exec whose
storage-relevant fields are the callee's (original empty, accounts `childXfer`,
self the callee, substate the post-access checkpoint). -/
theorem sstoreChargeOf_child (exec : ExecutionState)
    (h1 : exec.originalAccounts = ∅) (h2 : exec.accounts = childXfer)
    (h3 : exec.executionEnv.address = AccountAddress.ofUInt256 13242862)
    (h4 : exec.substate = childCkptSubstate) : sstoreChargeOf exec 7 5 = 22100 := by
  unfold sstoreChargeOf; rw [h1, h2, h3, h4]; dsimp only [childXfer, childCkptSubstate]; decide

/-- **Lower bound forcing the `∃G₀`.** For `g ≥ 30000` the 63/64-capped child gas
clears the callee's `22106` cold-SSTORE cost. (No upper bound on `g`: the gas-arg
cap `0xFFFFFFFF` is itself ≥ `22106`, so even astronomically large `g` succeeds.) -/
theorem childGas_lb (g : UInt64) (hg : 30000 ≤ g.toNat) : 22106 ≤ childGas g := by
  unfold childGas callGasCap
  rw [if_pos (by
    rw [show callExtraCost (AccountAddress.ofUInt256 13242862) (AccountAddress.ofUInt256 13242862) 0
          callerXfer default = 2600 from by decide]
    rw [show (g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
          - UInt64.ofNat 3 - UInt64.ofNat 3) = subCharges g [3,3,3,3,3,3,3] from by simp [subCharges]]
    rw [toNat_subCharges g [3,3,3,3,3,3,3] (by simp; omega)]; simp; omega)]
  rw [show callExtraCost (AccountAddress.ofUInt256 13242862) (AccountAddress.ofUInt256 13242862) 0
        callerXfer default = 2600 from by decide]
  rw [show (g - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3 - UInt64.ofNat 3
        - UInt64.ofNat 3 - UInt64.ofNat 3) = subCharges g [3,3,3,3,3,3,3] from by simp [subCharges]]
  rw [toNat_subCharges g [3,3,3,3,3,3,3] (by simp; omega)]
  unfold allButOneSixtyFourth
  show 22106 ≤ min ((g.toNat - List.sum [3,3,3,3,3,3,3] - 2600)
    - (g.toNat - List.sum [3,3,3,3,3,3,3] - 2600)/64) 4294967295
  simp only [List.sum_cons, List.sum_nil]; omega

/-- The child gas always fits in `UInt64` (it is capped by `min … 0xFFFFFFFF`). -/
theorem childGas_ub (g : UInt64) : childGas g < 2^64 := by
  have hgv : ((4294967295:UInt256)).toNat < 2^64 := by decide
  unfold childGas callGasCap
  split
  · exact lt_of_le_of_lt (min_le_right _ _) hgv
  · exact hgv

/-- The callee exec right after its two `PUSH`es (stack `[key, val] = [7,5]`). -/
def childAfter2Push (g : UInt64) : ExecutionState :=
  { (childFrame g).exec with
    gasAvailable := UInt64.ofNat (childGas g) - UInt64.ofNat 3 - UInt64.ofNat 3,
    pc := (default:ExecutionState).pc + UInt8.toUInt32 2 + UInt8.toUInt32 2, stack := [7,5] }

/-- The `CallResult` the successful callee delivers (its `endCall`). -/
def childResult (g : UInt64) : CallResult :=
  endCall ⟨∅, callerXfer, childCkptSubstate⟩ (.success (sstorePost (childAfter2Push g) 7 5 []) .empty)

/-- A `g`-free exec carrying the callee's post-SSTORE world (`childXfer` with cell
`7` of the callee set to `5`). -/
def childStoredExec : ExecutionState :=
  { (default:ExecutionState) with
    accounts := childXfer, originalAccounts := ∅,
    executionEnv := childEnv, substate := childCkptSubstate }

/-- The account map the callee leaves behind: `childXfer` after `SSTORE 7 5`. -/
def childStored : AccountMap := (childStoredExec.sstore 7 5).accounts

/-- `childResult`'s account map is `g`-independent (gas does not touch storage). -/
theorem childResult_accounts (g : UInt64) : (childResult g).accounts = childStored := by
  unfold childResult endCall sstorePost childAfter2Push childFrame childStored childStoredExec
  rfl

/-- The callee committed `5` to its own slot `7`. -/
theorem childStored_storage :
    ((childStored.find? addrCallee).option 0 (fun a => a.lookupStorage 7)) = (5:UInt256) := by
  unfold childStored childStoredExec childXfer childEnv childCkptSubstate; decide

/-- The callee reports success. -/
theorem childResult_success (g : UInt64) : (childResult g).success = true := by
  unfold childResult endCall; dsimp only

set_option maxHeartbeats 400000000 in
/-- **The child run, reflexively.** Starting from the real `childFrame g`
(`= beginCall (callChildParams …)`), the genuine driver runs the callee
`PUSH;PUSH;SSTORE;STOP` and delivers `childResult g` to the suspended parent `pd`,
which resumes. Five fuel units: 3 steps + the 2-unit halt-and-deliver. -/
theorem child_run (g : UInt64) (n : ℕ) (pd : PendingCall) (ps : List Pending)
    (hcg : 22106 ≤ childGas g) (hcg2 : childGas g < 2^64) :
    drive (n + 5) (.call pd :: ps) (.inl (childFrame g))
      = drive n ps (.inl (resumeAfterCall (childResult g) pd)) := by
  have hofnat : (UInt64.ofNat (childGas g)).toNat = childGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  conv_lhs => dsimp only [childFrame]
  rw [driveG_step _ _ _ _ (stepFrame_push1 _ 5 dce0 (by
        show 3 ≤ (UInt64.ofNat (childGas g)).toNat; rw [hofnat]; omega) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [driveG_step _ _ _ _ (stepFrame_push1 _ 7 dce2 (by
        show 3 ≤ (UInt64.ofNat (childGas g) - UInt64.ofNat 3).toNat
        rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega)
        (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  have hg6 : ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat = childGas g - 6 := by
    rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega) (by omega),
        toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega
  rw [driveG_step _ _ _ _ (stepFrame_sstore _ 7 5 _ dce4 rfl ?hsz rfl ?hstip ?hcost)]
  case hsz => show (2:ℕ) ≤ 1024; omega
  case hstip =>
    show ¬ ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat ≤ Gcallstipend
    rw [hg6, show Gcallstipend = 2300 from rfl]; omega
  case hcost => rw [sstoreChargeOf_child _ rfl rfl rfl rfl, hg6]; omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  rw [driveG_halt_callDeliver _ _ _ _ _ (stepFrame_stop _ dce5 (by show (0:ℕ)≤1024; omega))]
  unfold childResult endCall sstorePost childAfter2Push childFrame
  rfl

/-! ## The resumed caller, and the final observable -/

/-- After the child returns, `resumeAfterCall` writes the child's account map
(`childStored`) into the caller's frame. -/
theorem resumed_acc (g : UInt64) :
    (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295)).exec.accounts
      = childStored := by
  unfold resumeAfterCall callPending
  dsimp only [ExecutionState.replaceStackAndIncrPC]; exact childResult_accounts g

/-- The resumed caller frame keeps the caller's `.call` checkpoint. -/
theorem resumed_kind (g : UInt64) :
    (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295)).kind
      = .call ⟨∅, accts, default⟩ := by
  unfold resumeAfterCall callPending callerCalled; rfl

/-- `childStored` is non-empty (it carries the callee's committed cell), so
`endCall` keeps it rather than reverting to the checkpoint. -/
theorem childStored_ne : (childStored == (∅:AccountMap)) = false := by
  unfold childStored childStoredExec childXfer childEnv childCkptSubstate; decide

/-- The whole top-level call's storage observable at `(addrCallee, 7)` is `5`: the
caller `STOP`s with the child's committed map intact. -/
theorem final_obs (g : UInt64) :
    CallResult.storageAt
      (endFrame (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295))
        (FrameHalt.success
          (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295)).exec
          ByteArray.empty)).toCallResult addrCallee 7 = 5 := by
  unfold CallResult.storageAt endFrame
  rw [resumed_kind]
  dsimp only [FrameResult.toCallResult]
  unfold endCall
  dsimp only
  rw [resumed_acc]
  simp only [childStored_ne, if_false]
  exact childStored_storage

/-! ## The exported external-call theorem (`∃G₀`) -/

set_option maxHeartbeats 800000000 in
/-- **External-call rung — the `∃G₀` observables theorem.** There is a gas floor
`G₀` such that for every `g ≥ G₀` the top-level message call into the caller
contract (which forwards a real `CALL` to the callee) leaves the callee's storage
cell `(addrCallee, 7)` holding `5`. The child call is the **genuine reflexive**
`beginCall`/`drive` on the real child `CallParams` (`codeSource = toExecute …`):
the SSTORE that writes `5` runs inside that real sub-call, gets ≥ `22106` gas past
the 63/64 `callGasCap`, and commits.

The `∃G₀` is *forced*, not cosmetic: `call_counterexample` exhibits a modest `g`
for which the same observable is `0` (the 63/64 cap starves the callee, its SSTORE
out-of-gases and rolls back) while the top-level call still completes — so no
single gas-independent statement ("not OutOfGas ⇒ cell is 5") can hold. -/
theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 := by
  refine ⟨100000, fun g hg => ?_⟩
  have hg30 : 30000 ≤ g.toNat := by omega
  have hcg := childGas_lb g hg30
  have hcg2 := childGas_ub g
  unfold messageCall
  rw [beginCall_caller]
  dsimp only [callerFrame]
  rw [show (callerParams g).gas = g from rfl]
  rw [show seedFuel g = (seedFuel g - 15) + 15 by have := two_le_seedFuel g; unfold seedFuel; omega]
  simp only [show (default:ExecutionState).pc = (0:UInt32) from rfl,
             show (default:ExecutionState).stack = ([]:Stack UInt256) from rfl]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc0 (by show 3≤g.toNat;omega) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc2 (by
        show 3 ≤ (subCharges g [3]).toNat; rw [toNat_subCharges g [3] (by simp;omega)]; simp; omega)
        (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc4 (by
        show 3 ≤ (subCharges g [3,3]).toNat; rw [toNat_subCharges g [3,3] (by simp;omega)]; simp; omega)
        (by show (2:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc6 (by
        show 3 ≤ (subCharges g [3,3,3]).toNat; rw [toNat_subCharges g [3,3,3] (by simp;omega)]; simp; omega)
        (by show (3:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc8 (by
        show 3 ≤ (subCharges g [3,3,3,3]).toNat; rw [toNat_subCharges g [3,3,3,3] (by simp;omega)]; simp; omega)
        (by show (4:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push _ .PUSH3 0xCA11EE 3 (by nofun) dc10 rfl rfl (by
        show 3 ≤ (subCharges g [3,3,3,3,3]).toNat; rw [toNat_subCharges g [3,3,3,3,3] (by simp;omega)]; simp; omega)
        (by show (5:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push _ .PUSH4 0xFFFFFFFF 4 (by nofun) dc14 rfl rfl (by
        show 3 ≤ (subCharges g [3,3,3,3,3,3]).toNat; rw [toNat_subCharges g [3,3,3,3,3,3] (by simp;omega)]; simp; omega)
        (by show (6:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  -- fold the 7-pushed frame into `callerCalled g` (defeq), then take the real CALL
  show (FrameResult.toCallResult <$> drive (seedFuel g - 15 + 8) []
        (Sum.inl (callerCalled g))).map (fun r => CallResult.storageAt r addrCallee 7) = Except.ok 5
  rw [driveG_needsCall_code _ _ (callerCalled g) _ _ _
        (stepFrame_call _ 0xFFFFFFFF 0xCA11EE dc19 rfl (by show (7:ℕ)≤1024; omega) rfl (by show (0:ℕ)<1024; omega)
          (by
            show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0 _ _
                  ≤ (subCharges g [3,3,3,3,3,3,3]).toNat
            rw [toNat_subCharges g [3,3,3,3,3,3,3] (by simp;omega)]
            rw [show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
                  (callerCalled g).exec.accounts (callerCalled g).exec.substate = 2600 from by
                  unfold callerCalled; dsimp only; decide]
            simp; omega))
        (beginCall_child g)]
  -- the reflexive child run
  rw [child_run g _ _ _ hcg hcg2]
  -- resume, then the caller STOPs
  rw [drive_halt _ _ _ (stepFrame_stop
        (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295))
        (by
          show decode (resumeAfterCall (childResult g)
              (callPending (callerCalled g) 13242862 4294967295)).exec.executionEnv.code _ = _
          unfold resumeAfterCall callPending callerCalled callerEnv
          dsimp only [ExecutionState.replaceStackAndIncrPC, callerCharged]
          exact dc20)
        (by
          unfold resumeAfterCall callPending
          dsimp only [ExecutionState.replaceStackAndIncrPC]
          show (Stack.push [] _).size ≤ 1024; show (1:ℕ) ≤ 1024; omega))]
  -- read off the storage observable
  dsimp only [Except.map]
  exact congrArg Except.ok (final_obs g)

/-! ## The forced-`∃G₀` counterexample (the call OOGs, observable differs)

A *modest* gas `g = 24000` for which the 63/64 `callGasCap` starves the callee:
`childGas 24000 = 21045 < 22106`, so its `SSTORE` out-of-gases, its write is
rolled back, the caller is handed flag `0` and `STOP`s cleanly. The top-level
call completes (no `OutOfGas`), yet the callee's cell `(addrCallee, 7)` reads `0`,
not `5`. This is what makes the existential genuine: no gas-independent
"completes ⇒ cell is 5" statement can hold. -/

/-- The failing child's `CallResult`: the `endCall` of an `OutOfGas` exception,
reverting to the pre-call checkpoint (`callerXfer`), `success = false`. -/
def childResultFail : CallResult := endCall ⟨∅, callerXfer, childCkptSubstate⟩ (.exception .OutOfGas)

set_option maxHeartbeats 200000000 in
/-- **The starved child run.** When the 63/64-capped `childGas` clears the stipend
gate but cannot pay the `SSTORE` (`childGas - 6 < 22100`), the real child run
out-of-gases at the `SSTORE`; `endCall` reverts to the checkpoint and the parent
resumes with `childResultFail`. Four fuel units (2 pushes + the OOG halt-deliver). -/
theorem child_run_oog (g : UInt64) (n : ℕ) (pd : PendingCall) (ps : List Pending)
    (hstip : 2306 < childGas g) (hoog : childGas g - 6 < 22100) (hub : childGas g < 2^64) :
    drive (n + 4) (.call pd :: ps) (.inl (childFrame g))
      = drive n ps (.inl (resumeAfterCall childResultFail pd)) := by
  have hofnat : (UInt64.ofNat (childGas g)).toNat = childGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  conv_lhs => dsimp only [childFrame]
  rw [driveG_step _ _ _ _ (stepFrame_push1 _ 5 dce0 (by
        show 3 ≤ (UInt64.ofNat (childGas g)).toNat; rw [hofnat]; omega) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [driveG_step _ _ _ _ (stepFrame_push1 _ 7 dce2 (by
        show 3 ≤ (UInt64.ofNat (childGas g) - UInt64.ofNat 3).toNat
        rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega)
        (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  have hg6 : ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat = childGas g - 6 := by
    rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega) (by omega),
        toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega
  rw [driveG_halt_callDeliver _ _ _ _ _ (stepFrame_sstore_oog _ 7 5 _ dce4 rfl ?hsz rfl ?hstip2 ?hoog2)]
  case hsz => show (2:ℕ) ≤ 1024; omega
  case hstip2 =>
    show ¬ ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat ≤ Gcallstipend
    rw [hg6, show Gcallstipend = 2300 from rfl]; omega
  case hoog2 =>
    show ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat < sstoreChargeOf _ 7 5
    rw [hg6, sstoreChargeOf_child _ rfl rfl rfl rfl]; omega
  unfold childResultFail
  rfl

theorem resumedF_acc (g : UInt64) :
    (resumeAfterCall childResultFail (callPending (callerCalled g) 13242862 4294967295)).exec.accounts
      = callerXfer := by
  unfold resumeAfterCall callPending childResultFail endCall; rfl

theorem resumedF_kind (g : UInt64) :
    (resumeAfterCall childResultFail (callPending (callerCalled g) 13242862 4294967295)).kind
      = .call ⟨∅, accts, default⟩ := by
  unfold resumeAfterCall callPending callerCalled; rfl

theorem callerXfer_ne : (callerXfer == (∅:AccountMap)) = false := by unfold callerXfer; decide

/-- The callee's cell `7` is `0` in the pre-call world (it never committed). -/
theorem callerXfer_storage :
    ((callerXfer.find? addrCallee).option 0 (fun a => a.lookupStorage 7)) = (0:UInt256) := by
  unfold callerXfer; decide

theorem final_obs_fail (g : UInt64) :
    CallResult.storageAt
      (endFrame (resumeAfterCall childResultFail (callPending (callerCalled g) 13242862 4294967295))
        (FrameHalt.success
          (resumeAfterCall childResultFail (callPending (callerCalled g) 13242862 4294967295)).exec
          ByteArray.empty)).toCallResult addrCallee 7 = 0 := by
  unfold CallResult.storageAt endFrame
  rw [resumedF_kind]
  dsimp only [FrameResult.toCallResult]
  unfold endCall
  dsimp only
  rw [resumedF_acc]
  simp only [callerXfer_ne, if_false]
  exact callerXfer_storage

set_option maxHeartbeats 800000000 in
/-- **The executable counterexample.** At the modest gas `g = 24000` the same
message call leaves cell `(addrCallee, 7)` holding `0` — the callee's `SSTORE`
out-of-gased under the 63/64 cap and rolled back, while the caller completed. Read
against `messageCall_call_storageAt` (which gives `5` for all `g ≥ 100000`), this
shows the `∃G₀` is forced: there is no gas-floor-free statement. -/
theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0 := by
  have hstip : 2306 < childGas 24000 := by unfold childGas; decide
  have hoog : childGas 24000 - 6 < 22100 := by decide
  have hub : childGas 24000 < 2^64 := childGas_ub 24000
  unfold messageCall
  rw [beginCall_caller]
  dsimp only [callerFrame]
  rw [show (callerParams 24000).gas = 24000 from rfl]
  rw [show seedFuel 24000 = (seedFuel 24000 - 14) + 14 by unfold seedFuel; decide]
  simp only [show (default:ExecutionState).pc = (0:UInt32) from rfl,
             show (default:ExecutionState).stack = ([]:Stack UInt256) from rfl]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc0 (by decide) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc2 (by decide) (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc4 (by decide) (by show (2:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc6 (by decide) (by show (3:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 0 dc8 (by decide) (by show (4:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push _ .PUSH3 0xCA11EE 3 (by nofun) dc10 rfl rfl (by decide)
        (by show (5:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push _ .PUSH4 0xFFFFFFFF 4 (by nofun) dc14 rfl rfl (by decide)
        (by show (6:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  show (FrameResult.toCallResult <$> drive (seedFuel 24000 - 14 + 7) []
        (Sum.inl (callerCalled 24000))).map (fun r => CallResult.storageAt r addrCallee 7) = Except.ok 0
  rw [driveG_needsCall_code _ _ (callerCalled 24000) _ _ _
        (stepFrame_call _ 0xFFFFFFFF 0xCA11EE dc19 rfl (by show (7:ℕ)≤1024; omega) rfl (by show (0:ℕ)<1024; omega)
          (by
            show callExtraCost (AccountAddress.ofUInt256 0xCA11EE) (AccountAddress.ofUInt256 0xCA11EE) 0
                  (callerCalled 24000).exec.accounts (callerCalled 24000).exec.substate ≤ _
            unfold callerCalled; dsimp only; decide))
        (beginCall_child 24000)]
  rw [child_run_oog 24000 _ _ _ hstip hoog hub]
  rw [drive_halt _ _ _ (stepFrame_stop
        (resumeAfterCall childResultFail (callPending (callerCalled 24000) 13242862 4294967295))
        (by
          show decode (resumeAfterCall childResultFail
              (callPending (callerCalled 24000) 13242862 4294967295)).exec.executionEnv.code _ = _
          unfold resumeAfterCall callPending callerCalled callerEnv
          dsimp only [ExecutionState.replaceStackAndIncrPC, callerCharged]
          exact dc20)
        (by
          unfold resumeAfterCall callPending
          dsimp only [ExecutionState.replaceStackAndIncrPC]
          show (Stack.push [] _).size ≤ 1024; show (1:ℕ) ≤ 1024; omega))]
  dsimp only [Except.map]
  exact congrArg Except.ok (final_obs_fail 24000)

/-! ## Reflexivity witness

The child call inside `messageCall_call_storageAt` is run by the real
`beginCall`/`drive` on `callChildParams …` — the same operations `messageCall`
performs. This lemma makes that explicit: the **standalone** `messageCall` on the
very `CallParams` the `CALL` produced succeeds and commits cell `7 = 5`, i.e. the
in-parent child computation *is* the genuine top-level child message call (no
oracle). -/
set_option maxHeartbeats 400000000 in
theorem messageCall_child_reflexive (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (messageCall (callChildParams (callerCalled g) 13242862 4294967295)).map
      (fun r => (r.success, CallResult.storageAt r addrCallee 7)) = .ok (true, 5) := by
  have hcg := childGas_lb g hg
  have hcg2 := childGas_ub g
  have hofnat : (UInt64.ofNat (childGas g)).toNat = childGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  unfold messageCall
  rw [beginCall_child]
  dsimp only
  rw [show seedFuel (callChildParams (callerCalled g) 13242862 4294967295).gas
        = (seedFuel (childFrame g).exec.gasAvailable - 5) + 5 by
      have : (callChildParams (callerCalled g) 13242862 4294967295).gas
          = (childFrame g).exec.gasAvailable := by
        unfold callChildParams childFrame; dsimp only [callerCharged, childGas]; rfl
      rw [this]; have := two_le_seedFuel (childFrame g).exec.gasAvailable; unfold seedFuel; omega]
  conv_lhs => dsimp only [childFrame]
  rw [drive_step _ _ _ (stepFrame_push1 _ 5 dce0 (by
        show 3 ≤ (UInt64.ofNat (childGas g)).toNat; rw [hofnat]; omega) (by show (0:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  rw [drive_step _ _ _ (stepFrame_push1 _ 7 dce2 (by
        show 3 ≤ (UInt64.ofNat (childGas g) - UInt64.ofNat 3).toNat
        rw [toNat_sub_ofNat _ 3 (by rw [hofnat]; omega) (by omega), hofnat]; omega)
        (by show (1:ℕ)+1≤1024; omega))]
  dsimp only [ExecutionState.replaceStackAndIncrPC]; simp only [gv]
  have hg6 : ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat = childGas g - 6 := by
    rw [toNat_sub_ofNat _ 3 (by rw [toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega) (by omega),
        toNat_sub_ofNat _ 3 (by rw[hofnat];omega) (by omega), hofnat]; omega
  rw [drive_step _ _ _ (stepFrame_sstore _ 7 5 _ dce4 rfl ?hsz rfl ?hstip ?hcost)]
  case hsz => show (2:ℕ) ≤ 1024; omega
  case hstip =>
    show ¬ ((UInt64.ofNat (childGas g) - UInt64.ofNat 3) - UInt64.ofNat 3).toNat ≤ Gcallstipend
    rw [hg6, show Gcallstipend = 2300 from rfl]; omega
  case hcost => rw [sstoreChargeOf_child _ rfl rfl rfl rfl, hg6]; omega
  dsimp only [sstorePost, ExecutionState.replaceStackAndIncrPC]
  rw [drive_halt _ _ _ (stepFrame_stop _ dce5 (by show (0:ℕ)≤1024; omega))]
  show Except.ok ((childResult g).success, CallResult.storageAt (childResult g) addrCallee 7) = Except.ok (true, 5)
  rw [childResult_success, CallResult.storageAt, childResult_accounts, childStored_storage]

end BytecodeLayer
