import BytecodeLayer.Reasoning.DriveGen
import BytecodeLayer.Reasoning.Call
import BytecodeLayer.Reasoning.Step
import BytecodeLayer.Reasoning.Drive
import BytecodeLayer.Observables
import BytecodeLayer.Programs
import BytecodeLayer.Proof.DecodeGas
import BytecodeLayer.Proof.Sequence

/-!
# Proof — the external-call rung

Proof internals for M2. The exported statements (`messageCall_call_storageAt`,
`call_counterexample`, `messageCall_child_reflexive`) live in `Spec.lean`. The
caller/callee programs and `callerParams` live in `Programs.lean`. Everything
here — the intermediate frames at each pc, decode lemmas, the 63/64 gas
arithmetic, the reflexive child run, and the long reductions — is proof
machinery and not part of the audit surface.

The child call is modeled **reflexively**: the genuine leanevm `beginCall`/`drive`
on the real child `CallParams` (`codeSource = toExecute …`), never an oracle.
-/

namespace BytecodeLayer.Proof
open Evm Operation GasConstants

/-! ## Derived world states -/

/-- The caller's account map after `beginCall`'s (value-0, self-recipient)
balance transfer — a no-op on storage, re-inserting the caller with `balance+0`. -/
def callerXfer : AccountMap :=
  accts.insert addrCaller { callerAccount with balance := callerAccount.balance + 0 }

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
  simp only [childStored_ne]
  exact childStored_storage

/-! ## The exported external-call theorem (`∃G₀`) — proof

The top-level run is first pinned to the **exact `CallResult`** the caller `STOP`s
with (`callerResult g`), so that *both* its storage observable and its success flag
are readable; the `∃G₀ ∀g` storage theorem and the `completedWith` form (used by
the general rung-2 instance) are then corollaries. -/

/-- The exact `CallResult` the top-level caller `STOP`s with after the (successful)
child commits: the `endFrame`/`endCall` of the resumed caller frame. -/
def callerResult (g : UInt64) : CallResult :=
  (endFrame (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295))
    (FrameHalt.success
      (resumeAfterCall (childResult g) (callPending (callerCalled g) 13242862 4294967295)).exec
      ByteArray.empty)).toCallResult

/-- The caller `STOP`s successfully (it ignores the child's flag). -/
theorem callerResult_success (g : UInt64) : (callerResult g).success = true := by
  unfold callerResult endFrame
  rw [resumed_kind]; dsimp only [FrameResult.toCallResult]; unfold endCall; dsimp only

set_option maxHeartbeats 800000000 in
/-- **The top-level run pinned to its `CallResult`.** For `g ≥ 30000`, the whole
message call into the caller equals `.ok (callerResult g)` — the caller forwards a
real `CALL` to the callee, the child commits, and the caller `STOP`s carrying the
child's account map. Both the storage observable and the success flag read off this
single equation. -/
theorem messageCall_call_eq (g : UInt64) (hg : 30000 ≤ g.toNat) :
    messageCall (callerParams g) = .ok (callerResult g) := by
  have hg30 : 30000 ≤ g.toNat := hg
  have hcg := childGas_lb g hg30
  have hcg2 := childGas_ub g
  rw [messageCall_eq_drive _ _ (beginCall_caller g)]
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
  show FrameResult.toCallResult <$> drive (seedFuel g - 15 + 8) []
        (Sum.inl (callerCalled g)) = Except.ok (callerResult g)
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
  -- the driver returns `.ok (endFrame …)`, i.e. `.ok (callerResult g)`
  rfl

/-! ## The exported external-call theorem (`∃G₀`) — corollaries -/

theorem messageCall_call_storageAt :
    ∃ G₀ : ℕ, ∀ g : UInt64, G₀ ≤ g.toNat →
      (messageCall (callerParams g)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 5 := by
  refine ⟨100000, fun g hg => ?_⟩
  rw [messageCall_call_eq g (by omega)]
  exact congrArg Except.ok (final_obs g)

/-! ## The forced-`∃G₀` counterexample (the call OOGs, observable differs) — proof

A *modest* gas `g = 24000` for which the 63/64 `callGasCap` starves the callee:
`childGas 24000 = 21045 < 22106`, so its `SSTORE` out-of-gases, its write is
rolled back, the caller is handed flag `0` and `STOP`s cleanly. -/

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
  simp only [callerXfer_ne]
  exact callerXfer_storage

set_option maxHeartbeats 800000000 in
theorem call_counterexample :
    (messageCall (callerParams 24000)).map (fun r => CallResult.storageAt r addrCallee 7) = .ok 0 := by
  have hstip : 2306 < childGas 24000 := by unfold childGas; decide
  have hoog : childGas 24000 - 6 < 22100 := by decide
  have hub : childGas 24000 < 2^64 := childGas_ub 24000
  rw [messageCall_eq_drive _ _ (beginCall_caller 24000)]
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

/-! ## Reflexivity witness — proof

The child call inside `messageCall_call_storageAt` is run by the real
`beginCall`/`drive` on `callChildParams …` — the same operations `messageCall`
performs. This lemma makes that explicit. -/
set_option maxHeartbeats 400000000 in
theorem messageCall_child_reflexive (g : UInt64) (hg : 30000 ≤ g.toNat) :
    (messageCall (callChildParams (callerCalled g) 13242862 4294967295)).map
      (fun r => (r.success, CallResult.storageAt r addrCallee 7)) = .ok (true, 5) := by
  have hcg := childGas_lb g hg
  have hcg2 := childGas_ub g
  have hofnat : (UInt64.ofNat (childGas g)).toNat = childGas g := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [messageCall_eq_drive _ _ (beginCall_child g)]
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

end BytecodeLayer.Proof
