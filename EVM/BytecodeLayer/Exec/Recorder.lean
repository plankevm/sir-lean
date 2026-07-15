import BytecodeLayer.Exec.Observable
import BytecodeLayer.Exec.Call
import BytecodeLayer.Exec.Create

open BytecodeLayer.Exec

namespace BytecodeLayer.Exec.Recorder

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare
open GasConstants

def evmCallEntry (result : CallResult) (pd : PendingCall) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCallOracle.postStorage result pd self key)
  , evmCallOracle.successWord result pd )

def evmCreateEntry (result : CreateResult) (pd : PendingCreate) (self : AccountAddress) :
    World × Word :=
  ( (fun key => evmCreateOracle.postStorage result pd self key)
  , evmCreateOracle.addressWord result pd )

structure CallRecord where
  result : CallResult
  pending : PendingCall

structure CreateRecord where
  result : CreateResult
  pending : PendingCreate

structure RunLog where
  observable : FrameResult
  gas : List Word
  sloads : List Nat
  calls : List CallRecord
  creates : List CreateRecord

def RunLog.clean (log : RunLog) : Prop :=
  match log.observable with
    | .call r   => r.success = true ∨ r.gasRemaining ≠ 0
    | .create _ => False

def RunLog.cleanb (log : RunLog) : Bool :=
  match log.observable with
    | .call r   => r.success || r.gasRemaining != 0
    | .create _ => false

def isGasOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 == .Smsf .GAS

def isSloadOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 == .Smsf .SLOAD

/-- Detect a CREATE2 cursor (the twin of `isGasOp`/`isSloadOp`). Used by `driveLog`
to record a soft-fail entry on the `.next`-branch of a top-level CREATE2, so
`log.creates` aligns 1:1 with CREATE2 cursors (descend records the child result; a
soft-fail records `softFailCreateRecord`). -/
def isCreate2Op (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
    == .System .CREATE2

/-- Detect a CALL cursor so a top-level soft-fail still contributes its call record. -/
def isCallOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1
    == .System .CALL

/-- The record consumed by the call channel when `callArm` takes its soft-fail branch. -/
def softFailCallRecord (current : Frame) : CallRecord :=
  let exec := current.exec
  let (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) :=
    match exec.stack.pop7 with
      | some operands => operands
      | none => ([], 0, 0, 0, 0, 0, 0, 0)
  let codeAddress := AccountAddress.ofUInt256 toAddress
  let gasCap := callGasCap codeAddress codeAddress value gas
    exec.accounts exec.gasAvailable exec.substate
  let childGas := if value = 0 then gasCap else gasCap + Gcallstipend
  { result :=
      { createdAccounts := exec.createdAccounts
        accounts := exec.accounts
        gasRemaining := .ofNat childGas
        substate := (exec.addAccessedAccount codeAddress).substate
        success := false
        output := .empty }
    pending :=
      { frame := current
        stack := stack
        callerAccounts := exec.accounts
        value := value
        inOffset := inOffset.toUInt64
        inSize := inSize.toUInt64
        outOffset := outOffset.toUInt64
        outSize := outSize.toUInt64 } }

/-- A soft-failed CALL pushes its failure flag `0`. -/
theorem callSuccessFlag_softFailCallRecord (fr : Frame) :
    callSuccessFlag (softFailCallRecord fr).result (softFailCallRecord fr).pending = 0 := by
  unfold callSuccessFlag
  simp only [softFailCallRecord]
  rfl

/-- The soft-fail CREATE2 record, rebuilt from the pre-step frame `current` and
the four decoded operands. `result.accounts = current.exec.accounts`
(world unchanged through the self lens — soft-fail does NOT bump the nonce) and
`result.success = false` (⇒ `createAddrOrZero = 0`), so `evmCreateEntry` maps it to
`(currentWorld, 0)`. When the cursor's stack does not present four operands (never the
case at a genuine CREATE2 soft-fail, whose `createArm` popped them) the operands
default to `0`, keeping the builder total. -/
def softFailCreateRecord (current : Frame) : CreateRecord :=
  let exec := current.exec
  let (stack, value, initOffset, initSize) :=
    match exec.stack.pop4 with
      | some (stack, value, initOffset, initSize, _salt) => (stack, value, initOffset, initSize)
      | none => ([], 0, 0, 0)
  { result :=
      { address := default
        createdAccounts := exec.createdAccounts
        accounts := exec.accounts
        gasRemaining := .ofNat (allButOneSixtyFourth exec.gasAvailable.toNat)
        substate := exec.toState.substate
        success := false
        output := .empty }
    pending :=
      { frame := current
        stack := stack
        callerAccounts := exec.accounts
        value := value
        initOffset := initOffset.toUInt64
        initSize := initSize.toUInt64
        initCodeSize := (exec.memory.readWithPadding initOffset.toNat initSize.toNat).size } }

/-- The soft-fail record pushes address `0`: its `result.success = false`, so the
`createAddrOrZero` guard's first disjunct fires. -/
theorem createAddrOrZero_softFailCreateRecord (fr : Frame) :
    createAddrOrZero (softFailCreateRecord fr).result (softFailCreateRecord fr).pending = 0 := by
  have hcond : ((softFailCreateRecord fr).result.success = false
      ∨ (softFailCreateRecord fr).pending.frame.exec.executionEnv.depth = 1024
      ∨ (softFailCreateRecord fr).pending.value
          > ((softFailCreateRecord fr).pending.callerAccounts.find?
              (softFailCreateRecord fr).pending.frame.exec.executionEnv.address
              |>.option 0 (·.balance))
      ∨ (softFailCreateRecord fr).pending.initCodeSize > 49152) := Or.inl rfl
  unfold createAddrOrZero
  exact if_pos hcond

def sloadWarmthOf (fr : Frame) : Nat :=
  match fr.exec.stack.head? with
    | some key =>
        Evm.sloadCost (fr.exec.substate.accessedStorageKeys.contains
          (fr.exec.executionEnv.address, key))
    | none => 0

def recordCall (pending : Pending) (result : FrameResult) (callAcc : List CallRecord) :
    List CallRecord :=
  match pending with
    | .call pd => callAcc ++ [{ result := result.toCallResult, pending := pd }]
    | .create _ => callAcc

def recordCreate (pending : Pending) (result : FrameResult) (createAcc : List CreateRecord) :
    List CreateRecord :=
  match pending with
    | .call _ => createAcc
    | .create pd => createAcc ++ [{ result := result.toCreateResult, pending := pd }]

def driveLog (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult)
    (gasAcc : List Word) (sloadAcc : List Nat) (callAcc : List CallRecord)
    (createAcc : List CreateRecord) :
    Except ExecutionException
      (FrameResult × List Word × List Nat × List CallRecord × List CreateRecord) :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok (result, gasAcc, sloadAcc, callAcc, createAcc)
            | pending :: rest =>
              match pending.resume result with
                | .ok parent =>
                  driveLog fuel rest (.inl parent) gasAcc sloadAcc
                    (if rest.isEmpty then recordCall pending result callAcc else callAcc)
                    (if rest.isEmpty then recordCreate pending result createAcc else createAcc)
                | .error e =>
                  driveLog fuel rest (.inr (endFrame pending.frame (.exception e)))
                    gasAcc sloadAcc
                    (if rest.isEmpty then recordCall pending result callAcc else callAcc)
                    (if rest.isEmpty then recordCreate pending result createAcc else createAcc)
        | .inl current =>
          match stepFrame current with
            | .next exec =>
              if isGasOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  (gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable]) sloadAcc callAcc createAcc
              else if isSloadOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  gasAcc (sloadAcc ++ [sloadWarmthOf current]) callAcc createAcc
              else if isCreate2Op current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  gasAcc sloadAcc callAcc (createAcc ++ [softFailCreateRecord current])
              else if isCallOp current && stack.isEmpty then
                driveLog fuel stack (.inl { current with exec := exec })
                  gasAcc sloadAcc (callAcc ++ [softFailCallRecord current]) createAcc
              else
                driveLog fuel stack (.inl { current with exec := exec }) gasAcc sloadAcc callAcc createAcc
            | .halted halt => driveLog fuel stack (.inr (endFrame current halt)) gasAcc sloadAcc callAcc createAcc
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => driveLog fuel (.call pending :: stack) (.inl child) gasAcc sloadAcc callAcc createAcc
                | .inr result => driveLog fuel (.call pending :: stack) (.inr (.call result)) gasAcc sloadAcc callAcc createAcc
            | .needsCreate params pending =>
              driveLog fuel (.create pending :: stack) (.inl (beginCreate params)) gasAcc sloadAcc callAcc createAcc

def runWithLog (params : CallParams) (fuel : ℕ) : Option RunLog :=
  match beginCall params with
    | .inr _ => none
    | .inl frame =>
      match driveLog fuel [] (.inl frame) [] [] [] [] with
        | .ok (r, gas, sloads, calls, creates) =>
            some { observable := r, gas := gas, sloads := sloads, calls := calls,
                   creates := creates }
        | .error _ => none

/-- Restarting the recorder at a top-level boundary frame reproduces the final observable
and the unconsumed event suffixes. The empty pending stack makes the boundary top-level;
nested CALL/CREATE execution remains hidden by the recorder's stack gate. The prefix
witnesses ensure that every replayed suffix belongs to the original log. -/
structure RecorderCoupled (log : RunLog) (fr : Frame)
    (gasSuffix : List Word) (sloadSuffix : List Nat) (callSuffix : List CallRecord)
    (createSuffix : List CreateRecord) : Prop where
  /-- A deterministic replay from the boundary produces exactly the remaining streams. -/
  restart : ∃ fuel', driveLog fuel' [] (.inl fr) [] [] [] []
      = .ok (log.observable, gasSuffix, sloadSuffix, callSuffix, createSuffix)
  /-- The remaining gas events form a suffix of the recorded gas stream. -/
  gasPrefix : ∃ pre, log.gas = pre ++ gasSuffix
  /-- The remaining SLOAD events form a suffix of the recorded SLOAD stream. -/
  sloadPrefix : ∃ pre, log.sloads = pre ++ sloadSuffix
  /-- The remaining CALL events form a suffix of the recorded CALL stream. -/
  callPrefix : ∃ pre, log.calls = pre ++ callSuffix
  /-- The remaining CREATE events form a suffix of the recorded CREATE stream. -/
  createPrefix : ∃ pre, log.creates = pre ++ createSuffix

def callsCodeOk : ℕ → Frame → Bool
  | 0, _ => false
  | fuel+1, fr =>
    match stepFrame fr with
    | .next exec => callsCodeOk fuel { fr with exec := exec }
    | .halted _ => true
    | .needsCall cp pending =>
      (match cp.codeSource with
        | .Precompiled _ => false
        | .Code _ => true)
      && (match beginCall cp with
          | .inl child =>
            match drive (seedFuel cp.gas) [] (running child) with
            | .ok childRes => callsCodeOk fuel (resumeAfterCall childRes.toCallResult pending)
            | .error _ => true
          | .inr _ => true)
    | .needsCreate cp pending =>
      match drive (seedFuel cp.gas) [] (running (beginCreate cp)) with
      | .ok childRes =>
        match resumeAfterCreate childRes.toCreateResult pending with
        | .ok resumeFr => callsCodeOk fuel resumeFr
        | .error _ => false
      | .error _ => true

def realisedGas (log : RunLog) : GasOracle := log.gas

def realisedSload (log : RunLog) : List Nat := log.sloads

def callStreamOf (calls : List CallRecord) (self : AccountAddress) : CallStream :=
  calls.map (fun rec => evmCallEntry rec.result rec.pending self)

def realisedCall (log : RunLog) (self : AccountAddress) : CallStream :=
  callStreamOf log.calls self

def createStreamOf (creates : List CreateRecord) (self : AccountAddress) : CreateStream :=
  creates.map (fun rec => evmCreateEntry rec.result rec.pending self)

def realisedCreate (log : RunLog) (self : AccountAddress) : CreateStream :=
  createStreamOf log.creates self

def resultStorageAt (fr : FrameResult) (addr : AccountAddress) (key : Word) : Word :=
  fr.toCallResult.accounts.find? addr |>.option 0 (·.lookupStorage key)

def observe (self : AccountAddress) (fr : FrameResult) : Observable :=
  { world  := fun key => resultStorageAt fr self key
    result := let out := fr.toCallResult.output
              if out.isEmpty then .stopped else .returned (uInt256OfByteArray out) }

theorem observe_result (self : AccountAddress) (fr : FrameResult) :
    (observe self fr).result =
      (if fr.toCallResult.output.isEmpty then .stopped
        else .returned (uInt256OfByteArray fr.toCallResult.output)) := rfl

end BytecodeLayer.Exec.Recorder
