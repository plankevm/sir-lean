import LirLean.Spec.CallEntry

namespace Lir.V2

open Evm
open BytecodeLayer
open BytecodeLayer.System
open BytecodeLayer.Interpreter
open BytecodeLayer.Hoare

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

def isGasOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 == .Smsf .GAS

def isSloadOp (fr : Frame) : Bool :=
  (decode fr.exec.executionEnv.code fr.exec.pc |>.getD (Operation.STOP, .none)).1 == .Smsf .SLOAD

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

def realisedGas (log : RunLog) : GasOracle := log.gas

def realisedSload (log : RunLog) : List Nat := log.sloads

def callStreamOf (calls : List CallRecord) (self : AccountAddress) : CallStream :=
  calls.map (fun rec => evmV2CallEntry rec.result rec.pending self)

def realisedCall (log : RunLog) (self : AccountAddress) : CallStream :=
  callStreamOf log.calls self

def createStreamOf (creates : List CreateRecord) (self : AccountAddress) : CreateStream :=
  creates.map (fun rec => evmV2CreateEntry rec.result rec.pending self)

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

end Lir.V2
