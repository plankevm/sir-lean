import Evm.UInt256
import Evm.Machine.ExecutionState
import Evm.Semantics.Params

namespace Evm

/--
The revert target of a running frame: the world state captured when the frame
was entered. On exceptional halt (and partially on revert / failed code
deposit) the frame's result is rebuilt from this snapshot. The maps are
persistent, so a checkpoint is a set of shared references, not a copy.
-/
structure Checkpoint where
  createdAccounts : Batteries.RBSet AccountAddress compare
  accounts        : AccountMap
  substate        : Substate

/--
What kind of execution a frame is, plus the data its `endCall`/`endCreate`
needs once it halts.
-/
inductive FrameKind where
  | call   (checkpoint : Checkpoint)
  | create (address : AccountAddress) (checkpoint : Checkpoint)

structure Frame where
  kind       : FrameKind
  validJumps : Array UInt32
  exec       : ExecutionState

def Frame.get_dest (f : Frame) (dest : UInt256) : Option UInt32 := do
  let d ← dest.toUInt32?
  f.validJumps.find? (· == d)

inductive FrameHalt where
  | success (exec : ExecutionState) (output : ByteArray)
  | revert (gasRemaining : UInt64) (output : ByteArray)
  | exception (e : ExecutionException)

inductive FrameResult where
  | call   (result : CallResult)
  | create (result : CreateResult)

/--
A parent frame suspended on a CALL-family instruction: everything needed to
resume it once the child call's result is known. `stack` is the operand stack
with the instruction's arguments already popped (the success flag is pushed
onto it); `callerAccounts` is the account map from before the call.
-/
structure PendingCall where
  frame          : Frame
  stack          : Stack UInt256
  callerAccounts : AccountMap
  value          : UInt256
  inOffset       : UInt64
  inSize         : UInt64
  outOffset      : UInt64
  outSize        : UInt64

/--
A parent frame suspended on CREATE/CREATE2. `initCodeSize` feeds the
EIP-3860 component of the success-flag re-check.
-/
structure PendingCreate where
  frame          : Frame
  stack          : Stack UInt256
  callerAccounts : AccountMap
  value          : UInt256
  initOffset     : UInt64
  initSize       : UInt64
  initCodeSize   : ℕ

inductive Pending where
  | call   (pending : PendingCall)
  | create (pending : PendingCreate)

inductive Signal where
  | next (exec : ExecutionState)
  | halted (halt : FrameHalt)
  | needsCall (params : CallParams) (pending : PendingCall)
  | needsCreate (params : CreateParams) (pending : PendingCreate)

def FrameResult.toCallResult : FrameResult → CallResult
  | .call r   => r
  | .create r => r.toCallResult

def FrameResult.toCreateResult : FrameResult → CreateResult
  | .call r   => { toCallResult := r, address := 0 }
  | .create r => r

end Evm
