import Evm.Semantics.Call
import Evm.Semantics.Create
import Evm.Semantics.Dispatch
import Evm.Semantics.Frame

namespace Evm

def endFrame (fr : Frame) (halt : FrameHalt) : FrameResult :=
  match fr.kind with
    | .call checkpoint => .call (endCall checkpoint halt)
    | .create address checkpoint => .create (endCreate address checkpoint halt)

def Pending.resume (p : Pending) (result : FrameResult) : Except ExecutionException Frame :=
  match p with
    | .call pd => .ok (resumeAfterCall result.toCallResult pd)
    | .create pd => resumeAfterCreate result.toCreateResult pd

def Pending.frame : Pending → Frame
  | .call pd => pd.frame
  | .create pd => pd.frame

/--
The interpreter driver — the only recursion in the EVM semantics.

The machine is either executing the `current` frame (`.inl`) or delivering a
finished child's result to the innermost suspended frame (`.inr`); `stack`
holds the suspended ancestors. One iteration is one instruction, one
call/create descent, or one result delivery.

`fuel` is an implementation detail, not a semantic bound: it is seeded from
the gas limit (see `seedFuel`) and cannot run out for gas-respecting
executions, because every non-halting instruction costs at least 1 gas and
each descent/delivery pair is matched to a call charge of at least 100 gas.
`.OutOfFuel` therefore signals a broken gas table, not a program behavior.
-/
def drive (fuel : ℕ) (stack : List Pending) (state : Frame ⊕ FrameResult) :
    Except ExecutionException FrameResult :=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 =>
      match state with
        | .inr result =>
          match stack with
            | [] => .ok result
            | pending :: rest =>
              match pending.resume result with
                | .ok parent => drive fuel rest (.inl parent)
                | .error e =>
                  -- The resume itself faulted: the parent frame halts
                  -- exceptionally and its own result propagates up.
                  drive fuel rest (.inr (endFrame pending.frame (.exception e)))
        | .inl current =>
          match stepFrame current with
            | .next exec => drive fuel stack (.inl { current with exec := exec })
            | .halted halt => drive fuel stack (.inr (endFrame current halt))
            | .needsCall params pending =>
              match beginCall params with
                | .inl child => drive fuel (.call pending :: stack) (.inl child)
                | .inr result => drive fuel (.call pending :: stack) (.inr (.call result))
            | .needsCreate params pending =>
              -- `beginCreate` is total (its sole former `.error` path, a dead
              -- address-derivation guard, is removed): a CREATE always begins a
              -- child, so the descent is unconditional.
              drive fuel (.create pending :: stack) (.inl (beginCreate params))

/--
The driver's step budget for a top-level execution with gas limit `gas` —
generous (see `drive`): instructions cost ≥ 1 gas each and descents ≥ 100, so
`2 * gas` already overshoots; the constant covers the zero-gas edge cases.
-/
def seedFuel (gas : UInt64) : ℕ := 2 * gas.toNat + 4096

def messageCall (params : CallParams) : Except ExecutionException CallResult :=
  match beginCall params with
    | .inr result => .ok result
    | .inl frame => FrameResult.toCallResult <$> drive (seedFuel params.gas) [] (.inl frame)

def createContract (params : CreateParams) : Except ExecutionException CreateResult :=
  FrameResult.toCreateResult <$> drive (seedFuel params.gas) [] (.inl (beginCreate params))

end Evm
