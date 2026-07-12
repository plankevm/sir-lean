import Evm.Exception
import Evm.Instr
import Evm.Operations
import Evm.State.ExecutionEnv
import Evm.UInt256
import Evm.Wheels

namespace Evm

def pushArgWidth : Operation → UInt8
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  | _ => 0

def nextInstrPos (pc : UInt32) (instr : Operation) := pc + 1 + (pushArgWidth instr).toUInt32

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : UInt32) :
  Option (Operation × Option (UInt256 × UInt8)) := do
  let byte ← arr.get? pc.toNat
  let instr := Evm.parseInstr byte
  let argWidth := pushArgWidth instr
  let immediate :=
    if argWidth > 0
    then
      let pc' := pc.toNat + 1
      .some (Evm.uInt256OfByteArray (arr.extract pc' (pc' + argWidth.toNat)), argWidth)
    else .none
  .some (instr, immediate)

/--
Step from instruction-boundary index `i` to the start of the next instruction:
JUMPDEST / ordinary opcodes advance by one byte, a `PUSHn` skips its `n`
immediate bytes as well. Phrased on `Nat` so it is monotone without `UInt32`
wraparound; `nextInstrPos` is the `UInt32` mirror used by the executor.
-/
def nextInstrPosNat (i : Nat) (instr : Operation) : Nat :=
  i + 1 + (pushArgWidth instr).toNat

theorem nextInstrPosNat_gt (i : Nat) (instr : Operation) : i < nextInstrPosNat i instr := by
  unfold nextInstrPosNat; omega

/-- `ByteArray.get?` returns `some` exactly when the index is in bounds; the
forward direction is all the termination/characterization proofs need. -/
theorem lt_size_of_get?_isSome {c : ByteArray} {i : Nat} (h : (c.get? i).isSome) :
    i < c.size := by
  unfold ByteArray.get? at h
  by_cases hlt : i < c.size
  · exact hlt
  · simp [hlt] at h

-- `h` is consumed by `decreasing_by` (to bound `i < c.size`), which the
-- unused-variable linter does not see, so silence it just for this def.
set_option linter.unusedVariables false in
/--
Total, kernel-reducible replacement for the original `partial def`. Scans the
code from boundary index `i`, recording each `JUMPDEST` offset. Each recursive
call strictly increases `i` (`nextInstrPosNat_gt`) so the metric `c.size - i`
decreases; the recursion stops once `i` leaves the array's bounds.

Behaviour matches the original on every well-formed program: the index walks
instruction boundaries strictly upward and the scan halts at `c.size`. (The
original `UInt32` recursion only differed for the unreachable case of a code
array larger than `2^32` bytes, where its index could wrap.)
-/
def validJumpDestsAuxNat (c : ByteArray) (i : Nat) (result : Array UInt32) : Array UInt32 :=
  match h : c.get? i with
    | none => result
    | some byte =>
      let cᵢ := Evm.parseInstr byte
      validJumpDestsAuxNat c (nextInstrPosNat i cᵢ)
        (if cᵢ = .JUMPDEST then result.push i.toUInt32 else result)
  termination_by c.size - i
  decreasing_by
    have hlt : i < c.size := lt_size_of_get?_isSome (by rw [h]; exact Option.isSome_some)
    simp only [nextInstrPosNat]
    omega

/-- Unfolding equation for `validJumpDestsAuxNat` (kernel-provable, unlike the
original `partial def`). -/
theorem validJumpDestsAuxNat_eq (c : ByteArray) (i : Nat) (result : Array UInt32) :
    validJumpDestsAuxNat c i result =
      match c.get? i with
        | none => result
        | some byte =>
          let cᵢ := Evm.parseInstr byte
          validJumpDestsAuxNat c (nextInstrPosNat i cᵢ)
            (if cᵢ = .JUMPDEST then result.push i.toUInt32 else result) := by
  conv_lhs => rw [validJumpDestsAuxNat]
  cases c.get? i <;> rfl

def validJumpDests (c : ByteArray) (i : UInt32) : Array UInt32 :=
  validJumpDestsAuxNat c i.toNat #[]

/-! ### Characterization of `validJumpDests`

The scan only ever *adds* offsets, so whatever is already accumulated survives
(`mem_validJumpDestsAuxNat_of_mem`), and a `JUMPDEST` sitting at the current
boundary records itself (`self_mem_validJumpDestsAuxNat`). An instruction
boundary reachable from the start is captured by `ReachesBoundary`; together
these give: a `JUMPDEST` at a reachable boundary is a valid jump destination
(`mem_validJumpDests_of_reachable_jumpdest`), which is exactly what a lowered
program's branch needs for its block-start offsets. -/

/-- The accumulator only grows: anything already recorded stays in the result. -/
theorem mem_validJumpDestsAuxNat_of_mem (c : ByteArray) (i : Nat) (result : Array UInt32)
    {x : UInt32} (hx : x ∈ result) : x ∈ validJumpDestsAuxNat c i result := by
  rw [validJumpDestsAuxNat_eq]
  cases h : c.get? i with
  | none => simpa using hx
  | some byte =>
    simp only
    split
    · exact mem_validJumpDestsAuxNat_of_mem c _ _ (Array.mem_push_of_mem _ hx)
    · exact mem_validJumpDestsAuxNat_of_mem c _ _ hx
  termination_by c.size - i
  decreasing_by
    all_goals
      have hlt : i < c.size := lt_size_of_get?_isSome (by rw [h]; exact Option.isSome_some)
      simp only [nextInstrPosNat]; omega

/-- A `JUMPDEST` at the boundary the scan currently sits on records itself. -/
theorem self_mem_validJumpDestsAuxNat (c : ByteArray) (i : Nat) (result : Array UInt32)
    {byte : UInt8} (hget : c.get? i = some byte) (hj : Evm.parseInstr byte = .JUMPDEST) :
    i.toUInt32 ∈ validJumpDestsAuxNat c i result := by
  rw [validJumpDestsAuxNat_eq, hget]
  simp only [hj, if_true]
  exact mem_validJumpDestsAuxNat_of_mem c _ _ Array.mem_push_self

/-- `ReachesBoundary c start i`: walking the instruction stream from `start`,
each step landing on the next instruction's first byte, eventually lands exactly
on `i`. These are the offsets the scan from `start` actually visits. -/
inductive ReachesBoundary (c : ByteArray) : Nat → Nat → Prop where
  | refl (i : Nat) : ReachesBoundary c i i
  | step {start i : Nat} {byte : UInt8}
      (hget : c.get? start = some byte)
      (rest : ReachesBoundary c (nextInstrPosNat start (Evm.parseInstr byte)) i) :
      ReachesBoundary c start i

/-- The scan from `start` records every `JUMPDEST` sitting on a boundary
reachable from `start`. -/
theorem mem_validJumpDestsAuxNat_of_reachable (c : ByteArray) {start i : Nat}
    (result : Array UInt32) (hreach : ReachesBoundary c start i)
    {byte : UInt8} (hget : c.get? i = some byte) (hj : Evm.parseInstr byte = .JUMPDEST) :
    i.toUInt32 ∈ validJumpDestsAuxNat c start result := by
  induction hreach generalizing result with
  | refl j => exact self_mem_validJumpDestsAuxNat c j result hget hj
  | step hget' _ ih =>
    rw [validJumpDestsAuxNat_eq, hget']
    simp only
    split <;> exact ih _ hget

/-- **The destination a lowered branch needs.** A `JUMPDEST` byte at an offset
`i` reachable from the program start is a valid jump destination. -/
theorem mem_validJumpDests_of_reachable_jumpdest (c : ByteArray) {i : Nat}
    (hreach : ReachesBoundary c 0 i)
    {byte : UInt8} (hget : c.get? i = some byte) (hj : Evm.parseInstr byte = .JUMPDEST) :
    i.toUInt32 ∈ validJumpDests c 0 :=
  mem_validJumpDestsAuxNat_of_reachable c #[] hreach hget hj

/-- Looking an element up by equality in an array that contains it succeeds and
returns that very element. Bridges a membership fact (what the characterization
lemmas give) to the `find?`-based lookup `Frame.get_dest` performs. -/
theorem find?_beq_eq_some_of_mem {d : UInt32} {arr : Array UInt32} (hmem : d ∈ arr) :
    arr.find? (· == d) = some d := by
  have hsome : (arr.find? (· == d)).isSome := by
    rw [Array.find?_isSome]; exact ⟨d, hmem, beq_self_eq_true d⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsome
  have hpy : (y == d) = true := Array.find?_some (p := (· == d)) hy
  rw [hy, eq_of_beq hpy]

end Evm
