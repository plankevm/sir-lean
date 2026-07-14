import BytecodeLayer.Exec.SegmentedEval

/-!
# Checked kernel-evaluable step twin

The kernel cannot directly reduce padded byte-window operations through opaque,
platform-dependent `USize` normalization. This module provides a checked twin:

* the byte primitives get sanitized twins (`readWithPaddingK`, `writeK`,
  `toByteArrayK`, …) computing the padding lengths in `ℕ` (`Array.replicate` instead of
  `zeroes ∘ USize.ofNat`), with propositional equivalence lemmas — the `USize` bridging
  (`zeroes_cast`, `zeroes_cast_sub`) is discharged once via `System.Platform.numBits_eq`;
* the op layer gets an `Option`-valued checked twin (`smsfOpChk`/`systemOpChk`/
  `dispatchChk`/`stepFrameChk`) that REPLACES exactly the poisoned arms (MLOAD, MSTORE,
  CALL's calldata window) under decidable `< 2^32` bound checks, DELEGATES every clean
  arm verbatim (delegation is soundness-free: `some (original)`), and fails CLOSED
  (`none`) on the off-path memory ops (KECCAK256, copies, LOGs, RETURN's twin is
  delegated — its padded output is only ever carried lazily, never forced);
* the evaluator layer mirrors `nextLog` and `nextCC` over the checked step; every
  successful checked verdict is proved equal to the original evaluator's verdict.
-/

namespace BytecodeLayer.Exec.Recorder

open Evm
open BytecodeLayer
open BytecodeLayer.Interpreter

/-! ## §1 — the `USize`/`zeroes` bridge (the propositional wall-crossing) -/

/-- Both platforms give `USize` at least 32 bits. -/
theorem two_pow_32_le_usize_size : 2 ^ 32 ≤ USize.size := by
  rcases System.Platform.numBits_eq with h | h <;>
    simp [USize.size, h]

/-- `zeroes` at a `Nat`-cast `USize` under the 32-bit bound is a literal replicate. -/
theorem zeroes_cast {n : ℕ} (h : n < 2 ^ 32) :
    ffi.ByteArray.zeroes ⟨(n : BitVec System.Platform.numBits)⟩ =
      ⟨Array.replicate n 0⟩ := by
  show ffi.ByteArray.zeroes (USize.ofNat n) = _
  unfold ffi.ByteArray.zeroes
  have : (USize.ofNat n).toNat = n % 2 ^ System.Platform.numBits := rfl
  rw [this, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h two_pow_32_le_usize_size)]

/-- `zeroes` at a `Nat`-cast `USize` DIFFERENCE (the padded-read shape) under the
32-bit bound and the truncation-freeness side condition. -/
theorem zeroes_cast_sub {a b : ℕ} (hb : b ≤ a) (ha : a < 2 ^ 32) :
    ffi.ByteArray.zeroes
        ⟨(a : BitVec System.Platform.numBits) - (b : BitVec System.Platform.numBits)⟩ =
      ⟨Array.replicate (a - b) 0⟩ := by
  show ffi.ByteArray.zeroes (USize.ofNat a - USize.ofNat b) = _
  unfold ffi.ByteArray.zeroes
  have hblt : b < 2 ^ 32 := Nat.lt_of_le_of_lt hb ha
  have hsize : ∀ {n : ℕ}, n < 2 ^ 32 → (USize.ofNat n).toNat = n := fun h' => by
    have hmod : ∀ (m : ℕ), (USize.ofNat m).toNat = m % 2 ^ System.Platform.numBits :=
      fun _ => rfl
    rw [hmod, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h' two_pow_32_le_usize_size)]
  have hle : USize.ofNat b ≤ USize.ofNat a := by
    rw [USize.le_iff_toNat_le, hsize hblt, hsize ha]; exact hb
  rw [USize.toNat_sub_of_le _ _ hle, hsize hblt, hsize ha]

/-- The `toByteArray` left-pad shape: an `OfNat` bit-vector literal minus a cast. -/
theorem zeroes_ofNat32_sub {b : ℕ} (hb : b ≤ 32) :
    ffi.ByteArray.zeroes
        ⟨(32 : BitVec System.Platform.numBits) - (b : BitVec System.Platform.numBits)⟩ =
      ⟨Array.replicate (32 - b) 0⟩ :=
  zeroes_cast_sub (a := 32) hb (by norm_num)

/-! ## §2 — the padded-read/write twins -/

/-- The unpadded read never exceeds the requested length. -/
theorem readWithoutPadding_size_le (source : ByteArray) (addr len : ℕ) :
    (source.readWithoutPadding addr len).size ≤ len := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · simp only [ByteArray.size_extract]
    omega

/-- Sanitized `readWithPadding`: `ℕ`-computed padding, no `USize`. Total (the panic
branch is subsumed by the equivalence lemma's `< 2 ^ 32` bound). -/
def readWithPaddingK (source : ByteArray) (addr len : ℕ) : ByteArray :=
  let read := source.readWithoutPadding addr len
  read ++ ⟨Array.replicate (len - read.size) 0⟩

theorem readWithPadding_eq_K (source : ByteArray) (addr len : ℕ) (h : len < 2 ^ 32) :
    source.readWithPadding addr len = readWithPaddingK source addr len := by
  unfold ByteArray.readWithPadding readWithPaddingK
  rw [if_neg (by omega)]
  dsimp only []
  rw [zeroes_cast_sub (readWithoutPadding_size_le source addr len) h]

/-- Sanitized `ByteArray.write`: the three `zeroes` sites replaced by replicates. -/
def writeK (source : ByteArray) (sourceAddr : ℕ) (dest : ByteArray) (destAddr len : ℕ) :
    ByteArray :=
  if len = 0 then dest else
    if sourceAddr ≥ source.size then
      let len := min len (dest.size - destAddr)
      let destAddr := min destAddr dest.size
      (⟨Array.replicate len 0⟩ : ByteArray).copySlice 0 dest destAddr len
    else
      let practicalLen := min len (source.size - sourceAddr)
      let endPaddingAddr := min dest.size (destAddr + len)
      let sourcePaddingLength : ℕ := endPaddingAddr - (destAddr + practicalLen)
      let sourcePadding : ByteArray := ⟨Array.replicate sourcePaddingLength 0⟩
      let destPaddingLength : ℕ := destAddr - dest.size
      let destPadding : ByteArray := ⟨Array.replicate destPaddingLength 0⟩
      (source ++ sourcePadding).copySlice sourceAddr
        (dest ++ destPadding)
        destAddr
        (practicalLen + sourcePaddingLength)

theorem write_eq_K (source : ByteArray) (sourceAddr : ℕ) (dest : ByteArray)
    (destAddr len : ℕ) (hlen : len < 2 ^ 32) (hdest : dest.size < 2 ^ 32)
    (haddr : destAddr < 2 ^ 32) :
    source.write sourceAddr dest destAddr len = writeK source sourceAddr dest destAddr len := by
  unfold ByteArray.write writeK
  split
  · rfl
  · split
    · dsimp only []
      rw [zeroes_cast (by omega : min len (dest.size - destAddr) < 2 ^ 32)]
    · dsimp only []
      rw [zeroes_cast (by omega : destAddr - dest.size < 2 ^ 32),
        zeroes_cast (show min dest.size (destAddr + len) -
            (destAddr + min len (source.size - sourceAddr)) < 2 ^ 32 by omega)]

/-! ## §3 — the machine-level twins -/

/-- Sanitized `writeBytes`. -/
def writeBytesK (source : ByteArray) (sourceAddr : ℕ) (self : MachineState)
    (destAddr len : ℕ) : MachineState :=
  { self with memory := writeK source sourceAddr self.memory destAddr len }

theorem writeBytes_eq_K (source : ByteArray) (sourceAddr : ℕ) (self : MachineState)
    (destAddr len : ℕ) (hlen : len < 2 ^ 32) (hdest : self.memory.size < 2 ^ 32)
    (haddr : destAddr < 2 ^ 32) :
    writeBytes source sourceAddr self destAddr len = writeBytesK source sourceAddr self destAddr len := by
  unfold writeBytes writeBytesK
  rw [write_eq_K source sourceAddr self.memory destAddr len hlen hdest haddr]

/-- Sanitized `UInt256.toByteArray` (its left-pad is a `zeroes`). -/
def toByteArrayK (val : UInt256) : ByteArray :=
  let b := BE val.toNat
  (⟨Array.replicate (32 - b.size) 0⟩ : ByteArray) ++ b

theorem toByteArray_eq_K (val : UInt256) : val.toByteArray = toByteArrayK val := by
  unfold UInt256.toByteArray toByteArrayK
  dsimp only []
  have hb : (BE val.toNat).size ≤ 32 := by
    apply BE_size_le
    have hlt : val.toNat < 2 ^ 256 := val.toBitVec.isLt
    have : (256 : ℕ) ^ 32 = 2 ^ 256 := by norm_num
    omega
  rw [zeroes_ofNat32_sub hb]

/-- Sanitized `MachineState.writeWord`. -/
def writeWordK (self : MachineState) (addr val : UInt256) : MachineState :=
  writeBytesK (toByteArrayK val) 0 self addr.toNat 32

theorem writeWord_eq_K (self : MachineState) (addr val : UInt256)
    (hdest : self.memory.size < 2 ^ 32) (haddr : addr.toNat < 2 ^ 32) :
    self.writeWord addr val = writeWordK self addr val := by
  unfold MachineState.writeWord writeWordK
  rw [toByteArray_eq_K, writeBytes_eq_K _ _ _ _ _ (by omega) hdest haddr]

/-- Sanitized `MachineState.lookupMemory` — UNCONDITIONAL twin (the read length is
the fixed word width `32 < 2 ^ 32`). -/
def lookupMemoryK (self : MachineState) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr.toNat ≥ self.activeWords.toNat * 32 then 0 else
    let bytes := readWithPaddingK self.memory addr.toNat 32
    let val := fromByteArrayBigEndian bytes
    .ofNat val

theorem lookupMemory_eq_K (self : MachineState) (addr : UInt256) :
    self.lookupMemory addr = lookupMemoryK self addr := by
  unfold MachineState.lookupMemory lookupMemoryK
  dsimp only []
  rw [readWithPadding_eq_K self.memory addr.toNat 32 (by omega)]

/-- Sanitized `MachineState.mload` — unconditional twin. -/
def mloadK (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  let val := lookupMemoryK self spos
  let self :=
    { self with
      activeWords := MachineState.M self.activeWords spos.toUInt64 32 }
  (val, self)

theorem mload_eq_K (self : MachineState) (spos : UInt256) :
    self.mload spos = mloadK self spos := by
  unfold MachineState.mload mloadK
  rw [lookupMemory_eq_K]

/-- Sanitized `MachineState.mstore` (conditional on the write bounds). -/
def mstoreK (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := writeWordK self spos sval
  { self with
    activeWords := MachineState.M self.activeWords spos.toUInt64 32 }

theorem mstore_eq_K (self : MachineState) (spos sval : UInt256)
    (hdest : self.memory.size < 2 ^ 32) (haddr : spos.toNat < 2 ^ 32) :
    self.mstore spos sval = mstoreK self spos sval := by
  unfold MachineState.mstore mstoreK
  rw [writeWord_eq_K self spos sval hdest haddr]

/-- The checked (Option) mstore: the write bounds as decidable runtime checks. -/
def mstoreChk (self : MachineState) (spos sval : UInt256) : Option MachineState :=
  if self.memory.size < 2 ^ 32 ∧ spos.toNat < 2 ^ 32 then some (mstoreK self spos sval)
  else none

theorem mstoreChk_sound {self : MachineState} {spos sval : UInt256} {m' : MachineState}
    (h : mstoreChk self spos sval = some m') : self.mstore spos sval = m' := by
  unfold mstoreChk at h
  split at h
  · injection h with h
    rw [← h]
    exact mstore_eq_K self spos sval (by omega) (by omega)
  · cases h

/-! ## §4 — the checked op arms -/

/-- Checked `smsfOp`: MLOAD/MSTORE arms rebuilt over the sanitized memory twins;
MSTORE8/MCOPY fail closed; every other arm delegates verbatim. -/
def smsfOpChk (op : Operation.SmsfOp) (fr : Frame) (exec : ExecutionState) : Option Step :=
  match op with
    | .MLOAD => some (do
        let (stack, addr) ← exec.stack.pop
        let exec ← chargeMemExpansion exec addr 32
        let exec ← charge GasConstants.Gverylow exec
        let (v, machine') := mloadK exec.toMachineState addr
        continueWith <| ExecutionState.replaceStackAndIncrPC
          { exec with toMachineState := machine' } (stack.push v))
    | .MSTORE =>
      match exec.stack.pop2 with
        | none => some (.error .StackUnderflow)
        | some (stack, addr, val) =>
          match chargeMemExpansion exec addr 32 with
            | .error e => some (.error e)
            | .ok exec₁ =>
              match charge GasConstants.Gverylow exec₁ with
                | .error e => some (.error e)
                | .ok exec₂ =>
                  match mstoreChk exec₂.toMachineState addr val with
                    | none => none
                    | some machine' =>
                      some (continueWith <| ExecutionState.replaceStackAndIncrPC
                        { exec₂ with toMachineState := machine' } stack)
    | .MSTORE8 => none
    | .MCOPY => none
    | _ => some (smsfOp op fr exec)

/-- The `Option`-lift/`Except`-bind reductions the arm-soundness proofs normalize with
(the engine's `do` blocks lift `Stack.pop*` through `MonadLift Option (Except _)`). -/
private theorem liftOpt_some {α : Type} (v : α) :
    (liftM (some v) : Except ExecutionException α) = .ok v := rfl

private theorem liftOpt_none {α : Type} :
    (liftM (none : Option α) : Except ExecutionException α) = .error .StackUnderflow := rfl

private theorem ebind_ok {α β : Type} (a : α) (f : α → Except ExecutionException β) :
    (Except.ok a : Except ExecutionException α) >>= f = f a := rfl

private theorem ebind_err {α β : Type} (e : ExecutionException)
    (f : α → Except ExecutionException β) :
    (Except.error e : Except ExecutionException α) >>= f = .error e := rfl

theorem smsfOpChk_sound {op : Operation.SmsfOp} {fr : Frame} {exec : ExecutionState}
    {s : Step} (h : smsfOpChk op fr exec = some s) : smsfOp op fr exec = s := by
  cases op
  case MLOAD =>
    injection h with h
    rw [← h]
    unfold smsfOp
    simp only [mload_eq_K]
  case MSTORE =>
    unfold smsfOpChk at h
    unfold smsfOp
    dsimp only [] at h ⊢
    cases hp : exec.stack.pop2 with
    | none =>
      rw [hp] at h
      injection h
    | some v =>
      obtain ⟨stack, addr, val⟩ := v
      rw [hp] at h
      simp only [liftOpt_some, ebind_ok] at h ⊢
      cases hc1 : chargeMemExpansion exec addr 32 with
      | error e =>
        rw [hc1] at h
        injection h
      | ok exec₁ =>
        rw [hc1] at h
        simp only [ebind_ok] at h ⊢
        cases hc2 : charge GasConstants.Gverylow exec₁ with
        | error e =>
          rw [hc2] at h
          injection h
        | ok exec₂ =>
          rw [hc2] at h
          simp only [ebind_ok] at h ⊢
          cases hms : mstoreChk exec₂.toMachineState addr val with
          | none => rw [hms] at h; cases h
          | some machine' =>
            rw [hms] at h
            injection h with h
            rw [← h, ← mstoreChk_sound hms]
  case MSTORE8 => cases h
  case MCOPY => cases h
  all_goals exact Option.some.inj h

/-! ## §5 — the checked CALL arm and system/dispatch/step twins -/

/-- Checked `callArm`: the calldata window (`readWithPadding`) sanitized under an
`inSize < 2 ^ 32` runtime check; every other computation verbatim. -/
def callArmChk (fr : Frame) (exec : ExecutionState) (stack : Stack UInt256)
    (gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize :
      UInt256)
    (permission : Bool) : Option Step :=
  if inSize.toNat < 2 ^ 32 then
    match memoryExpansionWords? exec.activeWords inOffset inSize >>=
        (memoryExpansionWords? · outOffset outSize) with
      | none => some (.error .OutOfGas)
      | some words' =>
        match charge (Cₘ words' - Cₘ exec.activeWords) exec with
          | .error e => some (.error e)
          | .ok exec =>
            let codeAddress : AccountAddress := AccountAddress.ofUInt256 codeAddress
            let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
            let caller : AccountAddress := AccountAddress.ofUInt256 caller
            let self := exec.executionEnv.address
            let accounts := exec.accounts
            let depth := exec.executionEnv.depth
            let extraCost := callExtraCost codeAddress recipient value accounts exec.substate
            let gasCap := callGasCap codeAddress recipient value gas accounts exec.gasAvailable
              exec.substate
            let childGas := if value = 0 then gasCap else gasCap + GasConstants.Gcallstipend
            match charge (gasCap + extraCost) exec with
              | .error e => some (.error e)
              | .ok exec =>
                let inputData := readWithPaddingK exec.memory inOffset.toNat inSize.toNat
                let substate' := exec.addAccessedAccount codeAddress |>.substate
                let pending : PendingCall :=
                  { frame := { fr with exec := exec }
                    stack := stack
                    callerAccounts := accounts
                    value := value
                    inOffset := inOffset.toUInt64
                    inSize := inSize.toUInt64
                    outOffset := outOffset.toUInt64
                    outSize := outSize.toUInt64 }
                if value ≤ (accounts.find? self |>.option 0 (·.balance)) ∧ depth < 1024 then
                  some (.ok <| .needsCall
                    { blobVersionedHashes := exec.executionEnv.blobVersionedHashes
                      createdAccounts := exec.createdAccounts
                      genesisBlockHeader := exec.genesisBlockHeader
                      blocks := exec.blocks
                      accounts := accounts
                      originalAccounts := exec.originalAccounts
                      substate := substate'
                      caller := caller
                      origin := exec.executionEnv.origin
                      recipient := recipient
                      codeSource := toExecute accounts codeAddress
                      gas := .ofNat childGas
                      gasPrice := .ofNat exec.executionEnv.gasPrice
                      value := value
                      apparentValue := apparentValue
                      calldata := inputData
                      depth := depth + 1
                      blockHeader := exec.executionEnv.blockHeader
                      chainId := exec.executionEnv.chainId
                      canModifyState := permission }
                    pending)
                else
                  let failed : CallResult :=
                    { createdAccounts := exec.createdAccounts
                      accounts := accounts
                      gasRemaining := .ofNat childGas
                      substate := substate'
                      success := false
                      output := .empty }
                  some (.ok <| .next (resumeAfterCall failed pending).exec)
  else none

theorem callArmChk_sound {fr : Frame} {exec : ExecutionState} {stack : Stack UInt256}
    {gas caller recipient codeAddress value apparentValue inOffset inSize outOffset outSize :
      UInt256}
    {permission : Bool} {s : Step}
    (h : callArmChk fr exec stack gas caller recipient codeAddress value apparentValue
      inOffset inSize outOffset outSize permission = some s) :
    callArm fr exec stack gas caller recipient codeAddress value apparentValue
      inOffset inSize outOffset outSize permission = s := by
  unfold callArmChk at h
  unfold callArm
  split at h
  case isFalse => cases h
  case isTrue hin =>
  cases hm : memoryExpansionWords? exec.activeWords inOffset inSize >>=
      (memoryExpansionWords? · outOffset outSize) with
  | none =>
    rw [hm] at h
    injection h
  | some words' =>
    rw [hm] at h
    try dsimp only [] at h ⊢
    cases hc1 : charge (Cₘ words' - Cₘ exec.activeWords) exec with
    | error e =>
      rw [hc1] at h
      injection h
    | ok exec₁ =>
      rw [hc1] at h
      simp only [ebind_ok] at h ⊢
      try dsimp only [] at h ⊢
      cases hc2 : charge
          (callGasCap (AccountAddress.ofUInt256 codeAddress)
              (AccountAddress.ofUInt256 recipient) value gas exec₁.accounts
              exec₁.gasAvailable exec₁.substate +
            callExtraCost (AccountAddress.ofUInt256 codeAddress)
              (AccountAddress.ofUInt256 recipient) value exec₁.accounts exec₁.substate)
          exec₁ with
      | error e =>
        rw [hc2] at h
        injection h
      | ok exec₂ =>
        rw [hc2] at h
        try simp only [ebind_ok] at h ⊢
        try dsimp only [] at h ⊢
        rw [readWithPadding_eq_K exec₂.memory inOffset.toNat inSize.toNat hin]
        split at h
        · rename_i hcond
          rw [if_pos hcond]
          injection h
        · rename_i hcond
          rw [if_neg hcond]
          injection h

/-- Checked `systemOp`: the CALL arm over `callArmChk`; the other `callArm`/`createArm`
users and the memory-window halts fail closed; STOP (and the rest) delegate. -/
def systemOpChk (op : Operation.SystemOp) (fr : Frame) (exec : ExecutionState) :
    Option Step :=
  match op with
    | .CALL =>
      match exec.stack.pop7 with
        | none => some (.error .StackUnderflow)
        | some (stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize) =>
          if value ≠ 0 ∧ ¬ exec.executionEnv.canModifyState then
            some (.error .StaticModeViolation)
          else
            callArmChk fr exec stack
              gas (.ofNat exec.executionEnv.address) toAddress toAddress value value inOffset
              inSize outOffset outSize
              exec.executionEnv.canModifyState
    | .CALLCODE => none
    | .DELEGATECALL => none
    | .STATICCALL => none
    | .CREATE => none
    | .CREATE2 => none
    | .RETURN => none
    | .REVERT => none
    | .SELFDESTRUCT => none
    | _ => some (systemOp op fr exec)

theorem systemOpChk_sound {op : Operation.SystemOp} {fr : Frame} {exec : ExecutionState}
    {s : Step} (h : systemOpChk op fr exec = some s) : systemOp op fr exec = s := by
  cases op
  case CALL =>
    unfold systemOpChk at h
    unfold systemOp
    dsimp only [] at h ⊢
    cases hp : exec.stack.pop7 with
    | none =>
      rw [hp] at h
      injection h
    | some v =>
      obtain ⟨stack, gas, toAddress, value, inOffset, inSize, outOffset, outSize⟩ := v
      rw [hp] at h
      dsimp only [] at h
      simp only [liftOpt_some, ebind_ok]
      by_cases hguard : value ≠ 0 ∧ ¬ exec.executionEnv.canModifyState = true
      · rw [if_pos hguard] at h
        injection h with h
        rw [if_pos hguard, ← h]
        rfl
      · rw [if_neg hguard] at h
        rw [if_neg hguard]
        exact callArmChk_sound h
  all_goals first
    | exact Option.some.inj h
    | cases h

/-- Checked `dispatch`: `.Smsf`/`.System` route to the checked twins; the off-path
memory/hash ops fail closed; everything else delegates verbatim. -/
def dispatchChk (op : Operation) (arg : Option (UInt256 × UInt8)) (fr : Frame)
    (exec : ExecutionState) : Option Step :=
  match op with
    | .System s => systemOpChk s fr exec
    | .Smsf s => smsfOpChk s fr exec
    | .KECCAK256 => none
    | .CALLDATALOAD => none
    | .CALLDATACOPY => none
    | .CODECOPY => none
    | .EXTCODECOPY => none
    | .RETURNDATACOPY => none
    | .EXTCODEHASH => none
    | .BLOCKHASH => none
    | .LOG0 => none
    | .LOG1 => none
    | .LOG2 => none
    | .LOG3 => none
    | .LOG4 => none
    | _ => some (dispatch op arg fr exec)

theorem dispatchChk_sound {op : Operation} {arg : Option (UInt256 × UInt8)} {fr : Frame}
    {exec : ExecutionState} {s : Step} (h : dispatchChk op arg fr exec = some s) :
    dispatch op arg fr exec = s := by
  cases op
  case System sys => exact systemOpChk_sound h
  case Smsf sm => exact smsfOpChk_sound h
  case Env e => cases e <;> first | exact Option.some.inj h | cases h
  case Block b => cases b <;> first | exact Option.some.inj h | cases h
  case Log l => cases l <;> first | exact Option.some.inj h | cases h
  all_goals first
    | exact Option.some.inj h
    | cases h

/-- The checked step: `stepFrame` over `dispatchChk`. -/
def stepFrameChk (fr : Frame) : Option Signal :=
  let exec := fr.exec
  let (op, arg) := decode exec.executionEnv.code exec.pc |>.getD (.STOP, .none)
  if op = .INVALID then
    some (.halted (.exception .InvalidInstruction))
  else
    let δ := stackPopCount op
    let α := stackPushCount op
    if exec.stack.size - δ + α > 1024 then
      some (.halted (.exception .StackOverflow))
    else
      match dispatchChk op arg fr exec with
        | none => none
        | some (.ok signal) => some signal
        | some (.error e) => some (.halted (.exception e))

theorem stepFrameChk_sound {fr : Frame} {sig : Signal} (h : stepFrameChk fr = some sig) :
    stepFrame fr = sig := by
  unfold stepFrameChk at h
  unfold stepFrame
  dsimp only [] at h ⊢
  cases hd : decode fr.exec.executionEnv.code fr.exec.pc |>.getD (.STOP, .none) with
  | mk op arg =>
    rw [hd] at h
    dsimp only [] at h ⊢
    split at h
    case isTrue hinv =>
      rw [if_pos hinv]
      injection h
    case isFalse hinv =>
      rw [if_neg hinv]
      split at h
      case isTrue hover =>
        rw [if_pos hover]
        injection h
      case isFalse hover =>
        rw [if_neg hover]
        cases hdc : dispatchChk op arg fr fr.exec with
        | none => rw [hdc] at h; cases h
        | some st =>
          rw [hdc] at h
          rw [dispatchChk_sound hdc]
          cases st with
          | ok signal => injection h
          | error e => injection h

/-! ## §6 — the checked evaluators -/

/-- `nextLog`'s running-frame arm, factored over an already-computed signal. -/
def nextLogOnSig (c : LogConfig) (current : Frame) (sig : Signal) : LogConfig ⊕ LogResult :=
  match sig with
    | .next exec =>
      if isGasOp current && c.stack.isEmpty then
        .inl { c with state := .inl { current with exec := exec }
                      gasAcc := c.gasAcc ++ [UInt256.ofUInt64 exec.gasAvailable] }
      else if isSloadOp current && c.stack.isEmpty then
        .inl { c with state := .inl { current with exec := exec }
                      sloadAcc := c.sloadAcc ++ [sloadWarmthOf current] }
      else if isCreate2Op current && c.stack.isEmpty then
        .inl { c with state := .inl { current with exec := exec }
                      createAcc := c.createAcc ++ [softFailCreateRecord current] }
      else if isCallOp current && c.stack.isEmpty then
        .inl { c with state := .inl { current with exec := exec }
                      callAcc := c.callAcc ++ [softFailCallRecord current] }
      else
        .inl { c with state := .inl { current with exec := exec } }
    | .halted halt => .inl { c with state := .inr (endFrame current halt) }
    | .needsCall params pending =>
      match beginCall params with
        | .inl child => .inl { c with stack := .call pending :: c.stack
                                      state := .inl child }
        | .inr result => .inl { c with stack := .call pending :: c.stack
                                       state := .inr (.call result) }
    | .needsCreate params pending =>
      .inl { c with stack := .create pending :: c.stack
                    state := .inl (beginCreate params) }

/-- `nextLog` at a running frame IS the factored arm at its own signal. -/
theorem nextLog_inl (c : LogConfig) (current : Frame) (h : c.state = .inl current) :
    nextLog c = nextLogOnSig c current (stepFrame current) := by
  obtain ⟨stack, state, gasAcc, sloadAcc, callAcc, createAcc⟩ := c
  dsimp only [] at h
  subst h
  unfold nextLog nextLogOnSig
  dsimp only []
  cases hs : stepFrame current <;> rfl

/-- Checked `nextLog`: delivery steps delegate (the run's resumes are zero-window,
kernel-clean); running steps go through the checked `stepFrameChk`. -/
def nextLogChk (c : LogConfig) : Option (LogConfig ⊕ LogResult) :=
  match c.state with
    | .inr _ => some (nextLog c)
    | .inl current =>
      match stepFrameChk current with
        | none => none
        | some sig => some (nextLogOnSig c current sig)

theorem nextLogChk_sound {c : LogConfig} {x : LogConfig ⊕ LogResult}
    (h : nextLogChk c = some x) : nextLog c = x := by
  unfold nextLogChk at h
  cases hst : c.state with
  | inr result =>
    rw [hst] at h
    exact Option.some.inj h
  | inl current =>
    rw [hst] at h
    dsimp only [] at h
    cases hsf : stepFrameChk current with
    | none => rw [hsf] at h; cases h
    | some sig =>
      rw [hsf] at h
      injection h with h
      rw [nextLog_inl c current hst, stepFrameChk_sound hsf, h]

/-- Checked transition iterator (the kernel-crank surface for `exCheck`). -/
def stepsLogChk : ℕ → LogConfig → Option (LogConfig ⊕ LogResult)
  | 0, c => some (.inl c)
  | k + 1, c =>
    match nextLogChk c with
      | none => none
      | some (.inl c') => stepsLogChk k c'
      | some (.inr res) => some (.inr res)

theorem stepsLogChk_sound {k : ℕ} {c : LogConfig} {x : LogConfig ⊕ LogResult}
    (h : stepsLogChk k c = some x) : stepsLog k c = x := by
  induction k generalizing c with
  | zero =>
    unfold stepsLogChk at h
    unfold stepsLog
    exact Option.some.inj h
  | succ k ih =>
    unfold stepsLogChk at h
    unfold stepsLog
    cases hn : nextLogChk c with
    | none => rw [hn] at h; cases h
    | some y =>
      rw [hn] at h
      rw [nextLogChk_sound hn]
      cases y with
      | inl c' =>
        dsimp only [] at h ⊢
        exact ih h
      | inr res =>
        dsimp only [] at h ⊢
        exact Option.some.inj h

/-- `nextCC`'s body factored over an already-computed signal. -/
def nextCCOnSig (fr : Frame) (sig : Signal) : Frame ⊕ Bool :=
  match sig with
    | .next exec => .inl { fr with exec := exec }
    | .halted _ => .inr true
    | .needsCall cp pending =>
      match cp.codeSource with
        | .Precompiled _ => .inr false
        | .Code _ =>
          match beginCall cp with
            | .inl child =>
              match drive (seedFuel cp.gas) [] (running child) with
                | .ok childRes => .inl (resumeAfterCall childRes.toCallResult pending)
                | .error _ => .inr true
            | .inr _ => .inr true
    | .needsCreate cp pending =>
      match drive (seedFuel cp.gas) [] (running (beginCreate cp)) with
        | .ok childRes =>
          match resumeAfterCreate childRes.toCreateResult pending with
            | .ok resumeFr => .inl resumeFr
            | .error _ => .inr false
        | .error _ => .inr true

/-- `nextCC` IS the factored body at its own signal. -/
theorem nextCC_eq_onSig (fr : Frame) : nextCC fr = nextCCOnSig fr (stepFrame fr) := by
  unfold nextCC nextCCOnSig
  cases hs : stepFrame fr <;> rfl

/-- Checked `nextCC`. -/
def nextCCChk (fr : Frame) : Option (Frame ⊕ Bool) :=
  match stepFrameChk fr with
    | none => none
    | some sig => some (nextCCOnSig fr sig)

theorem nextCCChk_sound {fr : Frame} {x : Frame ⊕ Bool} (h : nextCCChk fr = some x) :
    nextCC fr = x := by
  unfold nextCCChk at h
  cases hsf : stepFrameChk fr with
  | none => rw [hsf] at h; cases h
  | some sig =>
    rw [hsf] at h
    injection h with h
    rw [nextCC_eq_onSig, stepFrameChk_sound hsf, h]

/-- Checked checker-transition iterator (the kernel-crank surface for
`entryCallsCodeOk`). -/
def stepsCCChk : ℕ → Frame → Option (Frame ⊕ Bool)
  | 0, fr => some (.inl fr)
  | k + 1, fr =>
    match nextCCChk fr with
      | none => none
      | some (.inl fr') => stepsCCChk k fr'
      | some (.inr b) => some (.inr b)

theorem stepsCCChk_sound {k : ℕ} {fr : Frame} {x : Frame ⊕ Bool}
    (h : stepsCCChk k fr = some x) : stepsCC k fr = x := by
  induction k generalizing fr with
  | zero =>
    unfold stepsCCChk at h
    unfold stepsCC
    exact Option.some.inj h
  | succ k ih =>
    unfold stepsCCChk at h
    unfold stepsCC
    cases hn : nextCCChk fr with
    | none => rw [hn] at h; cases h
    | some y =>
      rw [hn] at h
      rw [nextCCChk_sound hn]
      cases y with
      | inl fr' =>
        dsimp only [] at h ⊢
        exact ih h
      | inr b =>
        dsimp only [] at h ⊢
        exact Option.some.inj h

end BytecodeLayer.Exec.Recorder
