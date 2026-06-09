import ToyExternalCall.EVMBridgeSpec

namespace ToyExternalCall

open EvmYul

namespace EVMBytecode

def entryWithCode (code : ByteArray) (s : EVM.State) : EVM.State :=
  { s with pc := UInt256.ofNat 0, stack := [], executionEnv := { s.executionEnv with code := code } }

def afterStop (s : EVM.State) : EVM.State :=
  { s with execLength := s.execLength + 1, toMachineState := s.toMachineState.setReturnData .empty }

theorem UInt256_sub_zero (x : UInt256) : x - UInt256.ofNat 0 = x := by
  cases x with
  | mk val =>
    cases val with
    | mk n h =>
      have h' :
          n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
        simpa [UInt256.size] using h
      apply congrArg UInt256.mk
      apply Fin.ext
      change ((UInt256.size - 0 + n) % UInt256.size) = n
      rw [Nat.add_mod]
      simp [UInt256.size, Nat.mod_eq_of_lt h']

theorem UInt256_ofNat_zero_toNat : (UInt256.ofNat 0).toNat = 0 := by
  rfl

theorem UInt256_ofNat_33_toNat : (UInt256.ofNat 33).toNat = 33 := by
  rfl

theorem UInt256_toByteArray_data_length (value : UInt256) :
    (UInt256.toByteArray value).data.toList.length = 32 := by
  simp [UInt256.toByteArray, EvmYul.toBytes!_length]

theorem UInt256_toByteArray_roundtrip (value : UInt256) :
    EvmYul.uInt256OfByteArray value.toByteArray = value := by
  unfold EvmYul.uInt256OfByteArray UInt256.toByteArray
  simp [EvmYul.fromBytes'_toBytes!, EvmYul.UInt256.ofNat_toNat]

theorem parse_serialize_stop :
    EVM.parseInstr (EVM.serializeInstr (.STOP : Operation .EVM)) = some .STOP := by
  rfl

theorem parse_serialize_add :
    EVM.parseInstr (EVM.serializeInstr (.ADD : Operation .EVM)) = some .ADD := by
  rfl

theorem parse_serialize_calldataload :
    EVM.parseInstr (EVM.serializeInstr (.CALLDATALOAD : Operation .EVM)) =
      some .CALLDATALOAD := by
  rfl

theorem parse_serialize_mload :
    EVM.parseInstr (EVM.serializeInstr (.MLOAD : Operation .EVM)) = some .MLOAD := by
  rfl

theorem parse_serialize_mstore :
    EVM.parseInstr (EVM.serializeInstr (.MSTORE : Operation .EVM)) = some .MSTORE := by
  rfl

theorem parse_serialize_call :
    EVM.parseInstr (EVM.serializeInstr (.CALL : Operation .EVM)) = some .CALL := by
  rfl

theorem parse_serialize_push32 :
    EVM.parseInstr (EVM.serializeInstr (.PUSH32 : Operation .EVM)) = some .PUSH32 := by
  rfl

theorem decode_stop :
    EVM.decode (Bytecode.op .STOP) (UInt256.ofNat 0) = some (.STOP, none) := by
  decide

theorem decode_add :
    EVM.decode (Bytecode.op .ADD) (UInt256.ofNat 0) = some (.ADD, none) := by
  decide

theorem decode_calldataload :
    EVM.decode (Bytecode.op .CALLDATALOAD) (UInt256.ofNat 0) =
      some (.CALLDATALOAD, none) := by
  decide

theorem decode_mload :
    EVM.decode (Bytecode.op .MLOAD) (UInt256.ofNat 0) = some (.MLOAD, none) := by
  decide

theorem decode_mstore :
    EVM.decode (Bytecode.op .MSTORE) (UInt256.ofNat 0) = some (.MSTORE, none) := by
  decide

theorem decode_call :
    EVM.decode (Bytecode.op .CALL) (UInt256.ofNat 0) = some (.CALL, none) := by
  decide

theorem decode_push32 (value : Word) :
    EVM.decode (Bytecode.push32 value) (UInt256.ofNat 0) =
      some (.PUSH32, some (EvmYul.uInt256OfByteArray value.toByteArray, 32)) := by
  have h_take :
      List.take 32 (UInt256.toByteArray value).data.toList =
        (UInt256.toByteArray value).data.toList := by
    rw [← UInt256_toByteArray_data_length value]
    exact List.take_length
  unfold Bytecode.push32 EVM.decode EVM.argOnNBytesOfInstr Bytecode.opcode
  simp [ByteArray.get?, ByteArray.extract', Array.toList_append, UInt256_ofNat_zero_toNat,
    parse_serialize_push32, h_take]

def pushStopCode (value : Word) : ByteArray :=
  Bytecode.appendMany [Bytecode.push32 value, Bytecode.op .STOP]

theorem decode_push32_pushStopCode (value : Word) :
    EVM.decode (pushStopCode value) (UInt256.ofNat 0) =
      some (.PUSH32, some (EvmYul.uInt256OfByteArray value.toByteArray, 32)) := by
  have h_take_suffix :
      List.take 32
          ((UInt256.toByteArray value).data.toList ++ [EVM.serializeInstr (.STOP : Operation .EVM)]) =
        (UInt256.toByteArray value).data.toList := by
    rw [List.take_append_of_le_length (by rw [UInt256_toByteArray_data_length value])]
    rw [← UInt256_toByteArray_data_length value]
    exact List.take_length
  unfold pushStopCode Bytecode.appendMany Bytecode.push32 Bytecode.op EVM.decode
    EVM.argOnNBytesOfInstr Bytecode.opcode
  simp [ByteArray.get?, ByteArray.extract', Array.toList_append, UInt256_ofNat_zero_toNat,
    parse_serialize_push32, h_take_suffix]

theorem decode_stop_after_push32 (value : Word) :
    EVM.decode (pushStopCode value) (UInt256.ofNat 33) = some (.STOP, none) := by
  have h_size : (UInt256.toByteArray value).data.size = 32 := by
    simpa using UInt256_toByteArray_data_length value
  have h_get :
      (EVM.serializeInstr (.PUSH32 : Operation .EVM) ::
        ((UInt256.toByteArray value).data.toList ++ [EVM.serializeInstr (.STOP : Operation .EVM)]))[33]? =
        some (EVM.serializeInstr (.STOP : Operation .EVM)) := by
    rw [show 33 = 32 + 1 by rfl]
    rw [List.getElem?_cons_succ]
    rw [List.getElem?_append]
    simp [h_size]
  unfold pushStopCode Bytecode.appendMany Bytecode.push32 Bytecode.op EVM.decode
    EVM.argOnNBytesOfInstr Bytecode.opcode
  simp [ByteArray.get?, ByteArray.extract', Array.toList_append,
    UInt256_ofNat_33_toNat, parse_serialize_stop, h_get]

theorem memoryExpansionCost_stop (s : EVM.State) :
    EVM.memoryExpansionCost s (.STOP : Operation .EVM) = 0 := by
  unfold EVM.memoryExpansionCost
  change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  exact Nat.sub_self _

theorem C'_stop (s : EVM.State) :
    EVM.C' s (.STOP : Operation .EVM) = 0 := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wcopy,
    EVM.InstructionGasGroups.Wextaccount, GasConstants.Gzero]

theorem memoryExpansionCost_push32 (s : EVM.State) :
    EVM.memoryExpansionCost s (.PUSH32 : Operation .EVM) = 0 := by
  unfold EVM.memoryExpansionCost
  change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  exact Nat.sub_self _

theorem C'_push32 (s : EVM.State) :
    EVM.C' s (.PUSH32 : Operation .EVM) = GasConstants.Gverylow := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wbase,
    EVM.InstructionGasGroups.Wverylow,
    EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    EVM.InstructionGasGroups.Wcopy, EVM.InstructionGasGroups.Wextaccount]

def afterPush32 (value : UInt256) (s : EVM.State) : EVM.State :=
  EVM.State.replaceStackAndIncrPC
    { s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow }
    (s.stack.push value)
    (pcΔ := 33)

def chargeExec (gasCost : Nat) (s : EVM.State) : EVM.State :=
  { s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat gasCost }

theorem step_push32 (value : UInt256) (s : EVM.State) :
    EVM.step 1 GasConstants.Gverylow
      (some (((.PUSH32 : Operation .EVM), some (value, 32)))) s =
      .ok (afterPush32 value s) := by
  unfold EVM.step afterPush32
  change EvmYul.step (.PUSH32 : Operation .EVM) (some (value, 32))
      ({ s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow } : EVM.State) =
    .ok
      (EVM.State.replaceStackAndIncrPC
        { s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow }
        (s.stack.push value) (pcΔ := 33))
  unfold EvmYul.step
  rfl

theorem step_push32_succ (fuel : Nat) (value : UInt256) (s : EVM.State) :
    EVM.step (fuel + 1) GasConstants.Gverylow
      (some (((.PUSH32 : Operation .EVM), some (value, 32)))) s =
      .ok (afterPush32 value s) := by
  cases fuel with
  | zero => simpa using step_push32 value s
  | succ fuel =>
      unfold EVM.step afterPush32
      change EvmYul.step (.PUSH32 : Operation .EVM) (some (value, 32))
          ({ s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow } : EVM.State) =
        .ok
          (EVM.State.replaceStackAndIncrPC
            { s with execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow }
            (s.stack.push value) (pcΔ := 33))
      unfold EvmYul.step
      rfl

theorem step_add (lhs rhs : UInt256) (rest : List UInt256) (s : EVM.State) :
    EVM.step 1 GasConstants.Gverylow
      (some (((.ADD : Operation .EVM), (none : Option (UInt256 × Nat)))))
      { s with stack := lhs :: rhs :: rest } =
      .ok (EVM.State.replaceStackAndIncrPC
        (chargeExec GasConstants.Gverylow { s with stack := lhs :: rhs :: rest })
        ((lhs + rhs) :: rest)) := by
  unfold EVM.step chargeExec EvmYul.step
  change EvmYul.step (.ADD : Operation .EVM) none
      ({ s with stack := lhs :: rhs :: rest, execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow } : EVM.State) =
    .ok
      (EVM.State.replaceStackAndIncrPC
        { s with stack := lhs :: rhs :: rest, execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow }
        ((lhs + rhs) :: rest))
  rfl

theorem step_calldataload (offset : UInt256) (rest : List UInt256) (s : EVM.State) :
    EVM.step 1 GasConstants.Gverylow
      (some (((.CALLDATALOAD : Operation .EVM), (none : Option (UInt256 × Nat)))))
      { s with stack := offset :: rest } =
      .ok (EVM.State.replaceStackAndIncrPC
        (chargeExec GasConstants.Gverylow { s with stack := offset :: rest })
        (EvmYul.State.calldataload s.toState offset :: rest)) := by
  unfold EVM.step chargeExec EvmYul.step
  change EvmYul.step (.CALLDATALOAD : Operation .EVM) none
      ({ s with stack := offset :: rest, execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow } : EVM.State) =
    .ok
      (EVM.State.replaceStackAndIncrPC
        { s with stack := offset :: rest, execLength := s.execLength + 1, gasAvailable := s.gasAvailable - UInt256.ofNat GasConstants.Gverylow }
        (EvmYul.State.calldataload s.toState offset :: rest))
  rfl

theorem step_mload (offset : UInt256) (rest : List UInt256) (s : EVM.State) :
    EVM.step 1 GasConstants.Gverylow
      (some (((.MLOAD : Operation .EVM), (none : Option (UInt256 × Nat)))))
      { s with stack := offset :: rest } =
      let loaded := MachineState.mload
        (chargeExec GasConstants.Gverylow { s with stack := offset :: rest }).toMachineState
        offset
      .ok (EVM.State.replaceStackAndIncrPC
        { (chargeExec GasConstants.Gverylow { s with stack := offset :: rest }) with
          toMachineState := loaded.2 }
        (loaded.1 :: rest)) := by
  unfold EVM.step chargeExec EvmYul.step
  rfl

theorem step_mstore (offset value : UInt256) (rest : List UInt256) (s : EVM.State) :
    EVM.step 1 GasConstants.Gverylow
      (some (((.MSTORE : Operation .EVM), (none : Option (UInt256 × Nat)))))
      { s with stack := offset :: value :: rest } =
      .ok (EVM.State.replaceStackAndIncrPC
        { (chargeExec GasConstants.Gverylow { s with stack := offset :: value :: rest }) with
          toMachineState :=
            MachineState.mstore
              (chargeExec GasConstants.Gverylow { s with stack := offset :: value :: rest }).toMachineState
              offset value }
        rest) := by
  unfold EVM.step chargeExec EvmYul.step
  rfl

def afterSharedStop (s : EVM.State) : EVM.State :=
  { s with toMachineState := s.toMachineState.setReturnData .empty }

theorem shared_step_stop (s : EVM.State) :
    EvmYul.step (.STOP : Operation .EVM) none s = .ok (afterSharedStop s) := by
  unfold EvmYul.step afterSharedStop
  rfl

theorem step_stop (s : EVM.State) :
    EVM.step 1 0 (some (((.STOP : Operation .EVM), (none : Option (UInt256 × Nat))))) s =
      .ok (afterStop s) := by
  simp only [EVM.step, UInt256_sub_zero]
  change EvmYul.step (.STOP : Operation .EVM) none
      ({ s with execLength := s.execLength + 1 } : EVM.State) =
    .ok (afterStop s)
  rw [shared_step_stop]
  rfl

theorem evmX_stop (validJumps : Array UInt256) (s : EVM.State) :
    EVM.X 2 validJumps (entryWithCode (Bytecode.op .STOP) s) =
      .ok (EVM.ExecutionResult.success (afterStop (entryWithCode (Bytecode.op .STOP) s)) .empty) := by
  simp only [EVM.X, entryWithCode]
  simp only [decode_stop]
  simp [EVM.Z, EVM.H, EVM.W, EVM.notIn, EVM.belongs, memoryExpansionCost_stop, C'_stop,
    EVM.δ, EVM.α, Operation.isCreate, UInt256_sub_zero]
  change (do
      let evmState' ← EVM.step 1 0
        (some (((.STOP : Operation .EVM), (none : Option (UInt256 × Nat)))))
        (entryWithCode (Bytecode.op .STOP) s)
      .ok (EVM.ExecutionResult.success evmState' ByteArray.empty)) =
    .ok (EVM.ExecutionResult.success (afterStop (entryWithCode (Bytecode.op .STOP) s)) .empty)
  rw [step_stop]
  rfl

theorem evmX_continue
    (fuel : Nat) (validJumps : Array UInt256) (s pre s' : EVM.State)
    (instr : Operation .EVM) (arg : Option (UInt256 × Nat)) (cost : Nat)
    (hdecode : EVM.decode s.executionEnv.code s.pc = some (instr, arg))
    (hz : EVM.Z validJumps instr s = .ok (pre, cost))
    (hstep : EVM.step fuel cost (some (instr, arg)) pre = .ok s')
    (hhalt : EVM.H s'.toMachineState instr = none) :
    EVM.X (fuel + 1) validJumps s = EVM.X fuel validJumps s' := by
  conv_lhs => unfold EVM.X
  simp only [hdecode, Option.getD_some, hz, hstep]
  change (match EVM.H s'.toMachineState instr with
    | none => EVM.X fuel validJumps s'
    | some o =>
      if (instr == Operation.REVERT) = true then .ok (EVM.ExecutionResult.revert s'.gasAvailable o)
      else .ok (EVM.ExecutionResult.success s' o)) =
    EVM.X fuel validJumps s'
  rw [hhalt]

theorem evmX_halt_success
    (fuel : Nat) (validJumps : Array UInt256) (s pre s' : EVM.State)
    (instr : Operation .EVM) (arg : Option (UInt256 × Nat)) (cost : Nat) (output : ByteArray)
    (hdecode : EVM.decode s.executionEnv.code s.pc = some (instr, arg))
    (hz : EVM.Z validJumps instr s = .ok (pre, cost))
    (hstep : EVM.step fuel cost (some (instr, arg)) pre = .ok s')
    (hhalt : EVM.H s'.toMachineState instr = some output)
    (hnotRevert : instr ≠ .REVERT) :
    EVM.X (fuel + 1) validJumps s =
      .ok (EVM.ExecutionResult.success s' output) := by
  conv_lhs => unfold EVM.X
  simp only [hdecode, Option.getD_some, hz, hstep]
  change (match EVM.H s'.toMachineState instr with
    | none => EVM.X fuel validJumps s'
    | some o =>
      if (instr == Operation.REVERT) = true then .ok (EVM.ExecutionResult.revert s'.gasAvailable o)
      else .ok (EVM.ExecutionResult.success s' o)) =
    .ok (EVM.ExecutionResult.success s' output)
  rw [hhalt]
  simp [hnotRevert]

theorem empty_program_evmX (initial : ToyState) :
    EVM.X (Bytecode.lowerFuel [])
      (EVM.D_J (Bytecode.lower []) (UInt256.ofNat 0))
      (EVMBridgeSpec.withLoweredCodeAndLocals initial []) =
    .ok (EVM.ExecutionResult.success
      (afterStop (EVMBridgeSpec.withLoweredCodeAndLocals initial [])) .empty) := by
  simpa [Bytecode.lowerFuel, Bytecode.lower, Bytecode.lowerOps, Bytecode.assemble,
    Bytecode.assembleOp, EVMBridgeSpec.withLoweredCodeAndLocals, EVMBridgeSpec.seedLocals,
    entryWithCode, Bytecode.op, Bytecode.opcode] using
      evmX_stop (EVM.D_J (Bytecode.lower []) (UInt256.ofNat 0))
        ({ initial.evm with execLength := 0 })

end EVMBytecode

end ToyExternalCall
