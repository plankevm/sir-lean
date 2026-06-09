import ToyExternalCall.EVMBytecode

namespace ToyExternalCall

open EvmYul

namespace Obstruction

def zeroGasState : ToyState :=
  { evm := { (default : EVM.State) with gasAvailable := UInt256.ofNat 0 }
    locals := ToyState.emptyLocals }

def addOnlyProgram : Program :=
  [.add 0 (.const (UInt256.ofNat 1)) (.const (UInt256.ofNat 2))]

def emptyOracle : CallOracle :=
  fun state _request => .ok
    { successFlag := UInt256.ofNat 1
      returnData := .empty
      evm := state.evm }

theorem source_addOnlyProgram_succeeds :
    run emptyOracle (addOnlyProgram.length + 1) zeroGasState addOnlyProgram =
      .ok (zeroGasState.writeLocal 0 (UInt256.ofNat 1 + UInt256.ofNat 2)) := by
  rfl

theorem lowered_addOnlyProgram_zeroGas_fails :
    EVM.X (Bytecode.lowerFuel addOnlyProgram)
      (EVM.D_J (Bytecode.lower addOnlyProgram) (UInt256.ofNat 0))
      (EVMBridgeSpec.withLoweredCodeAndLocals zeroGasState addOnlyProgram) =
      .error .OutOfGass := by
  let s := EVMBridgeSpec.withLoweredCodeAndLocals zeroGasState addOnlyProgram
  have hdecode :
      EVM.decode s.executionEnv.code s.pc =
        some (.PUSH32, some (EvmYul.uInt256OfByteArray (UInt256.ofNat 2).toByteArray, 32)) := by
    native_decide
  have hz :
      EVM.Z (EVM.D_J (Bytecode.lower addOnlyProgram) (UInt256.ofNat 0))
        (.PUSH32 : Operation .EVM) s = .error .OutOfGass := by
    have hread :
        Program.readLocals
          [Instr.add 0 (Operand.const (UInt256.ofNat 1)) (Operand.const (UInt256.ofNat 2))] =
          [] := by
      rfl
    have hgas :
        (s.gasAvailable - UInt256.ofNat 0).toNat = 0 := by
      simp [s, zeroGasState, addOnlyProgram, Program.readLocals, Instr.readLocals,
        Operand.locals, EVMBridgeSpec.withLoweredCodeAndLocals, EVMBridgeSpec.seedLocals,
        EVMBytecode.UInt256_sub_zero, EVMBytecode.UInt256_ofNat_zero_toNat]
    unfold EVM.Z
    simp [s, zeroGasState, addOnlyProgram, EVMBytecode.memoryExpansionCost_push32,
      EVMBytecode.C'_push32, GasConstants.Gverylow,
      EVMBytecode.UInt256_sub_zero, EVMBytecode.UInt256_ofNat_zero_toNat,
      Program.readLocals, Instr.readLocals, Operand.locals,
      EVMBridgeSpec.withLoweredCodeAndLocals, EVMBridgeSpec.seedLocals]
    rfl
  change EVM.X (Bytecode.lowerFuel addOnlyProgram)
      (EVM.D_J (Bytecode.lower addOnlyProgram) (UInt256.ofNat 0)) s =
      .error .OutOfGass
  unfold EVM.X
  have hz' :
      EVM.Z
        (EVM.D_J
          (Bytecode.lower [Instr.add 0 (Operand.const (UInt256.ofNat 1))
            (Operand.const (UInt256.ofNat 2))])
          (UInt256.ofNat 0))
        ((some (.PUSH32, some (EvmYul.uInt256OfByteArray (UInt256.ofNat 2).toByteArray, 32))).getD
          (.STOP, none)).1
        s = .error .OutOfGass := by
    simpa [addOnlyProgram] using hz
  simp only [Bytecode.lowerFuel, addOnlyProgram, hdecode]
  rw [hz']
  simp [Bytecode.instrFuel, Bytecode.addFuel, Bytecode.operandFuel]

theorem current_evm_preservation_statement_is_false :
    ¬ EVMBridgeSpec.ResultRelOn
      addOnlyProgram.touchedLocals
      (run emptyOracle (addOnlyProgram.length + 1) zeroGasState addOnlyProgram)
      (EVM.X (Bytecode.lowerFuel addOnlyProgram)
        (EVM.D_J (Bytecode.lower addOnlyProgram) (UInt256.ofNat 0))
        (EVMBridgeSpec.withLoweredCodeAndLocals zeroGasState addOnlyProgram)) := by
  rw [source_addOnlyProgram_succeeds, lowered_addOnlyProgram_zeroGas_fails]
  simp [EVMBridgeSpec.ResultRelOn]

end Obstruction

end ToyExternalCall
