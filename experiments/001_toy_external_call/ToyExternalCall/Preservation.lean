import ToyExternalCall.EVMLemmas

/-!
# The lowering preservation theorem

`lowering_correct`: executing the lowered bytecode of a program under
EVMYulLean's `EVM.X` is equivalent to the IR's gas-exact executable
semantics, for **every** initial machine state, fuel and gas level. The
only assumption is `CallOracleSound` (the call oracle agrees with
`EVM.call`, which in turn ignores the frame fields), plus the
representability bound that the lowered code is addressable by a 256-bit
program counter.

The proof composes the per-opcode `EVM.X` iteration lemmas into chunk
lemmas (operand evaluation, local writes, one IR instruction) and then
inducts over the program.
-/

namespace ToyExternalCall

open EvmYul
open EVMLemmas

namespace Preservation

/-! ## Chunk lemmas -/

section Chunks

variable (code : ByteArray) (vj : Array UInt256)

/-- Evaluating one operand: the lowered ops push its value. -/
theorem operand_chunk (operand : Operand) (pre post : List UInt8)
    (hcode : code.data.toList =
      pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps operand) ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1022)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat pre.length) stk code) =
      match evalOperand s operand with
      | .error e => .error e
      | .ok (v, s') =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm
              (.ofNat (pre.length +
                (Bytecode.codeBytes (Bytecode.compileOperandOps operand)).length))
              (v :: stk) code) := by
  have hpre : pre.length < UInt256.size := by
    have := hsize
    rw [hcode] at this
    simp only [List.length_append] at this
    omega
  cases operand with
  | const v =>
      have hcode' : code.data.toList =
          pre ++ Bytecode.opBytes (.push v) ++ post := by
        simpa [Bytecode.compileOperandOps, Bytecode.codeBytes] using hcode
      rw [X_push code pre post vj v hcode' hpre stk (by omega) s]
      cases h : pushStep s with
      | error e => simp [evalOperand, h, Bind.bind, Except.bind]
      | ok s' =>
          simp only [evalOperand, h, Bind.bind, Except.bind]
          congr 2
          simp [Bytecode.compileOperandOps, Bytecode.codeBytes,
            Bytecode.opBytes_length, Bytecode.opSize]
  | «local» x =>
      have hcode₁ : code.data.toList =
          pre ++ Bytecode.opBytes (.push (localSlot x)) ++
            (Bytecode.opBytes .mload ++ post) := by
        simpa [Bytecode.compileOperandOps, Bytecode.codeBytes,
          List.append_assoc] using hcode
      rw [X_push code pre (Bytecode.opBytes .mload ++ post) vj (localSlot x)
        hcode₁ hpre stk (by omega) s]
      cases h : pushStep s with
      | error e => simp [evalOperand, h, Bind.bind, Except.bind]
      | ok s₁ =>
          dsimp only
          have hcode₂ : code.data.toList =
              (pre ++ Bytecode.opBytes (.push (localSlot x))) ++
                Bytecode.opBytes .mload ++ post := by
            simpa [List.append_assoc] using hcode₁
          have hpre₂ : (pre ++ Bytecode.opBytes (.push (localSlot x))).length <
              UInt256.size := by
            have := hsize
            rw [hcode₂] at this
            simp only [List.length_append] at this
            simp only [List.length_append]
            omega
          have hlen₁ : (pre ++ Bytecode.opBytes (.push (localSlot x))).length =
              pre.length + 33 := by
            simp [Bytecode.opBytes_length, Bytecode.opSize]
          rw [show (UInt256.ofNat (pre.length + 33)) =
              (UInt256.ofNat (pre ++ Bytecode.opBytes (.push (localSlot x))).length)
            from by rw [hlen₁]]
          rw [X_mload code (pre ++ Bytecode.opBytes (.push (localSlot x))) post vj
            (localSlot x) hcode₂ hpre₂ stk (by omega) s₁]
          cases h₂ : mloadStep (localSlot x) s₁ with
          | error e => simp [evalOperand, h, h₂, Bind.bind, Except.bind]
          | ok p =>
              simp only [evalOperand, h, h₂, Bind.bind, Except.bind]
              congr 2
              rw [hlen₁]
              simp [Bytecode.compileOperandOps, Bytecode.codeBytes,
                Bytecode.opBytes_length, Bytecode.opSize]

/-- Writing a local: `PUSH32 slot; MSTORE` consumes the top of stack. -/
theorem writeLocal_chunk (x : Local) (v : Word) (pre post : List UInt8)
    (hcode : code.data.toList =
      pre ++ Bytecode.codeBytes (Bytecode.storeLocalOps x) ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1022)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat pre.length) (v :: stk) code) =
      match writeLocal s x v with
      | .error e => .error e
      | .ok s' =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm
              (.ofNat (pre.length + (Bytecode.codeBytes (Bytecode.storeLocalOps x)).length))
              stk code) := by
  have hpre : pre.length < UInt256.size := by
    have := hsize
    rw [hcode] at this
    simp only [List.length_append] at this
    omega
  have hcode₁ : code.data.toList =
      pre ++ Bytecode.opBytes (.push (localSlot x)) ++
        (Bytecode.opBytes .mstore ++ post) := by
    simpa [Bytecode.storeLocalOps, Bytecode.codeBytes, List.append_assoc] using hcode
  rw [X_push code pre (Bytecode.opBytes .mstore ++ post) vj (localSlot x)
    hcode₁ hpre (v :: stk) (by simp; omega) s]
  cases h : pushStep s with
  | error e => simp [writeLocal, h, Bind.bind, Except.bind]
  | ok s₁ =>
      dsimp only
      have hcode₂ : code.data.toList =
          (pre ++ Bytecode.opBytes (.push (localSlot x))) ++
            Bytecode.opBytes .mstore ++ post := by
        simpa [List.append_assoc] using hcode₁
      have hpre₂ : (pre ++ Bytecode.opBytes (.push (localSlot x))).length <
          UInt256.size := by
        have := hsize
        rw [hcode₂] at this
        simp only [List.length_append] at this
        simp only [List.length_append]
        omega
      have hlen₁ : (pre ++ Bytecode.opBytes (.push (localSlot x))).length =
          pre.length + 33 := by
        simp [Bytecode.opBytes_length, Bytecode.opSize]
      rw [show (UInt256.ofNat (pre.length + 33)) =
          (UInt256.ofNat (pre ++ Bytecode.opBytes (.push (localSlot x))).length)
        from by rw [hlen₁]]
      rw [X_mstore code (pre ++ Bytecode.opBytes (.push (localSlot x))) post vj
        (localSlot x) v hcode₂ hpre₂ stk (by omega) s₁]
      cases h₂ : mstoreStep (localSlot x) v s₁ with
      | error e => simp [writeLocal, h, h₂, Bind.bind, Except.bind]
      | ok s₂ =>
          simp only [writeLocal, h, h₂, Bind.bind, Except.bind]
          congr 2
          rw [hlen₁]
          simp [Bytecode.storeLocalOps, Bytecode.codeBytes,
            Bytecode.opBytes_length, Bytecode.opSize]

/-! ### Position-generalized variants

The same chunk lemmas with the program counter given as an arbitrary
arithmetic expression plus a side equation, so that successive chunks
compose without rewriting between `+`-form and `List.length`-form. -/

theorem operand_chunk_at (operand : Operand) (n : Nat) (pre post : List UInt8)
    (hpre : pre.length = n)
    (hcode : code.data.toList =
      pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps operand) ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1022)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat n) stk code) =
      match evalOperand s operand with
      | .error e => .error e
      | .ok (v, s') =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm
              (.ofNat (n +
                (Bytecode.codeBytes (Bytecode.compileOperandOps operand)).length))
              (v :: stk) code) := by
  subst hpre
  exact operand_chunk code vj operand pre post hcode hsize stk hov s

theorem writeLocal_chunk_at (x : Local) (v : Word) (n : Nat) (pre post : List UInt8)
    (hpre : pre.length = n)
    (hcode : code.data.toList =
      pre ++ Bytecode.codeBytes (Bytecode.storeLocalOps x) ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1022)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat n) (v :: stk) code) =
      match writeLocal s x v with
      | .error e => .error e
      | .ok s' =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm
              (.ofNat (n + (Bytecode.codeBytes (Bytecode.storeLocalOps x)).length))
              stk code) := by
  subst hpre
  exact writeLocal_chunk code vj x v pre post hcode hsize stk hov s

theorem X_calldataload_at (addr : Word) (n : Nat) (pre post : List UInt8)
    (hpre : pre.length = n)
    (hcode : code.data.toList = pre ++ Bytecode.opBytes .calldataload ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1023)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat n) (addr :: stk) code) =
      match pushStep s with
      | .error e => .error e
      | .ok s' =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm (.ofNat (n + 1))
              (EvmYul.State.calldataload s'.evm.toState addr :: stk) code) := by
  subst hpre
  have hl : pre.length < UInt256.size := by
    have := hsize; rw [hcode] at this
    simp only [List.length_append] at this; omega
  exact X_calldataload code pre post vj addr hcode hl stk hov s

theorem X_add_at (a b : Word) (n : Nat) (pre post : List UInt8)
    (hpre : pre.length = n)
    (hcode : code.data.toList = pre ++ Bytecode.opBytes .add ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1023)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat n) (a :: b :: stk) code) =
      match pushStep s with
      | .error e => .error e
      | .ok s' =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm (.ofNat (n + 1)) ((a + b) :: stk) code) := by
  subst hpre
  have hl : pre.length < UInt256.size := by
    have := hsize; rw [hcode] at this
    simp only [List.length_append] at this; omega
  exact X_add code pre post vj a b hcode hl stk hov s

theorem X_call_at (oracle : CallOracle) (hsound : CallOracleSound oracle)
    (g t v io is oo os : Word) (n : Nat) (pre post : List UInt8)
    (hpre : pre.length = n)
    (hcode : code.data.toList = pre ++ Bytecode.opBytes .call ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1023)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat n)
        (g :: t :: v :: io :: is :: oo :: os :: stk) code) =
      match callStep oracle g t v io is oo os s with
      | .error e => .error e
      | .ok (flag, s') =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm (.ofNat (n + 1)) (flag :: stk) code) := by
  subst hpre
  have hl : pre.length < UInt256.size := by
    have := hsize; rw [hcode] at this
    simp only [List.length_append] at this; omega
  exact X_call code pre post vj oracle hsound g t v io is oo os hcode hl stk hov s

theorem X_stop_at (n : Nat) (pre post : List UInt8)
    (hpre : pre.length = n)
    (hcode : code.data.toList = pre ++ Bytecode.opBytes .stop ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (stk : List Word) (hov : stk.length ≤ 1024)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat n) stk code) =
      (stopStep s).map
        (fun s' => .success (injectFrame s'.evm (.ofNat n) stk code)
          ByteArray.empty) := by
  subst hpre
  have hl : pre.length < UInt256.size := by
    have := hsize; rw [hcode] at this
    simp only [List.length_append] at this; omega
  exact X_stop code pre post vj hcode hl stk hov s

/-- Cast a `UInt256` program counter along a `Nat` equation. -/
theorem pc_congr {a b : Nat} (h : a = b) : UInt256.ofNat a = UInt256.ofNat b :=
  congrArg _ h

/-- Executing the chunk of one IR instruction. -/
theorem instr_chunk (oracle : CallOracle) (hsound : CallOracleSound oracle)
    (instr : Instr) (pre post : List UInt8)
    (hcode : code.data.toList =
      pre ++ Bytecode.codeBytes (Bytecode.compileInstrOps instr) ++ post)
    (hsize : code.data.toList.length < UInt256.size)
    (s : Exec) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat pre.length) [] code) =
      match execInstr oracle s instr with
      | .error e => .error e
      | .ok s' =>
          EVM.X s'.fuel vj
            (injectFrame s'.evm
              (.ofNat (pre.length +
                (Bytecode.codeBytes (Bytecode.compileInstrOps instr)).length))
              [] code) := by
  cases instr with
  | inputLoad dst offset =>
      have hcode₁ : code.data.toList =
          pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps offset) ++
            (Bytecode.opBytes .calldataload ++
              (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post)) := by
        simpa [Bytecode.compileInstrOps, Bytecode.codeBytes, List.append_assoc]
          using hcode
      rw [operand_chunk_at code vj offset pre.length pre _ rfl hcode₁ hsize []
        (by simp; try omega) s]
      cases h₁ : evalOperand s offset with
      | error e => simp [execInstr, h₁, Bind.bind, Except.bind]
      | ok p₁ =>
      obtain ⟨off, s₁⟩ := p₁
      dsimp only
      have hcode₂ : code.data.toList =
          (pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps offset)) ++
            Bytecode.opBytes .calldataload ++
            (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post) := by
        simpa [List.append_assoc] using hcode₁
      rw [X_calldataload_at code vj off _ _ _ (by simp; try omega) hcode₂ hsize [] (by simp; try omega) s₁]
      cases h₂ : pushStep s₁ with
      | error e => simp [execInstr, h₁, h₂, Bind.bind, Except.bind]
      | ok s₂ =>
      dsimp only
      have hcode₃ : code.data.toList =
          ((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps offset)) ++
            Bytecode.opBytes .calldataload) ++
            Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post := by
        simpa [List.append_assoc] using hcode₂
      rw [writeLocal_chunk_at code vj dst
        (EvmYul.State.calldataload s₂.evm.toState off) _ _ post
        (by simp [Bytecode.opBytes_length, Bytecode.opSize]; try omega) hcode₃ hsize []
        (by simp; try omega) s₂]
      cases h₃ : writeLocal s₂ dst (EvmYul.State.calldataload s₂.evm.toState off) with
      | error e => simp [execInstr, h₁, h₂, h₃, Bind.bind, Except.bind]
      | ok s₃ =>
          simp only [execInstr, h₁, h₂, h₃, Bind.bind, Except.bind]
          congr 2
          apply pc_congr
          simp [Bytecode.compileInstrOps, Bytecode.codeBytes,
            Bytecode.opBytes_length, Bytecode.opSize]
          omega
  | add dst lhs rhs =>
      have hcode₁ : code.data.toList =
          pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps rhs) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps lhs) ++
              (Bytecode.opBytes .add ++
                (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post))) := by
        simpa [Bytecode.compileInstrOps, Bytecode.codeBytes, List.append_assoc]
          using hcode
      rw [operand_chunk_at code vj rhs pre.length pre _ rfl hcode₁ hsize []
        (by simp; try omega) s]
      cases h₁ : evalOperand s rhs with
      | error e => simp [execInstr, h₁, Bind.bind, Except.bind]
      | ok p₁ =>
      obtain ⟨vr, s₁⟩ := p₁
      dsimp only
      have hcode₂ : code.data.toList =
          (pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps rhs)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps lhs) ++
            (Bytecode.opBytes .add ++
              (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post)) := by
        simpa [List.append_assoc] using hcode₁
      rw [operand_chunk_at code vj lhs _ _ _ (by simp; try omega) hcode₂ hsize [vr]
        (by simp; try omega) s₁]
      cases h₂ : evalOperand s₁ lhs with
      | error e => simp [execInstr, h₁, h₂, Bind.bind, Except.bind]
      | ok p₂ =>
      obtain ⟨vl, s₂⟩ := p₂
      dsimp only
      have hcode₃ : code.data.toList =
          ((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps rhs)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps lhs)) ++
            Bytecode.opBytes .add ++
            (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post) := by
        simpa [List.append_assoc] using hcode₂
      rw [X_add_at code vj vl vr _ _ _ (by simp; try omega) hcode₃ hsize [] (by simp; try omega) s₂]
      cases h₃ : pushStep s₂ with
      | error e => simp [execInstr, h₁, h₂, h₃, Bind.bind, Except.bind]
      | ok s₃ =>
      dsimp only
      have hcode₄ : code.data.toList =
          (((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps rhs)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps lhs)) ++
            Bytecode.opBytes .add) ++
            Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post := by
        simpa [List.append_assoc] using hcode₃
      rw [writeLocal_chunk_at code vj dst (vl + vr) _ _ post
        (by simp [Bytecode.opBytes_length, Bytecode.opSize]; try omega) hcode₄ hsize []
        (by simp; try omega) s₃]
      cases h₄ : writeLocal s₃ dst (vl + vr) with
      | error e => simp [execInstr, h₁, h₂, h₃, h₄, Bind.bind, Except.bind]
      | ok s₄ =>
          simp only [execInstr, h₁, h₂, h₃, h₄, Bind.bind, Except.bind]
          congr 2
          apply pc_congr
          simp [Bytecode.compileInstrOps, Bytecode.codeBytes,
            Bytecode.opBytes_length, Bytecode.opSize]
          omega
  | call dst args =>
      obtain ⟨gasO, targetO, valueO, inOffO, inSizeO, outOffO, outSizeO⟩ := args
      have hcode₁ : code.data.toList =
          pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps outOffO) ++
              (Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO) ++
                (Bytecode.codeBytes (Bytecode.compileOperandOps inOffO) ++
                  (Bytecode.codeBytes (Bytecode.compileOperandOps valueO) ++
                    (Bytecode.codeBytes (Bytecode.compileOperandOps targetO) ++
                      (Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
                        (Bytecode.opBytes .call ++
                          (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++
                            post)))))))) := by
        simpa [Bytecode.compileInstrOps, Bytecode.codeBytes, List.append_assoc]
          using hcode
      rw [operand_chunk_at code vj outSizeO pre.length pre _ rfl hcode₁ hsize []
        (by simp; try omega) s]
      cases h₁ : evalOperand s outSizeO with
      | error e => simp [execInstr, h₁, Bind.bind, Except.bind]
      | ok p₁ =>
      obtain ⟨os, s₁⟩ := p₁
      dsimp only
      have hcode₂ : code.data.toList =
          (pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO) ++
              (Bytecode.codeBytes (Bytecode.compileOperandOps inOffO) ++
                (Bytecode.codeBytes (Bytecode.compileOperandOps valueO) ++
                  (Bytecode.codeBytes (Bytecode.compileOperandOps targetO) ++
                    (Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
                      (Bytecode.opBytes .call ++
                        (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++
                          post))))))) := by
        simpa [List.append_assoc] using hcode₁
      rw [operand_chunk_at code vj outOffO _ _ _ (by simp; try omega) hcode₂ hsize [os]
        (by simp; try omega) s₁]
      cases h₂ : evalOperand s₁ outOffO with
      | error e => simp [execInstr, h₁, h₂, Bind.bind, Except.bind]
      | ok p₂ =>
      obtain ⟨oo, s₂⟩ := p₂
      dsimp only
      have hcode₃ : code.data.toList =
          ((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps inOffO) ++
              (Bytecode.codeBytes (Bytecode.compileOperandOps valueO) ++
                (Bytecode.codeBytes (Bytecode.compileOperandOps targetO) ++
                  (Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
                    (Bytecode.opBytes .call ++
                      (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++
                        post)))))) := by
        simpa [List.append_assoc] using hcode₂
      rw [operand_chunk_at code vj inSizeO _ _ _ (by simp; try omega) hcode₃ hsize [oo, os]
        (by simp; try omega) s₂]
      cases h₃ : evalOperand s₂ inSizeO with
      | error e => simp [execInstr, h₁, h₂, h₃, Bind.bind, Except.bind]
      | ok p₃ =>
      obtain ⟨is, s₃⟩ := p₃
      dsimp only
      have hcode₄ : code.data.toList =
          (((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inOffO) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps valueO) ++
              (Bytecode.codeBytes (Bytecode.compileOperandOps targetO) ++
                (Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
                  (Bytecode.opBytes .call ++
                    (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++
                      post))))) := by
        simpa [List.append_assoc] using hcode₃
      rw [operand_chunk_at code vj inOffO _ _ _ (by simp; try omega) hcode₄ hsize [is, oo, os]
        (by simp; try omega) s₃]
      cases h₄ : evalOperand s₃ inOffO with
      | error e => simp [execInstr, h₁, h₂, h₃, h₄, Bind.bind, Except.bind]
      | ok p₄ =>
      obtain ⟨io, s₄⟩ := p₄
      dsimp only
      have hcode₅ : code.data.toList =
          ((((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps valueO) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps targetO) ++
              (Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
                (Bytecode.opBytes .call ++
                  (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++
                    post)))) := by
        simpa [List.append_assoc] using hcode₄
      rw [operand_chunk_at code vj valueO _ _ _ (by simp; try omega) hcode₅ hsize [io, is, oo, os]
        (by simp; try omega) s₄]
      cases h₅ : evalOperand s₄ valueO with
      | error e => simp [execInstr, h₁, h₂, h₃, h₄, h₅, Bind.bind, Except.bind]
      | ok p₅ =>
      obtain ⟨v, s₅⟩ := p₅
      dsimp only
      have hcode₆ : code.data.toList =
          (((((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps valueO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps targetO) ++
            (Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
              (Bytecode.opBytes .call ++
                (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post))) := by
        simpa [List.append_assoc] using hcode₅
      rw [operand_chunk_at code vj targetO _ _ _ (by simp; try omega) hcode₆ hsize
        [v, io, is, oo, os] (by simp; try omega) s₅]
      cases h₆ : evalOperand s₅ targetO with
      | error e => simp [execInstr, h₁, h₂, h₃, h₄, h₅, h₆, Bind.bind, Except.bind]
      | ok p₆ =>
      obtain ⟨t, s₆⟩ := p₆
      dsimp only
      have hcode₇ : code.data.toList =
          ((((((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps valueO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps targetO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps gasO) ++
            (Bytecode.opBytes .call ++
              (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post)) := by
        simpa [List.append_assoc] using hcode₆
      rw [operand_chunk_at code vj gasO _ _ _ (by simp; try omega) hcode₇ hsize
        [t, v, io, is, oo, os] (by simp; try omega) s₆]
      cases h₇ : evalOperand s₆ gasO with
      | error e =>
          simp [execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇, Bind.bind, Except.bind]
      | ok p₇ =>
      obtain ⟨gw, s₇⟩ := p₇
      dsimp only
      have hcode₈ : code.data.toList =
          (((((((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps valueO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps targetO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps gasO)) ++
            Bytecode.opBytes .call ++
            (Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post) := by
        simpa [List.append_assoc] using hcode₇
      rw [X_call_at code vj oracle hsound gw t v io is oo os _ _ _ (by simp; try omega)
        hcode₈ hsize [] (by simp; try omega) s₇]
      cases h₈ : callStep oracle gw t v io is oo os s₇ with
      | error e =>
          simp [execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, Bind.bind, Except.bind]
      | ok p₈ =>
      obtain ⟨flag, s₈⟩ := p₈
      dsimp only
      have hcode₉ : code.data.toList =
          ((((((((pre ++ Bytecode.codeBytes (Bytecode.compileOperandOps outSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps outOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inSizeO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps inOffO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps valueO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps targetO)) ++
            Bytecode.codeBytes (Bytecode.compileOperandOps gasO)) ++
            Bytecode.opBytes .call) ++
            Bytecode.codeBytes (Bytecode.storeLocalOps dst) ++ post := by
        simpa [List.append_assoc] using hcode₈
      rw [writeLocal_chunk_at code vj dst flag _ _ post
        (by simp [Bytecode.opBytes_length, Bytecode.opSize]; try omega) hcode₉ hsize []
        (by simp; try omega) s₈]
      cases h₉ : writeLocal s₈ dst flag with
      | error e =>
          simp [execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
            Bind.bind, Except.bind]
      | ok s₉ =>
          simp only [execInstr, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
            Bind.bind, Except.bind]
          congr 2
          apply pc_congr
          simp [Bytecode.compileInstrOps, Bytecode.codeBytes,
            Bytecode.opBytes_length, Bytecode.opSize]
          omega

end Chunks

/-! ## The main theorem -/

/-- Simulation of a program suffix whose lowered ops sit at the end of the
code, starting at the position right after `pre`. -/
theorem run_simulation (code : ByteArray) (vj : Array UInt256)
    (oracle : CallOracle) (hsound : CallOracleSound oracle)
    (rest : Program) (pre : List UInt8)
    (hsize : code.data.toList.length < UInt256.size)
    (s : Exec)
    (hcode : code.data.toList =
      pre ++ Bytecode.codeBytes (Bytecode.lowerOps rest)) :
    EVM.X s.fuel vj (injectFrame s.evm (.ofNat pre.length) [] code) =
      (run oracle rest s).map (fun s' =>
        .success
          (injectFrame s'.evm (.ofNat (code.data.toList.length - 1)) [] code)
          ByteArray.empty) := by
  induction rest generalizing pre s with
  | nil =>
      have hcode' : code.data.toList = pre ++ Bytecode.opBytes .stop ++ [] := by
        simpa [Bytecode.lowerOps, Bytecode.codeBytes] using hcode
      have hlen : code.data.toList.length - 1 = pre.length := by
        rw [hcode]
        simp [Bytecode.lowerOps, Bytecode.codeBytes, Bytecode.opBytes]
      rw [X_stop_at code vj pre.length pre [] rfl hcode' hsize [] (by simp) s,
        hlen]
      rfl
  | cons instr rest ih =>
      have hcode₁ : code.data.toList =
          pre ++ Bytecode.codeBytes (Bytecode.compileInstrOps instr) ++
            Bytecode.codeBytes (Bytecode.lowerOps rest) := by
        simpa [Bytecode.lowerOps, Bytecode.codeBytes, List.append_assoc]
          using hcode
      rw [instr_chunk code vj oracle hsound instr pre _ hcode₁ hsize s]
      cases h : execInstr oracle s instr with
      | error e => simp [run, h, Except.map]
      | ok s' =>
          dsimp only
          rw [pc_congr (show pre.length +
              (Bytecode.codeBytes (Bytecode.compileInstrOps instr)).length =
              (pre ++ Bytecode.codeBytes (Bytecode.compileInstrOps instr)).length
            by simp)]
          rw [ih (pre ++ Bytecode.codeBytes (Bytecode.compileInstrOps instr)) s'
            (by simpa [List.append_assoc] using hcode₁)]
          simp [run, h]

/-- **The lowering preservation theorem.**

For every program, initial EVM state, fuel and gas level, running the
lowered bytecode from its entry point under EVMYulLean's `EVM.X` produces
exactly the result of the IR's gas-exact semantics: the same final state
(up to the program counter, the empty machine stack, and the executing
code, which `injectFrame` pins), the same output, and the same exception
otherwise. The only assumptions are the soundness of the call oracle and
addressability of the code by a 256-bit program counter. -/
theorem lowering_correct (oracle : CallOracle) (hsound : CallOracleSound oracle)
    (program : Program) (vj : Array UInt256) (s : Exec)
    (hsize : (Bytecode.lower program).size < UInt256.size) :
    EVM.X s.fuel vj
      (injectFrame s.evm (.ofNat 0) [] (Bytecode.lower program)) =
      (run oracle program s).map (fun s' =>
        .success
          (injectFrame s'.evm (.ofNat ((Bytecode.lower program).size - 1)) []
            (Bytecode.lower program))
          ByteArray.empty) := by
  have hlist : (Bytecode.lower program).data.toList.length =
      (Bytecode.lower program).size := by
    simp [ByteArray.size]
  have hsize' : (Bytecode.lower program).data.toList.length < UInt256.size := by
    rw [hlist]; exact hsize
  have hcode : (Bytecode.lower program).data.toList =
      ([] : List UInt8) ++ Bytecode.codeBytes (Bytecode.lowerOps program) := by
    simp [Bytecode.lower]
  have h := run_simulation (Bytecode.lower program) vj oracle hsound program []
    hsize' s hcode
  rw [hlist] at h
  exact h

end Preservation

end ToyExternalCall
