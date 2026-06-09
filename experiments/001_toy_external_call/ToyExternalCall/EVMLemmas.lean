import ToyExternalCall.Bytecode

/-!
# Reusable lemmas about EVMYulLean's executable semantics

EVMYulLean is an executable specification: `EvmYul/EVM/Semantics.lean`
proves no theorems about execution. This file builds the lemma layer needed
to reason about `EVM.X` compositionally:

* arithmetic facts about `UInt256` program counters;
* projection lemmas for `injectFrame`;
* decode-at-prefix lemmas (`EVM.decode` of one-byte ops and `PUSH32`
  at an arbitrary position given a list-level decomposition of the code);
* gas-cost lemmas (`EVM.C'` and `EVM.memoryExpansionCost` of the opcodes
  produced by the lowering).
-/

namespace ToyExternalCall

open EvmYul

namespace EVMLemmas

/-! ## UInt256 arithmetic -/

theorem toNat_ofNat_of_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  simp [UInt256.ofNat, UInt256.toNat, Fin.ofNat, Id.run, Nat.mod_eq_of_lt h]

theorem ofNat_add (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  show UInt256.add _ _ = _
  simp only [UInt256.add, UInt256.ofNat, Id.run, Fin.ofNat]
  apply congrArg UInt256.mk
  apply Fin.ext
  show ((a % UInt256.size) + (b % UInt256.size)) % UInt256.size = (a + b) % UInt256.size
  conv_rhs => rw [Nat.add_mod]

/-! ## `injectFrame` projections

`injectFrame` overrides `pc`, `stack` and `executionEnv.code` and nothing
else; every other projection passes through.
-/

variable (evm : EVM.State) (pc : Word) (stk : List Word) (code : ByteArray)

@[simp] theorem injectFrame_pc : (injectFrame evm pc stk code).pc = pc := rfl

@[simp] theorem injectFrame_stack : (injectFrame evm pc stk code).stack = stk := rfl

@[simp] theorem injectFrame_code :
    (injectFrame evm pc stk code).executionEnv.code = code := rfl

@[simp] theorem injectFrame_toMachineState :
    (injectFrame evm pc stk code).toMachineState = evm.toMachineState := rfl

@[simp] theorem injectFrame_gasAvailable :
    (injectFrame evm pc stk code).gasAvailable = evm.gasAvailable := rfl

@[simp] theorem injectFrame_activeWords :
    (injectFrame evm pc stk code).activeWords = evm.activeWords := rfl

@[simp] theorem injectFrame_memory :
    (injectFrame evm pc stk code).memory = evm.memory := rfl

@[simp] theorem injectFrame_returnData :
    (injectFrame evm pc stk code).returnData = evm.returnData := rfl

@[simp] theorem injectFrame_execLength :
    (injectFrame evm pc stk code).execLength = evm.execLength := rfl

@[simp] theorem injectFrame_accountMap :
    (injectFrame evm pc stk code).accountMap = evm.accountMap := rfl

@[simp] theorem injectFrame_substate :
    (injectFrame evm pc stk code).substate = evm.substate := rfl

@[simp] theorem injectFrame_perm :
    (injectFrame evm pc stk code).executionEnv.perm = evm.executionEnv.perm := rfl

@[simp] theorem injectFrame_codeOwner :
    (injectFrame evm pc stk code).executionEnv.codeOwner = evm.executionEnv.codeOwner := rfl

@[simp] theorem injectFrame_blobVersionedHashes :
    (injectFrame evm pc stk code).executionEnv.blobVersionedHashes =
      evm.executionEnv.blobVersionedHashes := rfl

@[simp] theorem calldataload_injectFrame (v : Word) :
    EvmYul.State.calldataload (injectFrame evm pc stk code).toState v =
      EvmYul.State.calldataload evm.toState v := rfl

/-! ## Parse/serialize round-trips -/

theorem parse_serialize_stop :
    EVM.parseInstr (EVM.serializeInstr (.STOP : Operation .EVM)) = some .STOP := rfl

theorem parse_serialize_add :
    EVM.parseInstr (EVM.serializeInstr (.ADD : Operation .EVM)) = some .ADD := rfl

theorem parse_serialize_calldataload :
    EVM.parseInstr (EVM.serializeInstr (.CALLDATALOAD : Operation .EVM)) =
      some .CALLDATALOAD := rfl

theorem parse_serialize_mload :
    EVM.parseInstr (EVM.serializeInstr (.MLOAD : Operation .EVM)) = some .MLOAD := rfl

theorem parse_serialize_mstore :
    EVM.parseInstr (EVM.serializeInstr (.MSTORE : Operation .EVM)) = some .MSTORE := rfl

theorem parse_serialize_call :
    EVM.parseInstr (EVM.serializeInstr (.CALL : Operation .EVM)) = some .CALL := rfl

theorem parse_serialize_push32 :
    EVM.parseInstr (EVM.serializeInstr (.PUSH32 : Operation .EVM)) = some .PUSH32 := rfl

/-! ## Decode at a prefix -/

/-- Decode a one-byte instruction at position `l.length` of a code whose
byte list decomposes as `l ++ [serializeInstr w] ++ r`. -/
theorem decode_one_byte_at
    (code : ByteArray) (l r : List UInt8) (w : Operation .EVM)
    (hcode : code.data.toList = l ++ EVM.serializeInstr w :: r)
    (hparse : EVM.parseInstr (EVM.serializeInstr w) = some w)
    (hwidth : EVM.argOnNBytesOfInstr w = 0)
    (hl : l.length < UInt256.size) :
    EVM.decode code (.ofNat l.length) = some (w, none) := by
  unfold EVM.decode
  rw [ByteArray.get?, toNat_ofNat_of_lt hl, hcode,
    List.getElem?_append_right (Nat.le_refl _)]
  simp [hparse, hwidth]

/-- Decode a `PUSH32 v` at position `l.length` of a code whose byte list
decomposes as `l ++ opBytes (.push v) ++ r`. -/
theorem decode_push_at
    (code : ByteArray) (l r : List UInt8) (v : Word)
    (hcode : code.data.toList = l ++ Bytecode.opBytes (.push v) ++ r)
    (hl : l.length < UInt256.size) :
    EVM.decode code (.ofNat l.length) = some (.PUSH32, some (v, 32)) := by
  have hbytes : code.data.toList =
      (l ++ [Bytecode.opcode .PUSH32]) ++ ((EvmYul.toBytes! v).reverse ++ r) := by
    simpa [Bytecode.opBytes] using hcode
  have hcons : code.data.toList =
      l ++ Bytecode.opcode .PUSH32 :: ((EvmYul.toBytes! v).reverse ++ r) := by
    simpa [Bytecode.opBytes] using hcode
  have hlen32 : (EvmYul.toBytes! v).reverse.length = 32 := by
    simp [EvmYul.toBytes!_length]
  unfold EVM.decode
  rw [ByteArray.get?, toNat_ofNat_of_lt hl, hcons,
    List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some_bind,
    Bytecode.opcode, parse_serialize_push32]
  have harg : EVM.argOnNBytesOfInstr (.PUSH32 : Operation .EVM) = 32 := rfl
  have hextract :
      code.extract' l.length.succ (l.length.succ + 32) =
      ⟨⟨(EvmYul.toBytes! v).reverse⟩⟩ := by
    rw [ByteArray.extract', hbytes]
    have hdrop :
        ((l ++ [Bytecode.opcode .PUSH32]) ++ ((EvmYul.toBytes! v).reverse ++ r)).drop
          l.length.succ = (EvmYul.toBytes! v).reverse ++ r := by
      apply List.drop_left'
      simp
    have harith : l.length.succ + 32 - l.length.succ = 32 := by omega
    rw [hdrop, harith, List.take_left' hlen32]
  have hround :
      EvmYul.uInt256OfByteArray ⟨⟨(EvmYul.toBytes! v).reverse⟩⟩ = v := by
    unfold EvmYul.uInt256OfByteArray
    simp [List.reverse_reverse, EvmYul.fromBytes'_toBytes!, EvmYul.UInt256.ofNat_toNat]
  simp [parse_serialize_push32, harg, hextract, hround]

/-! ## Gas-cost lemmas -/

theorem memExp_stop (s : EVM.State) :
    EVM.memoryExpansionCost s (.STOP : Operation .EVM) = 0 := by
  unfold EVM.memoryExpansionCost
  change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  exact Nat.sub_self _

theorem memExp_push32 (s : EVM.State) :
    EVM.memoryExpansionCost s (.PUSH32 : Operation .EVM) = 0 := by
  unfold EVM.memoryExpansionCost
  change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  exact Nat.sub_self _

theorem memExp_add (s : EVM.State) :
    EVM.memoryExpansionCost s (.ADD : Operation .EVM) = 0 := by
  unfold EVM.memoryExpansionCost
  change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  exact Nat.sub_self _

theorem memExp_calldataload (s : EVM.State) :
    EVM.memoryExpansionCost s (.CALLDATALOAD : Operation .EVM) = 0 := by
  unfold EVM.memoryExpansionCost
  change EVM.Cₘ s.activeWords - EVM.Cₘ s.activeWords = 0
  exact Nat.sub_self _

theorem memExp_mload (evm : EVM.State) (pc : Word) (addr : Word) (rest : List Word)
    (code : ByteArray) :
    EVM.memoryExpansionCost (injectFrame evm pc (addr :: rest) code)
      (.MLOAD : Operation .EVM) = wordTouchCost evm addr := rfl

theorem memExp_mstore (evm : EVM.State) (pc : Word) (addr value : Word)
    (rest : List Word) (code : ByteArray) :
    EVM.memoryExpansionCost (injectFrame evm pc (addr :: value :: rest) code)
      (.MSTORE : Operation .EVM) = wordTouchCost evm addr := rfl

theorem memExp_call (evm : EVM.State) (pc : Word)
    (g t v io is oo os : Word) (rest : List Word) (code : ByteArray) :
    EVM.memoryExpansionCost
      (injectFrame evm pc (g :: t :: v :: io :: is :: oo :: os :: rest) code)
      (.CALL : Operation .EVM) = callTouchCost evm io is oo os := rfl

theorem C'_stop (s : EVM.State) :
    EVM.C' s (.STOP : Operation .EVM) = GasConstants.Gzero := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wcopy,
    EVM.InstructionGasGroups.Wextaccount]

theorem C'_push32 (s : EVM.State) :
    EVM.C' s (.PUSH32 : Operation .EVM) = GasConstants.Gverylow := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wbase,
    EVM.InstructionGasGroups.Wverylow,
    EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    EVM.InstructionGasGroups.Wcopy, EVM.InstructionGasGroups.Wextaccount]

theorem C'_add (s : EVM.State) :
    EVM.C' s (.ADD : Operation .EVM) = GasConstants.Gverylow := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wbase,
    EVM.InstructionGasGroups.Wverylow,
    EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    EVM.InstructionGasGroups.Wcopy, EVM.InstructionGasGroups.Wextaccount]

theorem C'_calldataload (s : EVM.State) :
    EVM.C' s (.CALLDATALOAD : Operation .EVM) = GasConstants.Gverylow := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wbase,
    EVM.InstructionGasGroups.Wverylow,
    EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    EVM.InstructionGasGroups.Wcopy, EVM.InstructionGasGroups.Wextaccount]

theorem C'_mload (s : EVM.State) :
    EVM.C' s (.MLOAD : Operation .EVM) = GasConstants.Gverylow := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wbase,
    EVM.InstructionGasGroups.Wverylow,
    EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    EVM.InstructionGasGroups.Wcopy, EVM.InstructionGasGroups.Wextaccount]

theorem C'_mstore (s : EVM.State) :
    EVM.C' s (.MSTORE : Operation .EVM) = GasConstants.Gverylow := by
  simp [EVM.C', EVM.InstructionGasGroups.Wzero, EVM.InstructionGasGroups.Wbase,
    EVM.InstructionGasGroups.Wverylow,
    EVM.InstructionGasGroups.Wverylow.pushInstrsWithoutZero,
    EVM.InstructionGasGroups.Wcopy, EVM.InstructionGasGroups.Wextaccount]

theorem C'_call (evm : EVM.State) (pc : Word)
    (g t v io is oo os : Word) (rest : List Word) (code : ByteArray) :
    EVM.C' (injectFrame evm pc (g :: t :: v :: io :: is :: oo :: os :: rest) code)
      (.CALL : Operation .EVM) =
    EVM.Ccall (.ofUInt256 t) (.ofUInt256 t) v g
      evm.accountMap evm.toMachineState evm.substate := rfl

/-! ## One iteration of `EVM.X`

Dispatch lemmas: an `EVM.X` iteration is determined by `decode`, `EVM.Z`,
`EVM.step` and `EVM.H`.
-/

theorem X_error_Z
    (fuel : Nat) (vj : Array UInt256) (s : EVM.State)
    (instr : Operation .EVM) (arg : Option (UInt256 × Nat)) (e : EVM.ExecutionException)
    (hdec : EVM.decode s.executionEnv.code s.pc = some (instr, arg))
    (hz : EVM.Z vj instr s = .error e) :
    EVM.X (fuel + 1) vj s = .error e := by
  conv_lhs => unfold EVM.X
  simp only [hdec, Option.getD_some, hz]

theorem X_error_step
    (fuel : Nat) (vj : Array UInt256) (s pre : EVM.State)
    (instr : Operation .EVM) (arg : Option (UInt256 × Nat)) (cost : Nat)
    (e : EVM.ExecutionException)
    (hdec : EVM.decode s.executionEnv.code s.pc = some (instr, arg))
    (hz : EVM.Z vj instr s = .ok (pre, cost))
    (hstep : EVM.step fuel cost (some (instr, arg)) pre = .error e) :
    EVM.X (fuel + 1) vj s = .error e := by
  conv_lhs => unfold EVM.X
  simp only [hdec, Option.getD_some, hz, hstep]
  rfl

theorem X_continue
    (fuel : Nat) (vj : Array UInt256) (s pre s' : EVM.State)
    (instr : Operation .EVM) (arg : Option (UInt256 × Nat)) (cost : Nat)
    (hdec : EVM.decode s.executionEnv.code s.pc = some (instr, arg))
    (hz : EVM.Z vj instr s = .ok (pre, cost))
    (hstep : EVM.step fuel cost (some (instr, arg)) pre = .ok s')
    (hhalt : EVM.H s'.toMachineState instr = none) :
    EVM.X (fuel + 1) vj s = EVM.X fuel vj s' := by
  conv_lhs => unfold EVM.X
  simp only [hdec, Option.getD_some, hz, hstep]
  change (match EVM.H s'.toMachineState instr with
    | none => EVM.X fuel vj s'
    | some o =>
      if (instr == Operation.REVERT) = true then .ok (EVM.ExecutionResult.revert s'.gasAvailable o)
      else .ok (EVM.ExecutionResult.success s' o)) =
    EVM.X fuel vj s'
  rw [hhalt]

theorem X_halt_success
    (fuel : Nat) (vj : Array UInt256) (s pre s' : EVM.State)
    (instr : Operation .EVM) (arg : Option (UInt256 × Nat)) (cost : Nat) (output : ByteArray)
    (hdec : EVM.decode s.executionEnv.code s.pc = some (instr, arg))
    (hz : EVM.Z vj instr s = .ok (pre, cost))
    (hstep : EVM.step fuel cost (some (instr, arg)) pre = .ok s')
    (hhalt : EVM.H s'.toMachineState instr = some output)
    (hnotRevert : instr ≠ .REVERT) :
    EVM.X (fuel + 1) vj s = .ok (.success s' output) := by
  conv_lhs => unfold EVM.X
  simp only [hdec, Option.getD_some, hz, hstep]
  change (match EVM.H s'.toMachineState instr with
    | none => EVM.X fuel vj s'
    | some o =>
      if (instr == Operation.REVERT) = true then .ok (EVM.ExecutionResult.revert s'.gasAvailable o)
      else .ok (EVM.ExecutionResult.success s' o)) =
    .ok (.success s' output)
  rw [hhalt]
  simp [hnotRevert]

/-! ## `EVM.Z` for the lowered opcodes -/

/-- Generic `EVM.Z` evaluation for any opcode that passes all validity
checks: only the two gas checks remain. The instruction-cost hypothesis
`hC` is stated componentwise so that it can be discharged definitionally
regardless of how the charged intermediate state is displayed. -/
theorem Z_generic (vj : Array UInt256) (w : Operation .EVM)
    (evm : EVM.State) (pc : Word) (stk : List Word) (code : ByteArray) (c₁ c₂ : Nat)
    (hmem : EVM.memoryExpansionCost (injectFrame evm pc stk code) w = c₁)
    (hC : ∀ st : EVM.State,
      st.toState = (injectFrame evm pc stk code).toState →
      st.stack = stk →
      st.toMachineState = { evm.toMachineState with
        gasAvailable := evm.gasAvailable - UInt256.ofNat c₁ } →
      EVM.C' st w = c₂)
    (hδ : EVM.δ w ≠ none)
    (hunder : ¬ (stk.length < (EVM.δ w).getD 0))
    (hover : ¬ (stk.length - (EVM.δ w).getD 0 + (EVM.α w).getD 0 > 1024))
    (hW : EVM.W w stk = false)
    (hJ : w ≠ .JUMP) (hJI : w ≠ .JUMPI) (hRD : w ≠ .RETURNDATACOPY)
    (hSS : w ≠ .SSTORE) (hCR : w.isCreate = false) :
    EVM.Z vj w (injectFrame evm pc stk code) =
      if evm.gasAvailable.toNat < c₁ then .error .OutOfGass
      else if (evm.gasAvailable - UInt256.ofNat c₁).toNat < c₂ then .error .OutOfGass
      else .ok ({ injectFrame evm pc stk code with
        gasAvailable := evm.gasAvailable - UInt256.ofNat c₁ }, c₂) := by
  unfold EVM.Z
  simp only [hmem]
  rw [hC { injectFrame evm pc stk code with
      gasAvailable := (injectFrame evm pc stk code).gasAvailable - UInt256.ofNat c₁ }
    rfl rfl rfl]
  by_cases h₁ : evm.gasAvailable.toNat < c₁
  · simp [h₁, Bind.bind, Except.bind]
  · by_cases h₂ : (evm.gasAvailable - UInt256.ofNat c₁).toNat < c₂
    · simp [h₁, h₂, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [h₁, h₂, hδ, hunder, hover, hW, hJ, hJI, hRD, hSS, hCR,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

/-! ## `EVM.step` for the lowered opcodes

Stated for an arbitrary pre-state (the state already validated and charged
by `EVM.Z`); the conclusions are plain record updates, provable by `rfl`.
-/

theorem step_push32 (f c : Nat) (v : Word) (st : EVM.State) :
    EVM.step (f + 1) c (some ((.PUSH32 : Operation .EVM), some (v, 32))) st =
      .ok { st with
        pc := st.pc + UInt256.ofNat 33,
        stack := v :: st.stack,
        execLength := st.execLength + 1,
        toMachineState := { st.toMachineState with
          gasAvailable := st.gasAvailable - UInt256.ofNat c } } := by
  unfold EVM.step
  rfl

theorem step_add (f c : Nat) (a b : Word) (rest : List Word) (st : EVM.State)
    (hstk : st.stack = a :: b :: rest) :
    EVM.step (f + 1) c (some ((.ADD : Operation .EVM), none)) st =
      .ok { st with
        pc := st.pc + UInt256.ofNat 1,
        stack := (a + b) :: rest,
        execLength := st.execLength + 1,
        toMachineState := { st.toMachineState with
          gasAvailable := st.gasAvailable - UInt256.ofNat c } } := by
  obtain ⟨shared, pc0, stk0, len0⟩ := st
  replace hstk : stk0 = _ := hstk
  subst hstk
  unfold EVM.step
  rfl

theorem step_calldataload (f c : Nat) (addr : Word) (rest : List Word) (st : EVM.State)
    (hstk : st.stack = addr :: rest) :
    EVM.step (f + 1) c (some ((.CALLDATALOAD : Operation .EVM), none)) st =
      .ok { st with
        pc := st.pc + UInt256.ofNat 1,
        stack := EvmYul.State.calldataload st.toState addr :: rest,
        execLength := st.execLength + 1,
        toMachineState := { st.toMachineState with
          gasAvailable := st.gasAvailable - UInt256.ofNat c } } := by
  obtain ⟨shared, pc0, stk0, len0⟩ := st
  replace hstk : stk0 = _ := hstk
  subst hstk
  unfold EVM.step
  rfl

theorem step_mload (f c : Nat) (addr : Word) (rest : List Word) (st : EVM.State)
    (hstk : st.stack = addr :: rest) :
    EVM.step (f + 1) c (some ((.MLOAD : Operation .EVM), none)) st =
      let m := { st.toMachineState with gasAvailable := st.gasAvailable - UInt256.ofNat c }
      .ok { st with
        pc := st.pc + UInt256.ofNat 1,
        stack := (m.mload addr).1 :: rest,
        execLength := st.execLength + 1,
        toMachineState := (m.mload addr).2 } := by
  obtain ⟨shared, pc0, stk0, len0⟩ := st
  replace hstk : stk0 = _ := hstk
  subst hstk
  unfold EVM.step
  rfl

theorem step_mstore (f c : Nat) (addr v : Word) (rest : List Word) (st : EVM.State)
    (hstk : st.stack = addr :: v :: rest) :
    EVM.step (f + 1) c (some ((.MSTORE : Operation .EVM), none)) st =
      let m := { st.toMachineState with gasAvailable := st.gasAvailable - UInt256.ofNat c }
      .ok { st with
        pc := st.pc + UInt256.ofNat 1,
        stack := rest,
        execLength := st.execLength + 1,
        toMachineState := m.mstore addr v } := by
  obtain ⟨shared, pc0, stk0, len0⟩ := st
  replace hstk : stk0 = _ := hstk
  subst hstk
  unfold EVM.step
  rfl

theorem step_call (f c : Nat) (g t v io is oo os : Word) (rest : List Word)
    (shared : SharedState .EVM) (pc0 : UInt256) (len0 : Nat) :
    EVM.step (f + 1) c (some ((.CALL : Operation .EVM), none))
      (⟨shared, pc0, g :: t :: v :: io :: is :: oo :: os :: rest, len0⟩ : EVM.State) =
      (EVM.call f c shared.toState.executionEnv.blobVersionedHashes g
        (.ofNat shared.toState.executionEnv.codeOwner) t t v v io is oo os
        shared.toState.executionEnv.perm
        (⟨shared, pc0, g :: t :: v :: io :: is :: oo :: os :: rest, len0 + 1⟩ : EVM.State)).map
        (fun p => { p.2 with pc := p.2.pc + UInt256.ofNat 1, stack := p.1 :: rest }) := by
  have key : ∀ x : Except EVM.ExecutionException (UInt256 × EVM.State),
      (x >>= fun p =>
        Except.ok (EVM.State.replaceStackAndIncrPC p.2 (Stack.push rest p.1))) =
      x.map (fun p => { p.2 with pc := p.2.pc + UInt256.ofNat 1, stack := p.1 :: rest }) := by
    intro x
    cases x with
    | error e => rfl
    | ok p => rfl
  exact key (EVM.call f c shared.toState.executionEnv.blobVersionedHashes g
    (.ofNat shared.toState.executionEnv.codeOwner) t t v v io is oo os
    shared.toState.executionEnv.perm
    (⟨shared, pc0, g :: t :: v :: io :: is :: oo :: os :: rest, len0 + 1⟩ : EVM.State))

end EVMLemmas

end ToyExternalCall
