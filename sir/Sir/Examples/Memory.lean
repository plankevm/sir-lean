import Sir.Vars.Spec
import Sir.Vars.Proofs.Steps
import Sir.Machine.Proofs.Memory
import BytecodeLayer.Semantics.Maps

namespace Sir.Examples

private abbrev sizeVar : VarId := ⟨0⟩
private abbrev xVar : VarId := ⟨1⟩
private abbrev valueVar : VarId := ⟨2⟩
private abbrev zVar : VarId := ⟨3⟩

private abbrev entryBlock : BlockId := ⟨0⟩
private abbrev entryFunction : FunctionId := ⟨0⟩

def initializedLoad : Vars.Program :=
  { init := {
      entry := {
        inputs := #[]
        statements := #[
          .assign sizeVar (.constant 32),
          .mallocUninit xVar sizeVar,
          .assign valueVar (.constant 42),
          .mstore32 xVar valueVar,
          .mload32 zVar xVar,
          .sstore zVar zVar]
        terminator := .halt
        outputs := #[]}
      rest := #[] }
    main := none
    rest := #[] }

def zeroSizeStore : Vars.Program :=
  { init := {
      entry := {
        inputs := #[]
        statements := #[
          .assign sizeVar (.constant 0),
          .mallocUninit xVar sizeVar,
          .sstore xVar xVar]
        terminator := .halt
        outputs := #[]}
      rest := #[] }
    main := none
    rest := #[] }

private theorem fold_set_get? {α : Type} (xs : List α) (start j : Nat) (dest : Array α)
    (hbound : start + xs.length ≤ dest.size) :
    ((xs.zipIdx start).foldl (fun a x => a.setIfInBounds x.2 x.1) dest)[j]? =
      if start ≤ j ∧ j < start + xs.length then xs[j - start]? else dest[j]? := by
  induction xs generalizing start dest with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons] at hbound
      rw [List.zipIdx_cons, List.foldl_cons,
        ih (start + 1) (dest.setIfInBounds start x) (by simp only [Array.size_setIfInBounds]; omega)]
      by_cases heq : start = j
      · subst j
        simp [show start < dest.size by omega]
      · by_cases hle : start ≤ j
        · have hnext : start + 1 ≤ j := by omega
          simp only [List.length_cons]
          by_cases hrange : j < start + 1 + xs.length
          · rw [if_pos ⟨hnext, hrange⟩, if_pos ⟨hle, by omega⟩]
            rw [show j - start = (j - (start + 1)) + 1 by omega]
            rfl
          · rw [if_neg (by simp [hrange]), if_neg (by intro h; apply hrange; omega)]
            simp [heq]
        · have hnext : ¬start + 1 ≤ j := by omega
          simp [heq, hle, hnext]

private theorem fold_set_size {α : Type} (xs : List (α × Nat)) (dest : Array α) :
    (xs.foldl (fun a x => a.setIfInBounds x.2 x.1) dest).size = dest.size := by
  induction xs generalizing dest with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem fold_set_zipIdx_eq {α : Type} (source dest : Array α)
    (hsize : dest.size = source.size) :
    source.toList.zipIdx.foldl (fun a x => a.setIfInBounds x.2 x.1) dest = source := by
  apply Array.ext
  · rw [fold_set_size, hsize]
  · intro i hi₁ hi₂
    have hget := fold_set_get? source.toList 0 i dest (by simp [hsize])
    simp [hi₂] at hget
    simpa only [Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂,
      Option.some.injEq] using hget


private def singletonMemory (alloc : Allocation) (data : Array UInt8) : MemoryState :=
  { provisioned := #[{ alloc with bytes := ⟨data⟩ }] }

private theorem writeByte_singleton (alloc : Allocation) (data : Array UInt8)
    (index : Nat) (byte : UInt8) :
    (singletonMemory alloc data).writeByte (alloc.start + index) byte =
      singletonMemory alloc (data.setIfInBounds index byte) := by
  have hc :
      alloc.start ≤ alloc.start + index ∧ alloc.start + index < alloc.start + data.size ↔
        index < data.size := by omega
  simp [singletonMemory, MemoryState.writeByte, Allocation.writeByte,
    Allocation.start, Allocation.endExclusive, Allocation.size]
  intro hle
  rw [Array.setIfInBounds_eq_of_size_le hle]

private theorem writeBytes_singleton (alloc : Allocation) (bytes : ByteArray)
    (hsize : alloc.bytes.size = bytes.size) :
    (MemoryState.empty.push alloc).writeBytes alloc.offset bytes =
      singletonMemory alloc bytes.data := by
  unfold MemoryState.writeBytes MemoryState.empty MemoryState.push
  change bytes.toList.zipIdx.foldl _ (singletonMemory alloc alloc.bytes.data) = _
  rw [List.foldl_hom (singletonMemory alloc)
    (g₁ := fun data x => data.setIfInBounds x.2 x.1)]
  · rw [toList_eq_data_toList]
    rw [fold_set_zipIdx_eq bytes.data alloc.bytes.data (by simpa using hsize)]
  · intro data x
    exact writeByte_singleton alloc data x.2 x.1

private theorem readBytes_singleton (alloc : Allocation) (bytes assumed : ByteArray)
    (hsize : assumed.size = bytes.size) :
    (singletonMemory alloc bytes.data).readBytes alloc.offset assumed = bytes := by
  unfold MemoryState.readBytes
  have hround : bytes.toList.toByteArray = bytes := by
    apply ByteArray.ext
    rw [List.data_toByteArray, toList_eq_data_toList]
  conv_rhs => rw [← hround]
  apply congrArg List.toByteArray
  apply List.ext_getElem
  · simpa [toList_eq_data_toList] using hsize
  · intro i hout hbytes
    have hi : i < bytes.size := by
      simpa [toList_eq_data_toList] using hbytes
    simp [MemoryState.readByte?, singletonMemory, Allocation.readByte?, Allocation.start,
      Allocation.endExclusive, Allocation.size,
      toList_eq_data_toList, ByteArray.get?, hi]
    rfl

private theorem read_written_word (alloc : Allocation)
    (hsize : alloc.size = 32) (assumed : Vector UInt8 32) :
    ((MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray).readBytes
      alloc.offset ⟨assumed.toArray⟩ = (42 : Word).toByteArray := by
  rw [writeBytes_singleton]
  · apply readBytes_singleton
    change assumed.toArray.size = (42 : Word).toByteArray.size
    rw [assumed.size_toArray, toByteArray_size]
  · simpa [toByteArray_size] using hsize

private theorem initialized_store_in_bounds (alloc : Allocation) (hsize : alloc.size = 32) :
    (MemoryState.empty.push alloc).InBounds alloc.offset.toNat 32 := by
  refine ⟨alloc, by simp [MemoryState.empty, MemoryState.push], ?_⟩
  exact ⟨Nat.le_refl _, by simp [Allocation.endExclusive, Allocation.start, hsize]⟩

private def stmtControl (index : Nat) : Machine.MachineControl :=
  .running { fn := entryFunction, block := entryBlock, position := .statement index }

private def termControl : Machine.MachineControl :=
  .running { fn := entryFunction, block := entryBlock, position := .terminator }

private def locals1 : Locals := Locals.empty.assign sizeVar 32
private def locals2 (alloc : Allocation) : Locals := locals1.assign xVar alloc.offset
private def locals3 (alloc : Allocation) : Locals := (locals2 alloc).assign valueVar 42
private def locals5 (alloc : Allocation) : Locals := (locals3 alloc).assign zVar 42

private def initializedState0 (world : World) : Vars.State :=
  { globals := { world }, environment := .empty, control := stmtControl 0 }

private def initializedState1 (world : World) : Vars.State :=
  { globals := { world }, environment := locals1, control := stmtControl 1 }

private def initializedState2 (world : World) (alloc : Allocation) : Vars.State :=
  { globals := { world, memory := MemoryState.empty.push alloc }
    environment := locals2 alloc
    control := stmtControl 2 }

private def initializedState3 (world : World) (alloc : Allocation) : Vars.State :=
  { globals := { world, memory := MemoryState.empty.push alloc }
    environment := locals3 alloc
    control := stmtControl 3 }

private def initializedState4 (world : World) (alloc : Allocation) : Vars.State :=
  { globals :=
      { world
        memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray }
    environment := locals3 alloc
    control := stmtControl 4 }

private def initializedState5 (world : World) (alloc : Allocation) : Vars.State :=
  { globals :=
      { world
        memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray }
    environment := locals5 alloc
    control := stmtControl 5 }

private def initializedState6 (ctx : CallContext) (world : World) (alloc : Allocation) : Vars.State :=
  { globals :=
      { world := world.storeStorage ctx.self 42 42
        memory := (MemoryState.empty.push alloc).writeBytes alloc.offset (42 : Word).toByteArray }
    environment := locals5 alloc
    control := termControl }

private def initializedState7 (ctx : CallContext) (world : World) (alloc : Allocation) : Vars.State :=
  { initializedState6 ctx world alloc with control := .halted }

private inductive InitializedReachable (ctx : CallContext) (world : World) : Vars.State → Prop where
  | state0 : InitializedReachable ctx world (initializedState0 world)
  | state1 : InitializedReachable ctx world (initializedState1 world)
  | state2 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState2 world alloc)
  | state3 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState3 world alloc)
  | state4 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState4 world alloc)
  | state5 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState5 world alloc)
  | state6 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState6 ctx world alloc)
  | state7 (alloc : Allocation) (hsize : alloc.size = 32) :
      InitializedReachable ctx world (initializedState7 ctx world alloc)

private theorem bindValues_empty (locals : Locals) :
    Locals.bindValues locals #[] #[] = .ok locals := by
  simp [Locals.bindValues, bind, Except.bind, pure, Except.pure]

private theorem bindValues_singleton (locals : Locals) (var : VarId) (value : Word) :
    Locals.bindValues locals #[var] #[value] = .ok (locals.assign var value) := by
  simp [Locals.bindValues, bind, Except.bind, pure, Except.pure]

private theorem next_inj {results results' : Array Word} {globals globals' : Globals}
    {trace trace' : Trace}
    (h : (Except.ok (.next results globals trace) : Except IRError Machine.Operation.Outcome) =
      .ok (.next results' globals' trace')) :
    results = results' ∧ globals = globals' ∧ trace = trace' := by
  injection h with h
  injection h with h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

private theorem decode_statement0 :
    (Vars.decoder initializedLoad).decode (stmtControl 0) =
      some (⟨Machine.Instruction.Kind.primitive (.constant 32), #[], #[sizeVar]⟩,
        stmtControl 1) := rfl

private theorem decode_statement1 :
    (Vars.decoder initializedLoad).decode (stmtControl 1) =
      some (⟨Machine.Instruction.Kind.primitive .mallocUninit, #[sizeVar], #[xVar]⟩,
        stmtControl 2) := rfl

private theorem decode_statement2 :
    (Vars.decoder initializedLoad).decode (stmtControl 2) =
      some (⟨Machine.Instruction.Kind.primitive (.constant 42), #[], #[valueVar]⟩,
        stmtControl 3) := rfl

private theorem decode_statement3 :
    (Vars.decoder initializedLoad).decode (stmtControl 3) =
      some (⟨Machine.Instruction.Kind.primitive .mstore32, #[xVar, valueVar], #[]⟩,
        stmtControl 4) := rfl

private theorem decode_statement4 :
    (Vars.decoder initializedLoad).decode (stmtControl 4) =
      some (⟨Machine.Instruction.Kind.primitive .mload32, #[xVar], #[zVar]⟩,
        stmtControl 5) := rfl

private theorem decode_statement5 :
    (Vars.decoder initializedLoad).decode (stmtControl 5) =
      some (⟨Machine.Instruction.Kind.primitive .sstore, #[zVar, zVar], #[]⟩,
        termControl) := rfl

private theorem control_statement (index : Nat) (env : Locals) (globals : Globals) :
    (Vars.decoder initializedLoad).control env globals (stmtControl index) = none := rfl

private theorem decode_terminator :
    (Vars.decoder initializedLoad).decode termControl = none := rfl

private theorem control_terminator (env : Locals) (globals : Globals) :
    (Vars.decoder initializedLoad).control env globals termControl =
      some ([], env, globals, .halted) := rfl

private theorem decode_halted :
    (Vars.decoder initializedLoad).decode .halted = none := rfl

private theorem control_halted (env : Locals) (globals : Globals) :
    (Vars.decoder initializedLoad).control env globals .halted = none := rfl

private theorem primitive_step_inv {ctx : CallContext} {operation : Machine.Operation}
    {src dst : Array VarId} {control control' : Machine.MachineControl}
    {state final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      state trace final)
    (hstate : state.control = control)
    (hdecode : (Vars.decoder initializedLoad).decode control =
      some (⟨Machine.Instruction.Kind.primitive operation, src, dst⟩, control'))
    (hcontrol : ∀ env globals,
      (Vars.decoder initializedLoad).control env globals control = none) :
    ∃ (operands results : Array Word) (globals' : Globals) (locals' : Locals)
      (oracle : operation.Oracle),
      operation.Admissible Machine.memoryPolicy state.globals operands oracle ∧
      src.mapM state.environment.lookup = .ok operands ∧
      operation.execute ctx oracle state.globals operands =
        .ok (.next results globals' trace) ∧
      Locals.bindValues state.environment dst results = .ok locals' ∧
      final = { globals := globals', environment := locals', control := control' } := by
  cases hstep with
  | operation hdec hfires =>
      rw [hstate, hdecode] at hdec
      simp only [Option.some.injEq, Prod.mk.injEq, Machine.Instruction.mk.injEq,
        Machine.Instruction.Kind.primitive.injEq] at hdec
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hdec
      cases hfires with
      | next hadmissible hfetch hexecute hstore =>
          exact ⟨_, _, _, _, _, hadmissible, hfetch, hexecute, hstore, rfl⟩
  | operationHalted _ hfires => exact (Machine.OperandFrame.firesHalt_false _ hfires).elim
  | internalCall hdec _ _ _ =>
      rw [hstate, hdecode] at hdec
      simp at hdec
  | control hctl =>
      rw [hstate, hcontrol] at hctl
      simp at hctl

private theorem control_step_inv {ctx : CallContext} {control : Machine.MachineControl}
    {state final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      state trace final)
    (hstate : state.control = control)
    (hdecode : (Vars.decoder initializedLoad).decode control = none) :
    (Vars.decoder initializedLoad).control state.environment state.globals control =
      some (trace, final.environment, final.globals, final.control) := by
  cases hstep with
  | operation hdec _ => rw [hstate, hdecode] at hdec; simp at hdec
  | operationHalted hdec _ => rw [hstate, hdecode] at hdec; simp at hdec
  | internalCall hdec _ _ _ => rw [hstate, hdecode] at hdec; simp at hdec
  | control hctl => rw [hstate] at hctl; exact hctl

private theorem fetch_none (locals : Locals) :
    (#[] : Array VarId).mapM locals.lookup = .ok #[] := by
  rw [Array.mapM_eq_mapM_toList]; rfl

private theorem fetch_size (world : World) :
    #[sizeVar].mapM (initializedState1 world).environment.lookup = .ok #[(32 : Word)] := by
  rw [Array.mapM_eq_mapM_toList]; rfl

private theorem fetch_offset_value (world : World) (alloc : Allocation) :
    #[xVar, valueVar].mapM (initializedState3 world alloc).environment.lookup =
      .ok #[alloc.offset, (42 : Word)] := by
  rw [Array.mapM_eq_mapM_toList]; rfl

private theorem fetch_offset (world : World) (alloc : Allocation) :
    #[xVar].mapM (initializedState4 world alloc).environment.lookup = .ok #[alloc.offset] := by
  rw [Array.mapM_eq_mapM_toList]; rfl

private theorem fetch_loaded (world : World) (alloc : Allocation) :
    #[zVar, zVar].mapM (initializedState5 world alloc).environment.lookup =
      .ok #[(42 : Word), (42 : Word)] := by
  rw [Array.mapM_eq_mapM_toList]; rfl

private theorem initialized_step0 {ctx : CallContext} {world : World}
    {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState0 world) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨operands, results, globals', locals', oracle, -, hfetch, hexecute, hstore, rfl⟩ :=
    primitive_step_inv hstep (by rfl) decode_statement0 (control_statement 0)
  obtain rfl := Except.ok.inj ((fetch_none _).symm.trans hfetch)
  obtain ⟨rfl, rfl, rfl⟩ := next_inj
    ((show Machine.Operation.execute ctx (.constant 32) oracle (initializedState0 world).globals
        #[] =
        .ok (.next #[(32 : Word)] (initializedState0 world).globals []) from
      rfl).symm.trans hexecute)
  obtain rfl := Except.ok.inj ((bindValues_singleton _ _ _).symm.trans hstore)
  exact ⟨rfl, .state1⟩

private theorem initialized_step1 {ctx : CallContext} {world : World}
    {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState1 world) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨operands, results, globals', locals', alloc, hadmissible, hfetch, hexecute,
      hstore, rfl⟩ :=
    primitive_step_inv hstep (by rfl) decode_statement1 (control_statement 1)
  obtain rfl := Except.ok.inj ((fetch_size world).symm.trans hfetch)
  obtain ⟨size, hoperand, -, -, hsize⟩ := hadmissible
  obtain rfl := (Option.some.inj hoperand).symm
  obtain ⟨rfl, rfl, rfl⟩ := next_inj
    ((Machine.Operation.execute_mallocUninit_ok ctx alloc (initializedState1 world).globals 32
      hsize).symm.trans hexecute)
  obtain rfl := Except.ok.inj ((bindValues_singleton _ _ _).symm.trans hstore)
  exact ⟨rfl, .state2 alloc hsize⟩

private theorem initialized_step2 {ctx : CallContext} {world : World} {alloc : Allocation}
    (hsize : alloc.size = 32) {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState2 world alloc) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨operands, results, globals', locals', oracle, -, hfetch, hexecute, hstore, rfl⟩ :=
    primitive_step_inv hstep (by rfl) decode_statement2 (control_statement 2)
  obtain rfl := Except.ok.inj ((fetch_none _).symm.trans hfetch)
  obtain ⟨rfl, rfl, rfl⟩ := next_inj
    ((show Machine.Operation.execute ctx (.constant 42) oracle
        (initializedState2 world alloc).globals #[] =
        .ok (.next #[(42 : Word)] (initializedState2 world alloc).globals []) from
      rfl).symm.trans hexecute)
  obtain rfl := Except.ok.inj ((bindValues_singleton _ _ _).symm.trans hstore)
  exact ⟨rfl, .state3 alloc hsize⟩

private theorem initialized_step3 {ctx : CallContext} {world : World} {alloc : Allocation}
    (hsize : alloc.size = 32) {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState3 world alloc) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨operands, results, globals', locals', oracle, -, hfetch, hexecute, hstore, rfl⟩ :=
    primitive_step_inv hstep (by rfl) decode_statement3 (control_statement 3)
  obtain rfl := Except.ok.inj ((fetch_offset_value world alloc).symm.trans hfetch)
  obtain ⟨rfl, rfl, rfl⟩ := next_inj
    ((Machine.Operation.execute_mstore32_ok ctx (initializedState3 world alloc).globals
      alloc.offset 42 (initialized_store_in_bounds alloc hsize)).symm.trans hexecute)
  obtain rfl := Except.ok.inj ((bindValues_empty _).symm.trans hstore)
  exact ⟨rfl, .state4 alloc hsize⟩

private theorem initialized_step4 {ctx : CallContext} {world : World} {alloc : Allocation}
    (hsize : alloc.size = 32) {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState4 world alloc) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨operands, results, globals', locals', assumed, -, hfetch, hexecute, hstore, rfl⟩ :=
    primitive_step_inv hstep (by rfl) decode_statement4 (control_statement 4)
  obtain rfl := Except.ok.inj ((fetch_offset world alloc).symm.trans hfetch)
  have hload : Machine.Operation.execute ctx .mload32 assumed
      ({ world := world,
         memory := (MemoryState.empty.push alloc).writeBytes alloc.offset
           (42 : Word).toByteArray } : Globals) #[alloc.offset] =
      .ok (.next #[(42 : Word)]
        { world := world,
          memory := (MemoryState.empty.push alloc).writeBytes alloc.offset
            (42 : Word).toByteArray } []) := by
    rw [Machine.Operation.execute_mload32_ok, read_written_word alloc hsize,
      fromByteArray_toByteArray, ofNat_toNat]
  obtain ⟨rfl, rfl, rfl⟩ := next_inj (hload.symm.trans hexecute)
  obtain rfl := Except.ok.inj ((bindValues_singleton _ _ _).symm.trans hstore)
  exact ⟨rfl, .state5 alloc hsize⟩

private theorem initialized_step5 {ctx : CallContext} {world : World} {alloc : Allocation}
    (hsize : alloc.size = 32) {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState5 world alloc) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨operands, results, globals', locals', oracle, -, hfetch, hexecute, hstore, rfl⟩ :=
    primitive_step_inv hstep (by rfl) decode_statement5 (control_statement 5)
  obtain rfl := Except.ok.inj ((fetch_loaded world alloc).symm.trans hfetch)
  obtain ⟨rfl, rfl, rfl⟩ := next_inj
    ((Machine.Operation.execute_sstore_ok ctx 42 42
      (initializedState5 world alloc).globals).symm.trans hexecute)
  obtain rfl := Except.ok.inj ((bindValues_empty _).symm.trans hstore)
  exact ⟨rfl, .state6 alloc hsize⟩

private theorem initialized_step6 {ctx : CallContext} {world : World} {alloc : Allocation}
    (hsize : alloc.size = 32) {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState6 ctx world alloc) trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  obtain ⟨fglobals, fenv, fcontrol⟩ := final
  have hcontrol := control_step_inv hstep (by rfl) decode_terminator
  rw [control_terminator] at hcontrol
  simp only [Option.some.injEq, Prod.mk.injEq] at hcontrol
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hcontrol
  exact ⟨rfl, .state7 alloc hsize⟩

private theorem initialized_step7 {ctx : CallContext} {world : World} {alloc : Allocation}
    {final : Vars.State} {trace : Trace}
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState7 ctx world alloc) trace final) : False := by
  have hcontrol := control_step_inv hstep (by rfl) decode_halted
  rw [control_halted] at hcontrol
  simp at hcontrol

private theorem initialized_step_closed {ctx : CallContext} {world : World}
    {state final : Vars.State} {trace : Trace}
    (hstate : InitializedReachable ctx world state)
    (hstep : Machine.Step Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      state trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  cases hstate with
  | state0 => exact initialized_step0 hstep
  | state1 => exact initialized_step1 hstep
  | state2 alloc hsize => exact initialized_step2 hsize hstep
  | state3 alloc hsize => exact initialized_step3 hsize hstep
  | state4 alloc hsize => exact initialized_step4 hsize hstep
  | state5 alloc hsize => exact initialized_step5 hsize hstep
  | state6 alloc hsize => exact initialized_step6 hsize hstep
  | state7 alloc hsize => exact (initialized_step7 hstep).elim

private theorem initialized_steps_from {ctx : CallContext} {world : World}
    {start final : Vars.State} {trace : Trace}
    (hstart : InitializedReachable ctx world start)
    (hsteps : Machine.Steps Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      start trace final) :
    trace = [] ∧ InitializedReachable ctx world final := by
  apply Machine.Steps.inductionOn
    (motive := fun state trace final _ =>
      InitializedReachable ctx world state →
        trace = [] ∧ InitializedReachable ctx world final)
    (fun _ hstate => ⟨rfl, hstate⟩)
    (fun steps next ih hstate => by
      rcases ih hstate with ⟨rfl, hmiddle⟩
      rcases initialized_step_closed hmiddle next with ⟨rfl, hfinal⟩
      exact ⟨rfl, hfinal⟩)
    hsteps hstart

private theorem initialized_steps {ctx : CallContext} {world : World}
    {trace : Trace} {state : Vars.State}
    (hsteps : Machine.Steps Vars.frame (Vars.decoder initializedLoad) Machine.memoryPolicy ctx
      (initializedState0 world) trace state) :
    trace = [] ∧ InitializedReachable ctx world state :=
  initialized_steps_from .state0 hsteps

private theorem initialized_entry (world : World) :
    initializedLoad.callState? entryFunction { world := world } #[] =
      some (initializedState0 world) := by
  apply Vars.Program.callState?_eq_some_iff.mpr
  refine ⟨_, Locals.empty, rfl, ?_, rfl⟩
  simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
    Array.toList_zip]
  rfl

private theorem initialized_no_next_event {ctx : CallContext} {world : World}
    {trace history rest : Trace} {event : Event} {state : Vars.State}
    (hrun : initializedLoad.RunsFunction ctx entryFunction { world := world } #[] trace state)
    (htrace : trace = history ++ event :: rest) : False := by
  obtain ⟨initial, hentry, hsteps⟩ := hrun
  have : initial = initializedState0 world := Option.some.inj
    (hentry.symm.trans (initialized_entry world))
  subst initial
  have hnil := (initialized_steps hsteps).1
  rw [htrace] at hnil
  have := congrArg List.length hnil
  simp at this

private theorem initialized_halted_world {ctx : CallContext} {world : World}
    {trace : Trace} {globals : Globals}
    (hrun : Vars.EvalFn initializedLoad ctx
      entryFunction { world := world } #[] trace globals .halted) :
    trace = [] ∧ globals.world = world.storeStorage ctx.self 42 42 := by
  cases hrun with
  | exit hentry hsteps hhalt =>
      rename_i initial exit
      have hinitial : initial = initializedState0 world := Option.some.inj
        (hentry.symm.trans (by simp [Vars.entry_eq, initialized_entry]))
      subst initial
      obtain ⟨exitGlobals, exitLocals, exitControl⟩ := exit
      rcases initialized_steps hsteps with ⟨htrace, hstate⟩
      refine ⟨htrace, ?_⟩
      change exitControl = .halted at hhalt
      cases hstate <;> simp [initializedState6, stmtControl, termControl] at hhalt ⊢


private def zeroAlloc (offset : Word) : Allocation :=
  { offset, bytes := ByteArray.empty }

private def zeroState0 (world : World) : Vars.State :=
  { globals := { world }, environment := .empty, control := stmtControl 0 }

private def zeroState1 (world : World) : Vars.State :=
  { globals := { world }, environment := Locals.empty.assign sizeVar 0, control := stmtControl 1 }

private def zeroState2 (world : World) (offset : Word) : Vars.State :=
  { globals := { world, memory := MemoryState.empty.push (zeroAlloc offset) }
    environment := (Locals.empty.assign sizeVar 0).assign xVar offset
    control := stmtControl 2 }

private def zeroState2Eval (world : World) (offset : Word) : Vars.State :=
  { globals := { world, memory := MemoryState.empty.push (zeroAlloc offset) }
    environment := (Locals.empty.assign sizeVar 0).assign xVar offset
    control := stmtControl 1 }

private def zeroState3 (ctx : CallContext) (world : World) (offset : Word) : Vars.State :=
  { zeroState2 world offset with
    globals := { (zeroState2 world offset).globals with
      world := world.storeStorage ctx.self offset offset }
    control := termControl }

private def zeroState4 (ctx : CallContext) (world : World) (offset : Word) : Vars.State :=
  { zeroState3 ctx world offset with control := .halted }

private theorem zero_entry (world : World) :
    zeroSizeStore.callState? entryFunction { world := world } #[] = some (zeroState0 world) := by
  apply Vars.Program.callState?_eq_some_iff.mpr
  refine ⟨_, Locals.empty, rfl, ?_, rfl⟩
  simp only [Locals.bindParams, Locals.bindValues, ← Array.forIn_toList,
    Array.toList_zip]
  rfl

private theorem zero_steps (ctx : CallContext) (world : World) (offset : Word) :
    Machine.Steps Vars.frame (Vars.decoder zeroSizeStore) Machine.memoryPolicy ctx
      (zeroState0 world) [] (zeroState4 ctx world offset) := by
  have hfetchEmpty : (#[] : Array VarId).mapM ((zeroState0 world).environment.lookup ·) =
      .ok #[] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreSize : Locals.bindValues (zeroState0 world).environment #[sizeVar] #[0] =
      .ok (zeroState1 world).environment := by
    simp only [zeroState0, zeroState1, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have step01 : Machine.Step Vars.frame (Vars.decoder zeroSizeStore) Machine.memoryPolicy ctx
      (zeroState0 world) [] (zeroState1 world) := by
    apply step_assign (program := zeroSizeStore) (ctx := ctx)
      (result := sizeVar) (expr := .constant 0)
      (by simp [zeroSizeStore, Vars.Program.decodeStmt, Vars.Program.block?,
        Vars.Program.function?, Vars.Program.functions, Vars.Function.block?,
        Vars.Function.blocks, Vars.Block.absoluteToPosition, zeroState0, stmtControl])
    simp only [Vars.decodeExpression, Machine.Instruction.Fires]
    exact fires_of hfetchEmpty (by trivial)
      (Machine.Operation.execute_constant_ok ctx 0 (zeroState0 world).globals #[]) hstoreSize
  have hfetchSize : #[sizeVar].mapM ((zeroState1 world).environment.lookup ·) = .ok #[0] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreOffset : Locals.bindValues (zeroState1 world).environment #[xVar] #[offset] =
      .ok (zeroState2 world offset).environment := by
    simp only [zeroState1, zeroState2, Locals.bindValues, ← Array.forIn_toList,
      Array.toList_zip]
    rfl
  have hvalid : (zeroState1 world).globals.memory.IsValidNewAlloc (zeroAlloc offset) := by
    constructor
    · change offset.toBitVec.toNat ≤ 2 ^ 256
      exact offset.toBitVec.isLt.le
    · simp [zeroState1, MemoryState.empty]
  have hsize : (zeroAlloc offset).size = (0 : Word).toNat := by
    change 0 = (0 : Word).toNat
    decide
  have step12 : Machine.Step Vars.frame (Vars.decoder zeroSizeStore) Machine.memoryPolicy ctx
      (zeroState1 world) [] (zeroState2 world offset) := by
    apply step_mallocUninit (program := zeroSizeStore) (ctx := ctx)
      (result := xVar) (size := sizeVar)
      (by simp [zeroSizeStore, Vars.Program.decodeStmt, Vars.Program.block?,
        Vars.Program.function?, Vars.Program.functions, Vars.Function.block?,
        Vars.Function.blocks, Vars.Block.absoluteToPosition, zeroState1, stmtControl])
    simp only [Vars.decodeStatement, Machine.Instruction.Fires]
    exact fires_of hfetchSize ⟨0, rfl, ⟨hvalid, hsize⟩, hvalid, hsize⟩
      (Machine.Operation.execute_mallocUninit_ok ctx (zeroAlloc offset)
        (zeroState1 world).globals 0 hsize) hstoreOffset
  have hfetchOffset : #[xVar, xVar].mapM ((zeroState2 world offset).environment.lookup ·) =
      .ok #[offset, offset] := by
    rw [Array.mapM_eq_mapM_toList]
    rfl
  have hstoreEmpty : Locals.bindValues (zeroState2 world offset).environment #[] #[] =
      .ok (zeroState2 world offset).environment := by
    simp only [Locals.bindValues, ← Array.forIn_toList, Array.toList_zip]
    rfl
  have step23 : Machine.Step Vars.frame (Vars.decoder zeroSizeStore) Machine.memoryPolicy ctx
      (zeroState2 world offset) [] (zeroState3 ctx world offset) := by
    apply step_sstore (program := zeroSizeStore) (ctx := ctx)
      (key := xVar) (value := xVar)
      (by simp [zeroSizeStore, Vars.Program.decodeStmt, Vars.Program.block?,
        Vars.Program.function?, Vars.Program.functions, Vars.Function.block?,
        Vars.Function.blocks, Vars.Block.absoluteToPosition, zeroState2, stmtControl, termControl])
    simp only [Vars.decodeStatement, Machine.Instruction.Fires]
    exact fires_of hfetchOffset (by trivial)
      (Machine.Operation.execute_sstore_ok ctx offset offset (zeroState2 world offset).globals)
      hstoreEmpty
  have step34 : Machine.Step Vars.frame (Vars.decoder zeroSizeStore) Machine.memoryPolicy ctx
      (zeroState3 ctx world offset) [] (zeroState4 ctx world offset) :=
    step_terminator (terminator := .halt)
      (by simp [zeroSizeStore, Vars.Program.terminatorAt, Vars.Program.block?,
        Vars.Program.function?, Vars.Program.functions, Vars.Function.block?,
        Vars.Function.blocks, zeroState3, termControl])
      (by simp [Vars.evaluateTerminator, zeroState3, zeroState4, pure, Except.pure])
  exact .tail (.tail (.tail (.tail .refl step01) step12) step23) step34

private theorem zero_eval (ctx : CallContext) (world : World) (offset : Word) :
    Vars.EvalFn zeroSizeStore ctx
      entryFunction { world := world } #[] [] (zeroState4 ctx world offset).globals .halted :=
  Vars.EvalFn.halted (zero_entry world) (zero_steps ctx world offset) rfl

private def zeroContext : CallContext :=
  { self := 0, caller := 0, value := 0, calldata := ByteArray.empty, isStatic := false }

private theorem zero_worlds_differ :
    (default : World).storeStorage zeroContext.self 1 1 ≠
      (default : World).storeStorage zeroContext.self 2 2 := by
  intro heq
  have hread := congrArg (fun world => world.loadStorage zeroContext.self 1) heq
  dsimp only at hread
  have hleft :
      ((default : World).storeStorage zeroContext.self 1 1).loadStorage
        zeroContext.self 1 = 1 := by decide
  have hright :
      ((default : World).storeStorage zeroContext.self 2 2).loadStorage
        zeroContext.self 1 = 0 := by decide
  rw [hleft, hright] at hread
  exact (by decide : (1 : Word) ≠ 0) hread

theorem adjacentAllocations_doNotAuthorizeStore
    (left right : Allocation) (start : Nat)
    (hinside : start < left.endExclusive) (hcross : left.endExclusive < start + 32)
    (hadjacent : left.endExclusive = right.start) :
    ¬ ({ provisioned := #[left, right] } : MemoryState).InBounds start 32 := by
  rintro ⟨allocation, hmember, hcontains⟩
  simp at hmember
  rcases hmember with rfl | rfl
  · exact (Nat.not_lt_of_ge hcontains.2) hcross
  · exact (Nat.not_lt_of_ge hcontains.1) (by omega)

theorem emptyMemory_readsAssumedBytes (offset : Word) (assumed : ByteArray) :
    MemoryState.empty.readBytes offset assumed = assumed := by
  unfold MemoryState.readBytes MemoryState.readByte? MemoryState.empty
  have hround : assumed.toList.toByteArray = assumed := by
    apply ByteArray.ext
    rw [List.data_toByteArray, toList_eq_data_toList]
  simp [hround]

theorem initializedLoad_deterministic : initializedLoad.Deterministic := by
  intro ctx world
  constructor
  · intro history outcome₁ outcome₂ h₁ h₂
    cases outcome₁ <;> cases outcome₂
    · rfl
    · rcases h₁ with ⟨_, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₁ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₂ with ⟨_, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rcases h₂ with ⟨_, _, _, _, _, hrun, htrace⟩
      exact (initialized_no_next_event hrun htrace).elim
    · rename_i world₁ world₂
      rcases h₁ with ⟨state₁, hrun₁, hworld₁⟩
      rcases h₂ with ⟨state₂, hrun₂, hworld₂⟩
      have fixed₁ := (initialized_halted_world hrun₁).2
      have fixed₂ := (initialized_halted_world hrun₂).2
      have : world₁ = world₂ :=
        hworld₁.symm.trans (fixed₁.trans (fixed₂.symm.trans hworld₂))
      exact congrArg ObservableOutcome.halt this
  · intro entry hentry
    simp [initializedLoad, Vars.Program.mainId?] at hentry

theorem zeroSizeStore_not_deterministic : ¬ zeroSizeStore.Deterministic := by
  intro hdet
  have eval₁ : Vars.EvalFn zeroSizeStore zeroContext entryFunction
      { world := default } #[] [] (zeroState4 zeroContext default 1).globals .halted :=
    zero_eval zeroContext default 1
  have eval₂ : Vars.EvalFn zeroSizeStore zeroContext entryFunction
      { world := default } #[] [] (zeroState4 zeroContext default 2).globals .halted :=
    zero_eval zeroContext default 2
  have heq := (hdet zeroContext (default : World)).1 []
    (.halt ((default : World).storeStorage zeroContext.self 1 1))
    (.halt ((default : World).storeStorage zeroContext.self 2 2))
    ⟨(zeroState4 zeroContext default 1).globals, eval₁, rfl⟩
    ⟨(zeroState4 zeroContext default 2).globals, eval₂, rfl⟩
  exact zero_worlds_differ (ObservableOutcome.halt.inj heq)

end Sir.Examples
