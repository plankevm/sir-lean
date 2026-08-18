import Sir.Text.Theorems
import Sir.Vars.Spec.Check
import Sir.Examples.TwoFunction
import Sir.Examples.Jump
import Sir.Examples.Memory
import Sir.Examples.HaltedCall
import Sir.Examples.ZeroedMalloc

namespace Sir.Examples

open Sir.Vars Sir.Vars.Text

def witnessAddSource : String :=
  "fn init:\nentry {\na = const 2\nb = const 3\nr = icall @add2 a b\nstop\n}\n" ++
  "fn add2:\nentry x y -> z {\nz = add x y\niret\n}\n"

theorem parse_witnessAddSource : parse witnessAddSource = .ok witnessAddProgram := by
  parse_rfl

theorem parse_print_witnessAdd : parse (print witnessAddProgram) = .ok witnessAddProgram := by
  exact parse_print parse_witnessAddSource

def jumpPrinted : String :=
  "fn init : \nblock0 -> v0 { \nv0 = const 7 \n=> @block1 \n} \n" ++
  "block1 v1 { \nv2 = add v1 v1 \nstop \n} \n"

theorem parse_print_jump : parse (print jumpProgram) = .ok jumpProgram := by
  exact parse_print (source := jumpPrinted) (by parse_rfl)

def initializedLoadPrinted : String :=
  "fn init : \nblock0 { \nv0 = const 32 \nv1 = mallocany v0 \nv2 = const 42 \n" ++
  "mstore256 v1 v2 \nv3 = mload256 v1 \nsstore v3 v3 \nstop \n} \n"

theorem parse_print_initializedLoad : parse (print initializedLoad) = .ok initializedLoad := by
  exact parse_print (source := initializedLoadPrinted) (by parse_rfl)

def zeroSizeStorePrinted : String :=
  "fn init : \nblock0 { \nv0 = const 0 \nv1 = mallocany v0 \nsstore v1 v1 \nstop \n} \n"

theorem parse_print_zeroSizeStore : parse (print zeroSizeStore) = .ok zeroSizeStore := by
  exact parse_print (source := zeroSizeStorePrinted) (by parse_rfl)

def zeroedMallocLoadPrinted : String :=
  "fn init : \nblock0 { \nv0 = const 32 \nv1 = malloc v0 \nv2 = mload256 v1 \nstop \n} \n"

theorem parse_print_zeroedMallocLoad :
    parse (print zeroedMallocLoad) = .ok zeroedMallocLoad := by
  exact parse_print (source := zeroedMallocLoadPrinted) (by parse_rfl)

def haltedCallPrinted : String :=
  "fn init : \nblock0 { \nicall @main \nstop \n} \nfn main : \nblock0 { \nstop \n} \n"

theorem parse_print_haltedCall : parse (print haltedCallProgram) = .ok haltedCallProgram := by
  exact parse_print (source := haltedCallPrinted) (by parse_rfl)

def selfCallProgram : Program :=
  { init :=
      { entry :=
          { inputs := #[]
            statements := #[.icall ⟨0⟩ #[] #[]]
            terminator := .halt
            outputs := #[] }
        rest := #[] }
    main := none
    rest := #[] }

theorem checkWellFormed_witnessAdd : (checkWellFormed witnessAddProgram).isOk = true := by
  rfl

theorem checkWellFormed_haltedCall : (checkWellFormed haltedCallProgram).isOk = true := by
  rfl

theorem checkWellFormed_jump : (checkWellFormed jumpProgram).isOk = true := by
  rfl

theorem checkWellFormed_selfCall :
    checkWellFormed selfCallProgram = .error (.recursiveCall ⟨0⟩ ⟨0⟩) := by
  rfl

end Sir.Examples
