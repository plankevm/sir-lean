import Sir.Text.Witness
import Sir.Examples.Jump
import Sir.Examples.Memory
import Sir.Examples.HaltedCall

namespace Sir.Vars.Text

open Sir.Examples

namespace Examples

def witnessAddPrinted : String :=
  "fn init : \nblock0 { \nv0 = const 2 \nv1 = const 3 \nv2 = icall @fn1 v0 v1 \nstop \n} \n" ++
  "fn fn1 : \nblock0 v3 v4 -> v5 { \nv5 = add v3 v4 \niret \n} \n"

theorem parse_print_witnessAdd : parse (print witnessAddProgram) = .ok witnessAddProgram := by
  rw [show print witnessAddProgram = witnessAddPrinted by parse_rfl]
  parse_rfl

def jumpPrinted : String :=
  "fn init : \nblock0 -> v0 { \nv0 = const 7 \n=> @block1 \n} \n" ++
  "block1 v1 { \nv2 = add v1 v1 \nstop \n} \n"

theorem parse_print_jump : parse (print jumpProgram) = .ok jumpProgram := by
  rw [show print jumpProgram = jumpPrinted by parse_rfl]
  parse_rfl

def initializedLoadPrinted : String :=
  "fn init : \nblock0 { \nv0 = const 32 \nv1 = mallocany v0 \nv2 = const 42 \n" ++
  "mstore256 v1 v2 \nv3 = mload256 v1 \nsstore v3 v3 \nstop \n} \n"

theorem parse_print_initializedLoad : parse (print initializedLoad) = .ok initializedLoad := by
  rw [show print initializedLoad = initializedLoadPrinted by parse_rfl]
  parse_rfl

def zeroSizeStorePrinted : String :=
  "fn init : \nblock0 { \nv0 = const 0 \nv1 = mallocany v0 \nsstore v1 v1 \nstop \n} \n"

theorem parse_print_zeroSizeStore : parse (print zeroSizeStore) = .ok zeroSizeStore := by
  rw [show print zeroSizeStore = zeroSizeStorePrinted by parse_rfl]
  parse_rfl

def haltedCallPrinted : String :=
  "fn init : \nblock0 { \nicall @fn1 \nstop \n} \nfn fn1 : \nblock0 { \nstop \n} \n"

theorem parse_print_haltedCall : parse (print haltedCallProgram) = .ok haltedCallProgram := by
  rw [show print haltedCallProgram = haltedCallPrinted by parse_rfl]
  parse_rfl

end Examples
end Sir.Vars.Text
