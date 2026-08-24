import Sir.Text.Spec.Lexer

namespace Sir.Vars.Text

structure Mnemonic where
  name : String
  results : Nat
  operands : Nat
  build : Vector VarId results → Vector VarId operands → Stmt

def mnemonics : List Mnemonic := [
  ⟨"copy", 1, 1, fun r o => .assign r[0] (.var o[0])⟩,
  ⟨"add", 1, 2, fun r o => .assign r[0] (.add o[0] o[1])⟩,
  ⟨"lt", 1, 2, fun r o => .assign r[0] (.lt o[0] o[1])⟩,
  ⟨"sload", 1, 1, fun r o => .assign r[0] (.sload o[0])⟩,
  ⟨"sstore", 0, 2, fun _ o => .sstore o[0] o[1]⟩,
  ⟨"gas", 1, 0, fun r _ => .gas r[0]⟩,
  ⟨"call", 1, 2, fun r o => .call { callee := o[1], gas := o[0], result := r[0] }⟩,
  ⟨"malloc", 1, 1, fun r o => .malloc r[0] o[0]⟩,
  ⟨"mallocany", 1, 1, fun r o => .mallocUninit r[0] o[0]⟩,
  ⟨"mstore256", 0, 2, fun _ o => .mstore32 o[0] o[1]⟩,
  ⟨"mload256", 1, 1, fun r o => .mload32 r[0] o[0]⟩]

structure Spelling where
  name : String
  results : List VarId
  operands : List VarId

def spelling : Stmt → Spelling
  | .assign result (.constant _) => ⟨"const", [result], []⟩
  | .assign result (.var source) => ⟨"copy", [result], [source]⟩
  | .assign result (.add lhs rhs) => ⟨"add", [result], [lhs, rhs]⟩
  | .assign result (.lt lhs rhs) => ⟨"lt", [result], [lhs, rhs]⟩
  | .assign result (.sload key) => ⟨"sload", [result], [key]⟩
  | .sstore key value => ⟨"sstore", [], [key, value]⟩
  | .gas result => ⟨"gas", [result], []⟩
  | .call callData => ⟨"call", [callData.result], [callData.gas, callData.callee]⟩
  | .malloc result size => ⟨"malloc", [result], [size]⟩
  | .mallocUninit result size => ⟨"mallocany", [result], [size]⟩
  | .mstore32 offset value => ⟨"mstore256", [], [offset, value]⟩
  | .mload32 result offset => ⟨"mload256", [result], [offset]⟩
  | .icall _ args dests => ⟨"icall", dests.toList, args.toList⟩

end Sir.Vars.Text
