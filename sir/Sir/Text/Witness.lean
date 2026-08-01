import Sir.Text.Parser
import Sir.Text.Printer
import Sir.Examples.TwoFunction

namespace Sir.Vars.Text

def witnessAddSource : String :=
  "fn init:\nentry {\na = const 2\nb = const 3\nr = icall @add2 a b\nstop\n}\n" ++
  "fn add2:\nentry x y -> z {\nz = add x y\niret\n}\n"

theorem parse_witnessAddSource : parse witnessAddSource = .ok witnessAddProgram := by
  parse_rfl

end Sir.Vars.Text
