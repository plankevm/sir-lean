import Sir.Text.Proofs.Printable
import Sir.Text.Proofs.RoundTrip

namespace Sir.Vars.Text

theorem tokenize_print (program : Program) :
    tokenize (print program) = programTokens program :=
  Proofs.tokenize_print program

theorem parse_normal {source : String} {program : Program}
    (parsed : parse source = .ok program) : program.Normal :=
  Proofs.parse_normal parsed

theorem parse_printable {source : String} {program : Program}
    (parsed : parse source = .ok program) : program.Printable :=
  Proofs.parse_printable parsed

theorem parse_print_normalize {program : Program} (printable : program.Printable) :
    parse (print program) = .ok program.normalize :=
  Proofs.parse_print_normalize printable

theorem Program.Printable.normalize {program : Program}
    (printable : program.Printable) : program.normalize.Printable :=
  Proofs.Program.Printable.normalize printable

theorem parse_print {source : String} {program : Program}
    (parsed : parse source = .ok program) :
    parse (print program) = .ok program :=
  Proofs.parse_print parsed

theorem parse_print_alphaEquiv {program parsedProgram : Program}
    (printable : program.Printable)
    (parsed : parse (print program) = .ok parsedProgram) :
    parsedProgram.AlphaEquiv program :=
  Proofs.parse_print_alphaEquiv printable parsed

end Sir.Vars.Text
