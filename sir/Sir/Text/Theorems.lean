import Sir.Text.Proofs.RoundTrip

namespace Sir.Vars.Text

theorem tokenize_print (program : Program) :
    tokenize (print program) = programTokens program :=
  Proofs.tokenize_print program

theorem parse_normal {source : String} {program : Program}
    (parsed : parse source = .ok program) : program.Normal :=
  Proofs.parse_normal parsed

theorem parse_print_normalize {program : Program} (wellFormed : program.WellFormed) :
    parse (print program) = .ok program.normalize :=
  Proofs.parse_print_normalize wellFormed

theorem parse_print {source : String} {program : Program}
    (parsed : parse source = .ok program) :
    parse (print program) = .ok program :=
  Proofs.parse_print parsed

end Sir.Vars.Text
