import Lean
import Sir.Theorems
import Sir.Examples.VarsWitness
import Sir.Examples.VarsJump
import Sir.Examples.VarsMemory
import Sir.Examples.VarsIcall
import Sir.Examples.VarsNondeterminism
import Sir.Examples.StackWitness

open Lean Elab Command

namespace Sir.Audit

private def moduleContainsSpec : Name → Bool
  | .anonymous => false
  | .num parent _ => moduleContainsSpec parent
  | .str parent segment => segment == "Spec" || moduleContainsSpec parent

private def auditedModule (moduleName : Name) : Bool :=
  ((`Sir).isPrefixOf moduleName &&
      (match moduleName with | .str _ "Theorems" => true | _ => false)) ||
    (`Sir.Examples).isPrefixOf moduleName

private def allowedModule (theoremModule moduleName : Name) : Bool :=
  ((`Sir).isPrefixOf moduleName && moduleContainsSpec moduleName) ||
    [`Init, `Lean, `Std, `Evm].any (·.isPrefixOf moduleName) ||
    (`Sir.Examples).isPrefixOf theoremModule && moduleName == theoremModule

private def auditTheorem (env : Environment) (theoremModule theoremName : Name)
    (theoremInfo : ConstantInfo) : CommandElabM Nat := do
  let mut violations := 0
  for constantName in theoremInfo.type.getUsedConstants do
    if let some moduleIndex := env.getModuleIdxFor? constantName then
      let moduleName := env.header.moduleNames[moduleIndex.toNat]!
      unless allowedModule theoremModule moduleName do
        logError m!"Sir audit violation: theorem '{theoremName}' statement references \
          constant '{constantName}' from module '{moduleName}'"
        violations := violations + 1
  return violations

private def allowedAxiom (axiomName : Name) : Bool :=
  [`propext, `Classical.choice, `Quot.sound].any (· == axiomName)

private def auditTheoremAxioms (theoremName : Name) : CommandElabM Nat := do
  let mut violations := 0
  for axiomName in ← collectAxioms theoremName do
    unless allowedAxiom axiomName do
      logError m!"Sir audit violation: theorem '{theoremName}' depends on disallowed \
        declaration '{axiomName}'"
      violations := violations + 1
  return violations

elab "audit_sir_theorems" : command => do
  let env ← getEnv
  let mut violations := 0
  for (declarationName, declarationInfo) in env.constants do
    if declarationInfo.isTheorem && !isPrivateName declarationName then
      if let some moduleIndex := env.getModuleIdxFor? declarationName then
        let moduleName := env.header.moduleNames[moduleIndex.toNat]!
        if auditedModule moduleName then
          violations := violations + (← auditTheorem env moduleName declarationName
            declarationInfo)
          violations := violations + (← auditTheoremAxioms declarationName)
  if violations != 0 then
    throwError m!"Sir audit found {violations} violations"

audit_sir_theorems

end Sir.Audit
