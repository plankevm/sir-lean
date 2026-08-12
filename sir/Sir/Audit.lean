import Lean
import Sir.Theorems
import Sir.Examples.TwoFunction
import Sir.Examples.Memory
import Sir.Examples.ZeroedMalloc
import Sir.Examples.HaltedCall
import Sir.Examples.Jump
import Sir.Examples.Machine

open Lean Elab Command

namespace Sir.Audit

private def moduleContainsSpec : Name → Bool
  | .anonymous => false
  | .num parent _ => moduleContainsSpec parent
  | .str parent segment => segment == "Spec" || moduleContainsSpec parent

private def allowedModule (theoremModule moduleName : Name) : Bool :=
  ((`Sir).isPrefixOf moduleName && moduleContainsSpec moduleName) ||
    [`Init, `Lean, `Std, `Evm].any (·.isPrefixOf moduleName) ||
    (`Sir.Examples).isPrefixOf theoremModule && moduleName == theoremModule

private def auditTheorem (env : Environment) (theoremModule theoremName : Name)
    (theoremInfo : ConstantInfo) : CommandElabM Unit := do
  for constantName in theoremInfo.type.getUsedConstants do
    if let some moduleIndex := env.getModuleIdxFor? constantName then
      let moduleName := env.header.moduleNames[moduleIndex.toNat]!
      unless allowedModule theoremModule moduleName do
        throwError m!"Sir audit violation: theorem '{theoremName}' statement references \
          constant '{constantName}' from module '{moduleName}'"

private def allowedAxiom (axiomName : Name) : Bool :=
  [`propext, `Classical.choice, `Quot.sound].any (· == axiomName)

private def auditTheoremAxioms (theoremName : Name) : CommandElabM Unit := do
  let axioms ← collectAxioms theoremName
  for axiomName in axioms do
    unless allowedAxiom axiomName do
      throwError m!"Sir audit violation: theorem '{theoremName}' depends on disallowed \
        declaration '{axiomName}'"

elab "audit_sir_theorems" : command => do
  let env ← getEnv
  let theoremModules := env.header.moduleNames.filter fun moduleName =>
    moduleName != `Sir.Theorems && (`Sir).isPrefixOf moduleName &&
      (match moduleName with | .str _ "Theorems" => true | _ => false)
  let exampleModules := env.header.moduleNames.filter fun moduleName =>
    (`Sir.Examples).isPrefixOf moduleName
  for theoremModule in theoremModules ++ exampleModules do
    let some theoremModuleIndex := env.getModuleIdx? theoremModule
      | throwError m!"Sir audit could not resolve module '{theoremModule}'"
    for (declarationName, declarationInfo) in env.constants do
      if !isPrivateName declarationName &&
          env.getModuleIdxFor? declarationName = some theoremModuleIndex then
        if declarationInfo.isTheorem then
          auditTheorem env theoremModule declarationName declarationInfo
          auditTheoremAxioms declarationName

audit_sir_theorems

end Sir.Audit
