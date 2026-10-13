import Lean

/-! Same module-based audit discipline as F02 and F03-B. This tool is not part
of the semantic library and adds no theorem assumption. -/
open Lean Elab Command
namespace F03A1Audit

def check (root : Name := `SmusniF03A1) : CommandElabM Unit := do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`SmusniPilot).isPrefixOf mod || (`SmusniF03B).isPrefixOf mod || (`SmusniF03A2).isPrefixOf mod then
      throwError "F03-A1 isolation violated: imported excluded module {mod}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if root.isPrefixOf env.header.moduleNames[idx.toNat]! then
        names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then throwError "F03-A1 audit found no declarations for {root}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut allAxioms : Array Name := #[]
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do
        throwError "F03-A1 audit rejected {name}: unexpected axiom {ax}"
      unless allAxioms.contains ax do allAxioms := allAxioms.push ax
    let info ← getConstInfo name
    if info.isUnsafe then
      throwError "F03-A1 has unsafe semantic declaration: {name}"
    match info with
    | .axiomInfo _ => throwError "F03-A1 declares its own axiom: {name}"
    | .thmInfo _ =>
      theorems := theorems + 1
      logInfo m!"THEOREM {name}: {axs}"
    | _ => pure ()
  logInfo m!"PASS F03-A1: {names.size} declarations audited; {theorems} theorem declarations (including generated lemmas); axioms {allAxioms.qsort Name.lt}"
end F03A1Audit
