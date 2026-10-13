import Lean

/-! Audit tooling, not a semantic premise. A1's reviewed general modules are
allowed dependencies. Production, F03-B, and A1 diagnostic controls are not. -/
open Lean Elab Command
namespace F03A2Audit

def check (root : Name := `SmusniF03A2) : CommandElabM Unit := do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`SmusniPilot).isPrefixOf mod || (`SmusniF03B).isPrefixOf mod || (`SmusniF03A1.Controls).isPrefixOf mod then
      throwError "F03-A2 isolation violated: imported excluded module {mod}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if root.isPrefixOf env.header.moduleNames[idx.toNat]! then
        names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then throwError "F03-A2 audit found no declarations for {root}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut allAxioms : Array Name := #[]
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do
        throwError "F03-A2 audit rejected {name}: unexpected axiom {ax}"
      unless allAxioms.contains ax do allAxioms := allAxioms.push ax
    let info ← getConstInfo name
    if info.isUnsafe then
      throwError "F03-A2 has unsafe semantic declaration: {name}"
    match info with
    | .axiomInfo _ => throwError "F03-A2 declares its own axiom: {name}"
    | .thmInfo _ =>
      theorems := theorems + 1
      logInfo m!"THEOREM {name}: {axs}"
    | _ => pure ()
  logInfo m!"PASS F03-A2: {names.size} declarations audited; {theorems} theorem declarations (including generated lemmas); axioms {allAxioms.qsort Name.lt}"
end F03A2Audit
