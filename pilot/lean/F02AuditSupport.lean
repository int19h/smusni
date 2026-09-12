import Lean

/-! Shared *actual* audit entry point for the normal check and isolated fixtures.
This tooling module is outside the semantic SmusniF02 library. -/
open Lean Elab Command
namespace F02Audit

def check : CommandElabM Unit := do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`SmusniPilot).isPrefixOf mod then
      throwError "F02 isolation violated: imported production module {mod}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if (`SmusniF02).isPrefixOf mod then
        names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then throwError "F02 audit found no declarations"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut allAxioms : Array Name := #[]
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do
        throwError "F02 audit rejected {name}: unexpected axiom {ax}"
      unless allAxioms.contains ax do allAxioms := allAxioms.push ax
    let info ← getConstInfo name
    if info.isUnsafe then
      throwError "F02 has unsafe semantic declaration: {name}"
    match info with
    | .axiomInfo _ => throwError "F02 declares its own axiom: {name}"
    | .thmInfo _ =>
      theorems := theorems + 1
      logInfo m!"THEOREM {name}: {axs}"
    | _ => pure ()
  logInfo m!"PASS F02: {names.size} declarations audited; {theorems} theorem declarations (including generated lemmas); axioms {allAxioms.qsort Name.lt}"
end F02Audit
