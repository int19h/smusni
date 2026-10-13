import Lean

/-! Audit tooling only. The construction uses general F02/A1/A2 interfaces,
not the production AST, conditional F03-B contracts, or prior diagnostic models. -/
open Lean Elab Command
namespace PositiveAudit

def check (root : Name := `SmusniPositive) : CommandElabM Unit := do
  let env ← getEnv
  let excluded := #[`SmusniPilot, `SmusniF03B, `SmusniF03A1.Controls,
    `SmusniF03A2.Controls, `SmusniF03A2.Descriptor, `SmusniF03A2.FailureControl, `SmusniF03A2.RegressionControls]
  for mod in env.header.moduleNames do
    if excluded.any (·.isPrefixOf mod) then
      throwError "Positive model isolation violated: imported excluded module {mod}"
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if root.isPrefixOf env.header.moduleNames[idx.toNat]! then names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then throwError "Positive audit found no declarations for {root}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut allAxioms : Array Name := #[]
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do throwError "Positive audit rejected {name}: unexpected axiom {ax}"
      unless allAxioms.contains ax do allAxioms := allAxioms.push ax
    let info ← getConstInfo name
    if info.isUnsafe then throwError "Positive model has unsafe semantic declaration: {name}"
    match info with
    | .axiomInfo _ => throwError "Positive model declares its own axiom: {name}"
    | .thmInfo _ =>
      theorems := theorems + 1
      logInfo m!"THEOREM {name}: {axs}"
    | _ => pure ()
  logInfo m!"PASS positive model: {names.size} declarations audited; {theorems} theorem declarations (including generated lemmas); axioms {allAxioms.qsort Name.lt}"
end PositiveAudit
