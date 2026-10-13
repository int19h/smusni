import Lean

/-! Audit tooling, outside the semantic library. Adapted from F02AuditSupport.
The optional module root lets existing audit fixtures exercise this same path. -/
open Lean Elab Command
namespace F03BAudit

def check (root : Name := `SmusniF03B) : CommandElabM Unit := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if root.isPrefixOf env.header.moduleNames[idx.toNat]! then
        names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then throwError "F03-B audit found no declarations for {root}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut allAxioms : Array Name := #[]
  for name in names do
    let axs ← collectAxioms name
    for ax in axs do
      unless allowed.contains ax do
        throwError "F03-B audit rejected {name}: unexpected axiom {ax}"
      unless allAxioms.contains ax do allAxioms := allAxioms.push ax
    let info ← getConstInfo name
    if info.isUnsafe then
      throwError "F03-B has unsafe semantic declaration: {name}"
    match info with
    | .axiomInfo _ => throwError "F03-B declares its own axiom: {name}"
    | .thmInfo _ =>
      theorems := theorems + 1
      logInfo m!"THEOREM {name}: {axs}"
    | _ => pure ()
  logInfo m!"PASS F03-B: {names.size} declarations audited; {theorems} theorem declarations (including generated lemmas); axioms {allAxioms.qsort Name.lt}"
end F03BAudit
