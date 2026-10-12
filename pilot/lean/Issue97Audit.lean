import Smusni97
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Smusni97).isPrefixOf env.header.moduleNames[idx.toNat]! then
        names := names.push name
  if names.isEmpty then throwError "No prototype declarations found"
  let mut theoremCount : Nat := 0
  let mut axioms : Array Name := #[]
  for name in names.qsort Name.lt do
    let info ← getConstInfo name
    if info.isUnsafe then throwError "Unsafe prototype declaration: {name}"
    let axs ← collectAxioms name
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
      unless axioms.contains ax do axioms := axioms.push ax
    match info with
    | .axiomInfo _ => throwError "Prototype declares an axiom: {name}"
    | .thmInfo _ =>
      theoremCount := theoremCount + 1
      logInfo m!"THEOREM {name}: {axs}"
    | _ => pure ()
  logInfo m!"PASS issue97: {names.size} declarations, {theoremCount} theorem declarations including generated, axioms {axioms.qsort Name.lt}"
