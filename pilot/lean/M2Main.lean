import SmusniPilot.M2Examples
import SmusniPilot.M2Cases
import SmusniPilot.M2Parity

open SmusniPilot

def main : IO Unit := do
  M2.runM2TypingGates
  let cases ← M2.runM2Cases "../.."
  let parity ← M2.runM2Parity "../.." cases
  IO.println <|
    s!"M2 definitions={M2DefinitionId.all.length} " ++
    s!"clauses={M2ClauseId.all.length} typing-rules={M2TypingRuleId.all.length} " ++
    s!"all-s1={cases.outcomes.length} unchanged={cases.typedUnchanged} " ++
    s!"expanded={cases.typeDirectedExpansion} rejected={cases.typedRejection} " ++
    s!"pending-m3={cases.pendingMilestone3} blocked={cases.blocked} " ++
    s!"input-unavailable={cases.inputUnavailable} out-of-slice={cases.outOfSlice} " ++
    s!"rr-declarations={cases.rrDeclarations} rr-mismatch-cases={cases.rrMismatchCases}"
  IO.println <|
    s!"M2 parity cohort={parity.cohort} available={parity.oracleAvailable} " ++
    s!"unavailable={parity.oracleUnavailable} compared={parity.compared} " ++
    s!"term-matches={parity.termMatches} site-matches={parity.siteMatches} " ++
    s!"differences={parity.differences.length} known-81={parity.knownBlockerDifferences} " ++
    s!"unexplained={parity.unexplainedDifferences}"
  for difference in parity.differences do
    IO.println <| s!"M2 parity-difference {difference.id} " ++
      s!"part={difference.part} issue={repr difference.knownIssue} " ++
      s!"detail={difference.detail}"
  for outcome in cases.outcomes do
    if outcome.originalTag == "primitive-core" &&
        outcome.disposition != .typedUnchanged then
      IO.println <| s!"M2 primitive {outcome.id} {repr outcome.disposition} " ++
        s!"rule={outcome.decidingRule} expanded={repr outcome.expandedDefinitions}"
  let rejectionRules := (cases.outcomes.filter fun outcome =>
    outcome.disposition == .typedRejection).map (·.decidingRule) |>.eraseDups
  for rule in rejectionRules do
    let count := cases.outcomes.countP fun outcome =>
      outcome.disposition == .typedRejection && outcome.decidingRule == rule
    IO.println s!"M2 rejection-rule {rule} count={count}"
  for outcome in cases.outcomes do
    if ["unsupported-primitive", "application-arity", "definition-property",
        "close-row", "template-certificate", "definition-basis"].contains
        outcome.decidingRule then
      IO.println <| s!"M2 implementation-rejection {outcome.id} " ++
        s!"rule={outcome.decidingRule} expanded={repr outcome.expandedDefinitions}"
