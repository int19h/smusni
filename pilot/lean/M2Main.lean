import SmusniPilot.M2Examples
import SmusniPilot.M2Cases
import SmusniPilot.M2Parity
import SmusniPilot.M2RRAudit

open SmusniPilot

def main : IO Unit := do
  M2.runM2TypingGates
  M2.runM2ParityMutationGates
  M2.runM2RRAuditMutationGates
  let cases ← M2.runM2Cases "../.."
  let parity ← M2.runM2Parity "../.." cases
  let rrAudit ← M2.runM2RRAudit "../.." cases
  IO.println <|
    s!"M2 definitions={M2DefinitionId.all.length} " ++
    s!"clauses={M2ClauseId.all.length} typing-rules={M2TypingRuleId.all.length} " ++
    s!"all-s1={cases.outcomes.length} unchanged={cases.typedUnchanged} " ++
    s!"expanded={cases.typeDirectedExpansion} rejected={cases.typedRejection} " ++
    s!"pending-m3={cases.pendingMilestone3} blocked={cases.blocked} " ++
    s!"input-unavailable={cases.inputUnavailable} out-of-slice={cases.outOfSlice} " ++
    s!"derived-site-entries={cases.rrDeclarations} " ++
    s!"derived-profile-mismatch-cases={cases.rrMismatchCases}"
  IO.println <|
    s!"M2 RR-adoption fixtures={rrAudit.fixturesRead} linked-cases={rrAudit.linkedCases} " ++
    s!"declared-sites={rrAudit.declaredSites} operand-sites={rrAudit.operandSites} " ++
    s!"comparable={rrAudit.comparableCases} agreement={rrAudit.agreementCases} " ++
    s!"mismatch={rrAudit.mismatchCases} unavailable={rrAudit.unavailableCases}"
  for audit in rrAudit.cases do
    if audit.declaredSites > 0 && (!audit.comparable || !audit.agreement) then
      IO.println <| s!"M2 RR-adoption-difference {audit.id} " ++
        s!"fixture={audit.fixture} case={audit.caseIndex} " ++
        s!"declared={audit.declaredSites} operand={audit.operandSites} " ++
        s!"comparable={audit.comparable}"
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
    if ["definition-property", "definition-basis"].contains
        outcome.decidingRule then
      let anchor := if outcome.decidingRule == "definition-property" then
        "spec §5.3:1457-1461; oracle not-in-domain/unavailable"
      else "spec §12:3565-3567; Massify basis type"
      IO.println <| s!"M2 semantic-typed-rejection {outcome.id} " ++
        s!"rule={outcome.decidingRule} anchor={anchor} " ++
        s!"expanded={repr outcome.expandedDefinitions}"
    else if ["unsupported-primitive", "application-arity", "close-row",
        "template-certificate"].contains outcome.decidingRule then
      IO.println <| s!"M2 implementation-limit {outcome.id} " ++
        s!"rule={outcome.decidingRule} expanded={repr outcome.expandedDefinitions}"
  IO.ofExcept parity.validate
