import SmusniPilot.M2Cases

namespace SmusniPilot
namespace M2

open Lean

structure RRDeclaredSite where
  role : String
  spelling : String
  dependencies : List String
  deriving Repr, BEq, Inhabited

structure RRFixtureCase where
  index : Nat
  sites : List RRDeclaredSite
  deriving Repr, BEq

structure RRFixture where
  source : String
  ordinal : Nat
  cases : List RRFixtureCase
  deriving Repr, BEq

def decodeRRSymbolList : SExpr → Except String (List String)
  | .list _ values => values.mapM fun
      | .atom (.symbol value) => pure value
      | value => throw s!"RR dependency is not a symbol: {repr value}"
  | value => throw s!"RR dependencies are not a list: {repr value}"

def decodeRRDeclaredSite : SExpr → Except String RRDeclaredSite
  | .list _ [
      .atom (.symbol role),
      .atom (.symbol spelling),
      .list _ [.atom (.symbol "deps"), dependencies]] =>
      return { role, spelling, dependencies := ← decodeRRSymbolList dependencies }
  | value => throw s!"malformed RR site declaration: {repr value}"

def decodeRRFixtureCase : SExpr → Except String RRFixtureCase
  | .list _ [
      .atom (.symbol "case"),
      .atom (.symbol rawIndex),
      .list _ (.atom (.symbol "rr") :: fields)] => do
      let some index := rawIndex.toNat?
        | throw s!"RR case index is not natural: {rawIndex}"
      let some rawSites := SExpr.field? "sites" fields
        | throw s!"RR case {index} lacks sites"
      let sites ← match rawSites with
        | .list _ values => values.mapM decodeRRDeclaredSite
        | value => throw s!"RR case {index} sites are not a list: {repr value}"
      pure { index, sites }
  | value => throw s!"malformed RR case: {repr value}"

def decodeRRFixture : SExpr → Except String RRFixture
  | .list _ (
      .atom (.symbol "smusni-rr-fixture") ::
      .atom (.symbol "1") ::
      .list _ [
        .atom (.symbol "fence"),
        .atom (.string source),
        .atom (.symbol rawOrdinal),
        .atom (.string _digest)] :: cases) => do
      let some ordinal := rawOrdinal.toNat?
        | throw "RR fixture ordinal is not natural"
      pure { source, ordinal, cases := ← cases.mapM decodeRRFixtureCase }
  | _ => throw "bad RR fixture root/version"

partial def rrCaseIndexFromProvenance : SExpr → Option Nat
  | .list _ (
      .atom (.symbol "fence") ::
      .atom (.string _) ::
      .atom (.symbol _) ::
      .atom (.symbol "specimen") ::
      .atom (.symbol rawIndex) :: _) => rawIndex.toNat?
  | .list _ values => values.findSome? rrCaseIndexFromProvenance
  | _ => none

abbrev BinderSiteOrigins (scope : Nat) := Fin scope → List SiteId

def BinderSiteOrigins.empty : BinderSiteOrigins 0 := Fin.elim0

def BinderSiteOrigins.extend {scope : Nat} (origins : BinderSiteOrigins scope)
    (sites : List SiteId) : BinderSiteOrigins (scope + 1) :=
  Fin.cases sites origins

def operandSiteOrigins {scope : Nat} (origins : BinderSiteOrigins scope)
    (dependencies : List (Dependency scope)) : List SiteId :=
  dependencies.flatMap fun
    | .bound index => origins index
    | .free _ => []
  |>.eraseDups

structure RRActualSite where
  identity : SiteId
  role : SiteRole
  dependencies : List SiteId
  deriving Repr, BEq

mutual
  def rrDependencyGraphTerm {scope : Nat} (origins : BinderSiteOrigins scope) :
      Term scope → List RRActualSite
    | .bound _ | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body =>
        rrDependencyGraphTerm (origins.extend []) body
    | .bind _ computation body =>
        rrDependencyGraphTerm origins computation ++
          rrDependencyGraphTerm (origins.extend computation.siteIds) body
    | .apply function arguments =>
        rrDependencyGraphTerm origins function ++
          rrDependencyGraphList origins arguments
    | .lexical _ arguments | .primitive _ arguments =>
        rrDependencyGraphList origins arguments
    | .context site arguments =>
        { identity := site
          role := .context
          dependencies := operandSiteOrigins origins arguments.dependencies } ::
          rrDependencyGraphList origins arguments
    | .vague site constraint =>
        { identity := site
          role := .vague
          dependencies := operandSiteOrigins origins constraint.dependencies } ::
          rrDependencyGraphTerm origins constraint

  def rrDependencyGraphList {scope : Nat}
      (origins : BinderSiteOrigins scope) :
      TermList scope → List RRActualSite
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        rrDependencyGraphTerm origins head ++ rrDependencyGraphList origins tail
end

structure RRDependencyComparison where
  declaredRoles : Nat
  matchedRoles : Nat
  dependencyAgreements : Nat
  dependencyMismatches : Nat
  missingDeclaredRoles : List String
  undeclaredEmittedOrigins : List String
  deriving Repr, BEq

def rrInjectiveAssignments : List RRDeclaredSite → List RRActualSite →
    List (List (RRDeclaredSite × RRActualSite))
  | [], _ => [[]]
  | declaration :: rest, actual =>
      actual.flatMap fun emitted =>
        (rrInjectiveAssignments rest (actual.erase emitted)).map fun assignment =>
          (declaration, emitted) :: assignment
termination_by declared _ => declared.length

def rrAssignmentPreservesDependencies
    (assignment : List (RRDeclaredSite × RRActualSite)) : Bool :=
  assignment.all fun pair =>
    let mappedDependencies := pair.2.dependencies.mapM fun dependency =>
      (assignment.find? fun candidate => candidate.2.identity == dependency).map
        (fun candidate => candidate.1.role)
    mappedDependencies == some pair.1.dependencies

def RRActualSite.embeddingCandidate (site : RRActualSite) : Bool :=
  let role := site.identity.expansionRole.splitOn "/" |>.getLast?.getD
    site.identity.expansionRole
  !role.startsWith "default-"

def rrDependencyComparison (declared : List RRDeclaredSite)
    (actual : List RRActualSite) : RRDependencyComparison :=
  let candidates := actual.filter RRActualSite.embeddingCandidate
  let embedding := (rrInjectiveAssignments declared candidates).find?
    rrAssignmentPreservesDependencies
  match embedding with
  | some matched =>
      let matchedIdentities := matched.map fun pair => pair.2.identity
      {
        declaredRoles := declared.length
        matchedRoles := matched.length
        dependencyAgreements := matched.length
        dependencyMismatches := 0
        missingDeclaredRoles := []
        undeclaredEmittedOrigins := actual.filterMap fun emitted =>
          if matchedIdentities.contains emitted.identity then none
          else some emitted.identity.expansionRole }
  | none => {
      declaredRoles := declared.length
      matchedRoles := 0
      dependencyAgreements := 0
      dependencyMismatches := 0
      missingDeclaredRoles := declared.map (·.role)
      undeclaredEmittedOrigins := actual.map fun emitted =>
        emitted.identity.expansionRole }

def rrDependencyAgreement (declared : List RRDeclaredSite)
    (actual : List RRActualSite) : Bool :=
  let comparison := rrDependencyComparison declared actual
  comparison.matchedRoles == comparison.declaredRoles &&
    comparison.dependencyMismatches == 0

structure RRCaseAudit where
  id : String
  fixture : String
  caseIndex : Nat
  declaredSites : Nat
  operandSites : Nat
  matchedRoles : Nat
  dependencyAgreements : Nat
  dependencyMismatches : Nat
  missingDeclaredRoles : List String
  undeclaredEmittedOrigins : List String
  unavailableCause : Option String
  comparable : Bool
  agreement : Bool
  deriving Repr

structure RRAuditRun where
  fixturesRead : Nat
  linkedCases : Nat
  declaredSites : Nat
  operandSites : Nat
  matchedRoles : Nat
  dependencyAgreements : Nat
  dependencyMismatches : Nat
  undeclaredEmittedSites : Nat
  comparableCases : Nat
  agreementCases : Nat
  mismatchCases : Nat
  unavailableCases : Nat
  cases : List RRCaseAudit
  deriving Repr

def loadRRFixtures (root : String) (manifest : S1Manifest) :
    IO (List (String × RRFixture)) := do
  let records := manifest.typed_records.toList.filter fun record =>
    record.schema == "RRFixture"
  records.mapM fun record => do
    let digest ← sha256File root record.path
    if digest != record.sha256 then
      throw <| IO.userError s!"RR audit digest mismatch for {record.path}"
    let fullPath : String := root ++ "/" ++ record.path
    let source ← IO.FS.readFile fullPath
    let fixture ← IO.ofExcept <| (SExpr.parse source >>= decodeRRFixture).mapError fun error =>
      s!"{record.path}: {error}"
    pure (record.path, fixture)

def runM2RRAudit (root : String) (caseRun : CaseRun) : IO RRAuditRun := do
  let manifestSource ← IO.FS.readFile (root ++ "/pilot/shared/M1_S1_MANIFEST.json")
  let manifest : S1Manifest ← IO.ofExcept (Json.parse manifestSource >>= fromJson?)
  let fixtures ← loadRRFixtures root manifest
  let corpusSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.port_corpus)
  let corpus ← IO.ofExcept (SExpr.parse corpusSource >>= decodeCorpus)
  let mut audits : List RRCaseAudit := []
  for record in corpus do
    if let some fixturePath := rrLinkFromProvenance record.provenance then
      if let some fixture := (fixtures.find? fun item => item.1 == fixturePath).map (·.2) then
        let some caseIndex := rrCaseIndexFromProvenance record.provenance
          | throw <| IO.userError s!"RR-linked case {record.id} lacks specimen index"
        let some fixtureCase := fixture.cases.find? fun item => item.index == caseIndex
          | throw <| IO.userError s!"RR-linked case {record.id} lacks fixture case {caseIndex}"
        let some outcome := caseRun.outcomes.find? fun item => item.id == record.id
          | throw <| IO.userError s!"RR-linked case {record.id} lacks M2 outcome"
        match outcome.term with
        | none =>
            audits := audits ++ [{
              id := record.id
              fixture := fixturePath
              caseIndex
              declaredSites := fixtureCase.sites.length
              operandSites := 0
              matchedRoles := 0
              dependencyAgreements := 0
              dependencyMismatches := 0
              missingDeclaredRoles := fixtureCase.sites.map (·.role)
              undeclaredEmittedOrigins := []
              unavailableCause := some <|
                s!"{repr outcome.disposition}:{outcome.decidingRule}"
              comparable := false
              agreement := false }]
        | some term =>
            let graph := rrDependencyGraphTerm BinderSiteOrigins.empty term
            let comparison := rrDependencyComparison fixtureCase.sites graph
            audits := audits ++ [{
              id := record.id
              fixture := fixturePath
              caseIndex
              declaredSites := fixtureCase.sites.length
              operandSites := graph.length
              matchedRoles := comparison.matchedRoles
              dependencyAgreements := comparison.dependencyAgreements
              dependencyMismatches := comparison.dependencyMismatches
              missingDeclaredRoles := comparison.missingDeclaredRoles
              undeclaredEmittedOrigins := comparison.undeclaredEmittedOrigins
              unavailableCause := if comparison.missingDeclaredRoles.isEmpty then none
                else some "emitted term has no preserving structural embedding"
              comparable := true
              agreement := comparison.matchedRoles == comparison.declaredRoles &&
                comparison.dependencyMismatches == 0 }]
  pure {
    fixturesRead := fixtures.length
    linkedCases := audits.length
    declaredSites := audits.foldl (fun count audit => count + audit.declaredSites) 0
    operandSites := audits.foldl (fun count audit => count + audit.operandSites) 0
    matchedRoles := audits.foldl (fun count audit => count + audit.matchedRoles) 0
    dependencyAgreements := audits.foldl
      (fun count audit => count + audit.dependencyAgreements) 0
    dependencyMismatches := audits.foldl
      (fun count audit => count + audit.dependencyMismatches) 0
    undeclaredEmittedSites := audits.foldl
      (fun count audit => count + audit.undeclaredEmittedOrigins.length) 0
    comparableCases := audits.countP (·.comparable)
    agreementCases := audits.countP fun audit => audit.comparable &&
      audit.declaredSites > 0 && audit.agreement
    mismatchCases := audits.countP fun audit => audit.comparable &&
      audit.declaredSites > 0 && !audit.agreement
    unavailableCases := audits.countP fun audit => !audit.comparable
    cases := audits }

def runM2RRAuditMutationGates : IO Unit := do
  let first : SiteId := {
    document := "rr-mutation", occurrence := 0,
    expansionRole := "D12.TooMany/0/purpose-context" }
  let second : SiteId := {
    document := "rr-mutation", occurrence := 1,
    expansionRole := "D12.TooMany/1/threshold-vague" }
  let declared : List RRDeclaredSite := [
    { role := "purpose", spelling := "probe", dependencies := [] },
    { role := "threshold", spelling := "probe", dependencies := ["purpose"] }]
  let actual : List RRActualSite := [
    { identity := first, role := .context, dependencies := [] },
    { identity := second, role := .vague, dependencies := [first] }]
  if !rrDependencyAgreement declared actual then
    throw <| IO.userError "RR dependency audit rejected its control graph"
  let control := rrDependencyComparison declared actual
  if control.matchedRoles != 2 || control.dependencyAgreements != 2 ||
      !control.undeclaredEmittedOrigins.isEmpty then
    throw <| IO.userError "RR role-matching control did not cover both declarations"
  let mutated := [declared[0]!, { declared[1]! with dependencies := [] }]
  if rrDependencyAgreement mutated actual then
    throw <| IO.userError "RR dependency mutation did not fail the audit"
  let extra : SiteId := {
    document := "rr-mutation", occurrence := 2,
    expansionRole := "D4.6.Close/0/default-:2" }
  let withExtra := actual ++ [{ identity := extra, role := .context, dependencies := [] }]
  let extraComparison := rrDependencyComparison declared withExtra
  if extraComparison.matchedRoles != 2 ||
      extraComparison.undeclaredEmittedOrigins != [extra.expansionRole] then
    throw <| IO.userError "RR audit did not isolate an undeclared emitted site"
  let defaultOnly := rrDependencyComparison
    [{ role := "relation", spelling := "probe", dependencies := [] }]
    [{ identity := extra, role := .context, dependencies := [] }]
  if defaultOnly.matchedRoles != 0 || defaultOnly.missingDeclaredRoles != ["relation"] ||
      defaultOnly.undeclaredEmittedOrigins != [extra.expansionRole] then
    throw <| IO.userError "RR audit allowed a computed default to satisfy a declaration"

end M2
end SmusniPilot
