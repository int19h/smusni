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

mutual
  def rrDependencyGraphTerm {scope : Nat} (origins : BinderSiteOrigins scope) :
      Term scope → List (SiteId × List SiteId)
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
        (site, operandSiteOrigins origins arguments.dependencies) ::
          rrDependencyGraphList origins arguments
    | .vague site constraint =>
        (site, operandSiteOrigins origins constraint.dependencies) ::
          rrDependencyGraphTerm origins constraint

  def rrDependencyGraphList {scope : Nat}
      (origins : BinderSiteOrigins scope) :
      TermList scope → List (SiteId × List SiteId)
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        rrDependencyGraphTerm origins head ++ rrDependencyGraphList origins tail
end

def rrDependencyAgreement (declared : List RRDeclaredSite)
    (actual : List (SiteId × List SiteId)) : Bool :=
  if declared.length != actual.length then false
  else
    let pairs := declared.zip actual
    pairs.all fun pair =>
      let actualRoles := pair.2.2.mapM fun identity =>
        pairs.findSome? fun candidate =>
          if candidate.2.1 == identity then some candidate.1.role else none
      actualRoles == some pair.1.dependencies

structure RRCaseAudit where
  id : String
  fixture : String
  caseIndex : Nat
  declaredSites : Nat
  operandSites : Nat
  comparable : Bool
  agreement : Bool
  deriving Repr

structure RRAuditRun where
  fixturesRead : Nat
  linkedCases : Nat
  declaredSites : Nat
  operandSites : Nat
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
              comparable := false
              agreement := false }]
        | some term =>
            let graph := rrDependencyGraphTerm BinderSiteOrigins.empty term
            audits := audits ++ [{
              id := record.id
              fixture := fixturePath
              caseIndex
              declaredSites := fixtureCase.sites.length
              operandSites := graph.length
              comparable := true
              agreement := rrDependencyAgreement fixtureCase.sites graph }]
  pure {
    fixturesRead := fixtures.length
    linkedCases := audits.length
    declaredSites := audits.foldl (fun count audit => count + audit.declaredSites) 0
    operandSites := audits.foldl (fun count audit => count + audit.operandSites) 0
    comparableCases := audits.countP (·.comparable)
    agreementCases := audits.countP fun audit => audit.comparable && audit.agreement
    mismatchCases := audits.countP fun audit => audit.comparable && !audit.agreement
    unavailableCases := audits.countP fun audit => !audit.comparable
    cases := audits }

def runM2RRAuditMutationGates : IO Unit := do
  let first : SiteId := {
    document := "rr-mutation", occurrence := 0, expansionRole := "first" }
  let second : SiteId := {
    document := "rr-mutation", occurrence := 1, expansionRole := "second" }
  let declared : List RRDeclaredSite := [
    { role := "purpose", spelling := "probe", dependencies := [] },
    { role := "threshold", spelling := "probe", dependencies := ["purpose"] }]
  let actual := [(first, []), (second, [first])]
  if !rrDependencyAgreement declared actual then
    throw <| IO.userError "RR dependency audit rejected its control graph"
  let mutated := [declared[0]!, { declared[1]! with dependencies := [] }]
  if rrDependencyAgreement mutated actual then
    throw <| IO.userError "RR dependency mutation did not fail the audit"

end M2
end SmusniPilot
