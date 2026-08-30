import SmusniPilot.M2Bundle

namespace SmusniPilot
namespace M2

open Lean

def erasedSiteId : SiteId := {
  document := "erased"
  occurrence := 0
  expansionRole := "site" }

mutual
  def eraseSiteIds {scope : Nat} : Term scope → Term scope
    | .bound index => .bound index
    | .free identity => .free identity
    | .natural value => .natural value
    | .string value => .string value
    | .index value => .index value
    | .lambda type body => .lambda type (eraseSiteIds body)
    | .bind type computation body =>
        .bind type (eraseSiteIds computation) (eraseSiteIds body)
    | .apply function arguments =>
        .apply (eraseSiteIds function) (eraseSiteIdsList arguments)
    | .lexical head arguments => .lexical head (eraseSiteIdsList arguments)
    | .context _ arguments =>
        .context erasedSiteId (eraseSiteIdsList arguments)
    | .vague _ constraint =>
        .vague erasedSiteId (eraseSiteIds constraint)
    | .primitive operator arguments =>
        .primitive operator (eraseSiteIdsList arguments)

  def eraseSiteIdsList {scope : Nat} : TermList scope → TermList scope
    | .nil => .nil
    | .positional head tail =>
        .positional (eraseSiteIds head) (eraseSiteIdsList tail)
    | .labelled label head tail =>
        .labelled label (eraseSiteIds head) (eraseSiteIdsList tail)
end

structure RedexOracleCase where
  id : String
  available : Bool
  term : Option SExpr
  reason : Option String
  deriving Repr

def decodeRedexOracleCase : SExpr → Except String RedexOracleCase
  | .list _ (.atom (.symbol "case") :: fields) => do
      let some rawId := SExpr.field? "id" fields
        | .error "Redex oracle case lacks id"
      let some id := rawId.stringValue?
        | .error "Redex oracle case id is not a string"
      let some rawStatus := SExpr.field? "status" fields
        | .error s!"Redex oracle case {id} lacks status"
      match rawStatus with
      | .atom (.symbol "available") =>
          let some term := SExpr.field? "term" fields
            | .error s!"available Redex oracle case {id} lacks term"
          pure { id, available := true, term := some term, reason := none }
      | .atom (.symbol "unavailable") =>
          let reason := (SExpr.field? "reason" fields).bind SExpr.stringValue?
          pure { id, available := false, term := none, reason }
      | _ => .error s!"Redex oracle case {id} has bad status"
  | value => .error s!"malformed Redex oracle case: {repr value}"

def decodeRedexOracle : SExpr → Except String (List RedexOracleCase)
  | .list _ [
      .atom (.symbol "smusni-m2-redex-oracle"),
      .atom (.symbol "1"),
      .list _ [.atom (.symbol "count"), .atom (.symbol rawCount)],
      .list _ (.atom (.symbol "cases") :: cases)] => do
        let some count := rawCount.toNat?
          | .error "Redex oracle count is not natural"
        if cases.length != count then
          .error "Redex oracle count mismatch"
        cases.mapM decodeRedexOracleCase
  | _ => .error "bad Redex oracle root/version"

structure ParityDifference where
  id : String
  part : String
  detail : String
  deriving Repr

structure ParityRun where
  cohort : Nat
  oracleAvailable : Nat
  oracleUnavailable : Nat
  compared : Nat
  termMatches : Nat
  siteMatches : Nat
  differences : List ParityDifference
  deriving Repr

def runM2Parity (root : String) (caseRun : CaseRun) : IO ParityRun := do
  let oracleSource ← IO.FS.readFile (root ++ "/pilot/shared/M2_REDEX_ORACLE.sexp")
  let oracle ← IO.ofExcept (SExpr.parse oracleSource >>= decodeRedexOracle)
  let manifestSource ← IO.FS.readFile (root ++ "/pilot/shared/M1_S1_MANIFEST.json")
  let manifest : S1Manifest ← IO.ofExcept (Json.parse manifestSource >>= fromJson?)
  let corpusSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.port_corpus)
  let corpus ← IO.ofExcept (SExpr.parse corpusSource >>= decodeCorpus)
  let fixtureSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.fixtures)
  let lexicalHeads ← IO.ofExcept (SExpr.parse fixtureSource >>= decodeLexicalHeads)
  let mut compared := 0
  let mut termMatches := 0
  let mut siteMatches := 0
  let mut differences : List ParityDifference := []
  for oracleCase in oracle do
    if oracleCase.available then
      let some rawOracle := oracleCase.term
        | throw <| IO.userError s!"available oracle case {oracleCase.id} lacks term"
      let some corpusCase := corpus.find? fun item => item.id == oracleCase.id
        | throw <| IO.userError s!"oracle case {oracleCase.id} absent from corpus"
      let some outcome := caseRun.outcomes.find? fun item => item.id == oracleCase.id
        | throw <| IO.userError s!"oracle case {oracleCase.id} absent from M2 run"
      match outcome.term with
      | none =>
          differences := differences ++ [{
            id := oracleCase.id
            part := "term"
            detail := "Lean elaboration produced no term for an available oracle case" }]
      | some leanTerm =>
          let surface := SurfaceTerm.ofSExprWithLexicon lexicalHeads rawOracle
          let freeNames := freeNamesFromEnvironment corpusCase.environment
          match Interchange.Bundle.ofSurfaceWith oracleCase.id lexicalHeads freeNames none surface with
          | .error detail =>
              differences := differences ++ [{
                id := oracleCase.id, part := "oracle-decode", detail }]
          | .ok redexBundle =>
              compared := compared + 1
              let leanCanonical := Interchange.renderCanonicalTerm
                (eraseSiteIds leanTerm)
              let redexCanonical := Interchange.renderCanonicalTerm
                (eraseSiteIds redexBundle.term)
              if leanCanonical == redexCanonical then
                termMatches := termMatches + 1
              else
                differences := differences ++ [{
                  id := oracleCase.id
                  part := "term"
                  detail := "alpha-normal CoreTerm differs after SiteId erasure" }]
              let leanSites := emittedSiteSignature leanTerm
              let redexSites := emittedSiteSignature redexBundle.term
              if leanSites == redexSites then
                siteMatches := siteMatches + 1
              else
                differences := differences ++ [{
                  id := oracleCase.id
                  part := "sites"
                  detail := s!"Lean={repr leanSites}; Redex={repr redexSites}" }]
  let available := oracle.countP (·.available)
  pure {
    cohort := oracle.length
    oracleAvailable := available
    oracleUnavailable := oracle.length - available
    compared
    termMatches
    siteMatches
    differences }

end M2
end SmusniPilot
