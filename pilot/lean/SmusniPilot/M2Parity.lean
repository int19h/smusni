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

def lexicalItems {scope : Nat} : TermList scope →
    List (Option String × Term scope)
  | .nil => []
  | .positional head tail => (none, head) :: lexicalItems tail
  | .labelled label head tail => (some label, head) :: lexicalItems tail

def canonicalLabelledList {scope : Nat} :
    List (String × Term scope) → TermList scope
  | [] => .nil
  | (label, head) :: tail =>
      .labelled label head (canonicalLabelledList tail)

def routeLexicalArguments {scope : Nat} (row : M2LexicalRowRecord)
    (arguments : TermList scope) : Except String (TermList scope) := do
  let items := lexicalItems arguments
  let explicitLabels := items.filterMap (·.1)
  if explicitLabels.length != explicitLabels.eraseDups.length then
    throw s!"{row.head} repeats a labelled fill"
  let mut explicitOrdinary : List Nat := []
  let mut explicitEvent : Option (Term scope) := none
  let mut explicitAssignments : List (Nat × Term scope) := []
  let mut positional : List (Term scope) := []
  for (label, term) in items do
    match label with
    | none => positional := positional ++ [term]
    | some ":Eventuality" =>
        if row.eventMode != .directEvent then
          throw s!"{row.head} has no Eventuality place"
        explicitEvent := some term
    | some label =>
        let some place := (label.drop 1).toString.toNat?
          | throw s!"{row.head} has unknown label {label}"
        if place == 0 || place > row.ordinaryArity then
          throw s!"{row.head} label {label} is outside its row"
        explicitOrdinary := explicitOrdinary ++ [place]
        explicitAssignments := explicitAssignments ++ [(place, term)]
  if explicitOrdinary.length != explicitOrdinary.eraseDups.length then
    throw s!"{row.head} repeats an ordinary place"
  let available := (List.range row.ordinaryArity).map (· + 1) |>.filter fun place =>
    !explicitOrdinary.contains place
  let ordinaryPositional := positional.take available.length
  let trailing := positional.drop available.length
  let positionalEvent ← match trailing with
    | [] => pure none
    | [term] =>
        if row.eventMode == .directEvent && explicitEvent.isNone then pure (some term)
        else throw s!"{row.head} has too many positional fills"
    | _ => throw s!"{row.head} has too many positional fills"
  let positionalAssignments := (available.zip ordinaryPositional).map fun pair =>
    (pair.1, pair.2)
  let assignments := explicitAssignments ++ positionalAssignments
  let ordinary := (List.range row.ordinaryArity).filterMap fun offset =>
    let place := offset + 1
    (assignments.find? fun item => item.1 == place).map fun item =>
      (s!":{place}", item.2)
  let event := (explicitEvent.orElse fun _ => positionalEvent).toList.map fun term =>
    (":Eventuality", term)
  pure <| canonicalLabelledList (ordinary ++ event)

mutual
  def canonicalizeLexicalLabels {scope : Nat} :
      Term scope → Except String (Term scope)
    | .bound index => pure (Term.bound index)
    | .free identity => pure (Term.free identity)
    | .natural value => pure (Term.natural value)
    | .string value => pure (Term.string value)
    | .index value => pure (Term.index value)
    | .lambda type body =>
        return .lambda type (← canonicalizeLexicalLabels body)
    | .bind type computation body =>
        return .bind type (← canonicalizeLexicalLabels computation)
          (← canonicalizeLexicalLabels body)
    | .apply function arguments =>
        return .apply (← canonicalizeLexicalLabels function)
          (← canonicalizeLexicalLabelsList arguments)
    | .lexical head arguments => do
        let arguments ← canonicalizeLexicalLabelsList arguments
        let some row := lookupLexicalRow head
          | throw s!"missing typed lexical row {head}"
        return .lexical head (← routeLexicalArguments row arguments)
    | .context site arguments =>
        return .context site (← canonicalizeLexicalLabelsList arguments)
    | .vague site constraint =>
        return .vague site (← canonicalizeLexicalLabels constraint)
    | .primitive operator arguments =>
        return .primitive operator (← canonicalizeLexicalLabelsList arguments)

  def canonicalizeLexicalLabelsList {scope : Nat} :
      TermList scope → Except String (TermList scope)
    | .nil => pure .nil
    | .positional head tail =>
        return .positional (← canonicalizeLexicalLabels head)
          (← canonicalizeLexicalLabelsList tail)
    | .labelled label head tail =>
        return .labelled label (← canonicalizeLexicalLabels head)
          (← canonicalizeLexicalLabelsList tail)
end

structure RedexOracleCase where
  id : String
  available : Bool
  term : Option SExpr
  reason : Option String
  context : String
  category : Option String
  deriving Repr

structure OracleTypingWitness where
  type : SExpr
  effects : List SExpr
  obligations : List SExpr
  deriving Repr, BEq

def decodeOracleTyping : SExpr → Except String OracleTypingWitness
  | .list _ [.atom (.symbol "typing"), type, .list _ effects, .list _ obligations] =>
      pure { type, effects, obligations }
  | _ => throw "malformed oracle typing witness"

def oracleField (fields : List SExpr) (name : String) : Except String SExpr :=
  match SExpr.field? name fields with
  | some value => pure value
  | none => throw s!"oracle evidence lacks {name}"

def assertOracleWitness (payload : OracleTypingWitness) : Except String OracleTypingWitness :=
  match payload.type with
  | .atom (.symbol "Content") => pure {
      type := .list .paren [.atom (.symbol "Act"), .atom (.symbol "Assertion")]
      effects := []
      obligations := payload.obligations }
  | _ => throw "Assert payload witness is not literally Content"

theorem assertOracleWitness_preserves_metadata (payload act : OracleTypingWitness)
    (accepted : assertOracleWitness payload = .ok act) :
    act.effects = [] ∧ act.obligations = payload.obligations := by
  unfold assertOracleWitness at accepted
  split at accepted <;> cases accepted <;> simp

def validateOracleEvidence (fields : List SExpr) (term : SExpr) : Except String String := do
  let context ← oracleField fields "context"
  let sourceType ← oracleField fields "source-type"
  let source ← decodeOracleTyping (← oracleField fields "source-typing")
  let target ← decodeOracleTyping (← oracleField fields "target-typing")
  if source.type != sourceType then throw "source type/witness mismatch"
  match context with
  | .atom (.symbol "whole-a0") => pure "whole-a0"
  | .atom (.symbol "assert-bridge") =>
      match term with
      | .list _ [.atom (.symbol "Assert"), _] => pure ()
      | _ => throw "Assert bridge stripped or changed its wrapper"
      let payloadSource ← decodeOracleTyping (← oracleField fields "payload-source-typing")
      let payloadTarget ← decodeOracleTyping (← oracleField fields "payload-target-typing")
      if source != (← assertOracleWitness payloadSource) ||
          target != (← assertOracleWitness payloadTarget) then
        throw "Assert bridge changed payload obligation metadata or immediate Act effects"
      pure "assert-bridge"
  | _ => throw "unknown oracle context certificate"

def decodeRedexOracleCase : SExpr → Except String RedexOracleCase
  | .list _ (.atom (.symbol "case") :: fields) => do
      let names ← fields.mapM fun
        | .list _ [.atom (.symbol name), _] => pure name
        | _ => throw "malformed oracle field"
      if names.length != names.eraseDups.length then throw "duplicate oracle field"
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
          let context ← validateOracleEvidence fields term
          pure { id, available := true, term := some term, reason := none, context, category := none }
      | .atom (.symbol "unavailable") =>
          let some reason := (SExpr.field? "reason" fields).bind SExpr.stringValue?
            | throw "non-admission lacks evidence reason"
          let .atom (.symbol category) ← oracleField fields "category"
            | throw "non-admission lacks category"
          let .atom (.symbol _) ← oracleField fields "stage"
            | throw "non-admission lacks a stage"
          if !["type/domain-rejected", "context-unsupported", "grammar-unsupported",
              "expansion-domain-unavailable", "malformed-input",
              "unclassified-non-admission"].contains category then
            throw "unknown non-admission category"
          if (SExpr.field? "term" fields).isSome then
            throw "unavailable oracle must not carry a usable target"
          pure {
            id
            available := false
            term := none
            reason := some reason
            context := "unavailable"
            category := some category }
      | _ => .error s!"Redex oracle case {id} has bad status"
  | value => .error s!"malformed Redex oracle case: {repr value}"

def decodeRedexOracle : SExpr → Except String (List RedexOracleCase)
  | .list _ [
      .atom (.symbol "smusni-m2-redex-oracle"),
      .atom (.symbol "2"),
      .list _ [.atom (.symbol "count"), .atom (.symbol rawCount)],
      .list _ (.atom (.symbol "cases") :: cases)] => do
        let some count := rawCount.toNat?
          | .error "Redex oracle count is not natural"
        if cases.length != count then
          .error "Redex oracle count mismatch"
        let decoded ← cases.mapM decodeRedexOracleCase
        if !(decoded.any (·.available)) then throw "empty typed oracle; refusing vacuous parity"
        let ids := decoded.map (·.id)
        if ids.length != ids.eraseDups.length then throw "duplicate oracle case"
        pure decoded
  | _ => .error "bad Redex oracle root/version"

structure ParityDifference where
  id : String
  part : String
  detail : String
  knownIssue : Option Nat := none
  deriving Repr

structure ParityRun where
  cohort : Nat
  oracleAvailable : Nat
  oracleUnavailable : Nat
  wholeA0Available : Nat
  assertBridgeAvailable : Nat
  unavailableCategories : List (String × Nat)
  compared : Nat
  termMatches : Nat
  siteMatches : Nat
  knownBlockerDifferences : Nat
  unexplainedDifferences : Nat
  differences : List ParityDifference
  deriving Repr

def ParityRun.validate (run : ParityRun) : Except String Unit := do
  if run.wholeA0Available + run.assertBridgeAvailable != run.oracleAvailable ||
      run.oracleAvailable == 0 then
    throw "empty or inconsistent typed context partition"
  if run.oracleAvailable + run.oracleUnavailable != run.cohort then
    throw "parity oracle partition does not cover the cohort"
  if run.compared != run.oracleAvailable then
    throw s!"parity skipped available targets: available={run.oracleAvailable}, compared={run.compared}"
  if run.termMatches != run.compared then
    throw s!"parity term mismatch: compared={run.compared}, matches={run.termMatches}"
  if run.siteMatches != run.compared then
    throw s!"parity site mismatch: compared={run.compared}, matches={run.siteMatches}"
  if !run.differences.isEmpty then
    throw s!"parity has {run.differences.length} recorded differences"
  if run.knownBlockerDifferences != 0 || run.unexplainedDifferences != 0 then
    throw "parity difference counters are nonzero"

def runM2ParityMutationGates : IO Unit := do
  let bridge ← IO.ofExcept <| SExpr.parse
    "(case (id \"bridge-control\") (status available) (context assert-bridge) (source-type (Act Assertion)) (source-typing (typing (Act Assertion) () ((presuppose top Content)))) (target-typing (typing (Act Assertion) () ((presuppose top Content)))) (payload-source-typing (typing Content (projective) ((presuppose top Content)))) (payload-target-typing (typing Content (projective) ((presuppose top Content)))) (term (Assert (Presuppose top top))))"
  let original ← IO.ofExcept (decodeRedexOracleCase bridge)
  if !original.available || original.context != "assert-bridge" then
    throw <| IO.userError "positive Assert certificate was not admitted"
  let replaceField := fun (record : SExpr) (name : String) (value : SExpr) =>
    match record with
    | .list bracket (head :: fields) => .list bracket <| head :: fields.map fun field =>
        match field with
        | .list b [.atom (.symbol key), _] =>
            if key == name then .list b [.atom (.symbol key), value] else field
        | _ => field
    | _ => record
  for (name, source) in [
      ("term", "(Presuppose top top)"),
      ("source-type", "Content"),
      ("context", "recursive-assert"),
      ("source-typing", "(typing (Act Assertion) () ())"),
      ("target-typing", "(typing (Act Assertion) () ())"),
      ("source-typing", "(typing (Act Assertion) (projective) ((presuppose top Content)))"),
      ("payload-source-typing", "(typing ClauseContent () ())")] do
    let value ← IO.ofExcept (SExpr.parse source)
    if (decodeRedexOracleCase (replaceField bridge name value)).isOk then
      throw <| IO.userError s!"oracle certificate mutation accepted: {name}={source}"
  for category in ["type/domain-rejected", "context-unsupported", "grammar-unsupported",
      "expansion-domain-unavailable", "malformed-input", "unclassified-non-admission"] do
    let source := s!"(case (id \"negative\") (status unavailable) (category {category}) (stage source) (reason \"explicit evidence\"))"
    let parsed ← IO.ofExcept (SExpr.parse source)
    let rejected ← IO.ofExcept (decodeRedexOracleCase parsed)
    if rejected.available || rejected.term.isSome then
      throw <| IO.userError s!"non-admission became available: {category}"
    let empty ← IO.ofExcept <| SExpr.parse s!"(smusni-m2-redex-oracle 2 (count 1) (cases {source}))"
    if (decodeRedexOracle empty).isOk then
      throw <| IO.userError "all-unavailable oracle passed the empty-oracle guard"
  let some row := lookupLexicalRow "tavla"
    | throw <| IO.userError "parity swap probe lacks the tavla row"
  let speaker : Term 0 := .primitive .speaker .nil
  let audience : Term 0 := .primitive .audience .nil
  let first : Term 0 := .lexical "tavla" <|
    .labelled ":2" speaker (.labelled ":1" audience .nil)
  let second : Term 0 := .lexical "tavla" <|
    .labelled ":1" speaker (.labelled ":2" audience .nil)
  let firstRouted ← IO.ofExcept <| canonicalizeLexicalLabels first
  let secondRouted ← IO.ofExcept <| canonicalizeLexicalLabels second
  if Interchange.renderCanonicalTerm firstRouted ==
      Interchange.renderCanonicalTerm secondRouted then
    throw <| IO.userError "row routing erased swapped tavla places"
  let duplicated : TermList 0 :=
    .labelled ":1" speaker (.labelled ":1" audience .nil)
  if (routeLexicalArguments row duplicated).isOk then
    throw <| IO.userError "row routing accepted a duplicate lexical place"
  let clean : ParityRun := {
    cohort := 1
    oracleAvailable := 1
    oracleUnavailable := 0
    wholeA0Available := 1
    assertBridgeAvailable := 0
    unavailableCategories := []
    compared := 1
    termMatches := 1
    siteMatches := 1
    knownBlockerDifferences := 0
    unexplainedDifferences := 0
    differences := [] }
  if !clean.validate.isOk then
    throw <| IO.userError "clean parity mutation control failed"
  let forcedDifference := { clean with
    termMatches := 0
    unexplainedDifferences := 1
    differences := [{ id := "mutation", part := "term", detail := "forced" }] }
  if forcedDifference.validate.isOk then
    throw <| IO.userError "forced parity difference did not fail the gate"
  let skippedAvailable := { clean with
    compared := 0
    termMatches := 0
    siteMatches := 0 }
  if skippedAvailable.validate.isOk then
    throw <| IO.userError "available-but-uncompared parity target did not fail the gate"

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
      if oracleCase.context == "assert-bridge" then
        match corpusCase.term with
        | .list _ [.atom (.symbol "Assert"), _] => pure ()
        | _ => throw <| IO.userError "Assert certificate attached to a different source context"
      let some outcome := caseRun.outcomes.find? fun item => item.id == oracleCase.id
        | throw <| IO.userError s!"oracle case {oracleCase.id} absent from M2 run"
      match outcome.term with
      | none =>
          differences := differences ++ [{
            id := oracleCase.id
            part := "term"
            detail := s!"Lean produced no term for an available oracle target ({repr outcome.disposition})" }]
      | some leanTerm =>
          let surface := SurfaceTerm.ofSExprWithLexicon lexicalHeads rawOracle
          let freeNames := freeNamesFromEnvironment corpusCase.environment
          match Interchange.Bundle.ofSurfaceWith oracleCase.id lexicalHeads freeNames none surface with
          | .error detail =>
              differences := differences ++ [{
                id := oracleCase.id, part := "oracle-decode", detail }]
          | .ok redexBundle =>
              compared := compared + 1
              match canonicalizeLexicalLabels (eraseSiteIds leanTerm),
                  canonicalizeLexicalLabels (eraseSiteIds redexBundle.term) with
              | .ok leanRouted, .ok redexRouted =>
                  let leanCanonical := Interchange.renderCanonicalTerm leanRouted
                  let redexCanonical := Interchange.renderCanonicalTerm redexRouted
                  if leanCanonical == redexCanonical then
                    termMatches := termMatches + 1
                  else
                    differences := differences ++ [{
                      id := oracleCase.id
                      part := "term"
                      detail := "alpha-normal CoreTerm differs after SiteId erasure and row routing"
                      knownIssue := if outcome.expandedDefinitions.contains .d46Close then
                        some 81 else none }]
              | .error detail, _ | _, .error detail =>
                  differences := differences ++ [{
                    id := oracleCase.id
                    part := "row-routing"
                    detail }]
              let leanSites := emittedSiteSignature leanTerm
              let redexSites := emittedSiteSignature redexBundle.term
              if leanSites == redexSites then
                siteMatches := siteMatches + 1
              else
                differences := differences ++ [{
                  id := oracleCase.id
                  part := "sites"
                  detail := s!"Lean={repr leanSites}; Redex={repr redexSites}"
                  knownIssue := if outcome.expandedDefinitions.contains .d46Close then
                    some 81 else none }]
  let available := oracle.countP (·.available)
  let categories := (oracle.filterMap (·.category)).eraseDups
  pure {
    cohort := oracle.length
    oracleAvailable := available
    oracleUnavailable := oracle.length - available
    wholeA0Available := oracle.countP fun item => item.available && item.context == "whole-a0"
    assertBridgeAvailable := oracle.countP fun item => item.available && item.context == "assert-bridge"
    unavailableCategories := categories.map fun category =>
      (category, oracle.countP fun item => item.category == some category)
    compared
    termMatches
    siteMatches
    knownBlockerDifferences := differences.countP fun difference =>
      difference.knownIssue == some 81
    unexplainedDifferences := differences.countP fun difference =>
      difference.knownIssue.isNone
    differences }

end M2
end SmusniPilot
