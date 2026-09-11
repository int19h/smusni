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
  evidence : List SExpr
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
          let allowed := ["id", "status", "context", "source-type", "source-typing", "target-typing", "term"] ++
            (if context == "assert-bridge" then ["payload-source-typing", "payload-target-typing"] else [])
          if names.any fun name => !allowed.contains name then throw "unknown/forbidden oracle evidence field"
          pure { id, available := true, term := some term, reason := none, context, category := none, evidence := fields }
      | .atom (.symbol "unavailable") =>
          if names.any fun name => !["id", "status", "category", "stage", "reason"].contains name then
            throw "unknown/forbidden non-admission evidence field"
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
            category := some category
            evidence := fields }
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

structure OracleSourceContract where
  id : String
  context : String
  typing : Option OracleTypingWitness
  payloadTyping : Option OracleTypingWitness := none
  deriving Repr

def decodeOracleSourceContract : SExpr → Except String OracleSourceContract
  | .list _ (.atom (.symbol "case") :: fields) => do
      let names ← fields.mapM fun
        | .list _ [.atom (.symbol name), _] => pure name
        | _ => throw "malformed source contract field"
      if names.length != names.eraseDups.length then throw "duplicate source contract field"
      let some id := (← oracleField fields "id").stringValue?
        | throw "source contract lacks id"
      match ← oracleField fields "status" with
      | .atom (.symbol "unavailable") =>
          if names.any fun name => !["id", "status"].contains name then
            throw "unknown non-typed source contract field"
          pure { id, context := "unavailable", typing := none }
      | .atom (.symbol "typed-source") =>
          let typing ← decodeOracleTyping (← oracleField fields "source-typing")
          match ← oracleField fields "context" with
          | .atom (.symbol "whole-a0") =>
              if names.any fun name => !["id", "status", "context", "source-typing"].contains name then
                throw "unknown ordinary source contract evidence"
              pure { id, context := "whole-a0", typing := some typing }
          | .atom (.symbol "assert-bridge") =>
              if names.any fun name =>
                  !["id", "status", "context", "source-typing", "payload-source-typing"].contains name then
                throw "unknown bridge source contract evidence"
              let payload ← decodeOracleTyping (← oracleField fields "payload-source-typing")
              if typing != (← assertOracleWitness payload) then
                throw "independent source contract violates Assert law"
              pure { id, context := "assert-bridge", typing := some typing, payloadTyping := some payload }
          | _ => throw "unknown source contract context"
      | _ => throw "unknown source contract status"
  | _ => throw "malformed source contract"

def decodeOracleSourceContracts : SExpr → Except String (List OracleSourceContract)
  | .list _ [.atom (.symbol "smusni-m2-oracle-sources"), .atom (.symbol "1"),
      .list _ [.atom (.symbol "count"), .atom (.symbol count)],
      .list _ (.atom (.symbol "cases") :: cases)] => do
      if count.toNat? != some cases.length then throw "source contract count mismatch"
      cases.mapM decodeOracleSourceContract
  | _ => throw "malformed source contract root/version"

def requireSameIds (label : String) (actual expected : List String) : Except String Unit := do
  if actual.length != actual.eraseDups.length || expected.length != expected.eraseDups.length then
    throw s!"{label}: duplicate IDs"
  if expected.isEmpty || !(actual.all expected.contains) || !(expected.all actual.contains) then
    throw s!"{label}: missing/extra IDs relative to independent selected cohort"

def sourceContext (source : SExpr) : String :=
  match source with
  | .list _ [.atom (.symbol "Assert"), _] => "assert-bridge"
  | _ => "whole-a0"

def oracleWitnessType (witness : OracleTypingWitness) : Except String Ty :=
  decodeTy (SurfaceTerm.ofSExpr witness.type)

-- Surface type decoding represents force words as variables; the executable
-- act constructors use closed indices. Reconcile only those declared index
-- positions, then use the existing compatibility relation (including genuine
-- checking refinements), not a new subtype rule or literal-type shortcut.
def normalizeOracleType : Ty → Ty
  | .named name arguments =>
      let arguments := arguments.map normalizeOracleType
      let arguments := if name == .typeFormAct || name == .typeFormActOccurrence then
        arguments.map fun
          | .variable "Assertion" => Ty.assertion
          | .variable "Expressive" => Ty.expressive
          | other => other
        else arguments
      .named name arguments
  | .function effectful parameters result =>
      .function effectful (parameters.map normalizeOracleType) (normalizeOracleType result)
  | other => other

def oracleCompatible (actual expected : Ty) : Bool :=
  Ty.compatible (normalizeOracleType actual) (normalizeOracleType expected)

def decodedLambdaType (effectful : Bool) (parameters : List Ty) (result : Ty) : Ty :=
  match parameters with
  | [] => .function effectful [] result
  | [parameter] => .function effectful [parameter] result
  | parameter :: rest => .function false [parameter] (decodedLambdaType effectful rest result)

-- A0 keeps a joint source lambda's parameter vector; M1's actual decoder
-- emits nested unary lambdas. Adapt that source syntax only. Do not identify
-- arbitrary function-valued results or change the semantic compatibility law.
partial def expectedTypeForDecodedSource (source : SurfaceTerm) (expected : Ty) : Except String Ty := do
  match source, expected with
  | .form _ (.primitive .lambda) [binders, body], .function effectful parameters result =>
      let binders ← decodeBinderGroup binders
      if binders.length != parameters.length then
        throw "source binder group disagrees with independent A0 parameter vector"
      let result ← expectedTypeForDecodedSource body result
      pure (decodedLambdaType effectful parameters result)
  | .form _ (.defined .let) [_, _, body], _ => expectedTypeForDecodedSource body expected
  | .form _ (.primitive .bind) arguments, _ =>
      let (_, body) ← decodeBindClauses arguments
      expectedTypeForDecodedSource body expected
  | _, _ => pure expected

def validateJoinedOracle (oracle : RedexOracleCase) (source : CorpusCase)
    (contract : OracleSourceContract) : Except String Ty := do
  if oracle.context != sourceContext source.term || oracle.context != contract.context then
    throw s!"{oracle.id}: oracle context disagrees with actual source"
  let some sourceTyping := contract.typing
    | throw s!"{oracle.id}: no independent source typing"
  let expected ← oracleWitnessType sourceTyping
  let declaredSource ← decodeOracleTyping (← oracleField oracle.evidence "source-typing")
  let declaredTarget ← decodeOracleTyping (← oracleField oracle.evidence "target-typing")
  if declaredSource != sourceTyping then
    throw s!"{oracle.id}: source witness differs from independent source contract"
  let targetType ← oracleWitnessType declaredTarget
  if !oracleCompatible targetType expected then
    throw s!"{oracle.id}: target witness is incompatible with independent expected type"
  if oracle.context == "assert-bridge" then
    let payload ← decodeOracleTyping (← oracleField oracle.evidence "payload-source-typing")
    if contract.payloadTyping != some payload then
      throw s!"{oracle.id}: bridge source payload witness changed"
  pure expected

def validateTypedParityOutcome (environment : Environment 0) (expected : Ty)
    (outcome : CaseOutcome) : Except String (Term 0) := do
  if outcome.disposition != .typedUnchanged && outcome.disposition != .typeDirectedExpansion then
    throw s!"{outcome.id}: rejected/non-successful outcome is not typed parity"
  if outcome.error.isSome || !outcome.outputTypingAvailable || !outcome.outputTraceSupported ||
      outcome.typingTrace.isEmpty || !outcome.excludedTraceRules.isEmpty then
    throw s!"{outcome.id}: missing/failed output typing evidence"
  if outcome.disposition == .typedUnchanged &&
      (!outcome.inputTypingAvailable || !outcome.inputTraceSupported) then
    throw s!"{outcome.id}: unchanged outcome lacks input typing evidence"
  let some type := outcome.type | throw s!"{outcome.id}: no output type"
  let some term := outcome.term | throw s!"{outcome.id}: no successful output term"
  -- Replay the actual existing checker, not a second typing relation or a
  -- predicate that trusts flags attached to an AST retained for diagnostics.
  let typed ← (synth environment term).mapError fun error =>
    s!"{outcome.id}: output typing failed: {error.code}"
  if typed.type != type || typed.effects != outcome.effects ||
      typed.trace != outcome.typingTrace || !typingTraceSupported typed then
    throw s!"{outcome.id}: outcome evidence disagrees with actual successful typing"
  if !oracleCompatible type expected then
    throw s!"{outcome.id}: output type {repr type} incompatible with independent expected {repr expected}"
  pure term

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

def compareM2Parity (selected : List String) (sources : List OracleSourceContract)
    (corpus : List CorpusCase) (manifestCases : Array S1CaseRecord)
    (lexicalHeads : List String) (caseRun : CaseRun) (oracle : List RedexOracleCase) :
    Except String ParityRun := do
  requireSameIds "oracle/cohort" (oracle.map (·.id)) selected
  requireSameIds "source-contract/cohort" (sources.map (·.id)) selected
  requireSameIds "corpus/S1" (corpus.map (·.id)) (manifestCases.toList.map (·.id))
  requireSameIds "outcomes/corpus" (caseRun.outcomes.map (·.id)) (corpus.map (·.id))
  let mut compared := 0
  let mut termMatches := 0
  let mut siteMatches := 0
  let mut differences : List ParityDifference := []
  for oracleCase in oracle do
    let some corpusCase := corpus.find? fun item => item.id == oracleCase.id
      | throw s!"oracle case {oracleCase.id} absent from corpus"
    let some contract := sources.find? fun item => item.id == oracleCase.id
      | throw s!"oracle case {oracleCase.id} lacks independent source contract"
    let some outcome := caseRun.outcomes.find? fun item => item.id == oracleCase.id
      | throw s!"oracle case {oracleCase.id} absent from M2 outcomes"
    if oracleCase.available then
      let some rawOracle := oracleCase.term | throw "available oracle has no target"
      let expected ← validateJoinedOracle oracleCase corpusCase contract
      let expected ← expectedTypeForDecodedSource
        (SurfaceTerm.ofSExprWithLexicon lexicalHeads corpusCase.term) expected
      let environment ← environmentForCorpus corpusCase.environment
      match validateTypedParityOutcome environment expected outcome with
      | .error detail =>
          differences := differences ++ [{ id := oracleCase.id, part := "typed-outcome", detail }]
      | .ok leanTerm =>
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

def loadM2ParityData (root : String) : IO (List String × List OracleSourceContract × List CorpusCase × S1Manifest × List String × List RedexOracleCase) := do
  let oracleSource ← IO.FS.readFile (root ++ "/pilot/shared/M2_REDEX_ORACLE.sexp")
  let oracle ← IO.ofExcept (SExpr.parse oracleSource >>= decodeRedexOracle)
  let manifestSource ← IO.FS.readFile (root ++ "/pilot/shared/M1_S1_MANIFEST.json")
  let manifest : S1Manifest ← IO.ofExcept (Json.parse manifestSource >>= fromJson?)
  let corpusSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.port_corpus)
  let corpus ← IO.ofExcept (SExpr.parse corpusSource >>= decodeCorpus)
  let fixtureSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.fixtures)
  let lexicalHeads ← IO.ofExcept (SExpr.parse fixtureSource >>= decodeLexicalHeads)
  let cohortSource ← IO.FS.readFile (root ++ "/pilot/shared/M2_CASE_MANIFEST.json")
  let cohort ← IO.ofExcept (Json.parse cohortSource)
  let schema ← IO.ofExcept (cohort.getObjValAs? String "schema")
  let version ← IO.ofExcept (cohort.getObjValAs? Nat "version")
  if schema != "smusni-lean-m2-case-manifest" || version != 1 then
    throw <| IO.userError "unsupported independent cohort manifest"
  let cohortSources ← IO.ofExcept (cohort.getObjVal? "sources")
  let s1Digest ← IO.ofExcept (cohortSources.getObjValAs? String "s1_sha256")
  let definitionDigest ← IO.ofExcept (cohortSources.getObjValAs? String "definitions_sha256")
  if s1Digest != (← sha256File root "pilot/shared/M1_S1_MANIFEST.json") ||
      definitionDigest != (← sha256File root "pilot/shared/M2_DEFINITION_MANIFEST.json") then
    throw <| IO.userError "independent cohort source digests disagree with current inputs"
  let selected ← IO.ofExcept <| do
    let cohorts ← cohort.getObjVal? "cohorts"
    fromJson? (← cohorts.getObjVal? "definition_parity")
  let sourceContracts ← IO.FS.readFile (root ++ "/pilot/shared/M2_ORACLE_SOURCES.sexp")
  let sources ← IO.ofExcept (SExpr.parse sourceContracts >>= decodeOracleSourceContracts)
  let actualDigest ← sha256File root manifest.sources.port_corpus
  if actualDigest != manifest.sources.port_corpus_sha256 then
    throw <| IO.userError "parity source corpus digest mismatch"
  pure (selected, sources, corpus, manifest, lexicalHeads, oracle)

def oracleSymbol (name : String) : SExpr := .atom (.symbol name)

def editOracleField (record : SExpr) (name : String) (value : SExpr) : SExpr :=
  match record with
  | .list b (head :: fields) => .list b (head :: fields.map fun field =>
      match field with
      | .list fb [.atom (.symbol key), _] =>
          if key == name then .list fb [oracleSymbol key, value] else field
      | _ => field)
  | _ => record

def dropOracleFields (record : SExpr) (names : List String) : SExpr :=
  match record with
  | .list b (head :: fields) => .list b (head :: fields.filter fun field =>
      match field with
      | .list _ [.atom (.symbol name), _] => !names.contains name
      | _ => true)
  | _ => record

def runM2ConsumerMutationGates (selected : List String) (sources : List OracleSourceContract)
    (corpus : List CorpusCase) (manifestCases : Array S1CaseRecord)
    (lexicalHeads : List String) (caseRun : CaseRun) (oracle : List RedexOracleCase) : IO Unit := do
  let rows := oracle.map fun item => SExpr.list .paren (oracleSymbol "case" :: item.evidence)
  let encode := fun (records : List SExpr) => SExpr.list .paren [
    oracleSymbol "smusni-m2-redex-oracle", oracleSymbol "2",
    .list .paren [oracleSymbol "count", oracleSymbol (toString records.length)],
    .list .paren (oracleSymbol "cases" :: records)]
  let expectFailure := fun (name : String) (records : List SExpr) (outcomes : CaseRun) => do
    let result : Except String ParityRun := do
      let parsed ← decodeRedexOracle (encode records)
      let compared ← compareM2Parity selected sources corpus manifestCases lexicalHeads outcomes parsed
      compared.validate
      pure compared
    if result.isOk then throw <| IO.userError s!"production parity accepted mutation: {name}"
  let some unavailable := oracle.find? fun item => !item.available
    | throw <| IO.userError "consumer mutation requires a selected unavailable case"
  let some bridge := oracle.find? fun item => item.available && item.context == "assert-bridge"
    | throw <| IO.userError "consumer mutation requires a bridge case"
  let some whole := oracle.find? fun item => item.available && item.context == "whole-a0" &&
      SExpr.field? "source-type" item.evidence == some (oracleSymbol "Content")
    | throw <| IO.userError "consumer mutation requires an ordinary Content case"
  let some outside := corpus.find? fun item => !selected.contains item.id
    | throw <| IO.userError "consumer mutation requires a known unselected source"
  let row := fun (item : RedexOracleCase) => SExpr.list .paren (oracleSymbol "case" :: item.evidence)
  let replace := fun (item : RedexOracleCase) (changed : SExpr) =>
    rows.map fun original => if original == row item then changed else original
  let wrongType ← IO.ofExcept (SExpr.parse "(typing (Act Assertion) () ())")
  let wrongContext := dropOracleFields
    (editOracleField (row bridge) "context" (oracleSymbol "whole-a0"))
    ["payload-source-typing", "payload-target-typing"]
  let unknownEvidence := SExpr.list .paren <| oracleSymbol "case" :: whole.evidence ++
    [.list .paren [oracleSymbol "unknown-evidence", oracleSymbol "true"]]
  let duplicateEvidence := SExpr.list .paren <| oracleSymbol "case" :: whole.evidence ++
    [.list .paren [oracleSymbol "target-typing", wrongType]]
  let sourceTypeMutation := editOracleField
    (editOracleField (row whole) "source-type"
      (.list .paren [oracleSymbol "Act", oracleSymbol "Assertion"]))
    "source-typing" wrongType
  let mutations := [
    ("unknown-unavailable-join", replace unavailable <| editOracleField (row unavailable) "id"
      (.atom (.string "not-a-selected-or-corpus-case"))),
    ("missing-unavailable-adjusted-count", rows.filter fun item => item != row unavailable),
    ("known-but-not-selected", replace unavailable <| editOracleField (row unavailable) "id"
      (.atom (.string outside.id))),
    ("duplicate-id", rows ++ [row unavailable]),
    ("bridge-relabelled-whole-a0", replace bridge wrongContext),
    ("whole-a0-wrong-target-type", replace whole <| editOracleField (row whole) "target-typing" wrongType),
    ("self-consistent-wrong-source-type", replace whole sourceTypeMutation),
    ("missing-source-evidence", replace whole <| dropOracleFields (row whole) ["source-typing"]),
    ("unknown-evidence", replace whole unknownEvidence),
    ("duplicate-evidence", replace whole duplicateEvidence)]
  for (name, records) in mutations do expectFailure name records caseRun
  let some original := caseRun.outcomes.find? fun item => item.id == whole.id
    | throw <| IO.userError "consumer mutation lacks original classifier outcome"
  let rejection : CaseOutcome := { original with
    disposition := .typedRejection
    decidingRule := "type-mismatch"
    type := none
    effects := []
    error := some { code := "type-mismatch", detail := "classifier-shaped rejected output" }
    inputTypingAvailable := false
    inputTraceSupported := false
    outputTypingAvailable := false
    outputTraceSupported := false
    typingTrace := []
    excludedTraceRules := [] }
  let outcomeMutations : List (String × CaseOutcome) := [
    ("classifier-rejection-retains-AST", rejection),
    ("rejection-label-retains-other-evidence", { original with disposition := .typedRejection }),
    ("missing-type", { original with type := none }),
    ("missing-output-typing", { original with outputTypingAvailable := false }),
    ("failed-output-typing", { original with error := rejection.error }),
    ("missing-trace", { original with typingTrace := [] }),
    ("incompatible-type", { original with type := some (Ty.act Ty.assertion) }),
    ("actually-ill-typed-retained-AST", { original with term := some (.apply (.natural 1) .nil) })]
  for (name, changed) in outcomeMutations do
    let mutated := CaseRun.ofOutcomes <| caseRun.outcomes.map fun item =>
      if item.id == whole.id then changed else item
    if name == "classifier-rejection-retains-AST" && !mutated.validateTypingCoverage.isOk then
      throw <| IO.userError "classifier-shaped control no longer isolates the parity gate"
    expectFailure name rows mutated

  -- Positive checking refinement: actual Natural remains Natural while the
  -- independent expected type is Number. This tests the real checker and
  -- compatibility relation rather than weakening types to equality.
  let typed ← IO.ofExcept <| (synth Environment.empty (.natural 417 : Term 0)).mapError (·.detail)
  let refined : CaseOutcome := {
    id := "checking-refinement"
    originalTag := "primitive-core"
    disposition := .typedUnchanged
    decidingRule := "bidirectional typing"
    type := some typed.type
    effects := typed.effects
    term := some (.natural 417)
    inputTypingAvailable := true
    inputTraceSupported := true
    outputTypingAvailable := true
    outputTraceSupported := true
    typingTrace := typed.trace }
  discard <| IO.ofExcept (validateTypedParityOutcome Environment.empty Ty.number refined)
  let refinementRecord ← IO.ofExcept <| SExpr.parse
    "(case (id \"checking-refinement\") (status available) (context whole-a0) (source-type Number) (source-typing (typing Number () ())) (target-typing (typing Natural () ())) (term 417))"
  let refinementOracle ← IO.ofExcept (decodeRedexOracleCase refinementRecord)
  let sourceTyping ← IO.ofExcept <| SExpr.parse "(typing Number () ())" >>= decodeOracleTyping
  let source : CorpusCase := {
    id := refined.id
    provenance := oracleSymbol "test"
    term := oracleSymbol "$number"
    environment := .list .paren [.list .paren [oracleSymbol "$number", oracleSymbol "Number"]]
    inventory := [] }
  let contract : OracleSourceContract := { id := refined.id, context := "whole-a0", typing := some sourceTyping }
  discard <| IO.ofExcept (validateJoinedOracle refinementOracle source contract)
  let joint ← IO.ofExcept <| SExpr.parse "(λ (($x :: Entity) ($n :: Number)) (∧))"
  let projected ← IO.ofExcept <| expectedTypeForDecodedSource (SurfaceTerm.ofSExpr joint)
    (Ty.pureFn [Ty.entity, Ty.number] Ty.content)
  if projected != Ty.pureFn [Ty.entity] (Ty.pureFn [Ty.number] Ty.content) then
    throw <| IO.userError "joint source lambda did not use the decoder's unary grouping"
  if !oracleCompatible (Ty.act Ty.assertion) (Ty.act (.variable "Assertion")) ||
      oracleCompatible (Ty.act Ty.expressive) (Ty.act (.variable "Assertion")) then
    throw <| IO.userError "closed force-index normalization changed force identity"
  IO.println s!"M2 production consumer mutations={mutations.length + outcomeMutations.length} positive-refinements=2 PASS"

def runM2Parity (root : String) (caseRun : CaseRun) : IO ParityRun := do
  let (selected, sources, corpus, manifest, lexicalHeads, oracle) ← loadM2ParityData root
  runM2ConsumerMutationGates selected sources corpus manifest.cases lexicalHeads caseRun oracle
  IO.ofExcept <| compareM2Parity selected sources corpus manifest.cases lexicalHeads caseRun oracle

end M2
end SmusniPilot
