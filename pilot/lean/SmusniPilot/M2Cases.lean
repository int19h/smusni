import SmusniPilot.S1
import SmusniPilot.M2Templates

namespace SmusniPilot
namespace M2

open Lean

inductive CaseDisposition where
  | typedUnchanged
  | typeDirectedExpansion
  | typedRejection
  | pendingMilestone3
  | blocked
  | inputUnavailable
  | outOfSlice
  deriving Repr, DecidableEq, BEq

structure CoreElaborationState where
  nextOccurrence : Nat := 0
  definitions : List M2DefinitionId := []
  clauses : List M2ClauseId := []
  deriving Repr, Inhabited

def overloadDefinition (operator : FirstOrderPrimitive) :
    Option M2DefinitionId :=
  let head := rawTermName operator.name
  (m2DefinitionRecords.find? fun record => record.head == head).map (·.id)

def expectedReferMember (expected : Option Ty) : Option Ty := do
  let expected ← expected
  let computation ← Ty.asUnary expected .typeFormRefComp
  Ty.asUnary computation .typeFormReferents

def coreElaborationFailure (code detail : String) :
    Except TypingError α :=
  .error { code, detail }

mutual
  partial def elaborateCore {scope : Nat} (document : String)
      (environment : Environment scope) (expected : Option Ty)
      (term : Term scope) (state : CoreElaborationState) :
      Except TypingError (Term scope × CoreElaborationState) := do
    match term with
    | .bound _ | .free _ | .natural _ | .string _ | .index _ =>
        pure (term, state)
    | .lambda binderType body =>
        let (body, state) ← elaborateCore document
          (environment.extend binderType) none body state
        pure (.lambda binderType body, state)
    | .bind binderType computation body =>
        let (computation, state) ← elaborateCore document environment
          (some (Ty.refComp binderType)) computation state
        let (body, state) ← elaborateCore document
          (environment.extend binderType) none body state
        pure (.bind binderType computation body, state)
    | .apply function arguments =>
        let (function, state) ← elaborateCore document environment none function state
        let (arguments, state) ←
          elaborateCoreList document environment arguments state
        pure (.apply function arguments, state)
    | .lexical predicate arguments =>
        let (arguments, state) ←
          elaborateCoreList document environment arguments state
        pure (.lexical predicate arguments, state)
    | .context site arguments =>
        let (arguments, state) ←
          elaborateCoreList document environment arguments state
        pure (.context site arguments, state)
    | .vague site constraint =>
        let (constraint, state) ←
          elaborateCore document environment none constraint state
        pure (.vague site constraint, state)
    | .primitive operator arguments =>
        let (arguments, state) ←
          elaborateCoreList document environment arguments state
        let primitiveTerm := Term.primitive operator arguments
        match overloadDefinition operator, expectedReferMember expected with
        | some definition, some memberType =>
            if definition != .d53ReferMemberLift || operator != .refer then
              pure (primitiveTerm, state)
            else do
              let [property] ← positionalTerms arguments
                | coreElaborationFailure "refer-arity" "Refer expects one property"
              let propertyResult ← synth environment property
              match propertyResult.type with
              | .function effectful [parameter] result =>
                  if result != Ty.content then
                    return ← coreElaborationFailure "refer-property"
                      "Refer property does not return Content"
                  else if parameter == Ty.referents memberType then
                    return (primitiveTerm, state)
                  else if parameter == memberType && !effectful &&
                      isPure propertyResult then
                    let expansion := expandReferMember memberType property
                    match expansion.validate definition with
                    | .error detail =>
                        return ← coreElaborationFailure "template-certificate" detail
                    | .ok _ =>
                        let updated : CoreElaborationState := {
                          nextOccurrence := state.nextOccurrence + 1
                          definitions := state.definitions ++ [definition]
                          clauses := state.clauses ++ expansion.clauses }
                        return (expansion.term, updated)
                  else if parameter == memberType &&
                      (effectful || !isPure propertyResult) then
                    return ← coreElaborationFailure "refer-member-purity"
                      "effectful member property must be hoisted before Refer"
                  else
                    return ← coreElaborationFailure "refer-property"
                      "Refer property domain is incompatible with the expected member type"
              | _ => coreElaborationFailure "refer-property" "Refer property is not unary"
        | _, _ => pure (primitiveTerm, state)

  partial def elaborateCoreList {scope : Nat} (document : String)
      (environment : Environment scope) (terms : TermList scope)
      (state : CoreElaborationState) :
      Except TypingError (TermList scope × CoreElaborationState) := do
    match terms with
    | .nil => pure (.nil, state)
    | .positional head tail =>
        let (head, state) ← elaborateCore document environment none head state
        let (tail, state) ← elaborateCoreList document environment tail state
        pure (.positional head tail, state)
    | .labelled label head tail =>
        let (head, state) ← elaborateCore document environment none head state
        let (tail, state) ← elaborateCoreList document environment tail state
        pure (.labelled label head tail, state)
end

def decodeCorpusTypingEnvironment (environment : SExpr) : Except String
    (List (FreeId × Ty)) :=
  match environment with
  | .list _ entries => entries.mapM fun
      | .list _ [.atom (.symbol name), rawType] => do
          if !name.startsWith "$" then
            .error s!"environment identity is not a variable: {name}"
          let type ← decodeTy (SurfaceTerm.ofSExpr rawType)
          pure ({ domain := name, serial := 0 }, type)
      | value => .error s!"malformed typed environment entry: {repr value}"
  | value => .error s!"environment is not a list: {repr value}"

def environmentForCorpus (environment : SExpr) : Except String (Environment 0) := do
  pure { Environment.empty with free := ← decodeCorpusTypingEnvironment environment }

def dispositionForHead (head : SurfaceHead) : M2DefinitionDispositionRecord :=
  (m2DefinitionDispositionRecords.find? fun record =>
    record.head == rawTermName head.name).getD {
      id := "missing"
      head := rawTermName head.name
      status := "missing"
      issue := none
      portState := "none"
      selected := false
      reason := "surface head is absent from the generated definition catalog" }

def selectedSurfaceDefinitions (lexicalHeads : List String)
    (surface : SurfaceTerm) : List M2DefinitionId :=
  surface.definedHeadsWith lexicalHeads |>.filterMap fun head =>
    let disposition := dispositionForHead head
    if disposition.selected then
      (m2DefinitionRecords.find? fun record => record.head == disposition.head).map (·.id)
    else none

def unselectedSurfaceDefinitions (lexicalHeads : List String) (surface : SurfaceTerm) :
    List M2DefinitionDispositionRecord :=
  surface.definedHeadsWith lexicalHeads |>.map dispositionForHead
    |>.filter fun record => !record.selected

structure ExpansionPayload (scope : Nat) where
  term : Term scope
  clauses : List M2ClauseId
  sites : List ExpansionSite := []

def Expansion.payload {scope : Nat} (expansion : Expansion scope) :
    ExpansionPayload scope := {
  term := expansion.term
  clauses := expansion.clauses }

def SiteExpansion.payload {scope : Nat} (expansion : SiteExpansion scope) :
    ExpansionPayload scope := {
  term := expansion.term
  clauses := expansion.clauses
  sites := expansion.sites }

def memberTypeOfProperty {scope : Nat} (environment : Environment scope)
    (property : Term scope) : Except TypingError Ty := do
  let result ← synth environment property
  match result.type with
  | .function false [memberType] output =>
      if output == Ty.content && isPure result then return memberType
      else return ← coreElaborationFailure "definition-property" "definition restrictor is not a pure Content property"
  | _ => coreElaborationFailure "definition-property" "definition restrictor is not a pure unary function"

def referenceMemberType {scope : Nat} (environment : Environment scope)
    (reference : Term scope) : Except TypingError Ty := do
  let result ← synth environment reference
  let some member := Ty.referenceInner result.type
    | coreElaborationFailure "definition-reference"
        "definition operand is not referential"
  pure member

def decompositionTypes {scope : Nat} (environment : Environment scope)
    (basis : Term scope) : Except TypingError (Ty × Ty) := do
  let result ← synth environment basis
  let some types := Ty.asBinary result.type .typeFormDecompositionBasis
    | coreElaborationFailure "definition-basis"
        "definition basis is not DecompositionBasis<W,C>"
  pure types

def termAsList {scope : Nat} (term : Term scope) : Except TypingError
    (List (Term scope)) :=
  match term with
  | .primitive .list arguments =>
      positionalTerms arguments
  | _ => coreElaborationFailure "definition-list" "ZipWith expects List terms"

def isZeroTerm {scope : Nat} : Term scope → Bool
  | .natural 0 => true
  | _ => false

def assignFill {scope : Nat} :
    List (Option (Term scope)) → Nat → Term scope →
      Except TypingError (List (Option (Term scope)))
  | [], _, _ => coreElaborationFailure "close-label" "fill is outside the lexical row"
  | _ :: tail, 0, value => pure (some value :: tail)
  | head :: tail, index + 1, value =>
      return head :: (← assignFill tail index value)

def firstMissing : List (Option α) → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: tail => (firstMissing tail).map (· + 1)

def lexicalClosePlan {scope : Nat} (term : Term scope) :
    Except TypingError (ClosePlan scope) := do
  let (.lexical head arguments) := term
    | coreElaborationFailure "close-row"
        "Close row metadata is unavailable for a non-lexical predicate"
  let some row := lookupLexicalRow head
    | coreElaborationFailure "close-row" s!"missing generated row for {head}"
  let mut fills : List (Option (Term scope)) :=
    List.replicate row.ordinaryArity none
  let mut eventFill : Option (Term scope) := none
  for (label, value) in (← labelledTerms arguments) do
    match label with
    | none =>
        let some index := firstMissing fills
          | coreElaborationFailure "close-arity" "too many positional fills"
        fills ← assignFill fills index value
    | some ":Eventuality" =>
        if eventFill.isSome then
          coreElaborationFailure "close-label" "duplicate Eventuality fill"
        else if row.eventMode != .directEvent then
          coreElaborationFailure "close-label" "holding-state row has no Eventuality fill"
        else eventFill := some value
    | some label =>
        let some index := (label.drop 1).toString.toNat?
          | coreElaborationFailure "close-label" s!"unknown Close label {label}"
        if index == 0 then
          coreElaborationFailure "close-label" "ordinary labels are one-based"
        else pure ()
        if (fills[index - 1]?).join.isSome then
          coreElaborationFailure "close-label" s!"duplicate Close label {label}"
        else pure ()
        fills ← assignFill fills (index - 1) value
  let places := fills.zipIdx.map fun item => {
    label := ":" ++ toString (item.2 + 1)
    type := Ty.referents Ty.entity
    fill := item.1 }
  pure {
    predicate := .lexical head .nil
    places
    eventMode := if row.eventMode == .directEvent then
      .directEvent else .holdingState
    eventFill }

def typedClosePlan {scope : Nat} (environment : Environment scope)
    (term : Term scope) : Except TypingError (ClosePlan scope) :=
  match term with
  | .lexical _ _ => lexicalClosePlan term
  | _ => do
      let result ← synth environment term
      if result.type == Ty.content then
        pure {
          predicate := term
          places := []
          eventMode := .holdingState }
      else
        let some row := Ty.asUnary result.type .typeFormPredTerm
          | coreElaborationFailure "close-row"
              "Close operand is neither Content nor PredTerm<row>"
        let shape ← match rowShape row with
          | some shape => pure shape
          | none =>
              match row with
              | .named .typeFormRowOf [.variable head] =>
                  coreElaborationFailure "unknown-row" s!"RowOf {head} has no declared lexical row"
              | _ => coreElaborationFailure "close-row" "Close residual row shape is unavailable"
        let (ordinary, event) := shape
        pure {
          predicate := term
          places := (List.range ordinary).map fun index => {
            label := ":" ++ toString (index + 1)
            type := Ty.referents Ty.entity
            fill := none }
          eventMode := if event then .directEvent else .holdingState }

def dispatchDefinition {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) : Except TypingError (ExpansionPayload scope) := do
  let expansion ← match definition with
    | .d12ActualClause =>
        let [clause] := arguments
          | coreElaborationFailure "definition-arity" "ActualClause expects one argument"
        pure <| (expandActualClause clause).payload
    | .d12AtLeast =>
        let [count, property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "AtLeast expects three arguments"
        let memberType ← memberTypeOfProperty environment property
        if !isZeroTerm count && !provablyPositive count then
          coreElaborationFailure "definition-domain"
            "AtLeast symbolic-natural domain is not selected"
        pure <| (expandAtLeast memberType count property nuclear).payload
    | .d12AtMost =>
        let [count, property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "AtMost expects three arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandAtMost memberType count property nuclear).payload
    | .d12CanonicalAggregateAt =>
        let [basis, group, cover] := arguments
          | coreElaborationFailure "definition-arity"
              "CanonicalAggregateAt expects basis, group, and cover"
        let (_, componentType) ← decompositionTypes environment basis
        pure <| (expandCanonicalAggregateAt componentType basis group cover).payload
    | .d12CoRef =>
        let [first, second] := arguments
          | coreElaborationFailure "definition-arity" "CoRef expects two arguments"
        pure <| (expandCoRef first second).payload
    | .d12Distrib =>
        let [property, reference] := arguments
          | coreElaborationFailure "definition-arity" "Distrib expects two arguments"
        let memberType ← referenceMemberType environment reference
        pure <| (expandDistrib memberType property reference).payload
    | .d12Every =>
        let [property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "Every expects two arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandEvery memberType property nuclear).payload
    | .d12Exactly =>
        let [count, property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "Exactly expects three arguments"
        let memberType ← memberTypeOfProperty environment property
        if !isZeroTerm count && !provablyPositive count then
          coreElaborationFailure "definition-domain"
            "Exactly requires a zero or provably positive count"
        pure <| (expandExactly memberType count property nuclear).payload
    | .d12FewerThan =>
        let [count, property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "FewerThan expects three arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandFewerThan memberType count property nuclear).payload
    | .d12GlobalExactly =>
        let [count, property, nuclear] := arguments
          | coreElaborationFailure "definition-arity"
              "GlobalExactly expects three arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandGlobalExactly memberType count property nuclear).payload
    | .d12Grade => coreElaborationFailure "row-input-unavailable" "Grade requires a resolved DegreeField row input"
    | .d12JaiRaise => coreElaborationFailure "row-input-unavailable" "JaiRaise requires resolved row reconstruction metadata"
    | .d12Massify =>
        let [basis, cover] := arguments
          | coreElaborationFailure "definition-arity" "Massify expects basis and cover"
        let (_, componentType) ← decompositionTypes environment basis
        pure <| (expandMassify componentType basis cover).payload
    | .d12MaxRefer =>
        let [property] := arguments
          | coreElaborationFailure "definition-arity" "MaxRefer expects one property"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandMaxRefer memberType property).payload
    | .d12MoreThan =>
        let [count, property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "MoreThan expects three arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandMoreThan memberType count property nuclear).payload
    | .d12No =>
        let [property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "No expects two arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandNo memberType property nuclear).payload
    | .d12Overlap =>
        let [first, second] := arguments
          | coreElaborationFailure "definition-arity" "Overlap expects two arguments"
        let memberType ← referenceMemberType environment first
        pure <| (expandOverlap memberType first second).payload
    | .d12Some =>
        let [property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "Some expects two arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandSome memberType property nuclear).payload
    | .d12TooMany =>
        let [property, nuclear] := arguments
          | coreElaborationFailure "definition-arity" "TooMany expects two arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandTooMany memberType key property nuclear).payload
    | .d12ZipWith =>
        let [function, left, right] := arguments
          | coreElaborationFailure "definition-arity" "ZipWith expects three arguments"
        let left ← termAsList left
        let right ← termAsList right
        match expandZipWith function left right with
        | .ok expansion => pure expansion.payload
        | .error detail => coreElaborationFailure "definition-domain" detail
    | .d44Let => coreElaborationFailure "structural-dispatch" "Let is dispatched with its binder, value, and scoped body"
    | .d46Close =>
        let [predicate] := arguments
          | coreElaborationFailure "definition-arity" "Close expects one predicate"
        let plan ← typedClosePlan environment predicate
        match expandClose key plan with
        | .ok expansion => pure expansion.payload
        | .error detail => coreElaborationFailure "close-row" detail
    | .d46DirectClause =>
        let [predicate] := arguments
          | coreElaborationFailure "definition-arity" "DirectClause expects one predicate"
        let plan ← typedClosePlan environment predicate
        pure <| (expandDirectClause key plan.predicate plan.places).payload
    | .d48CoveredBy =>
        let [property, reference] := arguments
          | coreElaborationFailure "definition-arity" "CoveredBy expects two arguments"
        let memberType ← memberTypeOfProperty environment property
        pure <| (expandCoveredBy memberType property reference).payload
    | .d49CompleteGunmaAt =>
        let [basis, whole, cover] := arguments
          | coreElaborationFailure "definition-arity"
              "CompleteGunmaAt expects basis, whole, and cover"
        let (wholeType, componentType) ← decompositionTypes environment basis
        pure <| (expandCompleteGunmaAt wholeType componentType basis whole cover).payload
    | .d49GunmaAt =>
        let [basis, whole, cover] := arguments
          | coreElaborationFailure "definition-arity"
              "GunmaAt expects basis, whole, and cover"
        let (wholeType, componentType) ← decompositionTypes environment basis
        pure <| (expandGunmaAt wholeType componentType basis whole cover).payload
    | .d53ReferMemberLift => coreElaborationFailure "domain-overload" "Refer member lift is dispatched from the primitive head by expected type"
    | .d56SelectSome =>
        let [property] := arguments
          | coreElaborationFailure "definition-arity" "SelectSome expects one property"
        pure <| (expandSelectSome property).payload
  let checked : Expansion scope := { term := expansion.term, clauses := expansion.clauses }
  match checked.validate definition with
  | .error detail => coreElaborationFailure "template-certificate" detail
  | .ok _ => pure expansion

def selectedDefinitionForSpelling (spelling : String) : Option M2DefinitionId :=
  (m2DefinitionRecords.find? fun record => record.head == spelling).map (·.id)

partial def mechanismDefinitions (lexicalHeads : List String) :
    SurfaceTerm → List M2DefinitionId
  | .atom (.string _) | .empty _ => []
  | .atom (.symbol raw) =>
      if raw.toNat?.isSome || raw.startsWith "$" || raw.startsWith ":" ||
          lexicalHeads.contains raw then []
      else (selectedDefinitionForSpelling raw).toList
  | term@(.form _ (.variable _) arguments) =>
      if term.isBinderDescriptor then []
      else arguments.flatMap (mechanismDefinitions lexicalHeads)
  | .form _ kind arguments =>
      (selectedDefinitionForSpelling kind.spelling).toList ++
        arguments.flatMap (mechanismDefinitions lexicalHeads)
  | .application _ function arguments =>
      mechanismDefinitions lexicalHeads function ++
        arguments.flatMap (mechanismDefinitions lexicalHeads)

structure SurfaceElaborationState where
  decode : DecodeState := {}
  core : CoreElaborationState := {}
  deriving Repr, Inhabited

def expansionSiteEntry (rrLink : Option String) (site : ExpansionSite) :
    SiteEntry := {
  identity := site.identity
  role := site.roleKind
  dependencies := site.dependencies
  rrLink }

def SurfaceElaborationState.addExpansion (state : SurfaceElaborationState)
    (definition : M2DefinitionId) (payload : ExpansionPayload scope)
    (rrLink : Option String) : SurfaceElaborationState := {
  decode := { state.decode with
    sites := state.decode.sites ++ payload.sites.map (expansionSiteEntry rrLink) }
  core := { state.core with
    definitions := state.core.definitions ++ [definition]
    clauses := state.core.clauses ++ payload.clauses } }

def mapDecodeError {α : Type} : Except String α → Except TypingError α :=
  Except.mapError fun detail => { code := "surface-decode", detail }

mutual
  partial def elaborateSurface (document : String) (lexicalHeads freeNames : List String)
      (rrLink : Option String) (names : List String)
      (environment : Environment names.length) (expected : Option Ty)
      (surface : SurfaceTerm) (state : SurfaceElaborationState) :
      Except TypingError (Term names.length × SurfaceElaborationState) := do
    if (mechanismDefinitions lexicalHeads surface).isEmpty then
      let (term, decode) ← mapDecodeError <|
        decodeCore document lexicalHeads freeNames rrLink names surface state.decode
      let (term, core) ← elaborateCore document environment expected term state.core
      return (term, { decode, core })
    match surface with
    | .atom (.symbol spelling) =>
        let some definition := selectedDefinitionForSpelling spelling
          | coreElaborationFailure "definition-dispatch"
              s!"selected mechanism atom {spelling} has no definition ID"
        let occurrence := state.core.nextOccurrence
        let state := { state with core := {
          state.core with nextOccurrence := occurrence + 1 } }
        let key : ExpansionKey := { document, occurrence, definition }
        let payload ← dispatchDefinition environment key definition []
        pure (payload.term, state.addExpansion definition payload rrLink)
    | .atom _ | .empty _ =>
        coreElaborationFailure "surface-decode" "unexpected selected leaf"
    | .application _ function arguments =>
        let (function, state) ← elaborateSurface document lexicalHeads freeNames
          rrLink names environment none function state
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        let term := Term.apply function arguments
        let (term, core) ← elaborateCore document environment expected term state.core
        pure (term, { state with core })
    | .form _ (.defined .let) [binderTerm, value, body] =>
        let binder ← mapDecodeError (decodeBinder binderTerm)
        let some definition := selectedDefinitionForSpelling "Let"
          | coreElaborationFailure "definition-dispatch" "Let definition is absent"
        let occurrence := state.core.nextOccurrence
        let state := { state with
          decode := state.decode.recordSource document [binder.spelling]
          core := { state.core with nextOccurrence := occurrence + 1 } }
        let (value, state) ← elaborateSurface document lexicalHeads freeNames rrLink
          names environment (some binder.type) value state
        let (body, state) ← elaborateSurface document lexicalHeads freeNames rrLink
          (binder.spelling :: names) (environment.extend binder.type) expected body state
        let expansion := expandLet binder.type value body
        match expansion.validate definition with
        | .error detail => coreElaborationFailure "template-certificate" detail
        | .ok _ =>
            let payload := expansion.payload
            pure (payload.term, state.addExpansion definition payload rrLink)
    | .form _ (.defined .let) _ =>
        coreElaborationFailure "definition-arity" "Let expects binder, value, and body"
    | .form _ (.defined head) arguments =>
        elaborateDefinedForm document lexicalHeads freeNames rrLink names environment
          expected (rawTermName head.name) arguments state
    | .form _ (.primitive .lambda) [binders, body] =>
        let decodedBinders ← mapDecodeError (decodeBinderGroup binders)
        let state := { state with
          decode := state.decode.recordSource document
            (decodedBinders.map (·.spelling)) }
        elaborateSurfaceLambdas document lexicalHeads freeNames rrLink names environment
          decodedBinders body state
    | .form _ (.primitive .bind) arguments =>
        let (clauses, body) ← mapDecodeError (decodeBindClauses arguments)
        elaborateSurfaceBinds document lexicalHeads freeNames rrLink names environment
          clauses body state
    | .form _ (.primitive .context) arguments =>
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        let dependencies := arguments.dependencies
        let (site, decode) := freshSite document "written-context" .context rrLink
          dependencies state.decode
        pure (.context site arguments, { state with decode })
    | .form _ (.primitive .vague) [constraint] =>
        let (constraint, state) ← elaborateSurface document lexicalHeads freeNames
          rrLink names environment none constraint state
        let (site, decode) := freshSite document "written-vague" .vague rrLink
          constraint.dependencies state.decode
        pure (.vague site constraint, { state with decode })
    | .form _ (.primitive .vague) _ =>
        coreElaborationFailure "surface-decode" "Vague expects one constraint"
    | .form _ (.primitive .application) (function :: arguments) =>
        let (function, state) ← elaborateSurface document lexicalHeads freeNames
          rrLink names environment none function state
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        let term := Term.apply function arguments
        let (term, core) ← elaborateCore document environment expected term state.core
        pure (term, { state with core })
    | .form _ (.primitive .lexicalPredication)
        (.atom (.symbol predicate) :: arguments) =>
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        pure (.lexical predicate arguments, state)
    | .form _ (.primitive operator) arguments =>
        let some firstOrder := FirstOrderPrimitive.ofName operator.name
          | coreElaborationFailure "surface-decode"
              s!"structural primitive {operator.name} has invalid selected shape"
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        let (term, core) ← elaborateCore document environment expected
          (.primitive firstOrder arguments) state.core
        pure (term, { state with core })
    | .form _ (.lexical predicate) arguments =>
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        pure (.lexical predicate arguments, state)
    | .form _ (.variable name) arguments =>
        let (function, state) ← elaborateSurface document lexicalHeads freeNames rrLink
          names environment none (.atom (.symbol name)) state
        let (arguments, state) ← elaborateSurfaceList document lexicalHeads freeNames
          rrLink names environment arguments state
        let term := Term.apply function arguments
        let (term, core) ← elaborateCore document environment expected term state.core
        pure (term, { state with core })
    | .form _ (.gap head) _ =>
        coreElaborationFailure "surface-gap" s!"gap/prose-only head {head.name}"
    | .form _ (.tool head) _ =>
        coreElaborationFailure "surface-tool" s!"tool-only head {head.name}"
    | .form _ (.unknown head) _ =>
        coreElaborationFailure "surface-unknown" s!"unknown head {head}"

  partial def elaborateDefinedForm (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (names : List String) (environment : Environment names.length)
      (_expected : Option Ty) (spelling : String) (arguments : List SurfaceTerm)
      (state : SurfaceElaborationState) :
      Except TypingError (Term names.length × SurfaceElaborationState) := do
    let some definition := selectedDefinitionForSpelling spelling
      | coreElaborationFailure "definition-dispatch"
          s!"selected head {spelling} has no definition ID"
    let occurrence := state.core.nextOccurrence
    let state := { state with core := {
      state.core with nextOccurrence := occurrence + 1 } }
    let key : ExpansionKey := { document, occurrence, definition }
    let (terms, state) ← elaborateSurfaceVector document lexicalHeads freeNames rrLink
      names environment arguments state
    let payload ← dispatchDefinition environment key definition terms
    pure (payload.term, state.addExpansion definition payload rrLink)

  partial def elaborateSurfaceVector (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (names : List String) (environment : Environment names.length) :
      List SurfaceTerm → SurfaceElaborationState →
      Except TypingError (List (Term names.length) × SurfaceElaborationState)
    | [], state => pure ([], state)
    | head :: tail, state => do
        let (head, state) ← elaborateSurface document lexicalHeads freeNames rrLink
          names environment none head state
        let (tail, state) ← elaborateSurfaceVector document lexicalHeads freeNames rrLink
          names environment tail state
        pure (head :: tail, state)

  partial def elaborateSurfaceList (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (names : List String) (environment : Environment names.length) :
      List SurfaceTerm → SurfaceElaborationState →
      Except TypingError (TermList names.length × SurfaceElaborationState)
    | [], state => pure (.nil, state)
    | head :: tail, state => do
        let positional := do
          let (head, state) ← elaborateSurface document lexicalHeads freeNames rrLink
            names environment none head state
          let (tail, state) ← elaborateSurfaceList document lexicalHeads freeNames rrLink
            names environment tail state
          pure (.positional head tail, state)
        match head, tail with
        | .atom (.symbol label), [] =>
            if label.startsWith ":" then
              coreElaborationFailure "surface-label" s!"label {label} is missing a value"
            else positional
        | .atom (.symbol label), value :: rest =>
            if label.startsWith ":" then
              let (value, state) ← elaborateSurface document lexicalHeads freeNames rrLink
                names environment none value state
              let (rest, state) ← elaborateSurfaceList document lexicalHeads freeNames
                rrLink names environment rest state
              pure (.labelled label value rest, state)
            else positional
        | _, _ => positional

  partial def elaborateSurfaceLambdas (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (names : List String) (environment : Environment names.length) :
      List Binder → SurfaceTerm → SurfaceElaborationState →
      Except TypingError (Term names.length × SurfaceElaborationState)
    | [], body, state =>
        elaborateSurface document lexicalHeads freeNames rrLink names environment
          none body state
    | binder :: rest, body, state => do
        let (body, state) ← elaborateSurfaceLambdas document lexicalHeads freeNames
          rrLink (binder.spelling :: names) (environment.extend binder.type)
          rest body state
        pure (.lambda binder.type body, state)

  partial def elaborateSurfaceBinds (document : String)
      (lexicalHeads freeNames : List String) (rrLink : Option String)
      (names : List String) (environment : Environment names.length) :
      List (Binder × SurfaceTerm) → SurfaceTerm → SurfaceElaborationState →
      Except TypingError (Term names.length × SurfaceElaborationState)
    | [], body, state =>
        elaborateSurface document lexicalHeads freeNames rrLink names environment
          none body state
    | (binder, computation) :: rest, body, state => do
        let state := { state with
          decode := state.decode.recordSource document [binder.spelling] }
        let (computation, state) ← elaborateSurface document lexicalHeads freeNames
          rrLink names environment (some (Ty.refComp binder.type)) computation state
        let (body, state) ← elaborateSurfaceBinds document lexicalHeads freeNames rrLink
          (binder.spelling :: names) (environment.extend binder.type) rest body state
        pure (.bind binder.type computation body, state)
end

def caseRRDeclarations (metadata : List SiteEntry) : List SiteEntry :=
  metadata.filter fun entry => entry.rrLink.isSome

def caseRRDeclarationAgreement {scope : Nat} (term : Term scope)
    (metadata : List SiteEntry) : Bool :=
  (caseRRDeclarations metadata).all fun entry =>
    term.siteOccurrences.any fun occurrence =>
      occurrence.use.identity == entry.identity &&
        occurrence.use.role == entry.role && occurrence.support == entry.dependencies

structure CaseOutcome where
  id : String
  originalTag : String
  disposition : CaseDisposition
  decidingRule : String
  type : Option Ty := none
  effects : List Effect := []
  expandedDefinitions : List M2DefinitionId := []
  clauses : List M2ClauseId := []
  term : Option (Term 0) := none
  error : Option TypingError := none
  rrDeclarations : Nat := 0
  rrAgreement : Bool := true
  inputTypingAvailable : Bool := false
  inputTraceSupported : Bool := false
  outputTypingAvailable : Bool := false
  outputTraceSupported : Bool := false
  excludedTraceRules : List M2TypingRuleId := []
  deriving Repr

def typingTraceSupported (result : TypingResult) : Bool :=
  result.trace.all typingRuleImplemented

def classifyUnselected (record : CorpusCase) (tag : String)
    (unselected : List M2DefinitionDispositionRecord) : Option CaseOutcome :=
  if let some blocked := unselected.find? fun item => item.status == "blocked" then
    some {
      id := record.id
      originalTag := tag
      disposition := .blocked
      decidingRule := blocked.id ++ ":" ++ blocked.issue.getD "blocked"
    }
  else if let some executable := unselected.find? fun item =>
      item.status == "executable" then
    some {
      id := record.id
      originalTag := tag
      disposition := .pendingMilestone3
      decidingRule := executable.id ++ ":" ++ executable.reason
    }
  else if let some other := unselected.head? then
    some {
      id := record.id
      originalTag := tag
      disposition := .outOfSlice
      decidingRule := other.id ++ ":" ++ other.status
    }
  else none

def classifyDecodedCase (lexicalHeads : List String) (manifestCase : S1CaseRecord)
    (record : CorpusCase) : Except String CaseOutcome := do
  let surface := SurfaceTerm.ofSExprWithLexicon lexicalHeads record.term
  if !manifestCase.offending_heads.isEmpty then
    return {
      id := record.id
      originalTag := manifestCase.tag
      disposition := .outOfSlice
      decidingRule := "M1 structural/offending-head provenance" }
  let unselected := unselectedSurfaceDefinitions lexicalHeads surface
  if let some outcome := classifyUnselected record manifestCase.tag unselected then
    return outcome
  let freeNames := freeNamesFromEnvironment record.environment
  let environment ← environmentForCorpus record.environment
  let rrLink := rrLinkFromProvenance record.provenance
  match elaborateSurface record.id lexicalHeads freeNames rrLink [] environment none
      surface {} with
  | .error error =>
      return {
        id := record.id
        originalTag := manifestCase.tag
        disposition := if ["row-input-unavailable", "close-row",
            "lexical-signature", "expected-type"].contains error.code then
            .inputUnavailable
          else if error.code == "definition-domain" then .blocked
          else .typedRejection
        decidingRule := error.code
        error := some error }
  | .ok (term, state) =>
      let rebuilt : Interchange.Bundle 0 := {
        version := 1
        term
        sites := state.decode.sites.filter fun entry =>
          term.siteIds.contains entry.identity
        sourceMap := state.decode.sourceNotes.map Interchange.SourceNote.ofDecodeNote }
      let _ ← rebuilt.checked
      let rrCount := caseRRDeclarations rebuilt.sites |>.length
      let rrAgrees := caseRRDeclarationAgreement term rebuilt.sites
      match synth environment term with
      | .error error =>
          return {
            id := record.id
            originalTag := manifestCase.tag
            disposition := .typedRejection
            decidingRule := error.code
            expandedDefinitions := state.core.definitions
            clauses := state.core.clauses
            term := some term
            error := some error
            rrDeclarations := rrCount
            rrAgreement := rrAgrees }
      | .ok typed =>
          let traceSupported := typingTraceSupported typed
          let inputAvailable := state.core.definitions.isEmpty
          return {
            id := record.id
            originalTag := manifestCase.tag
            disposition := if state.core.definitions.isEmpty then
              .typedUnchanged else .typeDirectedExpansion
            decidingRule := if state.core.definitions.isEmpty then
              "bidirectional typing" else "generated definition-domain overload"
            type := some typed.type
            effects := typed.effects
            expandedDefinitions := state.core.definitions
            clauses := state.core.clauses
            term := some term
            rrDeclarations := rrCount
            rrAgreement := rrAgrees
            inputTypingAvailable := inputAvailable
            inputTraceSupported := inputAvailable && traceSupported
            outputTypingAvailable := true
            outputTraceSupported := traceSupported
            excludedTraceRules := (typed.trace.filter fun rule =>
              !typingRuleImplemented rule).eraseDups }

structure CaseRun where
  outcomes : List CaseOutcome
  typedUnchanged : Nat
  typeDirectedExpansion : Nat
  typedRejection : Nat
  pendingMilestone3 : Nat
  blocked : Nat
  inputUnavailable : Nat
  outOfSlice : Nat
  rrDeclarations : Nat
  rrMismatchCases : Nat
  inputTypingsAvailable : Nat
  inputTypingsSupported : Nat
  outputTypingsAvailable : Nat
  outputTypingsSupported : Nat
  excludedTraceRules : List M2TypingRuleId
  deriving Repr

def CaseRun.ofOutcomes (outcomes : List CaseOutcome) : CaseRun := {
  outcomes
  typedUnchanged := outcomes.countP fun outcome =>
    outcome.disposition == .typedUnchanged
  typeDirectedExpansion := outcomes.countP fun outcome =>
    outcome.disposition == .typeDirectedExpansion
  typedRejection := outcomes.countP fun outcome =>
    outcome.disposition == .typedRejection
  pendingMilestone3 := outcomes.countP fun outcome =>
    outcome.disposition == .pendingMilestone3
  blocked := outcomes.countP fun outcome => outcome.disposition == .blocked
  inputUnavailable := outcomes.countP fun outcome =>
    outcome.disposition == .inputUnavailable
  outOfSlice := outcomes.countP fun outcome => outcome.disposition == .outOfSlice
  rrDeclarations := outcomes.foldl (fun count outcome =>
    count + outcome.rrDeclarations) 0
  rrMismatchCases := outcomes.countP fun outcome =>
    outcome.rrDeclarations > 0 && !outcome.rrAgreement
  inputTypingsAvailable := outcomes.countP (·.inputTypingAvailable)
  inputTypingsSupported := outcomes.countP (·.inputTraceSupported)
  outputTypingsAvailable := outcomes.countP (·.outputTypingAvailable)
  outputTypingsSupported := outcomes.countP (·.outputTraceSupported)
  excludedTraceRules := outcomes.flatMap (·.excludedTraceRules) |>.eraseDups }

def runM2Cases (root : String) : IO CaseRun := do
  let manifestSource ← IO.FS.readFile (root ++ "/pilot/shared/M1_S1_MANIFEST.json")
  let manifest : S1Manifest ←
    IO.ofExcept (Json.parse manifestSource >>= fromJson?)
  let corpusDigest ← sha256File root manifest.sources.port_corpus
  if corpusDigest != manifest.sources.port_corpus_sha256 then
    throw <| IO.userError "M2 port corpus source digest mismatch"
  let fixtureDigest ← sha256File root manifest.sources.fixtures
  if fixtureDigest != manifest.sources.fixtures_sha256 then
    throw <| IO.userError "M2 lexical fixture source digest mismatch"
  let corpusSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.port_corpus)
  let corpus ← IO.ofExcept (SExpr.parse corpusSource >>= decodeCorpus)
  let fixtureSource ← IO.FS.readFile (root ++ "/" ++ manifest.sources.fixtures)
  let lexicalHeads ← IO.ofExcept
    (SExpr.parse fixtureSource >>= decodeLexicalHeads)
  let outcomes ← corpus.mapM fun record => do
    let some manifestCase := findManifestCase manifest record.id
      | throw <| IO.userError s!"M2 case absent from S1 manifest: {record.id}"
    IO.ofExcept <| classifyDecodedCase lexicalHeads manifestCase record
  if outcomes.length != manifest.counts.total_cases then
    throw <| IO.userError "M2 did not classify every S1 case"
  let assertFrozen := fun (id : String) (disposition : CaseDisposition)
      (rule : String) (definitions : List M2DefinitionId) => do
    let some outcome := outcomes.find? fun candidate => candidate.id == id
      | throw <| IO.userError s!"frozen Refer case is absent: {id}"
    if outcome.disposition != disposition || outcome.decidingRule != rule ||
        outcome.expandedDefinitions != definitions then
      throw <| IO.userError <| s!"frozen Refer case drifted: {id} " ++
        s!"got {repr outcome.disposition}/{outcome.decidingRule}/" ++
        s!"{repr outcome.expandedDefinitions}"
  assertFrozen "58c6ffc749c2646868481de082505374ffabf2df"
    .typedRejection "set-property" [.d53ReferMemberLift]
  assertFrozen "58da5cf5634a11f88da8aa2a3f88db4707056141"
    .typeDirectedExpansion "generated definition-domain overload"
    [.d53ReferMemberLift]
  assertFrozen "2b3c9244ebe77552801d7ae17388f626b3dd74c3"
    .typedRejection "refer-member-purity" []
  assertFrozen "61a28f59bc37ccdacbcb320cc8b1704889eb23c8"
    .typedUnchanged "bidirectional typing" []
  pure <| CaseRun.ofOutcomes outcomes

end M2
end SmusniPilot
