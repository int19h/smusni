import SmusniPilot.M2Inventory
import SmusniPilot.BundleBinding

namespace SmusniPilot
namespace M2

namespace Ty

def named0 (name : TypeName) : Ty := .named name []
def entity : Ty := named0 .sortEntity
def eventuality : Ty := named0 .sortEventuality
def locution : Ty := named0 .sortLocution
def amount : Ty := named0 .sortAmount
def scale : Ty := named0 .sortScale
def text : Ty := named0 .sortText
def proposition : Ty := named0 .sortProposition
def utteranceToken : Ty := named0 .sortUtteranceToken
def time : Ty := named0 .sortTime
def epistemology : Ty := named0 .sortEpistemology
def truthValue : Ty := named0 .sortTruthValue
def abstractNature : Ty := named0 .sortAbstractNature
def number : Ty := named0 .sortNumber
def natural : Ty := named0 .sortNatural
def cardinal : Ty := named0 .sortCardinal
def thresholdKind : Ty := named0 .typeThresholdKind
def content : Ty := named0 .typeContent
def clauseContent : Ty := named0 .typeClauseContent
def discourse : Ty := named0 .typeDiscourse
def occurrenceRole : Ty := named0 .typeOccurrenceRole
def genericMode : Ty := named0 .typeGenericMode
def intensity : Ty := named0 .typeIntensity
def defectKind : Ty := named0 .typeDefectKind

def referents (inner : Ty) : Ty := .named .typeFormReferents [inner]
def group (inner : Ty) : Ty := .named .typeFormGroup [inner]
def list (inner : Ty) : Ty := .named .typeFormList [inner]
def set (inner : Ty) : Ty := .named .typeFormSet [inner]
def region (inner : Ty) : Ty := .named .typeFormRegion [inner]
def decompositionBasis (whole component : Ty) : Ty :=
  .named .typeFormDecompositionBasis [whole, component]
def refComp (inner : Ty) : Ty := .named .typeFormRefComp [inner]
def perfComp (inner : Ty) : Ty := .named .typeFormPerfComp [inner]
def act (force : Ty) : Ty := .named .typeFormAct [force]
def actOccurrence (force : Ty) : Ty := .named .typeFormActOccurrence [force]
def query (answer : Ty) : Ty := .named .typeFormQuery [answer]
def sign (kind : String) : Ty := .named .typeFormSign [.index kind]
def predTerm (row : Ty) : Ty := .named .typeFormPredTerm [row]
def record (row : Ty) : Ty := .named .typeFormRecord [row]
def rowOf (head : String) : Ty := .named .typeFormRowOf [.variable head]
def rowMinus (row label : Ty) : Ty := .named .typeFormRowMinus [row, label]
def arityRow (arity : Nat) : Ty :=
  .named .typeFormRow (List.replicate arity (.index "ordinary"))
def residualRow (ordinary : Nat) (event : Bool) : Ty :=
  .named .typeFormRow <|
    List.replicate ordinary (.index "ordinary") ++
      if event then [
        .named .typeFormLabel [.index "Eventuality", referents eventuality]]
      else []

def assertion : Ty := .index "Assertion"
def expressive : Ty := .index "Expressive"
def question : Ty := .index "Question"

def individualSortName : TypeName → Bool
  | .sortEntity | .sortEventuality | .sortAchievement | .sortProcess
  | .sortActivity | .sortState | .sortExperience | .sortLocution
  | .sortLocation | .sortTime | .sortAmount | .sortScale
  | .sortEpistemology | .sortTruthValue | .sortConcept
  | .sortAbstractNature | .sortProposition | .sortQuestion
  | .sortNumber | .sortNatural | .sortCardinal | .sortText
  | .sortUtteranceToken | .sortGround => true
  | _ => false

def directSuperSort : TypeName → Option TypeName
  | .sortEventuality | .sortLocation | .sortTime | .sortAmount | .sortScale
  | .sortEpistemology | .sortTruthValue | .sortConcept
  | .sortAbstractNature | .sortProposition | .sortQuestion
  | .sortNumber | .sortText | .sortUtteranceToken | .sortGround =>
      some .sortEntity
  | .sortAchievement | .sortProcess | .sortActivity | .sortState
  | .sortExperience | .sortLocution => some .sortEventuality
  | .sortNatural => some .sortNumber
  | .sortCardinal => some .sortNatural
  | _ => none

partial def sortSubtype (actual expected : TypeName) : Bool :=
  if actual == expected then true
  else match directSuperSort actual with
    | some parent => sortSubtype parent expected
    | none => false

def pureFn (parameters : List Ty) (result : Ty) : Ty :=
  .function false parameters result
def effectfulFn (parameters : List Ty) (result : Ty) : Ty :=
  .function true parameters result

def isNamed (type : Ty) (name : TypeName) (arity : Nat) : Bool :=
  match type with
  | .named actual arguments => actual == name && arguments.length == arity
  | _ => false

def asUnary (type : Ty) (name : TypeName) : Option Ty :=
  match type with
  | .named actual [inner] => if actual == name then some inner else none
  | _ => none

def asBinary (type : Ty) (name : TypeName) : Option (Ty × Ty) :=
  match type with
  | .named actual [first, second] =>
      if actual == name then some (first, second) else none
  | _ => none

def asFunction : Ty → Option (Bool × List Ty × Ty)
  | .function effectful parameters result => some (effectful, parameters, result)
  | _ => none

partial def compatible (actual expected : Ty) : Bool :=
  if actual == expected then true
  else if actual == clauseContent then
    expected == pureFn [referents eventuality] content ||
      expected == effectfulFn [referents eventuality] content
  else if expected == clauseContent then
    actual == pureFn [referents eventuality] content ||
      actual == effectfulFn [referents eventuality] content
  else match actual, expected with
    | .named actualName [], .named expectedName [] =>
        individualSortName actualName && individualSortName expectedName &&
          sortSubtype actualName expectedName
    | .named .typeFormReferents [actualInner],
        .named .typeFormReferents [expectedInner] =>
        compatible actualInner expectedInner
    | _, .named .typeFormReferents [expectedInner] =>
        compatible actual expectedInner
    | _, _ =>
      match asFunction actual, asFunction expected with
      | some (actualEffectful, actualParameters, actualResult),
          some (expectedEffectful, expectedParameters, expectedResult) =>
          (!actualEffectful || expectedEffectful) &&
            actualParameters.length == expectedParameters.length &&
            (expectedParameters.zip actualParameters).all
              (fun pair => compatible pair.1 pair.2) &&
            compatible actualResult expectedResult
      | _, _ => false

def equalityType : Ty → Bool
  | .named name arguments =>
      (individualSortName name || name == .typeThresholdKind) &&
        arguments.isEmpty ||
      [ .typeFormSet, .typeFormGroup, .typeFormList, .typeFormSign ].contains name &&
        arguments.length == 1
  | _ => false

def firstOrder : Ty → Bool
  | .named name arguments =>
      individualSortName name && arguments.isEmpty ||
      [ .typeFormSet, .typeFormGroup, .typeFormList, .typeFormSign ].contains name &&
        arguments.length == 1
  | _ => false

def quantifierDomain (type : Ty) : Bool :=
  firstOrder type || match asUnary type .typeFormReferents with
    | some inner => firstOrder inner
    | none => false

def referenceInner (type : Ty) : Option Ty :=
  (asUnary type .typeFormReferents).orElse fun _ =>
    if firstOrder type then some type else none

def referenceCompatible (first second : Ty) : Bool :=
  match referenceInner first, referenceInner second with
  | some firstInner, some secondInner =>
      compatible firstInner secondInner || compatible secondInner firstInner
  | _, _ => false

def computationCategory (type : Ty) : Bool :=
  type == content || type == clauseContent || type == discourse ||
    (asUnary type .typeFormRefComp).isSome ||
    (asUnary type .typeFormPerfComp).isSome

def numberJoin (first second : Ty) : Option Ty :=
  if first == natural && second == natural then some natural
  else if [natural, cardinal].contains first &&
      [natural, cardinal].contains second then some cardinal
  else if compatible first number && compatible second number then some number
  else none

end Ty

inductive Effect where
  | context
  | refer
  | projective
  | effectfulCall
  | performance
  deriving Repr, DecidableEq, BEq

inductive Obligation where
  | finiteSetCardinalityDefined
  | presuppose (condition : String) (category : Ty)
  | whenPositive (count : String) (inner : Obligation)
  | definedness (name : String) (category : Ty)
  deriving Repr, BEq, Inhabited

structure TypingResult where
  type : Ty
  effects : List Effect := []
  obligations : List Obligation := []
  trace : List M2TypingRuleId := []
  deriving Repr, BEq, Inhabited

def canonicalEffects (values : List Effect) : List Effect :=
  values.eraseDups

def TypingResult.withRule (result : TypingResult)
    (rule : M2TypingRuleId) : TypingResult :=
  { result with trace := result.trace ++ [rule] }

def mergeResults (type : Ty) (results : List TypingResult)
    (effects : List Effect := []) (obligations : List Obligation := [])
    (rule : M2TypingRuleId) : TypingResult := {
  type
  effects := canonicalEffects (results.flatMap (·.effects) ++ effects)
  obligations := results.flatMap (·.obligations) ++ obligations
  trace := results.flatMap (·.trace) ++ [rule] }

structure Environment (scope : Nat) where
  bound : Fin scope → Ty
  free : List (FreeId × Ty) := []
  lexical : List (String × Ty) := []

def Environment.empty : Environment 0 := {
  bound := Fin.elim0
}

def Environment.extend {scope : Nat} (environment : Environment scope)
    (type : Ty) : Environment (scope + 1) := {
  bound := Fin.cases type environment.bound
  free := environment.free
  lexical := environment.lexical }

def Environment.lookupFree {scope : Nat} (environment : Environment scope)
    (identity : FreeId) : Option Ty :=
  (environment.free.find? fun entry => entry.1 == identity).map (·.2)

def Environment.lookupLexical {scope : Nat} (environment : Environment scope)
    (name : String) : Option Ty :=
  (environment.lexical.find? fun entry => entry.1 == name).map (·.2)

def lookupLexicalRow (name : String) : Option M2LexicalRowRecord :=
  m2LexicalRowRecords.find? fun row => row.head == name

structure TypingError where
  code : String
  detail : String
  deriving Repr, DecidableEq, BEq, Inhabited

def failure {α : Type} (code detail : String) : Except TypingError α :=
  .error { code, detail }

def positionalTerms {scope : Nat} :
    TermList scope → Except TypingError (List (Term scope))
  | .nil => pure []
  | .positional head tail => return head :: (← positionalTerms tail)
  | .labelled label _ _ =>
      failure "labelled-fill" s!"labelled fill {label} requires row-directed typing"

def labelledTerms {scope : Nat} :
    TermList scope → Except TypingError (List (Option String × Term scope))
  | .nil => pure []
  | .positional head tail => return (none, head) :: (← labelledTerms tail)
  | .labelled label head tail => return (some label, head) :: (← labelledTerms tail)

def positionalList {scope : Nat} : List (Term scope) → TermList scope
  | [] => .nil
  | head :: tail => .positional head (positionalList tail)

def lexicalRowType (row : M2LexicalRowRecord) : Ty :=
  Ty.predTerm (Ty.rowOf row.head)

def rowShape : Ty → Option (Nat × Bool)
  | .named .typeFormRow fields =>
      let ordinary := fields.countP fun
        | .index _ => true
        | .named .typeFormLabel [.index label, _] => label.toNat?.isSome
        | _ => false
      let event := fields.any fun
        | .named .typeFormLabel [.index "Eventuality", _] => true
        | .named .sortEventuality _ => true
        | _ => false
      some (ordinary, event)
  | .named .typeFormRowOf [.variable head] => do
      let row ← lookupLexicalRow head
      some (row.ordinaryArity, row.eventMode == .directEvent)
  | .named .typeFormRowMinus [base, .index label] => do
      let (ordinary, event) ← rowShape base
      if label == "Eventuality" then
        if event then some (ordinary, false) else none
      else do
        let value ← label.toNat?
        if value > 0 && value <= ordinary then some (ordinary - 1, event)
        else none
  | _ => none

def predTermShape : Ty → Option (Nat × Bool)
  | .named .typeFormPredTerm [row] => rowShape row
  | _ => none

partial def isValue {scope : Nat} : Term scope → Bool
  | .bound _ | .free _ | .natural _ | .string _ | .index _ | .lambda _ _ => true
  | .primitive .list arguments =>
      match positionalTerms arguments with
      | .ok terms => terms.all isValue
      | .error _ => false
  | .primitive operator .nil =>
      [ .speaker, .audience, .tooManyK ].contains operator
  | _ => false

def isPure (result : TypingResult) : Bool := result.effects.isEmpty

def expectArity {scope : Nat} (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (arity : Nat) :
    Except TypingError (List (Term scope)) := do
  let terms ← positionalTerms arguments
  if terms.length == arity then pure terms
  else failure "arity" s!"{operator.name} expects {arity} arguments, got {terms.length}"

def oneArgumentFunction (result : TypingResult) : Option (Bool × Ty) :=
  match result.type with
  | .function effectful [parameter] output =>
      if output == Ty.content then some (effectful, parameter) else none
  | _ => none

def provablyPositive {scope : Nat} : Term scope → Bool
  | .natural value => value > 0
  | .primitive .add arguments =>
      match positionalTerms arguments with
      | .ok [.natural 1, _] | .ok [_, .natural 1] => true
      | _ => false
  | _ => false

mutual
  partial def synth {scope : Nat} (environment : Environment scope) :
      Term scope → Except TypingError TypingResult
    | .bound index =>
        pure { type := environment.bound index, trace := [.a0TVariable, .a0Synth] }
    | .free identity =>
        match environment.lookupFree identity with
        | some type => pure { type, trace := [.a0TVariable, .a0Synth] }
        | none => failure "free-variable" s!"undeclared free identity {repr identity}"
    | .natural _ =>
        pure { type := Ty.natural, trace := [.a0TNatural, .a0Synth] }
    | .string _ =>
        pure { type := Ty.text, trace := [.m2TString, .a0Synth] }
    | .index value => failure "unsupported-index" s!"A0 has no index rule for {value}"
    | .lambda binderType body => do
        let bodyResult ← synth (environment.extend binderType) body
        let effectful := !bodyResult.effects.isEmpty
        let rule := if effectful then .a0TLambdaEffectful else .a0TLambdaPure
        pure {
          type := .function effectful [binderType] bodyResult.type
          obligations := bodyResult.obligations
          trace := bodyResult.trace ++ [rule, .a0Synth] }
    | .bind binderType computation body => do
        let bodyResult ← synth (environment.extend binderType) body
        match check environment computation (Ty.refComp binderType) with
        | .ok referenceResult =>
            pure <| mergeResults bodyResult.type [referenceResult, bodyResult]
              [] [] .a0TBindReference |>.withRule .a0Synth
        | .error _ => do
            let performanceResult ←
              check environment computation (Ty.perfComp binderType)
            let resultType :=
              match bodyResult.type with
              | .named .typeFormAct _ => Ty.discourse
              | type => if type == Ty.discourse then Ty.discourse else type
            let rule :=
              match bodyResult.type with
              | .named .typeFormAct _ => .a0TBindPerformanceAct
              | .named .typeFormPerfComp _ => .a0TBindPerformanceComp
              | _ => .a0TBindPerformanceDiscourse
            pure <| mergeResults resultType [performanceResult, bodyResult]
              (if resultType == Ty.discourse then [.performance] else []) [] rule
              |>.withRule .a0Synth
    | .apply function arguments => do
        let functionResult ← synth environment function
        applyFunction environment functionResult arguments
    | .lexical predicate arguments => synthLexical environment predicate arguments
    | .context _ _ => failure "expected-type" "Context requires an expected RefComp type"
    | .vague _ _ => failure "expected-type" "Vague requires an expected RefComp type"
    | .primitive operator arguments => synthPrimitive environment operator arguments

  partial def check {scope : Nat} (environment : Environment scope)
      (term : Term scope) (expected : Ty) : Except TypingError TypingResult :=
    match term, Ty.asUnary expected .typeFormRefComp with
    | .context _ arguments, some _ => do
        let operands ← positionalTerms arguments
        let results ← operands.mapM fun operand => do
          if !isValue operand then
            failure "dependency-operand" "Context dependency operand is not a value"
          else pure ()
          synth environment operand
        pure <| mergeResults expected results [.context] [] .a0TContext
          |>.withRule .a0Check
    | .vague _ constraint, some inner => do
        let property ← synth environment constraint
        if property.type != Ty.pureFn [inner] Ty.content || !isPure property then
          failure "vague-constraint" "Vague constraint must be a pure unary Content property"
        else pure ()
        pure <| mergeResults expected [property] [.context] [] .a0TVague
          |>.withRule .a0Check
    | .primitive .refer arguments, some reference =>
        match Ty.asUnary reference .typeFormReferents with
        | none => failure "refer-type" "Refer expects RefComp<Referents<T>>"
        | some inner => do
            let [property] ← expectArity .refer arguments 1
              | failure "arity" "Refer expects one property"
            let propertyResult ← synth environment property
            match propertyResult.type with
            | .function effectful [parameter] result =>
                if result != Ty.content then
                  failure "refer-property" "Refer property must return Content"
                else pure ()
                let rule ←
                  if parameter == Ty.referents inner then
                    pure M2TypingRuleId.a0TReferReference
                  else if !effectful && Ty.compatible parameter inner then
                    pure M2TypingRuleId.a0TReferMember
                  else failure "refer-property" "Refer property has the wrong domain/purity"
                pure <| mergeResults expected [propertyResult]
                  ((if effectful then [.effectfulCall] else []) ++ [.refer]) [] rule
                  |>.withRule .a0Check
            | _ => failure "refer-property" "Refer property is not a function"
    | .primitive .presuppose arguments, some _ =>
        checkPresupposeReference environment arguments expected
    | .primitive .local arguments, some _ => do
        let [body] ← expectArity .local arguments 1
          | failure "arity" "Local expects one reference computation"
        let result ← check environment body expected
        pure <| mergeResults expected [result] [] [] .m2TLocal
          |>.withRule .a0Check
    | .primitive operator arguments, some reference =>
        checkReferencePrimitive environment operator arguments reference expected
    | _, _ =>
        match expected with
        | .named .typeFormList [itemType] =>
            match term with
            | .primitive .list arguments => do
                let terms ← positionalTerms arguments
                let results ← terms.mapM fun item => check environment item itemType
                pure <| mergeResults expected results [] [] .a0TListCheck
                  |>.withRule .a0Check
            | _ => checkSynth
        | _ => checkSynth
    where
      checkSynth : Except TypingError TypingResult :=
        match synth environment term with
        | .error error => .error error
        | .ok actual =>
            if Ty.compatible actual.type expected then
              .ok { actual with
                trace := actual.trace ++ [.a0TCheckSynth, .a0Check] }
            else failure "type-mismatch"
              (s!"expected {repr expected}, synthesized {repr actual.type}")

  partial def applyFunction {scope : Nat} (environment : Environment scope)
      (functionResult : TypingResult) (arguments : TermList scope) :
      Except TypingError TypingResult := do
    let items ← labelledTerms arguments
    if (predTermShape functionResult.type).isNone &&
        items.any fun item => item.1.isSome then
      failure "labelled-fill" "labelled fills require a PredTerm row"
    else pure ()
    let terms := items.map (·.2)
    match functionResult.type with
    | .function effectful parameters result =>
        if parameters.isEmpty && !terms.isEmpty then
          failure "application-arity" "zero-parameter function cannot consume arguments"
        else pure ()
        let consumed := min parameters.length terms.length
        let argumentResults ← ((terms.take consumed).zip
          (parameters.take consumed)).mapM fun pair => check environment pair.1 pair.2
        let rule := if effectful then .a0TApplyEffectful else .a0TApplyPure
        if terms.length < parameters.length then
          let remaining := parameters.drop consumed
          pure <| mergeResults (.function effectful remaining result)
            (functionResult :: argumentResults)
            (if effectful then [.effectfulCall] else []) [] rule |>.withRule .a0Synth
        else
          let applied := mergeResults result (functionResult :: argumentResults)
            (if effectful then [.effectfulCall] else []) [] rule |>.withRule .a0Synth
          let remaining := terms.drop consumed
          if remaining.isEmpty then pure applied
          else applyFunction environment applied (positionalList remaining)
    | type =>
        if type == Ty.clauseContent then
          let [argument] := terms
            | failure "application-arity" "ClauseContent expects one event reference"
          let result ← check environment argument (Ty.referents Ty.eventuality)
          pure <| mergeResults Ty.content [functionResult, result] [] []
            .a0TApplyClauseContent |>.withRule .a0Synth
        else match predTermShape type with
          | some (ordinary, eventRequired) => do
              let items ← labelledTerms arguments
              let ordinaryFilled := items.countP fun item =>
                item.1 != some ":Eventuality"
              let eventFilled := items.any fun item =>
                item.1 == some ":Eventuality"
              if ordinaryFilled > ordinary || (eventFilled && !eventRequired) then
                failure "predterm-row" "application fills outside the PredTerm row"
              else pure ()
              let results ← items.mapM fun item =>
                if item.1 == some ":Eventuality" then
                  check environment item.2 (Ty.referents Ty.eventuality)
                else synth environment item.2
              let output := if ordinaryFilled == ordinary &&
                  (!eventRequired || eventFilled) then Ty.content
                else Ty.predTerm <| Ty.residualRow
                  (ordinary - ordinaryFilled) (eventRequired && !eventFilled)
              pure <| mergeResults output (functionResult :: results) [] []
                .m2TPredTermApply |>.withRule .a0Synth
          | none => failure "application-type" s!"cannot apply {repr type}"

  partial def lexicalArgumentResults {scope : Nat}
      (environment : Environment scope) (row : M2LexicalRowRecord)
      (arguments : TermList scope) :
      Except TypingError (List TypingResult × Nat × Bool) := do
    let items ← labelledTerms arguments
    let labels := items.filterMap (·.1)
    if labels.length != labels.eraseDups.length then
      failure "lexical-label" s!"{row.head} repeats a labelled fill"
    else pure ()
    let mut ordinary := 0
    let mut eventFilled := false
    let mut results := []
    for (label, term) in items do
      match label with
      | none =>
          ordinary := ordinary + 1
          results := results ++ [← synth environment term]
      | some ":Eventuality" =>
          if row.eventMode != .directEvent then
            failure "lexical-label" s!"{row.head} has no Eventuality place"
          else pure ()
          eventFilled := true
          results := results ++ [← check environment term (Ty.referents Ty.eventuality)]
      | some label =>
          let raw := (label.drop 1).toString
          let some place := raw.toNat?
            | failure "lexical-label" s!"{row.head} has unknown label {label}"
          if place == 0 || place > row.ordinaryArity then
            failure "lexical-label" s!"{row.head} label {label} is outside its row"
          else pure ()
          ordinary := ordinary + 1
          results := results ++ [← synth environment term]
    if ordinary > row.ordinaryArity then
      failure "lexical-arity"
        s!"{row.head} has {row.ordinaryArity} ordinary places, got {ordinary}"
    pure (results, ordinary, eventFilled)

  partial def synthLexical {scope : Nat} (environment : Environment scope)
      (predicate : String) (arguments : TermList scope) :
      Except TypingError TypingResult :=
    match environment.lookupLexical predicate with
    | some type => applyFunction environment { type } arguments
    | none =>
        match lookupLexicalRow predicate with
        | none => failure "lexical-signature" s!"missing typed lexical row {predicate}"
        | some row => do
            let (results, ordinary, eventFilled) ←
              lexicalArgumentResults environment row arguments
            let complete := ordinary == row.ordinaryArity &&
              (row.eventMode == .holdingState || eventFilled)
            pure <| mergeResults
              (if complete then Ty.content else lexicalRowType row)
              results [] [] .m2TLexicalRow |>.withRule .a0Synth

  partial def synthPrimitive {scope : Nat} (environment : Environment scope)
      (operator : FirstOrderPrimitive) (arguments : TermList scope) :
      Except TypingError TypingResult :=
    match operator with
    | .speaker => constant .a0TSpeaker (Ty.referents Ty.entity)
    | .audience => constant .a0TAudience (Ty.referents Ty.entity)
    | .tooManyK => constant .a0TThresholdKind Ty.thresholdKind
    | .currentToken =>
        constant .m2TCoreConstant (Ty.referents Ty.utteranceToken)
    | .host | .attachedDisplay | .attachedAddress =>
        constant .m2TContextConstants Ty.occurrenceRole
    | .typical => constant .m2TContextConstants Ty.genericMode
    | .moderate | .intense => constant .m2TContextConstants Ty.intensity
    | .observation | .hearsay => constant .m2TContextConstants Ty.epistemology
    | .manyK => constant .m2TContextConstants Ty.thresholdKind
    | .now => constant .m2TContextConstants Ty.time
    | .miAOthers | .maAOthers | .doOOthers => do
        let result ← constant .m2TCoreConstant (Ty.referents Ty.entity)
        pure { result with
          effects := [.projective]
          obligations := [.definedness operator.name (Ty.referents Ty.entity)] }
    | .combine => do
        let [first, second] ← expectArity operator arguments 2
          | failure "arity" "Combine expects two referential values"
        let firstResult ← synth environment first
        let secondResult ← synth environment second
        let some firstInner := Ty.referenceInner firstResult.type
          | failure "combine-type" "Combine first operand is not referential"
        let some secondInner := Ty.referenceInner secondResult.type
          | failure "combine-type" "Combine second operand is not referential"
        let common ←
          if Ty.compatible firstInner secondInner then pure secondInner
          else if Ty.compatible secondInner firstInner then pure firstInner
          else failure "combine-type" "Combine operands have incompatible sorts"
        pure <| mergeResults (Ty.referents common) [firstResult, secondResult]
          [] [] .m2TCombine |>.withRule .a0Synth
    | .memberOf => do
        let [item, setTerm] ← expectArity operator arguments 2
          | failure "arity" "membership expects an item and a set"
        let itemResult ← synth environment item
        let setResult ← synth environment setTerm
        let some inner := Ty.asUnary setResult.type .typeFormSet
          | failure "membership-type" "membership second operand is not Set<T>"
        if !Ty.compatible itemResult.type inner then
          failure "membership-type" "membership item does not have the set element type"
        else pure ()
        pure <| mergeResults Ty.content [itemResult, setResult] [] []
          .m2TMemberOf |>.withRule .a0Synth
    | .assert => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" "Assert expects one Content"
        let result ← check environment content Ty.content
        let packaged : TypingResult := { type := Ty.act Ty.assertion }
        pure { packaged with
          obligations := result.obligations
          trace := result.trace ++ [.m2TForce, .a0Synth] }
    | .express => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" "Express expects one Content"
        let result ← check environment content Ty.content
        let packaged : TypingResult := { type := Ty.act Ty.expressive }
        pure { packaged with
          obligations := result.obligations
          trace := result.trace ++ [.m2TForce, .a0Synth] }
    | .mention => do
        let [value] ← expectArity operator arguments 1
          | failure "arity" "Mention expects one value"
        let result ← synth environment value
        let packaged : TypingResult := { type := Ty.act Ty.expressive }
        pure { packaged with
          obligations := result.obligations
          trace := result.trace ++ [.m2TForce, .a0Synth] }
    | .do => do
        let terms ← positionalTerms arguments
        let results ← terms.mapM fun term => synth environment term
        for result in results do
          if result.type == Ty.discourse ||
              (Ty.asUnary result.type .typeFormAct).isSome ||
              (Ty.asUnary result.type .typeFormPerfComp).isSome then pure ()
          else failure "discourse-type" "Do accepts acts, performance computations, or Discourse"
        pure <| mergeResults Ty.discourse results [.performance] []
          .m2TForce |>.withRule .a0Synth
    | .polar => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" "Polar expects one Content"
        let result ← check environment content Ty.content
        pure <| mergeResults (Ty.query (.named .sortBool [])) [result] [] []
          .m2TQuery |>.withRule .a0Synth
    | .openQ => do
        let [property] ← expectArity operator arguments 1
          | failure "arity" "OpenQ expects one Content-valued function"
        let result ← synth environment property
        match result.type with
        | .function _ [answer] output =>
            if output != Ty.content then
              failure "query-type" "OpenQ function does not return Content"
            else pure ()
            pure <| mergeResults (Ty.query answer) [result] [] []
              .m2TQuery |>.withRule .a0Synth
        | _ => failure "query-type" "OpenQ expects a unary function"
    | .ask => do
        let [query] ← expectArity operator arguments 1
          | failure "arity" "Ask expects one Query"
        let result ← synth environment query
        let some _ := Ty.asUnary result.type .typeFormQuery
          | failure "query-type" "Ask expects Query<A>"
        let packaged : TypingResult := { type := Ty.act Ty.question }
        pure { packaged with
          obligations := result.obligations
          trace := result.trace ++ [.m2TQuery, .a0Synth] }
    | .generic => do
        let [mode, property, nuclear] ← expectArity operator arguments 3
          | failure "arity" "Generic expects mode, restrictor, and nuclear scope"
        let modeResult ← check environment mode Ty.genericMode
        let propertyResult ← synth environment property
        let some (effectfulProperty, memberType) := oneArgumentFunction propertyResult
          | failure "generic-property" "Generic restrictor must be unary Content"
        if effectfulProperty || !isPure propertyResult then
          failure "generic-property" "Generic restrictor must be pure"
        else pure ()
        let nuclearResult ← check environment nuclear
          (Ty.effectfulFn [memberType] Ty.content)
        pure <| mergeResults Ty.content [modeResult, propertyResult, nuclearResult]
          (if nuclearResult.type == Ty.effectfulFn [memberType] Ty.content then
            [.effectfulCall] else []) [] .m2TGeneric |>.withRule .a0Synth
    | .locutionOf => do
        let [token, locution] ← expectArity operator arguments 2
          | failure "arity" "LocutionOf expects token and locution references"
        let tokenResult ← check environment token (Ty.referents Ty.utteranceToken)
        let locutionResult ← check environment locution (Ty.referents Ty.locution)
        pure <| mergeResults Ty.content [tokenResult, locutionResult] [] []
          .m2TLocutionOf |>.withRule .a0Synth
    | .named => contentInterface (some 2)
    | .happiness | .unhappiness | .desire | .evidentialBasis
    | .contrast | .metalinguisticallyDefective | .realizes | .speakerOf =>
        contentInterface none
    | .holds => do
        let [proposition] ← expectArity operator arguments 1
          | failure "arity" "Holds expects one Proposition"
        let result ← check environment proposition Ty.proposition
        pure <| mergeResults Ty.content [result] [] [] .m2TContentInterfaces
          |>.withRule .a0Synth
    | .supplement => do
        let [anchor, side, body] ← expectArity operator arguments 3
          | failure "arity" "Supplement expects anchor, side, and body"
        let anchorResult ← synth environment anchor
        let sideResult ← check environment side Ty.content
        let bodyResult ← check environment body Ty.content
        pure <| mergeResults Ty.content [anchorResult, sideResult, bodyResult]
          [.projective] [] .m2TContentInterfaces |>.withRule .a0Synth
    | .opaqueQuote => signConstructor "Opaque"
    | .wordSign => signConstructor "Word"
    | .nameSign => signConstructor "Name"
    | .letteralSign => signConstructor "Letteral"
    | .sentenceSign => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" "SentenceSign expects one Content"
        let result ← check environment content Ty.content
        let packaged : TypingResult := { type := Ty.sign "Sentence" }
        pure { packaged with
          obligations := result.obligations
          trace := result.trace ++ [.m2TSign, .a0Synth] }
    | .reify => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" "Reify expects one Content"
        let result ← check environment content Ty.content
        let packaged : TypingResult := { type := Ty.proposition }
        pure { packaged with
          obligations := result.obligations
          trace := result.trace ++ [.m2TReify, .a0Synth] }
    | .realizedContent => do
        let [token] ← expectArity operator arguments 1
          | failure "arity" "RealizedContent expects one token reference"
        let result ← check environment token (Ty.referents Ty.utteranceToken)
        pure <| mergeResults Ty.content [result] [.projective]
          [.definedness "RealizedContent" Ty.content] .m2TRealizedContent
          |>.withRule .a0Synth
    | .dropPlace => do
        let [relation, label] ← expectArity operator arguments 2
          | failure "arity" "DropPlace expects a relation and label"
        let relationResult ← synth environment relation
        let some row := Ty.asUnary relationResult.type .typeFormPredTerm
          | failure "drop-place-type" "DropPlace expects PredTerm<row>"
        let labelType ← match label with
          | .natural value =>
              if value > 0 then pure (Ty.index (toString value))
              else failure "drop-place-label" "DropPlace label must be positive"
          | .index "Eventuality" => pure (Ty.index "Eventuality")
          | _ => failure "drop-place-label" "DropPlace label is not a row label"
        let some _ := rowShape (Ty.rowMinus row labelType)
          | failure "drop-place-label" "DropPlace label is outside the row"
        pure <| mergeResults (Ty.predTerm (Ty.rowMinus row labelType))
          [relationResult] [] [] .m2TDropPlace |>.withRule .a0Synth
    | .teha => do
        let [base, exponent] ← expectArity operator arguments 2
          | failure "arity" "te'a expects base and exponent"
        let baseResult ← check environment base Ty.number
        let exponentResult ← check environment exponent Ty.natural
        pure <| mergeResults Ty.number [baseResult, exponentResult] [] []
          .m2TTeha |>.withRule .a0Synth
    | .subtract => do
        let [first, second] ← expectArity operator arguments 2
          | failure "arity" "subtraction expects two numbers"
        let firstResult ← check environment first Ty.number
        let secondResult ← check environment second Ty.number
        pure <| mergeResults Ty.number [firstResult, secondResult] [] []
          .m2TNumericInterfaces |>.withRule .a0Synth
    | .amountValue => do
        let [amount, scale] ← expectArity operator arguments 2
          | failure "arity" "AmountValue expects amount and scale"
        let amountResult ← check environment amount (Ty.referents Ty.amount)
        let scaleResult ← check environment scale (Ty.referents Ty.scale)
        pure <| mergeResults Ty.number [amountResult, scaleResult] [] []
          .m2TNumericInterfaces |>.withRule .a0Synth
    | .niRel | .jeiRel | .suhuRel => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" s!"{operator.name} expects one Content"
        let result ← check environment content Ty.content
        pure <| mergeResults (Ty.predTerm (Ty.arityRow 2)) [result] [] []
          .m2TNumericInterfaces |>.withRule .a0Synth
    | .aggregate => synthAggregate environment arguments
    | .basisUnitAt => synthBasisUnitAt environment arguments
    | .peerUnitAt => synthPeerUnitAt environment arguments
    | .jaiRoleAdmissible => synthJaiRoleAdmissible environment arguments
    | .add => binarySynth .b1TAddition fun first second =>
        match Ty.numberJoin first.type second.type with
        | some type => pure type
        | none => failure "number-type" "addition operands are not compatible numbers"
    | .equal => binarySynth .a0TEquality fun first second =>
        if Ty.equalityType first.type && Ty.equalityType second.type &&
            (Ty.compatible first.type second.type ||
              Ty.compatible second.type first.type) then pure Ty.content
        else failure "equality-type" "equality operands are incompatible"
    | .and => do
        let terms ← positionalTerms arguments
        match terms with
        | [] => pure { type := Ty.content, trace := [.a0TTop, .a0Synth] }
        | [first, second] =>
            let firstResult ← check environment first Ty.content
            let secondResult ← check environment second Ty.content
            pure <| mergeResults Ty.content [firstResult, secondResult] [] []
              .a0TAnd |>.withRule .a0Synth
        | _ => failure "arity" "and expects zero or two operands"
    | .implies => binaryCheck .b1TImplication Ty.content Ty.content
    | .not => unaryCheck .b1TNegation Ty.content Ty.content
    | .forall => quantify .b1TForall
    | .exists => quantify .b1TExists
    | .among => referenceBinary .b1TAmong
    | .presuppose => synthPresuppose environment arguments
    | .setOf => do
        let [property] ← expectArity operator arguments 1
          | failure "arity" "SetOf expects one property"
        let result ← synth environment property
        let some (effectful, inner) := oneArgumentFunction result
          | failure "set-property" "SetOf expects a unary Content property"
        if effectful || !isPure result then
          failure "set-property" "SetOf property must be pure"
        else pure ()
        pure <| mergeResults (Ty.set inner) [result] [] [] .a0TSetOf
          |>.withRule .a0Synth
    | .card => do
        let [setTerm] ← expectArity operator arguments 1
          | failure "arity" "Card expects one set"
        let setResult ← synth environment setTerm
        let some _ := Ty.asUnary setResult.type .typeFormSet
          | failure "card-type" "Card expects Set<T>"
        pure <| mergeResults Ty.cardinal [setResult] [.projective]
          [.finiteSetCardinalityDefined] .a0TCard |>.withRule .a0Synth
    | .admissibleThreshold => synthAdmissibleThreshold environment arguments
    | .stateClause => do
        let [content] ← expectArity operator arguments 1
          | failure "arity" "StateClause expects one Content"
        let result ← check environment content Ty.content
        pure <| mergeResults Ty.clauseContent [result] [] [] .a0TStateClause
          |>.withRule .a0Synth
    | .closeClause => do
        let [clause] ← expectArity operator arguments 1
          | failure "arity" "CloseClause expects one ClauseContent"
        let result ← check environment clause Ty.clauseContent
        pure <| mergeResults Ty.content [result] [] [] .a0TCloseClause
          |>.withRule .a0Synth
    | .perform => synthPerform environment arguments
    | .list => failure "expected-type" "List literals require an expected List<T>"
    | .refer | .selectExactly | .selectAtLeast | .selectAllBut | .local =>
        failure "expected-type" s!"{operator.name} requires an expected RefComp type"
    | _ => failure "unsupported-primitive"
        (s!"no M2 rule for first-order primitive {operator.name}")
    where
      constant (rule : M2TypingRuleId) (type : Ty) := do
        let terms ← positionalTerms arguments
        if !terms.isEmpty then failure "arity" s!"{operator.name} is nullary"
        else pure ()
        let raw := rawTermName operator.name
        if !(m2CoreConstantRecords.any fun record => record.name == raw) then
          failure "typing-manifest" s!"constant {raw} is absent from the generated core input"
        else pure ()
        pure { type, trace := [rule, .a0Synth] }
      signConstructor (kind : String) := do
        let [text] ← expectArity operator arguments 1
          | failure "arity" s!"{operator.name} expects one Text"
        let result ← check environment text Ty.text
        pure <| mergeResults (Ty.sign kind) [result] [] [] .m2TSign
          |>.withRule .a0Synth
      contentInterface (arity : Option Nat) := do
        let terms ← positionalTerms arguments
        match arity with
        | some expected =>
            if terms.length != expected then
              failure "arity" s!"{operator.name} expects {expected} arguments"
            else pure ()
        | none =>
            if terms.isEmpty then failure "arity" s!"{operator.name} expects arguments"
            else pure ()
        let results ← terms.mapM fun term => synth environment term
        pure <| mergeResults Ty.content results [] [] .m2TContentInterfaces
          |>.withRule .a0Synth
      binarySynth (rule : M2TypingRuleId)
          (resultType : TypingResult → TypingResult →
            Except TypingError Ty) := do
        let [first, second] ← expectArity operator arguments 2
          | failure "arity" s!"{operator.name} expects two operands"
        let firstResult ← synth environment first
        let secondResult ← synth environment second
        let type ← resultType firstResult secondResult
        pure <| mergeResults type [firstResult, secondResult] [] [] rule
          |>.withRule .a0Synth
      binaryCheck (rule : M2TypingRuleId) (expected resultType : Ty) := do
        let [first, second] ← expectArity operator arguments 2
          | failure "arity" s!"{operator.name} expects two operands"
        let firstResult ← check environment first expected
        let secondResult ← check environment second expected
        pure <| mergeResults resultType [firstResult, secondResult] [] [] rule
          |>.withRule .a0Synth
      unaryCheck (rule : M2TypingRuleId) (expected resultType : Ty) := do
        let [term] ← expectArity operator arguments 1
          | failure "arity" s!"{operator.name} expects one operand"
        let result ← check environment term expected
        pure <| mergeResults resultType [result] [] [] rule |>.withRule .a0Synth
      quantify (rule : M2TypingRuleId) := do
        let [property] ← expectArity operator arguments 1
          | failure "arity" s!"{operator.name} expects one property"
        let result ← synth environment property
        match result.type with
        | .function effectful parameters output =>
            if output != Ty.content || parameters.isEmpty ||
                !parameters.all Ty.quantifierDomain then
              failure "quantifier-property" "quantifier property has an invalid domain/result"
            else pure ()
            pure <| mergeResults Ty.content [result]
              (if effectful then [.effectfulCall] else []) [] rule
              |>.withRule .a0Synth
        | _ => failure "quantifier-property" "quantifier expects a function"
      referenceBinary (rule : M2TypingRuleId) := do
        let [first, second] ← expectArity operator arguments 2
          | failure "arity" s!"{operator.name} expects two references"
        let firstResult ← synth environment first
        let secondResult ← synth environment second
        if !Ty.referenceCompatible firstResult.type secondResult.type then
          failure "reference-type" s!"{operator.name} references are incompatible"
        else pure ()
        pure <| mergeResults Ty.content [firstResult, secondResult] [] [] rule
          |>.withRule .a0Synth

  partial def checkReferencePrimitive {scope : Nat}
      (environment : Environment scope) (operator : FirstOrderPrimitive)
      (arguments : TermList scope) (reference : Ty) (expected : Ty) :
      Except TypingError TypingResult := do
    let some inner := Ty.asUnary reference .typeFormReferents
      | failure "reference-type" "expected RefComp<Referents<T>>"
    match operator with
    | .selectExactly | .selectAtLeast | .selectAllBut => do
        let [count, property] ← expectArity operator arguments 2
          | failure "arity" s!"{operator.name} expects count and property"
        let countResult ← check environment count Ty.natural
        if operator != .selectAllBut && !provablyPositive count then
          failure "selection-floor" s!"{operator.name} requires a positive count"
        else pure ()
        let propertyResult ← check environment property (Ty.pureFn [inner] Ty.content)
        let rule := if operator == .selectExactly then .a0TSelectExactly
          else if operator == .selectAtLeast then .b1TSelectAtLeast
          else .b1TSelectAllBut
        pure <| mergeResults expected [countResult, propertyResult] [.refer] [] rule
          |>.withRule .a0Check
    | _ => failure "reference-form" s!"{operator.name} is not a reference computation"

  partial def synthPresuppose {scope : Nat} (environment : Environment scope)
      (arguments : TermList scope) : Except TypingError TypingResult := do
    let [condition, body] ← expectArity .presuppose arguments 2
      | failure "arity" "Presuppose expects condition and body"
    let conditionResult ← check environment condition Ty.content
    let bodyResult ← synth environment body
    if !Ty.computationCategory bodyResult.type then
      failure "presuppose-body" "Presuppose body is not a computation category"
    else pure ()
    pure <| mergeResults bodyResult.type [conditionResult, bodyResult]
      [.projective] [.presuppose "condition" bodyResult.type]
      .b1TPresupposeSynth |>.withRule .a0Synth

  partial def checkPresupposeReference {scope : Nat}
      (environment : Environment scope) (arguments : TermList scope)
      (expected : Ty) : Except TypingError TypingResult := do
    let [condition, body] ← expectArity .presuppose arguments 2
      | failure "arity" "Presuppose expects condition and body"
    let conditionResult ← check environment condition Ty.content
    let bodyResult ← check environment body expected
    pure <| mergeResults expected [conditionResult, bodyResult] [.projective]
      [.presuppose "condition" expected] .b1TPresupposeReference
      |>.withRule .a0Check

  partial def synthAdmissibleThreshold {scope : Nat}
      (environment : Environment scope) (arguments : TermList scope) :
      Except TypingError TypingResult := do
    let [kind, property, purpose] ← expectArity .admissibleThreshold arguments 3
      | failure "arity" "AdmissibleThreshold expects kind, property, purpose"
    let kindResult ← check environment kind Ty.thresholdKind
    let propertyResult ← synth environment property
    let some (effectful, _) := oneArgumentFunction propertyResult
      | failure "threshold-property" "threshold property must be unary Content"
    if effectful || !isPure propertyResult then
      failure "threshold-property" "threshold property must be pure"
    else pure ()
    let purposeResult ← check environment purpose (Ty.referents Ty.entity)
    pure <| mergeResults (Ty.pureFn [Ty.natural] Ty.content)
      [kindResult, propertyResult, purposeResult] [] [] .a0TAdmissibleThreshold
      |>.withRule .a0Synth

  partial def synthPerform {scope : Nat} (environment : Environment scope)
      (arguments : TermList scope) : Except TypingError TypingResult := do
    let terms ← positionalTerms arguments
    let (roleResult, act) ← match terms with
      | [act] => pure (none, act)
      | [role, act] =>
          pure (some (← check environment role Ty.occurrenceRole), act)
      | _ => failure "arity" "Perform expects an act, optionally preceded by a role"
    let result ← synth environment act
    match result.type with
    | .named .typeFormAct [force] =>
        pure <| mergeResults (Ty.perfComp (Ty.actOccurrence force))
          (roleResult.toList ++ [result]) [.performance] []
          (if roleResult.isSome then .m2TPerformRole else .a0TPerform)
          |>.withRule .a0Synth
    | _ => failure "perform-type" "Perform expects Act<F>"

  partial def synthAggregate {scope : Nat} (environment : Environment scope)
      (arguments : TermList scope) : Except TypingError TypingResult := do
    let [basis, group] ← expectArity .aggregate arguments 2
      | failure "arity" "Aggregate expects basis and group"
    let basisResult ← synth environment basis
    let some (whole, component) :=
        Ty.asBinary basisResult.type .typeFormDecompositionBasis
      | failure "aggregate-type" "Aggregate basis has the wrong type"
    let some inner := Ty.asUnary whole .typeFormGroup
      | failure "aggregate-type" "Aggregate basis whole must be Group<T>"
    if !Ty.compatible inner component || !Ty.compatible component inner then
      failure "aggregate-type" "Aggregate basis component does not match its group"
    else pure ()
    let groupResult ← check environment group (Ty.group component)
    pure <| mergeResults Ty.content [basisResult, groupResult] [] []
      .m2TAggregate |>.withRule .a0Synth

  partial def synthBasisUnitAt {scope : Nat} (environment : Environment scope)
      (arguments : TermList scope) : Except TypingError TypingResult := do
    let [basis, unit, cover] ← expectArity .basisUnitAt arguments 3
      | failure "arity" "BasisUnitAt expects basis, unit, and cover"
    let basisResult ← synth environment basis
    let some (_, component) :=
        Ty.asBinary basisResult.type .typeFormDecompositionBasis
      | failure "basis-unit-type" "BasisUnitAt basis has the wrong type"
    let unitResult ← check environment unit (Ty.referents component)
    let coverResult ← check environment cover (Ty.referents component)
    pure <| mergeResults Ty.content [basisResult, unitResult, coverResult] [] []
      .m2TBasisUnitAt |>.withRule .a0Synth

  partial def synthPeerUnitAt {scope : Nat} (environment : Environment scope)
      (arguments : TermList scope) : Except TypingError TypingResult := do
    let [basis, unit, wholeTerm] ← expectArity .peerUnitAt arguments 3
      | failure "arity" "PeerUnitAt expects basis, unit, and whole"
    let basisResult ← synth environment basis
    let some (whole, component) :=
        Ty.asBinary basisResult.type .typeFormDecompositionBasis
      | failure "peer-unit-type" "PeerUnitAt basis has the wrong type"
    let unitResult ← check environment unit (Ty.referents component)
    let wholeResult ← check environment wholeTerm (Ty.referents whole)
    pure <| mergeResults Ty.content [basisResult, unitResult, wholeResult] [] []
      .m2TPeerUnitAt |>.withRule .a0Synth

  partial def synthJaiRoleAdmissible {scope : Nat}
      (environment : Environment scope) (arguments : TermList scope) :
      Except TypingError TypingResult := do
    let [relation, role] ← expectArity .jaiRoleAdmissible arguments 2
      | failure "arity" "JaiRoleAdmissible expects relation and role"
    let relationResult ← synth environment relation
    let some _ := Ty.asUnary relationResult.type .typeFormPredTerm
      | failure "jai-role-type" "JaiRoleAdmissible first operand is not PredTerm"
    let roleResult ← synth environment role
    match roleResult.type with
    | .function false [first, second] result =>
        if result != Ty.content ||
            (Ty.asUnary first .typeFormReferents).isNone ||
            (Ty.asUnary second .typeFormReferents).isNone ||
            !isPure roleResult then
          failure "jai-role-type" "raised role must be a pure binary reference relation"
        else pure ()
    | _ => failure "jai-role-type" "raised role must be a pure binary reference relation"
    pure <| mergeResults Ty.content [relationResult, roleResult] [] []
      .m2TJaiRoleAdmissible |>.withRule .a0Synth
end

def typingRuleRecordsFor (result : TypingResult) : List M2TypingRuleRecord :=
  result.trace.map M2TypingRuleId.record

def wrongExpectedTypeFails {scope : Nat} (environment : Environment scope)
    (term : Term scope) (expected : Ty) : Prop :=
  ∀ actual, synth environment term = .ok actual →
    Ty.compatible actual.type expected = false →
      ∃ error, check environment term expected = .error error

end M2
end SmusniPilot
