import SmusniPilot.M2Inventory
import SmusniPilot.BundleBinding

namespace SmusniPilot
namespace M2

namespace Ty

def named0 (name : TypeName) : Ty := .named name []
def entity : Ty := named0 .sortEntity
def eventuality : Ty := named0 .sortEventuality
def amount : Ty := named0 .sortAmount
def scale : Ty := named0 .sortScale
def number : Ty := named0 .sortNumber
def natural : Ty := named0 .sortNatural
def cardinal : Ty := named0 .sortCardinal
def thresholdKind : Ty := named0 .typeThresholdKind
def content : Ty := named0 .typeContent
def clauseContent : Ty := named0 .typeClauseContent
def discourse : Ty := named0 .typeDiscourse

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
  else if actual == cardinal && (expected == natural || expected == number) then true
  else if actual == natural && expected == number then true
  else if actual == clauseContent then
    expected == pureFn [referents eventuality] content ||
      expected == effectfulFn [referents eventuality] content
  else if expected == clauseContent then
    actual == pureFn [referents eventuality] content ||
      actual == effectfulFn [referents eventuality] content
  else match asUnary expected .typeFormReferents with
    | some inner => compatible actual inner
    | none =>
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
      [ .sortEntity, .sortEventuality, .sortNumber, .sortNatural,
        .sortCardinal, .typeThresholdKind ].contains name && arguments.isEmpty ||
      [ .typeFormSet, .typeFormGroup, .typeFormList ].contains name &&
        arguments.length == 1
  | _ => false

def firstOrder : Ty → Bool
  | .named name arguments =>
      [ .sortEntity, .sortEventuality, .sortNumber, .sortNatural,
        .sortCardinal ].contains name && arguments.isEmpty ||
      [ .typeFormSet, .typeFormGroup, .typeFormList ].contains name &&
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
    | .string _ => failure "unsupported-literal" "A0 has no Text literal typing rule"
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
    | .lexical predicate arguments =>
        match environment.lookupLexical predicate with
        | none => failure "lexical-signature" s!"missing typed lexical signature {predicate}"
        | some type => applyFunction environment { type } arguments
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
    let terms ← positionalTerms arguments
    match functionResult.type with
    | .function effectful parameters result =>
        if parameters.length != terms.length then
          failure "application-arity"
            (s!"function expects {parameters.length}, got {terms.length}")
        else pure ()
        let argumentResults ← (terms.zip parameters).mapM fun pair =>
          check environment pair.1 pair.2
        let rule := if effectful then .a0TApplyEffectful else .a0TApplyPure
        pure <| mergeResults result (functionResult :: argumentResults)
          (if effectful then [.effectfulCall] else []) [] rule |>.withRule .a0Synth
    | type =>
        if type == Ty.clauseContent then
          let [argument] := terms
            | failure "application-arity" "ClauseContent expects one event reference"
          let result ← check environment argument (Ty.referents Ty.eventuality)
          pure <| mergeResults Ty.content [functionResult, result] [] []
            .a0TApplyClauseContent |>.withRule .a0Synth
        else failure "application-type" s!"cannot apply {repr type}"

  partial def synthPrimitive {scope : Nat} (environment : Environment scope)
      (operator : FirstOrderPrimitive) (arguments : TermList scope) :
      Except TypingError TypingResult :=
    match operator with
    | .speaker => constant .a0TSpeaker (Ty.referents Ty.entity)
    | .audience => constant .a0TAudience (Ty.referents Ty.entity)
    | .tooManyK => constant .a0TThresholdKind Ty.thresholdKind
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
        let some (_, inner) := oneArgumentFunction result
          | failure "set-property" "SetOf expects a unary Content property"
        if !isPure result then failure "set-property" "SetOf property must be pure"
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
    | .refer | .selectExactly | .selectAtLeast | .selectAllBut =>
        failure "expected-type" s!"{operator.name} requires an expected RefComp type"
    | _ => failure "unsupported-primitive"
        (s!"no M2 rule for first-order primitive {operator.name}")
    where
      constant (rule : M2TypingRuleId) (type : Ty) := do
        let terms ← positionalTerms arguments
        if !terms.isEmpty then failure "arity" s!"{operator.name} is nullary"
        else pure ()
        pure { type, trace := [rule, .a0Synth] }
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
    let some _ := oneArgumentFunction propertyResult
      | failure "threshold-property" "threshold property must be unary Content"
    if !isPure propertyResult then
      failure "threshold-property" "threshold property must be pure"
    else pure ()
    let purposeResult ← check environment purpose (Ty.referents Ty.entity)
    pure <| mergeResults (Ty.pureFn [Ty.natural] Ty.content)
      [kindResult, propertyResult, purposeResult] [] [] .a0TAdmissibleThreshold
      |>.withRule .a0Synth

  partial def synthPerform {scope : Nat} (environment : Environment scope)
      (arguments : TermList scope) : Except TypingError TypingResult := do
    let [act] ← expectArity .perform arguments 1
      | failure "arity" "Perform expects one act"
    let result ← synth environment act
    match result.type with
    | .named .typeFormAct [force] =>
        pure <| mergeResults (Ty.perfComp (Ty.actOccurrence force)) [result]
          [.performance] [] .a0TPerform |>.withRule .a0Synth
    | _ => failure "perform-type" "Perform expects Act<F>"
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
