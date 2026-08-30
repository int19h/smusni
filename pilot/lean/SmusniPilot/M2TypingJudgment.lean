import SmusniPilot.M2Typing

namespace SmusniPilot
namespace M2

structure TypingObservation where
  type : Ty
  effects : List Effect := []
  obligations : List Obligation := []
  deriving Repr, BEq, Inhabited

def TypingResult.observation (result : TypingResult) : TypingObservation := {
  type := result.type
  effects := result.effects
  obligations := result.obligations }

@[simp] theorem except_ok_bind_judgment {error first second : Type}
    (item : first) (next : first → Except error second) :
    ((Except.ok item : Except error first) >>= next) = next item := rfl

@[simp] theorem except_map_ok_judgment {error first second : Type}
    (item : first) (next : first → second) :
    next <$> (Except.ok item : Except error first) = .ok (next item) := rfl

@[simp] theorem except_pure_ok_judgment {error value : Type} (item : value) :
    (pure item : Except error value) = .ok item := rfl

def mergeObservations (type : Ty) (results : List TypingObservation)
    (effects : List Effect := []) (obligations : List Obligation := []) :
    TypingObservation := {
  type
  effects := canonicalEffects (results.flatMap (·.effects) ++ effects)
  obligations := results.flatMap (·.obligations) ++ obligations }

def judgmentTermList {scope : Nat} : List (Term scope) → TermList scope
  | [] => .nil
  | head :: tail => .positional head (judgmentTermList tail)

mutual
  inductive SynthJudgment : {scope : Nat} → Environment scope →
      Term scope → TypingObservation → Prop where
    | bound {scope : Nat} (environment : Environment scope) (index : Fin scope) :
        SynthJudgment environment (.bound index) { type := environment.bound index }
    | free {scope : Nat} (environment : Environment scope) (identity : FreeId)
        (type : Ty) (found : environment.lookupFree identity = some type) :
        SynthJudgment environment (.free identity) { type }
    | natural {scope : Nat} (environment : Environment scope) (value : Nat) :
        SynthJudgment environment (.natural value) { type := Ty.natural }
    | string {scope : Nat} (environment : Environment scope) (value : String) :
        SynthJudgment environment (.string value) { type := Ty.text }
    | lambda {scope : Nat} (environment : Environment scope) (binderType : Ty)
        (body : Term (scope + 1)) (bodyResult : TypingObservation)
        (bodyTyping : SynthJudgment (environment.extend binderType) body bodyResult) :
        SynthJudgment environment (.lambda binderType body) {
          type := .function (!bodyResult.effects.isEmpty) [binderType] bodyResult.type
          obligations := bodyResult.obligations }
    | bindReference {scope : Nat} (environment : Environment scope)
        (binderType : Ty) (computation : Term scope) (body : Term (scope + 1))
        (computationResult bodyResult : TypingObservation)
        (computationTyping : CheckJudgment environment computation
          (Ty.refComp binderType) computationResult)
        (bodyTyping : SynthJudgment (environment.extend binderType) body bodyResult) :
        SynthJudgment environment (.bind binderType computation body)
          (mergeObservations bodyResult.type [computationResult, bodyResult])
    | application {scope : Nat} (environment : Environment scope)
        (function : Term scope) (arguments : TermList scope)
        (functionResult result : TypingObservation)
        (functionTyping : SynthJudgment environment function functionResult)
        (applicationTyping : ApplyJudgment environment functionResult arguments result) :
        SynthJudgment environment (.apply function arguments) result
    | lexicalDeclared {scope : Nat} (environment : Environment scope)
        (head : String) (arguments : TermList scope) (type : Ty)
        (result : TypingObservation)
        (found : environment.lookupLexical head = some type)
        (applicationTyping : ApplyJudgment environment { type } arguments result) :
        SynthJudgment environment (.lexical head arguments) result
    | lexicalRow {scope : Nat} (environment : Environment scope)
        (head : String) (arguments : TermList scope) (row : M2LexicalRowRecord)
        (results : List TypingObservation) (ordinary : Nat) (eventFilled : Bool)
        (notDeclared : environment.lookupLexical head = none)
        (found : lookupLexicalRow head = some row)
        (argumentsTyping : LexicalArgumentsJudgment environment row arguments []
          results ordinary eventFilled)
        (withinRow : ordinary ≤ row.ordinaryArity) :
        SynthJudgment environment (.lexical head arguments)
          (mergeObservations
            (if ordinary == row.ordinaryArity &&
                (row.eventMode == .holdingState || eventFilled)
              then Ty.content else lexicalRowType row) results)
    | primitive {scope : Nat} (environment : Environment scope)
        (operator : FirstOrderPrimitive) (arguments : TermList scope)
        (result : TypingObservation)
        (typing : PrimitiveJudgment environment operator arguments result) :
        SynthJudgment environment (.primitive operator arguments) result

  inductive CheckJudgment : {scope : Nat} → Environment scope →
      Term scope → Ty → TypingObservation → Prop where
    | fromSynth {scope : Nat} (environment : Environment scope)
        (term : Term scope) (expected : Ty) (result : TypingObservation)
        (typing : SynthJudgment environment term result)
        (compatible : Ty.compatible result.type expected = true) :
        CheckJudgment environment term expected result
    | context {scope : Nat} (environment : Environment scope) (site : SiteId)
        (arguments : TermList scope) (inner : Ty)
        (results : List TypingObservation)
        (argumentsTyping : ValueArgumentsJudgment environment arguments results) :
        CheckJudgment environment (.context site arguments) (Ty.refComp inner)
          (mergeObservations (Ty.refComp inner) results [.context])
    | vague {scope : Nat} (environment : Environment scope) (site : SiteId)
        (constraint : Term scope) (inner : Ty) (property : TypingObservation)
        (propertyTyping : SynthJudgment environment constraint property)
        (propertyType : property.type = Ty.pureFn [inner] Ty.content)
        (pure : property.effects = []) :
        CheckJudgment environment (.vague site constraint) (Ty.refComp inner)
          (mergeObservations (Ty.refComp inner) [property] [.context])
    | referReference {scope : Nat} (environment : Environment scope)
        (property : Term scope) (inner : Ty) (propertyResult : TypingObservation)
        (propertyTyping : SynthJudgment environment property propertyResult)
        (propertyType : propertyResult.type =
          Ty.effectfulFn [Ty.referents inner] Ty.content ∨
          propertyResult.type = Ty.pureFn [Ty.referents inner] Ty.content) :
        CheckJudgment environment (Term.primitive .refer (judgmentTermList [property]))
          (Ty.refComp (Ty.referents inner))
          (mergeObservations (Ty.refComp (Ty.referents inner)) [propertyResult]
            ((if propertyResult.type ==
                Ty.effectfulFn [Ty.referents inner] Ty.content
              then [.effectfulCall] else []) ++ [.refer]))
    | referMember {scope : Nat} (environment : Environment scope)
        (property : Term scope) (inner : Ty) (propertyResult : TypingObservation)
        (propertyTyping : SynthJudgment environment property propertyResult)
        (propertyType : propertyResult.type = Ty.pureFn [inner] Ty.content)
        (pure : propertyResult.effects = [])
        (notReferenceDomain : (inner == Ty.referents inner) = false)
        (memberCompatible : Ty.compatible inner inner = true) :
        CheckJudgment environment (Term.primitive .refer (judgmentTermList [property]))
          (Ty.refComp (Ty.referents inner))
          (mergeObservations (Ty.refComp (Ty.referents inner)) [propertyResult] [.refer])
    | local {scope : Nat} (environment : Environment scope)
        (body : Term scope) (inner : Ty) (bodyResult : TypingObservation)
        (bodyTyping : CheckJudgment environment body (Ty.refComp inner) bodyResult) :
        CheckJudgment environment (Term.primitive .local (judgmentTermList [body]))
          (Ty.refComp inner) (mergeObservations (Ty.refComp inner) [bodyResult])
    | list {scope : Nat} (environment : Environment scope)
        (arguments : TermList scope) (itemType : Ty)
        (results : List TypingObservation)
        (itemsTyping : CheckArgumentsJudgment environment arguments itemType results) :
        CheckJudgment environment (.primitive .list arguments) (Ty.list itemType)
          (mergeObservations (Ty.list itemType) results)
    | select {scope : Nat} (environment : Environment scope)
        (operator : FirstOrderPrimitive) (count property : Term scope) (inner : Ty)
        (countResult propertyResult : TypingObservation)
        (selected : operator = .selectExactly ∨ operator = .selectAtLeast ∨
          operator = .selectAllBut)
        (countTyping : CheckJudgment environment count Ty.natural countResult)
        (floor : operator = .selectAllBut ∨ provablyPositive count = true)
        (propertyTyping : CheckJudgment environment property
          (Ty.pureFn [inner] Ty.content) propertyResult) :
        CheckJudgment environment
          (.primitive operator (judgmentTermList [count, property]))
          (Ty.refComp (Ty.referents inner))
          (mergeObservations (Ty.refComp (Ty.referents inner))
            [countResult, propertyResult] [.refer])

  inductive ApplyJudgment : {scope : Nat} → Environment scope →
      TypingObservation → TermList scope → TypingObservation → Prop where
    | functionZero {scope : Nat} (environment : Environment scope)
        (effectful : Bool) (result : Ty) (functionResult : TypingObservation)
        (functionType : functionResult.type = .function effectful [] result) :
        ApplyJudgment environment functionResult .nil
          (mergeObservations result [functionResult]
            (if effectful then [.effectfulCall] else []))
    | functionPartialZero {scope : Nat} (environment : Environment scope)
        (effectful : Bool) (parameters : List Ty) (result : Ty)
        (nonempty : parameters ≠ []) (functionResult : TypingObservation)
        (functionType : functionResult.type = .function effectful parameters result) :
        ApplyJudgment environment functionResult .nil
          (mergeObservations (.function effectful parameters result) [functionResult]
            (if effectful then [.effectfulCall] else []))
    | functionLast {scope : Nat} (environment : Environment scope)
        (effectful : Bool) (parameter : Ty) (remaining : List Ty) (result : Ty)
        (functionResult argumentResult : TypingObservation) (argument : Term scope)
        (functionType : functionResult.type =
          .function effectful (parameter :: remaining) result)
        (argumentTyping : CheckJudgment environment argument parameter argumentResult) :
        ApplyJudgment environment functionResult (.positional argument .nil)
          (mergeObservations
            (if remaining.isEmpty then result else .function effectful remaining result)
            [functionResult, argumentResult]
            (if effectful then [.effectfulCall] else []))
    | functionMore {scope : Nat} (environment : Environment scope)
        (effectful : Bool) (parameter : Ty) (remaining : List Ty) (result : Ty)
        (functionResult argumentResult intermediate final : TypingObservation)
        (argument : Term scope) (tail : TermList scope)
        (tailNonempty : tail ≠ .nil)
        (functionType : functionResult.type =
          .function effectful (parameter :: remaining) result)
        (argumentTyping : CheckJudgment environment argument parameter argumentResult)
        (intermediateEquation : intermediate = mergeObservations
          (if remaining.isEmpty then result else .function effectful remaining result)
          [functionResult, argumentResult]
          (if effectful then [.effectfulCall] else []))
        (tailTyping : ApplyJudgment environment intermediate tail final) :
        ApplyJudgment environment functionResult (.positional argument tail) final
    | clauseContent {scope : Nat} (environment : Environment scope)
        (functionResult argumentResult : TypingObservation) (argument : Term scope)
        (functionType : functionResult.type = Ty.clauseContent)
        (argumentTyping : CheckJudgment environment argument
          (Ty.referents Ty.eventuality) argumentResult) :
        ApplyJudgment environment functionResult (.positional argument .nil)
          (mergeObservations Ty.content [functionResult, argumentResult])
    | predTerm {scope : Nat} (environment : Environment scope)
        (functionResult : TypingObservation) (arguments : TermList scope)
        (row : Ty) (ordinary : Nat) (eventRequired : Bool)
        (results : List TypingObservation) (ordinaryFilled : Nat) (eventFilled : Bool)
        (functionType : functionResult.type = Ty.predTerm row)
        (shape : rowShape row = some (ordinary, eventRequired))
        (argumentsTyping : PredArgumentsJudgment environment arguments results
          ordinaryFilled eventFilled)
        (withinRow : ordinaryFilled ≤ ordinary)
        (eventWithinRow : eventFilled = true → eventRequired = true)
        (rowCondition : (decide (ordinaryFilled > ordinary) ||
          eventFilled && !eventRequired) = false)
        (noBadRow : ¬(ordinary < ordinaryFilled ∨
          (eventFilled = true ∧ eventRequired = false))) :
        ApplyJudgment environment functionResult arguments
          (mergeObservations
            (if ordinaryFilled == ordinary && (!eventRequired || eventFilled)
              then Ty.content else Ty.predTerm (Ty.residualRow
                (ordinary - ordinaryFilled) (eventRequired && !eventFilled)))
            (functionResult :: results))

  inductive SynthArgumentsJudgment : {scope : Nat} → Environment scope →
      TermList scope → List TypingObservation → Prop where
    | nil {scope : Nat} (environment : Environment scope) :
        SynthArgumentsJudgment environment .nil []
    | positional {scope : Nat} (environment : Environment scope)
        (head : Term scope) (tail : TermList scope)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (headTyping : SynthJudgment environment head headResult)
        (tailTyping : SynthArgumentsJudgment environment tail tailResults) :
        SynthArgumentsJudgment environment (.positional head tail)
          (headResult :: tailResults)

  inductive CheckArgumentsJudgment : {scope : Nat} → Environment scope →
      TermList scope → Ty → List TypingObservation → Prop where
    | nil {scope : Nat} (environment : Environment scope) (expected : Ty) :
        CheckArgumentsJudgment environment .nil expected []
    | positional {scope : Nat} (environment : Environment scope)
        (head : Term scope) (tail : TermList scope) (expected : Ty)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (headTyping : CheckJudgment environment head expected headResult)
        (tailTyping : CheckArgumentsJudgment environment tail expected tailResults) :
        CheckArgumentsJudgment environment (.positional head tail) expected
          (headResult :: tailResults)

  inductive ValueArgumentsJudgment : {scope : Nat} → Environment scope →
      TermList scope → List TypingObservation → Prop where
    | nil {scope : Nat} (environment : Environment scope) :
        ValueArgumentsJudgment environment .nil []
    | positional {scope : Nat} (environment : Environment scope)
        (head : Term scope) (tail : TermList scope)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (value : isValue head = true)
        (headTyping : SynthJudgment environment head headResult)
        (tailTyping : ValueArgumentsJudgment environment tail tailResults) :
        ValueArgumentsJudgment environment (.positional head tail)
          (headResult :: tailResults)

  inductive PredArgumentsJudgment : {scope : Nat} → Environment scope →
      TermList scope → List TypingObservation → Nat → Bool → Prop where
    | nil {scope : Nat} (environment : Environment scope) :
        PredArgumentsJudgment environment .nil [] 0 false
    | positional {scope : Nat} (environment : Environment scope)
        (head : Term scope) (tail : TermList scope)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (ordinary : Nat) (eventFilled : Bool)
        (headTyping : SynthJudgment environment head headResult)
        (tailTyping : PredArgumentsJudgment environment tail tailResults
          ordinary eventFilled) :
        PredArgumentsJudgment environment (.positional head tail)
          (headResult :: tailResults) (ordinary + 1) eventFilled
    | event {scope : Nat} (environment : Environment scope)
        (head : Term scope) (tail : TermList scope)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (ordinary : Nat) (headTyping : CheckJudgment environment head
          (Ty.referents Ty.eventuality) headResult)
        (tailTyping : PredArgumentsJudgment environment tail tailResults ordinary false) :
        PredArgumentsJudgment environment (.labelled ":Eventuality" head tail)
          (headResult :: tailResults) ordinary true
    | labelled {scope : Nat} (environment : Environment scope)
        (label : String) (notEvent : label ≠ ":Eventuality")
        (head : Term scope) (tail : TermList scope)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (ordinary : Nat) (eventFilled : Bool)
        (headTyping : SynthJudgment environment head headResult)
        (tailTyping : PredArgumentsJudgment environment tail tailResults
          ordinary eventFilled) :
        PredArgumentsJudgment environment (.labelled label head tail)
          (headResult :: tailResults) (ordinary + 1) eventFilled

  inductive LexicalArgumentsJudgment : {scope : Nat} → Environment scope →
      M2LexicalRowRecord → TermList scope → List String →
      List TypingObservation → Nat → Bool → Prop where
    | nil {scope : Nat} (environment : Environment scope)
        (row : M2LexicalRowRecord) (seen : List String) :
        LexicalArgumentsJudgment environment row .nil seen [] 0 false
    | positional {scope : Nat} (environment : Environment scope)
        (row : M2LexicalRowRecord) (head : Term scope) (tail : TermList scope)
        (seen : List String) (headResult : TypingObservation)
        (tailResults : List TypingObservation) (ordinary : Nat) (eventFilled : Bool)
        (headTyping : SynthJudgment environment head headResult)
        (tailTyping : LexicalArgumentsJudgment environment row tail seen
          tailResults ordinary eventFilled) :
        LexicalArgumentsJudgment environment row (.positional head tail) seen
          (headResult :: tailResults) (ordinary + 1) eventFilled
    | event {scope : Nat} (environment : Environment scope)
        (row : M2LexicalRowRecord) (head : Term scope) (tail : TermList scope)
        (seen : List String) (fresh : seen.contains ":Eventuality" = false)
        (direct : row.eventMode = .directEvent) (headResult : TypingObservation)
        (tailResults : List TypingObservation) (ordinary : Nat)
        (headTyping : CheckJudgment environment head
          (Ty.referents Ty.eventuality) headResult)
        (tailTyping : LexicalArgumentsJudgment environment row tail
          (":Eventuality" :: seen) tailResults ordinary false) :
        LexicalArgumentsJudgment environment row
          (.labelled ":Eventuality" head tail) seen
          (headResult :: tailResults) ordinary true
    | labelled {scope : Nat} (environment : Environment scope)
        (row : M2LexicalRowRecord) (label : String) (head : Term scope)
        (tail : TermList scope) (seen : List String)
        (fresh : seen.contains label = false) (notEvent : label ≠ ":Eventuality")
        (place : Nat) (decoded : (label.drop 1).toString.toNat? = some place)
        (positive : place > 0) (within : place ≤ row.ordinaryArity)
        (headResult : TypingObservation) (tailResults : List TypingObservation)
        (ordinary : Nat) (eventFilled : Bool)
        (headTyping : SynthJudgment environment head headResult)
        (tailTyping : LexicalArgumentsJudgment environment row tail (label :: seen)
          tailResults ordinary eventFilled) :
        LexicalArgumentsJudgment environment row (.labelled label head tail) seen
          (headResult :: tailResults) (ordinary + 1) eventFilled

  inductive PrimitiveJudgment : {scope : Nat} → Environment scope →
      FirstOrderPrimitive → TermList scope → TypingObservation → Prop where
    | constant {scope : Nat} (environment : Environment scope)
        (operator : FirstOrderPrimitive) (result : TypingObservation)
        (rule : ConstantPrimitiveRule operator result)
        (manifest : m2CoreConstantRecords.any
          (fun record => record.name == rawTermName operator.name) = true) :
        PrimitiveJudgment environment operator .nil result
    | binarySynth {scope : Nat} (environment : Environment scope)
        (operator : FirstOrderPrimitive) (first second : Term scope)
        (firstResult secondResult : TypingObservation) (resultType : Ty)
        (firstTyping : SynthJudgment environment first firstResult)
        (secondTyping : SynthJudgment environment second secondResult)
        (rule : BinaryPrimitiveRule operator firstResult secondResult resultType) :
        PrimitiveJudgment environment operator (judgmentTermList [first, second])
          (mergeObservations resultType [firstResult, secondResult])
    | unaryCheck {scope : Nat} (environment : Environment scope)
        (operator : FirstOrderPrimitive) (term : Term scope)
        (expected resultType : Ty) (result : TypingObservation)
        (typing : CheckJudgment environment term expected result)
        (rule : UnaryCheckedPrimitiveRule operator expected resultType) :
        PrimitiveJudgment environment operator (judgmentTermList [term])
          (mergeObservations resultType [result])
    | binaryCheck {scope : Nat} (environment : Environment scope)
        (operator : FirstOrderPrimitive) (first second : Term scope)
        (expected resultType : Ty) (firstResult secondResult : TypingObservation)
        (firstTyping : CheckJudgment environment first expected firstResult)
        (secondTyping : CheckJudgment environment second expected secondResult)
        (rule : BinaryCheckedPrimitiveRule operator expected resultType) :
        PrimitiveJudgment environment operator (judgmentTermList [first, second])
          (mergeObservations resultType [firstResult, secondResult])
    | top {scope : Nat} (environment : Environment scope) :
        PrimitiveJudgment environment .and .nil { type := Ty.content }
    | and {scope : Nat} (environment : Environment scope)
        (first second : Term scope) (firstResult secondResult : TypingObservation)
        (firstTyping : CheckJudgment environment first Ty.content firstResult)
        (secondTyping : CheckJudgment environment second Ty.content secondResult) :
        PrimitiveJudgment environment .and (judgmentTermList [first, second])
          (mergeObservations Ty.content [firstResult, secondResult])

  inductive ConstantPrimitiveRule : FirstOrderPrimitive → TypingObservation → Prop where
    | speaker : ConstantPrimitiveRule .speaker { type := Ty.referents Ty.entity }
    | audience : ConstantPrimitiveRule .audience { type := Ty.referents Ty.entity }
    | tooManyK : ConstantPrimitiveRule .tooManyK { type := Ty.thresholdKind }
    | currentToken : ConstantPrimitiveRule .currentToken
        { type := Ty.referents Ty.utteranceToken }
    | host : ConstantPrimitiveRule .host { type := Ty.occurrenceRole }
    | attachedDisplay : ConstantPrimitiveRule .attachedDisplay { type := Ty.occurrenceRole }
    | attachedAddress : ConstantPrimitiveRule .attachedAddress { type := Ty.occurrenceRole }
    | typical : ConstantPrimitiveRule .typical { type := Ty.genericMode }
    | moderate : ConstantPrimitiveRule .moderate { type := Ty.intensity }
    | intense : ConstantPrimitiveRule .intense { type := Ty.intensity }
    | observation : ConstantPrimitiveRule .observation { type := Ty.epistemology }
    | hearsay : ConstantPrimitiveRule .hearsay { type := Ty.epistemology }
    | manyK : ConstantPrimitiveRule .manyK { type := Ty.thresholdKind }
    | now : ConstantPrimitiveRule .now { type := Ty.time }
    | miAOthers : ConstantPrimitiveRule .miAOthers {
        type := Ty.referents Ty.entity
        effects := [.projective]
        obligations := [.definedness "term:MiAOthers" (Ty.referents Ty.entity)] }
    | maAOthers : ConstantPrimitiveRule .maAOthers {
        type := Ty.referents Ty.entity
        effects := [.projective]
        obligations := [.definedness "term:MaAOthers" (Ty.referents Ty.entity)] }
    | doOOthers : ConstantPrimitiveRule .doOOthers {
        type := Ty.referents Ty.entity
        effects := [.projective]
        obligations := [.definedness "term:DoOOthers" (Ty.referents Ty.entity)] }

  inductive BinaryPrimitiveRule : FirstOrderPrimitive → TypingObservation →
      TypingObservation → Ty → Prop where
    | addition (first second : TypingObservation) (result : Ty)
        (joined : Ty.numberJoin first.type second.type = some result) :
        BinaryPrimitiveRule .add first second result
    | equality (first second : TypingObservation)
        (firstAdmissible : Ty.equalityType first.type = true)
        (secondAdmissible : Ty.equalityType second.type = true)
        (compatible : Ty.compatible first.type second.type = true ∨
          Ty.compatible second.type first.type = true) :
        BinaryPrimitiveRule .equal first second Ty.content
    | among (first second : TypingObservation)
        (compatible : Ty.referenceCompatible first.type second.type = true) :
        BinaryPrimitiveRule .among first second Ty.content

  inductive UnaryCheckedPrimitiveRule : FirstOrderPrimitive → Ty → Ty → Prop where
    | not : UnaryCheckedPrimitiveRule .not Ty.content Ty.content
    | stateClause : UnaryCheckedPrimitiveRule .stateClause Ty.content Ty.clauseContent

  inductive BinaryCheckedPrimitiveRule : FirstOrderPrimitive → Ty → Ty → Prop where
    | implies : BinaryCheckedPrimitiveRule .implies Ty.content Ty.content
    | subtract : BinaryCheckedPrimitiveRule .subtract Ty.number Ty.number
end

def typingRuleImplemented (rule : M2TypingRuleId) : Bool :=
  [ .a0Synth, .a0Check, .a0TNatural, .a0TVariable,
    .a0TLambdaPure, .a0TLambdaEffectful, .a0TBindReference,
    .a0TCheckSynth, .a0TContext, .a0TVague,
    .a0TReferReference, .a0TReferMember, .a0TSelectExactly,
    .b1TSelectAtLeast, .b1TSelectAllBut, .a0TListCheck,
    .a0TApplyPure, .a0TApplyEffectful, .a0TApplyClauseContent,
    .m2TPredTermApply, .m2TLexicalRow, .m2TString,
    .a0TSpeaker, .a0TAudience, .a0TThresholdKind, .a0TTop,
    .a0TAnd, .b1TImplication, .b1TNegation, .a0TEquality,
    .b1TAmong, .b1TAddition, .a0TStateClause ].contains rule

def implementedTypingRuleRecords : List M2TypingRuleRecord :=
  m2TypingRuleRecords.filter fun record => typingRuleImplemented record.id

def unsupportedTypingRuleRecords : List M2TypingRuleRecord :=
  m2TypingRuleRecords.filter fun record => !typingRuleImplemented record.id

@[simp] theorem observation_withRule (result : TypingResult)
    (rule : M2TypingRuleId) :
    (result.withRule rule).observation = result.observation := by
  rfl

@[simp] theorem observation_mergeResults (type : Ty)
    (results : List TypingResult) (effects : List Effect)
    (obligations : List Obligation) (rule : M2TypingRuleId) :
    (mergeResults type results effects obligations rule).observation =
      mergeObservations type (results.map TypingResult.observation)
        effects obligations := by
  simp [TypingResult.observation, mergeResults, mergeObservations,
    List.flatMap_map]

end M2
end SmusniPilot
