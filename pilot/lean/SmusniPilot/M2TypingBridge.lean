import Lean
import SmusniPilot.M2TypingJudgment

namespace SmusniPilot
namespace M2

private def SynthCompleteMotive {scope : Nat} (environment : Environment scope)
    (term : Term scope) (observation : TypingObservation)
    (_ : SynthJudgment environment term observation) : Prop :=
  ∃ result, synth environment term = .ok result ∧ result.observation = observation

private def CheckCompleteMotive {scope : Nat} (environment : Environment scope)
    (term : Term scope) (expected : Ty) (observation : TypingObservation)
    (_ : CheckJudgment environment term expected observation) : Prop :=
  ∃ result, check environment term expected = .ok result ∧
    result.observation = observation

private def ApplyCompleteMotive {scope : Nat} (environment : Environment scope)
    (functionObservation : TypingObservation) (arguments : TermList scope)
    (observation : TypingObservation)
    (_ : ApplyJudgment environment functionObservation arguments observation) : Prop :=
  ∀ functionResult, functionResult.observation = functionObservation →
    ∃ result, applyFunction environment functionResult arguments = .ok result ∧
      result.observation = observation

private def SynthArgumentsCompleteMotive {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope)
    (observations : List TypingObservation)
    (_ : SynthArgumentsJudgment environment arguments observations) : Prop :=
  ∃ results, synthPositionalList environment arguments = .ok results ∧
    results.map TypingResult.observation = observations

private def CheckArgumentsCompleteMotive {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope) (expected : Ty)
    (observations : List TypingObservation)
    (_ : CheckArgumentsJudgment environment arguments expected observations) : Prop :=
  ∃ results, checkPositionalList environment arguments expected = .ok results ∧
    results.map TypingResult.observation = observations

private def ValueArgumentsCompleteMotive {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope)
    (observations : List TypingObservation)
    (_ : ValueArgumentsJudgment environment arguments observations) : Prop :=
  ∃ results, synthValueOperands environment arguments = .ok results ∧
    results.map TypingResult.observation = observations

private def PredArgumentsCompleteMotive {scope : Nat}
    (environment : Environment scope) (arguments : TermList scope)
    (observations : List TypingObservation) (ordinary : Nat) (eventFilled : Bool)
    (_ : PredArgumentsJudgment environment arguments observations ordinary eventFilled) :
    Prop :=
  ∃ results, predTermArgumentResults environment arguments =
      .ok (results, ordinary, eventFilled) ∧
    results.map TypingResult.observation = observations

private def LexicalArgumentsCompleteMotive {scope : Nat}
    (environment : Environment scope) (row : M2LexicalRowRecord)
    (arguments : TermList scope) (seen : List String)
    (observations : List TypingObservation) (ordinary : Nat) (eventFilled : Bool)
    (_ : LexicalArgumentsJudgment environment row arguments seen observations
      ordinary eventFilled) : Prop :=
  ordinary ≤ row.ordinaryArity →
    ∃ results, lexicalArgumentResults environment row arguments seen =
        .ok (results, ordinary, eventFilled) ∧
      results.map TypingResult.observation = observations

private def PrimitiveCompleteMotive {scope : Nat}
    (environment : Environment scope) (operator : FirstOrderPrimitive)
    (arguments : TermList scope) (observation : TypingObservation)
    (_ : PrimitiveJudgment environment operator arguments observation) : Prop :=
  ∃ result, synthPrimitive environment operator arguments = .ok result ∧
    result.observation = observation

set_option maxHeartbeats 300000 in
theorem synth_judgment_complete {scope : Nat} {environment : Environment scope}
    {term : Term scope} {observation : TypingObservation}
    (typing : SynthJudgment environment term observation) :
    ∃ result, synth environment term = .ok result ∧
      result.observation = observation := by
  change SynthCompleteMotive environment term observation typing
  induction typing using SynthJudgment.rec
    (motive_2 := CheckCompleteMotive)
    (motive_3 := ApplyCompleteMotive)
    (motive_4 := SynthArgumentsCompleteMotive)
    (motive_5 := CheckArgumentsCompleteMotive)
    (motive_6 := ValueArgumentsCompleteMotive)
    (motive_7 := PredArgumentsCompleteMotive)
    (motive_8 := LexicalArgumentsCompleteMotive)
    (motive_9 := PrimitiveCompleteMotive)
    (motive_10 := fun _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ => True)
  case bound environment index =>
    simp only [SynthCompleteMotive]
    let result : TypingResult := {
      type := environment.bound index
      trace := [.a0TVariable, .a0Synth] }
    exact ⟨result, synth.eq_1 environment index, rfl⟩
  case free environment identity type found =>
    simp only [SynthCompleteMotive]
    let result : TypingResult := {
      type
      trace := [.a0TVariable, .a0Synth] }
    refine ⟨result, ?_, rfl⟩
    rw [synth.eq_2, found]
    rfl
  case natural environment value =>
    simp only [SynthCompleteMotive]
    let result : TypingResult := {
      type := Ty.natural
      trace := [.a0TNatural, .a0Synth] }
    exact ⟨result, synth.eq_3 environment value, rfl⟩
  case string environment value =>
    simp only [SynthCompleteMotive]
    let result : TypingResult := {
      type := Ty.text
      trace := [.m2TString, .a0Synth] }
    exact ⟨result, synth.eq_4 environment value, rfl⟩
  case lambda environment binderType body bodyObservation bodyTyping bodyIH =>
    simp only [SynthCompleteMotive] at bodyIH ⊢
    rcases bodyIH with ⟨bodyResult, bodySuccess, bodyAgreement⟩
    cases bodyAgreement
    let result : TypingResult := {
      type := .function (!bodyResult.effects.isEmpty) [binderType] bodyResult.type
      obligations := bodyResult.obligations
      trace := bodyResult.trace ++ [
        if !bodyResult.effects.isEmpty then .a0TLambdaEffectful else .a0TLambdaPure,
        .a0Synth] }
    refine ⟨result, ?_, rfl⟩
    rw [synth.eq_6, bodySuccess]
    rfl
  case bindReference environment binderType computation body computationObservation
      bodyObservation computationTyping bodyTyping computationIH bodyIH =>
    simp only [CheckCompleteMotive] at computationIH
    simp only [SynthCompleteMotive] at bodyIH ⊢
    rcases computationIH with
      ⟨computationResult, computationSuccess, computationAgreement⟩
    rcases bodyIH with ⟨bodyResult, bodySuccess, bodyAgreement⟩
    cases computationAgreement
    cases bodyAgreement
    let result := (mergeResults bodyResult.type [computationResult, bodyResult]
      [] [] .a0TBindReference).withRule .a0Synth
    refine ⟨result, ?_, rfl⟩
    rw [synth.eq_7, bodySuccess, computationSuccess]
    rfl
  case application environment function arguments functionObservation resultObservation
      functionTyping applicationTyping functionIH applicationIH =>
    simp only [SynthCompleteMotive] at functionIH
    simp only [ApplyCompleteMotive] at applicationIH
    simp only [SynthCompleteMotive]
    rcases functionIH with ⟨functionResult, functionSuccess, functionAgreement⟩
    rcases applicationIH functionResult functionAgreement with
      ⟨result, applicationSuccess, resultAgreement⟩
    exact ⟨result, by rw [synth.eq_8, functionSuccess]; exact applicationSuccess,
      resultAgreement⟩
  case lexicalDeclared environment head arguments type resultObservation found
      applicationTyping applicationIH =>
    simp only [ApplyCompleteMotive] at applicationIH
    simp only [SynthCompleteMotive]
    let functionResult : TypingResult := { type }
    rcases applicationIH functionResult rfl with
      ⟨result, applicationSuccess, resultAgreement⟩
    refine ⟨result, ?_, resultAgreement⟩
    rw [synth.eq_9]
    unfold synthLexical
    rw [found]
    exact applicationSuccess
  case lexicalRow environment head arguments row observations ordinary eventFilled
      notDeclared found argumentsTyping withinRow argumentsIH =>
    simp only [LexicalArgumentsCompleteMotive] at argumentsIH
    simp only [SynthCompleteMotive]
    rcases argumentsIH withinRow with ⟨results, argumentsSuccess, resultsAgreement⟩
    cases resultsAgreement
    let result := (mergeResults
      (if ordinary == row.ordinaryArity &&
          (row.eventMode == .holdingState || eventFilled)
        then Ty.content else lexicalRowType row)
      results [] [] .m2TLexicalRow).withRule .a0Synth
    refine ⟨result, ?_, ?_⟩
    · simp [synth.eq_9, synthLexical, notDeclared, found, argumentsSuccess,
        result]
    · rw [observation_withRule, observation_mergeResults]
  case primitive environment operator arguments resultObservation primitiveTyping primitiveIH =>
    simp only [PrimitiveCompleteMotive] at primitiveIH
    simp only [SynthCompleteMotive]
    rcases primitiveIH with ⟨result, success, agreement⟩
    exact ⟨result, by rw [synth.eq_12, success], agreement⟩
  case fromSynth environment checked expected resultObservation synthesis compatible
      synthesisIH =>
    simp only [SynthCompleteMotive] at synthesisIH
    simp only [CheckCompleteMotive]
    rcases synthesisIH with ⟨raw, synthSuccess, agreement⟩
    cases agreement
    let result : TypingResult := { raw with
      trace := raw.trace ++ [.a0TCheckSynth, .a0Check] }
    have compatibleRaw : Ty.compatible raw.type expected = true := compatible
    refine ⟨result, ?_, rfl⟩
    rw [check.eq_1, synthSuccess]
    simp [compatibleRaw]
    rfl
  case context environment site arguments inner observations argumentsTyping argumentsIH =>
    simp only [ValueArgumentsCompleteMotive] at argumentsIH
    simp only [CheckCompleteMotive]
    rcases argumentsIH with ⟨results, argumentsSuccess, observationsAgreement⟩
    cases observationsAgreement
    let result := (mergeResults (Ty.refComp inner) results [.context] []
      .a0TContext).withRule .a0Check
    refine ⟨result, ?_, ?_⟩
    · simp [check.eq_1, synth.eq_10, checkExpected.eq_1,
        expectedCheckClause_context,
        argumentsSuccess, result, failure]
    · rw [observation_withRule, observation_mergeResults]
  case vague environment site constraint inner propertyObservation propertyTyping
      propertyType pure propertyIH =>
    simp only [SynthCompleteMotive] at propertyIH
    simp only [CheckCompleteMotive]
    rcases propertyIH with ⟨property, propertySuccess, agreement⟩
    cases agreement
    let result := (mergeResults (Ty.refComp inner) [property] [.context] []
      .a0TVague).withRule .a0Check
    have propertyTypeRaw : property.type = Ty.pureFn [inner] Ty.content := propertyType
    have pureRaw : property.effects = [] := pure
    have propertyTypeSelf :
        Ty.pureFn [inner] Ty.content == Ty.pureFn [inner] Ty.content :=
      Ty.beq_self _
    refine ⟨result, ?_, ?_⟩
    · simp [check.eq_1, synth.eq_11, checkExpected.eq_2,
        expectedCheckClause_vague, Ty.asUnary_refComp,
        propertySuccess, propertyTypeRaw, pureRaw, isPure, result, failure,
        TypingResult.observation, instBEqTy, Ty.beq, Ty.listBeq,
        propertyTypeSelf, beq_self_eq_true]
    · rw [observation_withRule, observation_mergeResults]
      simp [mergeObservations, TypingResult.observation]
  case referReference environment property inner propertyObservation propertyTyping
      propertyType propertyIH =>
    simp only [SynthCompleteMotive] at propertyIH
    simp only [CheckCompleteMotive]
    rcases propertyIH with ⟨propertyResult, propertySuccess, agreement⟩
    cases agreement
    rcases propertyType with effectfulType | pureType
    · let result := (mergeResults (Ty.refComp (Ty.referents inner)) [propertyResult]
        [.effectfulCall, .refer] [] .a0TReferReference).withRule .a0Check
      have effectfulTypeRaw : propertyResult.type =
          Ty.effectfulFn [Ty.referents inner] Ty.content := effectfulType
      simp only [Ty.effectfulFn, Ty.referents, Ty.content, Ty.named0] at effectfulTypeRaw
      have effectfulTypeSelf :
          Ty.effectfulFn [Ty.referents inner] Ty.content ==
            Ty.effectfulFn [Ty.referents inner] Ty.content := Ty.beq_self _
      have effectfulTypeSelfRaw :
          (Ty.function true [Ty.named .typeFormReferents [inner]]
            (.named .typeContent []) ==
           Ty.function true [Ty.named .typeFormReferents [inner]]
            (.named .typeContent [])) = true := Ty.beq_self _
      refine ⟨result, ?_, ?_⟩
      · simp [check.eq_1, synth.eq_12, synthPrimitive, checkExpected.eq_3,
          expectedCheckClause_refer, Ty.asUnary_refComp,
          judgmentTermList, propertySuccess,
          effectfulTypeRaw, result, failure, TypingResult.observation,
          Ty.effectfulFn, Ty.pureFn, Ty.referents, Ty.content, Ty.named0,
          Ty.asUnary_referents, Ty.asUnary_referents_raw, instBEqTy,
          Ty.beq, Ty.listBeq, effectfulTypeSelf,
          beq_self_eq_true]
      · rw [observation_withRule, observation_mergeResults]
        simp [TypingResult.observation, effectfulTypeRaw, effectfulTypeSelf,
          effectfulTypeSelfRaw,
          Ty.effectfulFn, Ty.referents, Ty.content, Ty.named0,
          Ty.pureFn, instBEqTy,
          Ty.beq, Ty.listBeq]
    · let result := (mergeResults (Ty.refComp (Ty.referents inner)) [propertyResult]
        [.refer] [] .a0TReferReference).withRule .a0Check
      have pureTypeRaw : propertyResult.type =
          Ty.pureFn [Ty.referents inner] Ty.content := pureType
      simp only [Ty.pureFn, Ty.referents, Ty.content, Ty.named0] at pureTypeRaw
      have pureNotEffectful :
          (Ty.pureFn [Ty.referents inner] Ty.content ==
            Ty.effectfulFn [Ty.referents inner] Ty.content) = false := rfl
      have pureNotEffectfulRaw :
          (Ty.function false [Ty.referents inner] Ty.content ==
            Ty.function true [Ty.referents inner] Ty.content) = false := rfl
      have pureNotEffectfulRawExpanded :
          (Ty.function false [Ty.named .typeFormReferents [inner]]
            (.named .typeContent []) ==
           Ty.function true [Ty.named .typeFormReferents [inner]]
            (.named .typeContent [])) = false := rfl
      refine ⟨result, ?_, ?_⟩
      · simp [check.eq_1, synth.eq_12, synthPrimitive, checkExpected.eq_3,
          expectedCheckClause_refer, Ty.asUnary_refComp,
          judgmentTermList, propertySuccess,
          pureTypeRaw, result, failure, TypingResult.observation,
          Ty.effectfulFn, Ty.pureFn, Ty.referents, Ty.content, Ty.named0,
          Ty.asUnary_referents, Ty.asUnary_referents_raw, instBEqTy,
          Ty.beq, Ty.listBeq,
          pureNotEffectful, pureNotEffectfulRaw,
          beq_self_eq_true]
      · rw [observation_withRule, observation_mergeResults]
        simp [TypingResult.observation, pureTypeRaw, pureNotEffectful,
          pureNotEffectfulRaw, pureNotEffectfulRawExpanded,
          Ty.effectfulFn, Ty.referents, Ty.content, Ty.named0,
          Ty.pureFn, instBEqTy,
          Ty.beq, Ty.listBeq]
  case referMember environment property inner propertyObservation propertyTyping
      propertyType pure notReferenceDomain memberCompatible propertyIH =>
    simp only [SynthCompleteMotive] at propertyIH
    simp only [CheckCompleteMotive]
    rcases propertyIH with ⟨propertyResult, propertySuccess, agreement⟩
    cases agreement
    let result := (mergeResults (Ty.refComp (Ty.referents inner)) [propertyResult]
      [.refer] [] .a0TReferMember).withRule .a0Check
    have propertyTypeRaw : propertyResult.type = Ty.pureFn [inner] Ty.content :=
      propertyType
    have pureRaw : propertyResult.effects = [] := pure
    have propertyTypeSelf : Ty.pureFn [inner] Ty.content ==
        Ty.pureFn [inner] Ty.content := Ty.beq_self _
    have propertyTypeSelfRaw :
        (Ty.function false [inner] (.named .typeContent []) ==
          Ty.function false [inner] (.named .typeContent [])) = true := Ty.beq_self _
    have notReferenceDomainRaw :
        (inner == Ty.named .typeFormReferents [inner]) = false := by
      simpa [Ty.referents] using notReferenceDomain
    refine ⟨result, ?_, ?_⟩
    · simp [check.eq_1, synth.eq_12, synthPrimitive, checkExpected.eq_3,
        expectedCheckClause_refer, Ty.asUnary_refComp,
        judgmentTermList, propertySuccess,
        propertyTypeRaw, pureRaw, isPure, result, failure, TypingResult.observation,
        Ty.referents, Ty.content, Ty.compatible, instBEqTy, Ty.beq,
        Ty.pureFn, Ty.named0, Ty.listBeq, propertyTypeSelf, propertyTypeSelfRaw,
        notReferenceDomain, notReferenceDomainRaw, memberCompatible,
        Ty.asUnary_referents, Ty.asUnary_referents_raw, beq_self_eq_true]
    · rw [observation_withRule, observation_mergeResults]
      simp [mergeObservations, TypingResult.observation]
  case «local» environment body expected bodyObservation bodyTyping bodyIH =>
    simp only [CheckCompleteMotive] at bodyIH ⊢
    rcases bodyIH with ⟨bodyResult, bodySuccess, agreement⟩
    cases agreement
    let result := (mergeResults (Ty.refComp expected) [bodyResult] [] []
      .m2TLocal).withRule .a0Check
    refine ⟨result, ?_, ?_⟩
    · rw [check.eq_1, synth.eq_12]
      simp only [synthPrimitive, failure]
      simp only [judgmentTermList]
      rw [checkExpected.eq_5]
      simp [expectedCheckClause_local_raw, bodySuccess, result]
    · rw [observation_withRule, observation_mergeResults]
      simp [mergeObservations, TypingResult.observation]
  case list environment arguments itemType observations itemsTyping itemsIH =>
    simp only [CheckArgumentsCompleteMotive] at itemsIH
    simp only [CheckCompleteMotive]
    rcases itemsIH with ⟨results, itemsSuccess, agreement⟩
    cases agreement
    let result := (mergeResults (Ty.list itemType) results [] []
      .a0TListCheck).withRule .a0Check
    refine ⟨result, ?_, ?_⟩
    · simp [check.eq_1, synth.eq_12, synthPrimitive, checkExpected.eq_9,
        expectedCheckClause_list,
        Ty.list, itemsSuccess, result, failure]
    · rw [observation_withRule, observation_mergeResults]
  case select environment operator count property inner countObservation
      propertyObservation selected countTyping floor propertyTyping countIH propertyIH =>
    simp only [CheckCompleteMotive] at countIH propertyIH ⊢
    rcases countIH with ⟨countResult, countSuccess, countAgreement⟩
    rcases propertyIH with ⟨propertyResult, propertySuccess, propertyAgreement⟩
    cases countAgreement
    cases propertyAgreement
    rcases selected with rfl | selected
    · have positive : provablyPositive count = true := by
        rcases floor with impossible | positive
        · contradiction
        · exact positive
      let result := (mergeResults (Ty.refComp (Ty.referents inner))
        [countResult, propertyResult] [.refer] [] .a0TSelectExactly).withRule .a0Check
      refine ⟨result, ?_, ?_⟩
      · rw [check.eq_1, synth.eq_12]
        simp only [synthPrimitive, failure, judgmentTermList]
        simp [checkExpected.eq_8, expectedCheckClause_selectExactly_raw,
          Ty.asUnary_refComp, Ty.asUnary_referents, checkReferencePrimitive,
          countSuccess, propertySuccess, positive, result, failure]
      · rw [observation_withRule, observation_mergeResults]
        rfl
    · rcases selected with rfl | rfl
      · have positive : provablyPositive count = true := by
          rcases floor with impossible | positive
          · contradiction
          · exact positive
        let result := (mergeResults (Ty.refComp (Ty.referents inner))
          [countResult, propertyResult] [.refer] [] .b1TSelectAtLeast).withRule .a0Check
        refine ⟨result, ?_, ?_⟩
        · rw [check.eq_1, synth.eq_12]
          simp only [synthPrimitive, failure, judgmentTermList]
          simp [checkExpected.eq_8, expectedCheckClause_selectAtLeast_raw,
            Ty.asUnary_refComp, Ty.asUnary_referents, checkReferencePrimitive,
            countSuccess, propertySuccess, positive, result, failure]
        · rw [observation_withRule, observation_mergeResults]
          rfl
      · let result := (mergeResults (Ty.refComp (Ty.referents inner))
          [countResult, propertyResult] [.refer] [] .b1TSelectAllBut).withRule .a0Check
        refine ⟨result, ?_, ?_⟩
        · rw [check.eq_1, synth.eq_12]
          simp only [synthPrimitive, failure, judgmentTermList]
          simp [checkExpected.eq_8, expectedCheckClause_selectAllBut_raw,
            Ty.asUnary_refComp, Ty.asUnary_referents, checkReferencePrimitive,
            countSuccess, propertySuccess, floor, result, failure]
        · rw [observation_withRule, observation_mergeResults]
          rfl
  case functionZero environment effectful outputType functionObservation functionType =>
    simp only [ApplyCompleteMotive]
    intro functionResult functionAgreement
    cases functionAgreement
    have rawType : functionResult.type = .function effectful [] outputType := functionType
    let output := (mergeResults outputType [functionResult]
      (if effectful then [.effectfulCall] else []) []
      (if effectful then .a0TApplyEffectful else .a0TApplyPure)).withRule .a0Synth
    refine ⟨output, ?_, ?_⟩
    · unfold applyFunction
      rw [rawType]
      rfl
    · rw [observation_withRule, observation_mergeResults]
      rfl
  case functionPartialZero environment effectful parameters outputType nonempty
      functionObservation functionType =>
    simp only [ApplyCompleteMotive]
    intro functionResult functionAgreement
    cases functionAgreement
    have rawType : functionResult.type = .function effectful parameters outputType :=
      functionType
    let output := (mergeResults (.function effectful parameters outputType)
      [functionResult] (if effectful then [.effectfulCall] else []) []
      (if effectful then .a0TApplyEffectful else .a0TApplyPure)).withRule .a0Synth
    refine ⟨output, ?_, ?_⟩
    · unfold applyFunction
      rw [rawType]
      simp [nonempty]
      rfl
    · rw [observation_withRule, observation_mergeResults]
      rfl
  case functionLast environment effectful parameter remaining outputType
      functionObservation argumentObservation argument functionType argumentTyping
      argumentIH =>
    simp only [CheckCompleteMotive] at argumentIH
    simp only [ApplyCompleteMotive]
    intro functionResult functionAgreement
    cases functionAgreement
    rcases argumentIH with ⟨argumentResult, argumentSuccess, argumentAgreement⟩
    cases argumentAgreement
    have rawType : functionResult.type =
        .function effectful (parameter :: remaining) outputType := functionType
    let resultType := if remaining.isEmpty then outputType
      else .function effectful remaining outputType
    let output := (mergeResults resultType [functionResult, argumentResult]
      (if effectful then [.effectfulCall] else []) []
      (if effectful then .a0TApplyEffectful else .a0TApplyPure)).withRule .a0Synth
    refine ⟨output, ?_, ?_⟩
    · unfold applyFunction
      rw [rawType]
      simp only
      rw [argumentSuccess]
      rfl
    · rw [observation_withRule, observation_mergeResults]
      rfl
  case functionMore environment effectful parameter remaining outputType
      functionObservation argumentObservation intermediateObservation finalObservation
      argument tail tailNonempty functionType argumentTyping intermediateEquation
      tailTyping argumentIH tailIH =>
    simp only [CheckCompleteMotive] at argumentIH
    simp only [ApplyCompleteMotive] at tailIH ⊢
    intro functionResult functionAgreement
    cases functionAgreement
    rcases argumentIH with ⟨argumentResult, argumentSuccess, argumentAgreement⟩
    cases argumentAgreement
    have rawType : functionResult.type =
        .function effectful (parameter :: remaining) outputType := functionType
    let resultType := if remaining.isEmpty then outputType
      else .function effectful remaining outputType
    let intermediate := (mergeResults resultType [functionResult, argumentResult]
      (if effectful then [.effectfulCall] else []) []
      (if effectful then .a0TApplyEffectful else .a0TApplyPure)).withRule .a0Synth
    have intermediateAgreement : intermediate.observation = intermediateObservation := by
      rw [observation_withRule, observation_mergeResults]
      exact intermediateEquation.symm
    rcases tailIH intermediate intermediateAgreement with
      ⟨finalResult, tailSuccess, finalAgreement⟩
    refine ⟨finalResult, ?_, finalAgreement⟩
    unfold applyFunction
    rw [rawType]
    cases tail with
    | nil => contradiction
    | positional next rest =>
        simp only
        rw [argumentSuccess]
        exact tailSuccess
    | labelled label next rest =>
        simp only
        rw [argumentSuccess]
        exact tailSuccess
  case clauseContent environment functionObservation argumentObservation argument
      functionType argumentTyping argumentIH =>
    simp only [CheckCompleteMotive] at argumentIH
    simp only [ApplyCompleteMotive]
    intro functionResult functionAgreement
    cases functionAgreement
    rcases argumentIH with ⟨argumentResult, argumentSuccess, argumentAgreement⟩
    cases argumentAgreement
    have rawType : functionResult.type = Ty.clauseContent := functionType
    let output := (mergeResults Ty.content [functionResult, argumentResult] [] []
      .a0TApplyClauseContent).withRule .a0Synth
    refine ⟨output, ?_, ?_⟩
    · unfold applyFunction
      rw [rawType]
      simp only
      rw [argumentSuccess]
      rfl
    · rw [observation_withRule, observation_mergeResults]
      rfl
  case predTerm environment functionObservation arguments row ordinary eventRequired
      observations ordinaryFilled eventFilled functionType shape argumentsTyping
      withinRow eventWithinRow rowCondition noBadRow argumentsIH =>
    simp only [PredArgumentsCompleteMotive] at argumentsIH
    simp only [ApplyCompleteMotive]
    intro functionResult functionAgreement
    cases functionAgreement
    rcases argumentsIH with ⟨results, argumentsSuccess, resultsAgreement⟩
    cases resultsAgreement
    have rawType : functionResult.type = Ty.predTerm row := functionType
    let outputType := if ordinaryFilled == ordinary && (!eventRequired || eventFilled)
      then Ty.content else Ty.predTerm (Ty.residualRow
        (ordinary - ordinaryFilled) (eventRequired && !eventFilled))
    let output := (mergeResults outputType (functionResult :: results) [] []
      .m2TPredTermApply).withRule .a0Synth
    refine ⟨output, ?_, ?_⟩
    · unfold applyFunction
      rw [rawType]
      simp [Ty.predTerm, Ty.clauseContent, predTermShape]
      rw [shape, argumentsSuccess]
      simp only [except_ok_bind_judgment]
      rw [if_neg noBadRow]
      simpa [output, outputType, Ty.predTerm, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true]
    · rw [observation_withRule, observation_mergeResults]
      rfl
  case constant environment operator resultObservation rule manifest ruleIH =>
    simp only [PrimitiveCompleteMotive]
    cases rule <;> simp only [synthPrimitive] <;>
      unfold synthPrimitive.constant <;>
      simp [positionalTerms, manifest, mergeResults, TypingResult.observation,
        TypingResult.withRule, failure]
    all_goals rfl
  case binarySynth environment operator first second firstObservation secondObservation
      resultType firstTyping secondTyping rule firstIH secondIH ruleIH =>
    simp only [SynthCompleteMotive] at firstIH secondIH
    simp only [PrimitiveCompleteMotive]
    rcases firstIH with ⟨firstResult, firstSuccess, firstAgreement⟩
    rcases secondIH with ⟨secondResult, secondSuccess, secondAgreement⟩
    cases firstAgreement
    cases secondAgreement
    cases rule <;> simp only [synthPrimitive]
    case addition =>
      unfold synthPrimitive.binarySynth
      simp_all [judgmentTermList, mergeResults, TypingResult.observation,
        TypingResult.withRule, failure, Ty.numberJoin]
      simp [mergeObservations, TypingResult.observation]
    case equality =>
      unfold synthPrimitive.binarySynth
      simp_all [judgmentTermList, mergeResults, TypingResult.observation,
        TypingResult.withRule, failure, Ty.equalityType]
      simp [mergeObservations, TypingResult.observation]
    case among =>
      unfold synthPrimitive.referenceBinary
      simp_all [judgmentTermList, mergeResults, TypingResult.observation,
        TypingResult.withRule, failure, Ty.referenceCompatible]
      simp [mergeObservations, TypingResult.observation]
  case unaryCheck environment operator checked expected resultType resultObservation
      typing rule typingIH ruleIH =>
    simp only [CheckCompleteMotive] at typingIH
    simp only [PrimitiveCompleteMotive]
    rcases typingIH with ⟨checkedResult, checkSuccess, checkAgreement⟩
    cases checkAgreement
    cases rule <;> try simp only [synthPrimitive] <;>
      try unfold synthPrimitive.unaryCheck <;>
      simp_all [expectArity,
        positionalOperands, judgmentTermList,
        mergeResults, mergeObservations, TypingResult.observation,
        TypingResult.withRule, failure]
    all_goals
      simp [synthPrimitive, judgmentTermList, checkSuccess, mergeResults,
        mergeObservations, TypingResult.observation, TypingResult.withRule, failure]
  case binaryCheck environment operator first second expected resultType firstObservation
      secondObservation firstTyping secondTyping rule firstIH secondIH ruleIH =>
    simp only [CheckCompleteMotive] at firstIH secondIH
    simp only [PrimitiveCompleteMotive]
    rcases firstIH with ⟨firstResult, firstSuccess, firstAgreement⟩
    rcases secondIH with ⟨secondResult, secondSuccess, secondAgreement⟩
    cases firstAgreement
    cases secondAgreement
    cases rule <;> try simp only [synthPrimitive] <;>
      try unfold synthPrimitive.binaryCheck <;>
      simp_all [expectArity,
        positionalOperands, judgmentTermList,
        mergeResults, mergeObservations, TypingResult.observation,
        TypingResult.withRule, failure]
    all_goals
      simp [synthPrimitive, judgmentTermList, firstSuccess, secondSuccess,
        mergeResults, mergeObservations, TypingResult.observation,
        TypingResult.withRule, failure]
  case top environment =>
    simp only [PrimitiveCompleteMotive]
    simp [synthPrimitive, judgmentTermList, mergeResults,
      TypingResult.observation, TypingResult.withRule, failure]
  case and environment first second firstObservation secondObservation firstTyping
      secondTyping firstIH secondIH =>
    simp only [CheckCompleteMotive] at firstIH secondIH
    simp only [PrimitiveCompleteMotive]
    rcases firstIH with ⟨firstResult, firstSuccess, firstAgreement⟩
    rcases secondIH with ⟨secondResult, secondSuccess, secondAgreement⟩
    cases firstAgreement
    cases secondAgreement
    simp [synthPrimitive, synthPrimitive.binaryCheck, expectArity,
      positionalOperands, judgmentTermList,
      firstSuccess, secondSuccess, mergeResults, TypingResult.observation,
      TypingResult.withRule, mergeObservations, failure]
  next environment =>
    simp only [SynthArgumentsCompleteMotive]
    exact ⟨[], synthPositionalList.eq_1 environment, rfl⟩
  next environment head tail headObservation tailObservations headTyping tailTyping
      headIH tailIH =>
    simp only [SynthCompleteMotive] at headIH
    simp only [SynthArgumentsCompleteMotive] at tailIH ⊢
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · simp [synthPositionalList.eq_3, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment =>
    intro expected
    simp only [CheckArgumentsCompleteMotive]
    exact ⟨[], checkPositionalList.eq_1 environment expected, rfl⟩
  next environment head tail expected headObservation tailObservations headTyping
      tailTyping headIH =>
    intro tailIH
    simp only [CheckCompleteMotive] at headIH
    simp only [CheckArgumentsCompleteMotive] at tailIH ⊢
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · simp [checkPositionalList.eq_3, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment =>
    simp only [ValueArgumentsCompleteMotive]
    exact ⟨[], synthValueOperands.eq_1 environment, rfl⟩
  next environment head tail headObservation tailObservations value headTyping
      tailTyping headIH =>
    intro tailIH
    simp only [SynthCompleteMotive] at headIH
    simp only [ValueArgumentsCompleteMotive] at tailIH ⊢
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · simp [synthValueOperands.eq_3, value, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment =>
    simp only [PredArgumentsCompleteMotive]
    exact ⟨[], predTermArgumentResults.eq_1 environment, rfl⟩
  next environment head tail headObservation tailObservations ordinary eventFilled
      headTyping tailTyping =>
    intro headIH tailIH
    simp only [SynthCompleteMotive] at headIH
    simp only [PredArgumentsCompleteMotive] at tailIH ⊢
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · simp [predTermArgumentResults.eq_2, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment head tail headObservation tailObservations ordinary headTyping
      tailTyping headIH tailIH =>
    simp only [CheckCompleteMotive] at headIH
    simp only [PredArgumentsCompleteMotive] at tailIH ⊢
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · simp [predTermArgumentResults.eq_3, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment label notEvent head tail headObservation tailObservations ordinary
      eventFilled headTyping tailTyping headIH tailIH =>
    simp only [SynthCompleteMotive] at headIH
    simp only [PredArgumentsCompleteMotive] at tailIH ⊢
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · simp [predTermArgumentResults.eq_4, notEvent, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment =>
    intro row seen
    simp only [LexicalArgumentsCompleteMotive]
    intro _within
    exact ⟨[], lexicalArgumentResults.eq_1 environment row seen, rfl⟩
  next environment row head tail seen headObservation tailObservations ordinary
      eventFilled =>
    intro headTyping tailTyping headIH tailIH
    simp only [SynthCompleteMotive] at headIH
    simp only [LexicalArgumentsCompleteMotive] at tailIH ⊢
    intro withinTotal
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH (by omega) with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · have withinOrdinary : ¬row.ordinaryArity < ordinary + 1 := by omega
      simp [lexicalArgumentResults.eq_2, headSuccess, tailSuccess, withinOrdinary]
    · simp [headAgreement, tailAgreement]
  next environment row head tail seen fresh direct headObservation tailObservations
      ordinary =>
    intro headTyping tailTyping headIH tailIH
    simp only [CheckCompleteMotive] at headIH
    simp only [LexicalArgumentsCompleteMotive] at tailIH ⊢
    intro withinTotal
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH withinTotal with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · have freshNotMem : ":Eventuality" ∉ seen := by simpa using fresh
      rw [lexicalArgumentResults.eq_3]
      simp [freshNotMem, direct, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  next environment row label head tail seen fresh notEvent place decoded positive
      within headObservation =>
    intro tailObservations ordinary eventFilled headTyping tailTyping headIH tailIH
    simp only [SynthCompleteMotive] at headIH
    simp only [LexicalArgumentsCompleteMotive] at tailIH ⊢
    intro withinTotal
    rcases headIH with ⟨headResult, headSuccess, headAgreement⟩
    rcases tailIH (by omega) with ⟨tailResults, tailSuccess, tailAgreement⟩
    refine ⟨headResult :: tailResults, ?_, ?_⟩
    · have freshNotMem : label ∉ seen := by simpa using fresh
      have decoded' : (label.drop 1).copy.toNat? = some place := by simpa using decoded
      have nonzero : place ≠ 0 := by omega
      have placeWithin : ¬row.ordinaryArity < place := by omega
      have ordinaryWithin : ¬row.ordinaryArity < ordinary + 1 := by omega
      simp [lexicalArgumentResults.eq_3, freshNotMem, notEvent, decoded', nonzero,
        placeWithin, ordinaryWithin, headSuccess, tailSuccess]
    · simp [headAgreement, tailAgreement]
  all_goals trivial

open Lean Meta Elab Tactic in
elab "exact_check_companion " typingSyntax:term : tactic => do
  withMainContext do
    let typing ← elabTerm typingSyntax none
    let declaration ← getConstInfo ``synth_judgment_complete
    let value ← match declaration with
      | .thmInfo information => pure information.value
      | _ => throwError "synthesis completeness is not a theorem"
    let mut body := value.consumeMData
    for _ in [0:5] do
      match body with
      | .lam _ _ next _ => body := next.consumeMData
      | _ => throwError "unexpected synthesis completeness proof shape"
    let idArguments := body.getAppArgs
    if idArguments.isEmpty then
      throwError "unexpected outer completeness proof shape"
    body := idArguments[idArguments.size - 1]!
    let betaFunction := body.getAppFn
    let betaArguments := body.getAppArgs
    match betaFunction with
    | .lam _ _ lambdaBody _ =>
        if betaArguments.isEmpty then
          throwError "empty mutual recursor beta application"
        let reduced := lambdaBody.instantiate1 betaArguments[0]!
        body := mkAppN reduced (betaArguments.extract 1 betaArguments.size)
    | _ => throwError "unexpected mutual recursor beta function"
    let arguments := body.getAppArgs
    if arguments.size < 5 then
      throwError "mutual completeness recursor has too few arguments"
    let shared := arguments.extract 0 (arguments.size - 5)
    for argument in shared do
      if argument.hasLooseBVars then
        throwError "mutual completeness handler unexpectedly captures root indices"
    let typingType ← whnf (← inferType typing)
    let indices := typingType.getAppArgs
    if indices.size != 5 then
      throwError "checking judgment has unexpected index arity"
    let recursor ← mkConstWithFreshMVarLevels ``CheckJudgment.rec
    let proof := mkAppN recursor (shared ++ indices ++ #[typing])
    let goal ← getMainGoal
    let goalType ← goal.getType
    let proofType ← inferType proof
    unless ← isDefEq proofType goalType do
      throwError "checking companion type mismatch\nproof: {proofType}\ngoal: {goalType}"
    closeMainGoalUsing `exact_check_companion fun _ _ => pure proof

theorem check_judgment_complete {scope : Nat} {environment : Environment scope}
    {term : Term scope} {expected : Ty} {observation : TypingObservation}
    (typing : CheckJudgment environment term expected observation) :
    ∃ result, checkBidirectional environment term expected = .ok result ∧
      result.observation = observation := by
  change CheckCompleteMotive environment term expected observation typing
  exact_check_companion typing

def SynthSupported {scope : Nat} (environment : Environment scope)
    (term : Term scope) : Prop := ∃ observation, SynthJudgment environment term observation

def CheckSupported {scope : Nat} (environment : Environment scope)
    (term : Term scope) (expected : Ty) : Prop :=
  ∃ observation, CheckJudgment environment term expected observation

theorem synthesis_observation_unique {scope : Nat} {environment : Environment scope}
    {term : Term scope} {first second : TypingObservation}
    (firstTyping : SynthJudgment environment term first)
    (secondTyping : SynthJudgment environment term second) : first = second := by
  rcases synth_judgment_complete firstTyping with
    ⟨firstResult, firstSuccess, firstAgreement⟩
  rcases synth_judgment_complete secondTyping with
    ⟨secondResult, secondSuccess, secondAgreement⟩
  rw [firstSuccess] at secondSuccess
  cases secondSuccess
  exact firstAgreement.symm.trans secondAgreement

theorem synthesis_type_unique {scope : Nat} {environment : Environment scope}
    {term : Term scope} {first second : TypingObservation}
    (firstTyping : SynthJudgment environment term first)
    (secondTyping : SynthJudgment environment term second) :
    first.type = second.type := by
  rw [synthesis_observation_unique firstTyping secondTyping]

theorem checking_observation_unique {scope : Nat} {environment : Environment scope}
    {term : Term scope} {expected : Ty} {first second : TypingObservation}
    (firstTyping : CheckJudgment environment term expected first)
    (secondTyping : CheckJudgment environment term expected second) : first = second := by
  rcases check_judgment_complete firstTyping with
    ⟨firstResult, firstSuccess, firstAgreement⟩
  rcases check_judgment_complete secondTyping with
    ⟨secondResult, secondSuccess, secondAgreement⟩
  rw [firstSuccess] at secondSuccess
  cases secondSuccess
  exact firstAgreement.symm.trans secondAgreement

theorem synth_characterized_on_supported {scope : Nat}
    {environment : Environment scope} {term : Term scope}
    (supported : SynthSupported environment term) (observation : TypingObservation) :
    (∃ result, synth environment term = .ok result ∧
      result.observation = observation) ↔
      SynthJudgment environment term observation := by
  constructor
  · rintro ⟨result, success, agreement⟩
    rcases supported with ⟨supportedObservation, supportedTyping⟩
    rcases synth_judgment_complete supportedTyping with
      ⟨supportedResult, supportedSuccess, supportedAgreement⟩
    rw [success] at supportedSuccess
    cases supportedSuccess
    have observationAgreement : observation = supportedObservation :=
      agreement.symm.trans supportedAgreement
    simpa [observationAgreement] using supportedTyping
  · exact synth_judgment_complete

theorem checkBidirectional_characterized_on_supported {scope : Nat}
    {environment : Environment scope} {term : Term scope} {expected : Ty}
    (supported : CheckSupported environment term expected)
    (observation : TypingObservation) :
    (∃ result, checkBidirectional environment term expected = .ok result ∧
      result.observation = observation) ↔
      CheckJudgment environment term expected observation := by
  constructor
  · rintro ⟨result, success, agreement⟩
    rcases supported with ⟨supportedObservation, supportedTyping⟩
    rcases check_judgment_complete supportedTyping with
      ⟨supportedResult, supportedSuccess, supportedAgreement⟩
    rw [success] at supportedSuccess
    cases supportedSuccess
    have observationAgreement : observation = supportedObservation :=
      agreement.symm.trans supportedAgreement
    simpa [observationAgreement] using supportedTyping
  · exact check_judgment_complete

inductive CheckPriorityCase {scope : Nat} (environment : Environment scope)
    (term : Term scope) (expected : Ty) : Except TypingError TypingResult → Prop where
  | compatible (actual : TypingResult)
      (synthesis : synth environment term = .ok actual)
      (compatible : Ty.compatible actual.type expected = true) :
      CheckPriorityCase environment term expected (.ok { actual with
        trace := actual.trace ++ [.a0TCheckSynth, .a0Check] })
  | mismatch (actual : TypingResult)
      (synthesis : synth environment term = .ok actual)
      (incompatible : Ty.compatible actual.type expected = false) :
      CheckPriorityCase environment term expected (.error {
        code := "type-mismatch"
        detail := s!"expected {repr expected}, synthesized {repr actual.type}" })
  | expectedOnly (synthError : TypingError)
      (synthesis : synth environment term = .error synthError) :
      CheckPriorityCase environment term expected
        (checkExpected environment term expected synthError)

theorem checkBidirectional_priority_partition {scope : Nat}
    (environment : Environment scope) (term : Term scope) (expected : Ty) :
    CheckPriorityCase environment term expected
      (checkBidirectional environment term expected) := by
  rw [checkBidirectional]
  rw [check.eq_1]
  cases synthesis : synth environment term with
  | error synthError => exact .expectedOnly synthError synthesis
  | ok actual =>
      cases compatible : Ty.compatible actual.type expected with
      | false =>
          simpa [compatible, failure] using
            (CheckPriorityCase.mismatch actual synthesis compatible)
      | true =>
          simpa [compatible] using
            (CheckPriorityCase.compatible actual synthesis compatible)

theorem judgment_wrong_expected_type {scope : Nat}
    {environment : Environment scope} {term : Term scope}
    {observation : TypingObservation} {expected : Ty}
    (typing : SynthJudgment environment term observation)
    (incompatible : Ty.compatible observation.type expected = false) :
    ∃ error, checkBidirectional environment term expected = .error error ∧
      error.code = "type-mismatch" := by
  rcases synth_judgment_complete typing with ⟨result, success, agreement⟩
  have incompatibleRaw : Ty.compatible result.type expected = false := by
    rw [← agreement] at incompatible
    simpa [TypingResult.observation] using incompatible
  refine ⟨{
    code := "type-mismatch"
    detail := s!"expected {repr expected}, synthesized {repr result.type}" }, ?_, rfl⟩
  simp [checkBidirectional, check.eq_1, success, incompatibleRaw, failure]

def PureObservation (observation : TypingObservation) : Prop :=
  observation.effects = []

theorem judgment_purity_characterized {scope : Nat}
    {environment : Environment scope} {term : Term scope}
    {observation : TypingObservation}
    (typing : SynthJudgment environment term observation) :
    ∃ result, synth environment term = .ok result ∧
      (isPure result = true ↔ PureObservation observation) := by
  rcases synth_judgment_complete typing with ⟨result, success, agreement⟩
  refine ⟨result, success, ?_⟩
  cases agreement
  exact purity_classifier_sound_complete result

theorem judgment_category_preserved {scope : Nat}
    {environment : Environment scope} {term : Term scope}
    {observation : TypingObservation}
    (typing : SynthJudgment environment term observation)
    (category : ComputationCategory observation.type) :
    ∃ result, synth environment term = .ok result ∧
      ComputationCategory result.type := by
  rcases synth_judgment_complete typing with ⟨result, success, agreement⟩
  refine ⟨result, success, ?_⟩
  cases agreement
  exact category

theorem judgment_effect_bound {scope : Nat}
    {environment : Environment scope} {term : Term scope}
    {observation : TypingObservation}
    (typing : SynthJudgment environment term observation) :
    ∀ effect, effect ∈ observation.effects → fiveNameEffectBound.contains effect := by
  rcases synth_judgment_complete typing with ⟨result, _success, agreement⟩
  cases agreement
  exact effect_analysis_sound result

def CheckJudgment.IsExpectedOnly {scope : Nat} {environment : Environment scope}
    {term : Term scope} {expected : Ty} {observation : TypingObservation} :
    CheckJudgment environment term expected observation → Prop :=
  fun typing => ¬∃ (synthesis : SynthJudgment environment term observation)
      (compatible : Ty.compatible observation.type expected = true),
    typing = .fromSynth environment term expected observation synthesis compatible

private theorem expected_only_internal_bridge {scope : Nat}
    {environment : Environment scope} {term : Term scope} {expected : Ty}
    {observation : TypingObservation}
    (typing : CheckJudgment environment term expected observation)
    (_expectedOnly : typing.IsExpectedOnly) :
    ∃ result, check environment term expected = .ok result ∧
      result.observation = observation := by
  simpa [checkBidirectional] using check_judgment_complete typing

end M2
end SmusniPilot
