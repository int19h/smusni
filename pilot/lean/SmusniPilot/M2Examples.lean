import SmusniPilot.M2Bundle

namespace SmusniPilot
namespace M2

def TypingError.message (error : TypingError) : String :=
  s!"{error.code}: {error.detail}"

def IO.ofTyping {α : Type} (result : Except TypingError α) : IO α :=
  IO.ofExcept (result.mapError TypingError.message)

def typingExampleSite (role : String) : SiteId :=
  { document := "m2-typing", occurrence := 0, expansionRole := role }

def unseenNaturalObservation : TypingObservation := { type := Ty.natural }

theorem unseen_natural_structural_judgment :
    SynthJudgment Environment.empty (.natural 917) unseenNaturalObservation :=
  .natural Environment.empty 917

theorem unseen_natural_judgment_executes :
    ∃ result, synth Environment.empty (.natural 917) = .ok result ∧
      result.observation = unseenNaturalObservation :=
  synth_judgment_complete unseen_natural_structural_judgment

def nestedPresupposeCondition : Term 0 := .primitive .and .nil

def nestedExpectedContext : Term 0 :=
  .context (typingExampleSite "nested-presuppose") .nil

def nestedExpectedPresuppose : Term 0 := .primitive .presuppose <|
  judgmentTermList [nestedPresupposeCondition, nestedExpectedContext]

def outerExpectedPresuppose : Term 0 := .primitive .presuppose <|
  judgmentTermList [nestedPresupposeCondition, nestedExpectedPresuppose]

def nestedSynthablePresuppose : Term 0 := .primitive .presuppose <|
  judgmentTermList [nestedPresupposeCondition, nestedPresupposeCondition]

def outerSynthablePresuppose : Term 0 := .primitive .presuppose <|
  judgmentTermList [nestedPresupposeCondition, nestedSynthablePresuppose]

theorem nested_expected_presuppose_is_expected_only :
    ExpectedOnlySynthesisForm nestedExpectedPresuppose :=
  .presuppose nestedPresupposeCondition nestedExpectedContext
    (.context (typingExampleSite "nested-presuppose") .nil)

theorem nested_synthable_presuppose_is_not_expected_only :
    ¬ExpectedOnlySynthesisForm nestedSynthablePresuppose := by
  intro form
  have classified := expected_only_classifier_complete form
  simp [nestedSynthablePresuppose, nestedPresupposeCondition,
    judgmentTermList, expectedOnlySynthesisForm] at classified

def nestedExpectedCheckResult : TypingResult := {
  type := Ty.refComp Ty.entity
  effects := [.context, .projective]
  obligations := [
    .presuppose "condition" (Ty.refComp Ty.entity),
    .presuppose "condition" (Ty.refComp Ty.entity)]
  trace := [
    .a0TTop, .a0Synth, .a0TCheckSynth, .a0Check,
    .a0TTop, .a0Synth, .a0TCheckSynth, .a0Check,
    .a0TContext, .a0Check,
    .b1TPresupposeReference, .a0Check,
    .b1TPresupposeReference, .a0Check] }

theorem nested_expected_check_soundness_instantiation :
    checkBidirectional Environment.empty outerExpectedPresuppose
      (Ty.refComp Ty.entity) = .ok nestedExpectedCheckResult →
    CheckJudgment Environment.empty outerExpectedPresuppose
      (Ty.refComp Ty.entity) nestedExpectedCheckResult.observation := by
  intro success
  exact checkBidirectional_success_sound success (by rfl)

def compatibleNaturalCheckResult : TypingResult := {
  type := Ty.natural
  trace := [.a0TNatural, .a0Synth, .a0TCheckSynth, .a0Check] }

theorem compatible_synthesis_check_soundness_instantiation :
    checkBidirectional Environment.empty (.natural 7) Ty.number =
      .ok compatibleNaturalCheckResult →
    CheckJudgment Environment.empty (.natural 7) Ty.number
      compatibleNaturalCheckResult.observation := by
  intro success
  exact checkBidirectional_success_sound success (by rfl)

def overacceptPresupposeMutation {scope : Nat} (term : Term scope) : Bool :=
  match term with
  | .primitive .presuppose
      (.positional _ (.positional _ .nil)) => true
  | other => expectedOnlySynthesisForm other

def validateExpectedOnlyClassifierWith
    (classifier : Term 0 → Bool) : Except String Unit := do
  if !classifier nestedExpectedPresuppose then
    throw "nested expected-only Presuppose was rejected"
  if classifier nestedSynthablePresuppose then
    throw "nested synthable Presuppose was over-accepted as expected-only"

def validateExpectedOnlyClassifierMutation : Except String Unit := do
  validateExpectedOnlyClassifierWith expectedOnlySynthesisForm
  if (validateExpectedOnlyClassifierWith overacceptPresupposeMutation).isOk then
    throw "expected-only over-acceptance mutation did not fail"

def duplicateEventIdentity : FreeId := {
  domain := "$duplicate-event"
  serial := 0 }

def duplicateEventEnvironment : Environment 0 := {
  Environment.empty with
  free := [(duplicateEventIdentity, Ty.referents Ty.eventuality)] }

def duplicateEventArguments : TermList 0 :=
  .labelled ":Eventuality" (.free duplicateEventIdentity) <|
    .labelled ":Eventuality" (.free duplicateEventIdentity) .nil

def validatePredTermDuplicateEventRejection : Except String Unit :=
  match predTermArgumentResults duplicateEventEnvironment duplicateEventArguments with
  | .error error =>
      if error.code == "predterm-row" then pure ()
      else throw s!"duplicate Eventuality used unexpected error {error.code}"
  | .ok _ => throw "duplicate Eventuality fill was over-accepted"

def unseenRelationKey : ExpansionKey := {
  document := "m2-relation-unseen"
  occurrence := 73
  definition := .d12ActualClause }

def unseenRelationClause : Term 0 :=
  .lambda (Ty.referents Ty.eventuality) (top (scope := 1))

def unseenRelationPayload : ExpansionPayload 0 :=
  (expandActualClause unseenRelationClause).payload

theorem unseen_actual_clause_template :
    TemplateEquation Environment.empty unseenRelationKey .d12ActualClause
      [unseenRelationClause] unseenRelationPayload :=
  .actualClause unseenRelationClause

theorem unseen_actual_clause_dispatch_to_relation
    (payload : ExpansionPayload 0)
    (success : dispatchDefinition Environment.empty unseenRelationKey
      .d12ActualClause [unseenRelationClause] = .ok payload) :
    TemplateEquation Environment.empty unseenRelationKey .d12ActualClause
      [unseenRelationClause] payload :=
  dispatch_sound_against_template Environment.empty unseenRelationKey
    .d12ActualClause [unseenRelationClause] payload success
    ⟨unseenRelationPayload, unseen_actual_clause_template⟩

theorem unseen_actual_clause_relation_to_dispatch
    (certificate :
      (show Expansion 0 from {
        term := unseenRelationPayload.term
        clauses := unseenRelationPayload.clauses }).validate .d12ActualClause = .ok ())
    (typing : ∃ observation,
      SynthJudgment Environment.empty unseenRelationPayload.term observation) :
    dispatchDefinition Environment.empty unseenRelationKey .d12ActualClause
      [unseenRelationClause] = .ok unseenRelationPayload :=
  declarative_dispatch_complete Environment.empty unseenRelationKey
    .d12ActualClause [unseenRelationClause] unseenRelationPayload
    ⟨unseen_actual_clause_template, certificate, typing⟩

def runM2TypingGates : IO Unit := do
  let environment := Environment.empty
  IO.ofExcept validateExpectedOnlyClassifierMutation
  IO.ofExcept validatePredTermDuplicateEventRejection
  let nestedExpected ← IO.ofTyping <|
    checkBidirectional environment outerExpectedPresuppose (Ty.refComp Ty.entity)
  if nestedExpected.obligations.length != 2 ||
      !nestedExpected.effects.contains .projective then
    throw <| IO.userError
      "nested expected-only Presuppose lost its projective obligations"
  if (checkBidirectional environment outerSynthablePresuppose
      (Ty.refComp Ty.entity)).isOk then
    throw <| IO.userError
      "nested synthable Presuppose was over-accepted in expected mode"
  if (checkPresupposeReference environment
      (judgmentTermList [nestedPresupposeCondition, nestedSynthablePresuppose])
      (Ty.refComp Ty.entity)).isOk then
    throw <| IO.userError
      "direct expected-mode helper bypassed the structural classifier"
  if implementedTypingRuleRecords.length + unsupportedTypingRuleRecords.length !=
      m2TypingRuleRecords.length ||
      implementedTypingRuleRecords.any (fun implemented =>
        unsupportedTypingRuleRecords.any (fun unsupported =>
          implemented.id == unsupported.id)) then
    throw <| IO.userError "declarative typing manifest partition is incomplete"
  let natural ← IO.ofTyping <| synth environment (.natural 7)
  if natural.type != Ty.natural ||
      !natural.trace.contains .a0TNatural ||
      !natural.trace.contains .a0Synth then
    throw <| IO.userError "natural synthesis did not cite its manifest rules"

  if (checkBidirectional environment (.natural 7) Ty.content).isOk then
    throw <| IO.userError "wrong expected type was accepted"
  let checkedNatural ← IO.ofTyping <| checkBidirectional environment (.natural 7) Ty.number
  if checkedNatural.type != Ty.natural ||
      !checkedNatural.trace.contains .a0TCheckSynth then
    throw <| IO.userError "compatible check did not retain synthesis evidence"

  let identity : Term 0 := .lambda Ty.natural (.bound 0)
  let application : Term 0 :=
    .apply identity (.positional (.natural 4) .nil)
  let applied ← IO.ofTyping <| synth environment application
  if applied.type != Ty.natural || !applied.trace.contains .a0TApplyPure then
    throw <| IO.userError "pure function application typing failed"

  let context : Term 0 :=
    .context (typingExampleSite "context") (.positional (.natural 1) .nil)
  let contextResult ← IO.ofTyping <|
    checkBidirectional environment context (Ty.refComp Ty.entity)
  if contextResult.type != Ty.refComp Ty.entity ||
      !contextResult.effects.contains .context then
    throw <| IO.userError "Context expected-mode typing failed"

  let nestedContext : Term 0 :=
    .context (typingExampleSite "outer") <|
      .positional (.context (typingExampleSite "inner") .nil) .nil
  if (checkBidirectional environment nestedContext (Ty.refComp Ty.entity)).isOk then
    throw <| IO.userError "direct Context computation was accepted as a value operand"

  -- `top` remains a defined M2 template and therefore cannot enter CoreTerm;
  -- use a primitive equality as an unseen pure Content body.
  let referProperty : Term 0 :=
    .lambda Ty.entity <| .primitive .equal <|
      .positional (.bound 0) (.positional (.bound 0) .nil)
  let refer : Term 0 :=
    .primitive .refer (.positional referProperty .nil)
  let referResult ← IO.ofTyping <|
    checkBidirectional environment refer (Ty.refComp (Ty.referents Ty.entity))
  if !referResult.effects.contains .refer ||
      !referResult.trace.contains .a0TReferMember then
    throw <| IO.userError "member-level Refer dispatch failed"

  let stateType := Ty.named0 .sortState
  let stateProperty : Term 0 :=
    .lambda stateType <| .primitive .equal <|
      .positional (.bound 0) (.positional (.bound 0) .nil)
  let stateRefer : Term 0 :=
    .primitive .refer (.positional stateProperty .nil)
  let _ ← IO.ofTyping <| checkBidirectional environment stateRefer
    (Ty.refComp (Ty.referents stateType))
  if (checkBidirectional environment stateRefer
      (Ty.refComp (Ty.referents Ty.eventuality))).isOk then
    throw <| IO.userError "Refer member lift accepted a subsort rather than exact domain"
  let constructionEffectProperty : Term 0 :=
    .bind stateType (.context (typingExampleSite "refer-construction") .nil)
      (.lambda stateType <| .primitive .equal <|
        .positional (.bound 0) (.positional (.bound 0) .nil))
  let constructionEffectRefer : Term 0 :=
    .primitive .refer (.positional constructionEffectProperty .nil)
  if (checkBidirectional environment constructionEffectRefer
      (Ty.refComp (Ty.referents stateType))).isOk then
    throw <| IO.userError "Refer member lift accepted construction effects"

  let unsupported : Term 0 :=
    .primitive .multiply (.positional (.natural 2) (.positional (.natural 3) .nil))
  if (synth environment unsupported).isOk then
    throw <| IO.userError "unsupported primitive passed through a catch-all"

  if typingRuleRecordsFor referResult |>.any
      (fun record => !M2TypingRuleId.all.contains record.id) then
    throw <| IO.userError "typing trace cited a rule outside the pinned manifest"

  let property : Term 0 :=
    .lambda Ty.entity <| primitive .equal [.bound 0, .bound 0]
  let nuclear : Term 0 := .lambda (Ty.referents Ty.entity) top
  let zero := expandAtLeast Ty.entity (.natural 0) property nuclear
  let zeroType ← IO.ofTyping <| synth environment zero.term
  if zeroType.type != Ty.content || zero.clauses != [.d12AtLeastZero] then
    throw <| IO.userError "AtLeast zero template did not use its direct clause"
  let positive := expandAtLeast Ty.entity (.natural 2) property nuclear
  let positiveType ← IO.ofTyping <| synth environment positive.term
  if positiveType.type != Ty.content ||
      !positive.clauses.contains .d12AtLeastPositive then
    throw <| IO.userError "AtLeast positive template failed typed expansion"

  let emptyZip ← IO.ofExcept <| expandZipWith property [] []
  if Interchange.renderCanonicalTerm emptyZip.term !=
      Interchange.renderCanonicalTerm (top (scope := 0)) ||
      emptyZip.clauses != [.d12ZipWithEmpty] then
    throw <| IO.userError "ZipWith empty clause is not the empty conjunction"

  let key : ExpansionKey :=
    { document := "m2-site-gate", occurrence := 4, definition := .d12TooMany }
  let tooMany := expandTooMany Ty.entity key property nuclear
  let tooManyAgain := expandTooMany Ty.entity key property nuclear
  let copied := expandTooMany Ty.entity { key with occurrence := 5 } property nuclear
  if tooMany.sites != tooManyAgain.sites then
    throw <| IO.userError "same syntactic TooMany occurrence minted new sites"
  if tooMany.sites.map (·.identity) == copied.sites.map (·.identity) then
    throw <| IO.userError "copied TooMany occurrence reused expansion sites"
  match tooMany.sites with
  | [first, second] =>
      if first.identity == second.identity then
        throw <| IO.userError "TooMany expansion site pair is not distinct"
  | _ => throw <| IO.userError "TooMany did not allocate one ordered site pair"
  let tooManyType ← IO.ofTyping <| synth environment tooMany.term
  if tooManyType.type != Ty.content ||
      !tooMany.clauses.contains .d12TooManyDependentThreshold then
    throw <| IO.userError "TooMany site-introducing template did not type"

  let validatedTooMany ← IO.ofExcept <|
    buildElaborationBundle tooMany.term [] tooMany.sites []
  if validatedTooMany.uses.length != 2 then
    throw <| IO.userError "certified elaboration bundle lost the TooMany site pair"
  let encodedTooMany := Interchange.renderCanonicalTerm tooMany.term
  let decodedTooMany ← IO.ofExcept <|
    Interchange.decodeCanonicalTerm 0 encodedTooMany
  if Interchange.renderCanonicalTerm decodedTooMany != encodedTooMany ||
      decodedTooMany.siteIds != tooMany.term.siteIds then
    throw <| IO.userError "canonical/bracket-insensitive reserialization changed expansion sites"
  let renamedTooMany := tooMany.term.rename
    (fun index => (Fin.elim0 index : Fin 1))
  if renamedTooMany.siteIds != tooMany.term.siteIds then
    throw <| IO.userError "alpha/renaming changed expansion site identities"

  let sharedFunction : Term 0 := .lambda Ty.entity (weaken tooMany.term)
  let sharedType := Ty.effectfulFn [Ty.entity] Ty.content
  let sharedUses : Term 1 := primitive .and [
    apply (.bound 0) [.natural 1], apply (.bound 0) [.natural 2]]
  let shared := expandLet sharedType sharedFunction sharedUses
  if shared.term.siteIds.length != 2 then
    throw <| IO.userError "one shared lambda occurrence did not retain exactly one site pair"

  let relationId : FreeId := { domain := "$grade-relation", serial := 0 }
  let degreeId : FreeId := { domain := "$grade-degree", serial := 0 }
  let scaleId : FreeId := { domain := "$grade-scale", serial := 0 }
  let regionId : FreeId := { domain := "$grade-region", serial := 0 }
  let gradeRow := Ty.arityRow 1
  let gradeEnvironment : Environment 0 := { Environment.empty with
    free := [
      (relationId, Ty.predTerm gradeRow),
      (degreeId, Ty.pureFn [Ty.record gradeRow, Ty.scale] Ty.amount),
      (scaleId, Ty.scale),
      (regionId, Ty.region Ty.scale)]
    lexical := [("InRegion", Ty.pureFn [Ty.amount, Ty.region Ty.scale] Ty.content)] }
  let grade := expandGrade {
    degree := {
      relation := .free relationId
      row := gradeRow
      projection := .free degreeId }
    scale := .free scaleId
    region := .free regionId }
  let gradeType ← IO.ofTyping <| synth gradeEnvironment grade.term
  if gradeType.type != Ty.pureFn [Ty.record gradeRow] Ty.content ||
      !gradeType.effects.isEmpty || !grade.term.siteIds.isEmpty ||
      grade.clauses != [.d12GradeRowDirected] then
    throw <| IO.userError "pure row-directed Grade specimen failed"

  let raisedRow := Ty.arityRow 1
  let baseRow := Ty.arityRow 1
  let jaiRelation : FreeId := { domain := "$jai-relation", serial := 0 }
  let jaiRole : FreeId := { domain := "$jai-role", serial := 0 }
  let jaiRebuild : FreeId := { domain := "$jai-rebuild", serial := 0 }
  let jaiRaised : FreeId := { domain := "$jai-raised", serial := 0 }
  let jaiOld : FreeId := { domain := "$jai-old", serial := 0 }
  let roleType := Ty.pureFn
    [Ty.referents Ty.entity, Ty.referents Ty.eventuality] Ty.content
  let jaiEnvironment : Environment 0 := { Environment.empty with free := [
    (jaiRelation, Ty.predTerm baseRow),
    (jaiRole, roleType),
    (jaiRebuild, Ty.pureFn [Ty.record raisedRow] (Ty.record baseRow)),
    (jaiRaised, Ty.pureFn [Ty.record raisedRow] (Ty.referents Ty.entity)),
    (jaiOld, Ty.pureFn [Ty.record raisedRow] (Ty.referents Ty.eventuality))] }
  let jai := expandJaiRaise {
    baseRow
    raisedRow
    relation := .free jaiRelation
    role := .free jaiRole
    reconstructBase := .free jaiRebuild
    raisedProjection := .free jaiRaised
    oldFirstProjection := .free jaiOld }
  let jaiType ← IO.ofTyping <| synth jaiEnvironment jai.term
  if jaiType.type != Ty.pureFn [Ty.record raisedRow] Ty.content ||
      jai.clauses != [.d12JaiRaiseRaisedRole] then
    throw <| IO.userError "pure JaiRaise row reconstruction specimen failed"

  let bareKey : ExpansionKey := {
    document := "m2-bare-jai", occurrence := 0, definition := .d12JaiRaise }
  let bareJai := expandBareJai bareKey (.free jaiRelation) roleType
    (top (scope := 1))
  let bareType ← IO.ofTyping <| synth jaiEnvironment bareJai.term
  let _ ← IO.ofExcept <| buildElaborationBundle bareJai.term [] bareJai.sites []
  if bareType.type != Ty.content || bareJai.sites.length != 1 ||
      bareJai.clauses != [.d12JaiRaiseBareJaiMapping] then
    throw <| IO.userError "bare-jai constrained Context mapping failed"

  let unknownRowId : FreeId := { domain := "$unknown-row", serial := 0 }
  let unknownRowEnvironment : Environment 0 := { Environment.empty with
    free := [(unknownRowId, Ty.predTerm (Ty.rowOf "unseen-row-head"))] }
  match typedClosePlan unknownRowEnvironment (.free unknownRowId) with
  | .error error =>
      if error.code != "unknown-row" then
        throw <| IO.userError "unknown RowOf failed without the named rejection rule"
  | .ok _ => throw <| IO.userError "unseen unknown RowOf was accepted"

end M2
end SmusniPilot
