import SmusniPilot.M2Bundle

namespace SmusniPilot
namespace M2

def TypingError.message (error : TypingError) : String :=
  s!"{error.code}: {error.detail}"

def IO.ofTyping {α : Type} (result : Except TypingError α) : IO α :=
  IO.ofExcept (result.mapError TypingError.message)

def typingExampleSite (role : String) : SiteId :=
  { document := "m2-typing", occurrence := 0, expansionRole := role }

def runM2TypingGates : IO Unit := do
  let environment := Environment.empty
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
