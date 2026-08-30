import SmusniPilot.M2Templates

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

  if (check environment (.natural 7) Ty.content).isOk then
    throw <| IO.userError "wrong expected type was accepted"
  let checkedNatural ← IO.ofTyping <| check environment (.natural 7) Ty.number
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
    check environment context (Ty.refComp Ty.entity)
  if contextResult.type != Ty.refComp Ty.entity ||
      !contextResult.effects.contains .context then
    throw <| IO.userError "Context expected-mode typing failed"

  let nestedContext : Term 0 :=
    .context (typingExampleSite "outer") <|
      .positional (.context (typingExampleSite "inner") .nil) .nil
  if (check environment nestedContext (Ty.refComp Ty.entity)).isOk then
    throw <| IO.userError "direct Context computation was accepted as a value operand"

  -- `top` remains a defined M2 template and therefore cannot enter CoreTerm;
  -- use a primitive equality as an unseen pure Content body.
  let referProperty : Term 0 :=
    .lambda Ty.entity <| .primitive .equal <|
      .positional (.bound 0) (.positional (.bound 0) .nil)
  let refer : Term 0 :=
    .primitive .refer (.positional referProperty .nil)
  let referResult ← IO.ofTyping <|
    check environment refer (Ty.refComp (Ty.referents Ty.entity))
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

end M2
end SmusniPilot
