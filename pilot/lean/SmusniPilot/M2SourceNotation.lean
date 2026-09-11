import SmusniPilot.M2TypingSoundness

namespace SmusniPilot
namespace M2

/- Source notation is separate from the strict core typing judgment. The
   wrapper contains the Act expression once, introduces no binder/site, and
   uses the ordinary Host performance and discourse/discard constructors. -/
def performAct {n : Nat} (act : Term n) : Term n :=
  .primitive .perform (.positional (.primitive .host .nil) (.positional act .nil))

def discardPerformance {n : Nat} (performance : Term n) : Term n :=
  .primitive .do (.positional performance .nil)

def sourcePerformanceOperand {n : Nat} (environment : Environment n)
    (term : Term n) : Except TypingError (Term n) := do
  let result ← synth environment term
  if (Ty.asUnary result.type .typeFormAct).isSome then pure (performAct term)
  else if result.type == Ty.discourse || (Ty.asUnary result.type .typeFormPerfComp).isSome then
    pure term
  else failure "expected-discourse" "source performance position requires Act, PerfComp or Discourse"

def sourceDiscourse {n : Nat} (environment : Environment n)
    (term : Term n) : Except TypingError (Term n) := do
  let operand ← sourcePerformanceOperand environment term
  let result ← synth environment operand
  if result.type == Ty.discourse then pure operand
  else pure (discardPerformance operand)

def sourceDoOperands {n : Nat} (environment : Environment n) :
    TermList n → Except TypingError (TermList n)
  | .nil => pure .nil
  | .positional head tail =>
      return .positional (← sourcePerformanceOperand environment head)
        (← sourceDoOperands environment tail)
  | .labelled _ _ _ => failure "discourse-label" "Do requires positional operands"

mutual
  def normalizeSourceTerm {n : Nat} (environment : Environment n) :
      Term n → Except TypingError (Term n)
    | .bound index => pure (.bound index)
    | .free id => pure (.free id)
    | .natural value => pure (.natural value)
    | .string value => pure (.string value)
    | .index value => pure (.index value)
    | .lambda type body => return .lambda type (← normalizeSourceTerm (environment.extend type) body)
    | .bind type value body =>
        return .bind type (← normalizeSourceTerm environment value)
          (← normalizeSourceTerm (environment.extend type) body)
    | .performSource reference source content continuation => do
        let source ← normalizeSourceTerm environment source
        let next := (environment.extend (Ty.refComp reference)).extend (Ty.actOccurrence Ty.assertion)
        let continuation ← normalizeSourceTerm next continuation
        -- C1 is already resolved: no notation traversal under this boundary.
        pure (.performSource reference source content (← sourceDiscourse next continuation))
    | .apply function arguments =>
        return .apply (← normalizeSourceTerm environment function)
          (← normalizeSourceTerms environment arguments)
    | .lexical head arguments => return .lexical head (← normalizeSourceTerms environment arguments)
    | .context site arguments => return .context site (← normalizeSourceTerms environment arguments)
    | .vague site constraint => return .vague site (← normalizeSourceTerm environment constraint)
    | .primitive operator arguments => do
        let arguments ← normalizeSourceTerms environment arguments
        pure (.primitive operator (← if operator == .do then sourceDoOperands environment arguments else pure arguments))

  def normalizeSourceTerms {n : Nat} (environment : Environment n) :
      TermList n → Except TypingError (TermList n)
    | .nil => pure .nil
    | .positional head tail =>
        return .positional (← normalizeSourceTerm environment head)
          (← normalizeSourceTerms environment tail)
    | .labelled label head tail =>
        return .labelled label (← normalizeSourceTerm environment head)
          (← normalizeSourceTerms environment tail)
end

-- Canonical AST is part of the result: callers cannot attach the deep typing
-- theorem to an unnormalized source tree. No Act/Discourse subtype is added.
def synthesizeSource {n : Nat} (environment : Environment n) (source : Term n) :
    Except TypingError (Term n × TypingResult) := do
  let canonical ← normalizeSourceTerm environment source
  pure (canonical, ← synth environment canonical)

theorem synthesizeSource_sound {n : Nat} (environment : Environment n)
    (source canonical : Term n) (result : TypingResult)
    (success : synthesizeSource environment source = .ok (canonical, result))
    (supported : result.trace.all typingRuleImplemented = true) :
    SynthJudgment environment canonical result.observation := by
  cases normalized : normalizeSourceTerm environment source with
  | error error => simp [synthesizeSource, normalized] at success
  | ok term =>
      cases typed : synth environment term with
      | error error => simp [synthesizeSource, normalized, typed] at success
      | ok typing =>
          simp [synthesizeSource, normalized, typed] at success
          rcases success with ⟨rfl, rfl⟩
          exact synth_success_sound typed supported

-- Primitive source decoder with declared free-variable types; M1's raw
-- decodeClosedCore remains structural and may represent ill-typed terms.
def decodeSourceCore (document : String) (lexicalHeads : List String)
    (environment : Environment 0) (surface : SurfaceTerm) (rrLink : Option String := none) :
    Except String (Term 0 × DecodeState) := do
  let freeNames := environment.free.map (fun entry => entry.1.domain)
  let (raw, state) ← decodeClosedCoreWith document lexicalHeads freeNames rrLink surface
  let canonical ← (normalizeSourceTerm environment raw).mapError (fun error => error.detail)
  pure (canonical, state)

theorem performAct_siteUses {n : Nat} (act : Term n) :
    (discardPerformance (performAct act)).siteUses = act.siteUses := by
  simp [discardPerformance, performAct, Term.siteUses, TermList.siteUses]

theorem performAct_siteOccurrences {n : Nat} (act : Term n) :
    (discardPerformance (performAct act)).siteOccurrences = act.siteOccurrences := by
  simp [discardPerformance, performAct, Term.siteOccurrences, TermList.siteOccurrences]

theorem performAct_rename {n m : Nat} (act : Term n) (rename : Renaming n m) :
    (discardPerformance (performAct act)).rename rename =
      discardPerformance (performAct (act.rename rename)) := rfl

theorem performAct_substitute {n m : Nat} (act : Term n) (substitute : Substitution n m) :
    (discardPerformance (performAct act)).substitute substitute =
      discardPerformance (performAct (act.substitute substitute)) := rfl

end M2
end SmusniPilot
