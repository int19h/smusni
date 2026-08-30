import SmusniPilot.M2Cases

namespace SmusniPilot
namespace M2

def executableCount {scope : Nat} (count : Term scope) : Bool :=
  isZeroTerm count || provablyPositive count

inductive TemplateEquation {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) :
    M2DefinitionId → List (Term scope) → ExpansionPayload scope → Prop where
  | actualClause (clause : Term scope) :
      TemplateEquation environment key .d12ActualClause [clause]
        (expandActualClause clause).payload
  | atLeast (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType)
      (domain : executableCount count = true) :
      TemplateEquation environment key .d12AtLeast [count, property, nuclear]
        (expandAtLeast memberType count property nuclear).payload
  | atMost (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12AtMost [count, property, nuclear]
        (expandAtMost memberType count property nuclear).payload
  | canonicalAggregateAt (basis group cover : Term scope)
      (wholeType componentType : Ty)
      (basisType : decompositionTypes environment basis = .ok (wholeType, componentType)) :
      TemplateEquation environment key .d12CanonicalAggregateAt [basis, group, cover]
        (expandCanonicalAggregateAt componentType basis group cover).payload
  | coRef (first second : Term scope) :
      TemplateEquation environment key .d12CoRef [first, second]
        (expandCoRef first second).payload
  | distrib (property reference : Term scope) (memberType : Ty)
      (referenceType : referenceMemberType environment reference = .ok memberType) :
      TemplateEquation environment key .d12Distrib [property, reference]
        (expandDistrib memberType property reference).payload
  | every (property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12Every [property, nuclear]
        (expandEvery memberType property nuclear).payload
  | exactly (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType)
      (domain : executableCount count = true) :
      TemplateEquation environment key .d12Exactly [count, property, nuclear]
        (expandExactly memberType count property nuclear).payload
  | fewerThan (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12FewerThan [count, property, nuclear]
        (expandFewerThan memberType count property nuclear).payload
  | globalExactly (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12GlobalExactly [count, property, nuclear]
        (expandGlobalExactly memberType count property nuclear).payload
  | massify (basis cover : Term scope) (wholeType componentType : Ty)
      (basisType : decompositionTypes environment basis = .ok (wholeType, componentType)) :
      TemplateEquation environment key .d12Massify [basis, cover]
        (expandMassify componentType basis cover).payload
  | maxRefer (property : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12MaxRefer [property]
        (expandMaxRefer memberType property).payload
  | moreThan (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12MoreThan [count, property, nuclear]
        (expandMoreThan memberType count property nuclear).payload
  | no (property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12No [property, nuclear]
        (expandNo memberType property nuclear).payload
  | overlap (first second : Term scope) (memberType : Ty)
      (referenceType : referenceMemberType environment first = .ok memberType) :
      TemplateEquation environment key .d12Overlap [first, second]
        (expandOverlap memberType first second).payload
  | some (property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12Some [property, nuclear]
        (expandSome memberType property nuclear).payload
  | tooMany (property nuclear : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d12TooMany [property, nuclear]
        (expandTooMany memberType key property nuclear).payload
  | zipWith (function left right : Term scope)
      (leftItems rightItems : List (Term scope)) (expansion : Expansion scope)
      (leftList : termAsList left = .ok leftItems)
      (rightList : termAsList right = .ok rightItems)
      (expanded : expandZipWith function leftItems rightItems = .ok expansion) :
      TemplateEquation environment key .d12ZipWith [function, left, right]
        expansion.payload
  | close (predicate : Term scope) (plan : ClosePlan scope)
      (expansion : SiteExpansion scope)
      (row : typedClosePlan environment predicate = .ok plan)
      (expanded : expandClose key plan = .ok expansion) :
      TemplateEquation environment key .d46Close [predicate] expansion.payload
  | directClause (predicate : Term scope) (plan : ClosePlan scope)
      (row : typedClosePlan environment predicate = .ok plan) :
      TemplateEquation environment key .d46DirectClause [predicate]
        (expandDirectClause key plan.predicate plan.places).payload
  | coveredBy (property reference : Term scope) (memberType : Ty)
      (propertyType : memberTypeOfProperty environment property = .ok memberType) :
      TemplateEquation environment key .d48CoveredBy [property, reference]
        (expandCoveredBy memberType property reference).payload
  | completeGunmaAt (basis whole cover : Term scope)
      (wholeType componentType : Ty)
      (basisType : decompositionTypes environment basis = .ok (wholeType, componentType)) :
      TemplateEquation environment key .d49CompleteGunmaAt [basis, whole, cover]
        (expandCompleteGunmaAt wholeType componentType basis whole cover).payload
  | gunmaAt (basis whole cover : Term scope) (wholeType componentType : Ty)
      (basisType : decompositionTypes environment basis = .ok (wholeType, componentType)) :
      TemplateEquation environment key .d49GunmaAt [basis, whole, cover]
        (expandGunmaAt wholeType componentType basis whole cover).payload
  | selectSome (property : Term scope) :
      TemplateEquation environment key .d56SelectSome [property]
        (expandSelectSome property).payload

structure DeclarativeElaboration {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) (payload : ExpansionPayload scope) : Prop where
  equation : TemplateEquation environment key definition arguments payload
  certificate :
    (show Expansion scope from { term := payload.term, clauses := payload.clauses }).validate
      definition = .ok ()
  typing : ∃ result, synth environment payload.term = .ok result

@[simp] theorem except_pure_eq_ok {error value : Type} (item : value) :
    (pure item : Except error value) = .ok item := rfl

@[simp] theorem except_ok_bind {error first second : Type}
    (item : first) (next : first → Except error second) :
    ((Except.ok item : Except error first) >>= next) = next item := rfl

theorem declarative_dispatch_complete {scope : Nat}
    (environment : Environment scope) (key : ExpansionKey)
    (definition : M2DefinitionId) (arguments : List (Term scope))
    (payload : ExpansionPayload scope)
    (derivation : DeclarativeElaboration environment key definition arguments payload) :
    dispatchDefinition environment key definition arguments = .ok payload := by
  rcases derivation with ⟨equation, certificate, _typing⟩
  cases equation <;>
    simp only [dispatchDefinition] <;>
    simp only [except_pure_eq_ok, except_ok_bind] <;>
    simp_all [executableCount, isZeroTerm] <;>
    try rw [certificate] <;>
    try rfl
  all_goals intros <;> simp_all

theorem declarative_sound {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) (payload : ExpansionPayload scope)
    (derivation : DeclarativeElaboration environment key definition arguments payload) :
    TemplateEquation environment key definition arguments payload :=
  derivation.equation

theorem dispatch_output_functional {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) (first second : ExpansionPayload scope)
    (firstSuccess : dispatchDefinition environment key definition arguments = .ok first)
    (secondSuccess : dispatchDefinition environment key definition arguments = .ok second) :
    first.term = second.term ∧ first.clauses = second.clauses ∧
      first.sites = second.sites := by
  rw [firstSuccess] at secondSuccess
  cases secondSuccess
  exact ⟨rfl, rfl, rfl⟩

theorem declarative_output_functional {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) (first second : ExpansionPayload scope)
    (_first : DeclarativeElaboration environment key definition arguments first)
    (_second : DeclarativeElaboration environment key definition arguments second)
    (firstExecutable : dispatchDefinition environment key definition arguments = .ok first)
    (secondExecutable : dispatchDefinition environment key definition arguments = .ok second) :
    first.term = second.term ∧ first.clauses = second.clauses ∧
      first.sites = second.sites :=
  dispatch_output_functional environment key definition arguments first second
    firstExecutable secondExecutable

end M2
end SmusniPilot
