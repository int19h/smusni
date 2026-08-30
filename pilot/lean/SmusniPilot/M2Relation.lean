import SmusniPilot.M2Cases
import SmusniPilot.M2TypingBridge

namespace SmusniPilot
namespace M2

def executableCount {scope : Nat} (count : Term scope) : Bool :=
  isZeroTerm count || provablyPositive count

def PurePropertyJudgment {scope : Nat} (environment : Environment scope)
    (property : Term scope) (memberType : Ty) : Prop :=
  ∃ observation, SynthJudgment environment property observation ∧
    observation.type = Ty.pureFn [memberType] Ty.content ∧
    observation.effects = []

def ReferenceMemberJudgment {scope : Nat} (environment : Environment scope)
    (reference : Term scope) (memberType : Ty) : Prop :=
  ∃ observation, SynthJudgment environment reference observation ∧
    Ty.referenceInner observation.type = some memberType

def DecompositionBasisJudgment {scope : Nat} (environment : Environment scope)
    (basis : Term scope) (wholeType componentType : Ty) : Prop :=
  ∃ observation, SynthJudgment environment basis observation ∧
    observation.type = Ty.decompositionBasis wholeType componentType

@[simp] theorem pure_property_member_unique {scope : Nat}
    {environment : Environment scope} {property : Term scope} {first second : Ty}
    (firstTyping : PurePropertyJudgment environment property first)
    (secondTyping : PurePropertyJudgment environment property second) : first = second := by
  rcases firstTyping with ⟨firstObservation, firstJudgment, firstType, _⟩
  rcases secondTyping with ⟨secondObservation, secondJudgment, secondType, _⟩
  have observationAgreement :=
    synthesis_observation_unique firstJudgment secondJudgment
  rw [observationAgreement] at firstType
  rw [firstType] at secondType
  injection secondType with _ parameters _
  injection parameters

@[simp] theorem reference_member_unique {scope : Nat}
    {environment : Environment scope} {reference : Term scope} {first second : Ty}
    (firstTyping : ReferenceMemberJudgment environment reference first)
    (secondTyping : ReferenceMemberJudgment environment reference second) : first = second := by
  rcases firstTyping with ⟨firstObservation, firstJudgment, firstType⟩
  rcases secondTyping with ⟨secondObservation, secondJudgment, secondType⟩
  have observationAgreement :=
    synthesis_observation_unique firstJudgment secondJudgment
  rw [observationAgreement] at firstType
  rw [firstType] at secondType
  injection secondType

@[simp] theorem decomposition_basis_unique {scope : Nat}
    {environment : Environment scope} {basis : Term scope}
    {firstWhole firstComponent secondWhole secondComponent : Ty}
    (firstTyping : DecompositionBasisJudgment environment basis
      firstWhole firstComponent)
    (secondTyping : DecompositionBasisJudgment environment basis
      secondWhole secondComponent) :
    firstWhole = secondWhole ∧ firstComponent = secondComponent := by
  rcases firstTyping with ⟨firstObservation, firstJudgment, firstType⟩
  rcases secondTyping with ⟨secondObservation, secondJudgment, secondType⟩
  have observationAgreement :=
    synthesis_observation_unique firstJudgment secondJudgment
  rw [observationAgreement] at firstType
  rw [firstType] at secondType
  injection secondType with _ arguments
  injection arguments with whole tail
  injection tail with component _
  exact ⟨whole, component⟩

@[simp] private theorem pure_property_executable {scope : Nat}
    {environment : Environment scope} {property : Term scope} {memberType : Ty}
    (typing : PurePropertyJudgment environment property memberType) :
    memberTypeOfProperty environment property = .ok memberType := by
  rcases typing with ⟨observation, judgment, propertyType, pure⟩
  rcases synth_judgment_complete judgment with ⟨result, success, agreement⟩
  have propertyTypeRaw : result.type = Ty.pureFn [memberType] Ty.content := by
    exact (congrArg TypingObservation.type agreement).trans propertyType
  have pureRaw : result.effects = [] := by
    exact (congrArg TypingObservation.effects agreement).trans pure
  simp [memberTypeOfProperty, success, propertyTypeRaw, pureRaw, isPure,
    Ty.pureFn, Ty.content, Ty.named0, instBEqTy, Ty.beq, Ty.listBeq]

@[simp] private theorem reference_member_executable {scope : Nat}
    {environment : Environment scope} {reference : Term scope} {memberType : Ty}
    (typing : ReferenceMemberJudgment environment reference memberType) :
    referenceMemberType environment reference = .ok memberType := by
  rcases typing with ⟨observation, judgment, referenceType⟩
  rcases synth_judgment_complete judgment with ⟨result, success, agreement⟩
  have referenceTypeRaw : Ty.referenceInner result.type = some memberType := by
    have typeAgreement : result.type = observation.type :=
      congrArg TypingObservation.type agreement
    rw [typeAgreement]
    exact referenceType
  simp [referenceMemberType, success, referenceTypeRaw]

@[simp] private theorem decomposition_basis_executable {scope : Nat}
    {environment : Environment scope} {basis : Term scope}
    {wholeType componentType : Ty}
    (typing : DecompositionBasisJudgment environment basis wholeType componentType) :
    decompositionTypes environment basis = .ok (wholeType, componentType) := by
  rcases typing with ⟨observation, judgment, basisType⟩
  rcases synth_judgment_complete judgment with ⟨result, success, agreement⟩
  have basisTypeRaw : result.type = Ty.decompositionBasis wholeType componentType := by
    exact (congrArg TypingObservation.type agreement).trans basisType
  simp [decompositionTypes, success, basisTypeRaw, Ty.decompositionBasis,
    Ty.asBinary]

inductive TemplateEquation {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) :
    M2DefinitionId → List (Term scope) → ExpansionPayload scope → Prop where
  | actualClause (clause : Term scope) :
      TemplateEquation environment key .d12ActualClause [clause]
        (expandActualClause clause).payload
  | atLeast (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType)
      (domain : executableCount count = true) :
      TemplateEquation environment key .d12AtLeast [count, property, nuclear]
        (expandAtLeast memberType count property nuclear).payload
  | atMost (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12AtMost [count, property, nuclear]
        (expandAtMost memberType count property nuclear).payload
  | canonicalAggregateAt (basis group cover : Term scope)
      (wholeType componentType : Ty)
      (basisType : DecompositionBasisJudgment environment basis wholeType componentType) :
      TemplateEquation environment key .d12CanonicalAggregateAt [basis, group, cover]
        (expandCanonicalAggregateAt componentType basis group cover).payload
  | coRef (first second : Term scope) :
      TemplateEquation environment key .d12CoRef [first, second]
        (expandCoRef first second).payload
  | distrib (property reference : Term scope) (memberType : Ty)
      (referenceType : ReferenceMemberJudgment environment reference memberType) :
      TemplateEquation environment key .d12Distrib [property, reference]
        (expandDistrib memberType property reference).payload
  | every (property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12Every [property, nuclear]
        (expandEvery memberType property nuclear).payload
  | exactly (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType)
      (domain : executableCount count = true) :
      TemplateEquation environment key .d12Exactly [count, property, nuclear]
        (expandExactly memberType count property nuclear).payload
  | fewerThan (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12FewerThan [count, property, nuclear]
        (expandFewerThan memberType count property nuclear).payload
  | globalExactly (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12GlobalExactly [count, property, nuclear]
        (expandGlobalExactly memberType count property nuclear).payload
  | massify (basis cover : Term scope) (wholeType componentType : Ty)
      (basisType : DecompositionBasisJudgment environment basis wholeType componentType) :
      TemplateEquation environment key .d12Massify [basis, cover]
        (expandMassify componentType basis cover).payload
  | maxRefer (property : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12MaxRefer [property]
        (expandMaxRefer memberType property).payload
  | moreThan (count property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12MoreThan [count, property, nuclear]
        (expandMoreThan memberType count property nuclear).payload
  | no (property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12No [property, nuclear]
        (expandNo memberType property nuclear).payload
  | overlap (first second : Term scope) (memberType : Ty)
      (referenceType : ReferenceMemberJudgment environment first memberType) :
      TemplateEquation environment key .d12Overlap [first, second]
        (expandOverlap memberType first second).payload
  | some (property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d12Some [property, nuclear]
        (expandSome memberType property nuclear).payload
  | tooMany (property nuclear : Term scope) (memberType : Ty)
      (propertyType : PurePropertyJudgment environment property memberType) :
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
      (propertyType : PurePropertyJudgment environment property memberType) :
      TemplateEquation environment key .d48CoveredBy [property, reference]
        (expandCoveredBy memberType property reference).payload
  | completeGunmaAt (basis whole cover : Term scope)
      (wholeType componentType : Ty)
      (basisType : DecompositionBasisJudgment environment basis wholeType componentType) :
      TemplateEquation environment key .d49CompleteGunmaAt [basis, whole, cover]
        (expandCompleteGunmaAt wholeType componentType basis whole cover).payload
  | gunmaAt (basis whole cover : Term scope) (wholeType componentType : Ty)
      (basisType : DecompositionBasisJudgment environment basis wholeType componentType) :
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
  typing : ∃ observation, SynthJudgment environment payload.term observation

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
  cases equation
  all_goals
    try have propertyExecutable :=
      pure_property_executable ‹PurePropertyJudgment _ _ _›
    try have referenceExecutable :=
      reference_member_executable ‹ReferenceMemberJudgment _ _ _›
    try have basisExecutable :=
      decomposition_basis_executable ‹DecompositionBasisJudgment _ _ _ _›
  all_goals
    simp only [dispatchDefinition] <;>
    simp only [except_pure_eq_ok, except_ok_bind] <;>
    simp_all [executableCount, isZeroTerm, pure_property_executable,
      reference_member_executable, decomposition_basis_executable] <;>
    try rw [certificate] <;>
    try rfl
  all_goals intros <;> try simp_all

theorem declarative_sound {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) (payload : ExpansionPayload scope)
    (derivation : DeclarativeElaboration environment key definition arguments payload) :
    TemplateEquation environment key definition arguments payload :=
  derivation.equation

theorem dispatch_sound_against_template {scope : Nat}
    (environment : Environment scope) (key : ExpansionKey)
    (definition : M2DefinitionId) (arguments : List (Term scope))
    (payload : ExpansionPayload scope)
    (success : dispatchDefinition environment key definition arguments = .ok payload)
    (supported : ∃ expectedPayload,
      TemplateEquation environment key definition arguments expectedPayload) :
    TemplateEquation environment key definition arguments payload := by
  rcases supported with ⟨expectedPayload, equation⟩
  have originalEquation := equation
  cases equation
  all_goals
    try have propertyExecutable :=
      pure_property_executable ‹PurePropertyJudgment _ _ _›
    try have referenceExecutable :=
      reference_member_executable ‹ReferenceMemberJudgment _ _ _›
    try have basisExecutable :=
      decomposition_basis_executable ‹DecompositionBasisJudgment _ _ _ _›
  all_goals
    simp_all [dispatchDefinition, executableCount, isZeroTerm]
  all_goals
    repeat' split at success
    try simp_all
  all_goals cases success
  all_goals assumption

theorem template_output_functional {scope : Nat} (environment : Environment scope)
    (key : ExpansionKey) (definition : M2DefinitionId)
    (arguments : List (Term scope)) (first second : ExpansionPayload scope)
    (firstEquation : TemplateEquation environment key definition arguments first)
    (secondEquation : TemplateEquation environment key definition arguments second) :
    first.term = second.term ∧ first.clauses = second.clauses ∧
      first.sites = second.sites := by
  cases firstEquation <;> cases secondEquation
  all_goals grind [synthesis_observation_unique, pure_property_member_unique,
    reference_member_unique, decomposition_basis_unique]

inductive SupplementalTemplateInput (scope : Nat) where
  | letTerm (binderType : Ty) (value : Term scope) (body : Term (scope + 1))
  | referMember (property : Term scope)

inductive SupplementalTemplateEquation {scope : Nat}
    (environment : Environment scope) :
    SupplementalTemplateInput scope → ExpansionPayload scope → Prop where
  | letTerm (binderType : Ty) (value : Term scope) (body : Term (scope + 1))
      (valueObservation bodyObservation : TypingObservation)
      (valueTyping : CheckJudgment environment value binderType valueObservation)
      (bodyTyping : SynthJudgment (environment.extend binderType) body bodyObservation) :
      SupplementalTemplateEquation environment (.letTerm binderType value body)
        (expandLet binderType value body).payload
  | referMember (property : Term scope) (memberType : Ty)
      (propertyTyping : PurePropertyJudgment environment property memberType) :
      SupplementalTemplateEquation environment (.referMember property)
        (expandReferMember memberType property).payload

theorem supplemental_template_functional {scope : Nat}
    (environment : Environment scope) (input : SupplementalTemplateInput scope)
    (first second : ExpansionPayload scope)
    (firstEquation : SupplementalTemplateEquation environment input first)
    (secondEquation : SupplementalTemplateEquation environment input second) :
    first.term = second.term ∧ first.clauses = second.clauses ∧
      first.sites = second.sites := by
  cases firstEquation <;> cases secondEquation
  all_goals grind [pure_property_member_unique]

/- The current converse theorem covers the core definition dispatcher.  The
recursive surface decoder/state allocator remains an explicitly narrower
domain; supplemental equations cover its typed Let and Refer-member leaves.
Grade/JaiRaise plan validation and a converse for decoding are not claimed. -/

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
    (firstDerivation : DeclarativeElaboration environment key definition arguments first)
    (secondDerivation : DeclarativeElaboration environment key definition arguments second)
    (_firstExecutable : dispatchDefinition environment key definition arguments = .ok first)
    (_secondExecutable : dispatchDefinition environment key definition arguments = .ok second) :
    first.term = second.term ∧ first.clauses = second.clauses ∧
      first.sites = second.sites :=
  template_output_functional environment key definition arguments first second
    firstDerivation.equation secondDerivation.equation

end M2
end SmusniPilot
