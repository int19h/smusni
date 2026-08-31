import SmusniPilot.M2Typing

namespace SmusniPilot
namespace M2

def termList {scope : Nat} : List (Term scope) → TermList scope
  | [] => .nil
  | head :: tail => .positional head (termList tail)

def labelledTermList {scope : Nat} :
    List (String × Term scope) → TermList scope
  | [] => .nil
  | (label, term) :: tail => .labelled label term (labelledTermList tail)

def primitive {scope : Nat} (operator : FirstOrderPrimitive)
    (arguments : List (Term scope) := []) : Term scope :=
  .primitive operator (termList arguments)

def apply {scope : Nat} (function : Term scope)
    (arguments : List (Term scope)) : Term scope :=
  .apply function (termList arguments)

def weaken {scope : Nat} (term : Term scope) : Term (scope + 1) :=
  term.rename Fin.succ

def weakenN {scope : Nat} (depth : Nat) (term : Term scope) :
    Term (scope + depth) :=
  term.rename (Renaming.shiftN depth)

structure Expansion (scope : Nat) where
  term : Term scope
  clauses : List M2ClauseId

def definitionByHead (head : String) : Option M2DefinitionId :=
  (m2DefinitionRecords.find? fun record => record.head == head).map (·.id)

def directDefinitionDependencies (definition : M2DefinitionId) :
    List M2DefinitionId :=
  definition.record.dependencies.filterMap definitionByHead

def definitionClosure : Nat → List M2DefinitionId → List M2DefinitionId
  | 0, seeds => seeds.eraseDups
  | fuel + 1, seeds =>
      let expanded := (seeds ++ seeds.flatMap directDefinitionDependencies).eraseDups
      definitionClosure fuel expanded

def Expansion.validate {scope : Nat} (root : M2DefinitionId)
    (expansion : Expansion scope) : Except String Unit := do
  let allowed := definitionClosure M2DefinitionId.all.length [root]
  if expansion.clauses.isEmpty then
    .error s!"template {root.name} emitted no definition clause certificate"
  else pure ()
  let some finalClause := expansion.clauses.getLast?
    | .error s!"template {root.name} emitted no final clause"
  if finalClause.definition != root then
    .error s!"template {root.name} final clause belongs to {finalClause.definition.name}"
  else pure ()
  for clause in expansion.clauses do
    if !allowed.contains clause.definition then
      .error s!"template {root.name} used undeclared definition dependency {clause.definition.name}"
    else if !clause.definition.record.clauses.contains clause then
      .error s!"clause {clause.name} is absent from its generated definition record"
    else pure ()

def Expansion.addClause {scope : Nat} (expansion : Expansion scope)
    (clause : M2ClauseId) : Expansion scope :=
  { expansion with clauses := expansion.clauses ++ [clause] }

def top {scope : Nat} : Term scope := primitive .and []

def expandLet {scope : Nat} (binderType : Ty) (value : Term scope)
    (body : Term (scope + 1)) : Expansion scope := {
  term := apply (.lambda binderType body) [value]
  clauses := [.d44LetBeta] }

def expandSelectSome {scope : Nat} (property : Term scope) : Expansion scope := {
  term := primitive .selectAtLeast [.natural 1, property]
  clauses := [.d56SelectSomeAtLeastOne] }

def expandCoRef {scope : Nat} (first second : Term scope) : Expansion scope := {
  term := primitive .and [
    primitive .among [first, second],
    primitive .among [second, first]]
  clauses := [.d12CoRefMutualAmong] }

def expandOverlap {scope : Nat} (memberType : Ty)
    (first second : Term scope) : Expansion scope :=
  let first' := weaken first
  let second' := weaken second
  {
    term := primitive .exists [
      .lambda (Ty.referents memberType) <| primitive .and [
        primitive .among [.bound 0, first'],
        primitive .among [.bound 0, second']]]
    clauses := [.d12OverlapCommonSubreference] }

def expandDistrib {scope : Nat} (memberType : Ty)
    (property reference : Term scope) : Expansion scope :=
  let property' := weaken property
  let reference' := weaken reference
  {
    term := primitive .forall [
      .lambda memberType <| primitive .implies [
        primitive .among [.bound 0, reference'],
        apply property' [.bound 0]]]
    clauses := [.d12DistribUniversalMembers] }

def expandCoveredBy {scope : Nat} (memberType : Ty)
    (property reference : Term scope) : Expansion scope :=
  let distributed := (expandDistrib memberType property reference).term
  let propertyAtR2 := weaken property
  let referenceAtR2 := weaken reference
  let propertyAtX := weaken propertyAtR2
  let overlapAtX := (expandOverlap memberType (.bound 0) (.bound 1)).term
  let residue := primitive .forall [
    .lambda (Ty.referents memberType) <| primitive .implies [
      primitive .among [.bound 0, referenceAtR2],
      primitive .exists [
        .lambda memberType <| primitive .and [
          apply propertyAtX [.bound 0], overlapAtX]]]]
  {
    term := primitive .and [distributed, residue]
    clauses := [
      .d12DistribUniversalMembers,
      .d12OverlapCommonSubreference,
      .d48CoveredByNoResidue] }

def expandReferMember {scope : Nat} (memberType : Ty)
    (property : Term scope) : Expansion scope :=
  let property' := weaken property
  {
    term := primitive .refer [
      .lambda (Ty.referents memberType) <|
        (expandCoveredBy memberType property' (.bound 0)).term]
    clauses := [
      .d12DistribUniversalMembers,
      .d12OverlapCommonSubreference,
      .d48CoveredByNoResidue,
      .d53ReferMemberLiftMemberLift] }

def expandSome {scope : Nat} (memberType : Ty)
    (property nuclear : Term scope) : Expansion scope :=
  let selection := (expandSelectSome property).term
  {
    term := .bind (Ty.referents memberType) selection <|
      apply (weaken nuclear) [.bound 0]
    clauses := [.d56SelectSomeAtLeastOne, .d12SomeWitness] }

def expandNo {scope : Nat} (memberType : Ty)
    (property nuclear : Term scope) : Expansion scope := {
  term := primitive .not [(expandSome memberType property nuclear).term]
  clauses := [.d56SelectSomeAtLeastOne, .d12SomeWitness, .d12NoNegatedSome] }

def expandAtLeast {scope : Nat} (memberType : Ty)
    (count property nuclear : Term scope) : Expansion scope :=
  match count with
  | .natural 0 => { term := top, clauses := [.d12AtLeastZero] }
  | _ => {
      term := .bind (Ty.referents memberType)
        (primitive .selectAtLeast [count, property]) <|
        apply (weaken nuclear) [.bound 0]
      clauses := [.d12AtLeastPositive] }

def expandExactly {scope : Nat} (memberType : Ty)
    (count property nuclear : Term scope) : Expansion scope :=
  match count with
  | .natural 0 =>
      (expandNo memberType property nuclear).addClause .d12ExactlyZero
  | _ => {
      term := .bind (Ty.referents memberType)
        (primitive .selectExactly [count, property]) <|
        apply (weaken nuclear) [.bound 0]
      clauses := [.d12ExactlyPositive] }

def increment {scope : Nat} (count : Term scope) : Term scope :=
  primitive .add [count, .natural 1]

def expandAtMost {scope : Nat} (memberType : Ty)
    (count property nuclear : Term scope) : Expansion scope :=
  let expanded := expandAtLeast memberType (increment count) property nuclear
  { term := primitive .not [expanded.term]
    clauses := expanded.clauses ++ [.d12AtMostNegatedSuccessor] }

def expandMoreThan {scope : Nat} (memberType : Ty)
    (count property nuclear : Term scope) : Expansion scope :=
  (expandAtLeast memberType (increment count) property nuclear).addClause
    .d12MoreThanSuccessor

def expandFewerThan {scope : Nat} (memberType : Ty)
    (count property nuclear : Term scope) : Expansion scope :=
  let expanded := expandAtLeast memberType count property nuclear
  { term := primitive .not [expanded.term]
    clauses := expanded.clauses ++ [.d12FewerThanNegatedAtLeast] }

def expandMaxRefer {scope : Nat} (memberType : Ty)
    (property : Term scope) : Expansion scope :=
  let propertyAtReference := weaken property
  let covered := expandCoveredBy memberType propertyAtReference (.bound 0)
  let propertyAtMember := weaken propertyAtReference
  let maximal := primitive .forall [
    .lambda memberType <| primitive .implies [
      apply propertyAtMember [.bound 0],
      primitive .among [.bound 0, (.bound 1 : Term (scope + 2))]]]
  {
    term := primitive .presuppose [
      primitive .exists [property],
      primitive .refer [
        .lambda (Ty.referents memberType) <|
          primitive .and [covered.term, maximal]]]
    clauses := covered.clauses ++ [.d12MaxReferInhabitedMaximalReference] }

def expandEvery {scope : Nat} (memberType : Ty)
    (property nuclear : Term scope) : Expansion scope :=
  let maxReference := expandMaxRefer memberType property
  {
    term := .bind (Ty.referents memberType) maxReference.term <|
      (expandDistrib memberType (weaken nuclear) (.bound 0)).term
    clauses := maxReference.clauses ++
      [.d12DistribUniversalMembers, .d12EveryMaximalDistribution] }

def expandGlobalExactly {scope : Nat} (memberType : Ty)
    (count property nuclear : Term scope) : Expansion scope :=
  let property' := weaken property
  let nuclear' := weaken nuclear
  {
    term := primitive .equal [
      primitive .card [
        primitive .setOf [
          .lambda memberType <| primitive .and [
            apply property' [.bound 0], apply nuclear' [.bound 0]]]],
      count]
    clauses := [.d12GlobalExactlyComprehension] }

def expandActualClause {scope : Nat} (clause : Term scope) : Expansion scope :=
  let clause' := weaken clause
  {
    term := .lambda (Ty.referents Ty.eventuality) <| primitive .and [
      apply clause' [.bound 0],
      .lexical "fasnu" (termList [.bound 0])]
    clauses := [.d12ActualClauseActualEvent] }

def expandGunmaAt {scope : Nat} (_wholeType componentType : Ty)
    (basis whole cover : Term scope) : Expansion scope :=
  let basisAtUnit := weaken basis
  let wholeAtUnit := weaken whole
  let coverAtUnit := weaken cover
  let basisAtPeer := weaken basisAtUnit
  let wholeAtPeer := weaken wholeAtUnit
  let coReference := expandCoRef (first := (.bound 1 : Term (scope + 2)))
    (second := .bound 0)
  {
    term := primitive .forall [
      .lambda (Ty.referents componentType) <| primitive .implies [
        primitive .basisUnitAt [basisAtUnit, .bound 0, coverAtUnit],
        primitive .exists [
          .lambda (Ty.referents componentType) <| primitive .and [
            primitive .peerUnitAt [basisAtPeer, .bound 0, wholeAtPeer],
            coReference.term]]]]
    clauses := coReference.clauses ++ [.d49GunmaAtBasisToPeerCover] }

def expandCompleteGunmaAt {scope : Nat} (wholeType componentType : Ty)
    (basis whole cover : Term scope) : Expansion scope :=
  let forward := expandGunmaAt wholeType componentType basis whole cover
  let basisAtPeer := weaken basis
  let wholeAtPeer := weaken whole
  let coverAtPeer := weaken cover
  let basisAtUnit := weaken basisAtPeer
  let coverAtUnit := weaken coverAtPeer
  let coReference := expandCoRef (first := (.bound 0 : Term (scope + 2)))
    (second := .bound 1)
  let converse := primitive .forall [
    .lambda (Ty.referents componentType) <| primitive .implies [
      primitive .peerUnitAt [basisAtPeer, .bound 0, wholeAtPeer],
      primitive .exists [
        .lambda (Ty.referents componentType) <| primitive .and [
          primitive .basisUnitAt [basisAtUnit, .bound 0, coverAtUnit],
          coReference.term]]]]
  {
    term := primitive .and [forward.term, converse]
    clauses := forward.clauses ++ coReference.clauses ++
      [.d49CompleteGunmaAtCompletePeerCover] }

def expandCanonicalAggregateAt {scope : Nat} (componentType : Ty)
    (basis group cover : Term scope) : Expansion scope :=
  let complete := expandCompleteGunmaAt (Ty.group componentType) componentType
    basis group cover
  {
    term := primitive .and [
      primitive .aggregate [basis, group], complete.term]
    clauses := complete.clauses ++
      [.d12CanonicalAggregateAtAggregateAndCompleteGunma] }

def expandMassify {scope : Nat} (componentType : Ty)
    (basis cover : Term scope) : Expansion scope :=
  let canonical := expandCanonicalAggregateAt componentType
    (weaken basis) (.bound 0) (weaken cover)
  {
    term := primitive .selectExactly [
      .natural 1,
      .lambda (Ty.group componentType) canonical.term]
    clauses := canonical.clauses ++ [.d12MassifyCanonicalSelection] }

def expandZipWith {scope : Nat} (function : Term scope)
    (left right : List (Term scope)) : Except String (Expansion scope) :=
  match left, right with
  | [], [] => pure { term := top, clauses := [.d12ZipWithEmpty] }
  | firstLeft :: restLeft, firstRight :: restRight => do
      let recursive ← expandZipWith function restLeft restRight
      pure {
        term := primitive .and [
          apply function [firstLeft, firstRight], recursive.term]
        clauses := recursive.clauses ++ [.d12ZipWithPairedStep] }
  | _, _ => .error "ZipWith unequal-length domain is blocked by #41"

structure ExpansionKey where
  document : String
  occurrence : Nat
  definition : M2DefinitionId
  deriving Repr, DecidableEq, BEq

def ExpansionKey.site (key : ExpansionKey) (slot : Nat)
    (role : String) : SiteId := {
  document := key.document
  occurrence := key.occurrence
  expansionRole := key.definition.name ++ "/" ++ toString slot ++ "/" ++ role }

structure ExpansionSite where
  definition : M2DefinitionId
  role : String
  roleKind : SiteRole
  identity : SiteId
  dependencies : List SerializedDependency
  deriving Repr, DecidableEq, BEq

structure SiteExpansion (scope : Nat) extends Expansion scope where
  sites : List ExpansionSite

inductive CloseEventMode where
  | holdingState
  | directEvent
  deriving Repr, DecidableEq, BEq

structure ClosePlace (scope : Nat) where
  label : String
  type : Ty
  fill : Option (Term scope)
  deriving Repr

structure ClosePlan (scope : Nat) where
  predicate : Term scope
  places : List (ClosePlace scope)
  eventMode : CloseEventMode
  eventFill : Option (Term scope) := none
  deriving Repr

def renameLabelled {source target : Nat} (ρ : Renaming source target) :
    List (String × Term source) → List (String × Term target) :=
  List.map fun item => (item.1, item.2.rename ρ)

def applyLabelled {scope : Nat} (function : Term scope)
    (arguments : List (String × Term scope)) : Term scope :=
  if arguments.isEmpty then function
  else match function with
    | .lexical head existing =>
        .lexical head (existing.append (labelledTermList arguments))
    | _ => .apply function (labelledTermList arguments)

def bindClosePlaces {source target : Nat} (key : ExpansionKey)
    (slot : Nat) (ρ : Renaming source target)
    (places : List (ClosePlace source))
    (arguments suffix : List (String × Term target))
    (finish : ∀ {innerScope : Nat}, Renaming source innerScope →
      List (String × Term innerScope) →
      List (String × Term innerScope) → Term innerScope) : Term target :=
  match places with
  | [] => finish ρ arguments suffix
  | place :: rest =>
      match place.fill with
      | some value =>
          bindClosePlaces key slot ρ rest
            (arguments ++ [(place.label, value.rename ρ)]) suffix finish
      | none =>
          let site := key.site slot ("default-" ++ place.label)
          let lift : Renaming target (target + 1) := Fin.succ
          let inner := bindClosePlaces key (slot + 1)
            (fun index => lift (ρ index)) rest
            (renameLabelled lift arguments ++ [(place.label, .bound 0)])
            (renameLabelled lift suffix) finish
          .bind place.type (.context site .nil) inner

def closeExpansionSites {scope : Nat} (key : ExpansionKey) :
    Nat → List (ClosePlace scope) → List ExpansionSite
  | _, [] => []
  | slot, place :: rest =>
      match place.fill with
      | some _ => closeExpansionSites key slot rest
      | none =>
          { definition := .d46Close
            role := "default-" ++ place.label
            roleKind := .context
            identity := key.site slot ("default-" ++ place.label)
            dependencies := [] } ::
          closeExpansionSites key (slot + 1) rest

def expandDirectClause {scope : Nat} (key : ExpansionKey)
    (predicate : Term scope) (places : List (ClosePlace scope)) :
    SiteExpansion scope :=
  let body : Term (scope + 1) := bindClosePlaces key 0 Fin.succ places []
    [(":Eventuality", .bound 0)] fun ρ arguments suffix =>
      applyLabelled (predicate.rename ρ) (arguments ++ suffix)
  {
    term := .lambda (Ty.referents Ty.eventuality) body
    clauses := [.d46DirectClauseDefaultedEventProperty]
    sites := closeExpansionSites key 0 places }

def expandClose {scope : Nat} (key : ExpansionKey)
    (plan : ClosePlan scope) : Except String (SiteExpansion scope) :=
  match plan.eventMode, plan.eventFill with
  | .holdingState, none =>
      let term := bindClosePlaces key 0 (fun index => index) plan.places [] []
        fun ρ arguments _ =>
          let content := applyLabelled (plan.predicate.rename ρ) arguments
          let actual := expandActualClause (primitive .stateClause [content])
          primitive .closeClause [actual.term]
      pure {
        term
        clauses := [.d12ActualClauseActualEvent, .d46CloseHoldingState]
        sites := closeExpansionSites key 0 plan.places }
  | .directEvent, none =>
      let direct := expandDirectClause key plan.predicate plan.places
      let actual := expandActualClause direct.term
      pure {
        term := primitive .closeClause [actual.term]
        clauses := direct.clauses ++ actual.clauses ++
          [.d46CloseDirectEventImplicit]
        sites := direct.sites }
  | .directEvent, some supplied =>
      let direct := expandDirectClause key plan.predicate plan.places
      let actual := expandActualClause direct.term
      let actualAtEvent := apply (weaken actual.term) [weaken supplied]
      let sameEvent := (expandCoRef (first := (.bound 0 : Term (scope + 1)))
        (second := weaken supplied))
      pure {
        term := primitive .closeClause [
          .lambda (Ty.referents Ty.eventuality) <|
            primitive .and [sameEvent.term, actualAtEvent]]
        clauses := direct.clauses ++ actual.clauses ++ sameEvent.clauses ++
          [.d46CloseDirectEventExplicit]
        sites := direct.sites }
  | .holdingState, some _ =>
      .error "holding-state Close cannot carry an Eventuality fill"

structure DegreeField (scope : Nat) where
  relation : Term scope
  row : Ty
  projection : Term scope
  deriving Repr

structure GradePlan (scope : Nat) where
  degree : DegreeField scope
  scale : Term scope
  region : Term scope
  deriving Repr

def expandGrade {scope : Nat} (plan : GradePlan scope) : Expansion scope :=
  let amount := apply (weaken plan.degree.projection)
    [.bound 0, weaken plan.scale]
  {
    term := .lambda (Ty.record plan.degree.row) <|
      .lexical "InRegion" (termList [amount, weaken plan.region])
    clauses := [.d12GradeRowDirected] }

structure JaiRaisePlan (scope : Nat) where
  baseRow : Ty
  raisedRow : Ty
  relation : Term scope
  role : Term scope
  reconstructBase : Term scope
  raisedProjection : Term scope
  oldFirstProjection : Term scope
  deriving Repr

def expandJaiRaise {scope : Nat} (plan : JaiRaisePlan scope) : Expansion scope :=
  let record : Term (scope + 1) := .bound 0
  let baseRecord := apply (weaken plan.reconstructBase) [record]
  let raised := apply (weaken plan.raisedProjection) [record]
  let oldFirst := apply (weaken plan.oldFirstProjection) [record]
  {
    term := .lambda (Ty.record plan.raisedRow) <| primitive .and [
      apply (weaken plan.relation) [baseRecord],
      apply (weaken plan.role) [raised, oldFirst]]
    clauses := [.d12JaiRaiseRaisedRole] }

def expandBareJai {scope : Nat} (key : ExpansionKey)
    (relation : Term scope) (roleType : Ty)
    (continuation : Term (scope + 1)) : SiteExpansion scope :=
  let site := key.site 0 "raised-role-context"
  let constraint := .lambda roleType <| primitive .jaiRoleAdmissible [
    weaken relation, .bound 0]
  {
    term := .bind roleType (.context site (termList [constraint])) continuation
    clauses := [.d12JaiRaiseBareJaiMapping]
    sites := [{
      definition := .d12JaiRaise
      role := "raised-role-context"
      roleKind := .context
      identity := site
      dependencies := constraint.dependencies.map
        SerializedDependency.ofDependency }] }

def expandTooMany {scope : Nat} (memberType : Ty) (key : ExpansionKey)
    (property nuclear : Term scope) : SiteExpansion scope :=
  let purposeId := key.site 0 "purpose-context"
  let thresholdId := key.site 1 "threshold-vague"
  let propertyAtPurpose := weaken property
  let thresholdConstraint : Term (scope + 1) :=
    primitive .admissibleThreshold [
      primitive .tooManyK,
      propertyAtPurpose,
      .bound 0]
  let propertyAtThreshold := weaken propertyAtPurpose
  let nuclearAtThreshold := weakenN 2 nuclear
  let body := (expandMoreThan memberType (.bound 0)
    propertyAtThreshold nuclearAtThreshold).term
  {
    term := .bind (Ty.referents Ty.entity) (.context purposeId .nil) <|
      .bind Ty.natural (.vague thresholdId thresholdConstraint) body
    clauses := [.d12MoreThanSuccessor, .d12TooManyDependentThreshold]
    sites := [
      { definition := .d12TooMany
        role := "purpose-context"
        roleKind := .context
        identity := purposeId
        dependencies := [] },
      { definition := .d12TooMany
        role := "threshold-vague"
        roleKind := .vague
        identity := thresholdId
        dependencies := thresholdConstraint.dependencies.map
          SerializedDependency.ofDependency }] }

end M2
end SmusniPilot
