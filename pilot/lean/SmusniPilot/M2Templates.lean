import SmusniPilot.M2Typing

namespace SmusniPilot
namespace M2

def termList {scope : Nat} : List (Term scope) → TermList scope
  | [] => .nil
  | head :: tail => .positional head (termList tail)

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

def expandEvery {scope : Nat} (memberType : Ty)
    (_property nuclear maxReference : Term scope) : Expansion scope := {
  term := .bind (Ty.referents memberType) maxReference <|
    (expandDistrib memberType (weaken nuclear) (.bound 0)).term
  clauses := [.d12DistribUniversalMembers, .d12EveryMaximalDistribution] }

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
  occurrence := key.occurrence * 16 + slot
  expansionRole := key.definition.name ++ "/" ++ role }

structure ExpansionSite where
  definition : M2DefinitionId
  role : String
  identity : SiteId
  deriving Repr, DecidableEq, BEq

structure SiteExpansion (scope : Nat) extends Expansion scope where
  sites : List ExpansionSite

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
        identity := purposeId },
      { definition := .d12TooMany
        role := "threshold-vague"
        identity := thresholdId }] }

end M2
end SmusniPilot
