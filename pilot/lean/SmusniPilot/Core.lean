import SmusniPilot.Types

namespace SmusniPilot

mutual
  inductive Term : Nat → Type where
    | bound {scope : Nat} (index : Fin scope) : Term scope
    | free {scope : Nat} (identity : FreeId) : Term scope
    | natural {scope : Nat} (literal : Nat) : Term scope
    | string {scope : Nat} (literal : String) : Term scope
    | index {scope : Nat} (literal : String) : Term scope
    | lambda {scope : Nat} (binderType : Ty)
        (body : Term (scope + 1)) : Term scope
    | bind {scope : Nat} (binderType : Ty)
        (computation : Term scope) (body : Term (scope + 1)) : Term scope
    | apply {scope : Nat} (function : Term scope)
        (arguments : TermList scope) : Term scope
    | lexical {scope : Nat} (predicate : String)
        (arguments : TermList scope) : Term scope
    | context {scope : Nat} (site : SiteId)
        (arguments : TermList scope) : Term scope
    | vague {scope : Nat} (site : SiteId)
        (constraint : Term scope) : Term scope
    | primitive {scope : Nat} (operator : FirstOrderPrimitive)
        (arguments : TermList scope) : Term scope
    deriving Repr

  inductive TermList : Nat → Type where
    | nil {scope : Nat} : TermList scope
    | positional {scope : Nat} (head : Term scope)
        (tail : TermList scope) : TermList scope
    | labelled {scope : Nat} (label : String) (head : Term scope)
        (tail : TermList scope) : TermList scope
    deriving Repr
end

structure SiteUse where
  identity : SiteId
  role : SiteRole
  scope : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

mutual
  def Term.siteUses {scope : Nat} : Term scope → List SiteUse
    | .bound _ | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body => body.siteUses
    | .bind _ computation body => computation.siteUses ++ body.siteUses
    | .apply function arguments => function.siteUses ++ arguments.siteUses
    | .lexical _ arguments => arguments.siteUses
    | .context site arguments =>
        { identity := site, role := .context, scope } :: arguments.siteUses
    | .vague site constraint =>
        { identity := site, role := .vague, scope } :: constraint.siteUses
    | .primitive _ arguments => arguments.siteUses

  def TermList.siteUses {scope : Nat} : TermList scope → List SiteUse
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.siteUses ++ tail.siteUses
end

namespace TermList

def append {scope : Nat} : TermList scope → TermList scope → TermList scope
  | .nil, second => second
  | .positional head tail, second => .positional head (append tail second)
  | .labelled label head tail, second =>
      .labelled label head (append tail second)

def length {scope : Nat} : TermList scope → Nat
  | .nil => 0
  | .positional _ tail | .labelled _ _ tail => tail.length + 1

def toList {scope : Nat} : TermList scope → List (Term scope)
  | .nil => []
  | .positional head tail | .labelled _ head tail => head :: tail.toList

end TermList

mutual
  def Term.siteIds {scope : Nat} : Term scope → List SiteId
    | .bound _ | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body => body.siteIds
    | .bind _ computation body => computation.siteIds ++ body.siteIds
    | .apply function arguments => function.siteIds ++ arguments.siteIds
    | .lexical _ arguments => arguments.siteIds
    | .context site arguments => site :: arguments.siteIds
    | .vague site constraint => site :: constraint.siteIds
    | .primitive _ arguments => arguments.siteIds

  def TermList.siteIds {scope : Nat} : TermList scope → List SiteId
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.siteIds ++ tail.siteIds
end

mutual
  def Term.freeIds {scope : Nat} : Term scope → List FreeId
    | .bound _ | .natural _ | .string _ | .index _ => []
    | .free identity => [identity]
    | .lambda _ body => body.freeIds
    | .bind _ computation body => computation.freeIds ++ body.freeIds
    | .apply function arguments => function.freeIds ++ arguments.freeIds
    | .lexical _ arguments => arguments.freeIds
    | .context _ arguments => arguments.freeIds
    | .vague _ constraint => constraint.freeIds
    | .primitive _ arguments => arguments.freeIds

  def TermList.freeIds {scope : Nat} : TermList scope → List FreeId
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.freeIds ++ tail.freeIds
end

mutual
  def Term.siteScopes {scope : Nat} : Term scope → List (SiteId × Nat)
    | .bound _ | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body => body.siteScopes
    | .bind _ computation body => computation.siteScopes ++ body.siteScopes
    | .apply function arguments => function.siteScopes ++ arguments.siteScopes
    | .lexical _ arguments => arguments.siteScopes
    | .context site arguments => (site, scope) :: arguments.siteScopes
    | .vague site constraint => (site, scope) :: constraint.siteScopes
    | .primitive _ arguments => arguments.siteScopes

  def TermList.siteScopes {scope : Nat} : TermList scope → List (SiteId × Nat)
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.siteScopes ++ tail.siteScopes
end

mutual
  def Term.substitutionUsesAt {scope : Nat} (depth : Nat) :
      Term scope → List (Nat × Nat)
    | .bound index =>
        if index.val < depth then [] else [(index.val - depth, depth)]
    | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body => body.substitutionUsesAt (depth + 1)
    | .bind _ computation body =>
        computation.substitutionUsesAt depth ++
          body.substitutionUsesAt (depth + 1)
    | .apply function arguments =>
        function.substitutionUsesAt depth ++
          arguments.substitutionUsesAt depth
    | .lexical _ arguments | .context _ arguments | .primitive _ arguments =>
        arguments.substitutionUsesAt depth
    | .vague _ constraint => constraint.substitutionUsesAt depth

  def TermList.substitutionUsesAt {scope : Nat} (depth : Nat) :
      TermList scope → List (Nat × Nat)
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.substitutionUsesAt depth ++ tail.substitutionUsesAt depth
end

def Term.substitutionUses {scope : Nat} (term : Term scope) :
    List (Nat × Nat) :=
  term.substitutionUsesAt 0

end SmusniPilot
