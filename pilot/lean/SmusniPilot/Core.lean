import SmusniPilot.Types

namespace SmusniPilot

mutual
  inductive Term : Nat → Type where
    | bound {scope : Nat} (index : Fin scope) : Term scope
    | free {scope : Nat} (identity : FreeId) : Term scope
    | natural {scope : Nat} (literal : Nat) : Term scope
    | lambda {scope : Nat} (binderType : Ty)
        (body : Term (scope + 1)) : Term scope
    | bind {scope : Nat} (binderType : Ty)
        (computation : Term scope) (body : Term (scope + 1)) : Term scope
    | apply {scope : Nat} (function argument : Term scope) : Term scope
    | lexical {scope : Nat} (predicate : String)
        (arguments : TermList scope) : Term scope
    | context {scope : Nat} (site : Site scope)
        (arguments : TermList scope) : Term scope
    | vague {scope : Nat} (site : Site scope)
        (constraint : Term scope) : Term scope
    | primitive {scope : Nat} (operator : Primitive)
        (arguments : TermList scope) : Term scope
    deriving Repr

  inductive TermList : Nat → Type where
    | nil {scope : Nat} : TermList scope
    | cons {scope : Nat} (head : Term scope)
        (tail : TermList scope) : TermList scope
    deriving Repr
end

namespace TermList

def append {scope : Nat} : TermList scope → TermList scope → TermList scope
  | .nil, second => second
  | .cons head tail, second => .cons head (append tail second)

def length {scope : Nat} : TermList scope → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1

def toList {scope : Nat} : TermList scope → List (Term scope)
  | .nil => []
  | .cons head tail => head :: tail.toList

end TermList

mutual
  def Term.siteIds {scope : Nat} : Term scope → List SiteId
    | .bound _ | .free _ | .natural _ => []
    | .lambda _ body => body.siteIds
    | .bind _ computation body => computation.siteIds ++ body.siteIds
    | .apply function argument => function.siteIds ++ argument.siteIds
    | .lexical _ arguments => arguments.siteIds
    | .context site arguments => site.identity :: arguments.siteIds
    | .vague site constraint => site.identity :: constraint.siteIds
    | .primitive _ arguments => arguments.siteIds

  def TermList.siteIds {scope : Nat} : TermList scope → List SiteId
    | .nil => []
    | .cons head tail => head.siteIds ++ tail.siteIds
end

mutual
  def Term.freeIds {scope : Nat} : Term scope → List FreeId
    | .bound _ | .natural _ => []
    | .free identity => [identity]
    | .lambda _ body => body.freeIds
    | .bind _ computation body => computation.freeIds ++ body.freeIds
    | .apply function argument => function.freeIds ++ argument.freeIds
    | .lexical _ arguments => arguments.freeIds
    | .context site arguments =>
        site.dependencies.flatMap (fun
          | .free identity => [identity]
          | _ => []) ++ arguments.freeIds
    | .vague site constraint =>
        site.dependencies.flatMap (fun
          | .free identity => [identity]
          | _ => []) ++ constraint.freeIds
    | .primitive _ arguments => arguments.freeIds

  def TermList.freeIds {scope : Nat} : TermList scope → List FreeId
    | .nil => []
    | .cons head tail => head.freeIds ++ tail.freeIds
end

end SmusniPilot
