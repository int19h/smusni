import SmusniPilot.Core

namespace SmusniPilot

abbrev Renaming (source target : Nat) := Fin source → Fin target
abbrev Substitution (source target : Nat) := Fin source → Term target

namespace Renaming

def lift {source target : Nat}
    (ρ : Renaming source target) : Renaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (ρ index))

end Renaming

def Dependency.rename {source target : Nat}
    (ρ : Renaming source target) : Dependency source → Dependency target
  | .bound index => .bound (ρ index)
  | .free identity => .free identity
  | .site identity => .site identity

def Site.rename {source target : Nat}
    (ρ : Renaming source target) (site : Site source) : Site target :=
  { site with dependencies := site.dependencies.map (Dependency.rename ρ) }

mutual
  def Term.rename {source target : Nat}
      (ρ : Renaming source target) : Term source → Term target
    | .bound index => .bound (ρ index)
    | .free identity => .free identity
    | .natural literal => .natural literal
    | .string literal => .string literal
    | .index literal => .index literal
    | .lambda binderType body =>
        .lambda binderType (body.rename (Renaming.lift ρ))
    | .bind binderType computation body =>
        .bind binderType (computation.rename ρ)
          (body.rename (Renaming.lift ρ))
    | .apply function arguments =>
        .apply (function.rename ρ) (arguments.rename ρ)
    | .lexical predicate arguments =>
        .lexical predicate (arguments.rename ρ)
    | .context site arguments => .context site (arguments.rename ρ)
    | .vague site constraint => .vague site (constraint.rename ρ)
    | .primitive operator arguments =>
        .primitive operator (arguments.rename ρ)

  def TermList.rename {source target : Nat}
      (ρ : Renaming source target) : TermList source → TermList target
    | .nil => .nil
    | .positional head tail => .positional (head.rename ρ) (tail.rename ρ)
    | .labelled label head tail =>
        .labelled label (head.rename ρ) (tail.rename ρ)
end

mutual
  def Dependency.lower {scope : Nat} :
      Dependency (scope + 1) → Option (Dependency scope)
    | .bound index =>
        Fin.cases Option.none (fun predecessor => Option.some (.bound predecessor)) index
    | .free identity => Option.some (.free identity)
    | .site identity => Option.some (.site identity)

  def Term.dependencies {scope : Nat} : Term scope → List (Dependency scope)
    | .bound index => [.bound index]
    | .free identity => [.free identity]
    | .natural _ | .string _ | .index _ => []
    | .lambda _ body => body.dependencies.filterMap Dependency.lower
    | .bind _ computation body =>
        computation.dependencies ++ body.dependencies.filterMap Dependency.lower
    | .apply function arguments => function.dependencies ++ arguments.dependencies
    | .lexical _ arguments => arguments.dependencies
    | .context _ arguments => arguments.dependencies
    | .vague _ constraint => constraint.dependencies
    | .primitive _ arguments => arguments.dependencies

  def TermList.dependencies {scope : Nat} :
      TermList scope → List (Dependency scope)
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.dependencies ++ tail.dependencies
end

namespace Substitution

def lift {source target : Nat}
    (substitution : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.bound 0)
    (fun index => (substitution index).rename Fin.succ)

def identity {scope : Nat} : Substitution scope scope :=
  fun index => .bound index

end Substitution

def Dependency.substitute {source target : Nat}
    (substitution : Substitution source target) :
    Dependency source → List (Dependency target)
  | .bound index => (substitution index).dependencies
  | .free identity => [.free identity]
  | .site identity => [.site identity]

def Site.substitute {source target : Nat}
    (substitution : Substitution source target) (site : Site source) : Site target :=
  { site with
    dependencies := site.dependencies.flatMap (Dependency.substitute substitution) }

mutual
  def Term.substitute {source target : Nat}
      (substitution : Substitution source target) : Term source → Term target
    | .bound index => substitution index
    | .free identity => .free identity
    | .natural literal => .natural literal
    | .string literal => .string literal
    | .index literal => .index literal
    | .lambda binderType body =>
        .lambda binderType (body.substitute (Substitution.lift substitution))
    | .bind binderType computation body =>
        .bind binderType (computation.substitute substitution)
          (body.substitute (Substitution.lift substitution))
    | .apply function arguments =>
        .apply (function.substitute substitution)
          (arguments.substitute substitution)
    | .lexical predicate arguments =>
        .lexical predicate (arguments.substitute substitution)
    | .context site arguments =>
        .context site (arguments.substitute substitution)
    | .vague site constraint =>
        .vague site (constraint.substitute substitution)
    | .primitive operator arguments =>
        .primitive operator (arguments.substitute substitution)

  def TermList.substitute {source target : Nat}
      (substitution : Substitution source target) :
      TermList source → TermList target
    | .nil => .nil
    | .positional head tail =>
        .positional (head.substitute substitution) (tail.substitute substitution)
    | .labelled label head tail =>
        .labelled label (head.substitute substitution)
          (tail.substitute substitution)
end

def Term.weaken {scope : Nat} (term : Term scope) : Term (scope + 1) :=
  term.rename Fin.succ

end SmusniPilot
