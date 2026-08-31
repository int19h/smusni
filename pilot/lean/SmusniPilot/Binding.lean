import SmusniPilot.Core

namespace SmusniPilot

abbrev Renaming (source target : Nat) := Fin source → Fin target
abbrev Substitution (source target : Nat) := Fin source → Term target

namespace Renaming

def lift {source target : Nat}
    (ρ : Renaming source target) : Renaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (ρ index))

def liftN {source target : Nat} (ρ : Renaming source target) :
    (depth : Nat) → Renaming (source + depth) (target + depth)
  | 0 => ρ
  | depth + 1 => lift (liftN ρ depth)

def shiftN {scope : Nat} : (depth : Nat) → Renaming scope (scope + depth)
  | 0 => fun index => index
  | depth + 1 => fun index => Fin.succ (shiftN depth index)

end Renaming

def Dependency.rename {source target : Nat}
    (ρ : Renaming source target) : Dependency source → Dependency target
  | .bound index => .bound (ρ index)
  | .free identity => .free identity

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

mutual
  def Term.siteOccurrences {scope : Nat} : Term scope → List SiteOccurrence
    | .bound _ | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body => body.siteOccurrences
    | .bind _ computation body =>
        computation.siteOccurrences ++ body.siteOccurrences
    | .apply function arguments =>
        function.siteOccurrences ++ arguments.siteOccurrences
    | .lexical _ arguments | .primitive _ arguments =>
        arguments.siteOccurrences
    | .context site arguments =>
        { use := { identity := site, role := .context, scope }
          support := arguments.dependencies.map
            SerializedDependency.ofDependency } :: arguments.siteOccurrences
    | .vague site constraint =>
        { use := { identity := site, role := .vague, scope }
          support := constraint.dependencies.map
            SerializedDependency.ofDependency } :: constraint.siteOccurrences

  def TermList.siteOccurrences {scope : Nat} :
      TermList scope → List SiteOccurrence
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        head.siteOccurrences ++ tail.siteOccurrences
end

@[simp] theorem Term.siteOccurrences_uses {scope : Nat} (term : Term scope) :
    term.siteOccurrences.map SiteOccurrence.use = term.siteUses := by
  induction term using Term.rec
    (motive_2 := fun scope terms =>
      terms.siteOccurrences.map SiteOccurrence.use = terms.siteUses) <;>
    simp_all [Term.siteOccurrences, TermList.siteOccurrences,
      Term.siteUses, TermList.siteUses]

@[simp] theorem TermList.siteOccurrences_uses {scope : Nat}
    (terms : TermList scope) :
    terms.siteOccurrences.map SiteOccurrence.use = terms.siteUses := by
  induction terms using TermList.rec
    (motive_1 := fun scope term =>
      term.siteOccurrences.map SiteOccurrence.use = term.siteUses) <;>
    simp_all [Term.siteOccurrences, TermList.siteOccurrences,
      Term.siteUses, TermList.siteUses]

namespace Substitution

def lift {source target : Nat}
    (substitution : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.bound 0)
    (fun index => (substitution index).rename Fin.succ)

def identity {scope : Nat} : Substitution scope scope :=
  fun index => .bound index

def liftN {source target : Nat} (substitution : Substitution source target) :
    (depth : Nat) → Substitution (source + depth) (target + depth)
  | 0 => substitution
  | depth + 1 => lift (liftN substitution depth)

end Substitution

def Dependency.substitute {source target : Nat}
    (substitution : Substitution source target) :
    Dependency source → List (Dependency target)
  | .bound index => (substitution index).dependencies
  | .free identity => [.free identity]

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
