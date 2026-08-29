import SmusniPilot.Interchange

namespace SmusniPilot
namespace Interchange

/-!
`TermDatum` is the typed structured interchange layer.  The text reader is an
untrusted byte boundary; it must produce this shape before a scoped term is
accepted.  Unlike a wrapper carrying the original term, this datatype is an
independent recursive representation with its own conversion functions.
-/

mutual
  inductive TermDatum : Nat → Type where
    | bound {scope : Nat} (index : Fin scope) : TermDatum scope
    | free {scope : Nat} (identity : FreeId) : TermDatum scope
    | natural {scope : Nat} (literal : Nat) : TermDatum scope
    | string {scope : Nat} (literal : String) : TermDatum scope
    | index {scope : Nat} (literal : String) : TermDatum scope
    | lambda {scope : Nat} (binderType : Ty)
        (body : TermDatum (scope + 1)) : TermDatum scope
    | bind {scope : Nat} (binderType : Ty)
        (computation : TermDatum scope)
        (body : TermDatum (scope + 1)) : TermDatum scope
    | apply {scope : Nat} (function : TermDatum scope)
        (arguments : TermDatumList scope) : TermDatum scope
    | lexical {scope : Nat} (predicate : String)
        (arguments : TermDatumList scope) : TermDatum scope
    | context {scope : Nat} (site : SiteId)
        (arguments : TermDatumList scope) : TermDatum scope
    | vague {scope : Nat} (site : SiteId)
        (constraint : TermDatum scope) : TermDatum scope
    | primitive {scope : Nat} (operator : FirstOrderPrimitive)
        (arguments : TermDatumList scope) : TermDatum scope
    deriving Repr

  inductive TermDatumList : Nat → Type where
    | nil {scope : Nat} : TermDatumList scope
    | positional {scope : Nat} (head : TermDatum scope)
        (tail : TermDatumList scope) : TermDatumList scope
    | labelled {scope : Nat} (label : String) (head : TermDatum scope)
        (tail : TermDatumList scope) : TermDatumList scope
    deriving Repr
end

mutual
  def TermDatum.ofTerm {scope : Nat} : Term scope → TermDatum scope
    | .bound index => .bound index
    | .free identity => .free identity
    | .natural literal => .natural literal
    | .string literal => .string literal
    | .index literal => .index literal
    | .lambda binderType body => .lambda binderType (TermDatum.ofTerm body)
    | .bind binderType computation body =>
        .bind binderType (TermDatum.ofTerm computation) (TermDatum.ofTerm body)
    | .apply function arguments =>
        .apply (TermDatum.ofTerm function) (TermDatumList.ofTerms arguments)
    | .lexical predicate arguments =>
        .lexical predicate (TermDatumList.ofTerms arguments)
    | .context site arguments =>
        .context site (TermDatumList.ofTerms arguments)
    | .vague site constraint => .vague site (TermDatum.ofTerm constraint)
    | .primitive operator arguments =>
        .primitive operator (TermDatumList.ofTerms arguments)

  def TermDatumList.ofTerms {scope : Nat} :
      TermList scope → TermDatumList scope
    | .nil => .nil
    | .positional head tail =>
        .positional (TermDatum.ofTerm head) (TermDatumList.ofTerms tail)
    | .labelled label head tail =>
        .labelled label (TermDatum.ofTerm head) (TermDatumList.ofTerms tail)
end

mutual
  def TermDatum.toTerm {scope : Nat} : TermDatum scope → Term scope
    | .bound index => .bound index
    | .free identity => .free identity
    | .natural literal => .natural literal
    | .string literal => .string literal
    | .index literal => .index literal
    | .lambda binderType body => .lambda binderType (TermDatum.toTerm body)
    | .bind binderType computation body =>
        .bind binderType (TermDatum.toTerm computation) (TermDatum.toTerm body)
    | .apply function arguments =>
        .apply (TermDatum.toTerm function) (TermDatumList.toTerms arguments)
    | .lexical predicate arguments =>
        .lexical predicate (TermDatumList.toTerms arguments)
    | .context site arguments =>
        .context site (TermDatumList.toTerms arguments)
    | .vague site constraint => .vague site (TermDatum.toTerm constraint)
    | .primitive operator arguments =>
        .primitive operator (TermDatumList.toTerms arguments)

  def TermDatumList.toTerms {scope : Nat} :
      TermDatumList scope → TermList scope
    | .nil => .nil
    | .positional head tail =>
        .positional (TermDatum.toTerm head) (TermDatumList.toTerms tail)
    | .labelled label head tail =>
        .labelled label (TermDatum.toTerm head) (TermDatumList.toTerms tail)
end

@[simp] theorem TermDatum.toTerm_ofTerm {scope : Nat} (term : Term scope) :
    (TermDatum.ofTerm term).toTerm = term := by
  induction term using Term.rec
    (motive_2 := fun scope terms =>
      (TermDatumList.ofTerms terms).toTerms = terms) <;>
    simp_all [TermDatum.ofTerm, TermDatumList.ofTerms,
      TermDatum.toTerm, TermDatumList.toTerms]

@[simp] theorem TermDatumList.toTerms_ofTerms {scope : Nat}
    (terms : TermList scope) :
    (TermDatumList.ofTerms terms).toTerms = terms := by
  induction terms using TermList.rec
    (motive_1 := fun scope term =>
      (TermDatum.ofTerm term).toTerm = term) <;>
    simp_all [TermDatum.ofTerm, TermDatumList.ofTerms,
      TermDatum.toTerm, TermDatumList.toTerms]

structure BundleDatum (scope : Nat) where
  version : Nat
  term : TermDatum scope
  sites : List SiteEntry
  sourceMap : List SourceNote
  deriving Repr

def BundleDatum.ofBundle {scope : Nat} (bundle : Bundle scope) :
    BundleDatum scope :=
  { version := bundle.version
    term := .ofTerm bundle.term
    sites := bundle.sites
    sourceMap := bundle.sourceMap }

def BundleDatum.toBundle {scope : Nat} (datum : BundleDatum scope) :
    Bundle scope :=
  { version := datum.version
    term := datum.term.toTerm
    sites := datum.sites
    sourceMap := datum.sourceMap }

theorem BundleDatum.toBundle_ofBundle {scope : Nat} (bundle : Bundle scope) :
    (BundleDatum.ofBundle bundle).toBundle = bundle := by
  cases bundle
  simp [BundleDatum.ofBundle, BundleDatum.toBundle]

end Interchange
end SmusniPilot
