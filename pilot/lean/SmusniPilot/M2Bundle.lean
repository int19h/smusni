import SmusniPilot.M2Relation

namespace SmusniPilot
namespace M2

def allocationEntry (rrLink : Option String) (site : ExpansionSite) : SiteEntry := {
  identity := site.identity
  role := site.roleKind
  dependencies := site.dependencies
  rrLink }

def buildElaborationBundle {scope : Nat} (term : Term scope)
    (rrMetadata : List SiteEntry) (allocation : List ExpansionSite)
    (sourceMap : List Interchange.SourceNote) (rrLink : Option String := none) :
    Except String (Interchange.ValidatedBundle scope) := do
  let allocated := allocation.map (allocationEntry rrLink)
  let raw : Interchange.Bundle scope := {
    version := 1
    term
    sites := rrMetadata ++ allocated
    sourceMap }
  raw.checked

def emittedSiteSignature {scope : Nat} (term : Term scope) :
    List (SiteRole × Nat × List SerializedDependency) :=
  term.siteOccurrences.map fun occurrence =>
    (occurrence.use.role, occurrence.use.scope, occurrence.support)

def rrDeclarations (metadata : List SiteEntry) : List SiteEntry :=
  metadata.filter fun entry => entry.rrLink.isSome

def rrDeclarationAgreement {scope : Nat} (term : Term scope)
    (metadata : List SiteEntry) : Bool :=
  (rrDeclarations metadata).all fun entry =>
    term.siteOccurrences.any fun occurrence =>
      occurrence.use.identity == entry.identity &&
        occurrence.use.role == entry.role && occurrence.support == entry.dependencies

theorem expansion_site_alpha_invariant {source target : Nat}
    (term : Term source) (ρ : Renaming source target) :
    (term.rename ρ).siteIds = term.siteIds :=
  Term.siteIds_rename ρ term

theorem ExpansionKey.site_occurrence (key : ExpansionKey) (slot : Nat)
    (role : String) : (key.site slot role).occurrence = key.occurrence := rfl

theorem ExpansionKey.site_ne_of_occurrence (first second : ExpansionKey)
    (different : first.occurrence ≠ second.occurrence) (firstSlot secondSlot : Nat)
    (firstRole secondRole : String) :
    first.site firstSlot firstRole ≠ second.site secondSlot secondRole := by
  intro equal
  apply different
  exact congrArg SiteId.occurrence equal

end M2
end SmusniPilot
