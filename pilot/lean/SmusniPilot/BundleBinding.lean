import SmusniPilot.Interchange
import SmusniPilot.BindingLaws

namespace SmusniPilot
namespace Interchange

structure ValidatedBundle (scope : Nat) where
  bundle : Bundle scope
  valid : bundle.validate = .ok ()
  deriving Repr

def Bundle.checked {scope : Nat} (bundle : Bundle scope) :
    Except String (ValidatedBundle scope) :=
  match evidence : bundle.validate with
  | .ok () => .ok { bundle, valid := evidence }
  | .error message => .error message

theorem ValidatedBundle.validate_ok {scope : Nat}
    (bundle : ValidatedBundle scope) :
    bundle.bundle.validate = .ok () :=
  bundle.valid

def shiftSerializedDependency (depth : Nat) :
    SerializedDependency → SerializedDependency
  | .bound index => .bound (index + depth)
  | .free identity => .free identity
  | .site identity => .site identity

def shiftSiteEntry (depth : Nat) (entry : SiteEntry) : SiteEntry :=
  { entry with
    dependencies := entry.dependencies.map (shiftSerializedDependency depth) }

def renameSerializedDependency {source target : Nat} (depth : Nat)
    (ρ : Renaming source target) :
    SerializedDependency → Except String SerializedDependency
  | .bound index =>
      if index < depth then pure (.bound index)
      else
        let outerIndex := index - depth
        if inBounds : outerIndex < source then
          pure (.bound ((ρ ⟨outerIndex, inBounds⟩).val + depth))
        else .error s!"bound dependency {index} is outside lifted source scope"
  | .free identity => pure (.free identity)
  | .site identity => pure (.site identity)

def renameSiteEntry {source target : Nat} (depth : Nat)
    (ρ : Renaming source target) (entry : SiteEntry) :
    Except String SiteEntry := do
  let dependencies ←
    entry.dependencies.mapM (renameSerializedDependency depth ρ)
  pure { entry with dependencies }

def serializedTermDependencyAtDepth {scope : Nat} (depth : Nat) :
    Dependency scope → SerializedDependency
  | .bound index => .bound (index.val + depth)
  | .free identity => .free identity
  | .site identity => .site identity

def substituteSerializedDependency {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target) :
    SerializedDependency → Except String (List SerializedDependency)
  | .bound index =>
      if index < depth then pure [.bound index]
      else
        let outerIndex := index - depth
        if inBounds : outerIndex < source then
          let replacement := (σ ⟨outerIndex, inBounds⟩).bundle.term
          pure <| replacement.dependencies.map
            (serializedTermDependencyAtDepth depth)
        else .error s!"bound dependency {index} is outside lifted source scope"
  | .free identity => pure [.free identity]
  | .site identity => pure [.site identity]

def substituteSerializedDependencies {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target) :
    List SerializedDependency → Except String (List SerializedDependency)
  | [] => pure []
  | dependency :: rest => do
      let first ← substituteSerializedDependency depth σ dependency
      let remaining ← substituteSerializedDependencies depth σ rest
      pure (first ++ remaining)

def substituteSiteEntry {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target) (entry : SiteEntry) :
    Except String SiteEntry := do
  let dependencies ← substituteSerializedDependencies depth σ
    entry.dependencies
  pure { entry with dependencies }

def siteUseDepth (outerScope : Nat) (use : SiteUse) : Except String Nat := do
  if outerScope <= use.scope then pure (use.scope - outerScope)
  else .error s!"site occurrence scope {use.scope} is below {outerScope}"

def renameEntryForUse {source target : Nat} (ρ : Renaming source target)
    (use : SiteUse) (entry : SiteEntry) : Except String SiteEntry := do
  let depth ← siteUseDepth source use
  renameSiteEntry depth ρ entry

def substituteEntryForUse {source target : Nat}
    (σ : Fin source → ValidatedBundle target)
    (use : SiteUse) (entry : SiteEntry) : Except String SiteEntry := do
  let depth ← siteUseDepth source use
  substituteSiteEntry depth σ entry

def consistentCandidate (identity : SiteId) :
    List SiteEntry → Except String SiteEntry
  | [] => .error s!"site table entry has no term occurrence: {repr identity}"
  | first :: rest =>
      if rest.any fun candidate => candidate != first then
        .error s!"shared site transforms inconsistently: {repr identity}"
      else pure first

def renameSiteTable {source target : Nat} (ρ : Renaming source target)
    (uses : List SiteUse) : List SiteEntry → Except String (List SiteEntry)
  | [] => pure []
  | entry :: rest => do
      let relevant := uses.filter fun use => use.identity == entry.identity
      let candidates ← relevant.mapM fun use =>
        renameEntryForUse ρ use entry
      let transformed ← consistentCandidate entry.identity candidates
      pure (transformed :: (← renameSiteTable ρ uses rest))

def substituteSiteTable {source target : Nat}
    (σ : Fin source → ValidatedBundle target) (uses : List SiteUse) :
    List SiteEntry → Except String (List SiteEntry)
  | [] => pure []
  | entry :: rest => do
      let relevant := uses.filter fun use => use.identity == entry.identity
      let candidates ← relevant.mapM fun use =>
        substituteEntryForUse σ use entry
      let transformed ← consistentCandidate entry.identity candidates
      pure (transformed :: (← substituteSiteTable σ uses rest))

def replacementSiteEntries {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (Nat × Nat) → Except String (List SiteEntry)
  | [] => pure []
  | (rawIndex, depth) :: rest => do
      if inBounds : rawIndex < source then
        let shifted := (σ ⟨rawIndex, inBounds⟩).bundle.sites.map
          (shiftSiteEntry depth)
        pure (shifted ++ (← replacementSiteEntries σ rest))
      else .error s!"substitution use {rawIndex} is outside source scope"

def replacementSourceNotes {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (Nat × Nat) → Except String (List SourceNote)
  | [] => pure []
  | (rawIndex, _depth) :: rest => do
      if inBounds : rawIndex < source then
        pure ((σ ⟨rawIndex, inBounds⟩).bundle.sourceMap ++
          (← replacementSourceNotes σ rest))
      else .error s!"substitution use {rawIndex} is outside source scope"

def dependencySubstitutionUse (source depth : Nat) :
    SerializedDependency → Except String (Option (Nat × Nat))
  | .bound index =>
      if index < depth then pure none
      else
        let outerIndex := index - depth
        if outerIndex < source then pure (some (outerIndex, depth))
        else .error s!"bound dependency {index} is outside lifted source scope"
  | .free _ | .site _ => pure none

def entrySubstitutionUses (source depth : Nat) (entry : SiteEntry) :
    Except String (List (Nat × Nat)) := do
  let uses ← entry.dependencies.mapM (dependencySubstitutionUse source depth)
  pure (uses.filterMap id)

def sidecarSubstitutionUses (source : Nat) (uses : List SiteUse) :
    List SiteEntry → Except String (List (Nat × Nat))
  | [] => pure []
  | entry :: rest => do
      let relevant := uses.filter fun use => use.identity == entry.identity
      let nested ← relevant.mapM fun use => do
        let depth ← siteUseDepth source use
        entrySubstitutionUses source depth entry
      pure (nested.flatten ++ (← sidecarSubstitutionUses source uses rest))

def insertSiteEntry (entries : List SiteEntry) (candidate : SiteEntry) :
    Except String (List SiteEntry) :=
  match entries.find? fun entry => entry.identity == candidate.identity with
  | none => pure (entries ++ [candidate])
  | some existing =>
      if existing == candidate then pure entries
      else .error s!"site table merge conflict: {repr candidate.identity}"

def mergeSiteEntries (candidates : List SiteEntry) :
    Except String (List SiteEntry) :=
  candidates.foldlM insertSiteEntry []

def Bundle.rename {source target : Nat} (bundle : Bundle source)
    (ρ : Renaming source target) : Except String (ValidatedBundle target) := do
  bundle.validate
  let sites ← renameSiteTable ρ bundle.term.siteUses bundle.sites
  let result : Bundle target :=
    { version := bundle.version
      term := bundle.term.rename ρ
      sites
      sourceMap := bundle.sourceMap }
  result.checked

def ValidatedBundle.rename {source target : Nat}
    (bundle : ValidatedBundle source) (ρ : Renaming source target) :
    Except String (ValidatedBundle target) :=
  bundle.bundle.rename ρ

def Bundle.weaken {scope : Nat} (bundle : Bundle scope) :
    Except String (ValidatedBundle (scope + 1)) :=
  bundle.rename Fin.succ

def ValidatedBundle.weaken {scope : Nat} (bundle : ValidatedBundle scope) :
    Except String (ValidatedBundle (scope + 1)) :=
  bundle.bundle.weaken

def Bundle.substitute {source target : Nat} (bundle : Bundle source)
    (σ : Fin source → ValidatedBundle target) :
    Except String (ValidatedBundle target) := do
  bundle.validate
  let originalSites ← substituteSiteTable σ bundle.term.siteUses bundle.sites
  let sidecarUses ←
    sidecarSubstitutionUses source bundle.term.siteUses bundle.sites
  let replacementSites ← replacementSiteEntries σ
    (bundle.term.substitutionUses ++ sidecarUses)
  let sites ← mergeSiteEntries (originalSites ++ replacementSites)
  let replacementNotes ← replacementSourceNotes σ
    (bundle.term.substitutionUses ++ sidecarUses)
  let result : Bundle target :=
    { version := bundle.version
      term := bundle.term.substitute fun index => (σ index).bundle.term
      sites
      sourceMap := bundle.sourceMap ++ replacementNotes }
  result.checked

def ValidatedBundle.substitute {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) :
    Except String (ValidatedBundle target) :=
  bundle.bundle.substitute σ

theorem Bundle.term_rename_preserves_site_ids {source target : Nat}
    (bundle : Bundle source) (ρ : Renaming source target) :
    (bundle.term.rename ρ).siteIds = bundle.term.siteIds :=
  Term.siteIds_rename ρ bundle.term

theorem Bundle.term_substitute_preserves_site_id {source target : Nat}
    (bundle : Bundle source) (σ : Fin source → ValidatedBundle target)
    (identity : SiteId) (present : identity ∈ bundle.term.siteIds) :
    identity ∈
      (bundle.term.substitute fun index => (σ index).bundle.term).siteIds :=
  Term.siteId_mem_substitute
    (fun index => (σ index).bundle.term) bundle.term identity present

theorem Bundle.rename_result_valid {source target : Nat}
    (bundle : Bundle source) (ρ : Renaming source target)
    (result : ValidatedBundle target) (_success : bundle.rename ρ = .ok result) :
    result.bundle.validate = .ok () := by
  exact result.valid

theorem Bundle.substitute_result_valid {source target : Nat}
    (bundle : Bundle source) (σ : Fin source → ValidatedBundle target)
    (result : ValidatedBundle target)
    (_success : bundle.substitute σ = .ok result) :
    result.bundle.validate = .ok () := by
  exact result.valid

end Interchange
end SmusniPilot
