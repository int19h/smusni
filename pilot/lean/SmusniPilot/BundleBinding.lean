import SmusniPilot.Interchange
import SmusniPilot.BindingLaws

namespace SmusniPilot
namespace Interchange

structure ScopedSiteUse (scope : Nat) (raw : SiteUse) where
  depth : Nat
  scopeEq : raw.scope = scope + depth
  entry : SiteEntry
  entryIdentity : entry.identity = raw.identity
  entryRole : entry.role = raw.role
  site : Site (scope + depth)
  siteIdentity : site.identity = entry.identity
  siteRole : site.role = entry.role

structure ScopedSiteClosure (scope : Nat) (uses : List SiteUse) where
  entries : List (Sigma fun raw => ScopedSiteUse scope raw)
  coverage : entries.map Sigma.fst = uses

def buildScopedSiteUse {scope : Nat} (bundle : Bundle scope) (raw : SiteUse) :
    Except String (ScopedSiteUse scope raw) := do
  if below : scope <= raw.scope then
    let depth := raw.scope - scope
    have scopeEq : raw.scope = scope + depth := by omega
    match lookup : bundle.sites.find? (fun candidate =>
        candidate.identity == raw.identity) with
    | none => .error s!"missing site sidecar entry: {repr raw.identity}"
    | some entry =>
        if identityMatches : entry.identity = raw.identity then
          if roleMatches : entry.role = raw.role then
            match deserialized : SiteEntry.toSite (scope + depth) entry with
            | .error message => .error message
            | .ok site => pure {
                depth := depth
                scopeEq := scopeEq
                entry := entry
                entryIdentity := identityMatches
                entryRole := roleMatches
                site := site
                siteIdentity := SiteEntry.toSite_preserves_identity
                  entry site deserialized
                siteRole := SiteEntry.toSite_preserves_role
                  entry site deserialized }
          else .error s!"site role conflicts with occurrence: {repr raw.identity}"
        else .error s!"site lookup identity mismatch: {repr raw.identity}"
  else .error s!"site occurrence scope {raw.scope} is below {scope}"

def buildScopedSiteClosure {scope : Nat} (bundle : Bundle scope) :
    (uses : List SiteUse) → Except String (ScopedSiteClosure scope uses)
  | [] => pure { entries := [], coverage := rfl }
  | use :: rest => do
      let first ← buildScopedSiteUse bundle use
      let remaining ← buildScopedSiteClosure bundle rest
      pure {
        entries := ⟨use, first⟩ :: remaining.entries
        coverage := by simp [remaining.coverage] }

structure TypedSubstitutionUse (source : Nat) where
  index : Fin source
  depth : Nat
  deriving Repr

mutual
  def typedTermSubstitutionUsesAt {scope : Nat} (source depth : Nat)
      (scopeEq : scope = source + depth) :
      Term scope → List (TypedSubstitutionUse source)
    | .bound index =>
        if isLocal : index.val < depth then []
        else
          have outer : index.val - depth < source := by omega
          [{ index := ⟨index.val - depth, outer⟩, depth }]
    | .free _ | .natural _ | .string _ | .index _ => []
    | .lambda _ body =>
        have bodyEq : scope + 1 = source + (depth + 1) := by omega
        typedTermSubstitutionUsesAt source (depth + 1) bodyEq body
    | .bind _ computation body =>
        typedTermSubstitutionUsesAt source depth scopeEq computation ++
          have bodyEq : scope + 1 = source + (depth + 1) := by omega
          typedTermSubstitutionUsesAt source (depth + 1) bodyEq body
    | .apply function arguments =>
        typedTermSubstitutionUsesAt source depth scopeEq function ++
          typedTermListSubstitutionUsesAt source depth scopeEq arguments
    | .lexical _ arguments | .context _ arguments | .primitive _ arguments =>
        typedTermListSubstitutionUsesAt source depth scopeEq arguments
    | .vague _ constraint =>
        typedTermSubstitutionUsesAt source depth scopeEq constraint

  def typedTermListSubstitutionUsesAt {scope : Nat} (source depth : Nat)
      (scopeEq : scope = source + depth) :
      TermList scope → List (TypedSubstitutionUse source)
    | .nil => []
    | .positional head tail | .labelled _ head tail =>
        typedTermSubstitutionUsesAt source depth scopeEq head ++
          typedTermListSubstitutionUsesAt source depth scopeEq tail
end

def typedTermSubstitutionUses {scope : Nat} (term : Term scope) :
    List (TypedSubstitutionUse scope) :=
  typedTermSubstitutionUsesAt scope 0 rfl term

def dependencyTypedSubstitutionUse {source depth : Nat} :
    Dependency (source + depth) → Option (TypedSubstitutionUse source)
  | .bound index =>
      if isLocal : index.val < depth then none
      else
        have outer : index.val - depth < source := by omega
        some { index := ⟨index.val - depth, outer⟩, depth }
  | .free _ | .site _ => none

def ScopedSiteUse.typedSubstitutionUses {source : Nat}
    {raw : SiteUse} (use : ScopedSiteUse source raw) :
    List (TypedSubstitutionUse source) :=
  use.site.dependencies.filterMap dependencyTypedSubstitutionUse

structure ValidatedBundle (scope : Nat) where
  private mk ::
  bundle : Bundle scope
  uses : List SiteUse
  closure : ScopedSiteClosure scope uses

structure SiteEntryConflict where
  identity : SiteId
  first : SiteEntry
  second : SiteEntry
  unequal : first ≠ second

inductive BundleBindingConflict where
  | inconsistentSharing (witness : SiteEntryConflict)

def BundleBindingConflict.message : BundleBindingConflict → String
  | .inconsistentSharing witness =>
      s!"bundle-binding inconsistent-sharing conflict at {repr witness.identity}: " ++
        s!"{repr witness.first} versus {repr witness.second}"

theorem BundleBindingConflict.has_unequal_candidates
    (conflict : BundleBindingConflict) :
    ∃ witness, conflict = .inconsistentSharing witness ∧
      witness.first ≠ witness.second := by
  cases conflict with
  | inconsistentSharing witness =>
      exact ⟨witness, rfl, witness.unequal⟩

def Bundle.checked {scope : Nat} (bundle : Bundle scope) :
    Except String (ValidatedBundle scope) :=
  match bundle.validateWithUses with
  | .ok uses => do
      let closure ← buildScopedSiteClosure bundle uses
      .ok {
        bundle
        uses
        closure }
  | .error message => .error message

@[simp] theorem toDependency_ofDependency {scope : Nat}
    (dependency : Dependency scope) :
    SerializedDependency.toDependency scope
      (SerializedDependency.ofDependency dependency) = .ok dependency := by
  cases dependency with
  | bound index =>
      simp only [SerializedDependency.ofDependency,
        SerializedDependency.toDependency]
      rw [dif_pos index.isLt]
      change Except.ok (Dependency.bound ⟨index.val, _⟩) =
        Except.ok (Dependency.bound index)
      congr
  | free _ => rfl
  | site _ => rfl

@[simp] theorem mapM_toDependency_ofDependency {scope : Nat}
    (dependencies : List (Dependency scope)) :
    (dependencies.map SerializedDependency.ofDependency).mapM
      (SerializedDependency.toDependency scope) = .ok dependencies := by
  induction dependencies with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.mapM_cons,
        toDependency_ofDependency]
      rw [ih]
      rfl

@[simp] theorem siteEntryToSite_ofSite {scope : Nat} (site : Site scope) :
    SiteEntry.toSite scope (SiteEntry.ofSite site) = .ok site := by
  cases site with
  | mk identity role dependencies rrLink =>
      unfold SiteEntry.toSite SiteEntry.ofSite
      rw [mapM_toDependency_ofDependency]
      rfl

def renameTypedSite {source target : Nat} (depth : Nat)
    (ρ : Renaming source target) (site : Site (source + depth)) :
    Site (target + depth) :=
  site.rename (Renaming.liftN ρ depth)

def substituteTypedSite {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target)
    (site : Site (source + depth)) : Site (target + depth) :=
  site.substitute <| Substitution.liftN
    (fun index => (σ index).bundle.term) depth

def shiftTypedSite {scope : Nat} (depth : Nat) (site : Site scope) :
    Site (scope + depth) :=
  site.rename (Renaming.shiftN depth)

@[simp] theorem renameTypedSite_preserves_identity {source target : Nat}
    (depth : Nat) (ρ : Renaming source target)
    (site : Site (source + depth)) :
    (renameTypedSite depth ρ site).identity = site.identity := rfl

@[simp] theorem substituteTypedSite_preserves_identity {source target : Nat}
    (depth : Nat) (σ : Fin source → ValidatedBundle target)
    (site : Site (source + depth)) :
    (substituteTypedSite depth σ site).identity = site.identity := rfl

@[simp] theorem shiftTypedSite_preserves_identity {scope : Nat}
    (depth : Nat) (site : Site scope) :
    (shiftTypedSite depth site).identity = site.identity := rfl

theorem renameTypedSite_dependencies {source target : Nat} (depth : Nat)
    (ρ : Renaming source target) (site : Site (source + depth)) :
    (renameTypedSite depth ρ site).dependencies =
      site.dependencies.map (Dependency.rename (Renaming.liftN ρ depth)) :=
  rfl

theorem substituteTypedSite_dependencies {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target)
    (site : Site (source + depth)) :
    (substituteTypedSite depth σ site).dependencies =
      site.dependencies.flatMap (Dependency.substitute
        (Substitution.liftN (fun index => (σ index).bundle.term) depth)) :=
  rfl

theorem shiftTypedSite_dependencies {scope : Nat} (depth : Nat)
    (site : Site scope) :
    (shiftTypedSite depth site).dependencies =
      site.dependencies.map (Dependency.rename (Renaming.shiftN depth)) :=
  rfl

@[simp] theorem serializedRenameTypedSite_preserves_identity
    {source target : Nat} (depth : Nat) (ρ : Renaming source target)
    (site : Site (source + depth)) :
    (SiteEntry.ofSite (renameTypedSite depth ρ site)).identity =
      site.identity := rfl

@[simp] theorem serializedSubstituteTypedSite_preserves_identity
    {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target)
    (site : Site (source + depth)) :
    (SiteEntry.ofSite (substituteTypedSite depth σ site)).identity =
      site.identity := rfl

def renameScopedSiteCandidate {source target : Nat}
    (ρ : Renaming source target) :
    (entry : Sigma fun raw => ScopedSiteUse source raw) → SiteEntry
  | ⟨_, use⟩ => SiteEntry.ofSite (renameTypedSite use.depth ρ use.site)

def substituteScopedSiteCandidate {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    (entry : Sigma fun raw => ScopedSiteUse source raw) → SiteEntry
  | ⟨_, use⟩ =>
      SiteEntry.ofSite (substituteTypedSite use.depth σ use.site)

def renameScopedSiteUse {source target : Nat} (ρ : Renaming source target) :
    (entry : Sigma fun raw => ScopedSiteUse source raw) →
      Sigma fun raw => ScopedSiteUse target raw
  | ⟨raw, use⟩ =>
      let site := renameTypedSite use.depth ρ use.site
      let tableEntry := SiteEntry.ofSite site
      let outputRaw : SiteUse := {
        identity := raw.identity
        role := raw.role
        scope := target + use.depth }
      ⟨outputRaw, {
        depth := use.depth
        scopeEq := rfl
        entry := tableEntry
        entryIdentity := by
          calc
            tableEntry.identity = site.identity := rfl
            _ = use.site.identity := rfl
            _ = use.entry.identity := use.siteIdentity
            _ = raw.identity := use.entryIdentity
        entryRole := by
          calc
            tableEntry.role = site.role := rfl
            _ = use.site.role := rfl
            _ = use.entry.role := use.siteRole
            _ = raw.role := use.entryRole
        site := site
        siteIdentity := rfl
        siteRole := rfl }⟩

def substituteScopedSiteUse {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    (entry : Sigma fun raw => ScopedSiteUse source raw) →
      Sigma fun raw => ScopedSiteUse target raw
  | ⟨raw, use⟩ =>
      let site := substituteTypedSite use.depth σ use.site
      let tableEntry := SiteEntry.ofSite site
      let outputRaw : SiteUse := {
        identity := raw.identity
        role := raw.role
        scope := target + use.depth }
      ⟨outputRaw, {
        depth := use.depth
        scopeEq := rfl
        entry := tableEntry
        entryIdentity := by
          calc
            tableEntry.identity = site.identity := rfl
            _ = use.site.identity := rfl
            _ = use.entry.identity := use.siteIdentity
            _ = raw.identity := use.entryIdentity
        entryRole := by
          calc
            tableEntry.role = site.role := rfl
            _ = use.site.role := rfl
            _ = use.entry.role := use.siteRole
            _ = raw.role := use.entryRole
        site := site
        siteIdentity := rfl
        siteRole := rfl }⟩

def scopedSiteEntryCandidates {scope : Nat}
    (entries : List (Sigma fun raw => ScopedSiteUse scope raw)) :
    List SiteEntry :=
  entries.map fun entry => entry.snd.entry

theorem Site.cast_preserves_identity {source target : Nat}
    (equal : source = target) (site : Site source) :
    (equal ▸ site).identity = site.identity := by
  cases equal
  rfl

theorem Site.cast_preserves_role {source target : Nat}
    (equal : source = target) (site : Site source) :
    (equal ▸ site).role = site.role := by
  cases equal
  rfl

theorem renameScopedSiteCandidate_preserves_identity {source target : Nat}
    (ρ : Renaming source target)
    (entry : Sigma fun raw => ScopedSiteUse source raw) :
    (renameScopedSiteCandidate ρ entry).identity = entry.snd.entry.identity := by
  cases entry with
  | mk raw use =>
      exact use.siteIdentity

theorem substituteScopedSiteCandidate_preserves_identity {source target : Nat}
    (σ : Fin source → ValidatedBundle target)
    (entry : Sigma fun raw => ScopedSiteUse source raw) :
    (substituteScopedSiteCandidate σ entry).identity =
      entry.snd.entry.identity := by
  cases entry with
  | mk raw use =>
      exact use.siteIdentity

def insertReconciledSiteEntry (entries : List SiteEntry)
    (candidate : SiteEntry) :
    Except BundleBindingConflict (List SiteEntry) :=
  match entries.find? fun entry => entry.identity == candidate.identity with
  | none => pure (entries ++ [candidate])
  | some existing =>
      if same : existing = candidate then pure entries
      else .error (.inconsistentSharing {
        identity := candidate.identity
        first := existing
        second := candidate
        unequal := same })

def reconcileSiteEntries (candidates : List SiteEntry) :
    Except BundleBindingConflict (List SiteEntry) :=
  candidates.foldlM insertReconciledSiteEntry []

def scopedSidecarSubstitutionUses {source : Nat}
    (bundle : ValidatedBundle source) : List (TypedSubstitutionUse source) :=
  bundle.closure.entries.flatMap fun entry =>
    match entry with
    | ⟨_, use⟩ => use.typedSubstitutionUses

def replacementScopedSiteCandidates {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (TypedSubstitutionUse source) → List SiteEntry
  | [] => []
  | use :: rest =>
      let replacement := σ use.index
      let shifted := replacement.closure.entries.map fun entry =>
        match entry with
        | ⟨_, siteUse⟩ => SiteEntry.ofSite <|
            renameTypedSite siteUse.depth
              (Renaming.shiftN (scope := target) use.depth) siteUse.site
      shifted ++ replacementScopedSiteCandidates σ rest

def insertReplacementScopedSiteUse {target : Nat} (insertionDepth : Nat) :
    (entry : Sigma fun raw => ScopedSiteUse target raw) →
      Sigma fun raw => ScopedSiteUse target raw
  | ⟨raw, use⟩ =>
      let site := renameTypedSite use.depth
        (Renaming.shiftN (scope := target) insertionDepth) use.site
      have scopeAssoc : target + insertionDepth + use.depth =
          target + (insertionDepth + use.depth) := by omega
      let shiftedSite : Site (target + (insertionDepth + use.depth)) :=
        scopeAssoc ▸ site
      let tableEntry := SiteEntry.ofSite shiftedSite
      let outputRaw : SiteUse := {
        identity := raw.identity
        role := raw.role
        scope := target + (insertionDepth + use.depth) }
      ⟨outputRaw, {
        depth := insertionDepth + use.depth
        scopeEq := rfl
        entry := tableEntry
        entryIdentity := by
          calc
            tableEntry.identity = shiftedSite.identity := rfl
            _ = site.identity := Site.cast_preserves_identity scopeAssoc site
            _ = use.site.identity := rfl
            _ = use.entry.identity := use.siteIdentity
            _ = raw.identity := use.entryIdentity
        entryRole := by
          calc
            tableEntry.role = shiftedSite.role := rfl
            _ = site.role := Site.cast_preserves_role scopeAssoc site
            _ = use.site.role := rfl
            _ = use.entry.role := use.siteRole
            _ = raw.role := use.entryRole
        site := shiftedSite
        siteIdentity := rfl
        siteRole := rfl }⟩

def replacementScopedSiteUses {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (TypedSubstitutionUse source) →
      List (Sigma fun raw => ScopedSiteUse target raw)
  | [] => []
  | use :: rest =>
      let shifted := (σ use.index).closure.entries.map
        (insertReplacementScopedSiteUse use.depth)
      shifted ++ replacementScopedSiteUses σ rest

def replacementSourceNotesForUses {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (TypedSubstitutionUse source) → List SourceNote
  | [] => []
  | use :: rest =>
      (σ use.index).bundle.sourceMap ++ replacementSourceNotesForUses σ rest

structure RenamedBundle {source target : Nat} (input : ValidatedBundle source)
    (ρ : Renaming source target) where
  validated : ValidatedBundle target
  termEq : validated.bundle.term = input.bundle.term.rename ρ
  sitesAreTypedCandidates :
    reconcileSiteEntries
      (scopedSiteEntryCandidates validated.closure.entries) =
        .ok validated.bundle.sites

structure SubstitutedBundle {source target : Nat}
    (input : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) where
  validated : ValidatedBundle target
  termEq : validated.bundle.term = input.bundle.term.substitute
    (fun index => (σ index).bundle.term)
  sitesAreTypedCandidates :
    reconcileSiteEntries
      (scopedSiteEntryCandidates validated.closure.entries) =
        .ok validated.bundle.sites

def RenamedBundle.bundle {source target : Nat}
    {input : ValidatedBundle source} {ρ : Renaming source target}
    (result : RenamedBundle input ρ) : Bundle target :=
  result.validated.bundle

def SubstitutedBundle.bundle {source target : Nat}
    {input : ValidatedBundle source}
    {σ : Fin source → ValidatedBundle target}
    (result : SubstitutedBundle input σ) : Bundle target :=
  result.validated.bundle

def shiftSiteEntry {scope : Nat} (depth : Nat) (entry : SiteEntry) :
    Except String SiteEntry := do
  let site ← SiteEntry.toSite scope entry
  pure <| SiteEntry.ofSite (shiftTypedSite depth site)

def renameSiteEntry {source target : Nat} (depth : Nat)
    (ρ : Renaming source target) (entry : SiteEntry) :
    Except String SiteEntry := do
  let site ← SiteEntry.toSite (source + depth) entry
  pure <| SiteEntry.ofSite (renameTypedSite depth ρ site)

def substituteSiteEntry {source target : Nat} (depth : Nat)
    (σ : Fin source → ValidatedBundle target) (entry : SiteEntry) :
    Except String SiteEntry := do
  let site ← SiteEntry.toSite (source + depth) entry
  pure <| SiteEntry.ofSite (substituteTypedSite depth σ site)

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
        let replacement := (σ ⟨rawIndex, inBounds⟩).bundle
        let replacementUses ← reachableSiteUses replacement.sites
          replacement.term.siteUses
        let shifted ← renameSiteTable
          (source := target) (target := target + depth)
          (Renaming.shiftN (scope := target) depth)
          replacementUses replacement.sites
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

def Bundle.renameWithUses {source target : Nat} (bundle : Bundle source)
    (uses : List SiteUse) (ρ : Renaming source target) :
    Except String (ValidatedBundle target) := do
  let sites ← renameSiteTable ρ uses bundle.sites
  let result : Bundle target :=
    { version := bundle.version
      term := bundle.term.rename ρ
      sites
      sourceMap := bundle.sourceMap }
  result.checked

def Bundle.rename {source target : Nat} (bundle : Bundle source)
    (ρ : Renaming source target) : Except String (ValidatedBundle target) := do
  let uses ← bundle.validateWithUses
  bundle.renameWithUses uses ρ

def ValidatedBundle.rename {source target : Nat}
    (bundle : ValidatedBundle source) (ρ : Renaming source target) :
    Except BundleBindingConflict (RenamedBundle bundle ρ) :=
  let outputEntries := bundle.closure.entries.map (renameScopedSiteUse ρ)
  let outputUses := outputEntries.map Sigma.fst
  let candidates := scopedSiteEntryCandidates outputEntries
  match evidence : reconcileSiteEntries candidates with
  | .error conflict => .error conflict
  | .ok sites =>
      let outputBundle : Bundle target := {
        version := bundle.bundle.version
        term := bundle.bundle.term.rename ρ
        sites
        sourceMap := bundle.bundle.sourceMap }
      let outputClosure : ScopedSiteClosure target outputUses := {
        entries := outputEntries
        coverage := rfl }
      let validated : ValidatedBundle target := {
        bundle := outputBundle
        uses := outputUses
        closure := outputClosure }
      .ok {
      validated := validated
      termEq := rfl
      sitesAreTypedCandidates := evidence }

def Bundle.weaken {scope : Nat} (bundle : Bundle scope) :
    Except String (ValidatedBundle (scope + 1)) :=
  bundle.rename Fin.succ

def ValidatedBundle.weaken {scope : Nat} (bundle : ValidatedBundle scope) :
    Except BundleBindingConflict (RenamedBundle bundle Fin.succ) :=
  bundle.rename Fin.succ

def Bundle.substituteWithUses {source target : Nat} (bundle : Bundle source)
    (uses : List SiteUse) (σ : Fin source → ValidatedBundle target) :
    Except String (ValidatedBundle target) := do
  let originalSites ← substituteSiteTable σ uses bundle.sites
  let sidecarUses ← sidecarSubstitutionUses source uses bundle.sites
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

def Bundle.substitute {source target : Nat} (bundle : Bundle source)
    (σ : Fin source → ValidatedBundle target) :
    Except String (ValidatedBundle target) := do
  let uses ← bundle.validateWithUses
  bundle.substituteWithUses uses σ

def ValidatedBundle.substitute {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) :
    Except BundleBindingConflict (SubstitutedBundle bundle σ) :=
  let uses := typedTermSubstitutionUses bundle.bundle.term ++
    scopedSidecarSubstitutionUses bundle
  let originalEntries := bundle.closure.entries.map (substituteScopedSiteUse σ)
  let replacementEntries := replacementScopedSiteUses σ uses
  let outputEntries := originalEntries ++ replacementEntries
  let outputUses := outputEntries.map Sigma.fst
  let candidates := scopedSiteEntryCandidates outputEntries
  match evidence : reconcileSiteEntries
      candidates with
  | .error conflict => .error conflict
  | .ok sites =>
      let outputBundle : Bundle target := {
        version := bundle.bundle.version
        term := bundle.bundle.term.substitute fun index => (σ index).bundle.term
        sites
        sourceMap := bundle.bundle.sourceMap ++
          replacementSourceNotesForUses σ uses }
      let outputClosure : ScopedSiteClosure target outputUses := {
        entries := outputEntries
        coverage := rfl }
      let validated : ValidatedBundle target := {
        bundle := outputBundle
        uses := outputUses
        closure := outputClosure }
      .ok {
      validated := validated
      termEq := rfl
      sitesAreTypedCandidates := evidence }

theorem RenamedBundle.site_ids {source target : Nat}
    {input : ValidatedBundle source} {ρ : Renaming source target}
    (result : RenamedBundle input ρ) :
    result.bundle.term.siteIds = input.bundle.term.siteIds := by
  change result.validated.bundle.term.siteIds = input.bundle.term.siteIds
  rw [result.termEq]
  exact Term.siteIds_rename ρ input.bundle.term

theorem SubstitutedBundle.preserves_site_id {source target : Nat}
    {input : ValidatedBundle source}
    {σ : Fin source → ValidatedBundle target}
    (result : SubstitutedBundle input σ)
    (identity : SiteId) (present : identity ∈ input.bundle.term.siteIds) :
    identity ∈ result.bundle.term.siteIds := by
  change identity ∈ result.validated.bundle.term.siteIds
  rw [result.termEq]
  exact Term.siteId_mem_substitute
    (fun index => (σ index).bundle.term) input.bundle.term identity present

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

end Interchange
end SmusniPilot
