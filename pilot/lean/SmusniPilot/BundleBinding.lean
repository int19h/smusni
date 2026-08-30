import SmusniPilot.Interchange
import SmusniPilot.BindingLaws

namespace SmusniPilot
namespace Interchange

theorem SerializedDependency.ofDependency_of_toDependency {scope : Nat}
    (raw : SerializedDependency) (dependency : Dependency scope)
    (success : raw.toDependency scope = .ok dependency) :
    SerializedDependency.ofDependency dependency = raw := by
  cases raw <;> cases dependency
  all_goals simp_all [SerializedDependency.toDependency,
    SerializedDependency.ofDependency, pure, Except.pure]
  all_goals split at success <;> simp_all <;> try { cases success; rfl }

theorem serializedDependencies_of_mapM_toDependency {scope : Nat}
    (raw : List SerializedDependency) (dependencies : List (Dependency scope))
    (success : raw.mapM (SerializedDependency.toDependency scope) =
      .ok dependencies) :
    dependencies.map SerializedDependency.ofDependency = raw := by
  induction raw generalizing dependencies with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure,
        Except.ok.injEq] at success
      subst dependencies
      rfl
  | cons head rest ih =>
      simp only [List.mapM_cons] at success
      cases headResult : head.toDependency scope with
      | error message =>
          simp [headResult, bind, Except.bind] at success
      | ok dependency =>
          rw [headResult] at success
          cases restResult : rest.mapM
              (SerializedDependency.toDependency scope) with
          | error message =>
              simp [restResult, bind, Except.bind] at success
          | ok tail =>
              rw [restResult] at success
              cases success
              simp [SerializedDependency.ofDependency_of_toDependency
                head dependency headResult, ih tail restResult]

theorem SiteEntry.toSite_serialized_dependencies {scope : Nat}
    (entry : SiteEntry) (site : Site scope)
    (success : entry.toSite scope = .ok site) :
    site.dependencies.map SerializedDependency.ofDependency =
      entry.dependencies := by
  unfold SiteEntry.toSite at success
  cases decoded : entry.dependencies.mapM
      (SerializedDependency.toDependency scope) with
  | error message =>
      simp [decoded, Functor.map, Except.map] at success
  | ok dependencies =>
      rw [decoded] at success
      cases success
      exact serializedDependencies_of_mapM_toDependency
        entry.dependencies dependencies decoded

theorem siteEntryToSite_reindex {source target : Nat}
    (equal : source = target) (entry : SiteEntry) (site : Site source)
    (typed : SiteEntry.toSite source entry = .ok site) :
    SiteEntry.toSite target entry = .ok (equal ▸ site) := by
  cases equal
  exact typed

theorem Site.cast_preserves_serialized_dependencies {source target : Nat}
    (equal : source = target) (site : Site source) :
    (equal ▸ site).dependencies.map SerializedDependency.ofDependency =
      site.dependencies.map SerializedDependency.ofDependency := by
  cases equal
  rfl

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

structure ScopedSiteUse (scope : Nat) (raw : SiteUse) where
  depth : Nat
  scopeEq : raw.scope = scope + depth
  entry : SiteEntry
  entryIdentity : entry.identity = raw.identity
  entryRole : entry.role = raw.role
  site : Site (scope + depth)
  siteIdentity : site.identity = entry.identity
  siteRole : site.role = entry.role
  typed : SiteEntry.toSite (scope + depth) entry = .ok site
  serializedDependencies :
    site.dependencies.map SerializedDependency.ofDependency =
      entry.dependencies

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
                  entry site deserialized
                typed := deserialized
                serializedDependencies :=
                  SiteEntry.toSite_serialized_dependencies
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

@[simp] theorem Renaming.shiftN_val {scope : Nat} (depth : Nat)
    (index : Fin scope) :
    (Renaming.shiftN depth index).val = index.val + depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change (Renaming.shiftN depth index).val + 1 = index.val + (depth + 1)
      omega

theorem Fin.eq_shiftN_of_depth_le {source depth : Nat}
    (index : Fin (source + depth)) (depthLe : depth ≤ index.val) :
    ∃ outer : Fin source, Renaming.shiftN depth outer = index := by
  have outerBound : index.val - depth < source := by omega
  let outer : Fin source := ⟨index.val - depth, outerBound⟩
  refine ⟨outer, Fin.ext ?_⟩
  simp [outer]
  omega

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
  coherence : BundleCoherence bundle

def ValidatedBundle.uses {scope : Nat} (bundle : ValidatedBundle scope) :
    List SiteUse := bundle.coherence.uses

def bundleSubstitutionAt {scope source target : Nat} (depth : Nat)
    (scopeEq : scope = source + depth)
    (σ : Fin source → ValidatedBundle target) :
    Substitution scope (target + depth) := fun index =>
  Substitution.liftN (fun outer => (σ outer).bundle.term) depth
    (Fin.cast scopeEq index)

theorem bundleSubstitutionAt_succ {scope source target : Nat} (depth : Nat)
    (scopeEq : scope = source + depth)
    (bodyEq : scope + 1 = source + (depth + 1))
    (σ : Fin source → ValidatedBundle target) :
    bundleSubstitutionAt (target := target) (depth + 1) bodyEq σ =
      Substitution.lift (bundleSubstitutionAt depth scopeEq σ) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    simp [bundleSubstitutionAt, Substitution.liftN, Substitution.lift]

@[simp] theorem Substitution.lift_bundleSubstitutionAt
    {scope source target : Nat} (depth : Nat)
    (scopeEq : scope = source + depth)
    (σ : Fin source → ValidatedBundle target) :
    Substitution.lift (bundleSubstitutionAt depth scopeEq σ) =
      bundleSubstitutionAt (target := target) (depth + 1) (by omega) σ :=
  (bundleSubstitutionAt_succ depth scopeEq (by omega) σ).symm

theorem bundleSubstitutionAt_nonlocal {scope source target : Nat}
    (depth : Nat) (scopeEq : scope = source + depth)
    (σ : Fin source → ValidatedBundle target) (index : Fin scope)
    (nonlocal : depth ≤ index.val) :
    bundleSubstitutionAt depth scopeEq σ index =
      (σ ⟨index.val - depth, by omega⟩).bundle.term.rename
        (Renaming.shiftN depth) := by
  let castIndex : Fin (source + depth) := Fin.cast scopeEq index
  have depthLeCast : depth ≤ castIndex.val := by
    simp [castIndex]
    exact nonlocal
  obtain ⟨outer, shifted⟩ :=
    Fin.eq_shiftN_of_depth_le castIndex depthLeCast
  unfold bundleSubstitutionAt
  change Substitution.liftN (fun outer => (σ outer).bundle.term) depth
      castIndex = _
  rw [← shifted]
  rw [Substitution.liftN_shiftN]
  congr
  apply Fin.ext
  have castValue : castIndex.val = index.val := by simp [castIndex]
  have shiftedValue := congrArg Fin.val shifted
  simp only [Renaming.shiftN_val] at shiftedValue
  simp
  omega

def scopedUseOfCoherence {scope : Nat} {bundle : Bundle scope}
    (coherence : BundleCoherence bundle) (raw : SiteUse)
    (present : raw ∈ coherence.uses) : ScopedSiteUse scope raw :=
  let depth := raw.scope - scope
  have scopeEq : raw.scope = scope + depth := by
    have bound := coherence.scopeBound raw present
    omega
  let sourceWitness := coherence.witness raw present
  let site : Site (scope + depth) := scopeEq ▸ sourceWitness.site
  {
    depth
    scopeEq
    entry := sourceWitness.entry
    entryIdentity := sourceWitness.entryIdentity
    entryRole := sourceWitness.entryRole
    site
    siteIdentity := by
      have sourceIdentity := SiteEntry.toSite_preserves_identity
        sourceWitness.entry sourceWitness.site sourceWitness.typed
      exact (Site.cast_preserves_identity scopeEq sourceWitness.site).trans
        sourceIdentity
    siteRole := by
      have sourceRole := SiteEntry.toSite_preserves_role
        sourceWitness.entry sourceWitness.site sourceWitness.typed
      exact (Site.cast_preserves_role scopeEq sourceWitness.site).trans
        sourceRole
    typed := siteEntryToSite_reindex scopeEq sourceWitness.entry
      sourceWitness.site sourceWitness.typed
    serializedDependencies := by
      calc
        site.dependencies.map SerializedDependency.ofDependency =
            sourceWitness.site.dependencies.map
              SerializedDependency.ofDependency :=
          Site.cast_preserves_serialized_dependencies scopeEq sourceWitness.site
        _ = sourceWitness.entry.dependencies :=
          SiteEntry.toSite_serialized_dependencies sourceWitness.entry
            sourceWitness.site sourceWitness.typed }

def scopedSiteUseOfCoherence {scope : Nat} {bundle : Bundle scope}
    (coherence : BundleCoherence bundle)
    (attached : {raw // raw ∈ coherence.uses}) :
    Sigma fun raw => ScopedSiteUse scope raw :=
  ⟨attached.val,
    scopedUseOfCoherence coherence attached.val attached.property⟩

def scopedSiteClosureOfCoherence {scope : Nat} {bundle : Bundle scope}
    (coherence : BundleCoherence bundle) :
    ScopedSiteClosure scope coherence.uses := {
  entries := coherence.uses.attach.map
    (scopedSiteUseOfCoherence coherence)
  coverage := by
    simp [List.map_map, Function.comp_def, scopedSiteUseOfCoherence] }

theorem scopedSiteUseOfCoherence_mem {scope : Nat} {bundle : Bundle scope}
    (coherence : BundleCoherence bundle) (raw : SiteUse)
    (present : raw ∈ coherence.uses) :
    scopedSiteUseOfCoherence coherence ⟨raw, present⟩ ∈
      (scopedSiteClosureOfCoherence coherence).entries := by
  apply List.mem_map.mpr
  exact ⟨⟨raw, present⟩, by simp, rfl⟩

def ValidatedBundle.closure {scope : Nat} (bundle : ValidatedBundle scope) :
    ScopedSiteClosure scope bundle.coherence.uses :=
  scopedSiteClosureOfCoherence bundle.coherence

theorem ValidatedBundle.closure_entry_origin {scope : Nat}
    (bundle : ValidatedBundle scope)
    (entry : Sigma fun raw => ScopedSiteUse scope raw)
    (present : entry ∈ bundle.closure.entries) :
    ∃ attached : {raw // raw ∈ bundle.coherence.uses},
      scopedSiteUseOfCoherence bundle.coherence attached = entry := by
  rcases List.mem_map.mp present with ⟨attached, _attachedPresent, equal⟩
  exact ⟨attached, equal⟩

structure SiteEntryConflict where
  identity : SiteId
  first : SiteEntry
  second : SiteEntry
  unequal : first ≠ second

inductive BundleBindingConflict where
  | inconsistentSharing (witness : SiteEntryConflict)
  | outputValidationFailure (detail : String)

def BundleBindingConflict.message : BundleBindingConflict → String
  | .inconsistentSharing witness =>
      s!"bundle-binding inconsistent-sharing conflict at {repr witness.identity}: " ++
        s!"{repr witness.first} versus {repr witness.second}"
  | .outputValidationFailure detail =>
      "bundle-binding output validation failure: " ++ detail

theorem BundleBindingConflict.inconsistent_has_unequal_candidates
    (witness : SiteEntryConflict) : witness.first ≠ witness.second :=
  witness.unequal

def Bundle.checked {scope : Nat} (bundle : Bundle scope) :
    Except String (ValidatedBundle scope) :=
  match bundle.buildCoherence with
  | .ok coherence => .ok { bundle, coherence }
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

theorem site_mem_of_mem_renameTypedSite_serialized {source target : Nat}
    (depth : Nat) (ρ : Renaming source target)
    (site : Site (source + depth)) (identity : SiteId)
    (present : .site identity ∈
      (renameTypedSite depth ρ site).dependencies.map
        SerializedDependency.ofDependency) :
    .site identity ∈
      site.dependencies.map SerializedDependency.ofDependency := by
  simp only [renameTypedSite_dependencies, List.map_map, List.mem_map] at present
  rcases present with ⟨dependency, dependencyPresent, serializedEq⟩
  cases dependency with
  | bound index => simp [Dependency.rename,
      SerializedDependency.ofDependency] at serializedEq
  | free freeIdentity => simp [Dependency.rename,
      SerializedDependency.ofDependency] at serializedEq
  | site siteIdentity =>
      cases serializedEq
      exact List.mem_map.mpr
        ⟨.site identity, dependencyPresent, rfl⟩

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
        siteRole := rfl
        typed := siteEntryToSite_ofSite site
        serializedDependencies := rfl }⟩

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
        siteRole := rfl
        typed := siteEntryToSite_ofSite site
        serializedDependencies := rfl }⟩

def SiteUse.Rebased (source target : Nat) (input output : SiteUse) : Prop :=
  input.identity = output.identity ∧
    input.role = output.role ∧
    output.scope + source = input.scope + target

theorem SiteUse.eq_of_components (first second : SiteUse)
    (identity : first.identity = second.identity)
    (role : first.role = second.role)
    (scope : first.scope = second.scope) : first = second := by
  cases first
  cases second
  simp_all

theorem Term.siteUses_rename_corresponds {source target : Nat}
    (ρ : Renaming source target) (term : Term source) (output : SiteUse)
    (present : output ∈ (term.rename ρ).siteUses) :
    ∃ input, input ∈ term.siteUses ∧
      SiteUse.Rebased source target input output := by
  revert target output
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {target} (ρ : Renaming source target) (output : SiteUse),
        output ∈ (terms.rename ρ).siteUses →
          ∃ input, input ∈ terms.siteUses ∧
            SiteUse.Rebased source target input output) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.siteUses,
      TermList.siteUses, SiteUse.Rebased] <;>
    grind

theorem Substitution.liftN_local_siteUses {source target : Nat}
    (σ : Substitution source target) (depth : Nat)
    (index : Fin (source + depth)) (isLocal : index.val < depth) :
    (Substitution.liftN σ depth index).siteUses = [] := by
  induction depth with
  | zero => omega
  | succ depth ih =>
      revert isLocal
      refine Fin.cases ?_ ?_ index
      · intro _isLocal
        rfl
      · intro predecessor isLocal
        change ((Substitution.liftN σ depth predecessor).rename Fin.succ).siteUses = []
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro output outputPresent
        obtain ⟨input, inputPresent, _rebased⟩ :=
          Term.siteUses_rename_corresponds Fin.succ
            (Substitution.liftN σ depth predecessor) output outputPresent
        have predecessorLocal : predecessor.val < depth := by
          change predecessor.val + 1 < depth + 1 at isLocal
          omega
        rw [ih predecessor predecessorLocal] at inputPresent
        simp at inputPresent

theorem bundleSubstitutionAt_local_siteUses {scope source target : Nat}
    (depth : Nat) (scopeEq : scope = source + depth)
    (σ : Fin source → ValidatedBundle target) (index : Fin scope)
    (isLocal : index.val < depth) :
    (bundleSubstitutionAt depth scopeEq σ index).siteUses = [] := by
  unfold bundleSubstitutionAt
  apply Substitution.liftN_local_siteUses
  simpa using isLocal

theorem Term.siteUses_substitute_correspondsAt {scope : Nat}
    (term : Term scope) (source depth : Nat)
    (scopeEq : scope = source + depth) (target : Nat)
    (σ : Fin source → ValidatedBundle target) (output : SiteUse)
    (present : output ∈
      (term.substitute (bundleSubstitutionAt depth scopeEq σ)).siteUses) :
    (∃ input, input ∈ term.siteUses ∧
      SiteUse.Rebased source target input output) ∨
    ∃ use,
      use ∈ typedTermSubstitutionUsesAt source depth scopeEq term ∧
      ∃ replacement,
        replacement ∈ (σ use.index).bundle.term.siteUses ∧
        SiteUse.Rebased target (target + use.depth) replacement output := by
  revert source depth target output
  induction term using Term.rec
    (motive_2 := fun scope terms =>
      ∀ (source depth : Nat) (scopeEq : scope = source + depth)
        (target : Nat) (σ : Fin source → ValidatedBundle target)
        (output : SiteUse),
        output ∈
            (terms.substitute
              (bundleSubstitutionAt depth scopeEq σ)).siteUses →
          (∃ input, input ∈ terms.siteUses ∧
            SiteUse.Rebased source target input output) ∨
          ∃ use,
            use ∈ typedTermListSubstitutionUsesAt source depth scopeEq terms ∧
            ∃ replacement,
              replacement ∈ (σ use.index).bundle.term.siteUses ∧
              SiteUse.Rebased target (target + use.depth) replacement output)
  case bound index =>
    intro source depth scopeEq target σ output present
    right
    change output ∈ (bundleSubstitutionAt depth scopeEq σ index).siteUses at present
    by_cases isLocal : index.val < depth
    · rw [bundleSubstitutionAt_local_siteUses depth scopeEq σ index isLocal] at present
      simp at present
    · have isOuter : depth ≤ index.val := by omega
      let outer : Fin source := ⟨index.val - depth, by omega⟩
      rw [bundleSubstitutionAt_nonlocal depth scopeEq σ index isOuter] at present
      change output ∈
        ((σ outer).bundle.term.rename (Renaming.shiftN depth)).siteUses at present
      obtain ⟨replacement, replacementRoot, rebased⟩ :=
        Term.siteUses_rename_corresponds (Renaming.shiftN depth)
          (σ outer).bundle.term output present
      let use : TypedSubstitutionUse source := { index := outer, depth }
      refine ⟨use, ?_, replacement, replacementRoot, ?_⟩
      · simp [typedTermSubstitutionUsesAt, isLocal, use, outer]
      · simpa [use] using rebased
  case lambda binderType body bodyIH =>
    intro source depth scopeEq target σ output present
    change output ∈
      (body.substitute
        (Substitution.lift (bundleSubstitutionAt depth scopeEq σ))).siteUses
        at present
    rw [Substitution.lift_bundleSubstitutionAt] at present
    exact bodyIH source (depth + 1) (by omega) target σ output present
  case bind binderType computation body computationIH bodyIH =>
    intro source depth scopeEq target σ output present
    simp only [Term.substitute, Term.siteUses, List.mem_append] at present
    simp only [Term.siteUses, typedTermSubstitutionUsesAt,
      List.mem_append]
    rcases present with computationPresent | bodyPresent
    · have result := computationIH source depth scopeEq target σ output
        computationPresent
      grind
    · rw [Substitution.lift_bundleSubstitutionAt] at bodyPresent
      have result := bodyIH source (depth + 1) (by omega) target σ output
        bodyPresent
      grind
  all_goals
    intros <;>
    simp_all [Term.substitute, TermList.substitute, Term.siteUses,
      TermList.siteUses, typedTermSubstitutionUsesAt,
      typedTermListSubstitutionUsesAt, SiteUse.Rebased] <;>
    grind

theorem Term.siteUses_substitute_corresponds {source target : Nat}
    (term : Term source) (σ : Fin source → ValidatedBundle target)
    (output : SiteUse)
    (present : output ∈
      (term.substitute (fun index => (σ index).bundle.term)).siteUses) :
    (∃ input, input ∈ term.siteUses ∧
      SiteUse.Rebased source target input output) ∨
    ∃ use,
      use ∈ typedTermSubstitutionUses term ∧
      ∃ replacement,
        replacement ∈ (σ use.index).bundle.term.siteUses ∧
        SiteUse.Rebased target (target + use.depth) replacement output := by
  apply Term.siteUses_substitute_correspondsAt term source 0 rfl target σ
    output
  have substitutionEq : bundleSubstitutionAt 0 rfl σ =
      (fun index => (σ index).bundle.term) := by
    funext index
    rfl
  rw [substitutionEq]
  exact present

def scopedSiteEntryCandidates {scope : Nat}
    (entries : List (Sigma fun raw => ScopedSiteUse scope raw)) :
    List SiteEntry :=
  entries.map fun entry => entry.snd.entry

@[simp] theorem scopedSiteEntryCandidates_rename {source target : Nat}
    (ρ : Renaming source target)
    (entries : List (Sigma fun raw => ScopedSiteUse source raw)) :
    scopedSiteEntryCandidates (entries.map (renameScopedSiteUse ρ)) =
      entries.map (renameScopedSiteCandidate ρ) := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨raw, use⟩
      simp [scopedSiteEntryCandidates, renameScopedSiteUse,
        renameScopedSiteCandidate]

def scopedUseFromEntries {scope : Nat} :
    (entries : List (Sigma fun raw => ScopedSiteUse scope raw)) →
    (raw : SiteUse) → raw ∈ entries.map Sigma.fst → ScopedSiteUse scope raw
  | [], raw, present => by simp at present
  | ⟨candidate, witness⟩ :: rest, raw, present =>
      if same : candidate = raw then
        same ▸ witness
      else
        scopedUseFromEntries rest raw (by
          simp only [List.map_cons, List.mem_cons] at present
          rcases present with equal | later
          · exact False.elim (same equal.symm)
          · exact later)

theorem scopedUseFromEntries_mem {scope : Nat}
    (entries : List (Sigma fun raw => ScopedSiteUse scope raw))
    (raw : SiteUse) (present : raw ∈ entries.map Sigma.fst) :
    (⟨raw, scopedUseFromEntries entries raw present⟩ :
      Sigma fun raw => ScopedSiteUse scope raw) ∈ entries := by
  induction entries with
  | nil => simp at present
  | cons head rest ih =>
      rcases head with ⟨candidate, witness⟩
      simp only [List.map_cons, List.mem_cons] at present
      simp only [scopedUseFromEntries]
      split
      · next same =>
          subst candidate
          exact List.mem_cons_self
      · next different =>
          apply List.mem_cons_of_mem
          apply ih

theorem siteEntryToSite_cast {source target : Nat}
    (equal : source = target) (entry : SiteEntry) (site : Site target)
    (typed : SiteEntry.toSite target entry = .ok site) :
    SiteEntry.toSite source entry = .ok (equal.symm ▸ site) := by
  cases equal
  exact typed

def ScopedSiteUse.toTypedWitness {scope : Nat} {bundle : Bundle scope}
    {raw : SiteUse} (use : ScopedSiteUse scope raw)
    (entryInTable : use.entry ∈ bundle.sites) :
    TypedSiteUseWitness bundle raw :=
  let site : Site raw.scope := use.scopeEq.symm ▸ use.site
  {
    entry := use.entry
    entryInTable
    entryIdentity := use.entryIdentity
    entryRole := use.entryRole
    site
    typed := siteEntryToSite_cast use.scopeEq use.entry use.site use.typed }

theorem scopedUseFromEntries_entry_mem_candidates {scope : Nat}
    (entries : List (Sigma fun raw => ScopedSiteUse scope raw))
    (raw : SiteUse) (present : raw ∈ entries.map Sigma.fst) :
    (scopedUseFromEntries entries raw present).entry ∈
      scopedSiteEntryCandidates entries := by
  apply List.mem_map.mpr
  exact ⟨⟨raw, scopedUseFromEntries entries raw present⟩,
    scopedUseFromEntries_mem entries raw present, rfl⟩

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

structure ReconciledSiteTable (candidates : List SiteEntry) where
  entries : List SiteEntry
  identitiesUnique : (entries.map fun entry => entry.identity).Nodup
  candidatesCovered : ∀ candidate, candidate ∈ candidates →
    candidate ∈ entries
  entriesCovered : ∀ entry, entry ∈ entries → entry ∈ candidates

def reconcileSiteTable : (candidates : List SiteEntry) →
    Except BundleBindingConflict (ReconciledSiteTable candidates)
  | [] => .ok {
      entries := []
      identitiesUnique := by simp
      candidatesCovered := by simp
      entriesCovered := by simp }
  | candidate :: rest =>
      match reconcileSiteTable rest with
      | .error conflict => .error conflict
      | .ok table =>
          match lookup : table.entries.find? (fun entry =>
              entry.identity == candidate.identity) with
          | none => .ok {
              entries := candidate :: table.entries
              identitiesUnique := by
                simp only [List.map_cons, List.nodup_cons]
                refine ⟨?_, table.identitiesUnique⟩
                intro identityPresent
                rcases List.mem_map.mp identityPresent with
                  ⟨entry, entryPresent, identityEq⟩
                have noMatch := (List.find?_eq_none.mp lookup) entry
                  entryPresent
                apply noMatch
                simpa using identityEq
              candidatesCovered := by
                intro entry present
                simp only [List.mem_cons] at present ⊢
                rcases present with isCandidate | inRest
                · exact Or.inl isCandidate
                · exact Or.inr (table.candidatesCovered entry inRest)
              entriesCovered := by
                intro entry present
                simp only [List.mem_cons] at present ⊢
                rcases present with isCandidate | inTable
                · exact Or.inl isCandidate
                · exact Or.inr (table.entriesCovered entry inTable) }
          | some existing =>
              if same : existing = candidate then
                .ok {
                  entries := table.entries
                  identitiesUnique := table.identitiesUnique
                  candidatesCovered := by
                    intro entry present
                    simp only [List.mem_cons] at present
                    rcases present with isCandidate | inRest
                    · subst entry
                      rw [← same]
                      exact List.mem_of_find?_eq_some lookup
                    · exact table.candidatesCovered entry inRest
                  entriesCovered := by
                    intro entry present
                    exact List.mem_cons_of_mem _
                      (table.entriesCovered entry present) }
              else .error (.inconsistentSharing {
                identity := candidate.identity
                first := existing
                second := candidate
                unequal := same })

def reconcileSiteEntries (candidates : List SiteEntry) :
    Except BundleBindingConflict (List SiteEntry) :=
  (reconcileSiteTable candidates).map ReconciledSiteTable.entries

def coherenceFromScopedEntries {scope : Nat}
    (version : Nat) (term : Term scope) (sourceMap : List SourceNote)
    (entries : List (Sigma fun raw => ScopedSiteUse scope raw))
    (table : ReconciledSiteTable (scopedSiteEntryCandidates entries))
    (rootsCovered : ∀ raw, raw ∈ term.siteUses →
      raw ∈ dedupSiteUses (entries.map Sigma.fst))
    (edgesClosed : ∀ raw
      (present : raw ∈ dedupSiteUses (entries.map Sigma.fst))
      (identity : SiteId),
      .site identity ∈
        (scopedUseFromEntries entries raw
          ((mem_dedupSiteUses raw _).mp present)).entry.dependencies →
      ∃ child,
        child ∈ dedupSiteUses (entries.map Sigma.fst) ∧
        child.identity = identity ∧ child.scope = raw.scope) :
    BundleCoherence ({ version, term, sites := table.entries, sourceMap } :
      Bundle scope) := by
  let outputBundle : Bundle scope :=
    { version, term, sites := table.entries, sourceMap }
  let uses := dedupSiteUses (entries.map Sigma.fst)
  let witnessFor : ∀ raw, raw ∈ uses →
      TypedSiteUseWitness outputBundle raw := fun raw present =>
    let rawPresent := (mem_dedupSiteUses raw _).mp present
    let selected := scopedUseFromEntries entries raw rawPresent
    selected.toTypedWitness <| table.candidatesCovered selected.entry <|
      scopedUseFromEntries_entry_mem_candidates entries raw rawPresent
  refine {
    uses := uses
    usesUnique := nodup_dedupSiteUses _
    rootsCovered := rootsCovered
    scopeBound := by
      intro raw present
      let rawPresent := (mem_dedupSiteUses raw _).mp present
      let selected := scopedUseFromEntries entries raw rawPresent
      have scopeEq := selected.scopeEq
      omega
    witness := witnessFor
    edgesClosed := ?_
    tableUnique := table.identitiesUnique
    tableCovered := ?_ }
  · intro raw present dependency dependencyPresent identity isSite
    subst dependency
    exact edgesClosed raw present identity dependencyPresent
  · intro entry entryPresent
    have fromCandidate := table.entriesCovered entry entryPresent
    simp only [scopedSiteEntryCandidates, List.mem_map] at fromCandidate
    rcases fromCandidate with ⟨⟨raw, selected⟩, selectedPresent, entryEq⟩
    refine ⟨raw, ?_, ?_⟩
    · exact (mem_dedupSiteUses raw _).mpr <|
        List.mem_map.mpr ⟨⟨raw, selected⟩, selectedPresent, rfl⟩
    · calc
        raw.identity = selected.entry.identity := selected.entryIdentity.symm
        _ = entry.identity := congrArg SiteEntry.identity entryEq

theorem renameScopedEntries_rootsCovered {source target : Nat}
    (bundle : ValidatedBundle source) (ρ : Renaming source target)
    (output : SiteUse)
    (present : output ∈ (bundle.bundle.term.rename ρ).siteUses) :
    output ∈ dedupSiteUses
      ((bundle.closure.entries.map (renameScopedSiteUse ρ)).map Sigma.fst) := by
  obtain ⟨input, inputRoot, rebased⟩ :=
    Term.siteUses_rename_corresponds ρ bundle.bundle.term output present
  have inputUse : input ∈ bundle.coherence.uses :=
    bundle.coherence.rootsCovered input inputRoot
  let selectedEntry := scopedSiteUseOfCoherence bundle.coherence
    ⟨input, inputUse⟩
  let selected := selectedEntry.snd
  have selectedPresent :
      (⟨input, selected⟩ : Sigma fun raw => ScopedSiteUse source raw) ∈
        bundle.closure.entries :=
    scopedSiteUseOfCoherence_mem bundle.coherence input inputUse
  let transformed := renameScopedSiteUse ρ
    (⟨input, selected⟩ : Sigma fun raw => ScopedSiteUse source raw)
  have rawEq : transformed.fst = output := by
    apply SiteUse.eq_of_components
    · exact rebased.1
    · exact rebased.2.1
    · dsimp [transformed, renameScopedSiteUse]
      have inputScope := selected.scopeEq
      have scopeRelation := rebased.2.2
      change input.scope = source + selected.depth at inputScope
      change output.scope + source = input.scope + target at scopeRelation
      omega
  apply (mem_dedupSiteUses output _).mpr
  apply List.mem_map.mpr
  refine ⟨transformed, ?_, rawEq⟩
  apply List.mem_map.mpr
  exact ⟨⟨input, selected⟩, selectedPresent, rfl⟩

theorem renameScopedEntries_edgesClosed {source target : Nat}
    (bundle : ValidatedBundle source) (ρ : Renaming source target)
    (output : SiteUse)
    (present : output ∈ dedupSiteUses
      ((bundle.closure.entries.map (renameScopedSiteUse ρ)).map Sigma.fst))
    (identity : SiteId)
    (dependencyPresent : .site identity ∈
      (scopedUseFromEntries
        (bundle.closure.entries.map (renameScopedSiteUse ρ)) output
        ((mem_dedupSiteUses output _).mp present)).entry.dependencies) :
    ∃ child,
      child ∈ dedupSiteUses
        ((bundle.closure.entries.map (renameScopedSiteUse ρ)).map Sigma.fst) ∧
      child.identity = identity ∧ child.scope = output.scope := by
  let outputEntries :=
    bundle.closure.entries.map (renameScopedSiteUse ρ)
  have outputProjection := (mem_dedupSiteUses output _).mp present
  let outputSelected := scopedUseFromEntries outputEntries output outputProjection
  have outputSelectedPresent :
      (⟨output, outputSelected⟩ :
        Sigma fun raw => ScopedSiteUse target raw) ∈ outputEntries :=
    scopedUseFromEntries_mem outputEntries output outputProjection
  rcases List.mem_map.mp outputSelectedPresent with
    ⟨⟨inputRaw, inputSelected⟩, inputEntryPresent, transformedEq⟩
  obtain ⟨⟨originRaw, originPresent⟩, originEq⟩ :=
    bundle.closure_entry_origin ⟨inputRaw, inputSelected⟩ inputEntryPresent
  cases originEq
  let inputSelected := scopedUseOfCoherence bundle.coherence
    originRaw originPresent
  have transformedRawEq := congrArg Sigma.fst transformedEq
  have transformedEntryEq := congrArg
    (fun entry => entry.snd.entry) transformedEq
  have renamedDependency : .site identity ∈
      (renameTypedSite inputSelected.depth ρ inputSelected.site).dependencies.map
        SerializedDependency.ofDependency := by
    have candidateDependency : .site identity ∈
        (renameScopedSiteUse ρ
          (⟨originRaw, inputSelected⟩ :
            Sigma fun raw => ScopedSiteUse source raw)).snd.entry.dependencies := by
      rw [transformedEntryEq]
      exact dependencyPresent
    change .site identity ∈
      (renameTypedSite inputSelected.depth ρ inputSelected.site).dependencies.map
        SerializedDependency.ofDependency at candidateDependency
    exact candidateDependency
  have inputSerialized := site_mem_of_mem_renameTypedSite_serialized
    inputSelected.depth ρ inputSelected.site identity renamedDependency
  have inputEntryDependency : .site identity ∈
      inputSelected.entry.dependencies := by
    rw [← inputSelected.serializedDependencies]
    exact inputSerialized
  have coherentDependency : .site identity ∈
      (bundle.coherence.witness originRaw originPresent).entry.dependencies := by
    simpa [inputSelected, scopedUseOfCoherence] using inputEntryDependency
  obtain ⟨child, childPresent, childIdentity, childScope⟩ :=
    bundle.coherence.edgesClosed originRaw originPresent (.site identity)
      coherentDependency identity rfl
  let childInputEntry := scopedSiteUseOfCoherence bundle.coherence
    ⟨child, childPresent⟩
  let childOutputEntry := renameScopedSiteUse ρ childInputEntry
  let childOutput := childOutputEntry.fst
  have childInputPresent : childInputEntry ∈ bundle.closure.entries :=
    scopedSiteUseOfCoherence_mem bundle.coherence child childPresent
  have childOutputPresent : childOutputEntry ∈ outputEntries := by
    apply List.mem_map.mpr
    exact ⟨childInputEntry, childInputPresent, rfl⟩
  refine ⟨childOutput, ?_, ?_, ?_⟩
  · apply (mem_dedupSiteUses childOutput _).mpr
    exact List.mem_map.mpr ⟨childOutputEntry, childOutputPresent, rfl⟩
  · dsimp [childOutput, childOutputEntry, renameScopedSiteUse]
    exact childIdentity
  · dsimp [childOutput, childOutputEntry, renameScopedSiteUse]
    have currentScopeEq := inputSelected.scopeEq
    have childScopeEq := childInputEntry.snd.scopeEq
    have currentOutputScope := congrArg SiteUse.scope transformedRawEq
    change originRaw.scope = source + inputSelected.depth at currentScopeEq
    change child.scope = source + childInputEntry.snd.depth at childScopeEq
    change target + inputSelected.depth = output.scope at currentOutputScope
    omega

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
        siteRole := rfl
        typed := siteEntryToSite_ofSite shiftedSite
        serializedDependencies := rfl }⟩

def replacementScopedSiteUses {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (TypedSubstitutionUse source) →
      List (Sigma fun raw => ScopedSiteUse target raw)
  | [] => []
  | use :: rest =>
      let shifted := (σ use.index).closure.entries.map
        (insertReplacementScopedSiteUse use.depth)
      shifted ++ replacementScopedSiteUses σ rest

def substitutionUses {source : Nat} (bundle : ValidatedBundle source) :
    List (TypedSubstitutionUse source) :=
  typedTermSubstitutionUses bundle.bundle.term ++
    scopedSidecarSubstitutionUses bundle

def substitutedScopedEntries {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) :
    List (Sigma fun raw => ScopedSiteUse target raw) :=
  bundle.closure.entries.map (substituteScopedSiteUse σ) ++
    replacementScopedSiteUses σ (substitutionUses bundle)

theorem insertReplacement_mem_replacementScopedSiteUses
    {source target : Nat} (σ : Fin source → ValidatedBundle target)
    (uses : List (TypedSubstitutionUse source))
    (use : TypedSubstitutionUse source) (usePresent : use ∈ uses)
    (entry : Sigma fun raw => ScopedSiteUse target raw)
    (entryPresent : entry ∈ (σ use.index).closure.entries) :
    insertReplacementScopedSiteUse use.depth entry ∈
      replacementScopedSiteUses σ uses := by
  induction uses with
  | nil => simp at usePresent
  | cons head rest ih =>
      simp only [List.mem_cons] at usePresent
      rcases usePresent with isHead | inRest
      · subst use
        simp only [replacementScopedSiteUses, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨entry, entryPresent, rfl⟩)
      · simp only [replacementScopedSiteUses, List.mem_append]
        exact Or.inr (ih inRest)

theorem substitutedScopedEntries_rootsCovered {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) (output : SiteUse)
    (present : output ∈
      (bundle.bundle.term.substitute
        (fun index => (σ index).bundle.term)).siteUses) :
    output ∈ dedupSiteUses
      ((substitutedScopedEntries bundle σ).map Sigma.fst) := by
  rcases Term.siteUses_substitute_corresponds bundle.bundle.term σ output
      present with original | replacementCase
  · rcases original with ⟨input, inputRoot, rebased⟩
    have inputUse := bundle.coherence.rootsCovered input inputRoot
    let selected := scopedUseOfCoherence bundle.coherence input inputUse
    let inputEntry : Sigma fun raw => ScopedSiteUse source raw :=
      ⟨input, selected⟩
    have inputEntryPresent : inputEntry ∈ bundle.closure.entries :=
      scopedSiteUseOfCoherence_mem bundle.coherence input inputUse
    let transformed := substituteScopedSiteUse σ inputEntry
    have rawEq : transformed.fst = output := by
      apply SiteUse.eq_of_components
      · exact rebased.1
      · exact rebased.2.1
      · dsimp [transformed, inputEntry, substituteScopedSiteUse]
        have inputScope := selected.scopeEq
        have scopeRelation := rebased.2.2
        change input.scope = source + selected.depth at inputScope
        change output.scope + source = input.scope + target at scopeRelation
        omega
    apply (mem_dedupSiteUses output _).mpr
    apply List.mem_map.mpr
    refine ⟨transformed, ?_, rawEq⟩
    simp only [substitutedScopedEntries, List.mem_append, List.mem_map]
    exact Or.inl ⟨inputEntry, inputEntryPresent, rfl⟩
  · rcases replacementCase with
      ⟨use, termUsePresent, replacement, replacementRoot, rebased⟩
    have replacementUse :=
      (σ use.index).coherence.rootsCovered replacement replacementRoot
    let replacementEntry := scopedSiteUseOfCoherence
      (σ use.index).coherence ⟨replacement, replacementUse⟩
    have replacementEntryPresent :
        replacementEntry ∈ (σ use.index).closure.entries :=
      scopedSiteUseOfCoherence_mem (σ use.index).coherence replacement
        replacementUse
    let inserted := insertReplacementScopedSiteUse use.depth replacementEntry
    have usePresent : use ∈ substitutionUses bundle := by
      apply List.mem_append_left
      exact termUsePresent
    have insertedPresent : inserted ∈
        replacementScopedSiteUses σ (substitutionUses bundle) :=
      insertReplacement_mem_replacementScopedSiteUses σ
        (substitutionUses bundle) use usePresent replacementEntry
        replacementEntryPresent
    have rawEq : inserted.fst = output := by
      apply SiteUse.eq_of_components
      · exact rebased.1
      · exact rebased.2.1
      · dsimp [inserted, insertReplacementScopedSiteUse]
        have replacementScope := replacementEntry.snd.scopeEq
        have scopeRelation := rebased.2.2
        change replacement.scope = target + replacementEntry.snd.depth at replacementScope
        change output.scope + target =
          replacement.scope + (target + use.depth) at scopeRelation
        omega
    apply (mem_dedupSiteUses output _).mpr
    apply List.mem_map.mpr
    refine ⟨inserted, ?_, rawEq⟩
    simp only [substitutedScopedEntries, List.mem_append]
    exact Or.inr insertedPresent

def replacementSourceNotesForUses {source target : Nat}
    (σ : Fin source → ValidatedBundle target) :
    List (TypedSubstitutionUse source) → List SourceNote
  | [] => []
  | use :: rest =>
      (σ use.index).bundle.sourceMap ++ replacementSourceNotesForUses σ rest

structure RenamedBundle {source target : Nat} (input : ValidatedBundle source)
    (ρ : Renaming source target) where
  certified : Bundle target
  validated : ValidatedBundle target
  termEq : certified.term = input.bundle.term.rename ρ
  sitesAreTypedCandidates :
    reconcileSiteEntries
      (input.closure.entries.map (renameScopedSiteCandidate ρ)) =
        .ok certified.sites

structure SubstitutedBundle {source target : Nat}
    (input : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) where
  certified : Bundle target
  validated : ValidatedBundle target
  termEq : certified.term = input.bundle.term.substitute
    (fun index => (σ index).bundle.term)
  sitesAreTypedCandidates :
    let uses := typedTermSubstitutionUses input.bundle.term ++
      scopedSidecarSubstitutionUses input
    let original := input.closure.entries.map (substituteScopedSiteCandidate σ)
    let replacements := replacementScopedSiteCandidates σ uses
    reconcileSiteEntries
      (original ++ replacements) = .ok certified.sites

def RenamedBundle.bundle {source target : Nat}
    {input : ValidatedBundle source} {ρ : Renaming source target}
    (result : RenamedBundle input ρ) : Bundle target :=
  result.certified

def SubstitutedBundle.bundle {source target : Nat}
    {input : ValidatedBundle source}
    {σ : Fin source → ValidatedBundle target}
    (result : SubstitutedBundle input σ) : Bundle target :=
  result.certified

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
        let replacementValidated := σ ⟨rawIndex, inBounds⟩
        let replacement := replacementValidated.bundle
        let replacementUses := replacementValidated.uses
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
  let candidates := scopedSiteEntryCandidates outputEntries
  match evidence : reconcileSiteTable candidates with
  | .error conflict => .error conflict
  | .ok table =>
      let outputBundle : Bundle target := {
        version := bundle.bundle.version
        term := bundle.bundle.term.rename ρ
        sites := table.entries
        sourceMap := bundle.bundle.sourceMap }
      let outputCoherence : BundleCoherence outputBundle :=
        coherenceFromScopedEntries bundle.bundle.version
          (bundle.bundle.term.rename ρ) bundle.bundle.sourceMap outputEntries
          table (renameScopedEntries_rootsCovered bundle ρ)
          (renameScopedEntries_edgesClosed bundle ρ)
      let validated : ValidatedBundle target := {
        bundle := outputBundle
        coherence := outputCoherence }
      .ok {
        certified := outputBundle
        validated := validated
        termEq := rfl
        sitesAreTypedCandidates := by
          unfold reconcileSiteEntries
          rw [← scopedSiteEntryCandidates_rename ρ bundle.closure.entries]
          exact congrArg (Except.map ReconciledSiteTable.entries) evidence }

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
  let originalCandidates := bundle.closure.entries.map
    (substituteScopedSiteCandidate σ)
  let replacementCandidates := replacementScopedSiteCandidates σ uses
  let candidates := originalCandidates ++ replacementCandidates
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
      match outputBundle.checked with
      | .error detail => .error (.outputValidationFailure detail)
      | .ok validated => .ok {
          certified := outputBundle
          validated := validated
          termEq := rfl
          sitesAreTypedCandidates := evidence }

theorem RenamedBundle.site_ids {source target : Nat}
    {input : ValidatedBundle source} {ρ : Renaming source target}
    (result : RenamedBundle input ρ) :
    result.bundle.term.siteIds = input.bundle.term.siteIds := by
  change result.certified.term.siteIds = input.bundle.term.siteIds
  rw [result.termEq]
  exact Term.siteIds_rename ρ input.bundle.term

theorem SubstitutedBundle.preserves_site_id {source target : Nat}
    {input : ValidatedBundle source}
    {σ : Fin source → ValidatedBundle target}
    (result : SubstitutedBundle input σ)
    (identity : SiteId) (present : identity ∈ input.bundle.term.siteIds) :
    identity ∈ result.bundle.term.siteIds := by
  change identity ∈ result.certified.term.siteIds
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
