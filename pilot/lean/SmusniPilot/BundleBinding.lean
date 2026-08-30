import SmusniPilot.Interchange
import SmusniPilot.BindingLaws

namespace SmusniPilot
namespace Interchange


theorem Term.siteOccurrence_support_typed {scope : Nat} (term : Term scope)
    (occurrence : SiteOccurrence)
    (present : occurrence ∈ term.siteOccurrences) :
    ∃ dependencies : List (Dependency occurrence.use.scope),
      occurrence.support =
        dependencies.map SerializedDependency.ofDependency := by
  revert occurrence
  induction term using Term.rec
    (motive_2 := fun scope terms => ∀ occurrence,
      occurrence ∈ terms.siteOccurrences →
        ∃ dependencies : List (Dependency occurrence.use.scope),
          occurrence.support =
            dependencies.map SerializedDependency.ofDependency) <;>
    intros <;>
    simp_all [Term.siteOccurrences, TermList.siteOccurrences] <;>
    grind

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

theorem BundleBindingConflict.inconsistent_has_unequal_candidates
    (witness : SiteEntryConflict) : witness.first ≠ witness.second :=
  witness.unequal

def Bundle.checked {scope : Nat} (bundle : Bundle scope) :
    Except String (ValidatedBundle scope) :=
  match bundle.buildCoherence with
  | .ok coherence => .ok { bundle, coherence }
  | .error message => .error message

theorem Bundle.checked_bundle {scope : Nat} (bundle : Bundle scope)
    (validated : ValidatedBundle scope)
    (success : bundle.checked = .ok validated) :
    validated.bundle = bundle := by
  unfold Bundle.checked at success
  cases coherenceResult : bundle.buildCoherence with
  | error message => simp [coherenceResult] at success
  | ok coherence =>
      rw [coherenceResult] at success
      cases success
      rfl

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

structure ReconciledSiteTable (candidates : List SiteEntry) where
  entries : List SiteEntry
  identitiesUnique : (entries.map fun entry => entry.identity).Nodup
  candidatesCovered : ∀ candidate, candidate ∈ candidates →
    candidate ∈ entries
  entriesCovered : ∀ entry, entry ∈ entries → entry ∈ candidates

theorem siteEntry_eq_of_identity_nodup (entries : List SiteEntry)
    (unique : (entries.map fun entry => entry.identity).Nodup)
    (first second : SiteEntry) (firstPresent : first ∈ entries)
    (secondPresent : second ∈ entries)
    (identityEq : first.identity = second.identity) : first = second := by
  induction entries with
  | nil => simp at firstPresent
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at firstPresent secondPresent
      rcases unique with ⟨headFresh, restUnique⟩
      rcases firstPresent with firstHead | firstRest
      · subst first
        rcases secondPresent with secondHead | secondRest
        · exact secondHead.symm
        · exfalso
          apply headFresh
          exact List.mem_map.mpr ⟨second, secondRest, identityEq.symm⟩
      · rcases secondPresent with secondHead | secondRest
        · subst second
          exfalso
          apply headFresh
          exact List.mem_map.mpr ⟨first, firstRest, identityEq⟩
        · exact ih restUnique firstRest secondRest

def clearSiteProfile (entry : SiteEntry) : SiteEntry :=
  { entry with dependencies := [] }

structure TypedOccurrenceEntry (occurrence : SiteOccurrence) where
  entry : SiteEntry
  entryIdentity : entry.identity = occurrence.use.identity
  entryRole : entry.role = occurrence.use.role
  profile : entry.dependencies = occurrence.support
  site : Site occurrence.use.scope
  typed : SiteEntry.toSite occurrence.use.scope entry = .ok site

def rrLinkFromMetadata (metadata : List SiteEntry) (occurrence : SiteOccurrence)
    (covered : ∃ entry, entry ∈ metadata ∧
      entry.identity = occurrence.use.identity) : Option String :=
  match lookup : metadata.find? (fun entry =>
      entry.identity == occurrence.use.identity) with
  | some entry => entry.rrLink
  | none => False.elim (by
      rcases covered with ⟨entry, entryPresent, identityEq⟩
      have noMatch := (List.find?_eq_none.mp lookup) entry entryPresent
      apply noMatch
      simpa using identityEq)

def occurrenceEntryFromMetadata (metadata : List SiteEntry)
    (occurrence : SiteOccurrence)
    (covered : ∃ entry, entry ∈ metadata ∧
      entry.identity = occurrence.use.identity) : SiteEntry := {
  identity := occurrence.use.identity
  role := occurrence.use.role
  dependencies := occurrence.support
  rrLink := rrLinkFromMetadata metadata occurrence covered }

def typedOccurrenceEntryFromMetadata (metadata : List SiteEntry)
    (occurrence : SiteOccurrence)
    (covered : ∃ entry, entry ∈ metadata ∧
      entry.identity = occurrence.use.identity)
    (supportTyped : ∃ dependencies : List (Dependency occurrence.use.scope),
      occurrence.support =
        dependencies.map SerializedDependency.ofDependency) :
    TypedOccurrenceEntry occurrence := by
  let entry := occurrenceEntryFromMetadata metadata occurrence covered
  have success : ∃ site, SiteEntry.toSite occurrence.use.scope entry =
      .ok site := by
    rcases supportTyped with ⟨dependencies, supportEq⟩
    let site : Site occurrence.use.scope := {
      identity := occurrence.use.identity
      role := occurrence.use.role
      dependencies
      rrLink := entry.rrLink }
    refine ⟨site, ?_⟩
    unfold SiteEntry.toSite
    change (do
      let decoded ← occurrence.support.mapM
        (SerializedDependency.toDependency occurrence.use.scope)
      pure ({
        identity := occurrence.use.identity
        role := occurrence.use.role
        dependencies := decoded
        rrLink := entry.rrLink } : Site occurrence.use.scope)) = .ok site
    rw [supportEq, mapM_toDependency_ofDependency]
    rfl
  exact match typed : SiteEntry.toSite occurrence.use.scope entry with
  | .error message => False.elim (by
      rcases success with ⟨site, success⟩
      rw [typed] at success
      contradiction)
  | .ok site => {
      entry
      entryIdentity := rfl
      entryRole := rfl
      profile := rfl
      site
      typed }

structure TypedOccurrenceTable {scope : Nat} (term : Term scope) where
  entries : List (Sigma fun occurrence => TypedOccurrenceEntry occurrence)
  coverage : entries.map Sigma.fst = term.siteOccurrences

def typedOccurrenceOfTerm {scope : Nat} (term : Term scope)
    (metadata : List SiteEntry)
    (metadataCoverage : ∀ occurrence, occurrence ∈ term.siteOccurrences →
      ∃ entry, entry ∈ metadata ∧
        entry.identity = occurrence.use.identity)
    (attached : {occurrence // occurrence ∈ term.siteOccurrences}) :
    Sigma fun occurrence => TypedOccurrenceEntry occurrence :=
  ⟨attached.val, typedOccurrenceEntryFromMetadata metadata attached.val
    (metadataCoverage attached.val attached.property)
    (Term.siteOccurrence_support_typed term attached.val attached.property)⟩

def typedOccurrenceTable {scope : Nat} (term : Term scope)
    (metadata : List SiteEntry)
    (metadataCoverage : ∀ occurrence, occurrence ∈ term.siteOccurrences →
      ∃ entry, entry ∈ metadata ∧
        entry.identity = occurrence.use.identity) :
    TypedOccurrenceTable term := {
  entries := term.siteOccurrences.attach.map
    (typedOccurrenceOfTerm term metadata metadataCoverage)
  coverage := by
    simp [List.map_map, Function.comp_def, typedOccurrenceOfTerm] }

def typedOccurrenceCandidates {scope : Nat} {term : Term scope}
    (occurrences : TypedOccurrenceTable term) : List SiteEntry :=
  occurrences.entries.map fun entry => entry.snd.entry

def typedOccurrenceFromEntries :
    (entries : List (Sigma fun occurrence => TypedOccurrenceEntry occurrence)) →
    (occurrence : SiteOccurrence) → occurrence ∈ entries.map Sigma.fst →
      TypedOccurrenceEntry occurrence
  | [], occurrence, present => by simp at present
  | ⟨candidate, typed⟩ :: rest, occurrence, present =>
      if same : candidate = occurrence then
        same ▸ typed
      else
        typedOccurrenceFromEntries rest occurrence (by
          simp only [List.map_cons, List.mem_cons] at present
          rcases present with equal | later
          · exact False.elim (same equal.symm)
          · exact later)

theorem typedOccurrenceFromEntries_mem
    (entries : List (Sigma fun occurrence => TypedOccurrenceEntry occurrence))
    (occurrence : SiteOccurrence)
    (present : occurrence ∈ entries.map Sigma.fst) :
    (⟨occurrence, typedOccurrenceFromEntries entries occurrence present⟩ :
      Sigma fun occurrence => TypedOccurrenceEntry occurrence) ∈ entries := by
  induction entries with
  | nil => simp at present
  | cons head rest ih =>
      rcases head with ⟨candidate, typed⟩
      simp only [List.map_cons, List.mem_cons] at present
      simp only [typedOccurrenceFromEntries]
      split
      · next same =>
          subst candidate
          exact List.mem_cons_self
      · next different =>
          apply List.mem_cons_of_mem
          exact ih _

structure OccurrenceForUse (occurrences : List SiteOccurrence)
    (use : SiteUse) where
  occurrence : SiteOccurrence
  present : occurrence ∈ occurrences
  useEq : occurrence.use = use

def occurrenceForUse : (occurrences : List SiteOccurrence) →
    (use : SiteUse) → use ∈ occurrences.map SiteOccurrence.use →
      OccurrenceForUse occurrences use
  | [], use, present => by simp at present
  | occurrence :: rest, use, present =>
      if same : occurrence.use = use then {
        occurrence
        present := List.mem_cons_self
        useEq := same }
      else
        let selected := occurrenceForUse rest use (by
          simp only [List.map_cons, List.mem_cons] at present
          rcases present with equal | later
          · exact False.elim (same equal.symm)
          · exact later)
        { selected with present := List.mem_cons_of_mem _ selected.present }

def TypedOccurrenceEntry.toTypedSiteUseWitness {scope : Nat}
    {bundle : Bundle scope} {occurrence : SiteOccurrence}
    (typed : TypedOccurrenceEntry occurrence)
    (entryInTable : typed.entry ∈ bundle.sites) :
    TypedSiteUseWitness bundle occurrence.use := {
  entry := typed.entry
  entryInTable
  entryIdentity := typed.entryIdentity
  entryRole := typed.entryRole
  site := typed.site
  typed := typed.typed }

def coherenceFromOccurrenceTable {scope : Nat}
    (version : Nat) (term : Term scope) (sourceMap : List SourceNote)
    (occurrences : TypedOccurrenceTable term)
    (table : ReconciledSiteTable (typedOccurrenceCandidates occurrences)) :
    BundleCoherence ({ version, term, sites := table.entries, sourceMap } :
      Bundle scope) := by
  let outputBundle : Bundle scope :=
    { version, term, sites := table.entries, sourceMap }
  let uses := dedupSiteUses term.siteUses
  let witnessFor : ∀ use, use ∈ uses →
      TypedSiteUseWitness outputBundle use := fun use present =>
    let rootPresent := (mem_dedupSiteUses use _).mp present
    let occurrencePresent : use ∈ term.siteOccurrences.map
        SiteOccurrence.use := by
      simpa using rootPresent
    let selectedOccurrence := occurrenceForUse term.siteOccurrences use
      occurrencePresent
    let typedPresent : selectedOccurrence.occurrence ∈
        occurrences.entries.map Sigma.fst := by
      rw [occurrences.coverage]
      exact selectedOccurrence.present
    let selected := typedOccurrenceFromEntries occurrences.entries
      selectedOccurrence.occurrence typedPresent
    let entryInTable := table.candidatesCovered selected.entry <|
      List.mem_map.mpr
        ⟨⟨selectedOccurrence.occurrence, selected⟩,
          typedOccurrenceFromEntries_mem occurrences.entries
            selectedOccurrence.occurrence typedPresent, rfl⟩
    selectedOccurrence.useEq ▸
      selected.toTypedSiteUseWitness entryInTable
  refine {
    uses
    usesUnique := nodup_dedupSiteUses _
    rootsCovered := by
      intro use present
      exact (mem_dedupSiteUses use _).mpr present
    scopeBound := by
      intro use present
      exact Term.scope_le_of_mem_siteUses term use <|
        (mem_dedupSiteUses use _).mp present
    witness := witnessFor
    profileAgreement := ?_
    tableUnique := table.identitiesUnique
    tableCovered := ?_ }
  · intro occurrence occurrencePresent
    have rootPresent : occurrence.use ∈ term.siteUses := by
      rw [← term.siteOccurrences_uses]
      exact List.mem_map.mpr ⟨occurrence, occurrencePresent, rfl⟩
    let present := (mem_dedupSiteUses occurrence.use _).mpr rootPresent
    refine ⟨present, ?_⟩
    have typedPresent : occurrence ∈ occurrences.entries.map Sigma.fst := by
      rw [occurrences.coverage]
      exact occurrencePresent
    let selected := typedOccurrenceFromEntries occurrences.entries occurrence
      typedPresent
    have selectedInTable : selected.entry ∈ table.entries :=
      table.candidatesCovered selected.entry <| List.mem_map.mpr
        ⟨⟨occurrence, selected⟩,
          typedOccurrenceFromEntries_mem occurrences.entries occurrence
            typedPresent, rfl⟩
    let chosen := witnessFor occurrence.use present
    have identityEq : chosen.entry.identity = selected.entry.identity := by
      calc
        chosen.entry.identity = occurrence.use.identity := chosen.entryIdentity
        _ = selected.entry.identity := selected.entryIdentity.symm
    have entryEq := siteEntry_eq_of_identity_nodup table.entries
      table.identitiesUnique chosen.entry selected.entry chosen.entryInTable
      selectedInTable identityEq
    change chosen.entry.dependencies = occurrence.support
    rw [entryEq]
    exact selected.profile
  · intro entry entryPresent
    have candidatePresent := table.entriesCovered entry entryPresent
    simp only [typedOccurrenceCandidates, List.mem_map] at candidatePresent
    rcases candidatePresent with
      ⟨⟨occurrence, typed⟩, typedPresent, entryEq⟩
    have occurrencePresent : occurrence ∈ term.siteOccurrences := by
      rw [← occurrences.coverage]
      exact List.mem_map.mpr ⟨⟨occurrence, typed⟩, typedPresent, rfl⟩
    refine ⟨occurrence, occurrencePresent, ?_⟩
    calc
      occurrence.use.identity = typed.entry.identity :=
        typed.entryIdentity.symm
      _ = entry.identity := congrArg SiteEntry.identity entryEq

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

theorem ReconciledSiteTable.coversIdentity {candidates : List SiteEntry}
    (table : ReconciledSiteTable candidates) (identity : SiteId)
    (covered : ∃ entry, entry ∈ candidates ∧ entry.identity = identity) :
    ∃ entry, entry ∈ table.entries ∧ entry.identity = identity := by
  rcases covered with ⟨entry, entryPresent, identityEq⟩
  exact ⟨entry, table.candidatesCovered entry entryPresent, identityEq⟩

def renameMetadata {source : Nat} (bundle : ValidatedBundle source) :
    List SiteEntry :=
  bundle.bundle.sites.map clearSiteProfile

theorem renamedOccurrence_metadataCovered {source target : Nat}
    (bundle : ValidatedBundle source) (ρ : Renaming source target)
    (occurrence : SiteOccurrence)
    (present : occurrence ∈
      (bundle.bundle.term.rename ρ).siteOccurrences) :
    ∃ entry, entry ∈ renameMetadata bundle ∧
      entry.identity = occurrence.use.identity := by
  have outputRoot : occurrence.use ∈
      (bundle.bundle.term.rename ρ).siteUses := by
    rw [← (bundle.bundle.term.rename ρ).siteOccurrences_uses]
    exact List.mem_map.mpr ⟨occurrence, present, rfl⟩
  obtain ⟨input, inputRoot, rebased⟩ :=
    Term.siteUses_rename_corresponds ρ bundle.bundle.term occurrence.use
      outputRoot
  have inputUse := bundle.coherence.rootsCovered input inputRoot
  let sourceEntry := (bundle.coherence.witness input inputUse).entry
  let metadataEntry := clearSiteProfile sourceEntry
  refine ⟨metadataEntry, ?_, ?_⟩
  · exact List.mem_map.mpr
      ⟨sourceEntry, (bundle.coherence.witness input inputUse).entryInTable,
        rfl⟩
  · calc
      metadataEntry.identity = sourceEntry.identity := rfl
      _ = input.identity :=
        (bundle.coherence.witness input inputUse).entryIdentity
      _ = occurrence.use.identity := rebased.1

def substitutionMetadata {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) : List SiteEntry :=
  bundle.bundle.sites.map clearSiteProfile ++
    (typedTermSubstitutionUses bundle.bundle.term).flatMap fun use =>
      (σ use.index).bundle.sites.map clearSiteProfile

theorem substitutedOccurrence_metadataCovered {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target)
    (occurrence : SiteOccurrence)
    (present : occurrence ∈
      (bundle.bundle.term.substitute
        (fun index => (σ index).bundle.term)).siteOccurrences) :
    ∃ entry, entry ∈ substitutionMetadata bundle σ ∧
      entry.identity = occurrence.use.identity := by
  have outputRoot : occurrence.use ∈
      (bundle.bundle.term.substitute
        (fun index => (σ index).bundle.term)).siteUses := by
    rw [← (bundle.bundle.term.substitute
      (fun index => (σ index).bundle.term)).siteOccurrences_uses]
    exact List.mem_map.mpr ⟨occurrence, present, rfl⟩
  rcases Term.siteUses_substitute_corresponds bundle.bundle.term σ
      occurrence.use outputRoot with original | replacementCase
  · rcases original with ⟨input, inputRoot, rebased⟩
    have inputUse := bundle.coherence.rootsCovered input inputRoot
    let sourceEntry := (bundle.coherence.witness input inputUse).entry
    let metadataEntry := clearSiteProfile sourceEntry
    refine ⟨metadataEntry, ?_, ?_⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨sourceEntry, (bundle.coherence.witness input inputUse).entryInTable,
          rfl⟩
    · calc
        metadataEntry.identity = sourceEntry.identity := rfl
        _ = input.identity :=
          (bundle.coherence.witness input inputUse).entryIdentity
        _ = occurrence.use.identity := rebased.1
  · rcases replacementCase with
      ⟨use, usePresent, replacement, replacementRoot, rebased⟩
    have replacementUse :=
      (σ use.index).coherence.rootsCovered replacement replacementRoot
    let sourceEntry :=
      ((σ use.index).coherence.witness replacement replacementUse).entry
    let metadataEntry := clearSiteProfile sourceEntry
    refine ⟨metadataEntry, ?_, ?_⟩
    · apply List.mem_append_right
      simp only [List.mem_flatMap]
      refine ⟨use, usePresent, ?_⟩
      exact List.mem_map.mpr
        ⟨sourceEntry,
          ((σ use.index).coherence.witness replacement
            replacementUse).entryInTable, rfl⟩
    · calc
        metadataEntry.identity = sourceEntry.identity := rfl
        _ = replacement.identity :=
          ((σ use.index).coherence.witness replacement
            replacementUse).entryIdentity
        _ = occurrence.use.identity := rebased.1

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
  validatedBundleEq : validated.bundle = certified
  termEq : certified.term = input.bundle.term.rename ρ

structure SubstitutedBundle {source target : Nat}
    (input : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) where
  certified : Bundle target
  validated : ValidatedBundle target
  validatedBundleEq : validated.bundle = certified
  termEq : certified.term = input.bundle.term.substitute
    (fun index => (σ index).bundle.term)

def RenamedBundle.bundle {source target : Nat}
    {input : ValidatedBundle source} {ρ : Renaming source target}
    (result : RenamedBundle input ρ) : Bundle target :=
  result.certified

def SubstitutedBundle.bundle {source target : Nat}
    {input : ValidatedBundle source}
    {σ : Fin source → ValidatedBundle target}
    (result : SubstitutedBundle input σ) : Bundle target :=
  result.certified

def ValidatedBundle.rename {source target : Nat}
    (bundle : ValidatedBundle source) (ρ : Renaming source target) :
    Except BundleBindingConflict (RenamedBundle bundle ρ) :=
  let term := bundle.bundle.term.rename ρ
  let metadataCandidates := renameMetadata bundle
  match reconcileSiteTable metadataCandidates with
  | .error conflict => .error conflict
  | .ok metadataTable =>
      let occurrences := typedOccurrenceTable term metadataTable.entries
        (fun occurrence present =>
          metadataTable.coversIdentity occurrence.use.identity <|
            renamedOccurrence_metadataCovered bundle ρ occurrence present)
      let candidates := typedOccurrenceCandidates occurrences
      match reconcileSiteTable candidates with
      | .error conflict => .error conflict
      | .ok table =>
          let outputBundle : Bundle target := {
            version := bundle.bundle.version
            term
            sites := table.entries
            sourceMap := bundle.bundle.sourceMap }
          let outputCoherence : BundleCoherence outputBundle :=
            coherenceFromOccurrenceTable bundle.bundle.version term
              bundle.bundle.sourceMap occurrences table
          let validated : ValidatedBundle target := {
            bundle := outputBundle
            coherence := outputCoherence }
          .ok {
            certified := outputBundle
            validated
            validatedBundleEq := rfl
            termEq := rfl }

def ValidatedBundle.weaken {scope : Nat} (bundle : ValidatedBundle scope) :
    Except BundleBindingConflict (RenamedBundle bundle Fin.succ) :=
  bundle.rename Fin.succ

def ValidatedBundle.substitute {source target : Nat}
    (bundle : ValidatedBundle source)
    (σ : Fin source → ValidatedBundle target) :
    Except BundleBindingConflict (SubstitutedBundle bundle σ) :=
  let term := bundle.bundle.term.substitute
    (fun index => (σ index).bundle.term)
  let metadataCandidates := substitutionMetadata bundle σ
  match reconcileSiteTable metadataCandidates with
  | .error conflict => .error conflict
  | .ok metadataTable =>
      let occurrences := typedOccurrenceTable term metadataTable.entries
        (fun occurrence present =>
          metadataTable.coversIdentity occurrence.use.identity <|
            substitutedOccurrence_metadataCovered bundle σ occurrence present)
      let candidates := typedOccurrenceCandidates occurrences
      match reconcileSiteTable candidates with
      | .error conflict => .error conflict
      | .ok table =>
          let uses := typedTermSubstitutionUses bundle.bundle.term
          let outputBundle : Bundle target := {
            version := bundle.bundle.version
            term
            sites := table.entries
            sourceMap := bundle.bundle.sourceMap ++
              replacementSourceNotesForUses σ uses }
          let outputCoherence : BundleCoherence outputBundle :=
            coherenceFromOccurrenceTable bundle.bundle.version term
              (bundle.bundle.sourceMap ++ replacementSourceNotesForUses σ uses)
              occurrences table
          let validated : ValidatedBundle target := {
            bundle := outputBundle
            coherence := outputCoherence }
          .ok {
            certified := outputBundle
            validated
            validatedBundleEq := rfl
            termEq := rfl }

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
