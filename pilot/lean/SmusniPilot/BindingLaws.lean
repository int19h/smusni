import SmusniPilot.Binding

namespace SmusniPilot

@[simp] theorem Renaming.lift_identity {scope : Nat} :
    Renaming.lift (fun index : Fin scope => index) =
      (fun index : Fin (scope + 1) => index) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    rfl

@[simp] theorem Dependency.rename_identity {scope : Nat}
    (dependency : Dependency scope) :
    dependency.rename (fun index => index) = dependency := by
  cases dependency <;> rfl

@[simp] theorem Site.rename_identity {scope : Nat} (site : Site scope) :
    site.rename (fun index => index) = site := by
  cases site with
  | mk identity role dependencies rrLink =>
      have mapped :
          dependencies.map (Dependency.rename (fun index => index)) =
            dependencies := by
        induction dependencies <;> simp_all [Dependency.rename_identity]
      simp [Site.rename, mapped]

@[simp] theorem Term.rename_identity {scope : Nat} (term : Term scope) :
    term.rename (fun index => index) = term := by
  induction term using Term.rec
    (motive_2 := fun scope terms =>
      terms.rename (fun index => index) = terms) <;>
    simp_all [Term.rename, TermList.rename]

@[simp] theorem TermList.rename_identity {scope : Nat}
    (terms : TermList scope) :
    terms.rename (fun index => index) = terms := by
  induction terms using TermList.rec
    (motive_1 := fun scope term =>
      term.rename (fun index => index) = term) <;>
    simp_all [Term.rename, TermList.rename]

theorem Renaming.lift_compose {first second third : Nat}
    (secondMap : Renaming second third)
    (firstMap : Renaming first second) :
    Renaming.lift (fun index => secondMap (firstMap index)) =
      fun index => Renaming.lift secondMap (Renaming.lift firstMap index) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    rfl

theorem Dependency.rename_compose {first second third : Nat}
    (secondMap : Renaming second third)
    (firstMap : Renaming first second)
    (dependency : Dependency first) :
    (dependency.rename firstMap).rename secondMap =
      dependency.rename (fun index => secondMap (firstMap index)) := by
  cases dependency <;> rfl

@[simp] theorem Dependency.rename_bound {source target : Nat}
    (ρ : Renaming source target) (index : Fin source) :
    (Dependency.bound index).rename ρ = Dependency.bound (ρ index) := rfl

@[simp] theorem Dependency.rename_free {source target : Nat}
    (ρ : Renaming source target) (identity : FreeId) :
    (Dependency.free identity : Dependency source).rename ρ =
      Dependency.free identity := rfl

@[simp] theorem Dependency.rename_site {source target : Nat}
    (ρ : Renaming source target) (identity : SiteId) :
    (Dependency.site identity : Dependency source).rename ρ =
      Dependency.site identity := rfl

theorem Site.rename_compose {first second third : Nat}
    (secondMap : Renaming second third)
    (firstMap : Renaming first second)
    (site : Site first) :
    (site.rename firstMap).rename secondMap =
      site.rename (fun index => secondMap (firstMap index)) := by
  cases site with
  | mk identity role dependencies rrLink =>
      simp only [Site.rename]
      congr 1
      induction dependencies <;> simp_all [Dependency.rename_compose]

theorem Term.rename_compose {first second third : Nat}
    (secondMap : Renaming second third)
    (firstMap : Renaming first second)
    (term : Term first) :
    (term.rename firstMap).rename secondMap =
      term.rename (fun index => secondMap (firstMap index)) := by
  revert second third secondMap
  induction term using Term.rec
    (motive_2 := fun scope terms =>
      ∀ {second third} (secondMap : Renaming second third)
        (firstMap : Renaming scope second),
        (terms.rename firstMap).rename secondMap =
          terms.rename (fun index => secondMap (firstMap index))) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Renaming.lift_compose]

theorem TermList.rename_compose {first second third : Nat}
    (secondMap : Renaming second third)
    (firstMap : Renaming first second)
    (terms : TermList first) :
    (terms.rename firstMap).rename secondMap =
      terms.rename (fun index => secondMap (firstMap index)) := by
  revert second third secondMap
  induction terms using TermList.rec
    (motive_1 := fun scope term =>
      ∀ {second third} (secondMap : Renaming second third)
        (firstMap : Renaming scope second),
        (term.rename firstMap).rename secondMap =
          term.rename (fun index => secondMap (firstMap index)))
    <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Renaming.lift_compose]

@[simp] theorem Substitution.lift_identity {scope : Nat} :
    Substitution.lift (Substitution.identity (scope := scope)) =
      Substitution.identity := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    rfl

@[simp] theorem Dependency.substitute_identity {scope : Nat}
    (dependency : Dependency scope) :
    dependency.substitute Substitution.identity = [dependency] := by
  cases dependency <;> rfl

@[simp] theorem Site.substitute_identity {scope : Nat} (site : Site scope) :
    site.substitute Substitution.identity = site := by
  cases site with
  | mk identity role dependencies rrLink =>
      have flattened :
          dependencies.flatMap
            (Dependency.substitute Substitution.identity) = dependencies := by
        induction dependencies <;> simp_all [Dependency.substitute_identity]
      simp [Site.substitute, flattened]

@[simp] theorem Term.substitute_identity {scope : Nat} (term : Term scope) :
    term.substitute Substitution.identity = term := by
  induction term using Term.rec
    (motive_2 := fun scope terms =>
      terms.substitute Substitution.identity = terms) <;>
    simp_all [Term.substitute, TermList.substitute, Substitution.identity]

@[simp] theorem TermList.substitute_identity {scope : Nat}
    (terms : TermList scope) :
    terms.substitute Substitution.identity = terms := by
  induction terms using TermList.rec
    (motive_1 := fun scope term =>
      term.substitute Substitution.identity = term) <;>
    simp_all [Term.substitute, TermList.substitute, Substitution.identity]

theorem Term.siteIds_rename {source target : Nat}
    (ρ : Renaming source target) (term : Term source) :
    (term.rename ρ).siteIds = term.siteIds := by
  revert target ρ
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {target} (ρ : Renaming source target),
        (terms.rename ρ).siteIds = terms.siteIds) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.siteIds, TermList.siteIds]

theorem TermList.siteIds_rename {source target : Nat}
    (ρ : Renaming source target) (terms : TermList source) :
    (terms.rename ρ).siteIds = terms.siteIds := by
  revert target ρ
  induction terms using TermList.rec
    (motive_1 := fun source term =>
      ∀ {target} (ρ : Renaming source target),
        (term.rename ρ).siteIds = term.siteIds)
    <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.siteIds, TermList.siteIds]

theorem Dependency.lower_rename {source target : Nat}
    (ρ : Renaming source target) (dependency : Dependency (source + 1)) :
    Dependency.lower (dependency.rename (Renaming.lift ρ)) =
      (Dependency.lower dependency).map (Dependency.rename ρ) := by
  cases dependency with
  | bound index =>
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro predecessor
        rfl
  | free identity => rfl
  | site identity => rfl

@[simp] theorem Dependency.lowerList_rename {source target : Nat}
    (ρ : Renaming source target) (dependencies : List (Dependency (source + 1))) :
    dependencies.filterMap
        (fun dependency =>
          Dependency.lower (dependency.rename (Renaming.lift ρ))) =
      (dependencies.filterMap Dependency.lower).map (Dependency.rename ρ) := by
  induction dependencies with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.filterMap_cons]
      rw [Dependency.lower_rename]
      cases Dependency.lower head <;> simp [ih]

theorem Term.dependencies_rename {source target : Nat}
    (ρ : Renaming source target) (term : Term source) :
    (term.rename ρ).dependencies =
      term.dependencies.map (Dependency.rename ρ) := by
  revert target ρ
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {target} (ρ : Renaming source target),
        (terms.rename ρ).dependencies =
          terms.dependencies.map (Dependency.rename ρ)) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.dependencies,
      TermList.dependencies, Dependency.lowerList_rename, List.map_append,
      Function.comp_def]

theorem TermList.dependencies_rename {source target : Nat}
    (ρ : Renaming source target) (terms : TermList source) :
    (terms.rename ρ).dependencies =
      terms.dependencies.map (Dependency.rename ρ) := by
  revert target ρ
  induction terms using TermList.rec
    (motive_1 := fun source term =>
      ∀ {target} (ρ : Renaming source target),
        (term.rename ρ).dependencies =
          term.dependencies.map (Dependency.rename ρ)) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.dependencies,
      TermList.dependencies, Dependency.lowerList_rename, List.map_append,
      Function.comp_def]

theorem Dependency.substitute_rename {source middle target : Nat}
    (σ : Substitution source middle) (ρ : Renaming middle target)
    (dependency : Dependency source) :
    (dependency.substitute σ).map (Dependency.rename ρ) =
      dependency.substitute (fun index => (σ index).rename ρ) := by
  cases dependency with
  | bound index =>
      exact (Term.dependencies_rename ρ (σ index)).symm
  | free identity => rfl
  | site identity => rfl

theorem Site.substitute_rename {source middle target : Nat}
    (σ : Substitution source middle) (ρ : Renaming middle target)
    (site : Site source) :
    (site.substitute σ).rename ρ =
      site.substitute (fun index => (σ index).rename ρ) := by
  cases site with
  | mk identity role dependencies rrLink =>
      simp only [Site.substitute, Site.rename]
      congr 1
      induction dependencies <;>
        simp_all [Dependency.substitute_rename]

theorem Substitution.lift_rename {source middle target : Nat}
    (σ : Substitution source middle) (ρ : Renaming middle target)
    (index : Fin (source + 1)) :
    (Substitution.lift σ index).rename (Renaming.lift ρ) =
      Substitution.lift (fun sourceIndex => (σ sourceIndex).rename ρ) index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    change
      ((σ predecessor).rename Fin.succ).rename (Renaming.lift ρ) =
        ((σ predecessor).rename ρ).rename Fin.succ
    rw [Term.rename_compose]
    rw [Term.rename_compose]
    rfl

theorem Term.substitute_rename {source middle target : Nat}
    (σ : Substitution source middle) (ρ : Renaming middle target)
    (term : Term source) :
    (term.substitute σ).rename ρ =
      term.substitute (fun index => (σ index).rename ρ) := by
  revert middle target σ ρ
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {middle target} (σ : Substitution source middle)
        (ρ : Renaming middle target),
        (terms.substitute σ).rename ρ =
          terms.substitute (fun index => (σ index).rename ρ)) <;>
    intros <;>
    simp_all [Term.substitute, TermList.substitute, Term.rename,
      TermList.rename, Substitution.lift_rename]

theorem TermList.substitute_rename {source middle target : Nat}
    (σ : Substitution source middle) (ρ : Renaming middle target)
    (terms : TermList source) :
    (terms.substitute σ).rename ρ =
      terms.substitute (fun index => (σ index).rename ρ) := by
  revert middle target σ ρ
  induction terms using TermList.rec
    (motive_1 := fun source term =>
      ∀ {middle target} (σ : Substitution source middle)
        (ρ : Renaming middle target),
        (term.substitute σ).rename ρ =
          term.substitute (fun index => (σ index).rename ρ)) <;>
    intros <;>
    simp_all [Term.substitute, TermList.substitute, Term.rename,
      TermList.rename, Substitution.lift_rename]

theorem Substitution.lift_after_renaming {source middle target : Nat}
    (ρ : Renaming source middle) (σ : Substitution middle target)
    (index : Fin (source + 1)) :
    Substitution.lift σ (Renaming.lift ρ index) =
      Substitution.lift (fun sourceIndex => σ (ρ sourceIndex)) index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    rfl

theorem Term.rename_substitute {source middle target : Nat}
    (ρ : Renaming source middle) (σ : Substitution middle target)
    (term : Term source) :
    (term.rename ρ).substitute σ =
      term.substitute (fun index => σ (ρ index)) := by
  revert middle target ρ σ
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {middle target} (ρ : Renaming source middle)
        (σ : Substitution middle target),
        (terms.rename ρ).substitute σ =
          terms.substitute (fun index => σ (ρ index))) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.substitute,
      TermList.substitute, Substitution.lift_after_renaming]

theorem TermList.rename_substitute {source middle target : Nat}
    (ρ : Renaming source middle) (σ : Substitution middle target)
    (terms : TermList source) :
    (terms.rename ρ).substitute σ =
      terms.substitute (fun index => σ (ρ index)) := by
  revert middle target ρ σ
  induction terms using TermList.rec
    (motive_1 := fun source term =>
      ∀ {middle target} (ρ : Renaming source middle)
        (σ : Substitution middle target),
        (term.rename ρ).substitute σ =
          term.substitute (fun index => σ (ρ index))) <;>
    intros <;>
    simp_all [Term.rename, TermList.rename, Term.substitute,
      TermList.substitute, Substitution.lift_after_renaming]

theorem Substitution.lift_compose {source middle target : Nat}
    (σ : Substitution source middle) (τ : Substitution middle target)
    (index : Fin (source + 1)) :
    (Substitution.lift σ index).substitute (Substitution.lift τ) =
      Substitution.lift (fun sourceIndex => (σ sourceIndex).substitute τ)
        index := by
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro predecessor
    change
      ((σ predecessor).rename Fin.succ).substitute (Substitution.lift τ) =
        ((σ predecessor).substitute τ).rename Fin.succ
    rw [Term.rename_substitute]
    rw [Term.substitute_rename]
    rfl

theorem Term.substitute_compose {source middle target : Nat}
    (σ : Substitution source middle) (τ : Substitution middle target)
    (term : Term source) :
    (term.substitute σ).substitute τ =
      term.substitute (fun index => (σ index).substitute τ) := by
  revert middle target σ τ
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {middle target} (σ : Substitution source middle)
        (τ : Substitution middle target),
        (terms.substitute σ).substitute τ =
          terms.substitute (fun index => (σ index).substitute τ)) <;>
    intros <;>
    simp_all [Term.substitute, TermList.substitute,
      Substitution.lift_compose]

theorem TermList.substitute_compose {source middle target : Nat}
    (σ : Substitution source middle) (τ : Substitution middle target)
    (terms : TermList source) :
    (terms.substitute σ).substitute τ =
      terms.substitute (fun index => (σ index).substitute τ) := by
  revert middle target σ τ
  induction terms using TermList.rec
    (motive_1 := fun source term =>
      ∀ {middle target} (σ : Substitution source middle)
        (τ : Substitution middle target),
        (term.substitute σ).substitute τ =
          term.substitute (fun index => (σ index).substitute τ)) <;>
    intros <;>
    simp_all [Term.substitute, TermList.substitute,
      Substitution.lift_compose]

@[simp] theorem Site.rename_preserves_identity {source target : Nat}
    (ρ : Renaming source target) (site : Site source) :
    (site.rename ρ).identity = site.identity := rfl

@[simp] theorem Site.substitute_preserves_identity {source target : Nat}
    (σ : Substitution source target) (site : Site source) :
    (site.substitute σ).identity = site.identity := rfl

theorem Term.siteId_mem_substitute {source target : Nat}
    (σ : Substitution source target) (term : Term source) (identity : SiteId)
    (present : identity ∈ term.siteIds) :
    identity ∈ (term.substitute σ).siteIds := by
  revert target σ identity
  induction term using Term.rec
    (motive_2 := fun source terms =>
      ∀ {target} (σ : Substitution source target) (identity : SiteId),
        identity ∈ terms.siteIds →
          identity ∈ (terms.substitute σ).siteIds) <;>
    intros <;>
    simp_all [Term.substitute, TermList.substitute, Term.siteIds,
      TermList.siteIds] <;> grind

theorem TermList.siteId_mem_substitute {source target : Nat}
    (σ : Substitution source target) (terms : TermList source)
    (identity : SiteId) (present : identity ∈ terms.siteIds) :
    identity ∈ (terms.substitute σ).siteIds := by
  revert target σ identity
  induction terms using TermList.rec
    (motive_1 := fun source term =>
      ∀ {target} (σ : Substitution source target) (identity : SiteId),
        identity ∈ term.siteIds →
          identity ∈ (term.substitute σ).siteIds) <;>
    intros <;>
    simp_all [Term.substitute, TermList.substitute, Term.siteIds,
      TermList.siteIds] <;> grind

end SmusniPilot
