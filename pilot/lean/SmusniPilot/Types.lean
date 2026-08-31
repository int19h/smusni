import SmusniPilot.Inventory

namespace SmusniPilot

inductive Ty where
  | named (name : TypeName) (arguments : List Ty)
  | variable (name : String)
  | index (value : String)
  | function (effectful : Bool) (parameters : List Ty) (result : Ty)
  deriving Repr, Inhabited

mutual
  def Ty.beq : Ty → Ty → Bool
    | .named firstName firstArguments, .named secondName secondArguments =>
        decide (firstName = secondName) && Ty.listBeq firstArguments secondArguments
    | .variable first, .variable second => first == second
    | .index first, .index second => first == second
    | .function firstEffectful firstParameters firstResult,
        .function secondEffectful secondParameters secondResult =>
        firstEffectful == secondEffectful &&
          Ty.listBeq firstParameters secondParameters &&
          Ty.beq firstResult secondResult
    | _, _ => false

  def Ty.listBeq : List Ty → List Ty → Bool
    | [], [] => true
    | firstHead :: firstTail, secondHead :: secondTail =>
        Ty.beq firstHead secondHead && Ty.listBeq firstTail secondTail
    | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

mutual
  theorem Ty.beq_self : ∀ type : Ty, Ty.beq type type = true
    | .named name arguments => by
        simp only [Ty.beq, decide_true, Bool.true_and]
        exact Ty.listBeq_self arguments
    | .variable name => by simp [Ty.beq]
    | .index value => by simp [Ty.beq]
    | .function effectful parameters result => by
        simp only [Ty.beq, beq_self_eq_true, Bool.true_and]
        rw [Ty.listBeq_self parameters, Ty.beq_self result]
        rfl

  theorem Ty.listBeq_self : ∀ types : List Ty, Ty.listBeq types types = true
    | [] => rfl
    | head :: tail => by
        simp only [Ty.listBeq]
        rw [Ty.beq_self head, Ty.listBeq_self tail]
        rfl
end

instance : ReflBEq Ty where
  rfl := Ty.beq_self _

mutual
  theorem Ty.eq_of_beq_true : ∀ {first second : Ty},
      Ty.beq first second = true → first = second
    | .named firstName firstArguments, .named secondName secondArguments, h => by
        simp only [Ty.beq, Bool.and_eq_true] at h
        rcases h with ⟨nameEq, argumentsEq⟩
        have names : firstName = secondName := of_decide_eq_true nameEq
        have arguments : firstArguments = secondArguments :=
          Ty.listEq_of_beq_true argumentsEq
        cases names
        cases arguments
        rfl
    | .variable first, .variable second, h => by
        have names : first = second := eq_of_beq h
        cases names
        rfl
    | .index first, .index second, h => by
        have values : first = second := eq_of_beq h
        cases values
        rfl
    | .function firstEffectful firstParameters firstResult,
        .function secondEffectful secondParameters secondResult, h => by
        simp only [Ty.beq, Bool.and_eq_true] at h
        rcases h with ⟨⟨effectfulEq, parametersEq⟩, resultEq⟩
        have effectful : firstEffectful = secondEffectful := eq_of_beq effectfulEq
        have parameters : firstParameters = secondParameters :=
          Ty.listEq_of_beq_true parametersEq
        have result : firstResult = secondResult := Ty.eq_of_beq_true resultEq
        cases effectful
        cases parameters
        cases result
        rfl
    | .named _ _, .variable _ , h | .named _ _, .index _, h |
      .named _ _, .function _ _ _, h | .variable _, .named _ _, h |
      .variable _, .index _, h | .variable _, .function _ _ _, h |
      .index _, .named _ _, h | .index _, .variable _, h |
      .index _, .function _ _ _, h | .function _ _ _, .named _ _, h |
      .function _ _ _, .variable _, h | .function _ _ _, .index _, h => by
        simp [Ty.beq] at h

  theorem Ty.listEq_of_beq_true : ∀ {first second : List Ty},
      Ty.listBeq first second = true → first = second
    | [], [], _ => rfl
    | firstHead :: firstTail, secondHead :: secondTail, h => by
        simp only [Ty.listBeq, Bool.and_eq_true] at h
        rcases h with ⟨headEq, tailEq⟩
        have head : firstHead = secondHead := Ty.eq_of_beq_true headEq
        have tail : firstTail = secondTail := Ty.listEq_of_beq_true tailEq
        cases head
        cases tail
        rfl
    | [], _ :: _, h | _ :: _, [], h => by simp [Ty.listBeq] at h
end

structure FreeId where
  domain : String
  serial : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

structure SiteId where
  document : String
  occurrence : Nat
  expansionRole : String
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

inductive SiteRole where
  | context
  | vague
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

inductive Dependency (scope : Nat) where
  | bound (index : Fin scope)
  | free (identity : FreeId)
  deriving Repr, DecidableEq, BEq

structure Site (scope : Nat) where
  identity : SiteId
  role : SiteRole
  dependencies : List (Dependency scope)
  rrLink : Option String := none
  deriving Repr, DecidableEq, BEq

inductive SerializedDependency where
  | bound (index : Nat)
  | free (identity : FreeId)
  | site (identity : SiteId)
  deriving Repr, DecidableEq, BEq, Inhabited

structure SiteEntry where
  identity : SiteId
  role : SiteRole
  dependencies : List SerializedDependency
  rrLink : Option String := Option.none
  deriving Repr, DecidableEq, BEq, Inhabited

def SerializedDependency.ofDependency {scope : Nat} :
    Dependency scope → SerializedDependency
  | .bound index => .bound index.val
  | .free identity => .free identity

def SiteEntry.ofSite {scope : Nat} (site : Site scope) : SiteEntry :=
  { identity := site.identity
    role := site.role
    dependencies := site.dependencies.map SerializedDependency.ofDependency
    rrLink := site.rrLink }

def SerializedDependency.toDependency (scope : Nat) :
    SerializedDependency → Except String (Dependency scope)
  | .bound index =>
      if inBounds : index < scope then pure (.bound ⟨index, inBounds⟩)
      else .error s!"bound dependency {index} outside scope {scope}"
  | .free identity => pure (.free identity)
  | .site identity =>
      .error s!"legacy site dependency is not a semantic profile: {repr identity}"

def SiteEntry.toSite (scope : Nat) (entry : SiteEntry) :
    Except String (Site scope) := do
  let dependencies ← entry.dependencies.mapM
    (SerializedDependency.toDependency scope)
  pure {
    identity := entry.identity
    role := entry.role
    dependencies
    rrLink := entry.rrLink
  }

theorem SiteEntry.toSite_preserves_identity {scope : Nat}
    (entry : SiteEntry) (site : Site scope)
    (success : entry.toSite scope = .ok site) :
    site.identity = entry.identity := by
  unfold SiteEntry.toSite at success
  cases decoded : entry.dependencies.mapM
      (SerializedDependency.toDependency scope) with
  | error message =>
      rw [decoded] at success
      contradiction
  | ok dependencies =>
      rw [decoded] at success
      cases success
      rfl

theorem SiteEntry.toSite_preserves_role {scope : Nat}
    (entry : SiteEntry) (site : Site scope)
    (success : entry.toSite scope = .ok site) :
    site.role = entry.role := by
  unfold SiteEntry.toSite at success
  cases decoded : entry.dependencies.mapM
      (SerializedDependency.toDependency scope) with
  | error message =>
      rw [decoded] at success
      contradiction
  | ok dependencies =>
      rw [decoded] at success
      cases success
      rfl

end SmusniPilot
