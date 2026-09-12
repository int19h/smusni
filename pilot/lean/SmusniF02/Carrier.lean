import Std

/-! F02-v2 §§2,7: an auxiliary, relative ground run carrier. No production imports.
Membership predicates are the semantic sets. Lists witness finiteness only:
order, duplicate entries, and the choice of witness are erased by `ext`. -/
namespace SmusniF02

universe u v w x

structure FSet (α : Type u) where
  mem : α → Prop
  finite : ∃ xs : List α, ∀ a, mem a ↔ a ∈ xs

namespace FSet
instance : Membership α (FSet α) := ⟨fun s a => s.mem a⟩

@[ext] theorem ext {s t : FSet α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t := by
  cases s; cases t
  congr
  funext a
  exact propext (h a)

def singleton (a : α) : FSet α := ⟨(· = a), ⟨[a], by simp⟩⟩
@[simp] theorem mem_singleton : b ∈ singleton a ↔ b = a := Iff.rfl

def ofList (xs : List α) : FSet α := ⟨(· ∈ xs), ⟨xs, fun _ => Iff.rfl⟩⟩
@[simp] theorem mem_ofList : a ∈ ofList xs ↔ a ∈ xs := Iff.rfl

noncomputable def elements (s : FSet α) : List α := s.finite.choose
theorem mem_elements (s : FSet α) (a : α) : a ∈ s.elements ↔ a ∈ s :=
  (s.finite.choose_spec a).symm

noncomputable def unionMap (s : FSet α) (f : α → FSet β) : FSet β where
  mem b := ∃ a, a ∈ s ∧ b ∈ f a
  finite := ⟨s.elements.flatMap (fun a => (f a).elements), by
    intro b
    simp only [List.mem_flatMap, mem_elements]⟩

@[simp] theorem mem_unionMap : b ∈ unionMap s f ↔ ∃ a, a ∈ s ∧ b ∈ f a := Iff.rfl

@[simp] theorem singleton_unionMap (a : α) (f : α → FSet β) :
    unionMap (singleton a) f = f a := by ext b; simp

@[simp] theorem unionMap_singleton (s : FSet α) : unionMap s singleton = s := by
  ext b; simp

theorem unionMap_assoc (s : FSet α) (f : α → FSet β) (g : β → FSet γ) :
    unionMap (unionMap s f) g = unionMap s (fun a => unionMap (f a) g) := by
  ext c
  simp only [mem_unionMap]
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, hc⟩
    exact ⟨a, ha, b, hb, hc⟩
  · rintro ⟨a, ha, b, hb, hc⟩
    exact ⟨b, ⟨a, ha, hb⟩, hc⟩
end FSet

structure NEFin (α : Type u) where
  set : FSet α
  inhabited : ∃ a, a ∈ set

namespace NEFin
instance : Membership α (NEFin α) := ⟨fun s a => a ∈ s.set⟩
@[ext] theorem ext {s t : NEFin α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t := by
  cases s; cases t
  congr 1
  exact FSet.ext h

def singleton (a : α) : NEFin α := ⟨FSet.singleton a, ⟨a, rfl⟩⟩
@[simp] theorem mem_singleton : b ∈ singleton a ↔ b = a := Iff.rfl

def ofHeadTail (a : α) (xs : List α) : NEFin α :=
  ⟨FSet.ofList (a :: xs), ⟨a, by simp⟩⟩
@[simp] theorem mem_ofHeadTail : b ∈ ofHeadTail a xs ↔ b = a ∨ b ∈ xs := by
  exact List.mem_cons

noncomputable def unionMap (s : NEFin α) (f : α → NEFin β) : NEFin β where
  set := s.set.unionMap (fun a => (f a).set)
  inhabited := by
    obtain ⟨a, ha⟩ := s.inhabited
    obtain ⟨b, hb⟩ := (f a).inhabited
    exact ⟨b, a, ha, hb⟩

@[simp] theorem mem_unionMap : b ∈ unionMap s f ↔ ∃ a, a ∈ s ∧ b ∈ f a := Iff.rfl
@[simp] theorem singleton_unionMap (a : α) (f : α → NEFin β) :
    unionMap (singleton a) f = f a := by ext b; simp
@[simp] theorem unionMap_singleton (s : NEFin α) : unionMap s singleton = s := by
  ext b; simp
theorem unionMap_assoc (s : NEFin α) (f : α → NEFin β) (g : β → NEFin γ) :
    unionMap (unionMap s f) g = unionMap s (fun a => unionMap (f a) g) := by
  ext c
  exact Iff.of_eq (congrArg (fun s : FSet _ => c ∈ s)
    (FSet.unionMap_assoc s.set (fun a => (f a).set) (fun b => (g b).set)))
end NEFin

inductive Outcome (State : Type u) (Value : Type v) where
  | live : State → Value → Outcome State Value
  | dead : State → Outcome State Value
  | undef : State → Outcome State Value
  deriving DecidableEq

def Outcome.state : Outcome S A → S
  | .live s _ | .dead s | .undef s => s

abbrev Terminal (S : Type u) (A : Type v) := NEFin (Outcome S A)
abbrev Run (S : Type u) (A : Type v) := S → Terminal S A

namespace Run
def pure (a : A) : Run S A := fun s => NEFin.singleton (.live s a)
def extend (k : A → Run S B) : Outcome S A → Terminal S B
  | .live s a => k a s
  | .dead s => NEFin.singleton (.dead s)
  | .undef s => NEFin.singleton (.undef s)
noncomputable def bind (m : Run S A) (k : A → Run S B) : Run S B :=
  fun s => (m s).unionMap (extend k)

@[simp] theorem pure_bind (a : A) (k : A → Run S B) : bind (pure a) k = k a := by
  funext s
  exact NEFin.singleton_unionMap _ _

@[simp] theorem extend_pure (z : Outcome S A) : extend pure z = NEFin.singleton z := by
  cases z <;> rfl

@[simp] theorem bind_pure (m : Run S A) : bind m pure = m := by
  funext s
  change (m s).unionMap (extend pure) = m s
  rw [show extend (pure : A → Run S A) = NEFin.singleton from funext extend_pure]
  exact NEFin.unionMap_singleton _

theorem extend_bind (z : Outcome S A) (k : A → Run S B) (l : B → Run S C) :
    (extend k z).unionMap (extend l) = extend (fun a => bind (k a) l) z := by
  cases z <;> simp [extend, bind]

theorem bind_assoc (m : Run S A) (k : A → Run S B) (l : B → Run S C) :
    bind (bind m k) l = bind m (fun a => bind (k a) l) := by
  funext s
  simp only [bind, NEFin.unionMap_assoc]
  congr 1
  funext z
  exact extend_bind z k l

theorem bind_congr (m m' : Run S A) (k k' : A → Run S B)
    (hm : ∀ s, m s = m' s) (hk : ∀ a s, k a s = k' a s) : bind m k = bind m' k' := by
  have hm' := funext hm
  have hk' : k = k' := funext (fun a => funext (hk a))
  rw [hm', hk']

theorem bind_finite (m : Run S A) (k : A → Run S B) (s : S) :
    ∃ xs : List (Outcome S B), ∀ z, z ∈ bind m k s ↔ z ∈ xs :=
  (bind m k s).set.finite
theorem bind_nonempty (m : Run S A) (k : A → Run S B) (s : S) :
    ∃ z, z ∈ bind m k s := (bind m k s).inhabited

/-- Successful projection can be empty. State/trace data is retained on live outputs. -/
def successes (t : Terminal S A) : S × A → Prop := fun p => .live p.1 p.2 ∈ t

@[simp] theorem successes_pure (a : A) (s t : S) (b : A) :
    successes (pure a s) (t, b) ↔ t = s ∧ b = a := by
  simp [successes, pure, Outcome.live.injEq]

theorem successes_bind (m : Run S A) (k : A → Run S B) (s t : S) (b : B) :
    successes (bind m k s) (t, b) ↔
      ∃ s' a, successes (m s) (s', a) ∧ successes (k a s') (t, b) := by
  simp only [successes, bind, NEFin.mem_unionMap]
  constructor
  · rintro ⟨z, hz, hb⟩
    cases z with
    | live s' a => exact ⟨s', a, hz, hb⟩
    | dead s' => simp [extend] at hb
    | undef s' => simp [extend] at hb
  · rintro ⟨s', a, ha, hb⟩
    exact ⟨.live s' a, ha, hb⟩
end Run
end SmusniF02
