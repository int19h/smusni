import SmusniF02.Host

/-! General map kernels and finite-family images. No diagnostic instance is used
to compute any map or establish any general transport theorem. -/
namespace SmusniF03A1
open SmusniF02

abbrev Onto (f : A → B) : Prop := ∀ b, ∃ a, f a = b
abbrev Kernel (f : A → B) (R : A → A → Prop) : Prop := ∀ a b, f a = f b ↔ R a b

/-- Ordered pointwise list relation (the design's List.Forall2). -/
def ListRel (R : A → B → Prop) : List A → List B → Prop
  | [], [] => True
  | a :: xs, b :: ys => R a b ∧ ListRel R xs ys
  | _, _ => False

def OptionRel (R : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem option_kernel (f : A → B) (R : A → A → Prop) (ker : Kernel f R) :
    Kernel (Option.map f) (OptionRel R) := by
  intro a b; cases a <;> cases b <;> simp [OptionRel, ker]

theorem option_onto (f : A → B) (onto : Onto f) : Onto (Option.map f) := by
  intro b; cases b with
  | none => exact ⟨none, rfl⟩
  | some b => obtain ⟨a, rfl⟩ := onto b; exact ⟨some a, rfl⟩

theorem list_kernel (f : A → B) (R : A → A → Prop) (ker : Kernel f R) :
    Kernel (List.map f) (ListRel R) := by
  intro xs ys
  induction xs generalizing ys with
  | nil => cases ys <;> simp [ListRel]
  | cons x xs ih => cases ys <;> simp [ListRel, ker, ih]

theorem list_onto (f : A → B) (onto : Onto f) : Onto (List.map f) := by
  intro ys
  induction ys with
  | nil => exact ⟨[], rfl⟩
  | cons y ys ih =>
    obtain ⟨x, rfl⟩ := onto y
    obtain ⟨xs, rfl⟩ := ih
    exact ⟨x :: xs, rfl⟩

def TagRel (R : P → P → Prop) : G ⊕ P → G ⊕ P → Prop
  | .inl g, .inl h => g = h
  | .inr p, .inr q => R p q
  | _, _ => False

def qTag (R : Setoid P) : G ⊕ P → G ⊕ Quotient R
  | .inl g => .inl g
  | .inr p => .inr (Quotient.mk R p)

theorem quotient_kernel (R : Setoid P) : Kernel (Quotient.mk R) R.r :=
  fun _ _ => ⟨Quotient.exact, Quotient.sound⟩
theorem quotient_onto (R : Setoid P) : Onto (Quotient.mk R) := Quotient.exists_rep

theorem tag_kernel (R : Setoid P) : Kernel (qTag (G := G) R) (TagRel R.r) := by
  intro a b; cases a <;> cases b <;> simp [qTag, TagRel, quotient_kernel R]

theorem tag_onto (R : Setoid P) : Onto (qTag (G := G) R) := by
  intro y; cases y with
  | inl g => exact ⟨.inl g, rfl⟩
  | inr q => obtain ⟨p, rfl⟩ := quotient_onto R q; exact ⟨.inr p, rfl⟩

noncomputable def mapResults (f : A → B) (xs : NEFin A) : NEFin B :=
  xs.unionMap (fun x => NEFin.singleton (f x))
@[simp] theorem mem_mapResults : y ∈ mapResults f xs ↔ ∃ x, x ∈ xs ∧ y = f x := Iff.rfl
@[simp] theorem mapResults_singleton (f : A → B) (a : A) :
    mapResults f (NEFin.singleton a) = NEFin.singleton (f a) := by ext b; simp

def FinRel (R : A → B → Prop) (xs : NEFin A) (ys : NEFin B) : Prop :=
  (∀ x, x ∈ xs → ∃ y, y ∈ ys ∧ R x y) ∧
  (∀ y, y ∈ ys → ∃ x, x ∈ xs ∧ R x y)

theorem finite_kernel (f : A → B) (R : A → A → Prop) (ker : Kernel f R) :
    Kernel (mapResults f) (FinRel R) := by
  intro xs ys
  constructor
  · intro eq
    constructor
    · intro x hx
      have hx' : f x ∈ mapResults f ys := by rw [← eq]; exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, he⟩ := hx'
      exact ⟨y, hy, (ker x y).mp he⟩
    · intro y hy
      have hy' : f y ∈ mapResults f xs := by rw [eq]; exact ⟨y, hy, rfl⟩
      obtain ⟨x, hx, he⟩ := hy'
      exact ⟨x, hx, (ker x y).mp he.symm⟩
  · intro rel
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := rel.1 x hx
      exact ⟨y, hy, (ker x y).mpr hxy⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := rel.2 y hy
      exact ⟨x, hx, ((ker x y).mpr hxy).symm⟩

theorem mapResults_comp (f : A → B) (g : B → C) (xs : NEFin A) :
    mapResults g (mapResults f xs) = mapResults (fun x => g (f x)) xs := by
  ext c
  simp only [mem_mapResults]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

theorem finite_onto (f : A → B) (onto : Onto f) : Onto (mapResults f) := by
  classical
  intro ys
  refine ⟨mapResults (fun b => (onto b).choose) ys, ?_⟩
  rw [mapResults_comp]
  have h : (fun b => f (onto b).choose) = id := funext (fun b => (onto b).choose_spec)
  rw [h]
  ext b; simp

theorem finRel_singleton (R : A → B → Prop) (a : A) (b : B) (rel : R a b) :
    FinRel R (NEFin.singleton a) (NEFin.singleton b) := by
  constructor <;> intro x hx <;> have eq := NEFin.mem_singleton.mp hx <;> subst x
  · exact ⟨b, rfl, rel⟩
  · exact ⟨a, rfl, rel⟩

theorem finRel_unionMap (R : A → B → Prop) (T : C → D → Prop)
    (xs : NEFin A) (ys : NEFin B) (f : A → NEFin C) (g : B → NEFin D)
    (input : FinRel R xs ys) (body : ∀ a b, R a b → FinRel T (f a) (g b)) :
    FinRel T (xs.unionMap f) (ys.unionMap g) := by
  constructor
  · rintro c ⟨a, ha, hc⟩
    obtain ⟨b, hb, hab⟩ := input.1 a ha
    obtain ⟨d, hd, hcd⟩ := (body a b hab).1 c hc
    exact ⟨d, ⟨b, hb, hd⟩, hcd⟩
  · rintro d ⟨b, hb, hd⟩
    obtain ⟨a, ha, hab⟩ := input.2 b hb
    obtain ⟨c, hc, hcd⟩ := (body a b hab).2 d hd
    exact ⟨c, ⟨a, ha, hc⟩, hcd⟩
end SmusniF03A1
