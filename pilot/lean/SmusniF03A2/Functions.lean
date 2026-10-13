import SmusniF03A1.Maps

namespace SmusniF03A2
open SmusniF03A1

def Respect (AR : Setoid A) (BR : Setoid B) (f : A → B) : Prop :=
  ∀ a b, AR.r a b → BR.r (f a) (f b)
abbrev Respectful (AR : Setoid A) (BR : Setoid B) := {f : A → B // Respect AR BR f}

def FunRel (AR : Setoid A) (BR : Setoid B) (f g : A → B) : Prop :=
  ∀ a b, AR.r a b → BR.r (f a) (g b)

/-- The respect proof is the well-definedness argument to the actual quotient lift. -/
def qFun (AR : Setoid A) (BR : Setoid B) (f : Respectful AR BR) : Quotient AR → Quotient BR :=
  Quotient.lift (fun a => Quotient.mk BR (f.val a))
    (fun a b h => Quotient.sound (f.property a b h))

@[simp] theorem qFun_at (AR : Setoid A) (BR : Setoid B) (f : Respectful AR BR) (a : A) :
    qFun AR BR f (Quotient.mk AR a) = Quotient.mk BR (f.val a) := rfl

theorem qFun_kernel (AR : Setoid A) (BR : Setoid B) :
    Kernel (qFun AR BR) (fun f g => FunRel AR BR f.val g.val) := by
  intro f g
  constructor
  · intro eq a b related
    apply Quotient.exact
    change qFun AR BR f (Quotient.mk AR a) = qFun AR BR g (Quotient.mk AR b)
    rw [eq, Quotient.sound related]
  · intro related
    funext q
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    exact Quotient.sound (related a a (AR.refl a))

/-- Only the represented image is named. No unrestricted function admission. -/
abbrev FunctionImage (AR : Setoid A) (BR : Setoid B) :=
  {g : Quotient AR → Quotient BR // ∃ f : Respectful AR BR, qFun AR BR f = g}

def representedFun (AR : Setoid A) (BR : Setoid B) (f : Respectful AR BR) : FunctionImage AR BR :=
  ⟨qFun AR BR f, f, rfl⟩

theorem representedFun_onto (AR : Setoid A) (BR : Setoid B) : Onto (representedFun AR BR) := by
  intro g
  obtain ⟨f, hf⟩ := g.property
  exact ⟨f, Subtype.ext hf⟩

theorem representedFun_kernel (AR : Setoid A) (BR : Setoid B) :
    Kernel (representedFun AR BR) (fun f g => FunRel AR BR f.val g.val) := by
  intro f g
  constructor
  · intro eq; exact (qFun_kernel AR BR f g).mp (congrArg Subtype.val eq)
  · intro rel; exact Subtype.ext ((qFun_kernel AR BR f g).mpr rel)
end SmusniF03A2
