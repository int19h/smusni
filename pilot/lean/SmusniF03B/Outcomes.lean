import SmusniF02.Host

namespace SmusniF03B
open SmusniF02

def negSK : Truth → Truth | .t => .f | .f => .t | .u => .u
@[simp] theorem negSK_involutive (status : Truth) : negSK (negSK status) = status := by cases status <;> rfl
theorem negSK_fixed (status : Truth) : status = negSK status ↔ status = .u := by cases status <;> simp [negSK]

noncomputable def image (f : A → B) (xs : NEFin A) : NEFin B :=
  xs.unionMap (fun x => NEFin.singleton (f x))
@[simp] theorem mem_image : y ∈ image f xs ↔ ∃ x, x ∈ xs ∧ y = f x := Iff.rfl

theorem image_comp (f : A → B) (g : B → C) (xs : NEFin A) :
    image g (image f xs) = image (fun x => g (f x)) xs := by
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

def flipOut : Outcome S Unit → Outcome S Unit
  | .live s _ => .dead s
  | .dead s => .live s ()
  | .undef s => .undef s
@[simp] theorem flipOut_involutive (z : Outcome S Unit) : flipOut (flipOut z) = z := by cases z <;> rfl
@[simp] theorem flipOut_truth (z : Outcome S Unit) : (flipOut z).truth = negSK z.truth := by cases z <;> rfl
@[simp] theorem flipOut_state (z : Outcome S Unit) : (flipOut z).state = z.state := by cases z <;> rfl

def Scalar (xs : Terminal S Unit) (status : Truth) : Prop := ∀ z, z ∈ xs → z.truth = status
theorem scalar_unique (xs : Terminal S Unit) (a b : Truth) (ha : Scalar xs a) (hb : Scalar xs b) : a = b := by
  obtain ⟨z, hz⟩ := xs.inhabited
  exact (ha z hz).symm.trans (hb z hz)

theorem scalar_image_flip (xs : Terminal S Unit) (status : Truth) (h : Scalar xs status) :
    Scalar (image flipOut xs) (negSK status) := by
  rintro y ⟨x, hx, rfl⟩
  rw [flipOut_truth, h x hx]

theorem scalar_fixed_is_undefined (xs : Terminal S Unit) (status : Truth)
    (fixed : xs = image flipOut xs) (h : Scalar xs status) : status = .u := by
  have hn := scalar_image_flip xs status h
  rw [← fixed] at hn
  exact (negSK_fixed status).mp (scalar_unique xs status (negSK status) h hn)

@[simp] theorem mem_neg_image (xs : NEFin Truth) (status : Truth) : status ∈ image negSK xs ↔ negSK status ∈ xs := by
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [negSK_involutive]; exact hx
  · intro h; exact ⟨negSK status, h, (negSK_involutive status).symm⟩
@[simp] theorem mem_flip_image (xs : Terminal S Unit) (z : Outcome S Unit) :
    z ∈ image flipOut xs ↔ flipOut z ∈ xs := by
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [flipOut_involutive]; exact hx
  · intro h; exact ⟨flipOut z, h, (flipOut_involutive z).symm⟩

def statusU : NEFin Truth := NEFin.singleton .u
def statusTF : NEFin Truth := NEFin.ofHeadTail .t [.f]
def statusTFU : NEFin Truth := NEFin.ofHeadTail .t [.f, .u]

theorem status_fixed_points (xs : NEFin Truth) :
    xs = image negSK xs ↔ xs = statusU ∨ xs = statusTF ∨ xs = statusTFU := by
  classical
  constructor
  · intro fixed
    have pair : Truth.f ∈ xs ↔ Truth.t ∈ xs := by
      have h := congrArg (fun s : NEFin Truth => Truth.f ∈ s) fixed
      simpa only [mem_neg_image, negSK] using Iff.of_eq h
    by_cases ht : Truth.t ∈ xs
    · have hf := pair.mpr ht
      by_cases hu : Truth.u ∈ xs
      · right; right; ext status; cases status <;> simp [statusTFU, ht, hf, hu]
      · right; left; ext status; cases status <;> simp [statusTF, ht, hf, hu]
    · have hf : ¬Truth.f ∈ xs := fun h => ht (pair.mp h)
      have hu : Truth.u ∈ xs := by
        obtain ⟨status, h⟩ := xs.inhabited
        cases status with
        | f => exact False.elim (hf h)
        | t => exact False.elim (ht h)
        | u => exact h
      left; ext status; cases status <;> simp [statusU, ht, hf, hu]
  · rintro (rfl | rfl | rfl) <;> ext status <;> cases status <;>
      simp [statusU, statusTF, statusTFU, negSK]

noncomputable def statuses (xs : Terminal S Unit) : NEFin Truth := image Outcome.truth xs
theorem statuses_flip (xs : Terminal S Unit) : statuses (image flipOut xs) = image negSK (statuses xs) := by
  simp only [statuses, image_comp]
  congr 1
  funext z
  exact flipOut_truth z

theorem status_fixed_necessary (xs : Terminal S Unit) (h : xs = image flipOut xs) :
    statuses xs = image negSK (statuses xs) := by
  have hs := congrArg statuses h
  rw [statuses_flip] at hs
  exact hs

def outAt (s : S) : Truth → Outcome S Unit | .t => .live s () | .f => .dead s | .u => .undef s
def SameState (xs : Terminal S Unit) (s : S) : Prop := ∀ z, z ∈ xs → z.state = s
theorem outAt_truth (s : S) (z : Outcome S Unit) (h : z.state = s) : outAt s z.truth = z := by
  cases z <;> cases h <;> rfl

theorem reconstruct_same_state (xs : Terminal S Unit) (s : S) (same : SameState xs s) :
    xs = image (outAt s) (statuses xs) := by
  ext z
  simp only [statuses, mem_image]
  constructor
  · intro h; exact ⟨z.truth, ⟨z, h, rfl⟩, (outAt_truth s z (same z h)).symm⟩
  · rintro ⟨status, ⟨x, hx, rfl⟩, rfl⟩
    simpa only [outAt_truth s x (same x hx)] using hx

def outcomeU (s : S) : Terminal S Unit := NEFin.singleton (.undef s)
def outcomeTF (s : S) : Terminal S Unit := NEFin.ofHeadTail (.live s ()) [.dead s]
def outcomeTFU (s : S) : Terminal S Unit := NEFin.ofHeadTail (.live s ()) [.dead s, .undef s]

theorem outAt_U (s : S) : image (outAt s) statusU = outcomeU s := by ext z; simp [statusU, outcomeU, outAt]
theorem outAt_TF (s : S) : image (outAt s) statusTF = outcomeTF s := by
  ext z; simp [statusTF, outcomeTF, outAt]
theorem outAt_TFU (s : S) : image (outAt s) statusTFU = outcomeTFU s := by
  ext z; simp [statusTFU, outcomeTFU, outAt]

theorem same_state_fixed_points (xs : Terminal S Unit) (s : S) (same : SameState xs s) :
    xs = image flipOut xs ↔ xs = outcomeU s ∨ xs = outcomeTF s ∨ xs = outcomeTFU s := by
  constructor
  · intro h
    have hs := (status_fixed_points (statuses xs)).mp (status_fixed_necessary xs h)
    have rebuild := reconstruct_same_state xs s same
    rcases hs with hs | hs | hs
    · left; simpa only [hs, outAt_U] using rebuild
    · right; left; simpa only [hs, outAt_TF] using rebuild
    · right; right; simpa only [hs, outAt_TFU] using rebuild
  · rintro (rfl | rfl | rfl) <;> ext z <;> cases z <;>
      simp [outcomeU, outcomeTF, outcomeTFU, flipOut, eq_comm]
end SmusniF03B
