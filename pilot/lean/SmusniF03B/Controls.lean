import SmusniF03B.Events
import SmusniF03B.Calls

/-! Mathematical discriminators, not a finite interpretation of the language.
No table dispatches on source text or chooses a cycle policy. -/
namespace SmusniF03B
open SmusniF02

theorem three_status_controls :
    statusU = image negSK statusU ∧ statusTF = image negSK statusTF ∧
    statusTFU = image negSK statusTFU :=
  ⟨(status_fixed_points _).mpr (Or.inl rfl),
   (status_fixed_points _).mpr (Or.inr (Or.inl rfl)),
   (status_fixed_points _).mpr (Or.inr (Or.inr rfl))⟩

theorem three_outcome_controls (s : S) :
    outcomeU s = image flipOut (outcomeU s) ∧
    outcomeTF s = image flipOut (outcomeTF s) ∧
    outcomeTFU s = image flipOut (outcomeTFU s) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext z <;> cases z <;>
    simp [outcomeU, outcomeTF, outcomeTFU, flipOut, eq_comm]

def mixedState : Terminal Bool Unit := NEFin.ofHeadTail (.live false ()) [.dead true]

theorem mixed_state_statuses : statuses mixedState = statusTF := by
  ext status; cases status <;> simp [statuses, mem_image, mixedState, statusTF, Outcome.truth]

theorem mixed_state_status_fixed : statuses mixedState = image negSK (statuses mixedState) := by
  rw [mixed_state_statuses]
  exact three_status_controls.2.1

theorem mixed_state_not_fixed : mixedState ≠ image flipOut mixedState := by
  intro fixed
  have hx : Outcome.live false () ∈ mixedState := by simp [mixedState]
  rw [fixed] at hx
  have hd := (mem_flip_image mixedState (.live false ())).mp hx
  simp [mixedState, flipOut] at hd

theorem mixed_state_not_same_state : ¬∃ s, SameState mixedState s := by
  rintro ⟨s, same⟩
  have hf := same (.live false ()) (by simp [mixedState])
  have ht := same (.dead true) (by simp [mixedState])
  have : false = true := hf.trans ht.symm
  cases this

def SomeLive (xs : Terminal S Unit) : Prop := ∃ s, Outcome.live s () ∈ xs

theorem mixed_success_cost (s : S) :
    SomeLive (outcomeTF s) ∧ SomeLive (image flipOut (outcomeTF s)) ∧
    SomeLive (outcomeTFU s) ∧ SomeLive (image flipOut (outcomeTFU s)) ∧
    Outcome.undef s ∈ outcomeTFU s := by
  simp [SomeLive, outcomeTF, outcomeTFU, flipOut]

theorem mixed_not_scalar (s : S) : ¬∃ status, Scalar (outcomeTF s) status := by
  rintro ⟨status, scalar⟩
  have live := scalar (.live s ()) (by simp [outcomeTF])
  have dead := scalar (.dead s) (by simp [outcomeTF])
  have : Truth.t = .f := live.trans dead.symm
  cases this

/-- Reporting success of each mixed family as scalar T violates scalar negation. -/
theorem two_successes_not_scalar_SK : Truth.t ≠ negSK Truth.t := by decide

def multipleUndefined : Terminal Bool Unit := NEFin.ofHeadTail (.undef false) [.undef true]

theorem multiple_undefined_scalar : Scalar multipleUndefined .u := by
  intro z hz
  simp only [multipleUndefined, NEFin.mem_ofHeadTail, List.mem_singleton] at hz
  rcases hz with rfl | rfl <;> rfl

theorem multiple_undefined_not_singleton : ¬∃ z, multipleUndefined = NEFin.singleton z := by
  rintro ⟨z, eq⟩
  have hf : Outcome.undef false ∈ multipleUndefined := by simp [multipleUndefined]
  have ht : Outcome.undef true ∈ multipleUndefined := by simp [multipleUndefined]
  rw [eq] at hf ht
  have : (Outcome.undef false : Outcome Bool Unit) = .undef true :=
    (NEFin.mem_singleton.mp hf).trans (NEFin.mem_singleton.mp ht).symm
  cases this

/-- The scalar contract alone cannot constrain reached states as SetNeg does. -/
theorem scalar_law_without_set_flip :
    (∀ status, Scalar (outcomeU false) status → Scalar (outcomeU true) (negSK status)) ∧
    outcomeU true ≠ image flipOut (outcomeU false) := by
  constructor
  · intro status scalar
    have hs := scalar (.undef false) (by simp [outcomeU])
    change Truth.u = status at hs
    rw [← hs]
    exact singleton_scalar (.undef true)
  · rw [← (three_outcome_controls false).1]
    intro eq
    have hz : Outcome.undef true ∈ outcomeU true := by simp [outcomeU]
    rw [eq] at hz
    simp [outcomeU] at hz

/-- Equal run observations supply no event value and no event co-reference. -/
theorem scalar_not_event_identity :
    Scalar (outcomeU ()) .u ∧
    ¬PartialEq (Eq : Bool → Bool → Prop) none (some false) ∧
    ¬PartialEq (Eq : Bool → Bool → Prop) (some false) (some true) := by
  exact ⟨singleton_scalar (.undef ()), by simp [PartialEq], by simp [PartialEq]⟩

theorem no_missing_holding (h : Event) : ¬PartialEq coRef none (some h) := by
  simp [PartialEq]

/-- Strict Bind forwards Undef and Dead without evaluating a successful body. -/
theorem strict_no_return_controls (s : S) (k : P → Run S Unit) :
    Run.bind (fun _ => NEFin.singleton (.undef s)) k s = NEFin.singleton (.undef s) ∧
    Run.bind (fun _ => NEFin.singleton (.dead s)) k s = NEFin.singleton (.dead s) := by
  simp [Run.bind, Run.extend]
end SmusniF03B
