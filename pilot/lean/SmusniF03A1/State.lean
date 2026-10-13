import SmusniF03A1.Maps

namespace SmusniF03A1
open SmusniF02
universe u v w x y

def mapSide (f : A → B) (side : ClosedSide A) : ClosedSide B := ⟨f side.anchor, side.holds⟩
def SideRel (R : A → B → Prop) (s : ClosedSide A) (t : ClosedSide B) : Prop :=
  R s.anchor t.anchor ∧ s.holds = t.holds

theorem side_kernel (f : A → B) (R : A → A → Prop) (ker : Kernel f R) :
    Kernel (mapSide f) (SideRel R) := by
  intro s t; cases s; cases t; simp [mapSide, SideRel, ker]

theorem side_onto (f : A → B) (onto : Onto f) : Onto (mapSide f) := by
  intro side
  obtain ⟨a, ha⟩ := onto side.anchor
  exact ⟨⟨a, side.holds⟩, by cases side; simp_all [mapSide]⟩

def mapState (fv : V → V') (fa : A → A') (s : HostState N V A H) : HostState N V' A' H where
  assignment n := (s.assignment n).map fv
  sides := s.sides.map (mapSide fa)
  history := s.history
  kappa := s.kappa
  chi := s.chi

def StateRel (VR : V → V' → Prop) (AR : A → A' → Prop)
    (s : HostState N V A H) (t : HostState N V' A' H) : Prop :=
  (∀ n, OptionRel VR (s.assignment n) (t.assignment n)) ∧
  ListRel (SideRel AR) s.sides t.sides ∧
  s.history = t.history ∧ s.kappa = t.kappa ∧ s.chi = t.chi

@[ext] theorem state_ext {s t : HostState N V A H}
    (assignment : s.assignment = t.assignment) (sides : s.sides = t.sides)
    (history : s.history = t.history) (kappa : s.kappa = t.kappa) (chi : s.chi = t.chi) : s = t := by
  cases s; cases t; simp_all

theorem state_kernel (fv : V → V') (fa : A → A') (VR : V → V → Prop) (AR : A → A → Prop)
    (kv : Kernel fv VR) (ka : Kernel fa AR) :
    Kernel (mapState (N := N) (H := H) fv fa) (StateRel VR AR) := by
  intro s t
  constructor
  · intro eq
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact (option_kernel fv VR kv _ _).mp (congrArg (fun s => s.assignment n) eq)
    · exact (list_kernel (mapSide fa) (SideRel AR) (side_kernel fa AR ka) _ _).mp
        (congrArg HostState.sides eq)
    · exact congrArg (fun x : HostState N V' A' H => x.history) eq
    · exact congrArg (fun x : HostState N V' A' H => x.kappa) eq
    · exact congrArg (fun x : HostState N V' A' H => x.chi) eq
  · rintro ⟨assign, sides, history, kappa, chi⟩
    apply state_ext
    · funext n; exact (option_kernel fv VR kv _ _).mpr (assign n)
    · exact (list_kernel (mapSide fa) (SideRel AR) (side_kernel fa AR ka) _ _).mpr sides
    · exact history
    · exact kappa
    · exact chi

/-- Coverage includes arbitrary assignment functions and every finite ordered side list. -/
theorem state_onto (fv : V → V') (fa : A → A') (ov : Onto fv) (oa : Onto fa) :
    Onto (mapState (N := N) (H := H) fv fa) := by
  classical
  intro target
  let assign := fun n => (option_onto fv ov (target.assignment n)).choose
  obtain ⟨sides, hs⟩ := list_onto (mapSide fa) (side_onto fa oa) target.sides
  refine ⟨⟨assign, sides, target.history, target.kappa, target.chi⟩, ?_⟩
  apply state_ext
  · funext n; exact (option_onto fv ov (target.assignment n)).choose_spec
  · exact hs
  · rfl
  · rfl
  · rfl

abbrev ValueRel {G : Type u} (R : Setoid P) := TagRel (G := G) R.r
abbrev AnchorRel {G : Type u} (R : Setoid P) := TagRel (G := G) R.r
abbrev qValue {G : Type u} (R : Setoid P) := qTag (G := G) R
abbrev qAnchor {G : Type u} (R : Setoid P) := qTag (G := G) R
abbrev RawState (N : Type u) (G : Type v) (GA : Type w) (P : Type x) (H : Type y) :=
  HostState N (G ⊕ P) (GA ⊕ P) H
abbrev QuotientState (N : Type u) (G : Type v) (GA : Type w) (P : Type x) (H : Type y) (R : Setoid P) :=
  HostState N (G ⊕ Quotient R) (GA ⊕ Quotient R) H

def qState (R : Setoid P) : RawState N G GA P H → QuotientState N G GA P H R :=
  mapState (qValue R) (qAnchor R)

theorem qState_kernel (R : Setoid P) :
    Kernel (qState (N := N) (G := G) (GA := GA) (H := H) R) (StateRel (ValueRel R) (AnchorRel R)) :=
  state_kernel _ _ _ _ (tag_kernel R) (tag_kernel R)

theorem qState_onto (R : Setoid P) : Onto (qState (N := N) (G := G) (GA := GA) (H := H) R) :=
  state_onto _ _ (tag_onto R) (tag_onto R)

def OutRel (SR : S → T → Prop) (AR : A → B → Prop) : Outcome S A → Outcome T B → Prop
  | .live s a, .live t b => SR s t ∧ AR a b
  | .dead s, .dead t | .undef s, .undef t => SR s t
  | _, _ => False

def mapOutcome (fs : S → T) (fa : A → B) : Outcome S A → Outcome T B
  | .live s a => .live (fs s) (fa a)
  | .dead s => .dead (fs s)
  | .undef s => .undef (fs s)

@[simp] theorem mapOutcome_state (fs : S → T) (fa : A → B) (z : Outcome S A) :
    (mapOutcome fs fa z).state = fs z.state := by cases z <;> rfl
@[simp] theorem mapOutcome_truth (fs : S → T) (fa : A → B) (z : Outcome S A) :
    (mapOutcome fs fa z).truth = z.truth := by cases z <;> rfl

theorem outcome_kernel (fs : S → T) (fa : A → B) (SR : S → S → Prop) (AR : A → A → Prop)
    (ks : Kernel fs SR) (ka : Kernel fa AR) : Kernel (mapOutcome fs fa) (OutRel SR AR) := by
  intro x y; cases x <;> cases y <;> simp [mapOutcome, OutRel, ks, ka]

theorem outcome_onto (fs : S → T) (fa : A → B) (os : Onto fs) (oa : Onto fa) :
    Onto (mapOutcome fs fa) := by
  intro z; cases z with
  | live s a =>
    obtain ⟨t, rfl⟩ := os s; obtain ⟨b, rfl⟩ := oa a
    exact ⟨.live t b, rfl⟩
  | dead s => obtain ⟨t, rfl⟩ := os s; exact ⟨.dead t, rfl⟩
  | undef s => obtain ⟨t, rfl⟩ := os s; exact ⟨.undef t, rfl⟩

def qOutcome (R : Setoid P) (AR : Setoid A) :
    Outcome (RawState N G GA P H) A → Outcome (QuotientState N G GA P H R) (Quotient AR) :=
  mapOutcome (qState R) (Quotient.mk AR)

theorem qOutcome_kernel (R : Setoid P) (AR : Setoid A) :
    Kernel (qOutcome (N := N) (G := G) (GA := GA) (H := H) R AR)
      (OutRel (StateRel (ValueRel R) (AnchorRel R)) AR.r) :=
  outcome_kernel _ _ _ _ (qState_kernel R) (quotient_kernel AR)

theorem qOutcome_onto (R : Setoid P) (AR : Setoid A) :
    Onto (qOutcome (N := N) (G := G) (GA := GA) (H := H) R AR) :=
  outcome_onto _ _ (qState_onto R) (quotient_onto AR)

theorem qResults_kernel (R : Setoid P) (AR : Setoid A) :
    Kernel (mapResults (qOutcome (N := N) (G := G) (GA := GA) (H := H) R AR))
      (FinRel (OutRel (StateRel (ValueRel R) (AnchorRel R)) AR.r)) :=
  finite_kernel _ _ (qOutcome_kernel R AR)

theorem qResults_onto (R : Setoid P) (AR : Setoid A) :
    Onto (mapResults (qOutcome (N := N) (G := G) (GA := GA) (H := H) R AR)) :=
  finite_onto _ (qOutcome_onto R AR)
end SmusniF03A1
