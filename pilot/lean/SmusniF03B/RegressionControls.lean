import SmusniF03B.Controls

/- Reviewer controls for commit 208904bc13330adf0270f42464c919e476f2717a.
These instantiate the supplied contracts. They are not a Lojban model. -/
namespace AstraPR101
open SmusniF03B SmusniF02 SmusniPilot

def D : Domains where
  Profile := Nat
  Source := Nat
  Context := Nat
  World := Nat
  State := Nat
  Key := Nat
  Dependencies := List Nat
  Segment := Nat

def observations (family : Nat → Terminal Nat Unit) : Observations D Unit where
  run _ xi := family xi.caller
  valueRun _ xi := NEFin.singleton (.live xi.caller ())
  bodyRun _ _ xi := family xi.caller
  reifyValue _ := ()
  resolve _ := some ()
  admits _ := True
  replay _ xi := xi
  noIntroductions _ _ := True
  noEmissions _ _ := True
  unchangedInput _ _ := True
  valueNoEmissions _ _ := True

theorem laws (family : Nat → Terminal Nat Unit) : RunLaws (observations family) where
  contextSuccess _ _ _ resolved := by
    cases resolved
    exact ⟨rfl, True.intro⟩
  strictBind _ _ _ := by
    simp [observations, Run.bind, Run.extend, Input.atState]
    rfl
  substitution _ _ _ := rfl
  roundTrip _ _ := rfl

theorem replay (family : Nat → Terminal Nat Unit) (xi : Input D) :
    ReplayAt ((observations family).replay (L xi.site) xi) xi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem readonly (family : Nat → Terminal Nat Unit) (c : Term 0) (xi : Input D) :
    ReadOnlyUse (observations family) c xi := ⟨True.intro, True.intro, True.intro⟩

/- The complete RunLaws bundle plus exact Context retrieval and the scalar
negation contract does not imply a scalar observation for L. -/
theorem mixed_sk : ScalarNegation (observations outcomeTF) := by
  intro c xi status _ scalar
  exact False.elim (mixed_not_scalar xi.caller ⟨status, scalar⟩)

theorem mixed_candidate (xi : Input D) :
    RunLaws (observations outcomeTF) ∧
    ScalarNegation (observations outcomeTF) ∧
    (observations outcomeTF).admits xi.context ∧
    (observations outcomeTF).resolve xi = some ((observations outcomeTF).reifyValue (L xi.site)) ∧
    ReadOnlyUse (observations outcomeTF) (H xi.site) xi ∧
    ¬∃ status, Scalar ((observations outcomeTF).run (L xi.site) xi) status :=
  ⟨laws _, mixed_sk, True.intro, rfl, readonly _ _ _, mixed_not_scalar xi.caller⟩

theorem mixed_set_result (xi : Input D) :
    (observations outcomeTF).run (L xi.site) xi =
      image flipOut ((observations outcomeTF).run (L xi.site) xi) := by
  apply conditional_set_fixed (laws _) xi True.intro rfl (replay _ xi)
  exact (three_outcome_controls xi.caller).2.1

theorem mixed_call_result (xi : Input D) :
    Calls (observations outcomeTF) (L xi.site, xi) (N xi.site, xi) ∧
    Calls (observations outcomeTF) (N xi.site, xi) (H xi.site, xi) ∧
    Calls (observations outcomeTF) (H xi.site, xi) (L xi.site, xi) :=
  call_cycle (laws _) xi True.intro rfl (replay _ xi)

/- All event observations can remain undefined while the supplied event laws
hold. Nonidentity coordinate maps do not create a missing holding value. -/
def absentEvents : EventObservations D Unit Nat Nat where
  event _ _ _ := none
  bodyEvent _ _ _ _ := none
  holding _ _ _ := none
  bindCoordinate _ _ _ _ beta := beta + 7
  substitutionCoordinate _ _ _ beta := beta * 3
  roundTripCoordinate _ _ beta := beta + 11

theorem absent_event_laws (family : Nat → Terminal Nat Unit) :
    EventLaws (observations family) absentEvents Eq where
  successfulBind _ _ _ _ _ _ _ := True.intro
  substitution _ _ _ _ := True.intro
  roundTrip _ _ _ := True.intro
  negative _ _ _ := True.intro

theorem absent_event_result (xi : Input D) (beta : Nat) :
    PartialEq Eq (absentEvents.event (L xi.site) xi beta)
      (absentEvents.event (N xi.site) xi (negativeCoordinate (observations outcomeTF) absentEvents xi beta)) :=
  event_L_eq_N (laws _) (absent_event_laws _) (fun _ _ _ => Eq.trans) xi True.intro rfl beta

theorem no_holding_value (xi : Input D) (beta : Nat) :
    ¬∃ h, absentEvents.holding (N xi.site) xi
      (negativeCoordinate (observations outcomeTF) absentEvents xi beta) = some h := by
  simp [absentEvents]

end AstraPR101

/- Fable reviewer control for commit 208904bc13330adf0270f42464c919e476f2717a.
Purpose: show that the complete hypothesis list of `conditional_scalar` and of
`conditional_set_fixed` is jointly satisfiable, so neither theorem is true only
because its premises contradict each other. Astra's first probe shows the
contracts do not force a scalar; this one shows they admit one. It is a
diagnostic instantiation of the supplied contracts, not a model of Lojban. -/
namespace FablePR101
open SmusniF03B SmusniF02 SmusniPilot

def D : Domains where
  Profile := Nat
  Source := Nat
  Context := Nat
  World := Nat
  State := Nat
  Key := Nat
  Dependencies := List Nat
  Segment := Nat

/-- Every content run is undefined at the caller state; Context retrieval succeeds. -/
def undefinedEverywhere : Observations D Unit where
  run _ xi := outcomeU xi.caller
  valueRun _ xi := NEFin.singleton (.live xi.caller ())
  bodyRun _ _ xi := outcomeU xi.caller
  reifyValue _ := ()
  resolve _ := some ()
  admits _ := True
  replay _ xi := xi
  noIntroductions _ _ := True
  noEmissions _ _ := True
  unchangedInput _ _ := True
  valueNoEmissions _ _ := True

theorem laws : RunLaws undefinedEverywhere where
  contextSuccess _ _ _ resolved := by
    cases resolved
    exact ⟨rfl, True.intro⟩
  strictBind _ _ _ := by
    simp [undefinedEverywhere, Run.bind, Run.extend, Input.atState]
  substitution _ _ _ := rfl
  roundTrip _ _ := rfl

theorem replay (xi : Input D) :
    ReplayAt (undefinedEverywhere.replay (L xi.site) xi) xi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem readonly (c : Term 0) (xi : Input D) :
    ReadOnlyUse undefinedEverywhere c xi := ⟨True.intro, True.intro, True.intro⟩

/-- The scalar law holds here with a real antecedent, not vacuously. -/
theorem scalar_negation : ScalarNegation undefinedEverywhere := by
  intro c xi status _ scalar
  have hu : status = .u := by
    have h := scalar (.undef xi.caller) (by simp [undefinedEverywhere, outcomeU])
    exact h.symm
  subst hu
  exact singleton_scalar (.undef xi.caller)

theorem scalar_exists (xi : Input D) :
    Scalar (undefinedEverywhere.run (L xi.site) xi) .u :=
  singleton_scalar (.undef xi.caller)

/-- All nine premises of `conditional_scalar` hold at once, and it instantiates. -/
theorem scalar_premises_consistent (xi : Input D) :
    RunLaws undefinedEverywhere ∧
    undefinedEverywhere.admits xi.context ∧
    undefinedEverywhere.resolve xi = some (undefinedEverywhere.reifyValue (L xi.site)) ∧
    ReplayAt (undefinedEverywhere.replay (L xi.site) xi) xi ∧
    ReadOnlyUse undefinedEverywhere (H xi.site) xi ∧
    ScalarNegation undefinedEverywhere ∧
    Scalar (undefinedEverywhere.run (L xi.site) xi) .u :=
  ⟨laws, True.intro, rfl, replay xi, readonly _ _, scalar_negation, scalar_exists xi⟩

theorem scalar_result (xi : Input D) (status : Truth)
    (scalar : Scalar (undefinedEverywhere.run (L xi.site) xi) status) : status = .u :=
  conditional_scalar laws xi True.intro rfl (replay xi) (readonly _ _) scalar_negation status scalar

/-- SetNeg also holds here, so the set theorem's premises are jointly satisfiable. -/
theorem set_neg (xi : Input D) : SetNeg undefinedEverywhere xi := by
  unfold SetNeg
  change outcomeU xi.caller = image flipOut (outcomeU xi.caller)
  exact (three_outcome_controls xi.caller).1

theorem set_result (xi : Input D) :
    undefinedEverywhere.run (L xi.site) xi =
      image flipOut (undefinedEverywhere.run (L xi.site) xi) :=
  conditional_set_fixed laws xi True.intro rfl (replay xi) (set_neg xi)
end FablePR101
