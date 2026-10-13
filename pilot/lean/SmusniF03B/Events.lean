import SmusniF03B.Conditional
import SmusniF02.Content

namespace SmusniF03B
open SmusniF02 SmusniPilot SmusniPilot.M2

theorem partial_trans (coRef : E → E → Prop)
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    {a b c : Option E} (ab : PartialEq coRef a b) (bc : PartialEq coRef b c) :
    PartialEq coRef a c := by
  cases a <;> cases b <;> cases c <;> simp_all [PartialEq]
  exact trans _ _ _ ab bc

/-- Beta is supplied independently of runs, states, and successful branches. -/
structure EventObservations (D : Domains) (P Beta Event : Type) where
  event : Term 0 → Input D → Beta → Option Event
  bodyEvent : Term 1 → P → Input D → Beta → Option Event
  holding : Term 0 → Input D → Beta → Option Event
  bindCoordinate : Term 0 → Term 1 → P → Input D → Beta → Beta
  substitutionCoordinate : Term 1 → Term 0 → Input D → Beta → Beta
  roundTripCoordinate : Term 0 → Input D → Beta → Beta

structure EventLaws (M : Observations D P) (E : EventObservations D P Beta Event)
    (coRef : Event → Event → Prop) : Prop where
  successfulBind : ∀ c b xi p beta,
    M.valueRun c xi = NEFin.singleton (.live xi.caller p) →
    M.valueNoEmissions c xi →
    PartialEq coRef (E.event (.bind Ty.proposition c b) xi beta)
      (E.bodyEvent b p xi (E.bindCoordinate c b p xi beta))
  substitution : ∀ b q xi beta,
    PartialEq coRef (E.bodyEvent b (M.reifyValue q) xi beta)
      (E.event (instantiate b (reify q)) xi (E.substitutionCoordinate b q xi beta))
  roundTrip : ∀ q xi beta,
    PartialEq coRef (E.event (holds (reify q)) xi beta)
      (E.event q (M.replay q xi) (E.roundTripCoordinate q xi beta))
  negative : ∀ c xi beta,
    PartialEq coRef (E.event (neg c) xi beta) (E.holding (neg c) xi beta)

def negativeCoordinate (M : Observations D P) (E : EventObservations D P Beta Event)
    (xi : Input D) (beta : Beta) : Beta :=
  E.substitutionCoordinate body (L xi.site) xi
    (E.bindCoordinate (source xi.site) body (M.reifyValue (L xi.site)) xi beta)

variable {M : Observations D P} {E : EventObservations D P Beta Event}
variable {coRef : Event → Event → Prop}

theorem event_L_eq_N (laws : RunLaws M) (events : EventLaws M E coRef)
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    (xi : Input D) (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site))) (beta : Beta) :
    PartialEq coRef (E.event (L xi.site) xi beta)
      (E.event (N xi.site) xi (negativeCoordinate M E xi beta)) := by
  have success := laws.contextSuccess xi _ admitted resolved
  have hb := events.successfulBind (source xi.site) body xi _ beta success.exactRun success.noEmission
  have hs := events.substitution body (L xi.site) xi
    (E.bindCoordinate (source xi.site) body (M.reifyValue (L xi.site)) xi beta)
  exact partial_trans coRef trans hb hs

theorem event_H_eq_L (events : EventLaws M E coRef) (xi : Input D)
    (replay : ReplayAt (M.replay (L xi.site) xi) xi) (beta : Beta) :
    PartialEq coRef (E.event (H xi.site) xi beta)
      (E.event (L xi.site) xi (E.roundTripCoordinate (L xi.site) xi beta)) := by
  have h := events.roundTrip (L xi.site) xi beta
  rw [replay.eq] at h
  exact h

/-- Holding values remain partial. This theorem requires one supplied value. -/
theorem event_constraint (laws : RunLaws M) (events : EventLaws M E coRef)
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    (xi : Input D) (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site))) (beta : Beta)
    (hN : Event)
    (supplied : E.holding (N xi.site) xi (negativeCoordinate M E xi beta) = some hN) :
    PartialEq coRef (E.event (L xi.site) xi beta) (some hN) := by
  have hn := events.negative (H xi.site) xi (negativeCoordinate M E xi beta)
  change PartialEq coRef (E.event (N xi.site) xi _) (E.holding (N xi.site) xi _) at hn
  rw [supplied] at hn
  exact partial_trans coRef trans (event_L_eq_N laws events trans xi admitted resolved beta) hn

/-- Full observations, not equality of one scalar or one run at one input. -/
def JointIdentity (M : Observations D P) (E : EventObservations D P Beta Event)
    (coRef : Event → Event → Prop) (c d : Term 0) : Prop :=
  (∀ xi, M.run c xi = M.run d xi) ∧
  (∀ xi beta, PartialEq coRef (E.event c xi beta) (E.event d xi beta))

/-- The rewrite additionally needs full identity and both congruence contracts. -/
theorem event_negative_rewrite (laws : RunLaws M) (events : EventLaws M E coRef)
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    (xi : Input D) (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site))) (beta : Beta)
    (fullRoundTrip : JointIdentity M E coRef (H xi.site) (L xi.site))
    (negCongruence : ∀ c d, JointIdentity M E coRef c d → JointIdentity M E coRef (neg c) (neg d))
    (holdingCongruence : ∀ c d, JointIdentity M E coRef c d → ∀ input index,
      PartialEq coRef (E.holding c input index) (E.holding d input index)) :
    PartialEq coRef (E.event (L xi.site) xi beta)
      (E.holding (neg (L xi.site)) xi (negativeCoordinate M E xi beta)) := by
  have hn := events.negative (H xi.site) xi (negativeCoordinate M E xi beta)
  have hh := holdingCongruence _ _ (negCongruence _ _ fullRoundTrip) xi (negativeCoordinate M E xi beta)
  exact partial_trans coRef trans
    (partial_trans coRef trans (event_L_eq_N laws events trans xi admitted resolved beta) hn) hh

/-- Definedness transfers only from a supplied holding value through full congruence. -/
theorem supplied_rewrite_exists
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    (eventL holdingN holdingNegL : Option Event) (hN : Event)
    (constraint : PartialEq coRef eventL (some hN))
    (supplied : holdingN = some hN)
    (congruent : PartialEq coRef holdingN holdingNegL) :
    ∃ hNegL, holdingNegL = some hNegL ∧ PartialEq coRef eventL (some hNegL) := by
  rw [supplied] at congruent
  cases holdingNegL with
  | none => exact False.elim congruent
  | some h => exact ⟨h, rfl, partial_trans coRef trans constraint congruent⟩

theorem event_constraint_rewritten (laws : RunLaws M) (events : EventLaws M E coRef)
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    (xi : Input D) (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site))) (beta : Beta)
    (hN : Event)
    (supplied : E.holding (N xi.site) xi (negativeCoordinate M E xi beta) = some hN)
    (fullRoundTrip : JointIdentity M E coRef (H xi.site) (L xi.site))
    (negCongruence : ∀ c d, JointIdentity M E coRef c d → JointIdentity M E coRef (neg c) (neg d))
    (holdingCongruence : ∀ c d, JointIdentity M E coRef c d → ∀ input index,
      PartialEq coRef (E.holding c input index) (E.holding d input index)) :
    ∃ hNegL,
      E.holding (neg (L xi.site)) xi (negativeCoordinate M E xi beta) = some hNegL ∧
      PartialEq coRef (E.event (L xi.site) xi beta) (some hNegL) := by
  exact supplied_rewrite_exists trans _ _ _ hN
    (event_constraint laws events trans xi admitted resolved beta hN supplied) supplied
    (holdingCongruence _ _ (negCongruence _ _ fullRoundTrip) xi (negativeCoordinate M E xi beta))
end SmusniF03B
