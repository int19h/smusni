import SmusniF03B.Syntax
import SmusniF03B.Outcomes

/-! Candidate interpretation contracts, not a constructed interpretation.
All external coordinates are explicit. Event indices are deliberately absent. -/
namespace SmusniF03B
open SmusniF02 SmusniPilot SmusniPilot.M2

structure Domains where
  Profile : Type
  Source : Type
  Context : Type
  World : Type
  State : Type
  Key : Type
  Dependencies : Type
  Segment : Type

structure Input (D : Domains) where
  profile : D.Profile
  source : D.Source
  context : D.Context
  world : D.World
  caller : D.State
  site : SiteId
  key : D.Key
  dependencies : D.Dependencies
  segment : D.Segment

def Input.atState (xi : Input D) (s : D.State) : Input D := { xi with caller := s }
@[simp] theorem Input.atState_self (xi : Input D) : xi.atState xi.caller = xi := by cases xi; rfl

/-- Each replay coordinate, including the caller state and formation site, is fixed. -/
structure ReplayAt (after before : Input D) : Prop where
  profile : after.profile = before.profile
  source : after.source = before.source
  context : after.context = before.context
  world : after.world = before.world
  caller : after.caller = before.caller
  site : after.site = before.site
  key : after.key = before.key
  dependencies : after.dependencies = before.dependencies
  segment : after.segment = before.segment

theorem ReplayAt.eq (h : ReplayAt after before) : after = before := by
  cases after; cases before; cases h
  congr

structure Observations (D : Domains) (P : Type) where
  run : Term 0 → Input D → Terminal D.State Unit
  valueRun : Term 0 → Input D → Terminal D.State P
  bodyRun : Term 1 → P → Input D → Terminal D.State Unit
  reifyValue : Term 0 → P
  resolve : Input D → Option P
  admits : D.Context → Prop
  replay : Term 0 → Input D → Input D
  noIntroductions : Term 0 → Input D → Prop
  noEmissions : Term 0 → Input D → Prop
  unchangedInput : Term 0 → Input D → Prop
  valueNoEmissions : Term 0 → Input D → Prop

/-- Supplied semantic conditions for this use, never inferred from static effects. -/
def ReadOnlyUse (M : Observations D P) (c : Term 0) (xi : Input D) : Prop :=
  M.noIntroductions c xi ∧ M.noEmissions c xi ∧ M.unchangedInput c xi

structure ContextSuccess (M : Observations D P) (xi : Input D) (p : P) : Prop where
  exactRun : M.valueRun (source xi.site) xi = NEFin.singleton (.live xi.caller p)
  noEmission : M.valueNoEmissions (source xi.site) xi

/-- Generic clauses supplied by a candidate interpretation. These are not axioms. -/
structure RunLaws (M : Observations D P) : Prop where
  contextSuccess : ∀ xi p, M.admits xi.context → M.resolve xi = some p → ContextSuccess M xi p
  strictBind : ∀ c b xi,
    M.run (.bind Ty.proposition c b) xi =
      Run.bind (fun s => M.valueRun c (xi.atState s))
        (fun p s => M.bodyRun b p (xi.atState s)) xi.caller
  substitution : ∀ b q xi,
    M.bodyRun b (M.reifyValue q) xi = M.run (instantiate b (reify q)) xi
  roundTrip : ∀ q xi, M.run (holds (reify q)) xi = M.run q (M.replay q xi)

variable {M : Observations D P}

theorem run_L_eq_N (laws : RunLaws M) (xi : Input D)
    (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site))) :
    M.run (L xi.site) xi = M.run (N xi.site) xi := by
  have success := laws.contextSuccess xi _ admitted resolved
  rw [L, laws.strictBind]
  simp only [Run.bind, Input.atState_self, success.exactRun, NEFin.singleton_unionMap, Run.extend]
  rw [laws.substitution]
  exact congrArg (fun c => M.run c xi) (body_instantiation xi.site)

theorem run_H_eq_L (laws : RunLaws M) (xi : Input D)
    (replay : ReplayAt (M.replay (L xi.site) xi) xi) :
    M.run (H xi.site) xi = M.run (L xi.site) xi := by
  change M.run (holds (reify (L xi.site))) xi = _
  rw [laws.roundTrip, replay.eq]

/-- The scalar SK contract is weaker than pointwise flipping complete outcomes. -/
def ScalarNegation (M : Observations D P) : Prop :=
  ∀ c xi status, ReadOnlyUse M c xi → Scalar (M.run c xi) status →
    Scalar (M.run (neg c) xi) (negSK status)

theorem conditional_scalar (laws : RunLaws M) (xi : Input D)
    (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site)))
    (replay : ReplayAt (M.replay (L xi.site) xi) xi)
    (readOnly : ReadOnlyUse M (H xi.site) xi)
    (sk : ScalarNegation M) (status : Truth)
    (scalar : Scalar (M.run (L xi.site) xi) status) : status = .u := by
  have hscalar : Scalar (M.run (H xi.site) xi) status := by
    rw [run_H_eq_L laws xi replay]; exact scalar
  have nscalar := sk (H xi.site) xi status readOnly hscalar
  change Scalar (M.run (N xi.site) xi) (negSK status) at nscalar
  rw [← run_L_eq_N laws xi admitted resolved] at nscalar
  exact (negSK_fixed status).mp (scalar_unique _ _ _ scalar nscalar)

theorem singleton_scalar (z : Outcome S Unit) : Scalar (NEFin.singleton z) z.truth := by
  intro y hy
  have : y = z := hy
  cases this; rfl

theorem conditional_singleton (laws : RunLaws M) (xi : Input D)
    (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site)))
    (replay : ReplayAt (M.replay (L xi.site) xi) xi)
    (readOnly : ReadOnlyUse M (H xi.site) xi) (sk : ScalarNegation M)
    (z : Outcome D.State Unit) (single : M.run (L xi.site) xi = NEFin.singleton z) :
    z.truth = .u := by
  apply conditional_scalar laws xi admitted resolved replay readOnly sk z.truth
  rw [single]; exact singleton_scalar z

/-- An additional outcome-level hypothesis, not a consequence of ScalarNegation. -/
def SetNeg (M : Observations D P) (xi : Input D) : Prop :=
  M.run (N xi.site) xi = image flipOut (M.run (H xi.site) xi)

theorem conditional_set_fixed (laws : RunLaws M) (xi : Input D)
    (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site)))
    (replay : ReplayAt (M.replay (L xi.site) xi) xi) (setNeg : SetNeg M xi) :
    M.run (L xi.site) xi = image flipOut (M.run (L xi.site) xi) := by
  calc
    M.run (L xi.site) xi = M.run (N xi.site) xi := run_L_eq_N laws xi admitted resolved
    _ = image flipOut (M.run (H xi.site) xi) := setNeg
    _ = image flipOut (M.run (L xi.site) xi) := congrArg _ (run_H_eq_L laws xi replay)
end SmusniF03B
