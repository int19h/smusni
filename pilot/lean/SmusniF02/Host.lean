import SmusniF02.Content

/-! F02-v2 §5: bounded assertion finalization. Scope eligibility, ground values
and already closed, total sides are supplied; no accommodation or guard policy
is computed here. The payload observation and successful performance return
are deliberately different operations. -/
namespace SmusniF02

inductive Truth where | f | u | t deriving DecidableEq, Repr

def Truth.and : Truth → Truth → Truth
  | .f, _ | _, .f => .f
  | .t, q => q
  | .u, .t | .u, .u => .u

def Outcome.truth : Outcome S A → Truth
  | .live _ _ => .t
  | .dead _ => .f
  | .undef _ => .u

/-- Anchor is supplied ground closure data, not a dangling discourse slot. -/
structure ClosedSide (Anchor : Type u) where
  anchor : Anchor
  holds : Bool
  deriving DecidableEq

structure HostRecord (Handle : Type u) where
  handle : Handle
  payload : Truth
  side : Truth
  deriving DecidableEq

/-- A separate, relative ground state; no Content, read closure or Act is stored. -/
structure HostState (Name : Type u) (Value : Type v) (Anchor : Type w) (Handle : Type x) where
  assignment : Name → Option Value
  sides : List (ClosedSide Anchor)
  history : List (HostRecord Handle)
  kappa : Truth
  chi : Truth

namespace Host
variable {N : Type u} {V : Type v} {A : Type w} {H : Type x}
abbrev State := HostState N V A H

def sideTruth (sides : List (ClosedSide A)) : Truth :=
  if sides.all (·.holds) then .t else .f

/-- A premise about the *input* payload frame, not a desired finalizer law.
It expresses only unchanged old bindings, prefix extension, and no nested Host. -/
structure LegalFrame (entry terminal : State (N := N) (V := V) (A := A) (H := H)) : Prop where
  incoming : ∀ n v, entry.assignment n = some v → terminal.assignment n = some v
  sidePrefix : ∃ suffix, terminal.sides = entry.sides ++ suffix
  history : terminal.history = entry.history
  kappa : terminal.kappa = entry.kappa
  chi : terminal.chi = entry.chi

def keep (entry terminal : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) : State (N := N) (V := V) (A := A) (H := H) :=
  { terminal with assignment := fun n =>
      if (entry.assignment n).isSome || eligible n then terminal.assignment n else none }

def currentSideTruth (entry terminal : State (N := N) (V := V) (A := A) (H := H)) : Truth :=
  sideTruth (terminal.sides.drop entry.sides.length)

def finalizeState (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome (State (N := N) (V := V) (A := A) (H := H)) B) :
    State (N := N) (V := V) (A := A) (H := H) :=
  let side := currentSideTruth entry z.state
  { keep entry z.state eligible with
    history := entry.history ++ [⟨h, z.truth, side⟩]
    kappa := entry.kappa.and z.truth
    chi := entry.chi.and side }

def finalize (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome (State (N := N) (V := V) (A := A) (H := H)) B) :
    Outcome (State (N := N) (V := V) (A := A) (H := H)) H :=
  .live (finalizeState entry eligible h z) h

theorem returns_live (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) :
    finalize entry eligible h z = .live (finalizeState entry eligible h z) h := rfl

theorem retain_incoming (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) (legal : LegalFrame entry z.state)
    (n : N) (v : V) (old : entry.assignment n = some v) :
    (finalizeState entry eligible h z).assignment n = some v := by
  simp [finalizeState, keep, old, legal.incoming n v old]

theorem retain_eligible (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) (n : N) (hn : eligible n = true) :
    (finalizeState entry eligible h z).assignment n = z.state.assignment n := by
  simp [finalizeState, keep, hn]

theorem drop_local (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) (n : N)
    (old : entry.assignment n = none) (hn : eligible n = false) :
    (finalizeState entry eligible h z).assignment n = none := by
  simp [finalizeState, keep, old, hn]

theorem sides_once (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) :
    (finalizeState entry eligible h z).sides = z.state.sides := rfl

theorem side_status_is_suffix (entry terminal : State (N := N) (V := V) (A := A) (H := H))
    (suffix : List (ClosedSide A)) (hs : terminal.sides = entry.sides ++ suffix) :
    currentSideTruth entry terminal = sideTruth suffix := by
  simp [currentSideTruth, hs]

theorem history_append (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) :
    (finalizeState entry eligible h z).history =
      entry.history ++ [⟨h, z.truth, currentSideTruth entry z.state⟩] := rfl

theorem cumulative_payload (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) :
    (finalizeState entry eligible h z).kappa = entry.kappa.and z.truth := rfl
theorem cumulative_sides (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B) :
    (finalizeState entry eligible h z).chi = entry.chi.and (currentSideTruth entry z.state) := rfl

theorem prior_failure_stays (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z : Outcome _ B)
    (hk : entry.kappa = .f) (hc : entry.chi = .f) :
    (finalizeState entry eligible h z).kappa = .f ∧
      (finalizeState entry eligible h z).chi = .f := by
  simp [finalizeState, hk, hc, Truth.and]

theorem finalize_congr (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (z z' : Outcome _ B)
    (he : z = z') : finalize entry eligible h z = finalize entry eligible h z' := by rw [he]

/-- The finalizer can process every terminal alternative without losing nonemptiness. -/
noncomputable def finalizeAll (entry : State (N := N) (V := V) (A := A) (H := H))
    (eligible : N → Bool) (h : H) (zs : Terminal (State (N := N) (V := V) (A := A) (H := H)) B) :
    Terminal (State (N := N) (V := V) (A := A) (H := H)) H :=
  zs.unionMap (fun z => NEFin.singleton (finalize entry eligible h z))
end Host
end SmusniF02
