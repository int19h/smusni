import Smusni97.Common

/-! Named operations with concrete model equations. No explicit-language import.
The ordinary term datatype provides no arbitrary state observer or injection. -/
namespace Smusni97.Opaque
open SmusniF02

def localOut (entry : State) (z : Out A) : Out A :=
  mapState (prune (support entry)) z

def hostOut (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit) : Out Nat :=
  .live (record h z.truth (suffixStatus entry z.state)
    (prune (unionMask (support entry) eligible) z.state)) h

def negOut (entry : State) (z : Out Unit) : Out Unit :=
  negate (prune (support entry) z.state) z

def finish (entry : State) (eligible : Mask) (h : Nat) (use : HostUse entry h) : Out Nat :=
  hostOut entry eligible h use.terminal

noncomputable def localRun (m : Run A) : Run A := fun entry => mapResults (localOut entry) (m entry)
noncomputable def hostRun (m : Run Unit) (eligible : Mask) (h : Nat) : Run Nat :=
  fun entry => mapResults (hostOut entry eligible h) (m entry)
def negRun (test : RefTest) : Run Unit :=
  fun entry => NEFin.singleton (negOut entry (test.observe entry))
def negative (entry : State) (use : NegativeUse entry) : Out Unit :=
  negOut entry (use.test.observe entry)

/-- One quantifier-body projection leg, not quantifier aggregation. -/
noncomputable def bodyLeg (m : Run A) : Run A := localRun m

/-- Strong opaque control: reviewed model definitions can also grow by name.
The implementation is a model function with a proved contract, not RunDef syntax. -/
structure NamedProjection (A : Type) where
  name : String
  operation : State → Out A → Out A
  correct : LocalLaw operation

def bodyExport : NamedProjection A := ⟨"quantifier-body", localOut, fun _ _ => rfl⟩
noncomputable def useProjection (exported : NamedProjection A) (m : Run A) : Run A :=
  fun entry => mapResults (exported.operation entry) (m entry)

inductive Cat where | ref | perf
inductive Term : Cat → Type → Type 1 where
  | pure (a : A) : Term c A
  | test (t : RefTest) : Term .ref Unit
  | emit (side : ClosedSide Nat) : Term .ref Unit
  | bind : Term c A → (A → Term c B) → Term c B
  | local : Term .ref A → Term .ref A
  | body : Term .ref A → Term .ref A
  | negative : RefTest → Term .ref Unit
  | host : Term .ref Unit → Mask → Nat → Term .perf Nat
  | lift : Term .ref A → Term .perf A
  | project : NamedProjection A → Term .ref A → Term .ref A

noncomputable def observe : Term c A → Run A
  | .pure a => SmusniF02.Run.pure a
  | .test t => fun s => NEFin.singleton (t.observe s)
  | .emit side => fun s => NEFin.singleton (.live {s with sides := s.sides ++ [side]} ())
  | .bind m k => SmusniF02.Run.bind (observe m) (fun a => observe (k a))
  | .local m => localRun (observe m)
  | .body m => bodyLeg (observe m)
  | .negative t => negRun t
  | .host m eligible h => hostRun (observe m) eligible h
  | .lift m => observe m
  | .project exported m => useProjection exported (observe m)

theorem local_value (entry : State) (z : Out A) : value (localOut entry z) = value z := value_map _ _
theorem local_truth (entry : State) (z : Out A) : (localOut entry z).truth = z.truth := truth_map _ _
theorem local_sides (entry : State) (z : Out A) : (localOut entry z).state.sides = z.state.sides := by
  simp [localOut, prune]
theorem local_obligations (entry : State) (z : Out A) :
    (localOut entry z).state.obligations = z.state.obligations := by simp [localOut, prune]
theorem local_incoming (entry : State) (z : Out A) (n v : Nat)
    (old : entry.slots n = some v) (retained : z.state.slots n = some v) :
    (localOut entry z).state.slots n = some v := by
  simp [localOut, prune, support, old, retained]
theorem local_fresh (entry : State) (z : Out A) (n : Nat) (fresh : entry.slots n = none) :
    (localOut entry z).state.slots n = none := by simp [localOut, prune, support, fresh]

theorem host_prefix (entry : State) (z : Out Unit) (eligible : Mask) (h n : Nat)
    (kept : support entry n = true ∨ eligible n = true) :
    (hostOut entry eligible h z).state.slots n = z.state.slots n := by
  rcases kept with kept | kept <;>
    simp [hostOut, Outcome.state, record, prune, unionMask, kept]
theorem host_returns_dead (entry s : State) (eligible : Mask) (h : Nat) :
    value (hostOut entry eligible h (.dead s)) = some h := rfl
theorem host_returns_undef (entry s : State) (eligible : Mask) (h : Nat) :
    value (hostOut entry eligible h (.undef s)) = some h := rfl
theorem host_sides_once (entry : State) (z : Out Unit) (eligible : Mask) (h : Nat) :
    (hostOut entry eligible h z).state.sides = z.state.sides := rfl
theorem host_suffix (entry s : State) (suffix : List (ClosedSide Nat))
    (hp : s.sides = entry.sides ++ suffix) : suffixStatus entry s = sideStatus suffix := by
  simp [suffixStatus, hp]
theorem host_record (entry : State) (z : Out Unit) (eligible : Mask) (h : Nat) :
    (hostOut entry eligible h z).state.hosts =
      z.state.hosts ++ [⟨h, z.truth, suffixStatus entry z.state⟩] := rfl
theorem host_prior_false (entry : State) (z : Out Unit) (eligible : Mask) (h : Nat)
    (hk : z.state.kappa = .f) (hc : z.state.chi = .f) :
    (hostOut entry eligible h z).state.kappa = .f ∧ (hostOut entry eligible h z).state.chi = .f := by
  change z.state.kappa.and z.truth = .f ∧ z.state.chi.and (suffixStatus entry z.state) = .f
  rw [hk, hc]
  exact ⟨rfl, rfl⟩

theorem bind_unit_left (a : A) (k : A → Term c B) :
    observe (.bind (.pure a) k) = observe (k a) := SmusniF02.Run.pure_bind _ _
theorem bind_unit_right (m : Term c A) : observe (.bind m Term.pure) = observe m :=
  SmusniF02.Run.bind_pure _
theorem bind_assoc (m : Term c A) (k : A → Term c B) (l : B → Term c C) :
    observe (.bind (.bind m k) l) = observe (.bind m (fun a => .bind (k a) l)) :=
  SmusniF02.Run.bind_assoc _ _ _

theorem neg_sides (entry : State) (z : Out Unit) :
    (negOut entry z).state.sides = z.state.sides := by cases z <;> rfl
theorem neg_fresh (entry : State) (z : Out Unit) (n : Nat) (fresh : entry.slots n = none) :
    (negOut entry z).state.slots n = none := by cases z <;> simp [negOut, negate, prune, support, fresh, Outcome.state]
theorem body_leg_same (m : Run A) : bodyLeg m = localRun m := rfl
end Smusni97.Opaque
