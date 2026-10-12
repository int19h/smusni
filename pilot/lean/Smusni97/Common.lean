import SmusniF02.Carrier
import SmusniF02.Host

/-! Shared data and state operations for issue 97. This is one supplied ground
sort with Nat-valued slots, not the full sorted information-state model.
Result types remain arbitrary. Closed records store values, not slot readers. -/
namespace Smusni97
open SmusniF02

structure Obligation where
  captured : Nat
  condition : Nat
  deriving DecidableEq

structure State where
  slots : Nat → Option Nat
  sides : List (ClosedSide Nat)
  obligations : List Obligation
  frames : List Nat
  hosts : List (HostRecord Nat)
  kappa : Truth
  chi : Truth

abbrev Out (A : Type u) := Outcome State A
abbrev Results (A : Type u) := NEFin (Out A)
abbrev Run (A : Type u) := State → Results A
abbrev Mask := Nat → Bool

def support (s : State) : Mask := fun n => (s.slots n).isSome
def prune (mask : Mask) (s : State) : State :=
  { s with slots := fun n => if mask n then s.slots n else none }
def unionMask (a b : Mask) : Mask := fun n => a n || b n
def sideStatus (xs : List (ClosedSide Nat)) : Truth := if xs.all (·.holds) then .t else .f
def suffixStatus (entry reached : State) : Truth := sideStatus (reached.sides.drop entry.sides.length)
def record (h : Nat) (payload side : Truth) (s : State) : State :=
  { s with hosts := s.hosts ++ [⟨h, payload, side⟩]
           kappa := s.kappa.and payload
           chi := s.chi.and side }

def mapState (f : State → State) : Out A → Out A
  | .live s a => .live (f s) a
  | .dead s => .dead (f s)
  | .undef s => .undef (f s)

def negate (s : State) : Out Unit → Out Unit
  | .live _ _ => .dead s
  | .dead _ => .live s ()
  | .undef _ => .undef s

def value : Out A → Option A
  | .live _ a => some a
  | .dead _ | .undef _ => none

noncomputable def mapResults (f : Out A → Out B) (zs : Results A) : Results B :=
  zs.unionMap (fun z => NEFin.singleton (f z))

@[simp] theorem map_singleton (f : Out A → Out B) (z : Out A) :
    mapResults f (NEFin.singleton z) = NEFin.singleton (f z) := by
  exact NEFin.singleton_unionMap _ _

@[simp] theorem state_map (f : State → State) (z : Out A) : (mapState f z).state = f z.state := by
  cases z <;> rfl
@[simp] theorem value_map (f : State → State) (z : Out A) : value (mapState f z) = value z := by
  cases z <;> rfl
@[simp] theorem truth_map (f : State → State) (z : Out A) : (mapState f z).truth = z.truth := by
  cases z <;> rfl

theorem prune_preserves (mask : Mask) (s : State) :
    (prune mask s).sides = s.sides ∧ (prune mask s).obligations = s.obligations ∧
    (prune mask s).frames = s.frames ∧ (prune mask s).hosts = s.hosts ∧
    (prune mask s).kappa = s.kappa ∧ (prune mask s).chi = s.chi := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem prune_keep (mask : Mask) (s : State) (n : Nat) (h : mask n = true) :
    (prune mask s).slots n = s.slots n := by simp [prune, h]
theorem prune_drop (mask : Mask) (s : State) (n : Nat) (h : mask n = false) :
    (prune mask s).slots n = none := by simp [prune, h]
theorem prune_inter (a b : Mask) (s : State) :
    prune a (prune b s) = prune (fun n => a n && b n) s := by
  unfold prune
  congr 1
  funext n
  cases ha : a n <;> cases hb : b n <;> simp [ha, hb]

/-- This input contract does not assume a finalizer result. It also excludes
nested Host recording in the bounded payload. Fresh occurrence is separate. -/
structure Frame (entry reached : State) : Prop where
  incoming : ∀ n v, entry.slots n = some v → reached.slots n = some v
  sidePrefix : ∃ suffix, reached.sides = entry.sides ++ suffix
  hosts : reached.hosts = entry.hosts
  kappa : reached.kappa = entry.kappa
  chi : reached.chi = entry.chi
  frames : reached.frames = entry.frames

def FreshHost (h : Nat) (s : State) : Prop := ∀ r ∈ s.hosts, r.handle ≠ h

/-- Both candidates use this same domain. The raw equations outside this domain
are total Lean functions, not an admission of invalid Host performances. -/
structure HostUse (entry : State) (h : Nat) where
  terminal : Out Unit
  frame : Frame entry terminal.state
  fresh : FreshHost h terminal.state

/-- Shared semantic proof obligations for reviewed exports. These are predicates,
not axioms: each delivered export supplies a kernel proof about its own body. -/
def LocalLaw (f : State → Out A → Out A) : Prop :=
  ∀ entry z, f entry z = mapState (prune (support entry)) z
def HostLaw (f : State → Mask → Nat → Out Unit → Out Nat) : Prop :=
  ∀ entry eligible h (use : HostUse entry h), f entry eligible h use.terminal =
    .live (record h use.terminal.truth (suffixStatus entry use.terminal.state)
      (prune (unionMask (support entry) eligible) use.terminal.state)) h

/-- The negative test grammar permits only fresh introduction and a terminal
truth observation. No side emission, erasure, Host, or imported state function. -/
inductive RefTest where
  | result : Truth → RefTest
  | introduce : Nat → Nat → RefTest → RefTest

def testOutcome (status : Truth) (s : State) : Out Unit :=
  match status with | .t => .live s () | .f => .dead s | .u => .undef s
def introduce (n v : Nat) (s : State) : State :=
  { s with slots := fun k => if k = n then some v else s.slots k }
def RefTest.observe : RefTest → State → Out Unit
  | .result status, s => testOutcome status s
  | .introduce n v next, s =>
      if (s.slots n).isNone then next.observe (Smusni97.introduce n v s) else .undef s

/-- Per-use admission excludes the collision branch of the total observer.
That branch is not a proposed core failure policy. -/
def RefTest.Admitted : RefTest → State → Prop
  | .result _, _ => True
  | .introduce n v next, s => s.slots n = none ∧ next.Admitted (Smusni97.introduce n v s)

structure NegativeUse (entry : State) where
  test : RefTest
  admitted : test.Admitted entry

theorem test_retains (test : RefTest) (s : State) :
    (test.observe s).state.sides = s.sides ∧
    (test.observe s).state.obligations = s.obligations ∧
    (test.observe s).state.frames = s.frames ∧
    (test.observe s).state.hosts = s.hosts ∧
    (test.observe s).state.kappa = s.kappa ∧ (test.observe s).state.chi = s.chi := by
  induction test generalizing s with
  | result status => cases status <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | introduce n v next ih =>
    simp only [RefTest.observe]
    split
    · exact ih (introduce n v s)
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem test_incoming (test : RefTest) (s : State) (n v : Nat) (old : s.slots n = some v) :
    (test.observe s).state.slots n = some v := by
  induction test generalizing s with
  | result status => cases status <;> exact old
  | introduce k x next ih =>
    simp only [RefTest.observe]
    split
    · rename_i fresh
      apply ih
      have hn : n ≠ k := by
        intro h; subst k; simp [old] at fresh
      simp [introduce, hn, old]
    · exact old

theorem test_frame (test : RefTest) (s : State) : Frame s (test.observe s).state where
  incoming := test_incoming test s
  sidePrefix := ⟨[], by simpa using (test_retains test s).1⟩
  hosts := (test_retains test s).2.2.2.1
  kappa := (test_retains test s).2.2.2.2.1
  chi := (test_retains test s).2.2.2.2.2
  frames := (test_retains test s).2.2.1
end Smusni97
