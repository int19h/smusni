import Smusni97.Opaque
import Smusni97.Explicit

/-! Equal tasks for independent implementations. Parity is a proved observation
equation, not an alias in either implementation. The F02 run lemmas are shared
evidence, not an exclusive advantage of the explicit defining language. -/
namespace Smusni97.Comparison
open SmusniF02

theorem local_parity (entry : State) (z : Out A) :
    Explicit.localOut entry z = Opaque.localOut entry z := by cases z <;> rfl
theorem host_parity (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit) :
    Explicit.hostOut entry eligible h z = Opaque.hostOut entry eligible h z := by cases z <;> rfl
theorem neg_parity (entry : State) (z : Out Unit) :
    Explicit.negOut entry z = Opaque.negOut entry z := by cases z <;> rfl

/-- Field-level laws cover every terminal, not only a successful fixture. -/
theorem local_matrix (entry : State) (z : Out A) :
    value (Explicit.localOut entry z) = value z ∧
    value (Opaque.localOut entry z) = value z ∧
    (Explicit.localOut entry z).state.sides = z.state.sides ∧
    (Opaque.localOut entry z).state.sides = z.state.sides ∧
    (Explicit.localOut entry z).state.obligations = z.state.obligations ∧
    (Opaque.localOut entry z).state.obligations = z.state.obligations :=
  ⟨Explicit.local_value _ _, Opaque.local_value _ _, Explicit.local_sides _ _,
    Opaque.local_sides _ _, Explicit.local_obligations _ _, Opaque.local_obligations _ _⟩

theorem incoming_matrix (entry : State) (z : Out A) (frame : Frame entry z.state)
    (n v : Nat) (old : entry.slots n = some v) :
    (Explicit.localOut entry z).state.slots n = some v ∧
    (Opaque.localOut entry z).state.slots n = some v :=
  ⟨Explicit.local_incoming _ _ _ _ old (frame.incoming n v old),
    Opaque.local_incoming _ _ _ _ old (frame.incoming n v old)⟩

theorem host_obligations (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit) :
    (Explicit.hostOut entry eligible h z).state.obligations = z.state.obligations ∧
    (Opaque.hostOut entry eligible h z).state.obligations = z.state.obligations := by
  rw [host_parity]; exact ⟨rfl, rfl⟩

theorem host_incoming (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit)
    (frame : Frame entry z.state) (n v : Nat) (old : entry.slots n = some v) :
    (Explicit.hostOut entry eligible h z).state.slots n = some v ∧
    (Opaque.hostOut entry eligible h z).state.slots n = some v := by
  have kept : support entry n = true ∨ eligible n = true := Or.inl (by simp [support, old])
  rw [Explicit.host_prefix _ _ _ _ _ kept, Opaque.host_prefix _ _ _ _ _ kept]
  exact ⟨frame.incoming n v old, frame.incoming n v old⟩

theorem host_local_drop (entry : State) (eligible : Mask) (h n : Nat) (z : Out Unit)
    (old : entry.slots n = none) (localOnly : eligible n = false) :
    (Explicit.hostOut entry eligible h z).state.slots n = none ∧
    (Opaque.hostOut entry eligible h z).state.slots n = none := by
  rw [host_parity]
  simp [Opaque.hostOut, Outcome.state, record, prune, unionMask, support, old, localOnly]

theorem host_fresh_record (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit)
    (fresh : FreshHost h z.state) :
    (Explicit.hostOut entry eligible h z).state.hosts =
      z.state.hosts ++ [⟨h, z.truth, suffixStatus entry z.state⟩] ∧
    (∀ r ∈ z.state.hosts, r.handle ≠ h) := ⟨Explicit.host_record _ _ _ _, fresh⟩

theorem host_cumulative (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit)
    (hk : z.state.kappa = .f) (hc : z.state.chi = .f) :
    (Explicit.hostOut entry eligible h z).state.kappa = .f ∧
    (Explicit.hostOut entry eligible h z).state.chi = .f := by
  rw [host_parity]; exact Opaque.host_prior_false _ _ _ _ hk hc

theorem bind_routes (k : A → Run B) (s : State) (a : A) :
    Explicit.route k (.live s a) = k a s ∧
    Explicit.route k (.dead s) = NEFin.singleton (.dead s) ∧
    Explicit.route k (.undef s) = NEFin.singleton (.undef s) ∧
    SmusniF02.Run.extend k (.live s a) = k a s ∧
    SmusniF02.Run.extend k (.dead s) = NEFin.singleton (.dead s) ∧
    SmusniF02.Run.extend k (.undef s) = NEFin.singleton (.undef s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem guarded_negative_preserves (test : RefTest) (entry : State) :
    (Explicit.negOut entry (test.observe entry)).state.sides = entry.sides ∧
    (Explicit.negOut entry (test.observe entry)).state.obligations = entry.obligations ∧
    (Opaque.negOut entry (test.observe entry)).state.sides = entry.sides ∧
    (Opaque.negOut entry (test.observe entry)).state.obligations = entry.obligations := by
  rw [neg_parity]
  have same := test_retains test entry
  have hs : (Opaque.negOut entry (test.observe entry)).state =
      prune (support entry) (test.observe entry).state := by
    cases test.observe entry <;> rfl
  rw [hs]
  exact ⟨same.1, same.2.1, same.1, same.2.1⟩

theorem negative_status (entry reached : State) :
    Explicit.negOut entry (.live reached ()) = .dead (prune (support entry) reached) ∧
    Explicit.negOut entry (.dead reached) = .live (prune (support entry) reached) () ∧
    Explicit.negOut entry (.undef reached) = .undef (prune (support entry) reached) ∧
    Opaque.negOut entry (.live reached ()) = .dead (prune (support entry) reached) ∧
    Opaque.negOut entry (.dead reached) = .live (prune (support entry) reached) () ∧
    Opaque.negOut entry (.undef reached) = .undef (prune (support entry) reached) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No state/value function is used as a syntax injection by this translation. -/
def cat : Opaque.Cat → Explicit.Cat | .ref => .ref | .perf => .perf
def translate : Opaque.Term c A → Explicit.Term (cat c) A
  | .pure a => .pure a
  | .test t => .test t
  | .emit s => .emit s
  | .bind m k => .bind (translate m) (fun a => translate (k a))
  | .local m => .local (translate m)
  | .body m => .body (translate m)
  | .negative t => .negative t
  | .host m e h => .host (translate m) e h
  | .lift m => .lift (translate m)
  | .project _ m => .local (translate m)

theorem term_parity (m : Opaque.Term c A) : Explicit.observe (translate m) = Opaque.observe m := by
  induction m with
  | pure a => rfl
  | test t => rfl
  | emit s => rfl
  | bind m k ihm ihk =>
    simp only [translate, Explicit.observe, Opaque.observe, Explicit.sequence_equation, ihm]
    congr 1
    funext a
    exact ihk a
  | «local» m ih =>
    change (fun s => mapResults (Explicit.localOut s) (Explicit.observe (translate m) s)) =
      (fun s => mapResults (Opaque.localOut s) (Opaque.observe m s))
    rw [ih]
    funext s
    exact congrArg (fun f => mapResults f (Opaque.observe m s)) (funext (local_parity s))
  | body m ih =>
    change (fun s => mapResults (Explicit.localOut s) (Explicit.observe (translate m) s)) =
      (fun s => mapResults (Opaque.localOut s) (Opaque.observe m s))
    rw [ih]
    funext s
    exact congrArg (fun f => mapResults f (Opaque.observe m s)) (funext (local_parity s))
  | negative t => funext s; rw [show Explicit.observe (translate (.negative t)) s =
      NEFin.singleton (Explicit.negOut s (t.observe s)) from rfl, neg_parity]; rfl
  | host m e h ih =>
    change (fun s => mapResults (Explicit.hostOut s e h) (Explicit.observe (translate m) s)) =
      (fun s => mapResults (Opaque.hostOut s e h) (Opaque.observe m s))
    rw [ih]
    funext s
    exact congrArg (fun f => mapResults f (Opaque.observe m s)) (funext (host_parity s e h))
  | lift m ih => exact ih
  | project exported m ih =>
    change (fun s => mapResults (Explicit.localOut s) (Explicit.observe (translate m) s)) =
      (fun s => mapResults (exported.operation s) (Opaque.observe m s))
    rw [ih]
    funext s
    apply congrArg (fun f => mapResults f (Opaque.observe m s))
    funext z
    rw [exported.correct s z]
    exact local_parity s z
end Smusni97.Comparison
