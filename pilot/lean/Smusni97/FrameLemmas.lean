import Smusni97.Common

namespace Smusni97
open SmusniF02

/-- Frame deliberately omits obligations. This stronger derived invariant records
what the current reference grammar preserves, not what every future frame must. -/
structure RefFrame (entry reached : State) : Prop extends Frame entry reached where
  obligations : reached.obligations = entry.obligations

theorem RefFrame.refl (s : State) : RefFrame s s :=
  ⟨⟨fun _ _ h => h, ⟨[], by simp⟩, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem RefFrame.trans {s t u : State} (h : RefFrame s t) (k : RefFrame t u) : RefFrame s u where
  incoming n v old := k.incoming n v (h.incoming n v old)
  sidePrefix := by
    obtain ⟨a, ha⟩ := h.sidePrefix
    obtain ⟨b, hb⟩ := k.sidePrefix
    exact ⟨a ++ b, by simp [hb, ha, List.append_assoc]⟩
  hosts := k.hosts.trans h.hosts
  kappa := k.kappa.trans h.kappa
  chi := k.chi.trans h.chi
  frames := k.frames.trans h.frames
  obligations := k.obligations.trans h.obligations

theorem RefFrame.project {s t : State} (h : RefFrame s t) : RefFrame s (prune (support s) t) where
  incoming n v old := by simp [prune, support, old, h.incoming n v old]
  sidePrefix := h.sidePrefix
  hosts := h.hosts
  kappa := h.kappa
  chi := h.chi
  frames := h.frames
  obligations := h.obligations

def Preserves (m : Run A) : Prop := ∀ s z, z ∈ m s → RefFrame s z.state

theorem preserves_pure (a : A) : Preserves (SmusniF02.Run.pure a : Run A) := by
  intro s z hz
  have same : z = .live s a := hz
  subst z
  exact RefFrame.refl s

theorem preserves_test (test : RefTest) : Preserves (fun s => NEFin.singleton (test.observe s)) := by
  intro s z hz
  have same : z = test.observe s := hz
  subst z
  exact ⟨test_frame test s, (test_retains test s).2.1⟩

theorem preserves_emit (side : ClosedSide Nat) : Preserves (fun s =>
    NEFin.singleton (.live {s with sides := s.sides ++ [side]} ())) := by
  intro s z hz
  have same : z = .live {s with sides := s.sides ++ [side]} () := hz
  subst z
  exact ⟨⟨fun _ _ h => h, ⟨[side], rfl⟩, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem preserves_bind (m : Run A) (k : A → Run B) (hm : Preserves m)
    (hk : ∀ a, Preserves (k a)) : Preserves (SmusniF02.Run.bind m k) := by
  intro s z hz
  change ∃ x, x ∈ m s ∧ z ∈ SmusniF02.Run.extend k x at hz
  obtain ⟨x, hx, hz⟩ := hz
  have first := hm s x hx
  cases x with
  | live t a => exact first.trans (hk a t z hz)
  | dead t =>
    have same : z = .dead t := hz
    subst z; exact first
  | undef t =>
    have same : z = .undef t := hz
    subst z; exact first

theorem preserves_project (m : Run A) (f : State → Out A → Out A)
    (law : LocalLaw f) (hm : Preserves m) : Preserves (fun s => mapResults (f s) (m s)) := by
  intro s z hz
  change ∃ x, x ∈ m s ∧ z = f s x at hz
  obtain ⟨x, hx, same⟩ := hz
  rw [same, law s x, state_map]
  exact (hm s x hx).project

theorem negate_state (s : State) (z : Out Unit) : (negate s z).state = s := by cases z <;> rfl

theorem preserves_negative (test : RefTest) : Preserves (fun s => NEFin.singleton
    (negate (prune (support s) (test.observe s).state) (test.observe s))) := by
  intro s z hz
  have same : z = negate (prune (support s) (test.observe s).state) (test.observe s) := hz
  rw [same, negate_state]
  exact (RefFrame.project ⟨test_frame test s, (test_retains test s).2.1⟩)

theorem record_kappa_false (s : State) (h : Nat) (tau sigma : Truth) (hk : s.kappa = .f) :
    (record h tau sigma s).kappa = .f := by change s.kappa.and tau = .f; rw [hk]; rfl
theorem record_chi_false (s : State) (h : Nat) (tau sigma : Truth) (hc : s.chi = .f) :
    (record h tau sigma s).chi = .f := by change s.chi.and sigma = .f; rw [hc]; rfl
end Smusni97
