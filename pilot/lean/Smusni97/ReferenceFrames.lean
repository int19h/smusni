import Smusni97.Admission
import Smusni97.Comparison
import Smusni97.FrameLemmas

namespace Smusni97
open SmusniF02

theorem Opaque.preserves_of_ref (m : Opaque.Term c A) : c = .ref → Preserves (Opaque.observe m) := by
  induction m with
  | pure a => intro _; exact preserves_pure a
  | test t => intro _; exact preserves_test t
  | emit side => intro _; exact preserves_emit side
  | bind m k ihm ihk => intro hc; exact preserves_bind _ _ (ihm hc) (fun a => ihk a hc)
  | «local» m ih => intro _; exact preserves_project _ _ (fun _ _ => rfl) (ih rfl)
  | body m ih => intro _; exact preserves_project _ _ (fun _ _ => rfl) (ih rfl)
  | negative t => intro _; exact preserves_negative t
  | host m e h ih => intro hc; cases hc
  | lift m ih => intro hc; cases hc
  | project e m ih => intro _; exact preserves_project _ _ e.correct (ih rfl)

theorem Explicit.preserves_of_ref (m : Explicit.Term c A) : c = .ref → Preserves (Explicit.observe m) := by
  induction m with
  | pure a => intro _; exact preserves_pure a
  | test t => intro _; exact preserves_test t
  | emit side => intro _; exact preserves_emit side
  | bind m k ihm ihk =>
    intro hc
    change Preserves (Explicit.sequence _ _)
    rw [Explicit.sequence_equation]
    exact preserves_bind _ _ (ihm hc) (fun a => ihk a hc)
  | «local» m ih =>
    intro _
    exact preserves_project _ _ (fun s z => Comparison.local_parity s z) (ih rfl)
  | body m ih =>
    intro _
    exact preserves_project _ _ (fun s z => Comparison.local_parity s z) (ih rfl)
  | negative t =>
    intro _
    have eq : (fun s => NEFin.singleton (Explicit.negOut s (t.observe s))) =
        (fun s => NEFin.singleton (Opaque.negOut s (t.observe s))) := by
      funext s; rw [Comparison.neg_parity]
    change Preserves (fun s => NEFin.singleton (Explicit.negOut s (t.observe s)))
    rw [eq]; exact preserves_negative t
  | host m e h ih => intro hc; cases hc
  | lift m ih => intro hc; cases hc

theorem Reviewed.preserves_of_ref (m : Reviewed.Term c A) : c = .ref → Preserves (Reviewed.observe m) := by
  induction m with
  | base m => intro hc; exact Explicit.preserves_of_ref m hc
  | bind m k ihm ihk =>
    intro hc
    change Preserves (Explicit.sequence _ _)
    rw [Explicit.sequence_equation]
    exact preserves_bind _ _ (ihm hc) (fun a => ihk a hc)
  | project e m ih => intro _; exact preserves_project _ _ e.correct (ih rfl)
  | host e m mask h ih => intro hc; cases hc
  | negative e t =>
    intro _
    have eq : Reviewed.observe (.negative e t) =
        (fun s => NEFin.singleton (negate (prune (support s) (t.observe s).state) (t.observe s))) := by
      funext s
      change NEFin.singleton _ = _
      rw [e.correct t s]
    rw [eq]; exact preserves_negative t

theorem Opaque.ref_frame (m : Opaque.Term .ref A) : Preserves (Opaque.observe m) := Opaque.preserves_of_ref m rfl
theorem Explicit.ref_frame (m : Explicit.Term .ref A) : Preserves (Explicit.observe m) := Explicit.preserves_of_ref m rfl
theorem Reviewed.ref_frame (m : Reviewed.Term .ref A) : Preserves (Reviewed.observe m) := Reviewed.preserves_of_ref m rfl

theorem host_domain_of_preserves (m : Run Unit) (hm : Preserves m) (s : State) (h : Nat) :
    HostDomain m s h ↔ FreshHost h s := by
  constructor
  · intro domain
    obtain ⟨z, hz⟩ := (m s).inhabited
    have fresh := (domain z hz).2
    simpa only [FreshHost, (hm s z hz).hosts] using fresh
  · intro fresh z hz
    refine ⟨(hm s z hz).toFrame, ?_⟩
    simpa only [FreshHost, (hm s z hz).hosts] using fresh

theorem Opaque.host_domain_iff (m : Opaque.Term .ref Unit) (s : State) (h : Nat) :
    HostDomain (Opaque.observe m) s h ↔ FreshHost h s := host_domain_of_preserves _ (Opaque.ref_frame m) s h
theorem Explicit.host_domain_iff (m : Explicit.Term .ref Unit) (s : State) (h : Nat) :
    HostDomain (Explicit.observe m) s h ↔ FreshHost h s := host_domain_of_preserves _ (Explicit.ref_frame m) s h
theorem Reviewed.host_domain_iff (m : Reviewed.Term .ref Unit) (s : State) (h : Nat) :
    HostDomain (Reviewed.observe m) s h ↔ FreshHost h s := host_domain_of_preserves _ (Reviewed.ref_frame m) s h

theorem Opaque.host_kappa_false (entry : State) (e : Mask) (h : Nat) (z : Out Unit)
    (hk : z.state.kappa = .f) : (Opaque.hostOut entry e h z).state.kappa = .f :=
  record_kappa_false _ _ _ _ hk
theorem Opaque.host_chi_false (entry : State) (e : Mask) (h : Nat) (z : Out Unit)
    (hc : z.state.chi = .f) : (Opaque.hostOut entry e h z).state.chi = .f :=
  record_chi_false _ _ _ _ hc
theorem Explicit.host_kappa_false (entry : State) (e : Mask) (h : Nat) (z : Out Unit)
    (hk : z.state.kappa = .f) : (Explicit.hostOut entry e h z).state.kappa = .f := by
  rw [Comparison.host_parity]; exact Opaque.host_kappa_false _ _ _ _ hk
theorem Explicit.host_chi_false (entry : State) (e : Mask) (h : Nat) (z : Out Unit)
    (hc : z.state.chi = .f) : (Explicit.hostOut entry e h z).state.chi = .f := by
  rw [Comparison.host_parity]; exact Opaque.host_chi_false _ _ _ _ hc
end Smusni97
