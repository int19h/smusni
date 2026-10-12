import Smusni97.ReferenceFrames

namespace Smusni97
open SmusniF02

def Explicit.opaqueCat : Explicit.Cat → Opaque.Cat | .ref => .ref | .perf => .perf
def Explicit.toOpaque : Explicit.Term c A → Opaque.Term (Explicit.opaqueCat c) A
  | .pure a => .pure a
  | .test t => .test t
  | .emit side => .emit side
  | .bind m k => .bind (Explicit.toOpaque m) (fun a => Explicit.toOpaque (k a))
  | .local m => .local (Explicit.toOpaque m)
  | .body m => .body (Explicit.toOpaque m)
  | .negative t => .negative t
  | .host m e h => .host (Explicit.toOpaque m) e h
  | .lift m => .lift (Explicit.toOpaque m)

theorem Explicit.toOpaque_observe (m : Explicit.Term c A) :
    Explicit.observe m = Opaque.observe (Explicit.toOpaque m) := by
  induction m with
  | pure a => rfl
  | test t => rfl
  | emit side => rfl
  | bind m k ihm ihk =>
    simp only [Explicit.observe, Explicit.toOpaque, Opaque.observe, Explicit.sequence_equation, ihm]
    congr 1; funext a; exact ihk a
  | «local» m ih =>
    change (fun s => mapResults (Explicit.localOut s) (Explicit.observe m s)) =
      (fun s => mapResults (Opaque.localOut s) (Opaque.observe (Explicit.toOpaque m) s))
    rw [ih]; funext s
    exact congrArg (fun f => mapResults f _) (funext (Comparison.local_parity s))
  | body m ih =>
    change (fun s => mapResults (Explicit.localOut s) (Explicit.observe m s)) =
      (fun s => mapResults (Opaque.localOut s) (Opaque.observe (Explicit.toOpaque m) s))
    rw [ih]; funext s
    exact congrArg (fun f => mapResults f _) (funext (Comparison.local_parity s))
  | negative t =>
    funext s
    exact congrArg NEFin.singleton (Comparison.neg_parity s (t.observe s))
  | host m e h ih =>
    change (fun s => mapResults (Explicit.hostOut s e h) (Explicit.observe m s)) =
      (fun s => mapResults (Opaque.hostOut s e h) (Opaque.observe (Explicit.toOpaque m) s))
    rw [ih]; funext s
    exact congrArg (fun f => mapResults f _) (funext (Comparison.host_parity s e h))
  | lift m ih => exact ih

theorem Explicit.toOpaque_admitted (m : Explicit.Term c A) :
    ∀ s, Explicit.Admitted m s → Opaque.Admitted (Explicit.toOpaque m) s := by
  induction m with
  | pure a => intro _ _; trivial
  | test t => intro _ h; exact h
  | emit side => intro _ _; trivial
  | bind m k ihm ihk =>
    intro s ok
    refine ⟨ihm s ok.1, ?_⟩
    intro t a hz
    apply ihk a t
    apply ok.2 t a
    rwa [Explicit.toOpaque_observe]
  | «local» m ih => exact ih
  | body m ih => exact ih
  | negative t => intro _ h; exact h
  | host m e h ih =>
    intro s ok
    refine ⟨ih s ok.1, ?_⟩
    intro z hz
    apply ok.2 z
    rwa [Explicit.toOpaque_observe]
  | lift m ih => exact ih

theorem mapResults_congr_on (xs : Results A) (f g : Out A → Out B)
    (h : ∀ x, x ∈ xs → f x = g x) : mapResults f xs = mapResults g xs := by
  apply NEFin.ext
  intro z
  change (∃ x, x ∈ xs ∧ z = f x) ↔ (∃ x, x ∈ xs ∧ z = g x)
  constructor
  · rintro ⟨x, hx, eq⟩; exact ⟨x, hx, eq.trans (h x hx)⟩
  · rintro ⟨x, hx, eq⟩; exact ⟨x, hx, eq.trans (h x hx).symm⟩

theorem bind_congr_on (m m' : Run A) (k k' : A → Run B) (s : State)
    (hm : m s = m' s) (hk : ∀ t a, .live t a ∈ m s → k a t = k' a t) :
    SmusniF02.Run.bind m k s = SmusniF02.Run.bind m' k' s := by
  change (m s).unionMap _ = (m' s).unionMap _
  rw [← hm]
  apply NEFin.ext
  intro z
  simp only [NEFin.mem_unionMap]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  cases x with
  | live t a => simp only [SmusniF02.Run.extend, hk t a hx]
  | dead t => rfl
  | undef t => rfl

/-- Certificates determine the operation, not a list of known body names. -/
def Reviewed.toOpaque : Reviewed.Term c A → Opaque.Term (Explicit.opaqueCat c) A
  | .base m => Explicit.toOpaque m
  | .bind m k => .bind (Reviewed.toOpaque m) (fun a => Reviewed.toOpaque (k a))
  | .project _ m => .local (Reviewed.toOpaque m)
  | .host _ m e h => .host (Reviewed.toOpaque m) e h
  | .negative _ t => .negative t

theorem Reviewed.project_observe (exported : Reviewed.LocalExport A) (m : Reviewed.Term .ref A) :
    Reviewed.observe (.project exported m) = Opaque.localRun (Reviewed.observe m) := by
  funext s
  apply mapResults_congr_on
  intro z _
  exact exported.correct s z

theorem Reviewed.negative_observe (exported : Reviewed.NegativeExport) (t : RefTest) :
    Reviewed.observe (.negative exported t) = Opaque.negRun t := by
  funext s
  exact congrArg NEFin.singleton (exported.correct t s)

theorem Reviewed.ref_observe_toOpaque (m : Reviewed.Term c A) :
    c = .ref → Reviewed.observe m = Opaque.observe (Reviewed.toOpaque m) := by
  induction m with
  | base m => intro _; exact Explicit.toOpaque_observe m
  | bind m k ihm ihk =>
    intro hc
    simp only [Reviewed.observe, Reviewed.toOpaque, Opaque.observe, Explicit.sequence_equation, ihm hc]
    congr 1; funext a; exact ihk a hc
  | project e m ih =>
    intro _
    rw [Reviewed.project_observe]
    change Opaque.localRun (Reviewed.observe m) = Opaque.localRun (Opaque.observe (Reviewed.toOpaque m))
    rw [ih rfl]
  | host e m mask h ih => intro hc; cases hc
  | negative e t => intro _; exact Reviewed.negative_observe e t

theorem Reviewed.toOpaque_transport (m : Reviewed.Term c A) : ∀ s, Reviewed.Admitted m s →
    Opaque.Admitted (Reviewed.toOpaque m) s ∧
    Reviewed.observe m s = Opaque.observe (Reviewed.toOpaque m) s := by
  induction m with
  | base m => intro s ok; exact ⟨Explicit.toOpaque_admitted m s ok, congrFun (Explicit.toOpaque_observe m) s⟩
  | bind m k ihm ihk =>
    intro s ok
    have first := ihm s ok.1
    constructor
    · refine ⟨first.1, ?_⟩
      intro t a hz
      apply (ihk a t ?_).1
      apply ok.2 t a
      rwa [first.2]
    · change Explicit.sequence _ _ s = _
      rw [Explicit.sequence_equation]
      exact bind_congr_on _ _ _ _ s first.2 (fun t a hz => (ihk a t (ok.2 t a hz)).2)
  | project e m ih =>
    intro s ok
    have first := ih s ok
    refine ⟨first.1, ?_⟩
    rw [Reviewed.project_observe]
    change mapResults (Opaque.localOut s) _ = mapResults (Opaque.localOut s) _
    rw [first.2]
    rfl
  | host e m mask h ih =>
    intro s ok
    have first := ih s ok.1
    constructor
    · refine ⟨first.1, ?_⟩
      intro z hz
      apply ok.2 z
      rwa [first.2]
    · change mapResults (Explicit.observeOut e.body s mask h) _ = mapResults (Opaque.hostOut s mask h) _
      calc
        _ = mapResults (Opaque.hostOut s mask h) (Reviewed.observe m s) := by
          apply mapResults_congr_on
          intro z hz
          exact e.correct s mask h ⟨z, (ok.2 z hz).1, (ok.2 z hz).2⟩
        _ = _ := congrArg (mapResults (Opaque.hostOut s mask h)) first.2
  | negative e t =>
    intro s ok
    exact ⟨ok, congrFun (Reviewed.negative_observe e t) s⟩

theorem Reviewed.public_run_parity (m : Reviewed.Term c A) (s : State) (ok : Reviewed.Admitted m s) :
    Reviewed.run m s ok = Opaque.run (Reviewed.toOpaque m) s (Reviewed.toOpaque_transport m s ok).1 :=
  (Reviewed.toOpaque_transport m s ok).2
end Smusni97
