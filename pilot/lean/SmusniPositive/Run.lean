import SmusniPositive.Events

namespace SmusniPositive
open SmusniF02 SmusniF03A1
universe u v
variable {sig : Signature.{u}} {W : Type v}

def outcomeOf (status : Truth) (s : S) : Outcome S Unit :=
  match status with | .t => .live s () | .f => .dead s | .u => .undef s
@[simp] theorem outcomeOf_truth (status : Truth) (s : S) : (outcomeOf status s).truth = status := by
  cases status <;> rfl
@[simp] theorem outcomeOf_state (status : Truth) (s : S) : (outcomeOf status s).state = s := by
  cases status <;> rfl

theorem map_outcomeOf (f : S → T) (status : Truth) (s : S) :
    mapOutcome f id (outcomeOf status s) = outcomeOf status (f s) := by cases status <;> rfl

noncomputable def run (M : Model sig W) (c : Code sig) (E : Context sig) (w : W) : SmusniF02.Run (RawState sig) Unit :=
  fun s => NEFin.singleton (outcomeOf (value M c ⟨E, w, s⟩) s)

noncomputable def rawContent (M : Model sig W) (c : Code sig) :
    Content Unit (fun _ => Unit) (Context sig) W (RawState sig) (RawState sig) (Code sig) where
  run _ _ := run M c
  event _ _ E w beta := event c ⟨E, w, beta⟩

theorem ctx_strict_bind (M : Model sig W) {m n} (k : sig.Key)
    (args : Fin (sig.siteArity k) → GroundTerm sig.Ground m) (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (E : Context sig) (w : W) (s : RawState sig) :
    run M (.mk (.ctx k args body) g r) E w s =
      SmusniF02.Run.bind (lookup (E k) (evalGround args g))
        (fun q => run M (.mk body g (extend r q)) E w) s := by
  cases found : E k (evalGround args g) <;>
    simp [run, value_ctx, found, lookup, SmusniF02.Run.bind, SmusniF02.Run.extend, outcomeOf]

theorem read_strict_bind (M : Model sig W) {m n} (name : sig.Name) (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (E : Context sig) (w : W) (s : RawState sig) :
    run M (.mk (.read name body) g r) E w s =
      SmusniF02.Run.bind (fun entry => lookup entry.assignment name entry)
        (fun q => run M (.mk body g (extend r q)) E w) s := by
  cases found : s.assignment name <;>
    simp [run, value_read, found, lookup, SmusniF02.Run.bind, SmusniF02.Run.extend, outcomeOf]

def flipOutcome : Outcome S Unit → Outcome S Unit
  | .live s _ => .dead s | .dead s => .live s () | .undef s => .undef s

theorem neg_run (M : Model sig W) {m n} (t : Term sig m n) (g : Fin m → sig.Ground)
    (r : Fin n → Code sig) (E : Context sig) (w : W) (s : RawState sig) :
    run M (.mk (.neg t) g r) E w s = mapResults flipOutcome (run M (.mk t g r) E w s) := by
  simp only [run, value_neg, mapResults_singleton]
  cases value M (.mk t g r) ⟨E, w, s⟩ <;> rfl

theorem singleton_truth (a b : Outcome S Unit) (eq : NEFin.singleton a = NEFin.singleton b) : a.truth = b.truth := by
  have ha : a ∈ NEFin.singleton b := by rw [← eq]; rfl
  exact congrArg Outcome.truth (NEFin.mem_singleton.mp ha)

theorem run_profile_kernel (M : Model sig W) (c d : Code sig) :
    run M c = run M d ↔ (Rv M).r c d := by
  constructor
  · intro eq i
    have h := congrArg (fun f => f i.context i.world i.state) eq
    have h' := singleton_truth _ _ h
    simpa only [outcomeOf_truth] using h'
  · intro eq
    funext E w s
    simp only [run, eq ⟨E, w, s⟩]

theorem default_rj_iff_rv (M : Model sig W) {c d} (hc : DefaultRow c) (hd : DefaultRow d) :
    (RJ M).r c d ↔ (Rv M).r c d := by
  constructor
  · exact fun h => h.1
  · intro rel
    refine ⟨rel, ?_⟩
    intro i
    rw [event_default hc i, event_default hd i]
    exact rel

theorem holds_code_rj (M : Model sig W) (c : Code sig) : (RJ M).r (holdsCode c) c := by
  constructor
  · intro i; exact value_holdsVar M _ _ i 0
  · intro i; rw [holdsCode, event_var]; exact SmusniF03A2.partial_refl (Rv M) (event c i)

theorem holds_reify_rj (M : Model sig W) {m n} (t : Term sig m n) (g : Fin m → sig.Ground) (r : Fin n → Code sig) :
    (RJ M).r (.mk (.holdsReify t) g r) (.mk t g r) := by
  constructor
  · intro i; exact value_holdsReify M g r i t
  · intro i; rw [event_reify]; exact SmusniF03A2.partial_refl (Rv M) _
end SmusniPositive
