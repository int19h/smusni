import Smusni97.Explicit
import Smusni97.Projection

namespace Smusni97.Explicit
open SmusniF02

/-- Only the state argument path is traversed. Masks remain pure expressions of
the supplied environment, including its entry and reached state. -/
def analyze (expression : Expr k) : Option (Env → Mask) :=
  match expression with
  | .reached => some (fun _ _ => true)
  | .prune mask state => (analyze state).map (fun keep e n => mask.eval e n && keep e n)
  | .entry | .record _ _ _ | .eligible | .support _ | .union _ _ | .payload | .suffix _ _ => none
termination_by structural expression

/-- Structural induction over the recognized state path. No preservation law or
input equality is assumed. A recognized mask can still remove incoming slots. -/
private def Sound (expression : Expr k) : Prop :=
  match k, expression with
  | .state, state => ∀ keep, analyze state = some keep → ∀ e, state.eval e = prune (keep e) e.reached
  | _, _ => True

private theorem sound_all (expression : Expr k) : Sound expression := by
  induction expression with
  | entry => intro keep ok e; simp [analyze] at ok
  | reached =>
    intro keep ok e
    simp only [analyze, Option.some.injEq] at ok
    subst keep
    rfl
  | record tau sigma state _ _ _ => intro keep ok e; simp [analyze] at ok
  | prune mask state _ ih =>
    intro keep ok e
    cases hs : analyze state with
    | none => simp [analyze, hs] at ok
    | some inner =>
      simp only [analyze, hs, Option.map_some, Option.some.injEq] at ok
      subst keep
      change prune (mask.eval e) (state.eval e) = _
      rw [ih inner hs e]
      exact prune_inter (mask.eval e) (inner e) e.reached
  | eligible => trivial
  | support _ _ => trivial
  | union _ _ _ _ => trivial
  | payload => trivial
  | suffix _ _ _ _ => trivial

theorem analyze_sound (state : Expr .state) (keep : Env → Mask) (ok : analyze state = some keep)
    (e : Env) : state.eval e = prune (keep e) e.reached := sound_all state keep ok e

def analyzed (state : Expr .state) (keep : Env → Mask) (ok : analyze state = some keep) :
    Projection Env.reached := ⟨state.eval, keep, analyze_sound state keep ok⟩

theorem analyzed_preserves (state : Expr .state) (keep : Env → Mask) (ok : analyze state = some keep)
    (e : Env) :
    (state.eval e).sides = e.reached.sides ∧ (state.eval e).obligations = e.reached.obligations ∧
    (state.eval e).frames = e.reached.frames ∧ (state.eval e).hosts = e.reached.hosts ∧
    (state.eval e).kappa = e.reached.kappa ∧ (state.eval e).chi = e.reached.chi :=
  (analyzed state keep ok).preserves e

theorem analyzed_slots (state : Expr .state) (keep : Env → Mask) (ok : analyze state = some keep)
    (e : Env) (n : Nat) :
    (state.eval e).slots n = if keep e n then e.reached.slots n else none :=
  (analyzed state keep ok).slots e n

theorem rejects_entry : analyze .entry = none := rfl
theorem rejects_record (tau sigma : Expr .status) (state : Expr .state) :
    analyze (.record tau sigma state) = none := rfl
theorem rejects_pruned_record (mask : Expr .mask) (tau sigma : Expr .status) (state : Expr .state) :
    analyze (.prune mask (.record tau sigma state)) = none := rfl
end Smusni97.Explicit
