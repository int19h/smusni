import SmusniPositive.Events

namespace SmusniPositive
universe u v
variable {sig : Signature.{u}} {W : Type v}

theorem extend_comp (rho : Fin n' → A) (a : A) (f : Fin n → Fin n') :
    (fun i => extend rho a (liftIndex f i)) = extend (fun j => rho (f j)) a :=
  funext (extend_liftIndex rho a f)

@[simp] theorem evalGround_rename {m m'} (args : Fin arity → GroundTerm G m) (f : Fin m → Fin m') (g : Fin m' → G) :
    evalGround (fun i => (args i).rename f) g = evalGround args (fun x => g (f x)) :=
  funext (fun i => GroundTerm.eval_rename f g (args i))

theorem rename_value (M : Model sig W) {m n} (t : Term sig m n) {m' n'}
    (fg : Fin m → Fin m') (fp : Fin n → Fin n') (g : Fin m' → sig.Ground)
    (r : Fin n' → Code sig) (i : Input sig W) :
    value M (.mk (t.rename fg fp) g r) i = value M (.mk t (fun x => g (fg x)) (fun x => r (fp x))) i := by
  induction t generalizing m' n' with
  | top => simp only [Term.rename, value_top]
  | bot => simp only [Term.rename, value_bot]
  | atom => simp only [Term.rename, value_atom, evalGround_rename]
  | neg t ih => simp only [Term.rename, value_neg, ih]
  | holdsVar => simp only [Term.rename, value_holdsVar]
  | holdsReify t ih => simp only [Term.rename, value_holdsReify, ih]
  | ctx k args body ih => simp only [Term.rename, value_ctx, evalGround_rename, ih, extend_comp]
  | read name body ih => simp only [Term.rename, value_read, ih, extend_comp]
  | allG body ih =>
    apply truth_ext
    · simp only [Term.rename, value_allG_true, ih, extend_comp]
    · simp only [Term.rename, value_allG_false, ih, extend_comp]
  | allP body ih =>
    apply truth_ext
    · simp only [Term.rename, value_allP_true, ih, extend_comp]
    · simp only [Term.rename, value_allP_false, ih, extend_comp]

theorem rename_event (M : Model sig W) {m n} (t : Term sig m n) {m' n'}
    (fg : Fin m → Fin m') (fp : Fin n → Fin n') (g : Fin m' → sig.Ground)
    (r : Fin n' → Code sig) (i : Input sig W) :
    SmusniF02.PartialEq (Rv M).r (event (.mk (t.rename fg fp) g r) i)
      (event (.mk t (fun x => g (fg x)) (fun x => r (fp x))) i) := by
  induction t generalizing m' n' with
  | top =>
    rw [Term.rename, event_default .top, event_default .top]
    exact fun j => rename_value M .top fg fp g r j
  | bot =>
    rw [Term.rename, event_default .bot, event_default .bot]
    exact fun j => rename_value M .bot fg fp g r j
  | atom a args =>
    rw [Term.rename, event_default (.atom _ _), event_default (.atom _ _)]
    exact fun j => rename_value M (.atom a args) fg fp g r j
  | neg t ih =>
    rw [Term.rename, event_default (.neg _), event_default (.neg _)]
    exact fun j => rename_value M (.neg t) fg fp g r j
  | allG body ih =>
    rw [Term.rename, event_default (.allG _), event_default (.allG _)]
    exact fun j => rename_value M (.allG body) fg fp g r j
  | allP body ih =>
    rw [Term.rename, event_default (.allP _), event_default (.allP _)]
    exact fun j => rename_value M (.allP body) fg fp g r j
  | holdsVar x =>
    simp only [Term.rename, event_var]
    exact SmusniF03A2.partial_refl (Rv M) _
  | holdsReify t ih =>
    simpa only [Term.rename, event_reify] using ih fg fp g r
  | ctx k args body ih =>
    simp only [Term.rename, event_ctx, evalGround_rename]
    cases found : i.context k (evalGround args (fun x => g (fg x))) with
    | none => trivial
    | some q => simpa only [extend_comp] using ih fg (liftIndex fp) g (extend r q)
  | read name body ih =>
    simp only [Term.rename, event_read]
    cases found : i.state.assignment name with
    | none => trivial
    | some q => simpa only [extend_comp] using ih fg (liftIndex fp) g (extend r q)

theorem rename_rj (M : Model sig W) {m n} (t : Term sig m n) {m' n'}
    (fg : Fin m → Fin m') (fp : Fin n → Fin n') (g : Fin m' → sig.Ground) (r : Fin n' → Code sig) :
    (RJ M).r (.mk (t.rename fg fp) g r) (.mk t (fun x => g (fg x)) (fun x => r (fp x))) :=
  ⟨fun i => rename_value M t fg fp g r i, fun i => rename_event M t fg fp g r i⟩

theorem weakenG_rj (M : Model sig W) {m n} (t : Term sig m n) (g : Fin m → sig.Ground)
    (r : Fin n → Code sig) (a : sig.Ground) : (RJ M).r (.mk t.weakenG (extend g a) r) (.mk t g r) :=
  rename_rj M t Fin.succ id (extend g a) r

theorem weakenP_rj (M : Model sig W) {m n} (t : Term sig m n) (g : Fin m → sig.Ground)
    (r : Fin n → Code sig) (q : Code sig) : (RJ M).r (.mk t.weakenP g (extend r q)) (.mk t g r) :=
  rename_rj M t id Fin.succ g (extend r q)
end SmusniPositive
