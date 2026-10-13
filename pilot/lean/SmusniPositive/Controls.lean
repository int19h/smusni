import SmusniPositive.Admission

namespace SmusniPositive.Controls
open SmusniF02 SmusniF03A1
universe u v
variable {sig : Signature.{u}} {W : Type v}

def nullTuple (k : sig.Key) (arity : sig.siteArity k = 0) : Fin (sig.siteArity k) → sig.Ground :=
  fun x => Fin.elim0 (Fin.cast arity x)
def nullArgs (k : sig.Key) (arity : sig.siteArity k = 0) : Fin (sig.siteArity k) → GroundTerm sig.Ground 0 :=
  fun x => Fin.elim0 (Fin.cast arity x)
theorem eval_null (k : sig.Key) (arity : sig.siteArity k = 0) :
    evalGround (nullArgs k arity) emptyEnv = nullTuple k arity := by
  funext x; exact Fin.elim0 (Fin.cast arity x)

def liarTerm (k : sig.Key) (arity : sig.siteArity k = 0) : Term sig 0 0 :=
  .ctx k (nullArgs k arity) (.neg (.holdsVar 0))
def L (k : sig.Key) (arity : sig.siteArity k = 0) : Code sig := closed (liarTerm k arity)
def BL (k : sig.Key) (arity : sig.siteArity k = 0) : Code sig := negCode (L k arity)
def literalNegL (k : sig.Key) (arity : sig.siteArity k = 0) : Code sig := closed (.neg (liarTerm k arity))
def J (k : sig.Key) (arity : sig.siteArity k = 0) : Code sig := closed (.ctx k (nullArgs k arity) (.holdsVar 0))

/-- In particular, the self-returning L/J conditions are satisfiable whenever
their declared key exists. They require no recursive literal closure. -/
theorem retrieval_condition_inhabited (c : Code sig) (k : sig.Key)
    (args : Fin (sig.siteArity k) → sig.Ground) :
    ∃ E : Context sig, E k args = some c := ⟨fun _ _ => some c, rfl⟩

theorem liar_equation (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (i : Input sig W)
    (self : i.context k (nullTuple k arity) = some (L k arity)) :
    value M (L k arity) i = negSK (value M (L k arity) i) := by
  have hc := value_ctx M emptyEnv emptyEnv i k (nullArgs k arity) (.neg (.holdsVar 0))
  simp only [eval_null, self] at hc
  calc
    value M (L k arity) i = value M (BL k arity) i := hc
    _ = negSK (value M (L k arity) i) := by
      change value M (.mk (.neg (.holdsVar 0)) emptyEnv (extend emptyEnv (L k arity))) i = _
      rw [value_neg, value_holdsVar]
      rfl

theorem liar_undefined (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (L k arity)) (w : W) (s : RawState sig) :
    value M (L k arity) ⟨E, w, s⟩ = .u := (negSK_fixed _).mp (liar_equation M k arity _ self)

theorem liar_event (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (L k arity)) (w : W) (beta : RawState sig) :
    event (L k arity) ⟨E, w, beta⟩ = some (BL k arity) := by
  have hc := event_ctx k (nullArgs k arity) (.neg (.holdsVar 0)) emptyEnv emptyEnv (⟨E, w, beta⟩ : Input sig W)
  simp only [eval_null, self] at hc
  exact hc.trans (event_default (.neg _) _)

/-- This profile-token equality is global, unlike the resolver-qualified event equation. -/
theorem liar_token_global (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) :
    Quotient.mk (Rv M) (BL k arity) = Quotient.mk (Rv M) (literalNegL k arity) := by
  apply Quotient.sound
  intro i
  change value M (.mk (.neg (.holdsVar 0)) emptyEnv (extend emptyEnv (L k arity))) i =
    value M (.mk (.neg (liarTerm k arity)) emptyEnv emptyEnv) i
  rw [value_neg, value_neg, value_holdsVar]
  rfl

theorem liar_observable_event (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (L k arity)) (w : W) (beta : RawState sig) :
    SmusniF03A2.qEvent (Rv M) (event (L k arity) ⟨E, w, beta⟩) =
      some (Quotient.mk (Rv M) (literalNegL k arity)) := by
  rw [liar_event k arity E self w beta]
  exact congrArg some (liar_token_global M k arity)

theorem liar_top_resolver (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (top : E k (nullTuple k arity) = some (topCode sig)) (w : W) (s : RawState sig) :
    value M (L k arity) ⟨E, w, s⟩ = .f := by
  have hc := value_ctx M emptyEnv emptyEnv (⟨E, w, s⟩ : Input sig W) k (nullArgs k arity) (.neg (.holdsVar 0))
  simp only [eval_null, top] at hc
  calc
    _ = value M (.mk (.neg (.holdsVar 0)) emptyEnv (extend emptyEnv (topCode sig))) ⟨E, w, s⟩ := hc
    _ = .f := by simp only [value_neg, value_holdsVar, extend_zero, topCode, closed, value_top, negSK]

theorem liar_absent_resolver (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (absent : E k (nullTuple k arity) = none) (w : W) (s beta : RawState sig) :
    value M (L k arity) ⟨E, w, s⟩ = .u ∧ event (L k arity) ⟨E, w, beta⟩ = none := by
  have hv := value_ctx M emptyEnv emptyEnv (⟨E, w, s⟩ : Input sig W) k (nullArgs k arity) (.neg (.holdsVar 0))
  have he := event_ctx k (nullArgs k arity) (.neg (.holdsVar 0)) emptyEnv emptyEnv (⟨E, w, beta⟩ : Input sig W)
  simp only [eval_null, absent] at hv he
  exact ⟨hv, he⟩

/-- A verified copying region cannot contain evidence in the least fixed point.
The hypothesis concerns one rule step for an arbitrary predicate X, not the desired absence. -/
theorem copying_region_absent (M : Model sig W) (i : Input sig W) (region : Code sig → Prop)
    (copy : ∀ c, region c → ∀ X b, Step M X c i b → ∃ d, region d ∧ X d i b)
    {c b} (member : region c) : ¬Evidence M c i b := by
  intro evidence
  let X : Code sig → Input sig W → Bool → Prop := fun d j _ => j = i → ¬region d
  have closed : ∀ d j sign, Step M X d j sign → X d j sign := by
    intro d j sign step equal
    subst j
    intro mem
    obtain ⟨next, nextMem, nextX⟩ := copy d mem X sign step
    exact nextX rfl nextMem
  exact least_prefixed M X closed evidence rfl member

def JRegion (k : sig.Key) (arity : sig.siteArity k = 0) (c : Code sig) : Prop :=
  c = J k arity ∨ c = holdsCode (J k arity)

theorem j_region_step (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (i : Input sig W)
    (self : i.context k (nullTuple k arity) = some (J k arity)) :
    ∀ c, JRegion k arity c → ∀ X b, Step M X c i b → ∃ d, JRegion k arity d ∧ X d i b := by
  intro c member X b step
  rcases member with rfl | rfl
  · change ∃ q, i.context k (evalGround (nullArgs k arity) emptyEnv) = some q ∧
      X (.mk (.holdsVar 0) emptyEnv (extend emptyEnv q)) i b at step
    obtain ⟨q, found, next⟩ := step
    rw [eval_null, self] at found
    have eq : J k arity = q := Option.some.inj found
    subst q
    exact ⟨holdsCode (J k arity), Or.inr rfl, next⟩
  · exact ⟨J k arity, Or.inl rfl, step⟩

theorem j_no_evidence (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (J k arity)) (w : W) (s : RawState sig) (b : Bool) :
    ¬Evidence M (J k arity) ⟨E, w, s⟩ b :=
  copying_region_absent M _ _ (j_region_step M k arity _ self) (Or.inl rfl)

theorem j_undefined (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (J k arity)) (w : W) (s : RawState sig) :
    value M (J k arity) ⟨E, w, s⟩ = .u :=
  (value_undefined M _ _).mpr ⟨j_no_evidence M k arity E self w s true, j_no_evidence M k arity E self w s false⟩

theorem event_copying_region_absent (i : Input sig W) (region : Code sig → Prop)
    (copy : ∀ c, region c → ∀ X token, EventStep X c i token → ∃ d, region d ∧ X d i token)
    {c token} (member : region c) : ¬EventEvidence c i token := by
  intro evidence
  let X : Code sig → Input sig W → Code sig → Prop := fun d j _ => j = i → ¬region d
  have closed : ∀ d j token, EventStep X d j token → X d j token := by
    intro d j token step equal
    subst j
    intro mem
    obtain ⟨next, nextMem, nextX⟩ := copy d mem X token step
    exact nextX rfl nextMem
  exact event_least_prefixed X closed evidence rfl member

theorem j_event_region_step (k : sig.Key) (arity : sig.siteArity k = 0) (i : Input sig W)
    (self : i.context k (nullTuple k arity) = some (J k arity)) :
    ∀ c, JRegion k arity c → ∀ X token, EventStep X c i token → ∃ d, JRegion k arity d ∧ X d i token := by
  intro c member X token step
  rcases member with rfl | rfl
  · change ∃ q, i.context k (evalGround (nullArgs k arity) emptyEnv) = some q ∧
      X (.mk (.holdsVar 0) emptyEnv (extend emptyEnv q)) i token at step
    obtain ⟨q, found, next⟩ := step
    rw [eval_null, self] at found
    have eq : J k arity = q := Option.some.inj found
    subst q
    exact ⟨holdsCode (J k arity), Or.inr rfl, next⟩
  · exact ⟨J k arity, Or.inl rfl, step⟩

theorem j_no_event_evidence (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (J k arity)) (w : W) (beta : RawState sig) (token : Code sig) :
    ¬EventEvidence (J k arity) ⟨E, w, beta⟩ token :=
  event_copying_region_absent _ _ (j_event_region_step k arity _ self) (Or.inl rfl)

theorem j_absent_event (k : sig.Key) (arity : sig.siteArity k = 0) (E : Context sig)
    (self : E k (nullTuple k arity) = some (J k arity)) (w : W) (beta : RawState sig) :
    event (J k arity) ⟨E, w, beta⟩ = none :=
  (event_none _ _).mpr (j_no_event_evidence k arity E self w beta)

def doubleNegHolds (c : Code sig) : Code sig :=
  .mk (.neg (.neg (.holdsVar 0))) emptyEnv (extend emptyEnv c)

theorem double_neg_same_runs (M : Model sig W) (c : Code sig) : run M c = run M (doubleNegHolds c) := by
  apply (run_profile_kernel M _ _).mpr
  intro i
  change value M c i = value M (.mk (.neg (.neg (.holdsVar 0))) emptyEnv (extend emptyEnv c)) i
  rw [value_neg, value_neg, value_holdsVar, negSK_twice]
  rfl

theorem j_double_neg_distinct (M : Model sig W) (k : sig.Key) (arity : sig.siteArity k = 0)
    (E : Context sig) (self : E k (nullTuple k arity) = some (J k arity)) (w : W) :
    Quotient.mk (RJ M) (J k arity) ≠ Quotient.mk (RJ M) (doubleNegHolds (J k arity)) := by
  intro eq
  have events := (Quotient.exact eq).2 (⟨E, w, initial sig⟩ : Input sig W)
  rw [j_absent_event k arity E self w (initial sig), doubleNegHolds, event_default (.neg _) _] at events
  exact events

def negBot (sig : Signature.{u}) : Code sig := closed (.neg .bot)

theorem top_neg_bot_same_class (M : Model sig W) :
    Quotient.mk (RJ M) (topCode sig) = Quotient.mk (RJ M) (negBot sig) := by
  apply Quotient.sound
  apply (default_rj_iff_rv M .top (.neg _)).mpr
  intro i
  simp only [value_top, value_neg, value_bot, negSK]

theorem top_bot_distinct (M : Model sig W) [Inhabited W] :
    Quotient.mk (RJ M) (topCode sig) ≠ Quotient.mk (RJ M) (botCode sig) := by
  intro eq
  have values := (Quotient.exact eq).1 (⟨absentContext sig, default, initial sig⟩ : Input sig W)
  simp [topCode, botCode, closed, value_top, value_bot] at values
end SmusniPositive.Controls
