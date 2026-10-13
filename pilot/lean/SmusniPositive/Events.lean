import SmusniPositive.Readout
import SmusniF03A2.Joint

namespace SmusniPositive
open SmusniF02 SmusniF03A1
universe u v
variable {sig : Signature.{u}} {W : Type v}

inductive DefaultRow : Code sig → Prop where
  | top {m n g r} : DefaultRow (.mk (@Term.top sig m n) g r)
  | bot {m n g r} : DefaultRow (.mk (@Term.bot sig m n) g r)
  | atom {m n g r} (a : sig.Predicate) (args : Fin (sig.predicateArity a) → GroundTerm sig.Ground m) :
      DefaultRow (.mk (@Term.atom sig m n a args) g r)
  | neg {m n g r} (t : Term sig m n) : DefaultRow (.mk (.neg t) g r)
  | allG {m n g r} (body : Term sig (m+1) n) : DefaultRow (.mk (.allG body) g r)
  | allP {m n g r} (body : Term sig m (n+1)) : DefaultRow (.mk (.allP body) g r)

/-- The Input-shaped coordinate here is supplied independently of the run state.
In Content.event its state field comes from Beta, never from a run outcome. -/
inductive EventEvidence : Code sig → Input sig W → Code sig → Prop where
  | default {c i} : DefaultRow c → EventEvidence c i c
  | holdsVar {m n g r i token} (x : Fin n) : EventEvidence (r x) i token →
      EventEvidence (.mk (@Term.holdsVar sig m n x) g r) i token
  | holdsReify {m n g r i token} {t : Term sig m n} : EventEvidence (.mk t g r) i token →
      EventEvidence (.mk (.holdsReify t) g r) i token
  | ctx {m n g r i token} (k : sig.Key) (args : Fin (sig.siteArity k) → GroundTerm sig.Ground m)
      (body : Term sig m (n+1)) (q : Code sig) :
      i.context k (evalGround args g) = some q → EventEvidence (.mk body g (extend r q)) i token →
      EventEvidence (.mk (.ctx k args body) g r) i token
  | read {m n g r i token} (name : sig.Name) (body : Term sig m (n+1)) (q : Code sig) :
      i.state.assignment name = some q → EventEvidence (.mk body g (extend r q)) i token →
      EventEvidence (.mk (.read name body) g r) i token

theorem default_reclose (R : Setoid (Code sig)) {c d} (row : DefaultRow c) (same : Reclose R c d) : DefaultRow d := by
  cases row <;> cases same <;> constructor

theorem event_functional {c : Code sig} {i : Input sig W} {e e'}
    (h : EventEvidence c i e) (other : EventEvidence c i e') : e = e' := by
  induction h generalizing e' with
  | default row => cases row <;> cases other <;> rfl
  | holdsVar _ _ ih =>
    cases other with
    | default row => cases row
    | holdsVar _ h => exact ih h
  | holdsReify _ ih =>
    cases other with
    | default row => cases row
    | holdsReify h => exact ih h
  | ctx _ _ _ q found _ ih =>
    cases other with
    | default row => cases row
    | ctx _ _ _ q' found' h =>
      have eq : q = q' := Option.some.inj (found.symm.trans found')
      subst q'; exact ih h
  | read _ _ q found _ ih =>
    cases other with
    | default row => cases row
    | read _ _ q' found' h =>
      have eq : q = q' := Option.some.inj (found.symm.trans found')
      subst q'; exact ih h

noncomputable def event (c : Code sig) (i : Input sig W) : Option (Code sig) := by
  classical
  exact if h : ∃ e, EventEvidence c i e then some h.choose else none

theorem event_some (c : Code sig) (i : Input sig W) (e : Code sig) : event c i = some e ↔ EventEvidence c i e := by
  classical
  unfold event
  split
  · rename_i existsEvent
    simp only [Option.some.injEq]
    constructor
    · intro eq; exact eq ▸ existsEvent.choose_spec
    · intro h; exact event_functional existsEvent.choose_spec h
  · rename_i absent
    constructor
    · intro impossible; cases impossible
    · intro h; exact False.elim (absent ⟨e, h⟩)

theorem event_none (c : Code sig) (i : Input sig W) : event c i = none ↔ ∀ e, ¬EventEvidence c i e := by
  classical
  simp [event, not_exists]

theorem event_default {c : Code sig} (row : DefaultRow c) (i : Input sig W) : event c i = some c :=
  (event_some c i c).mpr (.default row)

theorem event_var {m n} (g : Fin m → sig.Ground) (r : Fin n → Code sig) (x : Fin n) (i : Input sig W) :
    event (.mk (.holdsVar x) g r) i = event (r x) i := by
  cases result : event (r x) i with
  | some e => exact (event_some _ _ _).mpr (.holdsVar x ((event_some _ _ _).mp result))
  | none =>
    apply (event_none _ _).mpr
    intro e h
    cases h with
    | default row => cases row
    | holdsVar _ h => exact (event_none _ _).mp result e h

theorem event_reify {m n} (t : Term sig m n) (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) :
    event (.mk (.holdsReify t) g r) i = event (.mk t g r) i := by
  cases result : event (.mk t g r) i with
  | some e => exact (event_some _ _ _).mpr (.holdsReify ((event_some _ _ _).mp result))
  | none =>
    apply (event_none _ _).mpr
    intro e h
    cases h with
    | default row => cases row
    | holdsReify h => exact (event_none _ _).mp result e h

theorem event_ctx {m n} (k : sig.Key) (args : Fin (sig.siteArity k) → GroundTerm sig.Ground m)
    (body : Term sig m (n+1)) (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) :
    event (.mk (.ctx k args body) g r) i =
      match i.context k (evalGround args g) with
      | none => none
      | some q => event (.mk body g (extend r q)) i := by
  cases found : i.context k (evalGround args g) with
  | none =>
    apply (event_none _ _).mpr
    intro e h
    cases h with
    | default row => cases row
    | ctx _ _ _ q found' h => simp [found] at found'
  | some q =>
    change event (.mk (.ctx k args body) g r) i = event (.mk body g (extend r q)) i
    cases result : event (.mk body g (extend r q)) i with
    | some e => exact (event_some _ _ _).mpr (.ctx k args body q found ((event_some _ _ _).mp result))
    | none =>
      apply (event_none _ _).mpr
      intro e h
      cases h with
      | default row => cases row
      | ctx _ _ _ q' found' h =>
        have eq : q = q' := Option.some.inj (found.symm.trans found')
        subst q'; exact (event_none _ _).mp result e h

theorem event_read {m n} (name : sig.Name) (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) :
    event (.mk (.read name body) g r) i =
      match i.state.assignment name with
      | none => none
      | some q => event (.mk body g (extend r q)) i := by
  cases found : i.state.assignment name with
  | none =>
    apply (event_none _ _).mpr
    intro e h
    cases h with
    | default row => cases row
    | read _ _ q found' h => simp [found] at found'
  | some q =>
    change event (.mk (.read name body) g r) i = event (.mk body g (extend r q)) i
    cases result : event (.mk body g (extend r q)) i with
    | some e => exact (event_some _ _ _).mpr (.read name body q found ((event_some _ _ _).mp result))
    | none =>
      apply (event_none _ _).mpr
      intro e h
      cases h with
      | default row => cases row
      | read _ _ q' found' h =>
        have eq : q = q' := Option.some.inj (found.symm.trans found')
        subst q'; exact (event_none _ _).mp result e h

def RJ (M : Model sig W) : Setoid (Code sig) where
  r c d := (Rv M).r c d ∧ ∀ i : Input sig W, PartialEq (Rv M).r (event c i) (event d i)
  iseqv := ⟨fun c => ⟨fun _ => rfl, fun i => SmusniF03A2.partial_refl (Rv M) (event c i)⟩,
    fun h => ⟨fun i => (h.1 i).symm, fun i =>
      (SmusniF03A2.event_kernel (Rv M) _ _).mp ((SmusniF03A2.event_kernel (Rv M) _ _).mpr (h.2 i)).symm⟩,
    fun h k => ⟨fun i => (h.1 i).trans (k.1 i), fun i =>
      (SmusniF03A2.event_kernel (Rv M) _ _).mp
        (((SmusniF03A2.event_kernel (Rv M) _ _).mpr (h.2 i)).trans
          ((SmusniF03A2.event_kernel (Rv M) _ _).mpr (k.2 i)))⟩⟩

theorem rj_value_sound (M : Model sig W) : ValueSound M (RJ M) := fun _ _ h => h.1

def EventSound (M : Model sig W) (R : Setoid (Code sig)) : Prop :=
  ∀ c d, R.r c d → ∀ i : Input sig W, PartialEq (Rv M).r (event c i) (event d i)

theorem event_partner (M : Model sig W) {c d e : Code sig} {i : Input sig W}
    (rel : PartialEq (Rv M).r (event c i) (event d i)) (h : EventEvidence c i e) :
    ∃ e', EventEvidence d i e' ∧ (Rv M).r e e' := by
  have old := (event_some _ _ _).mpr h
  rw [old] at rel
  cases found : event d i with
  | none => simp [found, PartialEq] at rel
  | some e' => exact ⟨e', (event_some _ _ _).mp found, by simpa only [found, PartialEq] using rel⟩

theorem reclose_rv (M : Model sig W) (R : Setoid (Code sig)) (sound : ValueSound M R)
    {c d} (same : Reclose R c d) : (Rv M).r c d :=
  fun i => value_transport M R sound same (input_refl R i)

theorem event_evidence_transport (M : Model sig W) (R : Setoid (Code sig))
    (truthSound : ValueSound M R) (eventSound : EventSound M R)
    {c token : Code sig} {i : Input sig W} (h : EventEvidence c i token) :
    ∀ {d : Code sig} {j : Input sig W}, Reclose R c d → InputRel R i j →
      ∃ token', EventEvidence d j token' ∧ (Rv M).r token token' := by
  induction h with
  | default row =>
    intro d j same inputs
    exact ⟨d, .default (default_reclose R row same), reclose_rv M R truthSound same⟩
  | holdsVar x _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      obtain ⟨moved, hm, rm⟩ := ih (reclose_refl R _) inputs
      obtain ⟨replaced, hr, rr⟩ := event_partner M (eventSound _ _ (prop x) j) hm
      exact ⟨replaced, .holdsVar x hr, (Rv M).trans rm rr⟩
  | holdsReify _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      obtain ⟨token', h', related⟩ := ih (.mk ground prop) inputs
      exact ⟨token', .holdsReify h', related⟩
  | @ctx m n g r i token k args body q found _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      cases ground
      have relation := inputs.context k (evalGround args g)
      rw [found] at relation
      obtain ⟨q', found', related⟩ := option_partner _ relation
      obtain ⟨token', h', tokens⟩ := ih (.mk rfl (extend_related R prop related)) inputs
      exact ⟨token', .ctx k args body q' found' h', tokens⟩
  | read name body q found _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      have relation := inputs.state.1 name
      rw [found] at relation
      obtain ⟨q', found', related⟩ := option_partner _ relation
      obtain ⟨token', h', tokens⟩ := ih (.mk ground (extend_related R prop related)) inputs
      exact ⟨token', .read name body q' found' h', tokens⟩

theorem event_transport (M : Model sig W) (R : Setoid (Code sig))
    (truthSound : ValueSound M R) (eventSound : EventSound M R)
    {c d : Code sig} {i j : Input sig W} (same : Reclose R c d) (inputs : InputRel R i j) :
    PartialEq (Rv M).r (event c i) (event d j) := by
  cases old : event c i with
  | some token =>
    obtain ⟨token', h', tokens⟩ := event_evidence_transport M R truthSound eventSound
      ((event_some _ _ _).mp old) same inputs
    rw [(event_some _ _ _).mpr h']
    exact tokens
  | none =>
    cases new : event d j with
    | none => trivial
    | some token' =>
      obtain ⟨token, h, _⟩ := event_evidence_transport M R truthSound eventSound
        ((event_some _ _ _).mp new) (reclose_symm R same) (input_symm R inputs)
      exact False.elim ((event_none _ _).mp old token h)

theorem reclose_rj (M : Model sig W) {c d} (same : Reclose (RJ M) c d) : (RJ M).r c d :=
  ⟨reclose_rv M (RJ M) (rj_value_sound M) same,
   fun i => event_transport M (RJ M) (rj_value_sound M) (fun _ _ h => h.2) same (input_refl _ i)⟩

def EventStep (X : Code sig → Input sig W → Code sig → Prop) : Code sig → Input sig W → Code sig → Prop
  | .mk t g r, i, token => match t with
    | .holdsVar x => X (r x) i token
    | .holdsReify t => X (.mk t g r) i token
    | .ctx k args body => ∃ q, i.context k (evalGround args g) = some q ∧ X (.mk body g (extend r q)) i token
    | .read name body => ∃ q, i.state.assignment name = some q ∧ X (.mk body g (extend r q)) i token
    | .top => token = .mk .top g r
    | .bot => token = .mk .bot g r
    | .atom a args => token = .mk (.atom a args) g r
    | .neg t => token = .mk (.neg t) g r
    | .allG body => token = .mk (.allG body) g r
    | .allP body => token = .mk (.allP body) g r

theorem event_least_prefixed (X : Code sig → Input sig W → Code sig → Prop)
    (closed : ∀ c i token, EventStep X c i token → X c i token)
    {c i token} (h : EventEvidence c i token) : X c i token := by
  induction h with
  | default row => apply closed; cases row <;> rfl
  | holdsVar _ _ ih => exact closed _ _ _ ih
  | holdsReify _ ih => exact closed _ _ _ ih
  | ctx _ _ _ q found _ ih => exact closed _ _ _ ⟨q, found, ih⟩
  | read _ _ q found _ ih => exact closed _ _ _ ⟨q, found, ih⟩
end SmusniPositive
