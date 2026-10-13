import SmusniPositive.Syntax

namespace SmusniPositive
universe u v
variable {sig : Signature.{u}} {W : Type v}

/-- Positive signed evidence. Universal true rules range over the entire domain,
including all raw Code, with no finite enumeration or depth bound. -/
inductive Evidence (M : Model sig W) : Code sig → Input sig W → Bool → Prop where
  | top {m n g r i} : Evidence M (.mk (@Term.top sig m n) g r) i true
  | bot {m n g r i} : Evidence M (.mk (@Term.bot sig m n) g r) i false
  | atom {m n g r i} (a : sig.Predicate) (args : Fin (sig.predicateArity a) → GroundTerm sig.Ground m) :
      Evidence M (.mk (@Term.atom sig m n a args) g r) i (M.lexical a i.world (evalGround args g))
  | neg {m n g r i b} {t : Term sig m n} : Evidence M (.mk t g r) i (!b) →
      Evidence M (.mk (.neg t) g r) i b
  | holdsVar {m n g r i b} (x : Fin n) : Evidence M (r x) i b →
      Evidence M (.mk (@Term.holdsVar sig m n x) g r) i b
  | holdsReify {m n g r i b} {t : Term sig m n} : Evidence M (.mk t g r) i b →
      Evidence M (.mk (.holdsReify t) g r) i b
  | ctx {m n g r i b} (k : sig.Key) (args : Fin (sig.siteArity k) → GroundTerm sig.Ground m)
      (body : Term sig m (n+1)) (q : Code sig) :
      i.context k (evalGround args g) = some q → Evidence M (.mk body g (extend r q)) i b →
      Evidence M (.mk (.ctx k args body) g r) i b
  | read {m n g r i b} (name : sig.Name) (body : Term sig m (n+1)) (q : Code sig) :
      i.state.assignment name = some q → Evidence M (.mk body g (extend r q)) i b →
      Evidence M (.mk (.read name body) g r) i b
  | allGT {m n g r i} (body : Term sig (m+1) n) :
      (∀ a : sig.Ground, Evidence M (.mk body (extend g a) r) i true) →
      Evidence M (.mk (.allG body) g r) i true
  | allGF {m n g r i} (body : Term sig (m+1) n) (a : sig.Ground) :
      Evidence M (.mk body (extend g a) r) i false → Evidence M (.mk (.allG body) g r) i false
  | allPT {m n g r i} (body : Term sig m (n+1)) :
      (∀ q : Code sig, Evidence M (.mk body g (extend r q)) i true) →
      Evidence M (.mk (.allP body) g r) i true
  | allPF {m n g r i} (body : Term sig m (n+1)) (q : Code sig) :
      Evidence M (.mk body g (extend r q)) i false → Evidence M (.mk (.allP body) g r) i false

/-- The actual rule operator on arbitrary sets of signed configurations. -/
def Step (M : Model sig W) (X : Code sig → Input sig W → Bool → Prop) :
    Code sig → Input sig W → Bool → Prop
  | .mk t g r, i, b => match t with
    | .top => b = true
    | .bot => b = false
    | .atom a args => b = M.lexical a i.world (evalGround args g)
    | .neg t => X (.mk t g r) i (!b)
    | .holdsVar x => X (r x) i b
    | .holdsReify t => X (.mk t g r) i b
    | .ctx k args body => ∃ q, i.context k (evalGround args g) = some q ∧ X (.mk body g (extend r q)) i b
    | .read name body => ∃ q, i.state.assignment name = some q ∧ X (.mk body g (extend r q)) i b
    | .allG body => if b then ∀ a, X (.mk body (extend g a) r) i true else ∃ a, X (.mk body (extend g a) r) i false
    | .allP body => if b then ∀ q, X (.mk body g (extend r q)) i true else ∃ q, X (.mk body g (extend r q)) i false

theorem evidence_to_step {M : Model sig W} {c i b} (h : Evidence M c i b) : Step M (Evidence M) c i b := by
  cases h with
  | top => rfl
  | bot => rfl
  | atom => rfl
  | neg h => exact h
  | holdsVar _ h => exact h
  | holdsReify h => exact h
  | ctx _ _ _ q found h => exact ⟨q, found, h⟩
  | read _ _ q found h => exact ⟨q, found, h⟩
  | allGT _ h => exact h
  | allGF _ a h => exact ⟨a, h⟩
  | allPT _ h => exact h
  | allPF _ q h => exact ⟨q, h⟩

theorem step_to_evidence {M : Model sig W} {c i b} (h : Step M (Evidence M) c i b) : Evidence M c i b := by
  cases c with
  | mk t g r =>
    cases t with
    | top => cases h; exact .top
    | bot => cases h; exact .bot
    | atom a args => cases h; exact .atom a args
    | neg t => exact .neg h
    | holdsVar x => exact .holdsVar x h
    | holdsReify t => exact .holdsReify h
    | ctx k args body => obtain ⟨q, found, h⟩ := h; exact .ctx k args body q found h
    | read name body => obtain ⟨q, found, h⟩ := h; exact .read name body q found h
    | allG body =>
      cases b with
      | true => exact .allGT body h
      | false => obtain ⟨a, h⟩ := h; exact .allGF body a h
    | allP body =>
      cases b with
      | true => exact .allPT body h
      | false => obtain ⟨q, h⟩ := h; exact .allPF body q h

theorem evidence_fixed (M : Model sig W) (c i b) : Evidence M c i b ↔ Step M (Evidence M) c i b :=
  ⟨evidence_to_step, step_to_evidence⟩

theorem least_prefixed (M : Model sig W) (X : Code sig → Input sig W → Bool → Prop)
    (closed : ∀ c i b, Step M X c i b → X c i b) {c i b} (h : Evidence M c i b) : X c i b := by
  induction h with
  | top => exact closed _ _ _ rfl
  | bot => exact closed _ _ _ rfl
  | atom => exact closed _ _ _ rfl
  | neg _ ih => exact closed _ _ _ ih
  | holdsVar _ _ ih => exact closed _ _ _ ih
  | holdsReify _ ih => exact closed _ _ _ ih
  | ctx _ _ _ q found _ ih => exact closed _ _ _ ⟨q, found, ih⟩
  | read _ _ q found _ ih => exact closed _ _ _ ⟨q, found, ih⟩
  | allGT _ _ ih => exact closed _ _ _ ih
  | allGF _ a _ ih => exact closed _ _ _ ⟨a, ih⟩
  | allPT _ _ ih => exact closed _ _ _ ih
  | allPF _ q _ ih => exact closed _ _ _ ⟨q, ih⟩

theorem sign_unique {M : Model sig W} {c i b b'} (h : Evidence M c i b) (other : Evidence M c i b') : b = b' := by
  induction h generalizing b' with
  | top => cases other; rfl
  | bot => cases other; rfl
  | atom => cases other; rfl
  | neg _ ih =>
    cases other with
    | neg h => simpa only [Bool.not_not] using congrArg Bool.not (ih h)
  | holdsVar _ _ ih => cases other with | holdsVar _ h => exact ih h
  | holdsReify _ ih => cases other with | holdsReify h => exact ih h
  | ctx _ _ _ q found _ ih =>
    cases other with
    | ctx _ _ _ q' found' h =>
      have eq : q = q' := Option.some.inj (found.symm.trans found')
      subst q'
      exact ih h
  | read _ _ q found _ ih =>
    cases other with
    | read _ _ q' found' h =>
      have eq : q = q' := Option.some.inj (found.symm.trans found')
      subst q'
      exact ih h
  | allGT _ _ ih =>
    cases other with
    | allGT => rfl
    | allGF _ a h => exact ih a h
  | allGF _ a _ ih =>
    cases other with
    | allGT _ h => exact ih (h a)
    | allGF => rfl
  | allPT _ _ ih =>
    cases other with
    | allPT => rfl
    | allPF _ q h => exact ih q h
  | allPF _ q _ ih =>
    cases other with
    | allPT _ h => exact ih (h q)
    | allPF => rfl

theorem consistent {M : Model sig W} {c i b} (h : Evidence M c i b) : ¬Evidence M c i (!b) := by
  intro other
  have eq := sign_unique h other
  cases b <;> cases eq
end SmusniPositive
