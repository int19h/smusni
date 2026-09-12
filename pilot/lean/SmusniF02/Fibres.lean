import SmusniF02.Carrier

/-! F02-v2 §§3–6. Profiles are external indices, never existential alternatives.
No finiteness premise is imposed on profiles, inherited coordinates or descendants. -/
namespace SmusniF02
universe u v w x y z

inductive SourceResult (R : Type u) where
  | obtained : R → SourceResult R
  | empty : SourceResult R
  | unresolved : SourceResult R
  deriving DecidableEq

def Outcome.result : Outcome S R → SourceResult R
  | .live _ r => .obtained r
  | .dead _ => .empty
  | .undef _ => .unresolved

/-- Each inherited coordinate retains its own terminal fibre, including failures. -/
abbrev Origin {P : Type u} {B : P → Type v} (source : ∀ p, B p → Terminal S R)
    (p : P) := (b : B p) × {t : Outcome S R // t ∈ source p b}

def Origin.parent {P : Type u} {B : P → Type v} {source : ∀ p, B p → Terminal S R}
    {p : P} (i : Origin source p) : B p := i.1
def Origin.result {P : Type u} {B : P → Type v} {source : ∀ p, B p → Terminal S R}
    {p : P} (i : Origin source p) : SourceResult R := i.2.val.result
def Origin.reached {P : Type u} {B : P → Type v} {source : ∀ p, B p → Terminal S R}
    {p : P} (i : Origin source p) : S := i.2.val.state

theorem origin_over_each {P : Type u} {B : P → Type v}
    (source : ∀ p, B p → Terminal S R) (p : P) (b : B p) :
    ∃ i : Origin source p, i.parent = b := by
  obtain ⟨z, hz⟩ := (source p b).inhabited
  exact ⟨⟨b, z, hz⟩, rfl⟩

abbrev Descendant {P : Type u} (I : P → Type v) (L : ∀ p, I p → Type w) (p : P) :=
  (i : I p) × L p i
def parent {P : Type u} {I : P → Type v} {L : ∀ p, I p → Type w}
    (p : P) (j : Descendant I L p) : I p := j.1
theorem descendant_over_each {P : Type u} {I : P → Type v} {L : ∀ p, I p → Type w}
    (h : ∀ p i, Nonempty (L p i)) (p : P) (i : I p) :
    ∃ j : Descendant I L p, parent p j = i := by
  obtain ⟨l⟩ := h p i
  exact ⟨⟨i, l⟩, rfl⟩

abbrev Family (P : Type u) (I : P → Type v) (E : Type w) (W : Type x)
    (S : Type y) (A : Type z) := ∀ p, I p → E → W → Run S A

namespace Family
variable {P : Type u} {I : P → Type v} {J : P → Type w} {H : P → Type x}
variable {E W S A B C : Type _}

def pure (a : A) : Family P I E W S A := fun _ _ _ _ => Run.pure a
noncomputable def bind (m : Family P I E W S A) (k : A → Family P I E W S B) :
    Family P I E W S B := fun p i e w => Run.bind (m p i e w) (fun a => k a p i e w)
def pull (ρ : ∀ p, J p → I p) (m : Family P I E W S A) : Family P J E W S A :=
  fun p j => m p (ρ p j)
/-- Lift keeps inherited outer parameters; it forgets only added fibre choices. -/
def lift (ρ : ∀ p, J p → I p) (m : Family P I E W S A) : Family P J E W S A :=
  pull ρ m
def capture (e₀ : E) (m : Family P I E W S A) : Family P I E W S A :=
  fun p i _ w s => m p i e₀ w s

@[simp] theorem pure_bind (a : A) (k : A → Family P I E W S B) :
    bind (pure a) k = k a := by funext p i e w; exact Run.pure_bind _ _
@[simp] theorem bind_pure (m : Family P I E W S A) : bind m pure = m := by
  funext p i e w; exact Run.bind_pure _
theorem bind_assoc (m : Family P I E W S A) (k : A → Family P I E W S B)
    (l : B → Family P I E W S C) : bind (bind m k) l = bind m (fun a => bind (k a) l) := by
  funext p i e w; exact Run.bind_assoc _ _ _
theorem pull_pure (ρ : ∀ p, J p → I p) (a : A) :
    pull ρ (pure a : Family P I E W S A) = pure a := rfl
theorem pull_bind (ρ : ∀ p, J p → I p) (m : Family P I E W S A)
    (k : A → Family P I E W S B) :
    pull ρ (bind m k) = bind (pull ρ m) (fun a => pull ρ (k a)) := rfl
theorem pull_comp (ρ : ∀ p, J p → I p) (τ : ∀ p, H p → J p)
    (m : Family P I E W S A) : pull τ (pull ρ m) = pull (fun p h => ρ p (τ p h)) m := rfl
theorem pull_id (m : Family P I E W S A) : pull (fun _ i => i) m = m := rfl
theorem lift_pure (ρ : ∀ p, J p → I p) (a : A) :
    lift ρ (pure a : Family P I E W S A) = pure a := rfl
theorem lift_bind (ρ : ∀ p, J p → I p) (m : Family P I E W S A)
    (k : A → Family P I E W S B) :
    lift ρ (bind m k) = bind (lift ρ m) (fun a => lift ρ (k a)) := rfl
theorem capture_pull (ρ : ∀ p, J p → I p) (e₀ : E) (m : Family P I E W S A) :
    capture e₀ (pull ρ m) = pull ρ (capture e₀ m) := rfl
theorem capture_bind (e₀ : E) (m : Family P I E W S A) (k : A → Family P I E W S B) :
    capture e₀ (bind m k) = bind (capture e₀ m) (fun a => capture e₀ (k a)) := rfl
end Family

inductive ReadPhase where | first | later deriving DecidableEq

/-- Only K and the current caller state are available: no source callback or saved state. -/
def readOutcome (phase : ReadPhase) (k : SourceResult R) (s : S) : Outcome S R :=
  match k, phase with
  | .obtained r, _ => .live s r
  | .empty, .first => .dead s
  | .empty, .later | .unresolved, _ => .undef s
def read (phase : ReadPhase) (k : SourceResult R) : Run S R :=
  fun s => NEFin.singleton (readOutcome phase k s)

@[simp] theorem read_obtained (phase : ReadPhase) (r : R) :
    read phase (.obtained r) = (Run.pure r : Run S R) := by cases phase <;> rfl
@[simp] theorem read_state (phase : ReadPhase) (k : SourceResult R) (s : S) :
    (readOutcome phase k s).state = s := by cases k <;> cases phase <;> rfl
theorem read_preserves_caller (phase : ReadPhase) (k : SourceResult R) (s : S)
    (z : Outcome S R) (hz : z ∈ read phase k s) : z.state = s := by
  have h : z = readOutcome phase k s := hz
  rw [h, read_state]

def reads {P : Type u} {I : P → Type v} (phase : ReadPhase)
    (K : ∀ p, I p → SourceResult R) : Family P I E W S R :=
  fun p i _ _ => read phase (K p i)

/-- A supplied full-domain partial resolver; no visited-tuple cache. -/
def lookup (resolve : D → Option R) (d : D) : Run S R := fun s =>
  NEFin.singleton (match resolve d with | some r => .live s r | none => .undef s)

def resolverFamily : Family Unit (fun _ => D) (D → Option R) Unit S R :=
  fun _ d resolve _ => lookup resolve d

theorem capture_full_resolver (saved caller : D → Option R) (d : D) (s : S) :
    Family.capture saved resolverFamily () d caller () s =
      NEFin.singleton (match saved d with | some r => .live s r | none => .undef s) := rfl

theorem pull_reads {P : Type u} {I : P → Type v} {J : P → Type w}
    (ρ : ∀ p, J p → I p) (phase : ReadPhase) (K : ∀ p, I p → SourceResult R) :
    Family.pull ρ (reads phase K : Family P I E W S R) =
      reads phase (fun p j => K p (ρ p j)) := rfl

theorem reads_factor {P : Type u} {I : P → Type v} (phase : ReadPhase)
    (K K' : ∀ p, I p → SourceResult R) (h : ∀ p i, K p i = K' p i) :
    (reads phase K : Family P I E W S R) = reads phase K' := by
  funext p i e w s; rw [reads, reads, h p i]

/-- Any finite number of reads at one obtained fibre gives the diagonal, not a product. -/
noncomputable def repeatedRead (phase : ReadPhase) (k : SourceResult R) : Nat → Run S (List R)
  | 0 => Run.pure []
  | n+1 => Run.bind (read phase k) (fun r =>
      Run.bind (repeatedRead phase k n) (fun rs => Run.pure (r :: rs)))

theorem repeatedRead_diagonal (phase : ReadPhase) (r : R) (n : Nat) :
    (repeatedRead phase (.obtained r) n : Run S (List R)) = Run.pure (List.replicate n r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatedRead, ih, List.replicate_succ]

/-- A source's first execution uses the reached source state, unlike any later read. -/
def firstExecution {P : Type u} {B : P → Type v}
    (source : ∀ p, B p → Terminal S R) (world : ∀ p, B p → W)
    (e₀ : E) (m : Family P (Origin source) E W S A) :
    ∀ p, Origin source p → Terminal S A :=
  fun p i => m p i e₀ (world p i.parent) i.reached
end SmusniF02
