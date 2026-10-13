import SmusniF03A1.Operations

namespace SmusniF03A1
open SmusniF02
universe u v w x y z

def FamilyRel {P : Type u} {I : P → Type v}
    (SR : S → T → Prop) (AR : A → B → Prop) (ER : E → E' → Prop)
    (m : Family P I E W S A) (n : Family P I E' W T B) : Prop :=
  ∀ p i e e' w, ER e e' → RunRel SR AR (m p i e w) (n p i e' w)

theorem pull_compatible {P : Type u} {I : P → Type v} {J : P → Type w}
    (SR : S → T → Prop) (AR : A → B → Prop) (ER : E → E' → Prop)
    (rho : ∀ p, J p → I p) (m : Family P I E W S A) (n : Family P I E' W T B)
    (rel : FamilyRel SR AR ER m n) : FamilyRel SR AR ER (Family.pull rho m) (Family.pull rho n) :=
  fun p j e e' world h => rel p (rho p j) e e' world h

theorem capture_compatible {P : Type u} {I : P → Type v}
    (SR : S → T → Prop) (AR : A → B → Prop) (ER : E → E' → Prop)
    (saved : E) (saved' : E') (contexts : ER saved saved')
    (m : Family P I E W S A) (n : Family P I E' W T B) (rel : FamilyRel SR AR ER m n) :
    FamilyRel SR AR ER (Family.capture saved m) (Family.capture saved' n) :=
  fun p i _ _ world _ => rel p i saved saved' world contexts

abbrev RespectingFamily {P : Type u} {I : P → Type v} {E : Type _} {W : Type _}
    (SR : S → S → Prop) (AR : A → A → Prop) :=
  {m : Family P I E W S A // ∀ p i e w, RunRel SR AR (m p i e w) (m p i e w)}

noncomputable def descendFamily {P : Type u} {I : P → Type v} {E : Type _} {W : Type _}
    (fs : S → T) (onto : Onto fs) (fa : A → B) {SR : S → S → Prop} {AR : A → A → Prop}
    (m : RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR) : Family P I E W T B :=
  fun p i e w => descend fs onto fa ⟨m.val p i e w, m.property p i e w⟩

theorem family_descend_at {P : Type u} {I : P → Type v} {E : Type _} {W : Type _}
    (fs : S → T) (onto : Onto fs) (fa : A → B) (ks : Kernel fs SR) (ka : Kernel fa AR)
    (m : RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR) (p : P) (i : I p) (e : E) (w : W) (s : S) :
    descendFamily fs onto fa m p i e w (fs s) = mapResults (mapOutcome fs fa) (m.val p i e w s) :=
  descend_at fs onto fa ks ka _ s

def pullRespecting {P : Type u} {I : P → Type v} {J : P → Type w} {E : Type _} {W : Type _}
    (rho : ∀ p, J p → I p) (m : RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR) :
    RespectingFamily (P := P) (I := J) (E := E) (W := W) SR AR :=
  ⟨Family.pull rho m.val, fun p j e w => m.property p (rho p j) e w⟩

def captureRespecting {P : Type u} {I : P → Type v} {E : Type _} {W : Type _}
    (saved : E) (m : RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR) :
    RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR :=
  ⟨Family.capture saved m.val, fun p i _ w => m.property p i saved w⟩

theorem descend_pull {P : Type u} {I : P → Type v} {J : P → Type w} {E : Type _} {W : Type _}
    (fs : S → T) (onto : Onto fs) (fa : A → B) {SR : S → S → Prop} {AR : A → A → Prop}
    (rho : ∀ p, J p → I p) (m : RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR) :
    descendFamily fs onto fa (pullRespecting rho m) = Family.pull rho (descendFamily fs onto fa m) := rfl

theorem descend_capture {P : Type u} {I : P → Type v} {E : Type _} {W : Type _}
    (fs : S → T) (onto : Onto fs) (fa : A → B) {SR : S → S → Prop} {AR : A → A → Prop}
    (saved : E) (m : RespectingFamily (P := P) (I := I) (E := E) (W := W) SR AR) :
    descendFamily fs onto fa (captureRespecting saved m) = Family.capture saved (descendFamily fs onto fa m) := rfl

/-- Full-domain comparison, not agreement on a finite cache of visited tuples. -/
def ResolverRel (DR : D → D' → Prop) (AR : A → B → Prop)
    (resolve : D → Option A) (resolve' : D' → Option B) : Prop :=
  ∀ d d', DR d d' → OptionRel AR (resolve d) (resolve' d')

theorem full_resolver_lookup (SR : S → T → Prop) (DR : D → D' → Prop) (AR : A → B → Prop)
    (resolve : D → Option A) (resolve' : D' → Option B)
    (full : ResolverRel DR AR resolve resolve') (d : D) (d' : D') (deps : DR d d') :
    RunRel SR AR (lookup resolve d) (lookup resolve' d') :=
  lookup_compatible SR AR resolve resolve' d d' (full d d' deps)

/-- The entire remainder of a supplied context is one fixed, arbitrary parameter.
This auxiliary wrapper does not add fields to the normative context. -/
structure ResolverEnv (Other : Type u) (D : Type v) (A : Type w) where
  other : Other
  resolve : D → Option A

def EnvRel (DR : D → D' → Prop) (AR : A → B → Prop)
    (e : ResolverEnv Other D A) (e' : ResolverEnv Other D' B) : Prop :=
  e.other = e'.other ∧ ResolverRel DR AR e.resolve e'.resolve

def queryFamily : Family Unit (fun _ => D) (ResolverEnv Other D A) Unit S A :=
  fun _ d e _ => lookup e.resolve d

theorem captured_resolver_lookup (SR : S → T → Prop) (DR : D → D' → Prop) (AR : A → B → Prop)
    (saved : ResolverEnv Other D A) (saved' : ResolverEnv Other D' B)
    (caller : ResolverEnv Other D A) (caller' : ResolverEnv Other D' B)
    (contexts : EnvRel DR AR saved saved') (d : D) (d' : D') (deps : DR d d') :
    RunRel SR AR (Family.capture saved queryFamily () d caller ())
      (Family.capture saved' queryFamily () d' caller' ()) :=
  full_resolver_lookup SR DR AR _ _ contexts.2 d d' deps

/-- Arbitrary families can observe all Other fields. Their full EnvRel contract
is passed to capture, not replaced by resolver agreement alone. -/
theorem capture_env_compatible {P : Type u} {I : P → Type v}
    (SR : S → T → Prop) (AR : A → B → Prop) (DR : D → D' → Prop) (VR : V → V' → Prop)
    (saved : ResolverEnv Other D V) (saved' : ResolverEnv Other D' V')
    (contexts : EnvRel DR VR saved saved')
    (m : Family P I (ResolverEnv Other D V) W S A)
    (n : Family P I (ResolverEnv Other D' V') W T B)
    (rel : FamilyRel SR AR (EnvRel DR VR) m n) :
    FamilyRel SR AR (EnvRel DR VR) (Family.capture saved m) (Family.capture saved' n) :=
  capture_compatible SR AR _ saved saved' contexts m n rel
end SmusniF03A1
