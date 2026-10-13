import SmusniF02.Host

/-! The exact finite experimental grammar, separate from the full pilot AST.
Worlds, lexical interpretations, and context functions are not fields of Code. -/
namespace SmusniPositive
universe u v

structure Signature where
  Ground : Type u
  Name : Type u
  Key : Type u
  Predicate : Type u
  siteArity : Key → Nat
  predicateArity : Predicate → Nat

inductive GroundTerm (G : Type u) (m : Nat) where
  | var : Fin m → GroundTerm G m
  | literal : G → GroundTerm G m

def GroundTerm.eval (rho : Fin m → G) : GroundTerm G m → G
  | .var x => rho x
  | .literal g => g

def GroundTerm.rename (f : Fin m → Fin m') : GroundTerm G m → GroundTerm G m'
  | .var x => .var (f x)
  | .literal g => .literal g

theorem GroundTerm.eval_rename (f : Fin m → Fin m') (rho : Fin m' → G) (t : GroundTerm G m) :
    (t.rename f).eval rho = t.eval (fun x => rho (f x)) := by cases t <;> rfl

/-- Holds' two argument shapes are explicit constructors. `PropTerm` below
provides the paper's var/reify argument interface without additional syntax. -/
inductive Term (sig : Signature.{u}) : Nat → Nat → Type u where
  | top {m n} : Term sig m n
  | bot {m n} : Term sig m n
  | atom {m n} (a : sig.Predicate) (args : Fin (sig.predicateArity a) → GroundTerm sig.Ground m) : Term sig m n
  | neg {m n} : Term sig m n → Term sig m n
  | holdsVar {m n} : Fin n → Term sig m n
  | holdsReify {m n} : Term sig m n → Term sig m n
  | ctx {m n} (k : sig.Key) (args : Fin (sig.siteArity k) → GroundTerm sig.Ground m)
      (body : Term sig m (n+1)) : Term sig m n
  | read {m n} (name : sig.Name) (body : Term sig m (n+1)) : Term sig m n
  | allG {m n} : Term sig (m+1) n → Term sig m n
  | allP {m n} : Term sig m (n+1) → Term sig m n

inductive PropTerm (sig : Signature.{u}) (m n : Nat) : Type u where
  | var : Fin n → PropTerm sig m n
  | reify : Term sig m n → PropTerm sig m n

def holds : PropTerm sig m n → Term sig m n
  | .var x => .holdsVar x
  | .reify t => .holdsReify t

inductive Code (sig : Signature.{u}) : Type u where
  | mk {m n : Nat} (term : Term sig m n) (ground : Fin m → sig.Ground) (prop : Fin n → Code sig) : Code sig

def extend (rho : Fin n → A) (a : A) : Fin (n+1) → A := Fin.cases a rho
@[simp] theorem extend_zero (rho : Fin n → A) (a : A) : extend rho a 0 = a := rfl
@[simp] theorem extend_succ (rho : Fin n → A) (a : A) (i : Fin n) : extend rho a i.succ = rho i := rfl
def emptyEnv : Fin 0 → A := Fin.elim0

def evalProp (p : PropTerm sig m n) (g : Fin m → sig.Ground) (r : Fin n → Code sig) : Code sig :=
  match p with | .var x => r x | .reify t => .mk t g r

def evalGround (args : Fin arity → GroundTerm G m) (rho : Fin m → G) : Fin arity → G :=
  fun i => (args i).eval rho

def liftIndex (f : Fin n → Fin n') : Fin (n+1) → Fin (n'+1) := Fin.cases 0 (fun i => (f i).succ)

def Term.rename {sig : Signature.{u}} {m n m' n' : Nat} (fg : Fin m → Fin m') (fp : Fin n → Fin n') :
    Term sig m n → Term sig m' n'
  | .top => .top
  | .bot => .bot
  | .atom a args => .atom a (fun i => (args i).rename fg)
  | .neg t => .neg (t.rename fg fp)
  | .holdsVar x => .holdsVar (fp x)
  | .holdsReify t => .holdsReify (t.rename fg fp)
  | .ctx k args body => .ctx k (fun i => (args i).rename fg) (body.rename fg (liftIndex fp))
  | .read name body => .read name (body.rename fg (liftIndex fp))
  | .allG body => .allG (body.rename (liftIndex fg) fp)
  | .allP body => .allP (body.rename fg (liftIndex fp))

def Term.weakenG (t : Term sig m n) : Term sig (m+1) n := t.rename Fin.succ id
def Term.weakenP (t : Term sig m n) : Term sig m (n+1) := t.rename id Fin.succ

theorem extend_liftIndex (rho : Fin n' → A) (a : A) (f : Fin n → Fin n') (i : Fin (n+1)) :
    extend rho a (liftIndex f i) = extend (fun j => rho (f j)) a i := by
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem ground_weaken_preserves (t : GroundTerm G m) (rho : Fin m → G) (g : G) :
    (t.rename Fin.succ).eval (extend rho g) = t.eval rho := by
  cases t <;> rfl

def closed (t : Term sig 0 0) : Code sig := .mk t emptyEnv emptyEnv
def topCode (sig : Signature.{u}) : Code sig := closed .top
def botCode (sig : Signature.{u}) : Code sig := closed .bot
def negCode (c : Code sig) : Code sig := .mk (.neg (.holdsVar 0)) emptyEnv (extend emptyEnv c)
def holdsCode (c : Code sig) : Code sig := .mk (.holdsVar 0) emptyEnv (extend emptyEnv c)

structure Model (sig : Signature.{u}) (W : Type v) where
  lexical : (a : sig.Predicate) → W → (Fin (sig.predicateArity a) → sig.Ground) → Bool

abbrev RawState (sig : Signature.{u}) := SmusniF02.HostState sig.Name (Code sig) Unit Unit
abbrev Context (sig : Signature.{u}) := (k : sig.Key) → (Fin (sig.siteArity k) → sig.Ground) → Option (Code sig)

structure Input (sig : Signature.{u}) (W : Type v) where
  context : Context sig
  world : W
  state : RawState sig

def initial (sig : Signature.{u}) : RawState sig := ⟨fun _ => none, [], [], .t, .t⟩
def absentContext (sig : Signature.{u}) : Context sig := fun _ _ => none
end SmusniPositive
