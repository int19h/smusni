import Smusni97.Common

/-! A finite typed defining language. It has no arbitrary function-to-definition
constructor. The observer does not import the opaque candidate. -/
namespace Smusni97.Explicit
open SmusniF02

inductive Ty where | state | mask | status deriving DecidableEq
def Ty.Value : Ty → Type
  | .state => State
  | .mask => Mask
  | .status => Truth

structure Env where
  entry : State
  reached : State
  eligible : Mask
  occurrence : Nat
  payload : Truth

inductive Expr : Ty → Type where
  | entry : Expr .state
  | reached : Expr .state
  | eligible : Expr .mask
  | support : Expr .state → Expr .mask
  | union : Expr .mask → Expr .mask → Expr .mask
  | prune : Expr .mask → Expr .state → Expr .state
  | payload : Expr .status
  | suffix : Expr .state → Expr .state → Expr .status
  | record : Expr .status → Expr .status → Expr .state → Expr .state
  deriving DecidableEq

def Expr.eval : Expr k → Env → k.Value
  | .entry, e => e.entry
  | .reached, e => e.reached
  | .eligible, e => e.eligible
  | .support s, e => Smusni97.support (s.eval e)
  | .union a b, e => unionMask (a.eval e) (b.eval e)
  | .prune mask s, e => Smusni97.prune (mask.eval e) (s.eval e)
  | .payload, e => e.payload
  | .suffix a b, e => suffixStatus (a.eval e) (b.eval e)
  | .record tau sigma s, e => Smusni97.record e.occurrence (tau.eval e) (sigma.eval e) (s.eval e)

/-- `arg` exists only in the Live arm. Dead/Undef cannot manufacture its value. -/
inductive ValueExpr (A : Type) : Bool → Type → Type 1 where
  | arg : ValueExpr A true A
  | unit : ValueExpr A has Unit
  | occurrence : ValueExpr A has Nat

def Arg (has : Bool) (A : Type) : Type := if has then A else Unit
def ValueExpr.eval : ValueExpr A has B → Arg has A → Env → B
  | .arg, a, _ => a
  | .unit, _, _ => ()
  | .occurrence, _, e => e.occurrence

inductive Arm (has : Bool) (A B : Type) where
  | live : Expr .state → ValueExpr A has B → Arm has A B
  | dead : Expr .state → Arm has A B
  | undef : Expr .state → Arm has A B

def Arm.eval : Arm has A B → Arg has A → Env → Out B
  | .live s v, a, e => .live (s.eval e) (v.eval a e)
  | .dead s, _, e => .dead (s.eval e)
  | .undef s, _, e => .undef (s.eval e)

structure RunDef (A B : Type) where
  live : Arm true A B
  dead : Arm false A B
  undef : Arm false A B

def observeOut (d : RunDef A B) (entry : State) (eligible : Mask) (h : Nat) (z : Out A) : Out B :=
  let e : Env := ⟨entry, z.state, eligible, h, z.truth⟩
  match z with
  | .live _ a => d.live.eval a e
  | .dead _ => d.dead.eval () e
  | .undef _ => d.undef.eval () e

def localState : Expr .state := .prune (.support .entry) .reached
def hostState : Expr .state :=
  .record .payload (.suffix .entry .reached) (.prune (.union (.support .entry) .eligible) .reached)
def localDef : RunDef A A := ⟨.live localState .arg, .dead localState, .undef localState⟩
def negDef : RunDef Unit Unit := ⟨.dead localState, .live localState .unit, .undef localState⟩
def hostDef : RunDef Unit Nat :=
  ⟨.live hostState .occurrence, .live hostState .occurrence, .live hostState .occurrence⟩
def scrubDef : RunDef A A := ⟨.live .entry .arg, .dead .entry, .undef .entry⟩
def scrubHostDef : RunDef Unit Nat :=
  ⟨.live .entry .occurrence, .live .entry .occurrence, .live .entry .occurrence⟩

/-- Fixed reviewed-body export policy, not inferred capability admission.
The dependent indices enforce the input/output type of each named export. -/
def LocalExport (d : RunDef A A) : Prop := d = localDef
def HostExport (d : RunDef Unit Nat) : Prop := d = hostDef
def NegativeExport (d : RunDef Unit Unit) : Prop := d = negDef

theorem scrub_not_exported : ¬ LocalExport (scrubDef : RunDef A A) := by
  intro h
  have hs := congrArg (fun d : RunDef A A => d.dead) h
  simp [scrubDef, localDef, localState] at hs

theorem scrub_host_not_exported : ¬ HostExport scrubHostDef := by
  intro h
  have hs := congrArg (fun d : RunDef Unit Nat => d.dead) h
  simp [scrubHostDef, hostDef, hostState] at hs

def localOut (s : State) (z : Out A) : Out A := observeOut localDef s (fun _ => false) 0 z
def hostOut (s : State) (eligible : Mask) (h : Nat) (z : Out Unit) : Out Nat :=
  observeOut hostDef s eligible h z
def negOut (s : State) (z : Out Unit) : Out Unit := observeOut negDef s (fun _ => false) 0 z

def finish (entry : State) (eligible : Mask) (h : Nat) (use : HostUse entry h) : Out Nat :=
  hostOut entry eligible h use.terminal

noncomputable def applyDef (d : RunDef A B) (m : Run A) (eligible : Mask) (h : Nat) : Run B :=
  fun s => mapResults (observeOut d s eligible h) (m s)

noncomputable def exportLocal (d : RunDef A A) (_ : LocalExport d) (m : Run A) : Run A :=
  applyDef d m (fun _ => false) 0
noncomputable def exportHost (d : RunDef Unit Nat) (_ : HostExport d)
    (m : Run Unit) (eligible : Mask) (h : Nat) : Run Nat := applyDef d m eligible h
def exportNegative (d : RunDef Unit Unit) (_ : NegativeExport d) (test : RefTest) : Run Unit :=
  fun s => NEFin.singleton (observeOut d s (fun _ => false) 0 (test.observe s))

/-- Independent case routing. Shared finite union, not the opaque interpreter. -/
def route (k : A → Run B) : Out A → Results B
  | .live s a => k a s
  | .dead s => NEFin.singleton (.dead s)
  | .undef s => NEFin.singleton (.undef s)
noncomputable def sequence (m : Run A) (k : A → Run B) : Run B :=
  fun s => (m s).unionMap (route k)

inductive Cat where | ref | perf
inductive Term : Cat → Type → Type 1 where
  | pure (a : A) : Term c A
  | test (t : RefTest) : Term .ref Unit
  | emit (side : ClosedSide Nat) : Term .ref Unit
  | bind : Term c A → (A → Term c B) → Term c B
  | local : Term .ref A → Term .ref A
  | negative : RefTest → Term .ref Unit
  | host : Term .ref Unit → Mask → Nat → Term .perf Nat
  | lift : Term .ref A → Term .perf A
  | body : Term .ref A → Term .ref A

noncomputable def observe : Term c A → Run A
  | .pure a => fun s => NEFin.singleton (.live s a)
  | .test t => fun s => NEFin.singleton (t.observe s)
  | .emit side => fun s => NEFin.singleton (.live {s with sides := s.sides ++ [side]} ())
  | .bind m k => sequence (observe m) (fun a => observe (k a))
  | .local m => exportLocal localDef rfl (observe m)
  | .negative t => exportNegative negDef rfl t
  | .host m eligible h => exportHost hostDef rfl (observe m) eligible h
  | .lift m => observe m
  | .body m => exportLocal localDef rfl (observe m)

theorem local_value (entry : State) (z : Out A) : value (localOut entry z) = value z := by
  cases z <;> rfl
theorem local_truth (entry : State) (z : Out A) : (localOut entry z).truth = z.truth := by
  cases z <;> rfl
theorem local_sides (entry : State) (z : Out A) : (localOut entry z).state.sides = z.state.sides := by
  cases z <;> rfl
theorem local_obligations (entry : State) (z : Out A) :
    (localOut entry z).state.obligations = z.state.obligations := by cases z <;> rfl
theorem local_incoming (entry : State) (z : Out A) (n v : Nat)
    (old : entry.slots n = some v) (retained : z.state.slots n = some v) :
    (localOut entry z).state.slots n = some v := by
  cases z <;> simpa [localOut, observeOut, localDef, localState, Arm.eval, Expr.eval,
    prune, support, old, Outcome.state] using retained
theorem local_fresh (entry : State) (z : Out A) (n : Nat) (fresh : entry.slots n = none) :
    (localOut entry z).state.slots n = none := by
  cases z <;> simp [localOut, observeOut, localDef, localState, Arm.eval, Expr.eval,
    prune, support, fresh, Outcome.state]

theorem host_prefix (entry : State) (z : Out Unit) (eligible : Mask) (h n : Nat)
    (kept : support entry n = true ∨ eligible n = true) :
    (hostOut entry eligible h z).state.slots n = z.state.slots n := by
  cases z <;> rcases kept with kept | kept <;>
    simp [hostOut, observeOut, hostDef, hostState, Arm.eval, Expr.eval, Outcome.state,
      record, prune, unionMask, kept]
theorem host_returns_dead (entry s : State) (eligible : Mask) (h : Nat) :
    value (hostOut entry eligible h (.dead s)) = some h := rfl
theorem host_returns_undef (entry s : State) (eligible : Mask) (h : Nat) :
    value (hostOut entry eligible h (.undef s)) = some h := rfl
theorem host_sides_once (entry : State) (z : Out Unit) (eligible : Mask) (h : Nat) :
    (hostOut entry eligible h z).state.sides = z.state.sides := by cases z <;> rfl
theorem host_record (entry : State) (z : Out Unit) (eligible : Mask) (h : Nat) :
    (hostOut entry eligible h z).state.hosts =
      z.state.hosts ++ [⟨h, z.truth, suffixStatus entry z.state⟩] := by cases z <;> rfl

theorem route_equation (k : A → Run B) : route k = SmusniF02.Run.extend k := by
  funext z
  cases z <;> rfl
theorem sequence_equation (m : Run A) (k : A → Run B) :
    sequence m k = SmusniF02.Run.bind m k := by
  funext s
  simp only [sequence, SmusniF02.Run.bind, route_equation]
theorem bind_unit_left (a : A) (k : A → Term c B) :
    observe (.bind (.pure a) k) = observe (k a) := by
  simp only [observe, sequence_equation]
  exact SmusniF02.Run.pure_bind _ _
theorem bind_unit_right (m : Term c A) : observe (.bind m Term.pure) = observe m := by
  simp only [observe, sequence_equation]
  exact SmusniF02.Run.bind_pure _
theorem bind_assoc (m : Term c A) (k : A → Term c B) (l : B → Term c C) :
    observe (.bind (.bind m k) l) = observe (.bind m (fun a => .bind (k a) l)) := by
  simp only [observe, sequence_equation]
  exact SmusniF02.Run.bind_assoc _ _ _
theorem body_leg_same (m : Term .ref A) : observe (.body m) = observe (.local m) := rfl
end Smusni97.Explicit
