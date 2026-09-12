import SmusniF02.Content

/-! F02-A1 correction: F02-v2 §§4–5 requires inheritance along the source parent,
not an arbitrary map out of the newly added terminal fibre. The generic `payload`
remains available but is not the advertised source-specific construction. -/
namespace SmusniF02
universe u v w x y z q t r

section SourcePayload
variable {P : Type u} {B : P → Type v} {Outer : P → Type t}
variable {E : Type w} {W : Type x} {S : Type y} {Beta : Type z} {Event : Type q} {R : Type r}

/-- Source-bound payload: inherited parameters are supplied on B, before the new
terminal outcome is added. K and parent factorization are constructed here.
No saved-state map or desired invariance law is supplied by the client. -/
noncomputable def sourcePayload (phase : ReadPhase) (source : ∀ p, B p → Terminal S R)
    (inherited : ∀ p, B p → Outer p) (nucleus : R → Content P Outer E W S Beta Event) :
    Content P (Origin source) E W S Beta Event :=
  payload phase (fun _ i => i.result) (fun p i => inherited p i.parent) nucleus

theorem sourcePayload_run_invariant (phase : ReadPhase) (source : ∀ p, B p → Terminal S R)
    (inherited : ∀ p, B p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i j : Origin source p) (hp : i.parent = j.parent) (hk : i.result = j.result)
    (e : E) (w : W) :
    (sourcePayload phase source inherited nucleus).run p i e w =
      (sourcePayload phase source inherited nucleus).run p j e w := by
  change Run.bind (read phase i.result) (fun r => (nucleus r).run p (inherited p i.parent) e w) =
    Run.bind (read phase j.result) (fun r => (nucleus r).run p (inherited p j.parent) e w)
  rw [hp, hk]

theorem sourcePayload_event_invariant (phase : ReadPhase) (source : ∀ p, B p → Terminal S R)
    (inherited : ∀ p, B p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i j : Origin source p) (hp : i.parent = j.parent) (hk : i.result = j.result)
    (e : E) (w : W) (beta : Beta) :
    (sourcePayload phase source inherited nucleus).event p i e w beta =
      (sourcePayload phase source inherited nucleus).event p j e w beta := by
  change (match i.result with
    | .obtained r => (nucleus r).event p (inherited p i.parent) e w beta
    | .empty | .unresolved => none) = _
  rw [hp, hk]
  rfl

theorem sourcePayload_obtained_run (phase : ReadPhase) (source : ∀ p, B p → Terminal S R)
    (inherited : ∀ p, B p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i : Origin source p) (r : R) (h : i.result = .obtained r) (e : E) (w : W) :
    (sourcePayload phase source inherited nucleus).run p i e w =
      (nucleus r).run p (inherited p i.parent) e w :=
  payload_obtained_run phase _ _ nucleus p i r h e w

theorem sourcePayload_congr (coRef : Event → Event → Prop) (phase : ReadPhase)
    (source : ∀ p, B p → Terminal S R) (inherited : ∀ p, B p → Outer p)
    (n n' : R → Content P Outer E W S Beta Event)
    (h : ∀ r, Content.ObsEq coRef (n r) (n' r)) :
    Content.ObsEq coRef (sourcePayload phase source inherited n)
      (sourcePayload phase source inherited n') :=
  payload_congr coRef phase _ _ n n' h

theorem capture_sourcePayload (e₀ : E) (phase : ReadPhase) (source : ∀ p, B p → Terminal S R)
    (inherited : ∀ p, B p → Outer p) (n : R → Content P Outer E W S Beta Event) :
    Content.capture e₀ (sourcePayload phase source inherited n) =
      sourcePayload phase source inherited (fun r => Content.capture e₀ (n r)) := rfl
end SourcePayload
end SmusniF02
