import SmusniF02.Fibres

/-! F02-v2 §§5–6. These are local ground Content observations, not the normative
Proposition domain. Beta is a separate supplied event index: it is neither a
source-origin coordinate nor an index of successful terminal outcomes. -/
namespace SmusniF02
universe u v w x y z q t

structure Content (P : Type u) (I : P → Type v) (E : Type w) (W : Type x)
    (S : Type y) (Beta : Type z) (Event : Type q) where
  run : Family P I E W S Unit
  event : ∀ p, I p → E → W → Beta → Option Event

/-- Partial definedness must agree, and present events must co-refer. -/
def PartialEq (coRef : V → V → Prop) : Option V → Option V → Prop
  | none, none => True
  | some a, some b => coRef a b
  | _, _ => False

namespace Content
variable {P : Type u} {I : P → Type v} {J : P → Type t}
variable {E : Type w} {W : Type x} {S : Type y} {Beta : Type z} {Event : Type q}

def ObsEq (coRef : Event → Event → Prop) (c d : Content P I E W S Beta Event) : Prop :=
  c.run = d.run ∧ ∀ p i e w b, PartialEq coRef (c.event p i e w b) (d.event p i e w b)

theorem obsEq_refl (coRef : Event → Event → Prop) (h : ∀ a, coRef a a)
    (c : Content P I E W S Beta Event) : ObsEq coRef c c := by
  refine ⟨rfl, ?_⟩
  intro p i e w b
  cases c.event p i e w b <;> simp [PartialEq, h]

theorem obsEq_symm (coRef : Event → Event → Prop)
    (symm : ∀ a b, coRef a b → coRef b a)
    {c d : Content P I E W S Beta Event} (h : ObsEq coRef c d) : ObsEq coRef d c := by
  refine ⟨h.1.symm, ?_⟩
  intro p i e w b
  have he := h.2 p i e w b
  cases hc : c.event p i e w b <;> cases hd : d.event p i e w b <;>
    simp_all [PartialEq]

theorem obsEq_trans (coRef : Event → Event → Prop)
    (trans : ∀ a b c, coRef a b → coRef b c → coRef a c)
    {c d f : Content P I E W S Beta Event}
    (h : ObsEq coRef c d) (k : ObsEq coRef d f) : ObsEq coRef c f := by
  refine ⟨h.1.trans k.1, ?_⟩
  intro p i e w b
  have he := h.2 p i e w b
  have ke := k.2 p i e w b
  cases hc : c.event p i e w b <;> cases hd : d.event p i e w b <;>
    cases hf : f.event p i e w b <;> simp_all [PartialEq]
  exact trans _ _ _ he ke

def pull (ρ : ∀ p, J p → I p) (c : Content P I E W S Beta Event) :
    Content P J E W S Beta Event where
  run := Family.pull ρ c.run
  event p j := c.event p (ρ p j)

def capture (e₀ : E) (c : Content P I E W S Beta Event) : Content P I E W S Beta Event where
  run := Family.capture e₀ c.run
  event p i _ w b := c.event p i e₀ w b

theorem capture_pull (ρ : ∀ p, J p → I p) (e₀ : E) (c : Content P I E W S Beta Event) :
    capture e₀ (pull ρ c) = pull ρ (capture e₀ c) := rfl

theorem capture_congr (coRef : Event → Event → Prop) (e₀ : E)
    {c d : Content P I E W S Beta Event} (h : ObsEq coRef c d) :
    ObsEq coRef (capture e₀ c) (capture e₀ d) :=
  ⟨congrArg (Family.capture e₀) h.1, fun p i _ w b => h.2 p i e₀ w b⟩

theorem pull_congr (coRef : Event → Event → Prop) (ρ : ∀ p, J p → I p)
    {c d : Content P I E W S Beta Event} (h : ObsEq coRef c d) :
    ObsEq coRef (pull ρ c) (pull ρ d) :=
  ⟨congrArg (Family.pull ρ) h.1, fun p j e w b => h.2 p (ρ p j) e w b⟩
end Content

section Payload
variable {P : Type u} {I : P → Type v} {Outer : P → Type t}
variable {E : Type w} {W : Type x} {S : Type y} {Beta : Type z} {Event : Type q} {R : Type _}

/-- The nucleus gets only the inherited outer coordinate and returned reference.
It does not receive K, the newly added outcome, or its reached state. -/
noncomputable def payload (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (nucleus : R → Content P Outer E W S Beta Event) :
    Content P I E W S Beta Event where
  run := Family.bind (reads phase K) (fun r => Family.pull outer (nucleus r).run)
  event p i e w b := match K p i with
    | .obtained r => (nucleus r).event p (outer p i) e w b
    | .empty | .unresolved => none

theorem payload_obtained_run (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i : I p) (r : R) (h : K p i = .obtained r) (e : E) (w : W) :
    (payload phase K outer nucleus).run p i e w = (nucleus r).run p (outer p i) e w := by
  simp [payload, Family.bind, reads, Family.pull, h]

theorem payload_obtained_event (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i : I p) (r : R) (h : K p i = .obtained r) (e : E) (w : W) (b : Beta) :
    (payload phase K outer nucleus).event p i e w b = (nucleus r).event p (outer p i) e w b := by
  simp [payload, h]

theorem payload_no_value_event (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i : I p) (h : ∀ r, K p i ≠ .obtained r) (e : E) (w : W) (b : Beta) :
    (payload phase K outer nucleus).event p i e w b = none := by
  cases hk : K p i with
  | obtained r => exact False.elim (h r hk)
  | empty => simp [payload, hk]
  | unresolved => simp [payload, hk]

theorem payload_empty_run (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i : I p) (h : K p i = .empty) (e : E) (w : W) (s : S) :
    (payload phase K outer nucleus).run p i e w s =
      NEFin.singleton (match phase with | .first => .dead s | .later => .undef s) := by
  cases phase <;> simp [payload, Family.bind, Family.pull, reads, read, readOutcome,
    h, Run.bind, Run.extend]

theorem payload_unresolved_run (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (nucleus : R → Content P Outer E W S Beta Event)
    (p : P) (i : I p) (h : K p i = .unresolved) (e : E) (w : W) (s : S) :
    (payload phase K outer nucleus).run p i e w s = NEFin.singleton (.undef s) := by
  cases phase <;> simp [payload, Family.bind, Family.pull, reads, read, readOutcome,
    h, Run.bind, Run.extend]

theorem payload_congr (coRef : Event → Event → Prop) (phase : ReadPhase)
    (K : ∀ p, I p → SourceResult R) (outer : ∀ p, I p → Outer p)
    (n n' : R → Content P Outer E W S Beta Event)
    (h : ∀ r, Content.ObsEq coRef (n r) (n' r)) :
    Content.ObsEq coRef (payload phase K outer n) (payload phase K outer n') := by
  constructor
  · change Family.bind _ (fun r => Family.pull outer (n r).run) =
      Family.bind _ (fun r => Family.pull outer (n' r).run)
    have hn : (fun r => Family.pull outer (n r).run) =
        (fun r => Family.pull outer (n' r).run) := by
      funext r; rw [(h r).1]
    rw [hn]
  · intro p i e w b
    cases hk : K p i with
    | obtained r => simpa only [payload, hk] using (h r).2 p (outer p i) e w b
    | empty => simp [payload, hk, PartialEq]
    | unresolved => simp [payload, hk, PartialEq]

theorem pull_payload {J : P → Type _} (ρ : ∀ p, J p → I p)
    (phase : ReadPhase) (K : ∀ p, I p → SourceResult R) (outer : ∀ p, I p → Outer p)
    (n : R → Content P Outer E W S Beta Event) :
    Content.pull ρ (payload phase K outer n) =
      payload phase (fun p j => K p (ρ p j)) (fun p j => outer p (ρ p j)) n := rfl

theorem capture_payload (e₀ : E) (phase : ReadPhase) (K : ∀ p, I p → SourceResult R)
    (outer : ∀ p, I p → Outer p) (n : R → Content P Outer E W S Beta Event) :
    Content.capture e₀ (payload phase K outer n) =
      payload phase K outer (fun r => Content.capture e₀ (n r)) := rfl
end Payload

/-- One lexical package, with no source-index field. It is not stored in ground S. -/
structure Act (C : Type u) where
  content : C

/-- A supplied fresh handle/token and unique Host selection identify this one tuple.
This is not a transcript resolver, allocator, or term-level inspector. -/
structure HostOccurrence (Handle : Type u) (Token : Type v) (C : Type w) where
  handle : Handle
  token : Token
  act : Act C
  captured : C

def makeHost (h : H) (token : T) (c : C) (cap : C → C) : HostOccurrence H T C :=
  ⟨h, token, ⟨c⟩, cap c⟩
theorem host_raw (h : H) (token : T) (c : C) (cap : C → C) :
    (makeHost h token c cap).act.content = c := rfl
theorem host_captured (h : H) (token : T) (c : C) (cap : C → C) :
    (makeHost h token c cap).captured = cap c := rfl
end SmusniF02
