import SmusniF03A1.Families

namespace SmusniF03A2
open SmusniF02 SmusniF03A1
universe u v w x y z q

def qEvent (ER : Setoid Event) (event : Option Event) : Option (Quotient ER) :=
  event.map (Quotient.mk ER)

theorem event_kernel (ER : Setoid Event) : Kernel (qEvent ER) (PartialEq ER.r) := by
  intro a b
  cases a <;> cases b <;> simp [qEvent, PartialEq, quotient_kernel ER]

theorem event_onto (ER : Setoid Event) : Onto (qEvent ER) := option_onto _ (quotient_onto ER)

theorem partial_refl (ER : Setoid Event) (event : Option Event) : PartialEq ER.r event event :=
  (event_kernel ER event event).mp rfl

section Content
variable {P : Type u} {I : P → Type v} {E : Type w} {W : Type x}
variable {S : Type y} {Beta : Type z} {Event : Type q}

def ContentRespect (SR : S → S → Prop) (c : Content P I E W S Beta Event) : Prop :=
  ∀ p i e w, RunRel SR Eq (c.run p i e w) (c.run p i e w)

abbrev RespectingContent (SR : S → S → Prop) :=
  {c : Content P I E W S Beta Event // ContentRespect SR c}

def JointRel (SR : S → S → Prop) (ER : Setoid Event)
    (c d : Content P I E W S Beta Event) : Prop :=
  (∀ p i e w, RunRel SR Eq (c.run p i e w) (d.run p i e w)) ∧
  (∀ p i e w beta, PartialEq ER.r (c.event p i e w beta) (d.event p i e w beta))

@[ext] theorem content_ext {c d : Content P I E W S Beta Event}
    (run : c.run = d.run) (event : c.event = d.event) : c = d := by
  cases c; cases d; simp_all

/-- Runs use A1 descent with the identity Unit map. Events use a separate index
and the supplied co-reference quotient. No successful-run index is invented. -/
noncomputable def descendContent (fs : S → T) (onto : Onto fs) (ER : Setoid Event)
    {SR : S → S → Prop} (c : RespectingContent (P := P) (I := I) (E := E) (W := W)
      (Beta := Beta) (Event := Event) SR) : Content P I E W T Beta (Quotient ER) where
  run p i e w := descend fs onto id ⟨c.val.run p i e w, c.property p i e w⟩
  event p i e w beta := qEvent ER (c.val.event p i e w beta)

theorem descendContent_run_at (fs : S → T) (onto : Onto fs) (ER : Setoid Event)
    (ks : Kernel fs SR) (c : RespectingContent (P := P) (I := I) (E := E) (W := W)
      (Beta := Beta) (Event := Event) SR) (p : P) (i : I p) (e : E) (w : W) (s : S) :
    (descendContent fs onto ER c).run p i e w (fs s) =
      mapResults (mapOutcome fs id) (c.val.run p i e w s) :=
  descend_at fs onto id ks (fun _ _ => Iff.rfl) _ s

theorem descendContent_event_at (fs : S → T) (onto : Onto fs) (ER : Setoid Event)
    {SR : S → S → Prop} (c : RespectingContent (P := P) (I := I) (E := E) (W := W)
      (Beta := Beta) (Event := Event) SR) (p : P) (i : I p) (e : E) (w : W) (beta : Beta) :
    (descendContent fs onto ER c).event p i e w beta = qEvent ER (c.val.event p i e w beta) := rfl

theorem joint_kernel (fs : S → T) (onto : Onto fs) (ER : Setoid Event) (ks : Kernel fs SR) :
    Kernel (descendContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (SR := SR) fs onto ER)
      (fun c d => JointRel SR ER c.val d.val) := by
  intro c d
  constructor
  · intro eq
    constructor
    · intro p i e w
      exact (run_kernel fs onto id ks (fun _ _ => Iff.rfl)
        ⟨c.val.run p i e w, c.property p i e w⟩ ⟨d.val.run p i e w, d.property p i e w⟩).mp
        (congrArg (fun x : Content P I E W T Beta (Quotient ER) => x.run p i e w) eq)
    · intro p i e w beta
      apply (event_kernel ER _ _).mp
      exact congrArg (fun x : Content P I E W T Beta (Quotient ER) => x.event p i e w beta) eq
  · intro rel
    apply content_ext
    · funext p i e w
      exact (run_kernel fs onto id ks (fun _ _ => Iff.rfl)
        ⟨c.val.run p i e w, c.property p i e w⟩ ⟨d.val.run p i e w, d.property p i e w⟩).mpr (rel.1 p i e w)
    · funext p i e w beta
      exact (event_kernel ER _ _).mpr (rel.2 p i e w beta)

end Content

section Tagged
variable {Profile : Type u} {I : Profile → Type v} {E : Type w} {W : Type x}
variable {Beta : Type z} {Event : Type q} {N : Type _} {G : Type _}
variable {GA : Type _} {Rep : Type _} {H : Type _}

noncomputable def qContent (R : Setoid Rep) (ER : Setoid Event)
    (c : RespectingContent (P := Profile) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event)
      (StateRel (N := N) (H := H) (ValueRel (G := G) R) (AnchorRel (G := GA) R))) :
    Content Profile I E W (QuotientState N G GA Rep H R) Beta (Quotient ER) :=
  descendContent (qState R) (qState_onto R) ER c

theorem qContent_kernel (R : Setoid Rep) (ER : Setoid Event) :
    Kernel (qContent (Profile := Profile) (I := I) (E := E) (W := W) (Beta := Beta)
      (N := N) (G := G) (GA := GA) (H := H) R ER)
      (fun c d => JointRel (StateRel (ValueRel R) (AnchorRel R)) ER c.val d.val) :=
  joint_kernel _ (qState_onto R) ER (qState_kernel R)
end Tagged
end SmusniF03A2
