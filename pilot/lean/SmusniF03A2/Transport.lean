import SmusniF03A2.Joint

namespace SmusniF03A2
open SmusniF02 SmusniF03A1
universe u v w x y z q

variable {P : Type u} {I : P → Type v} {E : Type w} {W : Type x}
variable {S : Type y} {Beta : Type z} {Event : Type q}

def pullContent {J : P → Type _} (rho : ∀ p, J p → I p)
    (c : RespectingContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event) SR) :
    RespectingContent (P := P) (I := J) (E := E) (W := W) (Beta := Beta) (Event := Event) SR :=
  ⟨Content.pull rho c.val, fun p j e w => c.property p (rho p j) e w⟩

def captureContent (saved : E)
    (c : RespectingContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event) SR) :
    RespectingContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event) SR :=
  ⟨Content.capture saved c.val, fun p i _ w => c.property p i saved w⟩

theorem descendContent_pull {J : P → Type _} (fs : S → T) (onto : Onto fs) (ER : Setoid Event)
    {SR : S → S → Prop} (rho : ∀ p, J p → I p)
    (c : RespectingContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event) SR) :
    descendContent fs onto ER (pullContent rho c) = Content.pull rho (descendContent fs onto ER c) := rfl

theorem descendContent_capture (fs : S → T) (onto : Onto fs) (ER : Setoid Event)
    {SR : S → S → Prop} (saved : E)
    (c : RespectingContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event) SR) :
    descendContent fs onto ER (captureContent saved c) = Content.capture saved (descendContent fs onto ER c) := rfl

theorem joint_pull {J : P → Type _} (SR : S → S → Prop) (ER : Setoid Event)
    (rho : ∀ p, J p → I p) (c d : Content P I E W S Beta Event) (rel : JointRel SR ER c d) :
    JointRel SR ER (Content.pull rho c) (Content.pull rho d) :=
  ⟨fun p j e w => rel.1 p (rho p j) e w, fun p j e w beta => rel.2 p (rho p j) e w beta⟩

/-- Different saved contexts require respect for the entire supplied context
relation, in both runs and events. Run agreement alone supplies no event law. -/
def ContextJointRel (SR : S → S → Prop) (ER : Setoid Event) (CR : E → E → Prop)
    (c d : Content P I E W S Beta Event) : Prop :=
  FamilyRel SR Eq CR c.run d.run ∧
  ∀ p i e e' w beta, CR e e' → PartialEq ER.r (c.event p i e w beta) (d.event p i e' w beta)

theorem joint_capture_related (SR : S → S → Prop) (ER : Setoid Event) (CR : E → E → Prop)
    (saved saved' : E) (contexts : CR saved saved') (c d : Content P I E W S Beta Event)
    (rel : ContextJointRel SR ER CR c d) :
    JointRel SR ER (Content.capture saved c) (Content.capture saved' d) :=
  ⟨fun p i _ w => rel.1 p i saved saved' w contexts,
   fun p i _ w beta => rel.2 p i saved saved' w beta contexts⟩

theorem joint_capture_fixed (SR : S → S → Prop) (ER : Setoid Event) (saved : E)
    (c d : Content P I E W S Beta Event) (rel : JointRel SR ER c d) :
    JointRel SR ER (Content.capture saved c) (Content.capture saved d) :=
  ⟨fun p i _ w => rel.1 p i saved w, fun p i _ w beta => rel.2 p i saved w beta⟩

theorem captured_quotient_equal (fs : S → T) (onto : Onto fs) (ER : Setoid Event)
    (ks : Kernel fs SR) (CR : E → E → Prop) (saved saved' : E) (contexts : CR saved saved')
    (c d : RespectingContent (P := P) (I := I) (E := E) (W := W) (Beta := Beta) (Event := Event) SR)
    (rel : ContextJointRel SR ER CR c.val d.val) :
    descendContent fs onto ER (captureContent saved c) = descendContent fs onto ER (captureContent saved' d) :=
  (joint_kernel fs onto ER ks _ _).mpr (joint_capture_related SR ER CR saved saved' contexts _ _ rel)

/-- Reuse A1's full-domain resolver relation, including all remaining fields. -/
theorem joint_capture_full_env {Other : Type _} {D : Type _} {V : Type _}
    (SR : S → S → Prop) (ER : Setoid Event) (DR : D → D → Prop) (VR : V → V → Prop)
    (saved saved' : ResolverEnv Other D V) (contexts : EnvRel DR VR saved saved')
    (c d : Content P I (ResolverEnv Other D V) W S Beta Event)
    (rel : ContextJointRel SR ER (EnvRel DR VR) c d) :
    JointRel SR ER (Content.capture saved c) (Content.capture saved' d) :=
  joint_capture_related SR ER (EnvRel DR VR) saved saved' contexts c d rel
end SmusniF03A2
