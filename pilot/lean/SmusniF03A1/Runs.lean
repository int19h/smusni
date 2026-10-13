import SmusniF03A1.State

namespace SmusniF03A1
open SmusniF02

def RunRel (SR : S → T → Prop) (AR : A → B → Prop) (m : Run S A) (n : Run T B) : Prop :=
  ∀ s t, SR s t → FinRel (OutRel SR AR) (m s) (n t)

theorem pure_compatible (SR : S → T → Prop) (AR : A → B → Prop)
    (a : A) (b : B) (rel : AR a b) : RunRel SR AR (Run.pure a) (Run.pure b) := by
  intro s t hst
  exact finRel_singleton _ _ _ ⟨hst, rel⟩

theorem extend_compatible (SR : S → T → Prop) (AR : A → B → Prop) (BR : C → D → Prop)
    (k : A → Run S C) (l : B → Run T D)
    (body : ∀ a b, AR a b → RunRel SR BR (k a) (l b))
    (x : Outcome S A) (y : Outcome T B) (rel : OutRel SR AR x y) :
    FinRel (OutRel SR BR) (Run.extend k x) (Run.extend l y) := by
  cases x <;> cases y <;> simp only [OutRel] at rel
  · exact body _ _ rel.2 _ _ rel.1
  · exact finRel_singleton _ _ _ rel
  · exact finRel_singleton _ _ _ rel

theorem bind_compatible (SR : S → T → Prop) (AR : A → B → Prop) (BR : C → D → Prop)
    (m : Run S A) (n : Run T B) (k : A → Run S C) (l : B → Run T D)
    (input : RunRel SR AR m n) (body : ∀ a b, AR a b → RunRel SR BR (k a) (l b)) :
    RunRel SR BR (Run.bind m k) (Run.bind n l) := by
  intro s t hst
  exact finRel_unionMap _ _ _ _ _ _ (input s t hst) (extend_compatible SR AR BR k l body)

abbrev RespectingRun (SR : S → S → Prop) (AR : A → A → Prop) :=
  {m : Run S A // RunRel SR AR m m}

/-- Choose a preimage of the entire quotient state, run the arbitrary supplied
computation there, and map all terminal alternatives. The input carries respect. -/
noncomputable def descend (fs : S → T) (onto : Onto fs) (fa : A → B)
    {SR : S → S → Prop} {AR : A → A → Prop}
    (m : RespectingRun SR AR) : Run T B :=
  fun t => mapResults (mapOutcome fs fa) (m.val (onto t).choose)

theorem descend_at (fs : S → T) (onto : Onto fs) (fa : A → B)
    (ks : Kernel fs SR) (ka : Kernel fa AR) (m : RespectingRun SR AR) (s : S) :
    descend fs onto fa m (fs s) = mapResults (mapOutcome fs fa) (m.val s) := by
  apply (finite_kernel _ _ (outcome_kernel fs fa SR AR ks ka) _ _).mpr
  exact m.property _ s ((ks _ s).mp (onto (fs s)).choose_spec)

theorem run_kernel (fs : S → T) (onto : Onto fs) (fa : A → B)
    (ks : Kernel fs SR) (ka : Kernel fa AR) :
    Kernel (descend fs onto fa : RespectingRun SR AR → Run T B)
      (fun m n => RunRel SR AR m.val n.val) := by
  intro m n
  constructor
  · intro eq s t hst
    apply (finite_kernel _ _ (outcome_kernel fs fa SR AR ks ka) _ _).mp
    calc
      mapResults (mapOutcome fs fa) (m.val s) = descend fs onto fa m (fs s) :=
        (descend_at fs onto fa ks ka m s).symm
      _ = descend fs onto fa n (fs t) := by rw [eq, (ks s t).mpr hst]
      _ = mapResults (mapOutcome fs fa) (n.val t) := descend_at fs onto fa ks ka n t
  · intro rel
    funext t
    obtain ⟨s, rfl⟩ := onto t
    rw [descend_at fs onto fa ks ka, descend_at fs onto fa ks ka]
    exact (finite_kernel _ _ (outcome_kernel fs fa SR AR ks ka) _ _).mpr
      (rel s s ((ks s s).mp rfl))

/-- Coverage is algebraic, not admission of unrestricted functions into a Henkin model. -/
theorem descend_onto (fs : S → T) (os : Onto fs) (fa : A → B) (oa : Onto fa)
    (ks : Kernel fs SR) (ka : Kernel fa AR) :
    Onto (descend fs os fa : RespectingRun SR AR → Run T B) := by
  classical
  intro n
  have outputs := finite_onto (mapOutcome fs fa) (outcome_onto fs fa os oa)
  let m : Run S A := fun s => (outputs (n (fs s))).choose
  have respects : RunRel SR AR m m := by
    intro s t hst
    apply (finite_kernel _ _ (outcome_kernel fs fa SR AR ks ka) _ _).mp
    change mapResults _ (outputs (n (fs s))).choose = mapResults _ (outputs (n (fs t))).choose
    rw [(outputs (n (fs s))).choose_spec, (outputs (n (fs t))).choose_spec, (ks s t).mpr hst]
  refine ⟨⟨m, respects⟩, ?_⟩
  funext t
  obtain ⟨s, rfl⟩ := os t
  rw [descend_at fs os fa ks ka]
  exact (outputs (n (fs s))).choose_spec

noncomputable def qRun (R : Setoid P) (AR : Setoid A)
    (m : RespectingRun (StateRel (N := N) (H := H) (ValueRel (G := G) R) (AnchorRel (G := GA) R)) AR.r) :
    Run (QuotientState N G GA P H R) (Quotient AR) :=
  descend (qState R) (qState_onto R) (Quotient.mk AR) m

theorem qRun_at (R : Setoid P) (AR : Setoid A)
    (m : RespectingRun (StateRel (N := N) (H := H) (ValueRel (G := G) R) (AnchorRel (G := GA) R)) AR.r)
    (s : RawState N G GA P H) :
    qRun R AR m (qState R s) = mapResults (qOutcome R AR) (m.val s) :=
  descend_at _ (qState_onto R) _ (qState_kernel R) (quotient_kernel AR) m s

theorem qRun_kernel (R : Setoid P) (AR : Setoid A) :
    Kernel (qRun (N := N) (G := G) (GA := GA) (H := H) R AR)
      (fun m n => RunRel (StateRel (ValueRel R) (AnchorRel R)) AR.r m.val n.val) :=
  run_kernel _ (qState_onto R) _ (qState_kernel R) (quotient_kernel AR)

theorem qRun_onto (R : Setoid P) (AR : Setoid A) :
    Onto (qRun (N := N) (G := G) (GA := GA) (H := H) R AR) :=
  descend_onto _ (qState_onto R) _ (quotient_onto AR) (qState_kernel R) (quotient_kernel AR)

theorem descend_bind_at (fs : S → T) (onto : Onto fs) (fb : B → C)
    (ks : Kernel fs SR) (kb : Kernel fb BR) (m : RespectingRun SR (AR : A → A → Prop)) (k : A → Run S B)
    (body : ∀ a b, AR a b → RunRel SR BR (k a) (k b)) (s : S) :
    descend fs onto fb ⟨Run.bind m.val k, bind_compatible SR AR BR _ _ k k m.property body⟩ (fs s) =
      mapResults (mapOutcome fs fb) (Run.bind m.val k s) :=
  descend_at fs onto fb ks kb _ s
end SmusniF03A1
