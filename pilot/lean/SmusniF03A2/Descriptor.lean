import SmusniF03A2.Transport

/-! The released diagnostic instance, not the arbitrary-R implementation path.
Its state slots and anchors carry descriptors, but it is not a language model. -/
namespace SmusniF03A2.Descriptor
open SmusniF02 SmusniF03A1
universe u

abbrev Value (Event : Type u) := Truth × Option Event × Nat
abbrev State (Event : Type u) := RawState Unit Unit Unit (Value Event) Unit

def Relation (ER : Setoid Event) (a b : Value Event) : Prop :=
  a.1 = b.1 ∧ PartialEq ER.r a.2.1 b.2.1

def observationMap (ER : Setoid Event) (d : Value Event) : Truth × Option (Quotient ER) :=
  (d.1, qEvent ER d.2.1)

theorem observationMap_kernel (ER : Setoid Event) : Kernel (observationMap ER) (Relation ER) := by
  intro a b
  simp [observationMap, Relation, event_kernel]

def equivalence (ER : Setoid Event) : Setoid (Value Event) where
  r := Relation ER
  iseqv := ⟨fun a => (observationMap_kernel ER a a).mp rfl,
    fun h => (observationMap_kernel ER _ _).mp ((observationMap_kernel ER _ _).mpr h).symm,
    fun h k => (observationMap_kernel ER _ _).mp
      (((observationMap_kernel ER _ _).mpr h).trans ((observationMap_kernel ER _ _).mpr k))⟩

abbrev StateRelation (ER : Setoid Event) : State Event → State Event → Prop :=
  StateRel (ValueRel (equivalence ER)) (AnchorRel (equivalence ER))

def initial : State Event := ⟨fun _ => none, [], [], .t, .t⟩

def statusOutcome (status : Truth) (s : S) : Outcome S Unit :=
  match status with | .t => .live s () | .f => .dead s | .u => .undef s

@[simp] theorem statusOutcome_truth (status : Truth) (s : S) : (statusOutcome status s).truth = status := by
  cases status <;> rfl

theorem statusOutcome_related (status : Truth) (SR : S → T → Prop) (s : S) (t : T) (related : SR s t) :
    OutRel SR Eq (statusOutcome status s) (statusOutcome status t) := by
  cases status
  · exact related
  · exact related
  · exact ⟨related, rfl⟩

def observe (d : Value Event) : Content Unit (fun _ => Unit) Unit Unit (State Event) Unit Event where
  run _ _ _ _ s := NEFin.singleton (statusOutcome d.1 s)
  event _ _ _ _ _ := d.2.1

/-- This proof does not use the descriptor kernel theorem. It works for every
supplied state relation because the status is fixed and the input state is retained. -/
theorem state_respect (SR : State Event → State Event → Prop) (d : Value Event) : ContentRespect SR (observe d) := by
  intro p i e w s t hst
  exact finRel_singleton _ _ _ (statusOutcome_related d.1 SR s t hst)

theorem singleton_outcome_relation (SR : S → T → Prop) (AR : A → B → Prop)
    (x : Outcome S A) (y : Outcome T B) :
    FinRel (OutRel SR AR) (NEFin.singleton x) (NEFin.singleton y) ↔ OutRel SR AR x y := by
  constructor
  · intro rel
    obtain ⟨z, hz, related⟩ := rel.1 x rfl
    have eq : z = y := hz
    exact eq ▸ related
  · exact finRel_singleton _ _ _

theorem related_outcomes_same_truth (SR : S → T → Prop) (AR : A → B → Prop)
    (x : Outcome S A) (y : Outcome T B) (related : OutRel SR AR x y) : x.truth = y.truth := by
  cases x <;> cases y <;> simp_all [OutRel, Outcome.truth]

/-- Unit coordinates and the explicit empty state prevent a vacuous kernel. -/
theorem joint_observation_kernel (ER : Setoid Event) (a b : Value Event) :
    JointRel (StateRelation ER) ER (observe a) (observe b) ↔ Relation ER a b := by
  constructor
  · intro rel
    have self : StateRelation ER (initial : State Event) initial :=
      (qState_kernel (equivalence ER) _ _).mp rfl
    have terminals := rel.1 () () () () initial initial self
    have outcomes := (singleton_outcome_relation _ _ _ _).mp terminals
    have statuses := related_outcomes_same_truth _ _ _ _ outcomes
    exact ⟨by simpa only [statusOutcome_truth] using statuses, rel.2 () () () () ()⟩
  · rintro ⟨status, event⟩
    constructor
    · intro p i e w s t hst
      apply finRel_singleton
      change OutRel _ Eq (statusOutcome a.1 s) (statusOutcome b.1 t)
      rw [status]
      exact statusOutcome_related _ _ _ _ hst
    · intro p i e w beta
      exact event

def respecting (ER : Setoid Event) (d : Value Event) :
    RespectingContent (P := Unit) (I := fun _ => Unit) (E := Unit) (W := Unit)
      (Beta := Unit) (Event := Event) (StateRelation ER) :=
  ⟨observe d, state_respect _ d⟩

noncomputable def descended (ER : Setoid Event) (d : Value Event) :
    Content Unit (fun _ => Unit) Unit Unit (QuotientState Unit Unit Unit (Value Event) Unit (equivalence ER))
      Unit (Quotient ER) := qContent (equivalence ER) ER (respecting ER d)

theorem descended_kernel (ER : Setoid Event) : Kernel (descended ER) (Relation ER) := by
  intro a b
  exact (qContent_kernel (equivalence ER) ER (respecting ER a) (respecting ER b)).trans
    (joint_observation_kernel ER a b)

theorem descended_run (ER : Setoid Event) (d : Value Event) (s : State Event) :
    (descended ER d).run () () () () (qState (equivalence ER) s) =
      NEFin.singleton (statusOutcome d.1 (qState (equivalence ER) s)) := by
  change (descendContent _ _ ER (respecting ER d)).run _ _ _ _ _ = _
  rw [descendContent_run_at _ _ _ (qState_kernel (equivalence ER))]
  change mapResults (mapOutcome _ id) (NEFin.singleton (statusOutcome d.1 s)) = _
  cases d.1 <;> simp [statusOutcome, mapOutcome]

theorem descended_event (ER : Setoid Event) (d : Value Event) :
    (descended ER d).event () () () () () = qEvent ER d.2.1 := rfl

theorem annotations_ignored (ER : Setoid Event) (status : Truth) (event : Option Event) (n m : Nat) :
    descended ER (status, event, n) = descended ER (status, event, m) :=
  (descended_kernel ER _ _).mpr ⟨rfl, partial_refl ER event⟩

theorem different_status_classes (ER : Setoid Event) (event : Option Event) :
    descended ER (.t, event, 0) ≠ descended ER (.f, event, 1) := by
  intro eq
  have h := ((descended_kernel ER _ _).mp eq).1
  cases h

theorem supplied_event (ER : Setoid Event) (event : Event) (annotation : Nat) :
    (descended ER (.t, some event, annotation)).event () () () () () = some (Quotient.mk ER event) := rfl

def stored (d : Value Event) : State Event := putSlot () (some (.inr d)) initial

theorem stored_annotations_identify (ER : Setoid Event) (status : Truth) (event : Option Event) (n m : Nat) :
    qState (equivalence ER) (stored (status, event, n)) =
      qState (equivalence ER) (stored (status, event, m)) := by
  change mapState _ _ (putSlot _ _ _) = mapState _ _ (putSlot _ _ _)
  rw [map_putSlot, map_putSlot]
  have values : qValue (G := Unit) (equivalence ER) (.inr (status, event, n)) =
      qValue (equivalence ER) (.inr (status, event, m)) :=
    (tag_kernel (equivalence ER) _ _).mpr ⟨rfl, partial_refl ER event⟩
  simp only [Option.map_some, values]

theorem stored_descriptor_run (ER : Setoid Event) (d slot : Value Event) :
    (descended ER d).run () () () () (qState (equivalence ER) (stored slot)) =
      NEFin.singleton (statusOutcome d.1 (qState (equivalence ER) (stored slot))) :=
  descended_run ER d (stored slot)
end SmusniF03A2.Descriptor
