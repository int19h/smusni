import SmusniF03A2.Functions
import SmusniF03A2.FailureControl

namespace SmusniF03A2.Controls
open SmusniF02 SmusniF03A1

def equality (A : Type _) : Setoid A := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
def parity : Setoid Nat := ⟨fun a b => a % 2 = b % 2, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩

theorem identity_function_descends (AR : Setoid A) :
    qFun AR AR ⟨id, fun _ _ h => h⟩ = id := by
  funext q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  rfl

def shiftedRepresentative : Respectful parity parity :=
  ⟨fun n => n + 2, by
    intro a b related
    change a % 2 = b % 2 at related
    change (a + 2) % 2 = (b + 2) % 2
    simpa [Nat.add_mod] using related⟩

theorem related_functions_identify :
    qFun parity parity ⟨id, fun _ _ h => h⟩ = qFun parity parity shiftedRepresentative := by
  apply (qFun_kernel parity parity _ _).mpr
  intro a b related
  change a % 2 = b % 2 at related
  change a % 2 = (b + 2) % 2
  simpa [Nat.add_mod] using related

theorem raw_label_function_rejected : ¬Respect parity (equality Bool) (fun n => n == 0) := by
  intro respect
  have h := respect 0 2 rfl
  change true = false at h
  cases h

def rawContinuation (n : Nat) : Run Unit Unit := fun s =>
  if n = 0 then NEFin.singleton (.live s ()) else NEFin.singleton (.dead s)

theorem raw_label_continuation_rejected : ¬Respect parity (equality (Run Unit Unit)) rawContinuation := by
  intro respect
  have equal := respect 0 2 rfl
  have atState := congrFun equal ()
  have live : Outcome.live () () ∈ rawContinuation 0 () := rfl
  rw [atState] at live
  change (Outcome.live () () : Outcome Unit Unit) = .dead () at live
  cases live

theorem function_classes_distinct :
    qFun parity parity ⟨id, fun _ _ h => h⟩ (Quotient.mk parity 0) ≠
      qFun parity parity ⟨id, fun _ _ h => h⟩ (Quotient.mk parity 1) := by
  intro h
  have related := Quotient.exact h
  exact (by decide : ¬(0 % 2 = 1 % 2)) related

theorem related_events_identify : qEvent parity (some 0) = qEvent parity (some 2) :=
  (event_kernel parity _ _).mpr rfl

theorem event_definedness_retained (ER : Setoid Event) (event : Event) :
    qEvent ER none ≠ qEvent ER (some event) := by simp [qEvent]

theorem equal_run_different_event :
    (Descriptor.observe (.t, some false, 0)).run = (Descriptor.observe (.t, some true, 1)).run ∧
    ¬JointRel (Descriptor.StateRelation (equality Bool)) (equality Bool)
      (Descriptor.observe (.t, some false, 0)) (Descriptor.observe (.t, some true, 1)) := by
  refine ⟨rfl, ?_⟩
  intro joint
  have event := ((Descriptor.joint_observation_kernel (equality Bool) _ _).mp joint).2
  change false = true at event
  cases event

theorem equal_run_missing_event :
    (Descriptor.observe (.t, (none : Option Bool), 0)).run = (Descriptor.observe (.t, some false, 1)).run ∧
    ¬JointRel (Descriptor.StateRelation (equality Bool)) (equality Bool)
      (Descriptor.observe (.t, none, 0)) (Descriptor.observe (.t, some false, 1)) := by
  refine ⟨rfl, ?_⟩
  intro joint
  exact ((Descriptor.joint_observation_kernel (equality Bool) _ _).mp joint).2

theorem actual_descriptor_controls :
    Descriptor.descended (equality Bool) (.t, some false, 0) =
      Descriptor.descended (equality Bool) (.t, some false, 7) ∧
    Descriptor.descended (equality Bool) (.t, some false, 0) ≠
      Descriptor.descended (equality Bool) (.f, some false, 1) ∧
    (Descriptor.descended (equality Bool) (.t, some false, 0)).event () () () () () =
      some (Quotient.mk (equality Bool) false) :=
  ⟨Descriptor.annotations_ignored _ _ _ _ _, Descriptor.different_status_classes _ _, rfl⟩

theorem explicit_starting_state :
    (Descriptor.descended (equality Bool) (.t, some false, 0)).run () () () ()
      (qState (Descriptor.equivalence (equality Bool)) Descriptor.initial) =
      NEFin.singleton (.live (qState (Descriptor.equivalence (equality Bool)) Descriptor.initial) ()) :=
  Descriptor.descended_run _ _ _

/-- Both source and event coordinates vary here, independently of the run state. -/
def indexed : Content Unit (fun _ => Nat) Nat Unit Unit Nat Nat where
  run _ _ _ _ := Run.pure ()
  event _ source context _ beta := some (source + context + beta)

theorem event_pull_uses_source_and_event (source beta context : Nat) :
    (Content.pull (fun _ n => n + 5) indexed).event () source context () beta =
      some (source + 5 + context + beta) := rfl

theorem event_capture_uses_saved_context (source beta saved caller : Nat) :
    (Content.capture saved indexed).event () source caller () beta = some (source + saved + beta) := rfl

theorem indexed_respects : ContentRespect Eq indexed := by
  intro p i e w s t equal
  exact finRel_singleton _ _ _ ⟨equal, rfl⟩

theorem joint_descent_capture_control (saved : Nat) :
    descendContent id (fun s : Unit => ⟨s, rfl⟩) parity (captureContent saved ⟨indexed, indexed_respects⟩) =
      Content.capture saved (descendContent id (fun s : Unit => ⟨s, rfl⟩) parity ⟨indexed, indexed_respects⟩) :=
  descendContent_capture _ _ _ _ _
end SmusniF03A2.Controls
