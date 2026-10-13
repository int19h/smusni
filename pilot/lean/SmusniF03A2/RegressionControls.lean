import SmusniF03A2.Controls

/- Reviewer integration boundary at c503e51f1a5106ccc926f44af5ab246507f941ba.
This is an instance of the supplied carrier, not a Lojban model. -/
namespace AstraPR103
open SmusniF02 SmusniF03A1 SmusniF03A2

def events : Setoid Bool := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
def d (n : Nat) : Descriptor.Value Bool := (.u, some false, n)
def anchored (n : Nat) : Descriptor.State Bool :=
  { Descriptor.stored (d n) with sides := [⟨.inr (d n), false⟩] }

theorem annotations_in_slot_and_anchor (n m : Nat) :
    qState (Descriptor.equivalence events) (anchored n) =
      qState (Descriptor.equivalence events) (anchored m) := by
  apply (qState_kernel (Descriptor.equivalence events) _ _).mpr
  constructor
  · intro name
    cases name
    change Descriptor.Relation events (d n) (d m)
    exact ⟨rfl, rfl⟩
  · exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, True.intro⟩, rfl, rfl, rfl⟩

theorem anchored_side_keeps_false (n : Nat) :
    (qState (Descriptor.equivalence events) (anchored n)).sides =
      [⟨.inr (Quotient.mk (Descriptor.equivalence events) (d n)), false⟩] := rfl

theorem undefined_run_defined_event (n : Nat) :
    (Descriptor.descended events (d n)).run () () () ()
        (qState (Descriptor.equivalence events) (anchored n)) =
      NEFin.singleton (.undef (qState (Descriptor.equivalence events) (anchored n))) ∧
    (Descriptor.descended events (d n)).event () () () () () =
      some (Quotient.mk events false) := by
  constructor
  · exact Descriptor.descended_run events (d n) (anchored n)
  · rfl

def coordinateEvents : Setoid (Nat × Nat × Nat) :=
  ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

def coordinateContent : Content Unit (fun _ => Nat) Nat Unit Unit Nat (Nat × Nat × Nat) where
  run _ _ _ _ := Run.pure ()
  event _ source context _ beta := some (source, context, beta)

theorem coordinate_respect : ContentRespect Eq coordinateContent := by
  intro p i e w s t equal
  exact finRel_singleton _ _ _ ⟨equal, rfl⟩

theorem coordinates_remain_separate (source beta caller saved : Nat) :
    (descendContent id (fun s : Unit => ⟨s, rfl⟩) coordinateEvents
      (pullContent (fun _ n => n + 5)
        (captureContent saved ⟨coordinateContent, coordinate_respect⟩))).event
          () source caller () beta =
      some (Quotient.mk coordinateEvents (source + 5, saved, beta)) := rfl

end AstraPR103

/- Fable's distinct related-saved-context control, confirmed by Astra.
The full contract is proved before its selected capture instance. -/
namespace RelatedCapturePR103
open SmusniF02 SmusniF03A1 SmusniF03A2 SmusniF03A2.Controls

theorem full_context_parity : ContextJointRel Eq parity parity.r indexed indexed := by
  constructor
  · intro p source context context' world _
    exact pure_compatible Eq Eq () () rfl
  · intro p source context context' world beta related
    change context % 2 = context' % 2 at related
    change (source + context + beta) % 2 = (source + context' + beta) % 2
    rw [Nat.add_mod (source + context) beta 2, Nat.add_mod (source + context') beta 2,
      Nat.add_mod source context 2, Nat.add_mod source context' 2, related]

theorem related_saved_captures_equal :
    descendContent id (fun s : Unit => ⟨s, rfl⟩) parity
        (captureContent 1 ⟨indexed, indexed_respects⟩) =
      descendContent id (fun s : Unit => ⟨s, rfl⟩) parity
        (captureContent 3 ⟨indexed, indexed_respects⟩) :=
  captured_quotient_equal id (fun s : Unit => ⟨s, rfl⟩) parity (fun _ _ => Iff.rfl)
    parity.r 1 3 rfl ⟨indexed, indexed_respects⟩ ⟨indexed, indexed_respects⟩ full_context_parity

theorem raw_saved_events_differ (source beta caller : Nat) :
    (Content.capture 1 indexed).event () source caller () beta ≠
      (Content.capture 3 indexed).event () source caller () beta := by
  intro equal
  have values : source + 1 + beta = source + 3 + beta := Option.some.inj equal
  have impossible : 1 = 3 := Nat.add_left_cancel (Nat.add_right_cancel values)
  cases impossible
end RelatedCapturePR103
