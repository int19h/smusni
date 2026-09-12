import SmusniF02.SourcePayload

/-! Regression for Astra's F02-A1 counterexample (durable report
msg_20260912T001533789225Z_20c9b55654ac4877aed582c121383463).
Two terminals have the same parent and Obtained unit but different saved states.
The generic combinator can expose that state; the source constructor cannot. -/
namespace SmusniF02.SourceBoundary

def source (_ : Unit) (_ : Unit) : Terminal Bool Unit :=
  NEFin.ofHeadTail (.live false ()) [.live true ()]
abbrev I := Origin source
def left : I () := ⟨(), .live false (), by simp [source]⟩
def right : I () := ⟨(), .live true (), by simp [source]⟩
def nucleus (_ : Unit) : Content Unit (fun _ => Bool) Unit Unit Bool Bool (Bool × Bool) where
  run _ inherited _ _ caller :=
    NEFin.singleton (if inherited then .live caller () else .dead caller)
  event _ inherited _ _ beta := some (inherited, beta)

theorem same_parent_result_different_state :
    left.parent = right.parent ∧ left.result = right.result ∧ left.reached ≠ right.reached := by
  exact ⟨rfl, rfl, by decide⟩

noncomputable def broader := payload .first (fun _ i => i.result)
  (fun (_ : Unit) (i : I ()) => i.reached) nucleus

/-- Keep the counterexample: the generic combinator is intentionally broader. -/
theorem generic_can_expose_saved_state :
    broader.run () left () () false = NEFin.singleton (.dead false) ∧
    broader.run () right () () false = NEFin.singleton (.live false ()) ∧
    broader.event () left () () false = some (false, false) ∧
    broader.event () right () () false = some (true, false) := by
  constructor
  · change (payload .first _ _ nucleus).run () left () () false = _
    rw [payload_obtained_run .first _ _ nucleus () left () rfl]; rfl
  constructor
  · change (payload .first _ _ nucleus).run () right () () false = _
    rw [payload_obtained_run .first _ _ nucleus () right () rfl]; rfl
  exact ⟨rfl, rfl⟩

/-- Both phases, arbitrary lawful inherited map, caller and Beta. The source
terminals remain distinct; their equal replay observations follow from the API. -/
theorem restricted_same_parent_result (phase : ReadPhase) (inherited : Unit → Unit → Bool)
    (caller beta : Bool) :
    (sourcePayload phase source inherited nucleus).run () left () () caller =
      (sourcePayload phase source inherited nucleus).run () right () () caller ∧
    (sourcePayload phase source inherited nucleus).event () left () () beta =
      (sourcePayload phase source inherited nucleus).event () right () () beta := by
  exact ⟨congrFun (sourcePayload_run_invariant phase source inherited nucleus ()
    left right rfl rfl () ()) caller,
    sourcePayload_event_invariant phase source inherited nucleus () left right rfl rfl () () beta⟩

theorem fixed_false_caller_regression (phase : ReadPhase) :
    (sourcePayload phase source (fun _ _ => false) nucleus).run () left () () false =
      NEFin.singleton (.dead false) ∧
    (sourcePayload phase source (fun _ _ => false) nucleus).run () right () () false =
      NEFin.singleton (.dead false) ∧
    (sourcePayload phase source (fun _ _ => false) nucleus).event () left () () false =
      some (false, false) ∧
    (sourcePayload phase source (fun _ _ => false) nucleus).event () right () () false =
      some (false, false) := by
  constructor
  · rw [sourcePayload_obtained_run phase source _ nucleus () left () rfl]; rfl
  constructor
  · rw [sourcePayload_obtained_run phase source _ nucleus () right () rfl]; rfl
  exact ⟨rfl, rfl⟩

def parentSource (_ : Unit) (_ : Bool) : Terminal Bool Unit := NEFin.singleton (.live false ())
def atParent (b : Bool) : Origin parentSource () := ⟨b, .live false (), rfl⟩

/-- Lawful dependence on different inherited parents is preserved. -/
theorem different_parent_can_matter (phase : ReadPhase) :
    (sourcePayload phase parentSource (fun _ b => b) nucleus).run
      () (atParent false) () () false = NEFin.singleton (.dead false) ∧
    (sourcePayload phase parentSource (fun _ b => b) nucleus).run
      () (atParent true) () () false = NEFin.singleton (.live false ()) := by
  constructor <;> rw [sourcePayload_obtained_run phase parentSource _ nucleus () _ () rfl] <;> rfl

/-- Invariance fixes Beta; it does not erase independent event-branch distinctions. -/
theorem beta_remains_distinct (phase : ReadPhase) :
    (sourcePayload phase source (fun _ _ => false) nucleus).event () left () () false ≠
      (sourcePayload phase source (fun _ _ => false) nucleus).event () left () () true := by
  change (some (false, false) : Option (Bool × Bool)) ≠ some (false, true)
  decide
end SmusniF02.SourceBoundary
