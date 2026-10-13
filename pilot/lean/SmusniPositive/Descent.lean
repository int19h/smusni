import SmusniPositive.Run

namespace SmusniPositive
open SmusniF02 SmusniF03A1
universe u v
variable {sig : Signature.{u}} {W : Type v}

abbrev Proposition (M : Model sig W) := Quotient (RJ M)
abbrev State (M : Model sig W) := HostState sig.Name (Proposition M) Unit Unit
abbrev QuotContext (M : Model sig W) := (k : sig.Key) → (Fin (sig.siteArity k) → sig.Ground) → Option (Proposition M)
abbrev Observation (M : Model sig W) :=
  Content Unit (fun _ => Unit) (QuotContext M) W (State M) (State M) (Quotient (Rv M))

def qS (M : Model sig W) : RawState sig → State M := mapState (Quotient.mk (RJ M)) id
def qB (M : Model sig W) : RawState sig → State M := qS M
def qE (M : Model sig W) (E : Context sig) : QuotContext M :=
  fun k args => (E k args).map (Quotient.mk (RJ M))

def ContextRel (R : Setoid (Code sig)) (E F : Context sig) : Prop :=
  ∀ k args, OptionRel R.r (E k args) (F k args)

theorem qS_kernel (M : Model sig W) : Kernel (qS M) (StateRel (RJ M).r Eq) :=
  state_kernel _ _ _ _ (quotient_kernel (RJ M)) (fun _ _ => Iff.rfl)
theorem qS_onto (M : Model sig W) : Onto (qS M) :=
  state_onto _ _ (quotient_onto (RJ M)) (fun x => ⟨x, rfl⟩)
theorem qB_kernel (M : Model sig W) : Kernel (qB M) (StateRel (RJ M).r Eq) := qS_kernel M
theorem qB_onto (M : Model sig W) : Onto (qB M) := qS_onto M

theorem qE_kernel (M : Model sig W) : Kernel (qE M) (ContextRel (RJ M)) := by
  intro E F
  constructor
  · intro eq k args
    exact (option_kernel _ _ (quotient_kernel (RJ M)) _ _).mp (congrArg (fun E => E k args) eq)
  · intro rel
    funext k args
    exact (option_kernel _ _ (quotient_kernel (RJ M)) _ _).mpr (rel k args)

theorem qE_onto (M : Model sig W) : Onto (qE M) := by
  classical
  intro E
  have each := option_onto (Quotient.mk (RJ M)) (quotient_onto (RJ M))
  refine ⟨fun k args => (each (E k args)).choose, ?_⟩
  funext k args
  exact (each (E k args)).choose_spec

noncomputable def pickS (M : Model sig W) (s : State M) : RawState sig := (qS_onto M s).choose
noncomputable def pickB (M : Model sig W) (beta : State M) : RawState sig := (qB_onto M beta).choose
noncomputable def pickE (M : Model sig W) (E : QuotContext M) : Context sig := (qE_onto M E).choose
theorem pickS_image (M : Model sig W) (s : State M) : qS M (pickS M s) = s := (qS_onto M s).choose_spec
theorem pickB_image (M : Model sig W) (beta : State M) : qB M (pickB M beta) = beta := (qB_onto M beta).choose_spec
theorem pickE_image (M : Model sig W) (E : QuotContext M) : qE M (pickE M E) = E := (qE_onto M E).choose_spec

theorem selected_run_input (M : Model sig W) (E : Context sig) (w : W) (s : RawState sig) :
    InputRel (RJ M) ⟨pickE M (qE M E), w, pickS M (qS M s)⟩ ⟨E, w, s⟩ :=
  ⟨rfl, (qS_kernel M _ _).mp (pickS_image M _), (qE_kernel M _ _).mp (pickE_image M _)⟩

theorem selected_event_input (M : Model sig W) (E : Context sig) (w : W) (beta : RawState sig) :
    InputRel (RJ M) ⟨pickE M (qE M E), w, pickB M (qB M beta)⟩ ⟨E, w, beta⟩ :=
  ⟨rfl, (qB_kernel M _ _).mp (pickB_image M _), (qE_kernel M _ _).mp (pickE_image M _)⟩

/-- All three quotient coordinates are genuine inputs. Beta is supplied
independently and is never selected from the run output or its caller state. -/
noncomputable def denotation (M : Model sig W) (c : Code sig) : Observation M where
  run _ _ E w s := NEFin.singleton (outcomeOf (value M c ⟨pickE M E, w, pickS M s⟩) s)
  event _ _ E w beta := SmusniF03A2.qEvent (Rv M) (event c ⟨pickE M E, w, pickB M beta⟩)

theorem denotation_run_at (M : Model sig W) (c : Code sig) (E : Context sig) (w : W) (s : RawState sig) :
    (denotation M c).run () () (qE M E) w (qS M s) =
      mapResults (mapOutcome (qS M) id) (run M c E w s) := by
  have values := value_transport M (RJ M) (rj_value_sound M) (reclose_refl (RJ M) c) (selected_run_input M E w s)
  simp only [denotation, values, run, mapResults_singleton, map_outcomeOf]

theorem denotation_event_at (M : Model sig W) (c : Code sig) (E : Context sig) (w : W) (beta : RawState sig) :
    (denotation M c).event () () (qE M E) w (qB M beta) =
      SmusniF03A2.qEvent (Rv M) (event c ⟨E, w, beta⟩) :=
  (SmusniF03A2.event_kernel (Rv M) _ _).mpr
    (event_transport M (RJ M) (rj_value_sound M) (fun _ _ h => h.2)
      (reclose_refl (RJ M) c) (selected_event_input M E w beta))

theorem denotation_kernel (M : Model sig W) : Kernel (denotation M) (RJ M).r := by
  intro c d
  constructor
  · intro eq
    constructor
    · intro i
      have runs := congrArg (fun f : Observation M => f.run () () (qE M i.context) i.world (qS M i.state)) eq
      rw [denotation_run_at, denotation_run_at] at runs
      simp only [run, mapResults_singleton, map_outcomeOf] at runs
      simpa only [outcomeOf_truth] using singleton_truth _ _ runs
    · intro i
      have events := congrArg (fun f : Observation M => f.event () () (qE M i.context) i.world (qB M i.state)) eq
      rw [denotation_event_at, denotation_event_at] at events
      exact (SmusniF03A2.event_kernel (Rv M) _ _).mp events
  · intro rel
    apply SmusniF03A2.content_ext
    · funext p i E w s
      simp only [denotation, rel.1 ⟨pickE M E, w, pickS M s⟩]
    · funext p i E w beta
      exact (SmusniF03A2.event_kernel (Rv M) _ _).mpr (rel.2 ⟨pickE M E, w, pickB M beta⟩)

/-- Explicit computation at arbitrary quotient coordinates via proved coverage. -/
theorem all_inputs_covered (M : Model sig W) (E : QuotContext M) (s beta : State M) :
    ∃ E0 s0 beta0, qE M E0 = E ∧ qS M s0 = s ∧ qB M beta0 = beta :=
  ⟨pickE M E, pickS M s, pickB M beta, pickE_image M E, pickS_image M s, pickB_image M beta⟩
end SmusniPositive
