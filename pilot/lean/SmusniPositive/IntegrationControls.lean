import SmusniPositive.Chain
import SmusniPositive.Weakening
import SmusniPositive.Coding

/-! Novelty controls of the general construction. Supplied lexical data is
deliberately nonconstant in both its world and its ground tuple. -/
namespace SmusniPositive.IntegrationControls
open SmusniF02 SmusniF03A1 SmusniPositive.Controls

abbrev sig : Signature where
  Ground := Nat
  Name := Unit
  Key := Unit
  Predicate := Unit
  siteArity _ := 1
  predicateArity _ := 2

def model : Model sig Bool where
  lexical _ world args := world && decide (args 0 < args 1)

def atomCode (g : Nat) : Code sig :=
  .mk (.atom () (Fin.cases (.var 0) (fun _ => .literal 7))) (fun _ : Fin 1 => g) emptyEnv

theorem lexical_world_and_ground_consumed :
    value model (atomCode 5) ⟨absentContext sig, true, initial sig⟩ = .t ∧
    value model (atomCode 5) ⟨absentContext sig, false, initial sig⟩ = .f ∧
    value model (atomCode 9) ⟨absentContext sig, true, initial sig⟩ = .f := by
  simp only [atomCode, value_atom]
  exact ⟨rfl, rfl, rfl⟩

def allGroundLess : Code sig :=
  closed (.allG (.atom () (Fin.cases (.var 0) (fun _ => .literal 7))))

theorem all_ground_uses_entire_domain : value model allGroundLess ⟨absentContext sig, true, initial sig⟩ = .f := by
  apply (value_allG_false model emptyEnv emptyEnv _ _).mpr
  refine ⟨9, ?_⟩
  rw [value_atom]
  rfl

def allPropsHold : Code sig := closed (.allP (.holdsVar 0))

theorem all_propositions_not_finite_samples : value model allPropsHold ⟨absentContext sig, true, initial sig⟩ = .f := by
  apply (value_allP_false model emptyEnv emptyEnv _ _).mpr
  refine ⟨botCode sig, ?_⟩
  rw [value_holdsVar]
  exact value_bot model _ _ _

def slotCode : Code sig := closed (.read () (.holdsVar 0))
def slotState (c : Code sig) : RawState sig := putSlot () (some c) (initial sig)

theorem independent_event_assignment :
    (denotation model slotCode).run () () (qE model (absentContext sig)) true (qS model (slotState (topCode sig))) =
      NEFin.singleton (.live (qS model (slotState (topCode sig))) ()) ∧
    (denotation model slotCode).event () () (qE model (absentContext sig)) true (qB model (slotState (botCode sig))) =
      some (Quotient.mk (Rv model) (botCode sig)) ∧
    (denotation model slotCode).event () () (qE model (absentContext sig)) true (qB model (initial sig)) = none := by
  constructor
  · rw [denotation_run_at]
    simp [run, slotCode, closed, value_read, slotState, putSlot, value_holdsVar, topCode, value_top,
      outcomeOf, mapOutcome]
  · constructor
    · rw [denotation_event_at]
      simp [slotCode, closed, event_read, slotState, putSlot, event_var, botCode,
        event_default (DefaultRow.bot : DefaultRow (botCode sig)), SmusniF03A2.qEvent]
    · rw [denotation_event_at]
      simp [slotCode, closed, event_read, initial, SmusniF03A2.qEvent]

def alwaysTop : Context sig := fun _ _ => some (topCode sig)
def changedAfterZero : Context sig := fun _ args => if args 0 = 0 then some (topCode sig) else some (botCode sig)

theorem full_tuple_context_not_visited_cache :
    alwaysTop () (fun _ => 0) = changedAfterZero () (fun _ => 0) ∧
    qE model alwaysTop ≠ qE model changedAfterZero := by
  refine ⟨rfl, ?_⟩
  intro eq
  have later := congrArg (fun E => E () (fun _ : Fin 1 => 1)) eq
  have classes : Quotient.mk (RJ model) (topCode sig) = Quotient.mk (RJ model) (botCode sig) :=
    Option.some.inj later
  exact top_bot_distinct model classes

theorem context_representatives_identify :
    qE model alwaysTop = qE model (fun _ _ => some (negBot sig)) := by
  funext key args
  exact congrArg some (top_neg_bot_same_class model)

def unusedEnvironment (c : Code sig) : Code sig := .mk (.top : Term sig 0 1) emptyEnv (fun _ => c)
def firstCaptured : Code sig → Option (Code sig)
  | @Code.mk _ _ 0 _ _ _ => none
  | @Code.mk _ _ (_n+1) _ _ r => some (r 0)

theorem encoding_retains_unused_environments :
    Coding.encode (unusedEnvironment (topCode sig)) ≠ Coding.encode (unusedEnvironment (botCode sig)) := by
  intro eq
  have codes := Coding.encode_injective eq
  have captured := congrArg firstCaptured codes
  have impossible : topCode sig = botCode sig := Option.some.inj captured
  cases impossible
end SmusniPositive.IntegrationControls
