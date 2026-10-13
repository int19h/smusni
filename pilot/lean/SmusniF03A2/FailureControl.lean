import SmusniF03A2.Descriptor

/-! A separate diagnostic family with its own raw observational kernel.
The raw-tag inspection is intentional here and absent from the general path. -/
namespace SmusniF03A2.FailureControl
open SmusniF02 SmusniF03A1

inductive Label where
  | constant : Nat → Label
  | probe : Label

abbrev State := RawState Unit Unit Unit Label Unit
def initial : State := ⟨fun _ => none, [], [], .t, .t⟩
def stored (n : Nat) : State := putSlot () (some (.inr (.constant n))) initial

def rawTest (s : State) : Bool := match s.assignment () with
  | some (.inr (.constant n)) => n == 0
  | _ => false

def observe (label : Label) : Content Unit (fun _ => Unit) Unit Unit State Unit Bool where
  run _ _ _ _ s := match label with
    | .constant _ => NEFin.singleton (.live s ())
    | .probe => if rawTest s then NEFin.singleton (.live s ()) else NEFin.singleton (.dead s)
  event _ _ _ _ _ := some false

/-- This kernel uses equality of raw runs at the same state, plus actual partial
event equality. It is defined before, and independently of, StateRel. -/
def ownKernel : Setoid Label where
  r a b := Content.ObsEq Eq (observe a) (observe b)
  iseqv := ⟨fun a => Content.obsEq_refl Eq (fun _ => rfl) (observe a),
    fun h => Content.obsEq_symm Eq (fun _ _ h => h.symm) h,
    fun h k => Content.obsEq_trans Eq (fun _ _ _ => Eq.trans) h k⟩

abbrev StateRelation : State → State → Prop := StateRel (ValueRel ownKernel) (AnchorRel ownKernel)

theorem constants_identified : ownKernel.r (.constant 0) (.constant 1) :=
  ⟨rfl, fun _ _ _ _ _ => rfl⟩

theorem stored_states_related : StateRelation (stored 0) (stored 1) := by
  apply (qState_kernel ownKernel _ _).mp
  change mapState _ _ (putSlot _ _ _) = mapState _ _ (putSlot _ _ _)
  rw [map_putSlot, map_putSlot]
  have values : qValue (G := Unit) ownKernel (.inr (.constant 0)) =
      qValue ownKernel (.inr (.constant 1)) := (tag_kernel ownKernel _ _).mpr constants_identified
  simp only [Option.map_some, values]

theorem probe_not_state_respecting : ¬ContentRespect StateRelation (observe .probe) := by
  intro respects
  have h := respects () () () () (stored 0) (stored 1) stored_states_related
  change FinRel (OutRel StateRelation Eq)
    (NEFin.singleton (.live (stored 0) ())) (NEFin.singleton (.dead (stored 1))) at h
  exact (Descriptor.singleton_outcome_relation _ _ _ _).mp h

theorem kernel_equality_not_constructor_congruence :
    ownKernel.r (.constant 0) (.constant 1) ∧ ownKernel.r .probe .probe ∧
    ¬ContentRespect StateRelation (observe .probe) :=
  ⟨constants_identified, ownKernel.refl _, probe_not_state_respecting⟩
end SmusniF03A2.FailureControl
