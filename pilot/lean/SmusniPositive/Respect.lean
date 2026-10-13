import SmusniPositive.Evidence
import SmusniF03A1.State

namespace SmusniPositive
open SmusniF03A1
universe u v
variable {sig : Signature.{u}} {W : Type v}

inductive Reclose (R : Setoid (Code sig)) : Code sig → Code sig → Prop where
  | mk {m n} {t : Term sig m n} {g g' : Fin m → sig.Ground} {r r' : Fin n → Code sig}
      (ground : g = g') (prop : ∀ x, R.r (r x) (r' x)) : Reclose R (.mk t g r) (.mk t g' r')

theorem reclose_refl (R : Setoid (Code sig)) (c : Code sig) : Reclose R c c := by
  cases c with | mk t g r => exact .mk rfl (fun x => R.refl (r x))
theorem reclose_symm (R : Setoid (Code sig)) {c d} (h : Reclose R c d) : Reclose R d c := by
  cases h with | mk ground prop => exact .mk ground.symm (fun x => R.symm (prop x))

theorem extend_related (R : Setoid (Code sig)) {r r' : Fin n → Code sig} {q q'}
    (env : ∀ x, R.r (r x) (r' x)) (value : R.r q q') :
    ∀ x, R.r (extend r q x) (extend r' q' x) := Fin.cases value env

structure InputRel (R : Setoid (Code sig)) (i j : Input sig W) : Prop where
  world : i.world = j.world
  state : StateRel R.r Eq i.state j.state
  context : ∀ k args, OptionRel R.r (i.context k args) (j.context k args)

theorem state_refl (R : Setoid (Code sig)) (s : RawState sig) : StateRel R.r Eq s s :=
  (state_kernel (Quotient.mk R) id R.r Eq (quotient_kernel R) (fun _ _ => Iff.rfl) s s).mp rfl

theorem option_symm (R : Setoid A) {a b : Option A} (h : OptionRel R.r a b) : OptionRel R.r b a := by
  cases a <;> cases b <;> simp_all [OptionRel]
  exact R.symm h

theorem input_refl (R : Setoid (Code sig)) (i : Input sig W) : InputRel R i i := by
  refine ⟨rfl, state_refl R i.state, ?_⟩
  intro k args
  cases h : i.context k args <;> simp [OptionRel, R.refl]

theorem input_symm (R : Setoid (Code sig)) {i j : Input sig W} (h : InputRel R i j) : InputRel R j i := by
  refine ⟨h.world.symm, ?_, fun k args => option_symm R (h.context k args)⟩
  exact (state_kernel (Quotient.mk R) id R.r Eq (quotient_kernel R) (fun _ _ => Iff.rfl) j.state i.state).mp
    ((state_kernel (Quotient.mk R) id R.r Eq (quotient_kernel R) (fun _ _ => Iff.rfl) i.state j.state).mpr h.state).symm

theorem option_partner (R : A → B → Prop) {q : A} {value : Option B} (h : OptionRel R (some q) value) :
    ∃ q', value = some q' ∧ R q q' := by
  cases value with
  | none => exact False.elim h
  | some q' => exact ⟨q', rfl, h⟩

/-- Soundness only at one fixed raw input, not cross-input transport. -/
def EvidenceSound (M : Model sig W) (R : Setoid (Code sig)) : Prop :=
  ∀ c d, R.r c d → ∀ i b, Evidence M c i b → Evidence M d i b

/-- Partner closures and inputs are generalized before derivation induction. -/
theorem evidence_transport (M : Model sig W) (R : Setoid (Code sig)) (sound : EvidenceSound M R)
    {c i b} (h : Evidence M c i b) :
    ∀ {d j}, Reclose R c d → InputRel R i j → Evidence M d j b := by
  induction h with
  | top => intro d j same inputs; cases same; exact .top
  | bot => intro d j same inputs; cases same; exact .bot
  | atom a args =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      cases ground
      rw [inputs.world]
      exact .atom a args
  | neg _ ih =>
    intro d j same inputs
    cases same with | mk ground prop => exact .neg (ih (.mk ground prop) inputs)
  | holdsReify _ ih =>
    intro d j same inputs
    cases same with | mk ground prop => exact .holdsReify (ih (.mk ground prop) inputs)
  | holdsVar x _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      apply Evidence.holdsVar x
      apply sound _ _ (prop x) j _
      exact ih (reclose_refl R _) inputs
  | @ctx m n g r i b k args body q found _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      cases ground
      have relation := inputs.context k (evalGround args g)
      rw [found] at relation
      obtain ⟨q', found', related⟩ := option_partner _ relation
      exact .ctx k args body q' found' (ih (.mk rfl (extend_related R prop related)) inputs)
  | read name body q found _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      have relation := inputs.state.1 name
      rw [found] at relation
      obtain ⟨q', found', related⟩ := option_partner _ relation
      exact .read name body q' found' (ih (.mk ground (extend_related R prop related)) inputs)
  | allGT body _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      exact .allGT body (fun a => ih a (.mk (congrArg (fun g => extend g a) ground) prop) inputs)
  | allGF body a _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      exact .allGF body a (ih (.mk (congrArg (fun g => extend g a) ground) prop) inputs)
  | allPT body _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      exact .allPT body (fun q => ih q (.mk ground (extend_related R prop (R.refl q))) inputs)
  | allPF body q _ ih =>
    intro d j same inputs
    cases same with
    | mk ground prop =>
      exact .allPF body q (ih (.mk ground (extend_related R prop (R.refl q))) inputs)

theorem evidence_transport_iff (M : Model sig W) (R : Setoid (Code sig)) (sound : EvidenceSound M R)
    {c d i j b} (same : Reclose R c d) (inputs : InputRel R i j) :
    Evidence M c i b ↔ Evidence M d j b :=
  ⟨fun h => evidence_transport M R sound h same inputs,
   fun h => evidence_transport M R sound h (reclose_symm R same) (input_symm R inputs)⟩

/-- Explicit five-step Holds-variable bridge: move the same q using its own
reflexively related environment, then apply fixed-input soundness to q and q'. -/
theorem holds_variable_bridge (M : Model sig W) (R : Setoid (Code sig)) (sound : EvidenceSound M R)
    {q q' i j b} (related : R.r q q') (inputs : InputRel R i j) (h : Evidence M q i b) :
    Evidence M (holdsCode q') j b := by
  have moved := evidence_transport M R sound h (reclose_refl R q) inputs
  have replaced := sound q q' related j b moved
  exact .holdsVar 0 replaced
end SmusniPositive
