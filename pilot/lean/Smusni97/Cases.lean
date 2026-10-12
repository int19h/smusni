import Smusni97.Comparison
import Smusni97.Reviewed
import Smusni97.Admission

/-! Shared inputs exercise both candidates. Case labels never dispatch semantic
behavior. All data constructors below consume their arguments directly. -/
namespace Smusni97.Cases
open SmusniF02

def entry : State :=
  ⟨fun n => if n = 0 then some 7 else none, [⟨7, false⟩], [⟨7, 11⟩],
    [2, 1], [⟨4, .f, .f⟩], .f, .f⟩
def prepare (s : State) (v : Nat) : State :=
  { introduce 2 99 (introduce 1 v s) with
    sides := s.sides ++ [⟨v, true⟩]
    obligations := s.obligations ++ [⟨v, 12⟩] }
def scope (n : Nat) : Bool := n == 1

theorem local_all_terminal_cases (status : Truth) (v : Nat) :
    (Opaque.localOut entry (testOutcome status (prepare entry v))).state.slots 0 = some 7 ∧
    (Opaque.localOut entry (testOutcome status (prepare entry v))).state.slots 1 = none ∧
    (Explicit.localOut entry (testOutcome status (prepare entry v))).state.slots 0 = some 7 ∧
    (Explicit.localOut entry (testOutcome status (prepare entry v))).state.slots 1 = none := by
  cases status <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem host_all_terminal_cases (status : Truth) (v : Nat) :
    value (Opaque.hostOut entry scope 8 (testOutcome status (prepare entry v))) = some 8 ∧
    value (Explicit.hostOut entry scope 8 (testOutcome status (prepare entry v))) = some 8 ∧
    (Explicit.hostOut entry scope 8 (testOutcome status (prepare entry v))).state.slots 1 = some v ∧
    (Explicit.hostOut entry scope 8 (testOutcome status (prepare entry v))).state.slots 2 = none := by
  cases status <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem host_local_vs_cumulative (v : Nat) :
    (Explicit.hostOut entry scope 8 (.live (prepare entry v) ())).state.hosts =
      [⟨4, .f, .f⟩, ⟨8, .t, .t⟩] ∧
    (Explicit.hostOut entry scope 8 (.live (prepare entry v) ())).state.kappa = .f ∧
    (Explicit.hostOut entry scope 8 (.live (prepare entry v) ())).state.chi = .f ∧
    (Opaque.hostOut entry scope 8 (.live (prepare entry v) ())).state.hosts =
      [⟨4, .f, .f⟩, ⟨8, .t, .t⟩] := ⟨rfl, rfl, rfl, rfl⟩

theorem side_and_obligation_once (status : Truth) (v : Nat) :
    (Explicit.hostOut entry scope 8 (testOutcome status (prepare entry v))).state.sides =
      [⟨7, false⟩, ⟨v, true⟩] ∧
    (Opaque.localOut entry (testOutcome status (prepare entry v))).state.obligations =
      [⟨7, 11⟩, ⟨v, 12⟩] := by cases status <;> exact ⟨rfl, rfl⟩

theorem prepared_frame (v : Nat) : Frame entry (prepare entry v) where
  incoming := by
    intro n x old
    by_cases hn : n = 0
    · subst n; simpa [prepare, introduce, entry] using old
    · simp [entry, hn] at old
  sidePrefix := ⟨[⟨v, true⟩], rfl⟩
  hosts := rfl
  kappa := rfl
  chi := rfl
  frames := rfl

def admitted (status : Truth) (v : Nat) : HostUse entry 8 where
  terminal := testOutcome status (prepare entry v)
  frame := by cases status <;> exact prepared_frame v
  fresh := by cases status <;> simp [FreshHost, testOutcome, Outcome.state, prepare, introduce, entry]

theorem admitted_host_parity (status : Truth) (v : Nat) :
    Explicit.finish entry scope 8 (admitted status v) = Opaque.finish entry scope 8 (admitted status v) :=
  Comparison.host_parity _ _ _ _

theorem guarded_neg_actual_projection (status : Truth) (v : Nat) :
    let test := RefTest.introduce 1 v (.result status)
    (test.observe entry).state.slots 1 = some v ∧
    (Explicit.negOut entry (test.observe entry)).state.slots 1 = none ∧
    (Opaque.negOut entry (test.observe entry)).state.slots 1 = none := by
  cases status <;> exact ⟨rfl, rfl, rfl⟩

theorem guarded_neg_results :
    (Explicit.negOut entry ((RefTest.introduce 1 42 (.result .f)).observe entry)).truth = .t ∧
    (Opaque.negOut entry ((RefTest.introduce 1 42 (.result .t)).observe entry)).truth = .f ∧
    (Explicit.negOut entry ((RefTest.introduce 1 42 (.result .u)).observe entry)).truth = .u :=
  ⟨rfl, rfl, rfl⟩

/-- The returned value can be a function. Projection does not force or replace it. -/
theorem local_delayed_value (f : Nat → Nat) :
    value (Explicit.localOut entry (.live (prepare entry 42) f)) = some f ∧
    value (Opaque.localOut entry (.live (prepare entry 42) f)) = some f := ⟨rfl, rfl⟩

def scrub (s : State) (z : Out A) : Out A := mapState (fun _ => s) z
theorem scrub_breaks_local (status : Truth) :
    (scrub entry (testOutcome status (prepare entry 42))).state.sides ≠
      (Opaque.localOut entry (testOutcome status (prepare entry 42))).state.sides ∧
    Explicit.observeOut Explicit.scrubDef entry scope 8 (testOutcome status (prepare entry 42)) =
      scrub entry (testOutcome status (prepare entry 42)) := by
  cases status <;> exact ⟨by decide, rfl⟩

theorem scrub_breaks_host (status : Truth) :
    (Explicit.observeOut Explicit.scrubHostDef entry scope 8
      (testOutcome status (prepare entry 42))).state.slots 1 = none ∧
    (Opaque.hostOut entry scope 8 (testOutcome status (prepare entry 42))).state.slots 1 = some 42 := by
  cases status <;> exact ⟨rfl, rfl⟩

/-- The new consumer has a shared body input, not a second expected-output table. -/
noncomputable def bodyInput (v : Nat) : Run Nat := fun s =>
  NEFin.ofHeadTail (.live (prepare s v) v) [.dead (prepare s (v+1)), .undef (prepare s (v+2))]
theorem extra_consumer_parity (v : Nat) :
    Explicit.exportLocal Explicit.localDef rfl (bodyInput v) = Opaque.bodyLeg (bodyInput v) := by
  funext s
  exact congrArg (fun f => mapResults f (bodyInput v s)) (funext (Comparison.local_parity s))

theorem mixed_family_value_member (v : Nat) :
    .live (prune (support entry) (prepare entry v)) v ∈ Opaque.bodyLeg (bodyInput v) entry := by
  change ∃ z, z ∈ bodyInput v entry ∧
    .live (prune (support entry) (prepare entry v)) v = Opaque.localOut entry z
  exact ⟨.live (prepare entry v) v, by simp [bodyInput], rfl⟩

theorem bind_uses_returned_state_value (s : State) (a : Nat) :
    Explicit.route (fun v current => NEFin.singleton (.live (introduce 9 v current) (v+1)))
      (.live s a) = NEFin.singleton (.live (introduce 9 a s) (a+1)) := rfl

theorem scrub_fails_reviewed_contract : ¬ LocalLaw (fun s z =>
    Explicit.observeOut (Explicit.scrubDef : Explicit.RunDef Unit Unit) s (fun _ => false) 0 z) := by
  intro law
  have eq := law entry (.dead (prepare entry 42))
  have sides := congrArg (fun z : Out Unit => z.state.sides) eq
  change ([⟨7, false⟩] : List (ClosedSide Nat)) = [⟨7, false⟩, ⟨42, true⟩] at sides
  contradiction

theorem scrub_host_fails_reviewed_contract : ¬ HostLaw (Explicit.observeOut Explicit.scrubHostDef) := by
  intro law
  have eq := law entry scope 8 (admitted .f 42)
  have slots := congrArg (fun z : Out Nat => z.state.slots 1) eq
  change (none : Option Nat) = some 42 at slots
  contradiction

theorem named_growth_comparison (v : Nat) :
    Explicit.applyDef (Reviewed.alternateExport : Reviewed.LocalExport Nat).body
      (bodyInput v) (fun _ => false) 0 =
    Opaque.useProjection Opaque.bodyExport (bodyInput v) := by
  funext s
  change mapResults (fun z => Explicit.observeOut Reviewed.twiceDef s (fun _ => false) 0 z) _ = _
  have eq : (fun z => Explicit.observeOut (Reviewed.twiceDef : Explicit.RunDef Nat Nat) s
      (fun _ => false) 0 z) = Opaque.localOut s := funext (fun z => Reviewed.twice_correct s z)
  rw [eq]
  rfl

theorem named_consumer_ordinary (m : Opaque.Term .ref A) :
    Reviewed.observe (.project Reviewed.bodyExport (.base (Comparison.translate m))) =
      Opaque.observe (.project Opaque.bodyExport m) :=
  Comparison.term_parity (.project Opaque.bodyExport m)

def admittedNegative (status : Truth) (v : Nat) : NegativeUse entry :=
  ⟨.introduce 1 v (.result status), ⟨rfl, trivial⟩⟩

theorem admitted_negative_parity (status : Truth) (v : Nat) :
    Reviewed.negative Reviewed.canonicalNegative entry (admittedNegative status v) =
      Opaque.negative entry (admittedNegative status v) := by cases status <;> rfl

theorem scrub_fails_opaque_contract : ¬ LocalLaw (scrub : State → Out Unit → Out Unit) := by
  intro law
  have eq := law entry (.dead (prepare entry 42))
  have sides := congrArg (fun z : Out Unit => z.state.sides) eq
  change ([⟨7, false⟩] : List (ClosedSide Nat)) = [⟨7, false⟩, ⟨42, true⟩] at sides
  contradiction

theorem repeated_occurrence_rejected_opaque :
    ¬ Opaque.Admitted (.host (.pure ()) scope 4) entry := by
  intro ok
  have fresh := (ok.2 (.live entry ()) (by rfl)).2
  have impossible := fresh ⟨4, .f, .f⟩ (by simp [entry, Outcome.state])
  exact impossible rfl

theorem repeated_occurrence_rejected_explicit :
    ¬ Explicit.Admitted (.host (.pure ()) scope 4) entry := by
  intro ok
  have fresh := (ok.2 (.live entry ()) (by rfl)).2
  have impossible := fresh ⟨4, .f, .f⟩ (by simp [entry, Outcome.state])
  exact impossible rfl

theorem repeated_occurrence_rejected_reviewed :
    ¬ Reviewed.Admitted (.host Reviewed.canonicalHost (.base (.pure ())) scope 4) entry := by
  intro ok
  have fresh := (ok.2 (.live entry ()) (by rfl)).2
  have impossible := fresh ⟨4, .f, .f⟩ (by simp [entry, Outcome.state])
  exact impossible rfl

theorem nonprefix_rejected : ¬ Frame entry {entry with sides := []} := by
  intro frame
  obtain ⟨suffix, h⟩ := frame.sidePrefix
  simp [entry] at h

theorem fresh_intro_required : ¬ (RefTest.introduce 0 42 (.result .t)).Admitted entry := by
  simp [RefTest.Admitted, entry]

def operand (status : Truth) : RefTest := .introduce 1 42 (.result status)
theorem operand_host_domain (status : Truth) :
    HostDomain (fun s => NEFin.singleton ((operand status).observe s)) entry 8 := by
  intro z hz
  have same : z = (operand status).observe entry := hz
  subst z
  refine ⟨test_frame _ _, ?_⟩
  intro r hr
  have hist := (test_retains (operand status) entry).2.2.2.1
  rw [hist] at hr
  simp [entry] at hr
  subst r
  decide

def opaqueAdmitted (status : Truth) :
    Opaque.Admitted (.host (.test (operand status)) scope 8) entry :=
  ⟨⟨rfl, trivial⟩, operand_host_domain status⟩
def explicitAdmitted (status : Truth) :
    Explicit.Admitted (.host (.test (operand status)) scope 8) entry :=
  ⟨⟨rfl, trivial⟩, operand_host_domain status⟩
def reviewedAdmitted (status : Truth) :
    Reviewed.Admitted (.host Reviewed.canonicalHost (.base (.test (operand status))) scope 8) entry :=
  ⟨⟨rfl, trivial⟩, operand_host_domain status⟩

theorem admitted_execution (status : Truth) :
    Opaque.run (.host (.test (operand status)) scope 8) entry (opaqueAdmitted status) =
    Explicit.run (.host (.test (operand status)) scope 8) entry (explicitAdmitted status) ∧
    Explicit.run (.host (.test (operand status)) scope 8) entry (explicitAdmitted status) =
    Reviewed.run (.host Reviewed.canonicalHost (.base (.test (operand status))) scope 8)
      entry (reviewedAdmitted status) := by
  constructor
  · exact congrFun (Comparison.term_parity (.host (.test (operand status)) scope 8)).symm entry
  · rfl
end Smusni97.Cases
