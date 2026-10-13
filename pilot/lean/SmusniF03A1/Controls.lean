import SmusniF03A1.Families

/-! Algebraic controls only. These are neither the A2 descriptor instance nor a
model of Lojban. General maps and transport never dispatch on these examples. -/
namespace SmusniF03A1.Controls
open SmusniF02

def parity : Setoid Nat where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem representative_change (p q : Nat) (same : p % 2 = q % 2) :
    qValue (G := Nat) parity (.inr p) = qValue parity (.inr q) :=
  (tag_kernel parity _ _).mpr same

theorem distinct_class : qValue (G := Nat) parity (.inr 0) ≠ qValue parity (.inr 1) := by
  intro eq
  have h := (tag_kernel parity _ _).mp eq
  exact (by decide : ¬(0 % 2 = 1 % 2)) h

theorem distinct_tags (R : Setoid P) (g : G) (p : P) :
    qValue R (.inl g) ≠ qValue R (.inr p) := by simp [qValue, qTag]

theorem order_retained (R : Setoid P) (g : G) (p : P) :
    [ClosedSide.mk (.inl g) true, ⟨.inr p, false⟩].map (mapSide (qAnchor R)) ≠
      [ClosedSide.mk (.inr p) false, ⟨.inl g, true⟩].map (mapSide (qAnchor R)) := by
  simp [mapSide, qAnchor, qTag]

theorem truth_bit_retained (R : Setoid P) (p : P) :
    mapSide (qAnchor (G := G) R) ⟨.inr p, true⟩ ≠ mapSide (qAnchor R) ⟨.inr p, false⟩ := by
  simp [mapSide]

/-- Related proposition anchors identify through the whole state map without
changing the existing side prefix or the new side's truth bit. -/
theorem related_side_anchors
    (R : Setoid P) (s : RawState N G GA P H)
    (p q : P) (related : R.r p q) (bit : Bool) :
    qState R { s with sides := s.sides ++ [⟨.inr p, bit⟩] } =
      qState R { s with sides := s.sides ++ [⟨.inr q, bit⟩] } := by
  have eq : Quotient.mk R p = Quotient.mk R q := Quotient.sound related
  simp [qState, mapState, mapSide, qAnchor, qTag, eq]

def initial : RawState Nat Nat Nat Nat Nat := ⟨fun _ => none, [], [], .t, .t⟩
def oneSlot (p : Nat) : RawState Nat Nat Nat Nat Nat := putSlot 0 (some (.inr p)) initial

theorem oneSlot_same_image : qState parity (oneSlot 0) = qState parity (oneSlot 2) := by
  change mapState _ _ (putSlot _ _ _) = mapState _ _ (putSlot _ _ _)
  rw [map_putSlot, map_putSlot]
  congr 1
  exact congrArg some (representative_change 0 2 (by decide))

/-- Quotient equality cannot be substituted for raw incoming-binding equality. -/
theorem legal_frame_not_reflected :
    Host.LegalFrame (qState parity (oneSlot 0)) (qState parity (oneSlot 2)) ∧
    ¬Host.LegalFrame (oneSlot 0) (oneSlot 2) := by
  constructor
  · rw [oneSlot_same_image]
    exact ⟨fun _ _ h => h, ⟨[], by simp⟩, rfl, rfl, rfl⟩
  · intro legal
    have h := legal.incoming 0 (.inr 0) (by simp [oneSlot, putSlot])
    simp [oneSlot, putSlot] at h

theorem suffix_ignores_old_failure :
    let entry : RawState Nat Nat Nat Nat Nat := { initial with sides := [⟨.inl 7, false⟩] }
    let reached := { entry with sides := entry.sides ++ [⟨.inr 2, true⟩] }
    Host.currentSideTruth (qState parity entry) (qState parity reached) = .t := by
  dsimp
  simp only [qState, suffix_truth]
  rfl

/-- Entire families, not successful-only projections, pass through quotient maps. -/
theorem failure_tags_retained (R : Setoid P) (AR : Setoid A) (s : RawState N G GA P H) :
    qOutcome R AR (.dead s) ≠ qOutcome R AR (.undef s) := by
  simp [qOutcome, mapOutcome]

/-- Direct image retains both success and failure, even if their states identify. -/
theorem mixed_live_dead_image
    (R : Setoid P) (AR : Setoid A)
    (s t : RawState N G GA P H) (a : A) :
    mapResults (qOutcome R AR)
        (NEFin.ofHeadTail (.live s a) [.dead t]) =
      NEFin.ofHeadTail
        (.live (qState R s) (Quotient.mk AR a))
        [.dead (qState R t)] := by
  ext z
  simp [qOutcome, mapOutcome]

theorem two_equivalent_outputs_collapse :
    mapResults (Quotient.mk parity) (NEFin.ofHeadTail 0 [2]) = NEFin.singleton (Quotient.mk parity 0) := by
  have eq : Quotient.mk parity 2 = Quotient.mk parity 0 := Quotient.sound rfl
  ext q
  simp [eq]

/-- A raw label test violates the continuation premise of general Bind transport. -/
def distinguish (n : Nat) : Run Unit Unit := fun s =>
  if n = 0 then NEFin.singleton (.live s ()) else NEFin.singleton (.dead s)

theorem bind_body_premise_needed :
    RunRel Eq parity.r (Run.pure 0 : Run Unit Nat) (Run.pure 2) ∧
    ¬RunRel Eq Eq (Run.bind (Run.pure 0) distinguish) (Run.bind (Run.pure 2) distinguish) := by
  constructor
  · exact pure_compatible Eq parity.r 0 2 rfl
  · intro rel
    have h := (rel () () rfl).1 (.live () ()) (by simp [Run.pure_bind, distinguish])
    obtain ⟨z, hz, hrel⟩ := h
    simp only [Run.pure_bind, distinguish, show ¬(2 = 0) from by decide, if_false,
      NEFin.mem_singleton] at hz
    subst z
    exact hrel

def savedResolver (n : Nat) : Option Nat := if n = 0 then some 0 else none
def changedResolver (n : Nat) : Option Nat := if n = 0 then some 0 else some 2

theorem visited_tuple_insufficient :
    savedResolver 0 = changedResolver 0 ∧
    ¬ResolverRel Eq parity.r savedResolver changedResolver := by
  constructor
  · rfl
  · intro rel
    have h := rel 1 1 rfl
    simp [savedResolver, changedResolver, OptionRel] at h

def saved : ResolverEnv Nat Nat Nat := ⟨7, savedResolver⟩
def caller : ResolverEnv Nat Nat Nat := ⟨8, changedResolver⟩

theorem capture_uses_saved_unvisited_tuple :
    Family.capture saved (queryFamily (S := Unit)) () 1 caller () () = NEFin.singleton (.undef ()) := by
  simp [Family.capture, queryFamily, saved, lookup, savedResolver]

theorem other_context_fields_matter :
    ¬EnvRel Eq parity.r (ResolverEnv.mk 7 savedResolver) (ResolverEnv.mk 8 savedResolver) := by
  intro rel
  exact (by decide : ¬(7 = 8)) rel.1

theorem arbitrary_quotient_state_covered (R : Setoid P) (s : QuotientState N G GA P H R) :
    ∃ raw, qState R raw = s := qState_onto R s

/-- A uniform integration control over every declared source state and slot. -/
theorem arbitrary_slot_descends (R : Setoid P) (s : RawState N G GA P H) (n : N) :
    descend (qState R) (qState_onto R) (qValue R)
      ⟨lookupSlot n, lookupSlot_compatible (ValueRel R) (AnchorRel R) n⟩ (qState R s) =
      lookupSlot n (qState R s) := descend_lookupSlot R s n

theorem changed_state_is_used (entry reached : S) (a : A) (k : A → Run S B) :
    Run.bind (fun _ => NEFin.singleton (.live reached a)) k entry = k a reached := by
  simp [Run.bind, Run.extend]
end SmusniF03A1.Controls
