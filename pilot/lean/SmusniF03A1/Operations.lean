import SmusniF03A1.Runs

namespace SmusniF03A1
open SmusniF02

theorem map_pure (fs : S → T) (fa : A → B) (a : A) (s : S) :
    mapResults (mapOutcome fs fa) (Run.pure a s) = Run.pure (fa a) (fs s) := by
  simp [Run.pure, mapOutcome]

def SourceRel (R : A → B → Prop) : SourceResult A → SourceResult B → Prop
  | .obtained a, .obtained b => R a b
  | .empty, .empty | .unresolved, .unresolved => True
  | _, _ => False

def mapSource (f : A → B) : SourceResult A → SourceResult B
  | .obtained a => .obtained (f a)
  | .empty => .empty
  | .unresolved => .unresolved

theorem read_compatible (SR : S → T → Prop) (AR : A → B → Prop) (phase : ReadPhase)
    (a : SourceResult A) (b : SourceResult B) (rel : SourceRel AR a b) :
    RunRel SR AR (read phase a) (read phase b) := by
  intro s t hst
  apply finRel_singleton
  cases a <;> cases b <;> cases phase <;> simp_all [SourceRel, readOutcome, OutRel]

theorem map_read (fs : S → T) (fa : A → B) (phase : ReadPhase) (source : SourceResult A) (s : S) :
    mapResults (mapOutcome fs fa) (read phase source s) = read phase (mapSource fa source) (fs s) := by
  cases source <;> cases phase <;> simp [SmusniF02.read, readOutcome, mapOutcome, mapSource]

/-- Resolver outputs must match in definedness and be related at this input. -/
theorem lookup_compatible (SR : S → T → Prop) (AR : A → B → Prop)
    (resolve : D → Option A) (resolve' : D' → Option B) (d : D) (d' : D')
    (rel : OptionRel AR (resolve d) (resolve' d')) :
    RunRel SR AR (lookup resolve d) (lookup resolve' d') := by
  intro s t hst
  apply finRel_singleton
  cases h : resolve d <;> cases h' : resolve' d' <;> simp_all [OptionRel, OutRel]

theorem map_lookup (fs : S → T) (fa : A → B) (resolve : D → Option A) (d : D) (s : S) :
    mapResults (mapOutcome fs fa) (lookup resolve d s) =
      lookup (fun x => (resolve x).map fa) d (fs s) := by
  cases h : resolve d <;> simp [lookup, h, mapOutcome]

/-- A typed slot read uses the actual F02 partial lookup at the current state. -/
def lookupSlot (n : N) : Run (HostState N V A H) V := fun s => lookup s.assignment n s

def putSlot [DecidableEq N] (n : N) (value : Option V) (s : HostState N V A H) : HostState N V A H :=
  { s with assignment := fun key => if key = n then value else s.assignment key }

/-- A supplied mask projects assignments only. It does not decide accessibility. -/
def projectAssignment (mask : N → Bool) (s : HostState N V A H) : HostState N V A H :=
  { s with assignment := fun n => if mask n then s.assignment n else none }

theorem assignment_projection (fv : V → V') (fa : A → A') (s : HostState N V A H) (n : N) :
    (mapState fv fa s).assignment n = (s.assignment n).map fv := rfl

theorem map_lookupSlot (fv : V → V') (fa : A → A') (s : HostState N V A H) (n : N) :
    mapResults (mapOutcome (mapState fv fa) fv) (lookupSlot n s) =
      lookupSlot n (mapState fv fa s) := map_lookup _ _ s.assignment n s

theorem lookupSlot_compatible (VR : V → V' → Prop) (AR : A → A' → Prop) (n : N) :
    RunRel (StateRel (H := H) VR AR) VR (lookupSlot n) (lookupSlot n) := by
  intro s t hst
  exact lookup_compatible _ _ s.assignment t.assignment n n (hst.1 n) s t hst

theorem map_putSlot [DecidableEq N] (fv : V → V') (fa : A → A') (n : N)
    (value : Option V) (s : HostState N V A H) :
    mapState fv fa (putSlot n value s) = putSlot n (value.map fv) (mapState fv fa s) := by
  apply state_ext
  · funext key; by_cases h : key = n <;> simp [mapState, putSlot, h]
  all_goals rfl

theorem putSlot_compatible [DecidableEq N] (VR : V → V' → Prop) (AR : A → A' → Prop)
    (n : N) (v : Option V) (w : Option V') (s : HostState N V A H) (t : HostState N V' A' H)
    (states : StateRel VR AR s t) (values : OptionRel VR v w) :
    StateRel VR AR (putSlot n v s) (putSlot n w t) := by
  refine ⟨?_, states.2⟩
  intro key
  by_cases h : key = n
  · simpa [putSlot, h] using values
  · simpa [putSlot, h] using states.1 key

theorem map_projectAssignment (fv : V → V') (fa : A → A') (mask : N → Bool) (s : HostState N V A H) :
    mapState fv fa (projectAssignment mask s) = projectAssignment mask (mapState fv fa s) := by
  apply state_ext
  · funext n; cases h : mask n <;> simp [mapState, projectAssignment, h]
  all_goals rfl

theorem projectAssignment_compatible (VR : V → V' → Prop) (AR : A → A' → Prop)
    (mask : N → Bool) (s : HostState N V A H) (t : HostState N V' A' H) (rel : StateRel VR AR s t) :
    StateRel VR AR (projectAssignment mask s) (projectAssignment mask t) := by
  refine ⟨?_, rel.2⟩
  intro n
  cases h : mask n
  · simp [projectAssignment, h, OptionRel]
  · simpa [projectAssignment, h] using rel.1 n

@[simp] theorem mapSide_holds (fa : A → B) (side : ClosedSide A) : (mapSide fa side).holds = side.holds := rfl
theorem side_length (fa : A → B) (sides : List (ClosedSide A)) :
    (sides.map (mapSide fa)).length = sides.length := List.length_map _
theorem side_prefix (fa : A → B) (before after : List (ClosedSide A))
    (isPrefix : ∃ suffix, after = before ++ suffix) :
    ∃ suffix, after.map (mapSide fa) = before.map (mapSide fa) ++ suffix := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  exact ⟨suffix.map (mapSide fa), by simp⟩

theorem sideTruth_map (fa : A → B) (sides : List (ClosedSide A)) :
    Host.sideTruth (sides.map (mapSide fa)) = Host.sideTruth sides := by
  simp [Host.sideTruth, Function.comp_def]

theorem suffix_truth (fv : V → V') (fa : A → A') (entry terminal : HostState N V A H) :
    Host.currentSideTruth (mapState fv fa entry) (mapState fv fa terminal) =
      Host.currentSideTruth entry terminal := by
  simp [Host.currentSideTruth, mapState, ← List.map_drop, sideTruth_map]

theorem map_keep (fv : V → V') (fa : A → A') (entry terminal : HostState N V A H) (eligible : N → Bool) :
    mapState fv fa (Host.keep entry terminal eligible) =
      Host.keep (mapState fv fa entry) (mapState fv fa terminal) eligible := by
  apply state_ext
  · funext n; cases h : entry.assignment n <;> cases he : eligible n <;> simp [mapState, Host.keep, h, he]
  all_goals rfl

/-- Forward image of a raw legal frame, not transport through arbitrary related states. -/
theorem legalFrame_image (fv : V → V') (fa : A → A') (entry terminal : HostState N V A H)
    (legal : Host.LegalFrame entry terminal) : Host.LegalFrame (mapState fv fa entry) (mapState fv fa terminal) := by
  constructor
  · intro n value h
    cases old : entry.assignment n with
    | none => simp [mapState, old] at h
    | some v => simpa only [mapState, legal.incoming n v old, old, Option.map_some] using h
  · exact side_prefix fa _ _ legal.sidePrefix
  · exact legal.history
  · exact legal.kappa
  · exact legal.chi

/-- Arbitrary value/anchor maps commute with the actual F02 finalizer. -/
theorem finalize_commutes (fv : V → V') (fa : A → A') (fb : B → B')
    (entry : HostState N V A H) (eligible : N → Bool) (handle : H) (z : Outcome (HostState N V A H) B) :
    mapState fv fa (Host.finalizeState entry eligible handle z) =
      Host.finalizeState (mapState fv fa entry) eligible handle (mapOutcome (mapState fv fa) fb z) := by
  have keep := map_keep fv fa entry z.state eligible
  have side := suffix_truth fv fa entry z.state
  simp only [mapState] at side
  apply state_ext
  · have h := congrArg (fun s : HostState N V' A' H => s.assignment) keep
    simpa only [Host.finalizeState, mapState, mapOutcome_state] using h
  · simp [Host.finalizeState, mapState, Host.keep]
  · simp [Host.finalizeState, mapState, side]
  · simp [Host.finalizeState, mapState]
  · simp [Host.finalizeState, mapState, side]

theorem qFinalize_commutes (R : Setoid P) (AR : Setoid B)
    (entry : RawState N G GA P H) (eligible : N → Bool) (handle : H) (z : Outcome (RawState N G GA P H) B) :
    qState R (Host.finalizeState entry eligible handle z) =
      Host.finalizeState (qState R entry) eligible handle (qOutcome R AR z) :=
  finalize_commutes _ _ _ entry eligible handle z

theorem qLegalFrame_image (R : Setoid P) (entry terminal : RawState N G GA P H)
    (legal : Host.LegalFrame entry terminal) : Host.LegalFrame (qState R entry) (qState R terminal) :=
  legalFrame_image _ _ entry terminal legal

/-- The generic descent mechanism computes the actual lookup on quotient states. -/
theorem descend_lookupSlot (R : Setoid P) (s : RawState N G GA P H) (n : N) :
    descend (qState R) (qState_onto R) (qValue R)
      ⟨lookupSlot n, lookupSlot_compatible (ValueRel R) (AnchorRel R) n⟩ (qState R s) =
      lookupSlot n (qState R s) := by
  rw [descend_at _ _ _ (qState_kernel R) (tag_kernel R)]
  exact map_lookupSlot _ _ s n
end SmusniF03A1
