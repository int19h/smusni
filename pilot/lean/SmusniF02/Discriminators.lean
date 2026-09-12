import SmusniF02.Host

/-! F02-X01–08: kernel-checked concrete controls in addition to the universal laws.
The small sources/nuclei are explicit toy interpretations, not corpus dispatch.
No test labels are read by any semantic operation. -/
namespace SmusniF02.Controls

/-- Even the construction witnesses do not give sets an order or multiplicity. -/
theorem finite_set_identity (a b : A) :
    NEFin.ofHeadTail a [b, a] = NEFin.ofHeadTail b [a] := by
  ext x
  simp only [NEFin.mem_ofHeadTail, List.mem_cons, List.not_mem_nil, or_false]
  constructor <;> intro h
  · rcases h with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inr h
  · rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

abbrev S := HostState Nat Nat Nat Nat
def initial : S := ⟨fun _ => none, [], [], .t, .t⟩
def reachedPrefix (n : Nat) : S :=
  { initial with assignment := fun name => if name = 0 then some n else none
                 sides := [⟨n, true⟩] }
def failAfter (n : Nat) : Terminal S Unit := NEFin.singleton (.dead (reachedPrefix n))

theorem X01_equal_success_projection : Run.successes (failAfter 1) = Run.successes (failAfter 2) := by
  funext p
  simp [Run.successes, failAfter]

theorem X01_different_return :
    Host.finalize initial (fun _ => true) 0 (.dead (reachedPrefix 1) : Outcome S Unit) ≠
    Host.finalize initial (fun _ => true) 0 (.dead (reachedPrefix 2) : Outcome S Unit) := by
  intro h
  have hv := congrArg (fun z : Outcome S Nat => z.state.assignment 0) h
  simp [Host.finalize, Host.finalizeState, Host.keep, Outcome.state, initial, reachedPrefix] at hv

/-- A universal impossibility theorem, witnessed by two concrete legal prefixes. -/
theorem X01_no_success_factor :
    ¬ ∃ f : ((S × Unit) → Prop) → Outcome S Nat,
      ∀ z : Outcome S Unit,
        f (Run.successes (NEFin.singleton z)) = Host.finalize initial (fun _ => true) 0 z := by
  rintro ⟨f, hf⟩
  apply X01_different_return
  rw [← hf (.dead (reachedPrefix 1)), ← hf (.dead (reachedPrefix 2))]
  exact congrArg f X01_equal_success_projection

theorem prefix_legal (n : Nat) : Host.LegalFrame initial (reachedPrefix n) where
  incoming := by intro name v h; simp [initial] at h
  sidePrefix := ⟨[⟨n, true⟩], rfl⟩
  history := rfl
  kappa := rfl
  chi := rfl

def optionalReference : SourceResult R → Option R
  | .obtained r => some r
  | .empty | .unresolved => none

theorem X01_optional_loses_tag :
    optionalReference (.empty : SourceResult Nat) = optionalReference .unresolved ∧
    readOutcome .first (.empty : SourceResult Nat) 7 ≠ readOutcome .first .unresolved 7 := by
  constructor
  · rfl
  · decide

/-- Infinite profile space is intentional; 0 is empty, positive profiles permit selection. -/
def toySource (p : Nat) (sourceWorld : Bool) : Terminal S Nat :=
  if sourceWorld && (p != 0) then
    NEFin.ofHeadTail (.live (reachedPrefix 0) 0) [.live (reachedPrefix 1) 1]
  else NEFin.singleton (.dead (reachedPrefix 2))

abbrev I := Origin toySource
def K (p : Nat) (i : I p) : SourceResult Nat := i.result
def outer (p : Nat) (i : I p) : Bool := i.parent
def emptyOrigin : I 1 := ⟨false, .dead (reachedPrefix 2), by simp [toySource]⟩
def obtainedOrigin (n : Nat) (hn : n = 0 ∨ n = 1) : I 1 :=
  ⟨true, .live (reachedPrefix n) n, by
    rcases hn with rfl | rfl <;> simp [toySource]⟩
def profileZeroOrigin : I 0 := ⟨true, .dead (reachedPrefix 2), by simp [toySource]⟩

/-- Inherited outer parameter is available but not needed by this nucleus.
Current world, context and beta are separate inputs; none is the source outcome. -/
def nucleus (test : Nat → Bool → Bool → Bool) (r : Nat) :
    Content Nat (fun _ => Bool) Bool Bool S Bool Nat where
  run _ _ e w s := NEFin.singleton (if test r e w then .live s () else .dead s)
  event _ _ _ _ beta := some (if beta then 20 else 10)

noncomputable def constantPayload := payload .first K outer (nucleus (fun _ _ _ => true))

theorem X02_origin_distinction (s : S) (e w : Bool) :
    constantPayload.run 1 emptyOrigin e w s ≠
      constantPayload.run 1 (obtainedOrigin 0 (Or.inl rfl)) e w s := by
  intro h
  have he := congrArg (fun zs : Terminal S Unit => .dead s ∈ zs) h
  simp [constantPayload, payload, Family.bind, Family.pull, reads, read, readOutcome,
    K, emptyOrigin, obtainedOrigin, Origin.result, Outcome.result, Run.bind,
    Run.extend, nucleus] at he

theorem X02_no_origin_erasure (s : S) (e w : Bool) :
    ¬ ∃ f : Bool → S → Terminal S Unit,
      ∀ i : I 1, constantPayload.run 1 i e w s = f w s := by
  rintro ⟨f, hf⟩
  exact X02_origin_distinction s e w ((hf emptyOrigin).trans
    (hf (obtainedOrigin 0 (Or.inl rfl))).symm)

theorem X03_false_run_distinct_beta (s : S) :
    (nucleus (fun _ _ _ => false) 0).run 1 true false false s = NEFin.singleton (.dead s) ∧
    (nucleus (fun _ _ _ => false) 0).event 1 true false false false = some 10 ∧
    (nucleus (fun _ _ _ => false) 0).event 1 true false false true = some 20 := by
  exact ⟨rfl, rfl, rfl⟩

def falseEvent (event : Nat) : Content Nat (fun _ => Bool) Bool Bool S Bool Nat :=
  { nucleus (fun _ _ _ => false) 0 with event := fun _ _ _ _ _ => some event }

theorem X03_run_equality_not_content_equality :
    (falseEvent 10).run = (falseEvent 20).run ∧
    ¬ Content.ObsEq Eq (falseEvent 10) (falseEvent 20) := by
  refine ⟨rfl, ?_⟩
  intro h
  have he := h.2 0 false false false false
  simp [falseEvent, PartialEq] at he

theorem X03_payload_false_event (phase : ReadPhase) (s : S) :
    (payload phase K outer (nucleus (fun _ _ _ => false))).run
      1 (obtainedOrigin 0 (Or.inl rfl)) false false s = NEFin.singleton (.dead s) ∧
    (payload phase K outer (nucleus (fun _ _ _ => false))).event
      1 (obtainedOrigin 0 (Or.inl rfl)) false false true = some 20 := by
  constructor
  · rw [payload_obtained_run phase K outer _ 1 _ 0 rfl]; rfl
  · rfl

theorem X03_no_value_events (phase : ReadPhase) (k : SourceResult Nat)
    (h : ∀ r, k ≠ .obtained r) :
    (payload phase (fun (_ : Nat) (_ : Unit) => k) (fun _ _ => true)
      (nucleus (fun _ _ _ => true))).event 0 () false true true = none := by
  apply payload_no_value_event
  exact h

theorem X04_constant_replay (s : S) :
    constantPayload.run 1 (obtainedOrigin 0 (Or.inl rfl)) false false s =
      NEFin.singleton (.live s ()) := by
  unfold constantPayload
  rw [payload_obtained_run .first K outer _ 1 _ 0 rfl]; rfl

theorem X04_world_sensitive_replay (s : S) :
    (payload .first K outer (nucleus (fun _ _ w => w))).run
      1 (obtainedOrigin 0 (Or.inl rfl)) false false s = NEFin.singleton (.dead s) ∧
    (payload .first K outer (nucleus (fun _ _ w => w))).run
      1 (obtainedOrigin 0 (Or.inl rfl)) false true s = NEFin.singleton (.live s ()) := by
  constructor <;> rw [payload_obtained_run .first K outer _ 1 _ 0 rfl] <;> rfl

theorem X04_empty_replay (s : S) (test : Nat → Bool → Bool → Bool) :
    (payload .first K outer (nucleus test)).run 1 emptyOrigin false true s =
      NEFin.singleton (.dead s) := by
  simp [payload, Family.bind, Family.pull, reads, read, readOutcome, K, emptyOrigin,
    Origin.result, Outcome.result, Run.bind, Run.extend]

theorem X05_profiles_not_alternatives (s : S) :
    constantPayload.run 0 profileZeroOrigin false true s = NEFin.singleton (.dead s) ∧
    constantPayload.run 1 (obtainedOrigin 0 (Or.inl rfl)) false true s =
      NEFin.singleton (.live s ()) := by
  constructor
  · simp [constantPayload, payload, Family.bind, Family.pull, reads, read, readOutcome,
      K, profileZeroOrigin, Origin.result, Outcome.result, Run.bind, Run.extend]
  · unfold constantPayload
    rw [payload_obtained_run .first K outer _ 1 _ 0 rfl]; rfl

def emittingNucleus (r : Nat) : Content Nat (fun _ => Bool) Bool Bool S Bool Nat where
  run _ _ e _ s := NEFin.singleton (.live {s with sides := s.sides ++ [⟨r, e⟩]} ())
  event _ _ _ _ beta := some (if beta then 20 else 10)

theorem X06_capture_caller_and_sides (s : S) :
    (Content.capture true (payload .first K outer emittingNucleus)).run
      1 (obtainedOrigin 0 (Or.inl rfl)) false false s =
        NEFin.singleton (.live {s with sides := s.sides ++ [⟨0, true⟩]} ()) := by
  change (payload .first K outer emittingNucleus).run
    1 (obtainedOrigin 0 (Or.inl rfl)) true false s = _
  rw [payload_obtained_run .first K outer _ 1 _ 0 rfl]; rfl

theorem X06_raw_captured_context (s : S) :
    (Content.capture true (payload .first K outer (nucleus (fun _ e _ => e)))).run
      1 (obtainedOrigin 0 (Or.inl rfl)) false false s = NEFin.singleton (.live s ()) ∧
    (payload .first K outer (nucleus (fun _ e _ => e))).run
      1 (obtainedOrigin 0 (Or.inl rfl)) false false s = NEFin.singleton (.dead s) := by
  constructor
  · change (payload .first K outer (nucleus (fun _ e _ => e))).run
      1 (obtainedOrigin 0 (Or.inl rfl)) true false s = _
    rw [payload_obtained_run .first K outer _ 1 _ 0 rfl]; rfl
  · rw [payload_obtained_run .first K outer _ 1 _ 0 rfl]; rfl

theorem X06_saved_resolver_undefined (saved caller : Nat → Option Nat) (d : Nat) (s : S)
    (h : saved d = none) :
    Family.capture saved resolverFamily () d caller () s = NEFin.singleton (.undef s) := by
  rw [capture_full_resolver, h]

noncomputable def firstHost (p : Nat) (i : I p) : Terminal S Nat :=
  Host.finalizeAll initial (fun _ => true) 100
    (firstExecution toySource (fun _ b => b) true (payload .first K outer emittingNucleus).run p i)

/-- Supplied later source interpretation: consumes the first returned ground binding.
This example is not a general multi-source-failure performance semantics. -/
def nextSource (s : S) : Terminal S Nat :=
  match s.assignment 0 with
  | none => NEFin.singleton (.dead s)
  | some 0 => NEFin.singleton (.live s 30)
  | some 1 => NEFin.ofHeadTail (.live s 40) [.live s 41]
  | some _ => NEFin.singleton (.undef s)

abbrev Children (p : Nat) (i : I p) :=
  (z : {z : Outcome S Nat // z ∈ firstHost p i}) ×
    {t : Outcome S Nat // t ∈ nextSource z.val.state}
abbrev Child (p : Nat) := Descendant I Children p

theorem children_nonempty (p : Nat) (i : I p) : Nonempty (Children p i) := by
  obtain ⟨z, hz⟩ := (firstHost p i).inhabited
  obtain ⟨t, ht⟩ := (nextSource z.state).inhabited
  exact ⟨⟨⟨z, hz⟩, t, ht⟩⟩

/-- A genuinely dependent grandchild fibre, supplied from its immediate child's state. -/
abbrev Grandchildren (p : Nat) (j : Child p) :=
  {t : Outcome S Nat // t ∈ nextSource j.2.2.val.state}
abbrev Grandchild (p : Nat) := Descendant Child Grandchildren p

theorem grandchildren_nonempty (p : Nat) (j : Child p) : Nonempty (Grandchildren p j) := by
  obtain ⟨t, ht⟩ := (nextSource j.2.2.val.state).inhabited
  exact ⟨⟨t, ht⟩⟩

noncomputable def nextAlternatives (p : Nat) (i : I p) : Terminal S Nat :=
  (firstHost p i).unionMap (fun z => nextSource z.state)

def afterNucleus (n : Nat) : S :=
  { reachedPrefix n with sides := (reachedPrefix n).sides ++ [⟨n, true⟩] }
def returned (n : Nat) : S := Host.finalizeState initial (fun _ => true) 100
  (.live (afterNucleus n) () : Outcome S Unit)

theorem firstHost_obtained (n : Nat) (hn : n = 0 ∨ n = 1) :
    firstHost 1 (obtainedOrigin n hn) = NEFin.singleton (.live (returned n) 100) := by
  unfold firstHost firstExecution
  rw [payload_obtained_run .first K outer _ 1 _ n rfl]
  simp [emittingNucleus, obtainedOrigin, Origin.reached, Outcome.state, Host.finalizeAll,
    Host.finalize, returned, afterNucleus]

theorem X06_first_source_side_once (n : Nat) (hn : n = 0 ∨ n = 1) :
    firstHost 1 (obtainedOrigin n hn) = NEFin.singleton (.live (returned n) 100) ∧
    (returned n).sides = [⟨n, true⟩, ⟨n, true⟩] := by
  exact ⟨firstHost_obtained n hn, rfl⟩

theorem X07_dependent_one_two :
    nextAlternatives 1 (obtainedOrigin 0 (Or.inl rfl)) =
      NEFin.singleton (.live (returned 0) 30) ∧
    nextAlternatives 1 (obtainedOrigin 1 (Or.inr rfl)) =
      NEFin.ofHeadTail (.live (returned 1) 40) [.live (returned 1) 41] := by
  constructor <;> unfold nextAlternatives <;> rw [firstHost_obtained] <;>
    simp [nextSource, returned, Host.finalizeState, Host.keep,
      initial, afterNucleus, reachedPrefix, Outcome.state]

theorem X07_dependent_failure :
    nextSource initial = NEFin.singleton (.dead initial) ∧
    nextSource (reachedPrefix 2) = NEFin.singleton (.undef (reachedPrefix 2)) := by
  exact ⟨rfl, rfl⟩

theorem X07_child_read (phase : ReadPhase) :
    Family.pull (parent (I := I) (L := Children)) (reads phase K : Family Nat I Bool Bool S Nat) =
      reads phase (fun p j => K p j.1) := rfl

theorem X07_composed_read (phase : ReadPhase) :
    Family.pull (parent (I := Child) (L := Grandchildren))
      (Family.pull (parent (I := I) (L := Children))
        (reads phase K : Family Nat I Bool Bool S Nat)) =
      reads phase (fun p (j : Grandchild p) => K p j.1.1) := rfl

theorem X07_child_bind (m : Family Nat I Bool Bool S Nat)
    (k : Nat → Family Nat I Bool Bool S Unit) :
    Family.pull (parent (I := I) (L := Children)) (Family.bind m k) =
      Family.bind (Family.pull parent m) (fun r => Family.pull parent (k r)) := rfl

def priorFalse : S :=
  { initial with sides := [⟨7, false⟩]
                 history := [⟨10, .f, .f⟩]
                 kappa := .f
                 chi := .f }
def newTrue : S := { priorFalse with sides := priorFalse.sides ++ [⟨8, true⟩] }

theorem X08_local_true_cumulative_false :
    Host.currentSideTruth priorFalse newTrue = .t ∧
    (Host.finalizeState priorFalse (fun _ => false) 11 (.live newTrue ())).history =
      [⟨10, .f, .f⟩, ⟨11, .t, .t⟩] ∧
    (Host.finalizeState priorFalse (fun _ => false) 11 (.live newTrue ())).kappa = .f ∧
    (Host.finalizeState priorFalse (fun _ => false) 11 (.live newTrue ())).chi = .f ∧
    (Host.finalizeState priorFalse (fun _ => false) 11 (.live newTrue ())).sides =
      [⟨7, false⟩, ⟨8, true⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem X08_legal_frame : Host.LegalFrame priorFalse newTrue where
  incoming := by intro name v h; exact h
  sidePrefix := ⟨[⟨8, true⟩], rfl⟩
  history := rfl
  kappa := rfl
  chi := rfl

end SmusniF02.Controls
