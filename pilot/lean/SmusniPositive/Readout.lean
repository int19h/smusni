import SmusniPositive.Respect

namespace SmusniPositive
open SmusniF02
universe u v
variable {sig : Signature.{u}} {W : Type v}

noncomputable def value (M : Model sig W) (c : Code sig) (i : Input sig W) : Truth := by
  classical
  exact if Evidence M c i true then .t else if Evidence M c i false then .f else .u

def boolTruth : Bool → Truth | true => .t | false => .f
def negSK : Truth → Truth | .t => .f | .f => .t | .u => .u

theorem value_true (M : Model sig W) (c i) : value M c i = .t ↔ Evidence M c i true := by
  classical
  by_cases ht : Evidence M c i true <;> by_cases hf : Evidence M c i false <;> simp [value, ht, hf]

theorem value_false (M : Model sig W) (c i) : value M c i = .f ↔ Evidence M c i false := by
  classical
  by_cases ht : Evidence M c i true
  · have hf : ¬Evidence M c i false := consistent ht
    simp [value, ht, hf]
  · simp [value, ht]

theorem value_undefined (M : Model sig W) (c i) :
    value M c i = .u ↔ ¬Evidence M c i true ∧ ¬Evidence M c i false := by
  classical
  by_cases ht : Evidence M c i true <;> by_cases hf : Evidence M c i false <;> simp [value, ht, hf]

theorem evidence_value (M : Model sig W) (c i b) : Evidence M c i b ↔ value M c i = boolTruth b := by
  cases b
  · exact (value_false M c i).symm
  · exact (value_true M c i).symm

theorem value_congr (M : Model sig W) {c d i j} (h : ∀ b, Evidence M c i b ↔ Evidence M d j b) :
    value M c i = value M d j := by
  classical
  simp only [value, h]

theorem truth_ext (a b : Truth) (ht : a = .t ↔ b = .t) (hf : a = .f ↔ b = .f) : a = b := by
  cases a <;> cases b <;> simp_all

@[simp] theorem negSK_true (a : Truth) : negSK a = .t ↔ a = .f := by cases a <;> simp [negSK]
@[simp] theorem negSK_false (a : Truth) : negSK a = .f ↔ a = .t := by cases a <;> simp [negSK]
@[simp] theorem negSK_twice (a : Truth) : negSK (negSK a) = a := by cases a <;> rfl
theorem negSK_fixed (a : Truth) : a = negSK a ↔ a = .u := by cases a <;> simp [negSK]

variable (M : Model sig W)
variable {m n : Nat} (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W)

theorem value_top : value M (.mk (.top : Term sig m n) g r) i = .t :=
  (value_true _ _ _).mpr .top
theorem value_bot : value M (.mk (.bot : Term sig m n) g r) i = .f :=
  (value_false _ _ _).mpr .bot
theorem value_atom (a : sig.Predicate) (args : Fin (sig.predicateArity a) → GroundTerm sig.Ground m) :
    value M (.mk (.atom a args : Term sig m n) g r) i = boolTruth (M.lexical a i.world (evalGround args g)) :=
  (evidence_value _ _ _ _).mp (.atom a args)

theorem value_neg (t : Term sig m n) :
    value M (.mk (.neg t) g r) i = negSK (value M (.mk t g r) i) := by
  apply truth_ext
  · rw [value_true, negSK_true, value_false, evidence_fixed]
    rfl
  · rw [value_false, negSK_false, value_true, evidence_fixed]
    rfl

theorem value_holdsVar (x : Fin n) : value M (.mk (.holdsVar x : Term sig m n) g r) i = value M (r x) i := by
  apply value_congr
  intro b
  exact evidence_fixed M _ _ _

theorem value_holdsReify (t : Term sig m n) :
    value M (.mk (.holdsReify t) g r) i = value M (.mk t g r) i := by
  apply value_congr
  intro b
  exact evidence_fixed M _ _ _

theorem value_ctx (k : sig.Key) (args : Fin (sig.siteArity k) → GroundTerm sig.Ground m)
    (body : Term sig m (n+1)) :
    value M (.mk (.ctx k args body) g r) i =
      match i.context k (evalGround args g) with
      | none => .u
      | some q => value M (.mk body g (extend r q)) i := by
  cases found : i.context k (evalGround args g) with
  | none =>
    apply (value_undefined M _ _).mpr
    constructor <;> intro h <;> have hs := evidence_to_step h <;> simp [Step, found] at hs
  | some q =>
    apply value_congr
    intro b
    rw [evidence_fixed]
    simp [Step, found]

theorem value_read (name : sig.Name) (body : Term sig m (n+1)) :
    value M (.mk (.read name body) g r) i =
      match i.state.assignment name with
      | none => .u
      | some q => value M (.mk body g (extend r q)) i := by
  cases found : i.state.assignment name with
  | none =>
    apply (value_undefined M _ _).mpr
    constructor <;> intro h <;> have hs := evidence_to_step h <;> simp [Step, found] at hs
  | some q =>
    apply value_congr
    intro b
    rw [evidence_fixed]
    simp [Step, found]

theorem value_allG_true (body : Term sig (m+1) n) :
    value M (.mk (.allG body) g r) i = .t ↔ ∀ a, value M (.mk body (extend g a) r) i = .t := by
  rw [value_true, evidence_fixed]
  simp only [Step, ↓reduceIte, value_true]

theorem value_allG_false (body : Term sig (m+1) n) :
    value M (.mk (.allG body) g r) i = .f ↔ ∃ a, value M (.mk body (extend g a) r) i = .f := by
  rw [value_false, evidence_fixed]
  simp only [Step, Bool.false_eq_true, ↓reduceIte, value_false]

theorem value_allP_true (body : Term sig m (n+1)) :
    value M (.mk (.allP body) g r) i = .t ↔ ∀ q : Code sig, value M (.mk body g (extend r q)) i = .t := by
  rw [value_true, evidence_fixed]
  simp only [Step, ↓reduceIte, value_true]

theorem value_allP_false (body : Term sig m (n+1)) :
    value M (.mk (.allP body) g r) i = .f ↔ ∃ q : Code sig, value M (.mk body g (extend r q)) i = .f := by
  rw [value_false, evidence_fixed]
  simp only [Step, Bool.false_eq_true, ↓reduceIte, value_false]

theorem undefined_iff_not_tf (a : Truth) : a = .u ↔ a ≠ .t ∧ a ≠ .f := by cases a <;> simp

theorem value_allG_undefined (body : Term sig (m+1) n) :
    value M (.mk (.allG body) g r) i = .u ↔
      (¬∀ a, value M (.mk body (extend g a) r) i = .t) ∧
      ¬∃ a, value M (.mk body (extend g a) r) i = .f := by
  rw [undefined_iff_not_tf]
  exact and_congr (not_congr (value_allG_true M g r i body)) (not_congr (value_allG_false M g r i body))

theorem value_allP_undefined (body : Term sig m (n+1)) :
    value M (.mk (.allP body) g r) i = .u ↔
      (¬∀ q : Code sig, value M (.mk body g (extend r q)) i = .t) ∧
      ¬∃ q : Code sig, value M (.mk body g (extend r q)) i = .f := by
  rw [undefined_iff_not_tf]
  exact and_congr (not_congr (value_allP_true M g r i body)) (not_congr (value_allP_false M g r i body))

def ValueSound (R : Setoid (Code sig)) : Prop := ∀ c d, R.r c d → ∀ i, value M c i = value M d i

theorem valueSound_evidenceSound (R : Setoid (Code sig)) (sound : ValueSound M R) : EvidenceSound M R := by
  intro c d related i b h
  apply (evidence_value M d i b).mpr
  rw [← sound c d related i]
  exact (evidence_value M c i b).mp h

theorem value_transport (R : Setoid (Code sig)) (sound : ValueSound M R)
    {c d i j} (same : Reclose R c d) (inputs : InputRel R i j) : value M c i = value M d j :=
  value_congr M (fun _ => evidence_transport_iff M R (valueSound_evidenceSound M R sound) same inputs)

def Rv : Setoid (Code sig) where
  r c d := ∀ i, value M c i = value M d i
  iseqv := ⟨fun _ _ => rfl, fun h i => (h i).symm, fun h k i => (h i).trans (k i)⟩

theorem rv_sound : ValueSound M (Rv M) := fun _ _ h => h
end SmusniPositive
