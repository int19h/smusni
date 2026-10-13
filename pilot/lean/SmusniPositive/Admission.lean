import SmusniPositive.Descent

namespace SmusniPositive
open SmusniF02 SmusniF03A1
universe u v
variable {sig : Signature.{u}} {W : Type v}

abbrev Admitted (M : Model sig W) := {d : Observation M // ∃ c : Code sig, denotation M c = d}
noncomputable def admit (M : Model sig W) (c : Code sig) : Admitted M := ⟨denotation M c, c, rfl⟩

noncomputable def Holds (M : Model sig W) : Proposition M → Admitted M :=
  Quotient.lift (admit M) (fun c d related => Subtype.ext ((denotation_kernel M c d).mpr related))

noncomputable def Reify (M : Model sig W) (d : Admitted M) : Proposition M :=
  Quotient.mk (RJ M) d.property.choose

theorem holds_mk (M : Model sig W) (c : Code sig) : Holds M (Quotient.mk (RJ M) c) = admit M c := rfl

theorem reify_admit (M : Model sig W) (c : Code sig) : Reify M (admit M c) = Quotient.mk (RJ M) c := by
  apply Quotient.sound
  exact (denotation_kernel M _ c).mp (admit M c).property.choose_spec

theorem holds_reify_inverse (M : Model sig W) (d : Admitted M) : Holds M (Reify M d) = d :=
  Subtype.ext d.property.choose_spec

theorem reify_holds_inverse (M : Model sig W) (p : Proposition M) : Reify M (Holds M p) = p := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep p
  exact reify_admit M c

noncomputable def representative (M : Model sig W) (p : Proposition M) : Code sig :=
  (Quotient.exists_rep p).choose
theorem representative_section (M : Model sig W) (p : Proposition M) :
    Quotient.mk (RJ M) (representative M p) = p := (Quotient.exists_rep p).choose_spec
theorem representative_injective (M : Model sig W) {p q : Proposition M}
    (h : representative M p = representative M q) : p = q := by
  have eq := congrArg (Quotient.mk (RJ M)) h
  simpa only [representative_section] using eq

theorem language_holds_reify (M : Model sig W) {m n} (t : Term sig m n)
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) :
    admit M (.mk (.holdsReify t) g r) = admit M (.mk t g r) :=
  Subtype.ext ((denotation_kernel M _ _).mpr (holds_reify_rj M t g r))

theorem language_reify_holds (M : Model sig W) (c : Code sig) :
    Quotient.mk (RJ M) (holdsCode c) = Quotient.mk (RJ M) c := Quotient.sound (holds_code_rj M c)

theorem language_holds_prop (M : Model sig W) {m n} (p : PropTerm sig m n)
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) :
    admit M (.mk (holds p) g r) = Holds M (Quotient.mk (RJ M) (evalProp p g r)) := by
  apply Subtype.ext
  apply (denotation_kernel M _ _).mpr
  cases p with
  | var x =>
    constructor
    · intro i; exact value_holdsVar M g r i x
    · intro i
      change SmusniF02.PartialEq (Rv M).r (event (.mk (.holdsVar x) g r) i) (event (r x) i)
      rw [event_var]
      exact SmusniF03A2.partial_refl (Rv M) _
  | reify t => exact holds_reify_rj M t g r

/-- Every constructor consumes an actual finite term and finite environments.
Proposition environments are decoded through the proved quotient section. -/
noncomputable def interpretTerm (M : Model sig W) {m n} (t : Term sig m n)
    (g : Fin m → sig.Ground) (r : Fin n → Proposition M) : Admitted M :=
  admit M (.mk t g (fun x => representative M (r x)))

theorem interpretTerm_at (M : Model sig W) {m n} (t : Term sig m n) (g : Fin m → sig.Ground)
    (r : Fin n → Code sig) :
    interpretTerm M t g (fun x => Quotient.mk (RJ M) (r x)) = admit M (.mk t g r) := by
  apply Subtype.ext
  apply (denotation_kernel M _ _).mpr
  apply reclose_rj M
  exact .mk rfl (fun x => Quotient.exact (representative_section M (Quotient.mk (RJ M) (r x))))

noncomputable def representedBody (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) : Proposition M → Admitted M :=
  Quotient.lift (fun q => admit M (.mk body g (extend r q))) (by
    intro q q' related
    apply Subtype.ext
    apply (denotation_kernel M _ _).mpr
    exact reclose_rj M (.mk rfl (extend_related (RJ M) (fun x => (RJ M).refl (r x)) related)))

theorem representedBody_at (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (q : Code sig) :
    representedBody M body g r (Quotient.mk (RJ M) q) = admit M (.mk body g (extend r q)) := rfl

theorem representedBody_env (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r r' : Fin n → Code sig) (related : ∀ x, (RJ M).r (r x) (r' x)) :
    representedBody M body g r = representedBody M body g r' := by
  funext p
  obtain ⟨q, rfl⟩ := Quotient.exists_rep p
  apply Subtype.ext
  apply (denotation_kernel M _ _).mpr
  exact reclose_rj M (.mk rfl (extend_related (RJ M) related ((RJ M).refl q)))

abbrev AdmittedBodyFamily (M : Model sig W) :=
  {f : Proposition M → Admitted M // ∃ (m n : Nat) (body : Term sig m (n+1)) (g : Fin m → sig.Ground)
    (r : Fin n → Code sig), f = representedBody M body g r}

noncomputable def admitBody (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) : AdmittedBodyFamily M :=
  ⟨representedBody M body g r, m, n, body, g, r, rfl⟩

noncomputable def representedGroundBody (M : Model sig W) {m n} (body : Term sig (m+1) n)
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) : sig.Ground → Admitted M :=
  fun a => admit M (.mk body (extend g a) r)

abbrev AdmittedGroundFamily (M : Model sig W) :=
  {f : sig.Ground → Admitted M // ∃ (m n : Nat) (body : Term sig (m+1) n) (g : Fin m → sig.Ground)
    (r : Fin n → Code sig), f = representedGroundBody M body g r}

noncomputable def admitGroundBody (M : Model sig W) {m n} (body : Term sig (m+1) n)
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) : AdmittedGroundFamily M :=
  ⟨representedGroundBody M body g r, m, n, body, g, r, rfl⟩

noncomputable def bodyValue (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) : Proposition M → Truth :=
  Quotient.lift (fun q => value M (.mk body g (extend r q)) i) (by
    intro q q' related
    exact (reclose_rj M (.mk rfl (extend_related (RJ M) (fun x => (RJ M).refl (r x)) related))).1 i)

theorem bodyValue_at (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) (q : Code sig) :
    bodyValue M body g r i (Quotient.mk (RJ M) q) = value M (.mk body g (extend r q)) i := rfl

theorem body_observation_at (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) (p : Proposition M) :
    (representedBody M body g r p).val.run () () (qE M i.context) i.world (qS M i.state) =
      NEFin.singleton (outcomeOf (bodyValue M body g r i p) (qS M i.state)) := by
  obtain ⟨q, rfl⟩ := Quotient.exists_rep p
  change (denotation M (.mk body g (extend r q))).run _ _ _ _ _ = _
  rw [denotation_run_at]
  simp only [run, mapResults_singleton, map_outcomeOf, bodyValue_at]

theorem allP_true_classes (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) :
    value M (.mk (.allP body) g r) i = .t ↔ ∀ p : Proposition M, bodyValue M body g r i p = .t := by
  rw [value_allP_true]
  constructor
  · intro all p; obtain ⟨q, rfl⟩ := Quotient.exists_rep p; exact all q
  · intro all q; exact all (Quotient.mk (RJ M) q)

theorem allP_false_classes (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) :
    value M (.mk (.allP body) g r) i = .f ↔ ∃ p : Proposition M, bodyValue M body g r i p = .f := by
  rw [value_allP_false]
  constructor
  · rintro ⟨q, h⟩; exact ⟨Quotient.mk (RJ M) q, h⟩
  · rintro ⟨p, h⟩; obtain ⟨q, rfl⟩ := Quotient.exists_rep p; exact ⟨q, h⟩

theorem allP_undefined_classes (M : Model sig W) {m n} (body : Term sig m (n+1))
    (g : Fin m → sig.Ground) (r : Fin n → Code sig) (i : Input sig W) :
    value M (.mk (.allP body) g r) i = .u ↔
      (¬∀ p : Proposition M, bodyValue M body g r i p = .t) ∧
      ¬∃ p : Proposition M, bodyValue M body g r i p = .f := by
  rw [undefined_iff_not_tf]
  exact and_congr (not_congr (allP_true_classes M body g r i)) (not_congr (allP_false_classes M body g r i))
end SmusniPositive
