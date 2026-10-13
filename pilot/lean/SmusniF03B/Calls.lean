import SmusniF03B.Conditional

namespace SmusniF03B
open SmusniF02 SmusniPilot SmusniPilot.M2

abbrev Configuration (D : Domains) := Term 0 × Input D

/-- Generic dependency rules for the direct-unfolding evaluator under examination.
They do not follow from denotational equality and do not define a total evaluator. -/
inductive Calls (M : Observations D P) : Configuration D → Configuration D → Prop
  | bind (c : Term 0) (b : Term 1) (q : Term 0) (xi : Input D) (s : D.State)
      (success : Outcome.live s (M.reifyValue q) ∈ M.valueRun c xi) :
      Calls M (.bind Ty.proposition c b, xi) (instantiate b (reify q), xi.atState s)
  | negation (c : Term 0) (xi : Input D) : Calls M (neg c, xi) (c, xi)
  | holds (q : Term 0) (xi : Input D) : Calls M (holds (reify q), xi) (q, M.replay q xi)

theorem call_cycle {M : Observations D P} (laws : RunLaws M) (xi : Input D)
    (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site)))
    (replay : ReplayAt (M.replay (L xi.site) xi) xi) :
    Calls M (L xi.site, xi) (N xi.site, xi) ∧
    Calls M (N xi.site, xi) (H xi.site, xi) ∧
    Calls M (H xi.site, xi) (L xi.site, xi) := by
  have success := laws.contextSuccess xi _ admitted resolved
  have found : Outcome.live xi.caller (M.reifyValue (L xi.site)) ∈ M.valueRun (source xi.site) xi := by
    rw [success.exactRun]; rfl
  refine ⟨?_, Calls.negation _ _, ?_⟩
  · simpa only [Input.atState_self, L, N, H, pL, instantiate, body, reify, holds, neg,
      Term.substitute, TermList.substitute] using
      Calls.bind (M := M) (source xi.site) body (L xi.site) xi xi.caller found
  · simpa only [replay.eq, H, pL] using Calls.holds (M := M) (L xi.site) xi

theorem acc_no_three_cycle {r : A → A → Prop} {x : A} (acc : Acc r x) :
    ∀ y z, r y x → r z y → r x z → False := by
  induction acc with
  | intro x _ ih =>
    intro y z xy yz zx
    exact ih y xy z x yz zx xy

/-- Any well-founded target relation is impossible, not only a natural-number size. -/
theorem no_decreasing_measure {M : Observations D P} (laws : RunLaws M) (xi : Input D)
    (admitted : M.admits xi.context)
    (resolved : M.resolve xi = some (M.reifyValue (L xi.site)))
    (replay : ReplayAt (M.replay (L xi.site) xi) xi)
    (measure : Configuration D → A) (r : A → A → Prop) (wf : WellFounded r)
    (decreases : ∀ before after, Calls M before after → r (measure after) (measure before)) : False := by
  obtain ⟨ln, nh, hl⟩ := call_cycle laws xi admitted resolved replay
  exact acc_no_three_cycle (wf.apply (measure (L xi.site, xi))) _ _
    (decreases _ _ ln) (decreases _ _ nh) (decreases _ _ hl)
end SmusniF03B
