import SmusniPilot.M2TypingJudgment
import SmusniPilot.Binding

/-! Actual pilot terms and declarative typing witnesses. These derive formation
only. No resolver admission or semantic interpretation follows from typing. -/
namespace SmusniF03B
open SmusniPilot SmusniPilot.M2

def neg {n : Nat} (t : Term n) : Term n := .primitive .not (.positional t .nil)
def holds {n : Nat} (p : Term n) : Term n := .primitive .holds (.positional p .nil)
def reify {n : Nat} (t : Term n) : Term n := .primitive .reify (.positional t .nil)
def source (k : SiteId) : Term 0 := .context k .nil
def body : Term 1 := neg (holds (.bound 0))
def L (k : SiteId) : Term 0 := .bind Ty.proposition (source k) body
def pL (k : SiteId) : Term 0 := reify (L k)
def H (k : SiteId) : Term 0 := holds (pL k)
def N (k : SiteId) : Term 0 := neg (H k)
def instantiate (b : Term 1) (q : Term 0) : Term 0 := b.substitute (fun _ => q)

theorem body_instantiation (k : SiteId) : instantiate body (pL k) = N k := rfl
theorem L_one_site (k : SiteId) : (L k).siteIds = [k] := rfl

def pureContent : TypingObservation := { type := Ty.content }
def contextualContent : TypingObservation := { type := Ty.content, effects := [.context] }
def propositionObservation : TypingObservation := { type := Ty.proposition }
def contextObservation : TypingObservation := { type := Ty.refComp Ty.proposition, effects := [.context] }

private theorem contentCompatible : Ty.compatible Ty.content Ty.content = true := by
  unfold Ty.compatible
  rfl
private theorem propositionCompatible : Ty.compatible Ty.proposition Ty.proposition = true := by
  unfold Ty.compatible
  rfl

theorem source_typed (k : SiteId) :
    CheckJudgment Environment.empty (source k) (Ty.refComp Ty.proposition) contextObservation :=
  .context Environment.empty k .nil Ty.proposition [] (.nil Environment.empty)

theorem bound_holds_typed : SynthJudgment (Environment.empty.extend Ty.proposition)
    (holds (.bound 0)) pureContent := by
  apply SynthJudgment.primitive
  refine PrimitiveJudgment.holds _ _ propositionObservation ?_
  exact .fromSynth _ _ _ _ (.bound _ 0) propositionCompatible

theorem body_typed : SynthJudgment (Environment.empty.extend Ty.proposition) body pureContent := by
  apply SynthJudgment.primitive
  refine PrimitiveJudgment.negation _ _ pureContent ?_
  exact .fromSynth _ _ _ _ bound_holds_typed contentCompatible

theorem L_typed (k : SiteId) : SynthJudgment Environment.empty (L k) contextualContent :=
  .bindReference _ Ty.proposition (source k) body contextObservation pureContent (source_typed k) body_typed

theorem pL_typed (k : SiteId) : SynthJudgment Environment.empty (pL k) propositionObservation := by
  apply SynthJudgment.primitive
  refine PrimitiveJudgment.reify _ _ contextualContent ?_
  exact .fromSynth _ _ _ _ (L_typed k) contentCompatible

theorem H_typed (k : SiteId) : SynthJudgment Environment.empty (H k) pureContent := by
  apply SynthJudgment.primitive
  refine PrimitiveJudgment.holds _ _ propositionObservation ?_
  exact .fromSynth _ _ _ _ (pL_typed k) propositionCompatible

theorem N_typed (k : SiteId) : SynthJudgment Environment.empty (N k) pureContent := by
  apply SynthJudgment.primitive
  refine PrimitiveJudgment.negation _ _ pureContent ?_
  exact .fromSynth _ _ _ _ (H_typed k) contentCompatible

theorem static_effects : contextualContent.effects = [.context] ∧ pureContent.effects = [] := ⟨rfl, rfl⟩
end SmusniF03B
