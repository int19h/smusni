import Smusni97.Explicit

/-! O2: extensible named definitions with actual semantic certificates.
Unlike Explicit.LocalExport, admission here is not equality to a fixed body.
The ordinary term boundary consumes the supplied body AND its proof. -/
namespace Smusni97.Reviewed
open SmusniF02 Explicit

structure LocalExport (A : Type) where
  name : String
  body : RunDef A A
  correct : LocalLaw (fun entry z => observeOut body entry (fun _ => false) 0 z)

structure HostExport where
  name : String
  body : RunDef Unit Nat
  correct : HostLaw (observeOut body)

structure NegativeExport where
  name : String
  body : RunDef Unit Unit
  correct : ∀ (test : RefTest) (entry : State),
    observeOut body entry (fun _ => false) 0 (test.observe entry) =
      negate (prune (support entry) (test.observe entry).state) (test.observe entry)

def canonicalLocal : LocalExport A :=
  ⟨"Local", localDef, by intro entry z; cases z <;> rfl⟩
def canonicalHost : HostExport :=
  ⟨"Host", hostDef, by intro entry eligible h use; cases use.terminal <;> rfl⟩
def canonicalNegative : NegativeExport :=
  ⟨"negRef1", negDef, by intro test entry; cases test.observe entry <;> rfl⟩

def negative (exported : NegativeExport) (entry : State) (use : NegativeUse entry) : Out Unit :=
  observeOut exported.body entry (fun _ => false) 0 (use.test.observe entry)

/-- A different finite defining tree. It is rejected by O1 and admitted by O2. -/
def twiceState : Expr .state := .prune (.support .entry) localState
def twiceDef : RunDef A A := ⟨.live twiceState .arg, .dead twiceState, .undef twiceState⟩

theorem twice_not_canonical : (twiceDef : RunDef A A) ≠ localDef := by
  intro h
  have same := congrArg (fun d : RunDef A A => d.dead) h
  simp [twiceDef, twiceState, localDef, localState] at same

theorem prune_idempotent (mask : Mask) (s : State) : prune mask (prune mask s) = prune mask s := by
  rw [prune_inter]
  congr 1
  funext n
  simp

theorem twice_correct : LocalLaw (fun entry z =>
    observeOut (twiceDef : RunDef A A) entry (fun _ => false) 0 z) := by
  intro entry z
  cases z with
  | live s a =>
    change Outcome.live (prune (support entry) (prune (support entry) s)) a = _
    rw [prune_idempotent]; rfl
  | dead s =>
    change Outcome.dead (prune (support entry) (prune (support entry) s)) = _
    rw [prune_idempotent]; rfl
  | undef s =>
    change Outcome.undef (prune (support entry) (prune (support entry) s)) = _
    rw [prune_idempotent]; rfl

def bodyExport : LocalExport A := { canonicalLocal with name := "quantifier-body" }
def alternateExport : LocalExport A := ⟨"equivalent-local", twiceDef, twice_correct⟩

inductive Term : Explicit.Cat → Type → Type 1 where
  | base : Explicit.Term c A → Term c A
  | bind : Term c A → (A → Term c B) → Term c B
  | project : LocalExport A → Term .ref A → Term .ref A
  | host : HostExport → Term .ref Unit → Mask → Nat → Term .perf Nat
  | negative : NegativeExport → RefTest → Term .ref Unit

noncomputable def observe : Term c A → Run A
  | .base t => Explicit.observe t
  | .bind m k => sequence (observe m) (fun a => observe (k a))
  | .project exported m => applyDef exported.body (observe m) (fun _ => false) 0
  | .host exported m eligible h => applyDef exported.body (observe m) eligible h
  | .negative exported test => fun entry =>
      NEFin.singleton (observeOut exported.body entry (fun _ => false) 0 (test.observe entry))

theorem admitted_local_laws (exported : LocalExport A) (entry : State) (z : Out A) :
    value (observeOut exported.body entry (fun _ => false) 0 z) = value z ∧
    (observeOut exported.body entry (fun _ => false) 0 z).state.sides = z.state.sides ∧
    (observeOut exported.body entry (fun _ => false) 0 z).state.obligations = z.state.obligations := by
  have he : observeOut exported.body entry (fun _ => false) 0 z =
      mapState (prune (support entry)) z := exported.correct entry z
  rw [he]
  simp [prune]

theorem different_body_runs (m : Explicit.Term .ref A) :
    observe (.project alternateExport (.base m)) = Explicit.observe (.local m) := by
  funext entry
  change mapResults (fun z => observeOut twiceDef entry (fun _ => false) 0 z) _ = _
  have he : (fun z => observeOut (twiceDef : RunDef A A) entry (fun _ => false) 0 z) =
      Explicit.localOut entry := by
    funext z
    have hz : observeOut (twiceDef : RunDef A A) entry (fun _ => false) 0 z =
        mapState (prune (support entry)) z := twice_correct entry z
    rw [hz]
    cases z <;> rfl
  rw [he]
  rfl
end Smusni97.Reviewed
