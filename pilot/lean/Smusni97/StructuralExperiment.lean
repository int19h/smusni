import Smusni97.Cases
import Smusni97.Transport
import Smusni97.OpaqueProjection

/-! Exactly the two reviewed-export demonstrations and the internal mixed-mask
probe requested by the consolidated follow-up. No new surface operator. -/
namespace Smusni97.StructuralExperiment
open SmusniF02 Explicit

def badEnv : Env := ⟨Cases.entry, Cases.prepare Cases.entry 42, fun _ => false, 8, .f⟩

theorem entry_root_loses_sides :
    analyze Expr.entry = none ∧ (Expr.entry.eval badEnv).sides ≠ badEnv.reached.sides := by
  exact ⟨rfl, by decide⟩

theorem recognized_can_drop_incoming :
    analyze (.prune .eligible .reached) = some (fun e n => e.eligible n && true) ∧
    badEnv.entry.slots 0 = some 7 ∧
    ((Expr.prune .eligible .reached).eval badEnv).slots 0 = none := ⟨rfl, rfl, rfl⟩

def eligibleBody : RunDef A A :=
  let s := Expr.prune .eligible .reached
  ⟨.live s .arg, .dead s, .undef s⟩

theorem eligible_is_not_local : ¬ LocalLaw (fun s z =>
    observeOut (eligibleBody : RunDef Unit Unit) s (fun _ => false) 0 z) := by
  intro h
  have eq := h Cases.entry (.dead Cases.entry)
  have slot := congrArg (fun z : Out Unit => z.state.slots 0) eq
  change (none : Option Nat) = some 7 at slot
  contradiction

def mixed : Expr .state := .prune .eligible (.prune (.support .entry) .reached)

theorem mixed_analyzed (e : Env) :
    mixed.eval e = prune (fun n => e.eligible n && support e.entry n) e.reached := by
  have h := analyze_sound mixed (fun e n => e.eligible n && (support e.entry n && true)) rfl e
  simpa only [Bool.and_true] using h

theorem mixed_matches_opaque (e : Env) : mixed.eval e =
    Opaque.mixedProjection.evaluate ((e.entry, e.eligible), e.reached) := by
  rw [mixed_analyzed, Opaque.mixedProjection.correct, Opaque.mixed_mask]

theorem mixed_differs_from_local_and_host :
    (mixed.eval badEnv).slots 0 = none ∧
    (prune (support badEnv.entry) badEnv.reached).slots 0 = some 7 ∧
    (prune (unionMask (support badEnv.entry) badEnv.eligible) badEnv.reached).slots 0 = some 7 :=
  ⟨rfl, rfl, rfl⟩

theorem analyzer_slot_alternatives (state : Expr .state) (keep : Env → Mask)
    (ok : analyze state = some keep) (e : Env) (n : Nat) :
    (state.eval e).slots n = e.reached.slots n ∨ (state.eval e).slots n = none := by
  rw [analyzed_slots state keep ok]
  cases keep e n <;> simp

theorem local_certificate_matches_opaque (entry : State) (z : Out A) :
    observeOut Reviewed.twiceDef entry (fun _ => false) 0 z = Opaque.twiceExport.operation entry z := by
  have l : observeOut Reviewed.twiceDef entry (fun _ => false) 0 z =
      mapState (prune (support entry)) z := Reviewed.twice_correct entry z
  exact l.trans (Opaque.twiceExport.correct entry z).symm

theorem host_certificate_matches_opaque (entry : State) (mask : Mask) (h : Nat) (use : HostUse entry h) :
    observeOut Reviewed.hostTwiceDef entry mask h use.terminal = Opaque.hostTwice entry mask h use.terminal :=
  (Reviewed.host_twice_correct entry mask h use).trans (Opaque.hostTwice_correct entry mask h use).symm

def reviewedLocal (status : Truth) : Reviewed.Term .ref Unit :=
  .project Reviewed.alternateExport (.base (.test (Cases.operand status)))
def reviewedHost (status : Truth) : Reviewed.Term .perf Nat :=
  .host Reviewed.alternateHost (.base (.test (Cases.operand status))) Cases.scope 8

def localAdmitted (status : Truth) : Reviewed.Admitted (reviewedLocal status) Cases.entry := ⟨rfl, trivial⟩
def hostAdmitted (status : Truth) : Reviewed.Admitted (reviewedHost status) Cases.entry :=
  ⟨⟨rfl, trivial⟩, Cases.operand_host_domain status⟩

theorem local_public_execution (status : Truth) :
    Reviewed.run (reviewedLocal status) Cases.entry (localAdmitted status) =
      Opaque.run (Reviewed.toOpaque (reviewedLocal status)) Cases.entry
        (Reviewed.toOpaque_transport _ _ (localAdmitted status)).1 :=
  Reviewed.public_run_parity _ _ _

theorem host_public_execution (status : Truth) :
    Reviewed.run (reviewedHost status) Cases.entry (hostAdmitted status) =
      Opaque.run (Reviewed.toOpaque (reviewedHost status)) Cases.entry
        (Reviewed.toOpaque_transport _ _ (hostAdmitted status)).1 :=
  Reviewed.public_run_parity _ _ _

theorem frame_does_not_constrain_obligations (s : State) (obligations : List Obligation) :
    Frame s {s with obligations := obligations} :=
  ⟨fun _ _ h => h, ⟨[], by simp⟩, rfl, rfl, rfl, rfl⟩

theorem reviewed_kappa_false (exported : Reviewed.HostExport) (entry : State) (mask : Mask)
    (h : Nat) (use : HostUse entry h) (hk : use.terminal.state.kappa = .f) :
    (observeOut exported.body entry mask h use.terminal).state.kappa = .f := by
  have law := exported.correct entry mask h use
  rw [law]
  exact record_kappa_false _ _ _ _ hk

theorem reviewed_chi_false (exported : Reviewed.HostExport) (entry : State) (mask : Mask)
    (h : Nat) (use : HostUse entry h) (hc : use.terminal.state.chi = .f) :
    (observeOut exported.body entry mask h use.terminal).state.chi = .f := by
  have law := exported.correct entry mask h use
  rw [law]
  exact record_chi_false _ _ _ _ hc
end Smusni97.StructuralExperiment
