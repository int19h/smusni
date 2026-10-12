import Smusni97.Cases

/-! Retained from Astra's PR100-PUBLIC-BOUNDARY.lean, October 12, 2026.
Only the import changes to avoid a root-module cycle. The ten theorem bodies
and the actual F/U continuation and handle-reuse cases are unchanged. -/

namespace AstraPR100
open Smusni97 SmusniF02

def first (status : Truth) : Opaque.Term .perf Nat :=
  .host (.test (Cases.operand status)) Cases.scope 8

def reached (status : Truth) : State :=
  (Opaque.hostOut Cases.entry Cases.scope 8 ((Cases.operand status).observe Cases.entry)).state

theorem first_result (status : Truth) :
    Opaque.observe (first status) Cases.entry = NEFin.singleton (.live (reached status) 8) := by
  change mapResults (Opaque.hostOut Cases.entry Cases.scope 8)
    (NEFin.singleton ((Cases.operand status).observe Cases.entry)) = _
  rw [map_singleton]
  rfl

def chain (status : Truth) : Opaque.Term .perf Nat :=
  .bind (first status) (fun h => .lift (.bind (.emit ⟨h, true⟩) (fun _ => .pure (h+1))))

theorem chain_admitted (status : Truth) : Opaque.Admitted (chain status) Cases.entry := by
  refine ⟨Cases.opaqueAdmitted status, ?_⟩
  intro s a _
  exact ⟨trivial, by intro _ _ _; trivial⟩

theorem chain_runs_after_false_or_undefined (status : Truth) :
    Opaque.run (chain status) Cases.entry (chain_admitted status) =
      NEFin.singleton (.live {reached status with sides := (reached status).sides ++ [⟨8, true⟩]} 9) := by
  change SmusniF02.Run.bind (Opaque.observe (first status)) _ Cases.entry = _
  simp only [SmusniF02.Run.bind, first_result, NEFin.singleton_unionMap, SmusniF02.Run.extend]
  simp [Opaque.observe, SmusniF02.Run.bind, SmusniF02.Run.extend, SmusniF02.Run.pure]

def duplicate (status : Truth) : Opaque.Term .perf Nat :=
  .bind (first status) (fun h => .host (.pure ()) Cases.scope h)

theorem duplicate_rejected_after_first_host (status : Truth) :
    ¬ Opaque.Admitted (duplicate status) Cases.entry := by
  intro ok
  have cont := ok.2 (reached status) 8 (by rw [first_result]; rfl)
  have fresh := (cont.2 (.live (reached status) ()) (by rfl)).2
  have mem : (⟨8, status, .t⟩ : HostRecord Nat) ∈ (reached status).hosts := by
    cases status <;> decide
  exact fresh _ mem rfl

def explicitChain (status : Truth) : Explicit.Term .perf Nat := Comparison.translate (chain status)

theorem explicit_chain_admitted (status : Truth) :
    Explicit.Admitted (explicitChain status) Cases.entry := by
  refine ⟨Cases.explicitAdmitted status, ?_⟩
  intro s a _
  exact ⟨trivial, by intro _ _ _; trivial⟩

theorem explicit_chain_same (status : Truth) :
    Explicit.run (explicitChain status) Cases.entry (explicit_chain_admitted status) =
      Opaque.run (chain status) Cases.entry (chain_admitted status) :=
  congrFun (Comparison.term_parity (chain status)) Cases.entry

theorem duplicate_rejected_explicit (status : Truth) :
    ¬ Explicit.Admitted (Comparison.translate (duplicate status)) Cases.entry := by
  intro ok
  have firstObs := congrFun (Comparison.term_parity (first status)) Cases.entry
  have cont := ok.2 (reached status) 8 (by
    change .live (reached status) 8 ∈ Explicit.observe (Comparison.translate (first status)) Cases.entry
    rw [firstObs, first_result]
    rfl)
  have fresh := (cont.2 (.live (reached status) ()) (by rfl)).2
  have mem : (⟨8, status, .t⟩ : HostRecord Nat) ∈ (reached status).hosts := by
    cases status <;> decide
  exact fresh _ mem rfl

def reviewedFirst (status : Truth) : Reviewed.Term .perf Nat :=
  .host Reviewed.canonicalHost (.base (.test (Cases.operand status))) Cases.scope 8

def reviewedChain (status : Truth) : Reviewed.Term .perf Nat :=
  .bind (reviewedFirst status)
    (fun h => .base (.lift (.bind (.emit ⟨h, true⟩) (fun _ => .pure (h+1)))))

theorem reviewed_chain_admitted (status : Truth) :
    Reviewed.Admitted (reviewedChain status) Cases.entry := by
  refine ⟨Cases.reviewedAdmitted status, ?_⟩
  intro s a _
  exact ⟨trivial, by intro _ _ _; trivial⟩

theorem reviewed_chain_same (status : Truth) :
    Reviewed.run (reviewedChain status) Cases.entry (reviewed_chain_admitted status) =
      Explicit.run (explicitChain status) Cases.entry (explicit_chain_admitted status) := rfl

theorem duplicate_rejected_reviewed (status : Truth) :
    ¬ Reviewed.Admitted
      (.bind (reviewedFirst status)
        (fun h => .host Reviewed.canonicalHost (.base (.pure ())) Cases.scope h)) Cases.entry := by
  intro ok
  have firstObs : Reviewed.observe (reviewedFirst status) Cases.entry =
      Opaque.observe (first status) Cases.entry := by
    change Explicit.observe (Comparison.translate (first status)) Cases.entry = _
    exact congrFun (Comparison.term_parity (first status)) Cases.entry
  have cont := ok.2 (reached status) 8 (by rw [firstObs, first_result]; rfl)
  have fresh := (cont.2 (.live (reached status) ()) (by rfl)).2
  have mem : (⟨8, status, .t⟩ : HostRecord Nat) ∈ (reached status).hosts := by
    cases status <;> decide
  exact fresh _ mem rfl

end AstraPR100
