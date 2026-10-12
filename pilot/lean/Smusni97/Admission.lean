import Smusni97.Opaque
import Smusni97.Reviewed

/-! Per-use formation is separate from raw observation. All public `run` entry
points require admission. These judgments check proofs, not infer scope plans,
fresh allocation, or admissibility of arbitrary imported functions. -/
namespace Smusni97
open SmusniF02

def HostDomain (m : Run Unit) (s : State) (h : Nat) : Prop :=
  ∀ z, z ∈ m s → Frame s z.state ∧ FreshHost h z.state

namespace Opaque
noncomputable def Admitted : Term c A → State → Prop
  | .pure _, _ => True
  | .test t, s => t.Admitted s
  | .emit _, _ => True
  | .bind m k, s => Admitted m s ∧
      ∀ reached a, .live reached a ∈ observe m s → Admitted (k a) reached
  | .local m, s => Admitted m s
  | .body m, s => Admitted m s
  | .negative t, s => t.Admitted s
  | .host m _ h, s => Admitted m s ∧ HostDomain (observe m) s h
  | .lift m, s => Admitted m s
  | .project _ m, s => Admitted m s

noncomputable def run (m : Term c A) (s : State) (_ : Admitted m s) : Results A := observe m s

theorem host_domain_required (m : Term .ref Unit) (e : Mask) (h : Nat) (s : State)
    (ok : Admitted (.host m e h) s) : HostDomain (observe m) s h := ok.2
end Opaque

namespace Explicit
noncomputable def Admitted : Term c A → State → Prop
  | .pure _, _ => True
  | .test t, s => t.Admitted s
  | .emit _, _ => True
  | .bind m k, s => Admitted m s ∧
      ∀ reached a, .live reached a ∈ observe m s → Admitted (k a) reached
  | .local m, s => Admitted m s
  | .body m, s => Admitted m s
  | .negative t, s => t.Admitted s
  | .host m _ h, s => Admitted m s ∧ HostDomain (observe m) s h
  | .lift m, s => Admitted m s

noncomputable def run (m : Term c A) (s : State) (_ : Admitted m s) : Results A := observe m s

theorem host_domain_required (m : Term .ref Unit) (e : Mask) (h : Nat) (s : State)
    (ok : Admitted (.host m e h) s) : HostDomain (observe m) s h := ok.2
end Explicit

namespace Reviewed
noncomputable def Admitted : Term c A → State → Prop
  | .base m, s => Explicit.Admitted m s
  | .bind m k, s => Admitted m s ∧
      ∀ reached a, .live reached a ∈ observe m s → Admitted (k a) reached
  | .project _ m, s => Admitted m s
  | .host _ m _ h, s => Admitted m s ∧ HostDomain (observe m) s h
  | .negative _ t, s => t.Admitted s

noncomputable def run (m : Term c A) (s : State) (_ : Admitted m s) : Results A := observe m s

theorem host_domain_required (exported : HostExport) (m : Term .ref Unit) (e : Mask) (h : Nat)
    (s : State) (ok : Admitted (.host exported m e h) s) : HostDomain (observe m) s h := ok.2
end Reviewed
end Smusni97
