import Smusni97.Common

/-! Shared semantic certificates for both candidates. No defining interpreter is
imported. A certificate can accompany an ordinary function without syntax. -/
namespace Smusni97
open SmusniF02

theorem prune_all (s : State) : prune (fun _ => true) s = s := rfl

structure Projection {E : Type} (root : E → State) where
  evaluate : E → State
  keep : E → Mask
  correct : ∀ e, evaluate e = prune (keep e) (root e)

namespace Projection
def root (f : E → State) : Projection f := ⟨f, fun _ _ => true, fun _ => rfl⟩
def restrict {root : E → State} (mask : E → Mask) (p : Projection root) : Projection root where
  evaluate e := prune (mask e) (p.evaluate e)
  keep e n := mask e n && p.keep e n
  correct e := by rw [p.correct, prune_inter]

theorem preserves {root : E → State} (p : Projection root) (e : E) :
    (p.evaluate e).sides = (root e).sides ∧
    (p.evaluate e).obligations = (root e).obligations ∧
    (p.evaluate e).frames = (root e).frames ∧
    (p.evaluate e).hosts = (root e).hosts ∧
    (p.evaluate e).kappa = (root e).kappa ∧ (p.evaluate e).chi = (root e).chi := by
  rw [p.correct]; exact prune_preserves _ _

theorem slots {root : E → State} (p : Projection root) (e : E) (n : Nat) :
    (p.evaluate e).slots n = if p.keep e n then (root e).slots n else none := by rw [p.correct]; rfl

theorem incoming {root : E → State} (p : Projection root) (e : E) (entry : State)
    (frame : Frame entry (root e)) (mask : ∀ n, support entry n = true → p.keep e n = true)
    (n v : Nat) (old : entry.slots n = some v) : (p.evaluate e).slots n = some v := by
  rw [p.slots, mask n (by simp [support, old])]
  exact frame.incoming n v old

def localOperation (p : Projection (Prod.snd : State × State → State)) (entry : State) (z : Out A) : Out A :=
  mapState (fun reached => p.evaluate (entry, reached)) z

theorem localCertificate (p : Projection (Prod.snd : State × State → State))
    (mask : ∀ e, p.keep e = support e.1) : LocalLaw (localOperation (A := A) p) := by
  intro entry z
  cases z <;> simp only [localOperation, mapState, p.correct, mask]

abbrev HostEnv := (State × Mask) × State
def hostOperation (p : Projection (Prod.snd : HostEnv → State))
    (entry : State) (eligible : Mask) (h : Nat) (z : Out Unit) : Out Nat :=
  .live (record h z.truth (suffixStatus entry z.state) (p.evaluate ((entry, eligible), z.state))) h

theorem hostCertificate (p : Projection (Prod.snd : HostEnv → State))
    (mask : ∀ e, p.keep e = unionMask (support e.1.1) e.1.2) : HostLaw (hostOperation p) := by
  intro entry eligible h use
  simp only [hostOperation, p.correct, mask]
end Projection
end Smusni97
