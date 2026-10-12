import Smusni97.Opaque
import Smusni97.Projection

/-! Strong opaque control. These functions and certificates do not import the
explicit grammar or interpreter. The same generic projection facts are shared. -/
namespace Smusni97.Opaque

def twiceProjection : Projection (Prod.snd : State × State → State) :=
  Projection.restrict (fun e => support e.1)
    (Projection.restrict (fun e => support e.1) (Projection.root Prod.snd))

theorem twice_mask (e : State × State) : twiceProjection.keep e = support e.1 := by
  funext n
  simp [twiceProjection, Projection.restrict, Projection.root]

def twiceExport : NamedProjection A :=
  ⟨"twice-local", Projection.localOperation twiceProjection,
    Projection.localCertificate twiceProjection twice_mask⟩

def hostTwiceProjection : Projection (Prod.snd : Projection.HostEnv → State) :=
  let mask := fun e : Projection.HostEnv => unionMask (support e.1.1) e.1.2
  Projection.restrict mask (Projection.restrict mask (Projection.root Prod.snd))

theorem host_twice_mask (e : Projection.HostEnv) :
    hostTwiceProjection.keep e = unionMask (support e.1.1) e.1.2 := by
  funext n
  simp [hostTwiceProjection, Projection.restrict, Projection.root]

def hostTwice := Projection.hostOperation hostTwiceProjection
theorem hostTwice_correct : HostLaw hostTwice :=
  Projection.hostCertificate hostTwiceProjection host_twice_mask

def mixedProjection : Projection (Prod.snd : Projection.HostEnv → State) :=
  Projection.restrict (fun e => e.1.2)
    (Projection.restrict (fun e => support e.1.1) (Projection.root Prod.snd))

theorem mixed_mask (e : Projection.HostEnv) :
    mixedProjection.keep e = fun n => e.1.2 n && support e.1.1 n := by
  funext n
  simp [mixedProjection, Projection.restrict, Projection.root]
end Smusni97.Opaque
