import Smusni97.Cases
open Smusni97
def badOpaque : Opaque.NamedProjection Unit :=
  ⟨"bad", Cases.scrub, fun _ _ => rfl⟩
