import Smusni97.Reviewed
open Smusni97 Smusni97.Explicit
-- A body does not gain a reviewed name without a semantic proof.
def badCertificate : LocalLaw (fun s z =>
    observeOut (scrubDef : RunDef Unit Unit) s (fun _ => false) 0 z) := fun _ _ => rfl
