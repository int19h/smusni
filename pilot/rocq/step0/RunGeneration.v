Require Import Step0.

(* Diagnostic producer-only run.  This cannot satisfy Step 0 by itself. *)
QuickChickWith step0_args synth_generation_only.
QuickChickWith step0_args check_generation_only.
